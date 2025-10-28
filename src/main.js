
/* ===== 유틸 ===== */
function fnv1a(str) { let h = 0x811c9dc5; for (const ch of str) { h ^= ch.codePointAt(0); h = (h >>> 0) * 0x01000193; } return h >>> 0; }
function xorshift(seed) { let x = seed >>> 0 || 123456789; return () => { x ^= (x << 13); x >>>= 0; x ^= (x >>> 17); x >>>= 0; x ^= (x << 5); x >>>= 0; return (x >>> 0) / 0xFFFFFFFF; }; }
const clamp = (n, a, b) => Math.max(a, Math.min(b, n));
const log = (t) => { const el = document.getElementById('log'); if (el) el.textContent = `[S${state.stage} T${state.round}] ${t}\n` + el.textContent; };

/* 에러를 화면 로그에 바로 표시 */
window.onerror = function (message, source, lineno, colno) { log(`[JS ERROR] ${message} @ ${lineno}:${colno}`); };

/* ===== 효과 설명표 ===== */
const EFFECT_DESCS = {
    Hangul: '기본피해 + 같은 열의 나머지 모든 적 추가피해(+1, 20% 확률 +2)',
    Latin: '기본피해 + 2턴 DOT 1 (25% 확률 DOT 2)',
    Han: '기본피해 + 좌/우 열 전투타깃 및 같은 열에서 타깃 바로 뒤 1칸에도 동일 피해',
    Japanese: '요격: 해당 열 전투구역(0~2) 중 가장 뒤의 적을 기본피해로 타격 (타깃 기본피해 없음)',
    Sludge: '오물: 피해 1, 20% 자해/잠금(프로토타입)',
};

/* ===== 스크립트 판정 ===== */
function isAsciiPunctOrSpace(cp) {
    return (
        (cp >= 0x0000 && cp <= 0x002F) ||
        (cp >= 0x003A && cp <= 0x0040) ||
        (cp >= 0x005B && cp <= 0x0060) ||
        (cp >= 0x007B && cp <= 0x007E) ||
        (cp === 0x00A0)
    );
}
function isLatinLetter(cp) {
    if ((cp >= 0x0041 && cp <= 0x005A) || (cp >= 0x0061 && cp <= 0x007A)) return true;
    if ((cp >= 0x00C0 && cp <= 0x00FF) || (cp >= 0x0100 && cp <= 0x017F) || (cp >= 0x0180 && cp <= 0x024F) || (cp >= 0x1E00 && cp <= 0x1EFF)) return true;
    return false;
}
function scriptOf(cp) {
    if (isAsciiPunctOrSpace(cp)) return null;
    if (cp >= 0x0030 && cp <= 0x0039) return null;
    if (cp >= 0x2000 && cp <= 0x206F) return null;
    if ((cp >= 0xAC00 && cp <= 0xD7A3) || (cp >= 0x1100 && cp <= 0x11FF) || (cp >= 0x3130 && cp <= 0x318F)) return 'Hangul';
    if (isLatinLetter(cp)) return 'Latin';
    if ((cp >= 0x4E00 && cp <= 0x9FFF) || (cp >= 0x3400 && cp <= 0x4DBF)) return 'Han';
    if (cp >= 0x3040 && cp <= 0x309F) return 'Hiragana';
    if (cp >= 0x30A0 && cp <= 0x30FF) return 'Katakana';
    return 'Other';
}
function analyzeScripts(words) {
    const joined = words.join('|').normalize('NFC');
    const counts = { Hangul: 0, Latin: 0, Han: 0, Katakana: 0, Hiragana: 0, Other: 0 };
    for (let i = 0; i < joined.length;) {
        const cp = joined.codePointAt(i);
        const sc = scriptOf(cp);
        if (sc) { counts[sc] = (counts[sc] || 0) + 1; }
        i += cp > 0xFFFF ? 2 : 1;
    }
    const set = new Set();
    ['Hangul', 'Latin', 'Han', 'Hiragana', 'Katakana'].forEach(k => { if (counts[k] > 0) set.add(k); });
    return { counts, set, hasOther: counts.Other > 0, joined };
}
const detectJP = (set) => set.has('Hiragana') || set.has('Katakana');
/* ===== 포션 한도/사용 횟수 상수 & 헬퍼 ===== */
const BASE_POTION_CAP = 2;          // 턴당 생성/보유 가능 기본치
const BASE_PLAYS_PER_TURN = 2;      // 턴당 사용 가능 기본치

function getPotionCap() {
    return BASE_POTION_CAP + (state.potionCapBonus || 0);
}
function getPlaysPerTurn() {
    return BASE_PLAYS_PER_TURN + (state.potionPlayBonus || 0);
}

/* ===== 상태 ===== */
const MAX_COLS = 5;
/* 5칸: 0 Front, 1 Path1, 2 Path2, 3 Queue1, 4 Queue2 */
const ROWS = 5, COMBAT_ZONE = [0, 1, 2], QUEUE_ZONE = [3, 4];

const state = {
    // 런 시드 & 스테이지 변주
    runSeed: 0,
    stage: 1,
    stageMods: { hpScale: 1, dmgScale: 1, eliteBonus: 0 },
    laneBias: [0, 0, 0, 0, 0],

    round: 1,
    coreMax: 12, core: 12,

    energyMax: 6, energyGain: 4, energy: 4, // 턴당 +4
    potionCapBonus: 0,   // 유물 등으로 증가하는 '턴당 보유/생성 한도' 보너스
    potionPlayBonus: 0,  // 유물 등으로 증가하는 '턴당 사용 횟수' 보너스


    lanes: Array.from({ length: MAX_COLS }, () => ({ queue: [null, null, null, null, null], locked: false })),

    // 턴 당 포션 2장
    turnPotions: [],
    usedThisTurn: 0,
    potion: null,

    /* ★ 이번 스테이지에서 보스가 이미 소환되었는지 체크 */
    _bossSpawnedThisStage: false,

    /* ★ 유물 시스템 상태 */
    relics: [],                        // 보유 유물 목록
    _bossRelicOfferedThisStage: false,
};

/* ===== 타깃 유틸 ===== */
function getCombatIdx(lane) { for (const i of COMBAT_ZONE) { if (lane.queue[i]) return i; } return -1; }
function getCombatEnemy(lane) { const idx = getCombatIdx(lane); return idx >= 0 ? { enemy: lane.queue[idx], idx } : { enemy: null, idx: -1 }; }
function getBackmostCombatIdx(lane) { // 2→1→0
    for (let i = 2; i >= 0; i--) if (lane.queue[i]) return i;
    return -1;
}

/* ===== 적 모델/스폰 ===== */
function makeEnemy(baseType, variant, rng) {
    let hp = 5, dmg = 1, badge = '';
    if (baseType === 'basic') { hp = Math.floor(3 + rng() * 4); dmg = 1; }
    if (baseType === 'elite') { hp = Math.floor(7 + rng() * 6); dmg = (rng() < 0.5 ? 2 : 3); badge = 'elite'; }
    if (baseType === 'boss') { hp = Math.floor(20 + rng() * 10); dmg = Math.floor(3 + rng() * 3); badge = 'boss'; }

    if (variant === 'tank') { hp = Math.floor(hp * 1.35); dmg = Math.max(1, Math.floor(dmg * 0.6)); }
    else if (variant === 'skirm') { hp = Math.max(3, Math.floor(hp * 0.55)); dmg = Math.ceil(dmg * 1.4); }
    else if (variant === 'frenzy') { hp = Math.floor(hp * 0.8); dmg = dmg + 1; }

    hp = Math.ceil(hp * state.stageMods.hpScale);
    dmg = Math.max(1, Math.round(dmg * state.stageMods.dmgScale));

    return { type: baseType, variant, hp, dmg, badge, dot: null };
}


function pickEnemyType(wave, rng) {
    const baseElite = 0.10 + 0.02 * wave + state.stageMods.eliteBonus;
    const eliteProb = clamp(baseElite, 0, 0.6);
    return (rng() < eliteProb) ? 'elite' : 'basic';
}
function pickVariant(rng) {
    const r = rng();
    if (r < 0.20) return 'tank';
    if (r < 0.40) return 'skirm';
    if (r < 0.55) return 'frenzy';
    return 'normal';
}
function spawnEnemyForLane(lane, rng, wave) {
    if (lane.locked) { lane.locked = false; log(`열 스폰 잠금 해제`); return; }
    const q = lane.queue;
    if (q[4] !== null) return;
    const baseType = pickEnemyType(wave, rng);
    const variant = pickVariant(rng);
    const enemy = makeEnemy(baseType, variant, rng);
    for (let i = 4; i >= 3; i--) { if (q[i] == null) { q[i] = enemy; break; } }
}

/* ★ 스테이지 보스 강제 스폰(2라운드에, 7의 배수 스테이지) */
function spawnStageBoss(rng) {
    // Queue2(4) 우선, 가득 차면 Queue1(3)
    const candidates4 = [];
    const candidates3 = [];
    for (let c = 0; c < MAX_COLS; c++) {
        const q = state.lanes[c].queue;
        if (q[4] == null) candidates4.push(c);
        else if (q[3] == null) candidates3.push(c);
    }
    const pool = candidates4.length ? candidates4 : candidates3;
    if (pool.length === 0) {
        log('보스 스폰 실패: 모든 열의 대기열이 가득 찼습니다.');
        return false;
    }
    const col = pool[Math.floor(rng() * pool.length)];
    const q = state.lanes[col].queue;
    const slot = (q[4] == null ? 4 : 3);
    const boss = makeEnemy('boss', pickVariant(rng), rng);
    q[slot] = boss;
    log(`◎ 보스 등장: 스테이지 ${state.stage} / 라운드 ${state.round} / 열${col + 1} (${slot === 4 ? 'Queue2' : 'Queue1'})`);
    return true;
}

/* ===== 전개 & 공격/도트 처리 ===== */
function advanceAll() {
    for (const lane of state.lanes) {
        const q = lane.queue;
        for (let i = 0; i < ROWS - 1; i++) {
            if (q[i] == null && q[i + 1] != null) { q[i] = q[i + 1]; q[i + 1] = null; }
        }
    }
}
function enemyAttackPhase() {
    for (let c = 0; c < MAX_COLS; c++) {
        const e = state.lanes[c].queue[0];
        if (e) { state.core = Math.max(0, state.core - e.dmg); log(`적 공격: 열${c + 1} / 코어 -${e.dmg} (남은 ${state.core})`); }
    }
}
function dotResolvePhase() {
    for (let c = 0; c < MAX_COLS; c++) {
        const q = state.lanes[c].queue;
        for (let i = 0; i < ROWS; i++) {
            const e = q[i];
            if (e && e.dot && e.dot.turns > 0) {
                e.hp -= e.dot.value; e.dot.turns--;
                log(`DOT: 열${c + 1} 슬롯${i} -${e.dot.value} (HP ${e.hp})`);
                if (e.hp <= 0) { q[i] = null; log(`DOT 처치 @열${c + 1}/슬롯${i}`); }
            }
        }
    }
}
function killEnemyAt(col, idx) {
    const q = state.lanes[col].queue, e = q[idx]; if (!e) return;
    q[idx] = null; log(`적 처치: 열${col + 1} (${(e.badge ? e.badge.toUpperCase() : e.type.toUpperCase())}/${e.variant || 'normal'})`);

    // ★ 보스 처치 → 유물 선택 팝업 (스테이지당 1회)
    if (e.badge === 'boss' && !state._bossRelicOfferedThisStage) {
        state._bossRelicOfferedThisStage = true;
        openBossRelicPicker(); // (정의는 PART 3에 있음)
    }
}

/* ===== 스폰 선택(열/마릿수) — 런/스테이지 가중 랜덤 ===== */
function chooseSpawnColumns(rng) {
    const r = rng();
    let want = (r < 0.5 ? 1 : (r < 0.85 ? 2 : 3));
    const candidates = [];
    for (let c = 0; c < MAX_COLS; c++) {
        const q = state.lanes[c].queue;
        if (q[4] == null) candidates.push(c);
    }
    if (candidates.length === 0) return [];
    want = Math.min(want, candidates.length);

    const scored = candidates.map(c => {
        const noise = rng() * 0.4;
        const crowded = (state.lanes[c].queue[3] != null ? 0.35 : 0) + (state.lanes[c].queue[4] != null ? 0.35 : 0);
        const score = state.laneBias[c] + noise - crowded;
        return { c, score };
    }).sort((a, b) => b.score - a.score);

    return scored.slice(0, want).map(s => s.c);
}

/* ===== 턴 루프/스테이지 ===== */
function nextTurn() {
    advanceAll();

    const seed = fnv1a(`spawn|${state.stage}|${state.round}|${state.runSeed}`);
    const rng = xorshift(seed);

    /* ★ 조건: 스테이지 7의 배수 & 라운드 2 & 아직 미소환 → 보스 대기열 스폰 */
    if ((state.stage % 7 === 0) && state.round === 2 && !state._bossSpawnedThisStage) {
        spawnStageBoss(rng);
        state._bossSpawnedThisStage = true;
    }

    const cols = chooseSpawnColumns(rng);
    for (const c of cols) spawnEnemyForLane(state.lanes[c], rng, (state.round >= 10 ? 10 : state.round));

    state.energy = clamp(state.energy + state.energyGain, 0, state.energyMax);

    state.usedThisTurn = 0;
    state.turnPotions.length = 0;
    state.potion = null;

    for (let i = 0; i < state.laneBias.length; i++) {
        state.laneBias[i] = clamp(state.laneBias[i] + (rng() - 0.5) * 0.15, 0, 1);
    }

    updateUI();
    log(`— 턴 시작: 스폰 ${cols.map(c => c + 1).join(', ') || '없음'}, 에너지 +${state.energyGain}`);
}
function bossJumpNextTurn() {
    // 스테이지를 7의 배수로 맞춤 (현재보다 낮아지지 않게)
    if (state.stage % 7 !== 0) state.stage = Math.ceil(state.stage / 7) * 7;

    // 플래그 초기화 및 라운드 1로 세팅
    state._bossSpawnedThisStage = false;
    state._bossRelicOfferedThisStage = false;
    state.round = 1;

    updateUI();
    log('보스 테스트: 다음 턴에 보스가 등장합니다. (스테이지 ' + state.stage + ', 라운드 2 조건)');
}
document.addEventListener('keydown', (e) => {
    if (e.shiftKey && (e.key === ',' || e.key === '<')) {
        bossJumpNextTurn();
    }
});
document.addEventListener('keydown', (e) => {
    if (e.shiftKey && (e.key === '.' || e.key === '>')) {
        const seed = fnv1a(`filltest|${state.stage}|${state.round}|${state.runSeed}`);
        const rng = xorshift(seed);

        for (let c = 0; c < MAX_COLS; c++) {
            const lane = state.lanes[c];
            for (let i = 0; i < COMBAT_ZONE.length; i++) {
                const enemy = makeEnemy('basic', pickVariant(rng), rng);
                lane.queue[i] = enemy;
            }
        }

        updateUI();
        log('◎ 테스트: 전투구역 전체를 적으로 채웠습니다.');
    }
});
function endOfTurnResolve() {
    enemyAttackPhase();
    dotResolvePhase();

    if (state.round === 10) {
        log(`◎ 스테이지 ${state.stage} 클리어! 다음 스테이지로…`);
        toNextStage();
        updateUI();
        return;
    }

    state.round++;
    updateUI();
    if (state.core <= 0) { alert('패배! 코어 파괴'); resetGame(); return; }
}
function toNextStage() {
    state.stage++;
    state.round = 1;

    state.stageMods.hpScale = 1 + (state.stage - 1) * 0.08;
    state.stageMods.dmgScale = 1 + (state.stage - 1) * 0.06;
    state.stageMods.eliteBonus = 0.05 * (state.stage - 1);

    state.lanes = Array.from({ length: MAX_COLS }, () => ({ queue: [null, null, null, null, null], locked: false }));

    state.core = clamp(state.core + 3, 0, state.coreMax);

    const stSeed = fnv1a(`laneBias|${state.stage}|${state.runSeed}`);
    const stRng = xorshift(stSeed);
    for (let i = 0; i < state.laneBias.length; i++) {
        state.laneBias[i] = clamp((state.laneBias[i] * 0.6) + stRng() * 0.4, 0, 1);
    }

    state.energy = clamp(state.energy + 2, 0, state.energyMax);

    /* ★ 새 스테이지 진입 시 보스/유물 플래그 초기화 */
    state._bossSpawnedThisStage = false;
    state._bossRelicOfferedThisStage = false;

    /* ★ 유물 지속효과: 스테이지 시작 회복 */
    const stageHealer = state.relics.find(rr => rr.id === 'hardened_shell_stage_heal');
    if (stageHealer) {
        state.core = Math.min(state.coreMax, state.core + (stageHealer.heal || 2));
    }

    log(`▶ 스테이지 ${state.stage} 시작: hp×${state.stageMods.hpScale.toFixed(2)}, dmg×${state.stageMods.dmgScale.toFixed(2)}, elite+${(state.stageMods.eliteBonus * 100) | 0}%`);
}


/* ===== 포션 생성 ===== */
function makeName(main, sub) {
    const m = { Hangul: '서릿빛', Latin: '전격', Han: '석화', Japanese: '요격', Sludge: '오염' };
    return `【${sub ? m[main] + '·' + m[sub] : m[main]} 포션】`;
}
function describeEffect(main, sub) {
    const one = (s) => EFFECT_DESCS[s] || EFFECT_DESCS.Sludge;
    return sub ? `${one(main)} + ${one(sub)}(보조 약화)` : one(main);
}

/* ===== 포션 로직 수정 (유물 보정 포함) ===== */
function potionFrom(words) {
    const { counts, set, hasOther, joined } = analyzeScripts(words);
    const hasJP = detectJP(set);
    if (hasOther) return makeSludge(joined, '허용외 문자 포함');
    const k = set.size;
    if (k === 0) return null;
    if (k >= 3) return makeSludge(joined, '스크립트 3종 이상');

    const score = {
        Hangul: counts.Hangul || 0,
        Latin: counts.Latin || 0,
        Han: counts.Han || 0,
        Japanese: (counts.Hiragana || 0) + (counts.Katakana || 0)
    };
    const present = [];
    if (score.Hangul) present.push('Hangul');
    if (score.Latin) present.push('Latin');
    if (score.Han) present.push('Han');
    if (hasJP) present.push('Japanese');

    function firstIdxOfScript(s) {
        for (const w of words) {
            for (let i = 0; i < w.length;) {
                const cp = w.codePointAt(i);
                const sc = scriptOf(cp);
                const map = (sc === 'Hiragana' || sc === 'Katakana') ? 'Japanese' : sc;
                if (map === s) return 1;
                i += cp > 0xFFFF ? 2 : 1;
            }
        }
        return 0;
    }
    let main = null, sub = null;
    if (present.length === 1) main = present[0];
    else {
        present.sort((a, b) => {
            const d = (score[b] || 0) - (score[a] || 0);
            return d !== 0 ? d : (firstIdxOfScript(b) - firstIdxOfScript(a));
        });
        main = present[0];
        sub = present[1];
    }

    const seedBase = fnv1a(words.join('|').normalize('NFC')) ^
        (state.round * 2654435761 >>> 0) ^ state.runSeed ^ (state.stage * 0x9e3779b9);
    const rng = xorshift(seedBase);

    let cost = 2;
    if (sub && rng() < 0.10) cost = 3;
    let baseDmg = Math.floor((sub ? 2 : 3) + rng() * ((sub ? 4 : 5) - (sub ? 2 : 3) + 1));

    /* ★ 유물 보정: 증류 촉매(distill) */
    const distill = state.relics.find(r => r.id === 'distill_bonus');
    if (distill && distill.dmg) baseDmg += distill.dmg;

    return { seed: seedBase, rng, main, sub, type: (sub ? '듀얼' : '단일'), cost, baseDmg, isSludge: false, desc: describeEffect(main, sub) };
}
function makeSludge(joined, reason) {
    const seedBase = fnv1a(joined) ^ (state.round * 2654435761 >>> 0) ^ state.runSeed ^ (state.stage * 0x9e3779b9);
    return { seed: seedBase, rng: xorshift(seedBase), main: 'Sludge', sub: null, type: '오물', cost: 1, baseDmg: 1, isSludge: true, desc: `오물 포션 (${reason}) — 피해 1, 20% 자해/잠금(프로토타입)` };
}
/* ===== 포션 사용 전 공통 소비 처리 ===== */

function afterCastConsume() {
    // 이 턴 사용 카운트 증가
    state.usedThisTurn = (state.usedThisTurn || 0) + 1;

    // 대기 중 포션 큐에서 1장 소모
    if (Array.isArray(state.turnPotions) && state.turnPotions.length > 0) {
        state.turnPotions.shift();
    }

    // 다음 사용할 포션 업데이트
    state.potion = (state.turnPotions && state.turnPotions[0]) || null;
}

if (typeof window !== 'undefined') {
    window.afterCastConsume = afterCastConsume;
}
/* ===== 포션 사용 ===== */
function castPotionOnColumn(p, col) {
    if (!p) return;
    if (state.usedThisTurn >= getPlaysPerTurn()) {
        log(`이 턴에 더 이상 카드를 사용할 수 없습니다 (최대 ${getPlaysPerTurn()}장).`);
        return;
    }
    if (state.energy < p.cost) { log(`에너지 부족: 필요 ${p.cost}`); return; }
    state.energy = Math.max(0, state.energy - p.cost);

    const lane = state.lanes[col];
    const { enemy: eTarget, idx: ti } = getCombatEnemy(lane);

    // ✅ 메인/보조가 공유할 앵커 인덱스를 시전 직전에 고정
    const anchorIdx = (p.main === 'Japanese')
        ? getBackmostCombatIdx(lane)                      // 일본어: 전투구역의 뒤쪽
        : (ti >= 0 ? ti : getCombatIdx(lane));            // 그 외: 전투구역의 맨 앞

    if (p.isSludge) {
        if (eTarget) { eTarget.hp -= 1; if (eTarget.hp <= 0) killEnemyAt(col, ti); }
        if (p.rng() < 0.2) { state.core = Math.max(0, state.core - 1); log(`오물 반동! 코어 -1 (남은 ${state.core})`); }
        log(`오물 포션: 열${col + 1} 슬롯${ti >= 0 ? ti : '-'} -1`);
        afterCastConsume(); updateUI(); return;
    }

    if (p.main !== 'Japanese') {
        if (!eTarget) { log(`타깃 없음: 열${col + 1}에 전투 가능한 적이 없습니다.`); afterCastConsume(); updateUI(); return; }
        eTarget.hp -= p.baseDmg;
        log(`${p.type} ${p.main}${p.sub ? '/' + p.sub : ''}: 열${col + 1} 슬롯${anchorIdx} -${p.baseDmg} (HP ${Math.max(0, eTarget.hp)})`);
        if (eTarget.hp <= 0) killEnemyAt(col, anchorIdx);
    } else {
        log(`${p.type} ${p.main}${p.sub ? '/' + p.sub : ''}: 기본 타격은 요격 규칙으로 대체`);
    }

    // ✅ 고정된 anchorIdx로 메인/보조 모두 호출
    applyMainEffect(p.main, col, p.baseDmg, p, anchorIdx);
    if (p.sub) applySubEffect(p.sub, col, p.baseDmg, p, anchorIdx);

    afterCastConsume();
    updateUI();
}

/* ===== 메인 효과 ===== */
function applyMainEffect(kind, col, base, p, combatIdx) {
    const lane = state.lanes[col];

    if (kind === 'Hangul') {
        const add = (p.rng() < 0.2) ? 2 : 1;
        for (let i = 0; i < ROWS; i++) {
            if (i === combatIdx) continue;
            const e = lane.queue[i];
            if (e) {
                e.hp -= add;
                log(`한글 확장피해: 열${col + 1} 슬롯${i} -${add} (HP ${Math.max(0, e.hp)})`);
                if (e.hp <= 0) { lane.queue[i] = null; log(`처치(한글 확장) @열${col + 1}/슬롯${i}`); }
            }
        }
        return;
    }

    if (kind === 'Latin') {
        const idx = combatIdx >= 0 ? combatIdx : getCombatIdx(lane);
        if (idx >= 0) {
            const e = lane.queue[idx];
            if (e) {
                const v = (p.rng() < 0.40) ? 2 : 1;
                e.dot = { value: v, turns: 2 };
                log(`라틴 DOT: 열${col + 1} 슬롯${idx} DOT${v}x2T`);
            }
        }
        return;
    }

    if (kind === 'Han') {
        for (const dc of [-1, +1]) {
            const cc = col + dc;
            if (cc < 0 || cc >= MAX_COLS) continue;
            const ni = getCombatIdx(state.lanes[cc]);
            if (ni >= 0) {
                const ne = state.lanes[cc].queue[ni];
                if (ne) {
                    ne.hp -= base;
                    log(`한자 확산(좌/우): 열${cc + 1} 슬롯${ni} -${base} (HP ${Math.max(0, ne.hp)})`);
                    if (ne.hp <= 0) killEnemyAt(cc, ni);
                }
            }
        }
        if (combatIdx >= 0) {
            const bi = combatIdx + 1;
            if (bi < ROWS) {
                const be = lane.queue[bi];
                if (be) {
                    be.hp -= base;
                    log(`한자 추가(후열): 열${col + 1} 슬롯${bi} -${base} (HP ${Math.max(0, be.hp)})`);
                    if (be.hp <= 0) killEnemyAt(col, bi);
                }
            }
        }
        return;
    }

    if (kind === 'Japanese') {
        const bi = getBackmostCombatIdx(lane);
        if (bi >= 0) {
            const e = lane.queue[bi];
            e.hp -= base;
            log(`일본어 요격: 열${col + 1} 슬롯${bi} -${base} (HP ${Math.max(0, e.hp)})`);
            if (e.hp <= 0) killEnemyAt(col, bi);
        } else {
            log(`일본어 요격: 전투구역에 적 없음`);
        }
        return;
    }
}

/* ===== 보조 효과 (Han에 fallback 추가, Latin 로그 정합) ===== */
function applySubEffect(kind, col, base, p, combatIdx) {
    const lane = state.lanes[col];

    if (kind === 'Hangul') {
        if (p.rng() < 0.6) {
            for (let i = 0; i < ROWS; i++) {
                if (i === combatIdx) continue;
                const e = lane.queue[i];
                if (e) {
                    e.hp -= 1;
                    log(`보조(한글) 여진: 열${col + 1} 슬롯${i} -1 (HP ${Math.max(0, e.hp)})`);
                    if (e.hp <= 0) { lane.queue[i] = null; }
                }
            }
        }

    } else if (kind === 'Latin') {
        const idx = (combatIdx >= 0) ? combatIdx : getCombatIdx(lane);
        if (idx >= 0 && p.rng() < 0.30) {
            const e = lane.queue[idx];
            if (e) {
                e.dot = { value: 1, turns: 2 };
                log(`보조(라틴) DOT1x2T (30%) @열${col + 1}/슬롯${idx}`);
            }
        }

    } else if (kind === 'Han') {
        // ✅ combatIdx가 없으면 현재 전투구역 맨앞을 기준으로 대체
        const baseIdx = (combatIdx >= 0) ? combatIdx : getCombatIdx(lane);
        if (baseIdx >= 0) {
            const bi = baseIdx + 1;
            if (p.rng() < 0.5 && bi >= 0 && bi < ROWS) {
                const be = lane.queue[bi];
                if (be) {
                    be.hp -= base;
                    log(`보조(한자) 후열추가: 열${col + 1} 슬롯${bi} -${base} (HP ${Math.max(0, be.hp)})`);
                    if (be.hp <= 0) killEnemyAt(col, bi);
                }
            }
        }

    } else if (kind === 'Japanese') {
        const bi = getBackmostCombatIdx(lane);
        if (bi >= 0) {
            const e = lane.queue[bi];
            const dmg = Math.floor(base / 2);
            if (dmg > 0 && e) {
                e.hp -= dmg;
                log(`보조(일본어) 약화요격: 열${col + 1} 슬롯${bi} -${dmg} (HP ${Math.max(0, e.hp)})`);
                if (e.hp <= 0) killEnemyAt(col, bi);
            }
        }
    }
}


/* ===== UI (Grid & Potion Panel) ===== */
function renderGrid() {
    const grid = document.getElementById('grid'); if (!grid) return;
    grid.innerHTML = '';

    for (let c = 0; c < MAX_COLS; c++) {
        const col = document.createElement('div'); col.className = 'col';

        const h3 = document.createElement('h3');
        const left = document.createElement('span'); left.textContent = `열 ${c + 1}`;
        const right = document.createElement('span'); right.className = 'mini'; right.textContent = state.lanes[c].locked ? '🔒 잠금' : ' ';
        h3.appendChild(left); h3.appendChild(right); col.appendChild(h3);

        const lane = document.createElement('div'); lane.className = 'lane';
        for (let r = 0; r < ROWS; r++) {
            const slot = document.createElement('div');
            let cls = 'queue'; if (r === 0) cls = 'front'; else if (r === 1 || r === 2) cls = 'path';
            slot.className = 'slot ' + cls;

            const label = document.createElement('div');
            label.style.position = 'absolute'; label.style.top = '2px'; label.style.right = '4px';
            label.style.fontSize = '10px'; label.style.color = '#555';
            label.textContent = (r === 0 ? 'Front' : r <= 2 ? `Path${r}` : `Queue${r - 2}`);
            slot.appendChild(label);

            const e = state.lanes[c].queue[r];
            if (e) {
                const enemy = document.createElement('div'); enemy.className = 'enemy';
                const hp = document.createElement('div'); hp.className = 'hp'; hp.textContent = `HP ${e.hp}`;
                const info = document.createElement('div'); info.className = 'mini'; info.textContent = `DMG ${e.dmg}` + (e.dot ? ` · DOT${e.dot.value}x${e.dot.turns}` : '');
                const badge = document.createElement('div'); badge.className = 'badge ' + (e.badge || ''); badge.textContent = e.badge ? (`${e.badge.toUpperCase()}`) : 'BASIC';
                const sub = document.createElement('div'); sub.className = 'mini'; sub.textContent = e.variant && e.variant !== 'normal' ? `(${e.variant})` : '';
                enemy.appendChild(hp); enemy.appendChild(info); enemy.appendChild(sub);
                slot.appendChild(badge); slot.appendChild(enemy);
            }
            lane.appendChild(slot);
        }

        const ctr = document.createElement('div'); ctr.className = 'controls';
        const btn = document.createElement('button'); btn.className = 'btn';
        const playsLeftGrid = Math.max(0, getPlaysPerTurn() - state.usedThisTurn);
        btn.textContent = (playsLeftGrid > 0 ? `여기에 사용 (${playsLeftGrid}장 남음)` : `사용 불가`);
        btn.disabled = !state.potion || playsLeftGrid <= 0 || state.energy < (state.potion ? state.potion.cost : 999);
        btn.onclick = () => castPotionOnColumn(state.potion, c);
        ctr.appendChild(btn);

        col.appendChild(lane); col.appendChild(ctr); grid.appendChild(col);
    }
}


// 매일 같은 '시'에 같은 결과를 주기 위한 키
function currentHourKey() {
    try { return new Date().getHours(); } catch (e) { return 0; }
}

// 이름(NFC) + 시간(시) → 결정적 코스트/계수
function deriveRelicTuning(name, hour) {
    const base = (name || '').normalize('NFC');
    const seed = fnv1a(base) ^ ((hour & 0xff) * 2654435761 >>> 0);
    const rng = xorshift(seed);

    const cost = 1 + Math.floor(rng() * 3); // 1~3
    const coeffs = {
        dmgFlat: Math.floor(rng() * 2),            // {0,1}
        energyCapBonus: Math.floor(rng() * 3),     // {0,1,2}
        energyGainBonus: (rng() < 0.5 ? 0 : 1),    // 0 or 1
        coreMaxBonus: Math.floor(rng() * 5),       // {0..4}
        coreHealInstant: Math.floor(rng() * 4),    // {0..3}
    };
    return { cost, coeffs, seed };
}

// 현재 보유 유물의 총 코스트
function totalRelicCost() {
    return state.relics.reduce((s, r) => s + (r.cost || 0), 0);
}

// 유물 풀(베이스 효과)
const RELIC_POOL = [
    {
        id: 'core_cap',
        name: '코어 증폭기',
        desc: '코어 최대치 +4, 즉시 +4 회복',
        apply(base, tuneName, tune) {
            const addCap = 4 + tune.coeffs.coreMaxBonus;     // 4~8
            const heal = 4 + tune.coeffs.coreHealInstant;  // 4~7
            state.coreMax += addCap;
            state.core = Math.min(state.coreMax, state.core + heal);
            state.relics.push({ id: base.id, name: tuneName, cost: tune.cost, seed: tune.seed });
            log(`유물 획득: ${tuneName} (코스트 ${tune.cost}) / 코어 최대 +${addCap}, 즉시 +${heal}`);
        }
    },
    {
        id: 'overclock',
        name: '오버클록 플라스크',
        desc: '에너지 상한 +2, 턴당 +1',
        apply(base, tuneName, tune) {
            const cap = 2 + tune.coeffs.energyCapBonus;     // 2~4
            const gain = 1 + tune.coeffs.energyGainBonus;    // 1~2
            state.energyMax += cap;
            state.energyGain += gain;
            state.relics.push({ id: base.id, name: tuneName, cost: tune.cost, seed: tune.seed });
            log(`유물 획득: ${tuneName} (코스트 ${tune.cost}) / 에너지 상한 +${cap}, 턴당 +${gain}`);
        }
    },
    {
        id: 'swift_path',
        name: '신속 경로',
        desc: '즉시 에너지 +1',
        apply(base, tuneName, tune) {
            const instant = 1 + (tune.coeffs.energyGainBonus ? 1 : 0); // 1~2
            state.energy = Math.min(state.energyMax, state.energy + instant);
            state.relics.push({ id: base.id, name: tuneName, cost: tune.cost, seed: tune.seed });
            log(`유물 획득: ${tuneName} (코스트 ${tune.cost}) / 즉시 에너지 +${instant}`);
        }
    },
    {
        id: 'hardened_shell',
        name: '강화 외골격',
        desc: '스테이지 시작 회복 +2',
        apply(base, tuneName, tune) {
            const addCap = 2 + Math.floor(tune.coeffs.coreMaxBonus / 2); // 2~4
            const healOnStage = 2 + Math.floor(tune.coeffs.coreHealInstant / 2); // 2~3
            state.coreMax += addCap;
            state.relics.push({ id: 'hardened_shell_stage_heal', heal: healOnStage });
            state.relics.push({ id: base.id, name: tuneName, cost: tune.cost, seed: tune.seed });
            log(`유물 획득: ${tuneName} (코스트 ${tune.cost}) / 코어 최대 +${addCap}, 스테이지 시작마다 +${healOnStage}`);
        }
    },
    {
        id: 'distill',
        name: '증류 촉매',
        desc: '포션 기본피해 +1',
        apply(base, tuneName, tune) {
            const dmg = 1 + tune.coeffs.dmgFlat; // 1~2
            state.relics.push({ id: 'distill_bonus', dmg });
            state.relics.push({ id: base.id, name: tuneName, cost: tune.cost, seed: tune.seed });
            log(`유물 획득: ${tuneName} (코스트 ${tune.cost}) / 포션 기본피해 +${dmg}`);
        }
    },
    {
        id: 'potion_bandolier',
        name: '증강 밴돌리어',
        desc: '턴당 생성 한도 +1, 사용 횟수 +1',
        apply(base, tuneName, tune) {
            // 고정 +1 (가변/가중치 없음)
            state.potionCapBonus = (state.potionCapBonus || 0) + 1;
            state.potionPlayBonus = (state.potionPlayBonus || 0) + 1;

            state.relics.push({ id: base.id, name: tuneName, cost: tune.cost, seed: tune.seed });
            log(`유물 획득: ${tuneName} (코스트 ${tune.cost}) / 생성 한도 +1, 사용 +1 → 현재 생성 ${getPotionCap()}개, 사용 ${getPlaysPerTurn()}장`);
        }
    }


];

// 후보 3개(결정적) 생성
function genBossRelicChoices() {
    const seed = fnv1a(`relic|${state.stage}|${state.runSeed}|${state.round}`);
    const rng = xorshift(seed);
    const idxs = Array.from({ length: RELIC_POOL.length }, (_, i) => i);
    for (let i = idxs.length - 1; i > 0; i--) {
        const j = Math.floor(rng() * (i + 1));
        [idxs[i], idxs[j]] = [idxs[j], idxs[i]];
    }
    return idxs.slice(0, 3).map(i => RELIC_POOL[i]);
}

// 모달 열기/닫기
function openBossRelicPicker() {
    const modal = document.getElementById('relicModal');
    const scrim = document.getElementById('relicScrim');
    if (!modal || !scrim) { log('유물 모달 요소를 찾을 수 없습니다.'); return; }

    const picks = genBossRelicChoices();
    const cards = modal.querySelectorAll('.rel-card');

    cards.forEach((btn, i) => {
        const r = picks[i];
        const nameEl = btn.querySelector('.rel-name');
        const descEl = btn.querySelector('.rel-desc');
        const input = btn.querySelector('.rel-input');

        nameEl.textContent = r.name;
        descEl.textContent = r.desc;

        // 버튼 클릭: 입력란을 클릭한 경우는 무시
        const choose = (customName) => {
            const hour = currentHourKey();
            const tune = deriveRelicTuning(customName, hour);
            const newTotal = totalRelicCost() + tune.cost;
            if (newTotal > 10) { log(`유물 코스트 초과: 현재 ${totalRelicCost()} + ${tune.cost} > 10`); return; }
            r.apply(r, customName, tune);
            updateUI();
            closeBossRelicPicker();
        };

        btn.addEventListener('click', (ev) => {
            if (ev.target && ev.target.closest('.rel-input')) return; // 입력란 클릭은 선택 취급 X
            const customName = (input && input.value.trim()) || r.name;
            choose(customName);
        });

        // 입력란: 클릭/포커스 시 버블링 차단 (버튼으로 올라가지 않게)
        if (input) {
            const stop = (e) => e.stopPropagation();
            input.addEventListener('click', stop);
            input.addEventListener('mousedown', stop);
            input.addEventListener('mouseup', stop);
            input.addEventListener('touchstart', stop);
            input.addEventListener('touchend', stop);
            input.addEventListener('keydown', (e) => {
                e.stopPropagation();
                if (e.key === 'Enter') {
                    e.preventDefault();
                    const customName = input.value.trim() || r.name;
                    choose(customName); // Enter로 바로 선택 허용
                }
            });
        }
    });

    scrim.style.display = 'block';
    modal.style.display = 'block';
    scrim.onclick = null; // 강제 선택 유지(필요하면 닫기 허용 가능)
}

function closeBossRelicPicker() {
    const modal = document.getElementById('relicModal');
    const scrim = document.getElementById('relicScrim');
    if (!modal || !scrim) return;
    modal.style.display = 'none';
    scrim.style.display = 'none';
}

/* ===== 상단 바 & 포션 패널 ===== */
function updateTopBars() {
    document.getElementById('roundTxt').textContent = `라운드 ${state.round} (스테이지 ${state.stage})`;
    document.getElementById('coreTxt').textContent = state.core;
    document.getElementById('coreBar').style.width = (state.core / state.coreMax * 100) + '%';
    document.getElementById('energyTxt').textContent = `에너지 ${state.energy} / ${state.energyMax}`;
    document.getElementById('energyBar').style.width = (state.energy / state.energyMax * 100) + '%';
}
function showPotion(p) {
    const box = document.getElementById('potionView');
    if (!box) return;

    const playsLeft = Math.max(0, getPlaysPerTurn() - state.usedThisTurn);

    function wirePanelButtons(enabled) {
        box.querySelectorAll('[data-cast]').forEach(btn => {
            const col = parseInt(btn.dataset.cast, 10);
            btn.textContent = `열 ${col + 1}`;
            btn.disabled = !enabled;
            btn.onclick = enabled ? (() => castPotionOnColumn(state.potion, col)) : null;
        });
    }

    if (!p) {
        box.style.display = 'block';
        document.getElementById('potionName').textContent = '(포션 없음)';
        document.getElementById('pMain').textContent = '메인: -';
        document.getElementById('pSub').textContent = '보조: -';
        document.getElementById('pType').textContent = '타입: -';
        document.getElementById('pCost').textContent = '코스트: -';
        document.getElementById('pDmg').textContent = '기본피해: -';
        document.getElementById('potionDesc').textContent = '이 턴에는 최대 2장까지 생성/사용할 수 있습니다. (턴당 에너지 +4)';
        wirePanelButtons(false);
        return;
    }

    box.style.display = 'block';
    const waiting = state.turnPotions.length > 1 ? ` (대기 ${state.turnPotions.length - 1}장)` : '';
    document.getElementById('potionName').textContent = makeName(p.main, p.sub) + waiting;
    document.getElementById('pMain').textContent = `메인: ${p.main}`;
    document.getElementById('pSub').textContent = p.sub ? `보조: ${p.sub}` : '보조: 없음';
    document.getElementById('pType').textContent = `타입: ${p.type}`;
    document.getElementById('pCost').textContent = `코스트: ${p.cost}`;
    document.getElementById('pDmg').textContent = `기본피해: ${p.baseDmg}`;
    document.getElementById('potionDesc').textContent = EFFECT_DESCS[p.main] + (p.sub ? ' + ' + EFFECT_DESCS[p.sub] + ' (보조 약화)' : '');
    const canPlay = !!state.potion && playsLeft > 0 && state.energy >= p.cost;
    wirePanelButtons(canPlay);
}
function updateLangDebug() {
    const w1 = document.getElementById('w1').value || '';
    const w2 = document.getElementById('w2').value || '';
    const w3 = document.getElementById('w3').value || '';
    const { counts, set, hasOther } = analyzeScripts([w1, w2, w3]);
    const parts = [];
    ['Hangul', 'Latin', 'Han', 'Hiragana', 'Katakana'].forEach(k => { if (counts[k] > 0) parts.push(`${k}(${counts[k]})`); });
    const s = `감지된: ${parts.join(' + ') || '없음'}  |  상태: ` +
        (hasOther ? '오물(허용 외 문자)' : (set.size === 0 ? '무효' : (set.size <= 2 ? `정상 조합 (${set.size}/2)` : '오물(3종 이상)')));
    document.getElementById('langInfo').textContent = s;
}
function updateUI() { renderGrid(); updateTopBars(); showPotion(state.potion); }

/* ===== 이벤트 ===== */
document.getElementById('genBtn').onclick = () => {
    if (state.turnPotions.length >= getPotionCap()) {
        log(`이 턴에 더 이상 포션을 생성할 수 없습니다 (최대 ${getPotionCap()}개).`);
        return;
    }
    const p = potionFrom([
        document.getElementById('w1').value || '',
        document.getElementById('w2').value || '',
        document.getElementById('w3').value || '',
    ]);
    if (!p) { log('유효한 입력이 없습니다.'); return; }

    state.turnPotions.push(p);
    if (!state.potion) state.potion = state.turnPotions[0];
    showPotion(state.potion);
    log(`포션 생성(${state.turnPotions.length}/${getPotionCap()}): ${makeName(p.main, p.sub)} | 코스트 ${p.cost} | 기본피해 ${p.baseDmg}`);
    updateUI();
};
document.getElementById('turnBtn').onclick = () => { endOfTurnResolve(); nextTurn(); };
document.getElementById('resetBtn').onclick = resetGame;
['w1', 'w2', 'w3'].forEach(id => document.getElementById(id).addEventListener('input', updateLangDebug));
/* ===== 유물 리스트 바텀시트 ===== */
(function setupRelicSheet() {
    const sheet = document.getElementById('relicSheet');
    const btnToggle = document.getElementById('relicToggleBtn');
    const btnClose = document.getElementById('relicCloseBtn');
    const handle = document.getElementById('relicSheetHandle');
    const listEl = document.getElementById('relicList');
    const sumEl = document.getElementById('relicCostSum');

    if (!sheet || !btnToggle || !btnClose || !handle || !listEl || !sumEl) return;

    function openSheet() { sheet.classList.add('open'); sheet.setAttribute('aria-hidden', 'false'); }
    function closeSheet() { sheet.classList.remove('open'); sheet.setAttribute('aria-hidden', 'true'); }

    function renderRelicList() {
        listEl.innerHTML = '';
        let costSum = 0;


        // 화면엔 "플레이어가 실제로 획득한 유물(id가 풀에 등록된 것)"만 보여주자.
        const visible = state.relics.filter(r => {
            // 풀 유물 id 집합과 매칭
            return ['core_cap', 'overclock', 'swift_path', 'hardened_shell', 'distill', 'potion_bandolier'].includes(r.id);
        });

        for (const r of visible) {
            costSum += (r.cost || 0);
            const li = document.createElement('li');
            li.className = 'relic-item';

            const left = document.createElement('div');
            const name = document.createElement('div');
            name.className = 'relic-name';
            name.textContent = r.name || '(이름 없음)';

            const meta = document.createElement('div');
            meta.className = 'relic-meta';
            // 간단 설명: id 기반
            meta.textContent =
                r.id === 'core_cap' ? '코어 최대/회복 강화'
                    : r.id === 'overclock' ? '에너지 상한/수급 강화'
                        : r.id === 'swift_path' ? '즉시 에너지'
                            : r.id === 'hardened_shell' ? '스테이지 시작 회복'
                                : r.id === 'distill' ? '포션 기본피해 +'
                                    : r.id === 'potion_bandolier' ? '생성/사용 +1'
                                        : '유물';

            left.appendChild(name);
            left.appendChild(meta);

            const right = document.createElement('div');
            const costBadge = document.createElement('span');
            costBadge.className = 'relic-cost';
            costBadge.textContent = `Cost ${r.cost || 0}`;
            right.appendChild(costBadge);

            li.appendChild(left);
            li.appendChild(right);
            listEl.appendChild(li);
        }

        sumEl.textContent = costSum.toString();
    }


    handle.addEventListener('click', () => {
        if (sheet.classList.contains('open')) closeSheet(); else openSheet();
    });
    btnToggle.addEventListener('click', () => { renderRelicList(); openSheet(); });
    btnClose.addEventListener('click', closeSheet);


    window.renderRelicList = renderRelicList;
})();



/* ===== 초기화 & 런 시드 ===== */
function initRunSeed() {
    try {
        const buf = new Uint32Array(1);
        (crypto || window.msCrypto).getRandomValues(buf);
        state.runSeed = buf[0] >>> 0;
    } catch (e) {
        state.runSeed = (Math.random() * 0xFFFFFFFF) >>> 0;
    }
    const rng = xorshift(fnv1a(`laneBias|${state.runSeed}`));
    for (let i = 0; i < state.laneBias.length; i++) state.laneBias[i] = rng();
}
function resetGame() {
    initRunSeed();
    state.stage = 1;
    state.stageMods = { hpScale: 1, dmgScale: 1, eliteBonus: 0 };
    state.round = 1; state.core = state.coreMax; state.energy = state.energyGain;
    state.lanes = Array.from({ length: MAX_COLS }, () => ({ queue: [null, null, null, null, null], locked: false }));
    state.turnPotions.length = 0; state.usedThisTurn = 0; state.potion = null;
    state._bossSpawnedThisStage = false;
    state._bossRelicOfferedThisStage = false;
    document.getElementById('log').textContent = '';
    updateLangDebug(); updateUI(); nextTurn();
}

resetGame();

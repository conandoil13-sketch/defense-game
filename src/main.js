/* ===== 유틸 ===== */
function fnv1a(str) { let h = 0x811c9dc5; for (const ch of str) { h ^= ch.codePointAt(0); h = (h >>> 0) * 0x01000193; } return h >>> 0; }
function xorshift(seed) { let x = seed >>> 0 || 123456789; return () => { x ^= (x << 13); x >>>= 0; x ^= (x >>> 17); x >>>= 0; x ^= (x << 5); x >>>= 0; return (x >>> 0) / 0xFFFFFFFF; }; }
const clamp = (n, a, b) => Math.max(a, Math.min(b, n));
const log = (t) => { const el = document.getElementById('log'); if (el) el.textContent = `[S${state.stage} T${state.round}] ${t}\n` + el.textContent; };

/* 에러를 화면 로그에 바로 표시 */
window.onerror = function (message, source, lineno, colno) { log(`[JS ERROR] ${message} @ ${lineno}:${colno}`); };

/* ===== 효과 설명표 (단 한 번만 선언) ===== */
const EFFECT_DESCS = {
    Hangul: '기본피해 + 같은 열의 나머지 모든 적 추가피해(+1, 20% 확률 +2)',
    Latin: '기본피해 + 2턴 DOT 1 (25% 확률 DOT 2)',
    Han: '기본피해 + 좌/우 열 전투타깃 및 같은 열에서 타깃 바로 뒤 1칸에도 동일 피해',
    Japanese: '요격: 해당 열 전투구역(0~2) 중 가장 뒤의 적을 기본피해로 타격 (타깃 기본피해 없음)',
    Sludge: '오물: 피해 1, 20% 자해/잠금(프로토타입)',
};

/* ===== 스크립트 판정 (라틴 오탐 FIX) ===== */
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

    lanes: Array.from({ length: MAX_COLS }, () => ({ queue: [null, null, null, null, null], locked: false })),

    // 턴 당 포션 2장
    turnPotions: [],
    usedThisTurn: 0,
    potion: null,
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
    if (wave === 10) return 'boss';
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
}

/* ===== 포션 생성 ===== */
function makeName(main, sub) { const m = { Hangul: '서릿빛', Latin: '전격', Han: '석화', Japanese: '요격', Sludge: '오염' }; return `【${sub ? m[main] + '·' + m[sub] : m[main]} 포션】`; }
function describeEffect(main, sub) { const one = (s) => EFFECT_DESCS[s] || EFFECT_DESCS.Sludge; return sub ? `${one(main)} + ${one(sub)}(보조 약화)` : one(main); }

function potionFrom(words) {
    const { counts, set, hasOther, joined } = analyzeScripts(words);
    const hasJP = detectJP(set);
    if (hasOther) return makeSludge(joined, '허용외 문자 포함');
    const k = set.size; if (k === 0) return null; if (k >= 3) return makeSludge(joined, '스크립트 3종 이상');

    const score = { Hangul: counts.Hangul || 0, Latin: counts.Latin || 0, Han: counts.Han || 0, Japanese: (counts.Hiragana || 0) + (counts.Katakana || 0) };
    const present = []; if (score.Hangul) present.push('Hangul'); if (score.Latin) present.push('Latin'); if (score.Han) present.push('Han'); if (hasJP) present.push('Japanese');

    function firstIdxOfScript(s) {
        for (const w of words) { for (let i = 0; i < w.length;) { const cp = w.codePointAt(i); const sc = scriptOf(cp); const map = (sc === 'Hiragana' || sc === 'Katakana') ? 'Japanese' : sc; if (map === s) return 1; i += cp > 0xFFFF ? 2 : 1; } }
        return 0;
    }
    let main = null, sub = null;
    if (present.length === 1) { main = present[0]; }
    else {
        present.sort((a, b) => { const d = (score[b] || 0) - (score[a] || 0); return d !== 0 ? d : (firstIdxOfScript(b) - firstIdxOfScript(a)); });
        main = present[0]; sub = present[1];
    }

    const seedBase = fnv1a(words.join('|').normalize('NFC')) ^ (state.round * 2654435761 >>> 0) ^ state.runSeed ^ (state.stage * 0x9e3779b9);
    const rng = xorshift(seedBase);

    let cost = 2; if (sub && rng() < 0.10) cost = 3;
    const baseDmg = Math.floor((sub ? 2 : 3) + rng() * ((sub ? 4 : 5) - (sub ? 2 : 3) + 1));
    return { seed: seedBase, rng, main, sub, type: (sub ? '듀얼' : '단일'), cost, baseDmg, isSludge: false, desc: describeEffect(main, sub) };
}
function makeSludge(joined, reason) {
    const seedBase = fnv1a(joined) ^ (state.round * 2654435761 >>> 0) ^ state.runSeed ^ (state.stage * 0x9e3779b9);
    return { seed: seedBase, rng: xorshift(seedBase), main: 'Sludge', sub: null, type: '오물', cost: 1, baseDmg: 1, isSludge: true, desc: `오물 포션 (${reason}) — 피해 1, 20% 자해/잠금(프로토타입)` };
}

/* ===== 효과 적용 ===== */
function castPotionOnColumn(p, col) {
    if (!p) return;
    if (state.usedThisTurn >= 2) { log('이 턴에 더 이상 카드를 사용할 수 없습니다 (최대 2장).'); return; }
    if (state.energy < p.cost) { log(`에너지 부족: 필요 ${p.cost}`); return; }
    state.energy = Math.max(0, state.energy - p.cost);

    const lane = state.lanes[col];
    const { enemy: eTarget, idx: ti } = getCombatEnemy(lane); // 0→1→2 중 맨앞

    // 오물
    if (p.isSludge) {
        if (eTarget) { eTarget.hp -= 1; if (eTarget.hp <= 0) killEnemyAt(col, ti); }
        if (p.rng() < 0.2) { state.core = Math.max(0, state.core - 1); log(`오물 반동! 코어 -1 (남은 ${state.core})`); }
        log(`오물 포션: 열${col + 1} 슬롯${ti >= 0 ? ti : '-'} -1`);
        afterCastConsume(); updateUI(); return;
    }

    // 일본어는 '요격'이므로 기본 타깃에 기본피해를 주지 않고, applyMainEffect에서 별도 타격
    if (p.main !== 'Japanese') {
        if (!eTarget) { log(`타깃 없음: 열${col + 1}에 전투 가능한 적이 없습니다.`); afterCastConsume(); updateUI(); return; }
        eTarget.hp -= p.baseDmg;
        log(`${p.type} ${p.main}${p.sub ? '/' + p.sub : ''}: 열${col + 1} 슬롯${ti} -${p.baseDmg} (HP ${Math.max(0, eTarget.hp)})`);
        if (eTarget.hp <= 0) killEnemyAt(col, ti);
    } else {
        // 일본어 메인일 때, 타깃 없어도 applyMainEffect에서 뒤쪽 요격을 시도
        log(`${p.type} ${p.main}${p.sub ? '/' + p.sub : ''}: 기본 타격은 요격 규칙으로 대체`);
    }

    applyMainEffect(p.main, col, p.baseDmg, p, ti);
    if (p.sub) applySubEffect(p.sub, col, p.baseDmg, p, ti);

    afterCastConsume();
    updateUI();
}
function afterCastConsume() {
    state.usedThisTurn++;
    if (state.turnPotions.length > 0) state.turnPotions.shift();
    state.potion = state.turnPotions[0] || null;
}

/* ===== 메인 효과 구현 ===== */
function applyMainEffect(kind, col, base, p, combatIdx) {
    const lane = state.lanes[col];

    if (kind === 'Hangul') {
        // 타깃을 제외한 같은 열의 모든 적에게 추가 피해 (+1, 20% 확률 +2)
        const add = (p.rng() < 0.2) ? 2 : 1;
        for (let i = 0; i < ROWS; i++) {
            if (i === combatIdx) continue;
            const e = lane.queue[i];
            if (e) { e.hp -= add; log(`한글 확장피해: 열${col + 1} 슬롯${i} -${add} (HP ${Math.max(0, e.hp)})`); if (e.hp <= 0) { lane.queue[i] = null; log(`처치(한글 확장) @열${col + 1}/슬롯${i}`); } }
        }

    } else if (kind === 'Latin') {
        // DOT 부여 (타깃 기준)
        const idx = combatIdx >= 0 ? combatIdx : getCombatIdx(lane);
        if (idx >= 0) {
            const e = lane.queue[idx];
            if (e) { const v = (p.rng() < 0.40) ? 2 : 1; e.dot = { value: v, turns: 2 }; log(`라틴 DOT: 열${col + 1} 슬롯${idx} DOT${v}x2T`); }
        }

    } else if (kind === 'Han') {
        // 좌/우 열 전투타깃에 확산
        for (const dc of [-1, +1]) {
            const cc = col + dc; if (cc < 0 || cc >= MAX_COLS) continue;
            const { enemy: ne, idx: ni } = getCombatEnemy(state.lanes[cc]);
            if (ne) { ne.hp -= base; log(`한자 확산(좌/우): 열${cc + 1} 슬롯${ni} -${base} (HP ${Math.max(0, ne.hp)})`); if (ne.hp <= 0) killEnemyAt(cc, ni); }
        }
        // 같은 열에서 타깃 '바로 뒤 1칸'에도 적용
        const bi = (combatIdx >= 0 ? combatIdx : getCombatIdx(lane)) + 1;
        if (bi >= 0 && bi < ROWS) {
            const be = lane.queue[bi];
            if (be) { be.hp -= base; log(`한자 추가(후열): 열${col + 1} 슬롯${bi} -${base} (HP ${Math.max(0, be.hp)})`); if (be.hp <= 0) killEnemyAt(col, bi); }
        }

    } else if (kind === 'Japanese') {
        // 요격: 전투구역(0~2) 중 가장 뒤의 적(2→1→0)을 기본피해로 타격
        const bi = getBackmostCombatIdx(lane);
        if (bi >= 0) {
            const e = lane.queue[bi];
            e.hp -= base;
            log(`일본어 요격: 열${col + 1} 슬롯${bi} -${base} (HP ${Math.max(0, e.hp)})`);
            if (e.hp <= 0) killEnemyAt(col, bi);
        } else {
            log(`일본어 요격: 전투구역에 적 없음`);
        }
    }
}

/* ===== 보조 효과(약화판) ===== */
function applySubEffect(kind, col, base, p, combatIdx) {
    const lane = state.lanes[col];

    if (kind === 'Hangul') {
        // 60% 확률로 타깃 제외 같은 열 모든 적에게 +1
        if (p.rng() < 0.6) {
            for (let i = 0; i < ROWS; i++) {
                if (i === combatIdx) continue;
                const e = lane.queue[i];
                if (e) { e.hp -= 1; log(`보조(한글) 여진: 열${col + 1} 슬롯${i} -1 (HP ${Math.max(0, e.hp)})`); if (e.hp <= 0) { lane.queue[i] = null; } }
            }
        }

    } else if (kind === 'Latin') {
        // 30% 확률 DOT1x2T
        const idx = combatIdx >= 0 ? combatIdx : getCombatIdx(lane);
        if (idx >= 0 && p.rng() < 0.30) {
            const e = lane.queue[idx]; if (e) { e.dot = { value: 1, turns: 2 }; log(`보조(라틴) DOT1x2T (12%) @열${col + 1}/슬롯${idx}`); }
        }

    } else if (kind === 'Han') {
        // 50% 확률로 같은 열 '바로 뒤 1칸'에만 동일 피해
        const bi = (combatIdx >= 0 ? combatIdx : getCombatIdx(lane)) + 1;
        if (p.rng() < 0.5 && bi >= 0 && bi < ROWS) {
            const be = lane.queue[bi]; if (be) { be.hp -= base; log(`보조(한자) 후열추가: 열${col + 1} 슬롯${bi} -${base}`); if (be.hp <= 0) killEnemyAt(col, bi); }
        }

    } else if (kind === 'Japanese') {
        // 요격(약화): 전투구역에서 가장 뒤의 적에 ⌊base/2⌋
        const bi = getBackmostCombatIdx(lane);
        if (bi >= 0) {
            const e = lane.queue[bi]; const dmg = Math.floor(base / 2);
            if (dmg > 0) { e.hp -= dmg; log(`보조(일본어) 약화요격: 열${col + 1} 슬롯${bi} -${dmg}`); if (e.hp <= 0) killEnemyAt(col, bi); }
        }
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

    log(`▶ 스테이지 ${state.stage} 시작: hp×${state.stageMods.hpScale.toFixed(2)}, dmg×${state.stageMods.dmgScale.toFixed(2)}, elite+${(state.stageMods.eliteBonus * 100) | 0}%`);
}

/* ===== UI ===== */
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
        btn.textContent = (state.usedThisTurn < 2 ? `여기에 사용 (${2 - state.usedThisTurn}장 남음)` : `사용 불가`);
        btn.disabled = !state.potion || state.usedThisTurn >= 2 || state.energy < (state.potion ? state.potion.cost : 999);
        btn.onclick = () => castPotionOnColumn(state.potion, c);
        ctr.appendChild(btn);

        col.appendChild(lane); col.appendChild(ctr); grid.appendChild(col);
    }
}
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

    const playsLeft = Math.max(0, 2 - state.usedThisTurn);

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
    const parts = [];['Hangul', 'Latin', 'Han', 'Hiragana', 'Katakana'].forEach(k => { if (counts[k] > 0) parts.push(`${k}(${counts[k]})`); });
    const s = `감지된: ${parts.join(' + ') || '없음'}  |  상태: ` + (hasOther ? '오물(허용 외 문자)' : (set.size === 0 ? '무효' : (set.size <= 2 ? `정상 조합 (${set.size}/2)` : '오물(3종 이상)')));
    document.getElementById('langInfo').textContent = s;
}
function updateUI() { renderGrid(); updateTopBars(); showPotion(state.potion); }

/* ===== 이벤트 ===== */
document.getElementById('genBtn').onclick = () => {
    if (state.turnPotions.length >= 2) { log('이 턴에 더 이상 포션을 생성할 수 없습니다 (최대 2개).'); return; }
    const p = potionFrom([
        document.getElementById('w1').value || '',
        document.getElementById('w2').value || '',
        document.getElementById('w3').value || '',
    ]);
    if (!p) { log('유효한 입력이 없습니다.'); return; }

    state.turnPotions.push(p);
    if (!state.potion) state.potion = state.turnPotions[0];
    showPotion(state.potion);
    log(`포션 생성(${state.turnPotions.length}/2): ${makeName(p.main, p.sub)} | 코스트 ${p.cost} | 기본피해 ${p.baseDmg}`);
    updateUI();
};
document.getElementById('turnBtn').onclick = () => { endOfTurnResolve(); nextTurn(); };
document.getElementById('resetBtn').onclick = resetGame;
['w1', 'w2', 'w3'].forEach(id => document.getElementById(id).addEventListener('input', updateLangDebug));

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
    document.getElementById('log').textContent = '';
    updateLangDebug(); updateUI(); nextTurn();
}
resetGame();
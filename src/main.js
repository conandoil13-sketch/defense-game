/* ===== 유틸 ===== */
function fnv1a(str) { let h = 0x811c9dc5; for (const ch of str) { h ^= ch.codePointAt(0); h = (h >>> 0) * 0x01000193; } return h >>> 0; }
function xorshift(seed) { let x = seed >>> 0 || 123456789; return () => { x ^= (x << 13); x >>>= 0; x ^= (x >>> 17); x >>>= 0; x ^= (x << 5); x >>>= 0; return (x >>> 0) / 0xFFFFFFFF; }; }
const clamp = (n, a, b) => Math.max(a, Math.min(b, n));
const log = (t) => { const el = document.getElementById('log'); if (el) el.textContent = `[T${state.round}] ${t}\n` + el.textContent; };

/* 화면 로그로 에러 확인 */
window.onerror = function (message, source, lineno, colno) {
    log(`[JS ERROR] ${message} @ ${lineno}:${colno}`);
};

/* ===== 스크립트 판정 (라틴 오탐 FIX) ===== */
/* ASCII 문장부호/공백/숫자 등은 전부 무시 */
function isAsciiPunctOrSpace(cp) {
    return (
        (cp >= 0x0000 && cp <= 0x002F) || // 제어/기호/숫자 앞
        (cp >= 0x003A && cp <= 0x0040) || // : ; < = > ? @
        (cp >= 0x005B && cp <= 0x0060) || // [ \ ] ^ _ `
        (cp >= 0x007B && cp <= 0x007E) || // { | } ~  ← 여기 때문에 '|' 오탐 방지
        (cp === 0x00A0)                 // NBSP
    );
}
function isLatinLetter(cp) {
    // A-Z, a-z
    if ((cp >= 0x0041 && cp <= 0x005A) || (cp >= 0x0061 && cp <= 0x007A)) return true;
    // 확장 라틴 (문자만)
    if ((cp >= 0x00C0 && cp <= 0x00FF) || (cp >= 0x0100 && cp <= 0x017F) || (cp >= 0x0180 && cp <= 0x024F) || (cp >= 0x1E00 && cp <= 0x1EFF)) return true;
    return false;
}
function scriptOf(cp) {
    // 공통 제외
    if (isAsciiPunctOrSpace(cp)) return null;
    if (cp >= 0x0030 && cp <= 0x0039) return null; // 0-9
    if (cp >= 0x2000 && cp <= 0x206F) return null; // General Punctuation

    // 한글
    if ((cp >= 0xAC00 && cp <= 0xD7A3) || (cp >= 0x1100 && cp <= 0x11FF) || (cp >= 0x3130 && cp <= 0x318F)) return 'Hangul';
    // 라틴(문자만)
    if (isLatinLetter(cp)) return 'Latin';
    // 한자
    if ((cp >= 0x4E00 && cp <= 0x9FFF) || (cp >= 0x3400 && cp <= 0x4DBF)) return 'Han';
    // 히라가나 / 가타카나
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
    round: 1,
    coreMax: 12, core: 12,
    energyMax: 6, energyGain: 3, energy: 2,
    lanes: Array.from({ length: MAX_COLS }, () => ({ queue: [null, null, null, null, null], locked: false })),
    // --- 턴 당 포션 2장 (생성/사용) ---
    turnPotions: [],      // 이 턴에 생성된 포션 대기열 (최대 2)
    usedThisTurn: 0,      // 이 턴에 사용한 장수 (최대 2)
    potion: null,         // 현재 화면에 표시/사용할 포션(= turnPotions[0] 또는 null)
};

/* ===== 타깃 유틸 ===== */
function getCombatIdx(lane) { for (const i of COMBAT_ZONE) { if (lane.queue[i]) return i; } return -1; }
function getCombatEnemy(lane) { const idx = getCombatIdx(lane); return idx >= 0 ? { enemy: lane.queue[idx], idx } : { enemy: null, idx: -1 }; }

/* ===== 적 생성/이동/공격 ===== */
function makeEnemy(type, rng) {
    let hp = 5, dmg = 1, badge = '';
    if (type === 'basic') { hp = Math.floor(4 + rng() * 4); dmg = 1; }
    if (type === 'elite') { hp = Math.floor(8 + rng() * 5); dmg = (rng() < 0.5 ? 2 : 3); badge = 'elite'; }
    if (type === 'boss') { hp = Math.floor(20 + rng() * 9); dmg = Math.floor(3 + rng() * 3); badge = 'boss'; }
    return { type, hp, dmg, badge, dot: null };
}
function spawnEnemyForLane(lane, rng, wave) {
    if (lane.locked) { lane.locked = false; log('열 스폰 잠금 해제'); return; }
    const q = lane.queue; if (q[4] !== null) return;
    let type = 'basic', r = rng(); if (wave >= 4 && r < 0.18) type = 'elite'; if (wave === 10) type = 'boss';
    const e = makeEnemy(type, rng);
    for (let i = 4; i >= 3; i--) { if (q[i] == null) { q[i] = e; break; } } // Queue부터 채움
}
function advanceAll() {
    // 한 턴에 정확히 "한 칸" 이동
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
    q[idx] = null; log(`적 처치: 열${col + 1} (${e.type.toUpperCase()})`);
}

/* ===== 포션 생성 ===== */
const EFFECT_DESCS = {
    Hangul: '전열 기본 피해 + 대기열(3,4) 각 +1 (20% 확률 +2)',
    Latin: '전열 기본 피해 + 2턴 DOT 1 (25% 확률 DOT 2)',
    Han: '전열과 좌/우 열의 전투타깃에 동일 피해',
    Japanese: '해당 열 스폰 1턴 잠금 + 전체 1칸 후퇴',
    Sludge: '오물: 피해 1, 20% 자해/잠금(프로토타입)',
};
function makeName(main, sub) { const m = { Hangul: '서릿빛', Latin: '전격', Han: '석화', Japanese: '파형', Sludge: '오염' }; return `【${sub ? m[main] + '·' + m[sub] : m[main]} 포션】`; }
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

    const seedBase = fnv1a(words.join('|').normalize('NFC')) ^ (state.round * 2654435761 >>> 0);
    const rng = xorshift(seedBase);

    let cost = 2; if (sub && rng() < 0.10) cost = 3;
    const baseDmg = Math.floor((sub ? 2 : 3) + rng() * ((sub ? 4 : 5) - (sub ? 2 : 3) + 1));
    return { seed: seedBase, rng, main, sub, type: (sub ? '듀얼' : '단일'), cost, baseDmg, isSludge: false, desc: describeEffect(main, sub) };
}
function makeSludge(joined, reason) {
    const seedBase = fnv1a(joined) ^ (state.round * 2654435761 >>> 0);
    return { seed: seedBase, rng: xorshift(seedBase), main: 'Sludge', sub: null, type: '오물', cost: 1, baseDmg: 1, isSludge: true, desc: `오물 포션 (${reason}) — 피해 1, 20% 자해/잠금(프로토타입)` };
}

/* ===== 효과 적용 ===== */
function castPotionOnColumn(p, col) {
    if (!p) return;

    // 턴당 2장 제한
    if (state.usedThisTurn >= 2) { log('이 턴에 더 이상 카드를 사용할 수 없습니다 (최대 2장).'); return; }

    if (state.energy < p.cost) { log(`에너지 부족: 필요 ${p.cost}`); return; }
    state.energy = Math.max(0, state.energy - p.cost);

    const lane = state.lanes[col];
    const { enemy: eTarget, idx: ti } = getCombatEnemy(lane); // 0→1→2 중 맨앞

    if (p.isSludge) {
        if (eTarget) { eTarget.hp -= 1; if (eTarget.hp <= 0) killEnemyAt(col, ti); }
        if (p.rng() < 0.2) { state.core = Math.max(0, state.core - 1); log(`오물 반동! 코어 -1 (남은 ${state.core})`); }
        log(`오물 포션: 열${col + 1} 슬롯${ti >= 0 ? ti : '-'} -1`);
        afterCastConsume(); updateUI(); return;
    }

    if (!eTarget) { log(`타깃 없음: 열${col + 1}에 전투 가능한 적이 없습니다.`); afterCastConsume(); updateUI(); return; }

    const base = p.baseDmg;
    eTarget.hp -= base;
    log(`${p.type} ${p.main}${p.sub ? '/' + p.sub : ''}: 열${col + 1} 슬롯${ti} -${base} (HP ${Math.max(0, eTarget.hp)})`);
    if (eTarget.hp <= 0) killEnemyAt(col, ti);

    applyMainEffect(p.main, col, base, p, ti);
    if (p.sub) applySubEffect(p.sub, col, base, p, ti);

    afterCastConsume();
    updateUI();
}
function afterCastConsume() {
    state.usedThisTurn++;
    // 현재 포션을 큐에서 제거하고 다음 포션을 보여줌
    if (state.turnPotions.length > 0) state.turnPotions.shift();
    state.potion = state.turnPotions[0] || null;
}

/* 메인 효과 */
function applyMainEffect(kind, col, base, p, combatIdx) {
    const lane = state.lanes[col];
    if (kind === 'Hangul') {
        const add = (p.rng() < 0.2) ? 2 : 1; // 대기열에만
        for (const i of QUEUE_ZONE) {
            const e = lane.queue[i]; if (e) { e.hp -= add; log(`한글 추가피해: 열${col + 1} 대기${i} -${add} (HP ${Math.max(0, e.hp)})`); if (e.hp <= 0) { lane.queue[i] = null; } }
        }
    } else if (kind === 'Latin') {
        const e = lane.queue[combatIdx]; if (e) { const v = (p.rng() < 0.25) ? 2 : 1; e.dot = { value: v, turns: 2 }; log(`라틴 DOT: 열${col + 1} 슬롯${combatIdx} DOT${v}x2T`); }
    } else if (kind === 'Han') {
        for (const dc of [-1, +1]) {
            const cc = col + dc; if (cc < 0 || cc >= MAX_COLS) continue;
            const { enemy: ne, idx: ni } = getCombatEnemy(state.lanes[cc]);
            if (ne) { ne.hp -= base; log(`한자 확산: 열${cc + 1} 슬롯${ni} -${base} (HP ${Math.max(0, ne.hp)})`); if (ne.hp <= 0) killEnemyAt(cc, ni); }
        }
    } else if (kind === 'Japanese') {
        state.lanes[col].locked = true;
        const q = state.lanes[col].queue; q.pop(); q.unshift(null); // 전체 1칸 후퇴
        log(`일본어 제어: 열${col + 1} 스폰 1턴 잠금 + 후퇴`);
    }
}
/* 보조 효과(약화판) */
function applySubEffect(kind, col, base, p, combatIdx) {
    const lane = state.lanes[col];
    if (kind === 'Hangul') {
        if (p.rng() < 0.5) { for (const i of QUEUE_ZONE) { const e = lane.queue[i]; if (e) { e.hp -= 1; log(`보조(한글) 여진: 열${col + 1} 대기${i} -1`); if (e.hp <= 0) { lane.queue[i] = null; } } } }
    } else if (kind === 'Latin') {
        const e = lane.queue[combatIdx]; if (e && p.rng() < 0.12) { e.dot = { value: 1, turns: 2 }; log(`보조(라틴) DOT1x2T (12%) @열${col + 1}/슬롯${combatIdx}`); }
    } else if (kind === 'Han') {
        const dirs = []; if (col > 0) dirs.push(col - 1); if (col < MAX_COLS - 1) dirs.push(col + 1);
        if (dirs.length && p.rng() < 0.5) {
            const cc = dirs[Math.floor(p.rng() * dirs.length)];
            const { enemy: ne, idx: ni } = getCombatEnemy(state.lanes[cc]);
            if (ne) { ne.hp -= base; log(`보조(한자) 확산: 열${cc + 1} 슬롯${ni} -${base}`); if (ne.hp <= 0) killEnemyAt(cc, ni); }
        }
    } else if (kind === 'Japanese') {
        if (p.rng() < 0.5) { state.lanes[col].locked = true; log(`보조(일본어) 50%로 스폰 잠금`); }
    }
}

/* ===== 턴 루프 ===== */
function nextTurn() {
    advanceAll();
    const seed = fnv1a('spawn|' + state.round) ^ 0x9e3779b9;
    const rng = xorshift(seed);
    const spawnCount = (rng() < 0.6 ? 1 : 2);
    const cols = [0, 1, 2, 3, 4].sort(() => rng() < 0.5 ? -1 : 1).slice(0, spawnCount);
    for (const c of cols) spawnEnemyForLane(state.lanes[c], rng, (state.round >= 10 ? 10 : state.round));
    state.energy = clamp(state.energy + state.energyGain, 0, state.energyMax);

    // 턴 리셋: 사용/생성 카운터
    state.usedThisTurn = 0;
    state.turnPotions.length = 0;
    state.potion = null;

    updateUI(); log(`— 턴 시작: 전진/스폰 완료, 에너지 +${state.energyGain} (이 턴 최대 2장 사용 가능)`);
}
function endOfTurnResolve() {
    enemyAttackPhase(); dotResolvePhase(); state.round++; updateUI();
    if (state.core <= 0) { alert('패배! 코어 파괴'); resetGame(); return; }
    if (state.round === 11) { alert('승리! 10웨이브 생존'); resetGame(); return; }
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
                const badge = document.createElement('div'); badge.className = 'badge ' + (e.badge || ''); badge.textContent = e.badge ? e.badge.toUpperCase() : 'BASIC';
                enemy.appendChild(hp); enemy.appendChild(info);
                slot.appendChild(badge); slot.appendChild(enemy);
            }
            lane.appendChild(slot);
        }

        const ctr = document.createElement('div'); ctr.className = 'controls';
        const btn = document.createElement('button'); btn.className = 'btn';
        btn.textContent = (state.usedThisTurn < 2 ? `여기에 사용 (${2 - state.usedThisTurn}장 남음)` : `사용 불가`);
        btn.disabled = !state.potion || state.usedThisTurn >= 2;
        btn.onclick = () => castPotionOnColumn(state.potion, c);
        ctr.appendChild(btn);

        col.appendChild(lane); col.appendChild(ctr); grid.appendChild(col);
    }
}
function updateTopBars() {
    document.getElementById('roundTxt').textContent = `라운드 ${state.round}`;
    document.getElementById('coreTxt').textContent = state.core;
    document.getElementById('coreBar').style.width = (state.core / state.coreMax * 100) + '%';
    document.getElementById('energyTxt').textContent = `에너지 ${state.energy} / ${state.energyMax}`;
    document.getElementById('energyBar').style.width = (state.energy / state.energyMax * 100) + '%';
}
function showPotion(p) {
    const box = document.getElementById('potionView');
    if (!box) return;

    // 공통: 이 턴 남은 사용 가능 장수
    const playsLeft = Math.max(0, 2 - state.usedThisTurn);

    // 헬퍼: 패널 버튼 활성/비활성 + 핸들러 바인딩
    function wirePanelButtons(enabled) {
        box.querySelectorAll('[data-cast]').forEach(btn => {
            const col = parseInt(btn.dataset.cast, 10);
            btn.textContent = enabled ? `열 ${col + 1}` : `열 ${col + 1}`;
            btn.disabled = !enabled;
            btn.onclick = enabled ? (() => castPotionOnColumn(state.potion, col)) : null;
        });
    }

    // 포션이 없을 때도 패널은 보여주되, 버튼은 잠금
    if (!p) {
        box.style.display = 'block';
        document.getElementById('potionName').textContent = '(포션 없음)';
        document.getElementById('pMain').textContent = '메인: -';
        document.getElementById('pSub').textContent = '보조: -';
        document.getElementById('pType').textContent = '타입: -';
        document.getElementById('pCost').textContent = '코스트: -';
        document.getElementById('pDmg').textContent = '기본피해: -';
        document.getElementById('potionDesc').textContent = '이 턴에는 최대 2장까지 생성/사용할 수 있습니다.';
        wirePanelButtons(false);
        return;
    }

    // 포션 정보 표시
    box.style.display = 'block';
    const waiting = state.turnPotions.length > 1 ? ` (대기 ${state.turnPotions.length - 1}장)` : '';
    document.getElementById('potionName').textContent = makeName(p.main, p.sub) + waiting;
    document.getElementById('pMain').textContent = `메인: ${p.main}`;
    document.getElementById('pSub').textContent = p.sub ? `보조: ${p.sub}` : '보조: 없음';
    document.getElementById('pType').textContent = `타입: ${p.type}`;
    document.getElementById('pCost').textContent = `코스트: ${p.cost}`;
    document.getElementById('pDmg').textContent = `기본피해: ${p.baseDmg}`;
    document.getElementById('potionDesc').textContent = p.desc;

    // 남은 장수/에너지 상태에 따라 버튼 활성화
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
// 포션 생성: 이 턴에 최대 2번
document.getElementById('genBtn').onclick = () => {
    if (state.turnPotions.length >= 2) { log('이 턴에 더 이상 포션을 생성할 수 없습니다 (최대 2개).'); return; }
    const p = potionFrom([
        document.getElementById('w1').value || '',
        document.getElementById('w2').value || '',
        document.getElementById('w3').value || '',
    ]);
    if (!p) { log('유효한 입력이 없습니다.'); return; }

    state.turnPotions.push(p);
    // 현재 표시 포션이 없으면 꺼내서 세팅
    if (!state.potion) state.potion = state.turnPotions[0];

    showPotion(state.potion);
    log(`포션 생성(${state.turnPotions.length}/2): ${makeName(p.main, p.sub)} | 코스트 ${p.cost} | 기본피해 ${p.baseDmg}`);
    updateUI();
};
// 턴 종료 → 다음 턴
document.getElementById('turnBtn').onclick = () => { endOfTurnResolve(); nextTurn(); };
document.getElementById('resetBtn').onclick = resetGame;
['w1', 'w2', 'w3'].forEach(id => document.getElementById(id).addEventListener('input', updateLangDebug));

/* ===== 초기화 ===== */
function resetGame() {
    state.round = 1; state.core = state.coreMax; state.energy = state.energyGain;
    state.lanes = Array.from({ length: MAX_COLS }, () => ({ queue: [null, null, null, null, null], locked: false }));
    state.turnPotions.length = 0; state.usedThisTurn = 0;
    state.potion = null;
    document.getElementById('log').textContent = '';
    updateLangDebug(); updateUI(); nextTurn();
}
resetGame();
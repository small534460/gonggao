'use strict';

/* ==================== 工具函数 ==================== */
const $ = (sel) => document.querySelector(sel);
const uid = () => 'l' + Date.now().toString(36) + Math.random().toString(36).slice(2, 8);
const clamp = (v, min, max) => Math.min(max, Math.max(min, v));
const clampNum = (v, min, max) => { const n = +v; return isNaN(n) ? min : clamp(n, min, max); };

function escapeHtml(s) {
  return String(s).replace(/[&<>"']/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]));
}

function debounce(fn, ms) {
  let t = null;
  return (...a) => { clearTimeout(t); t = setTimeout(() => fn(...a), ms); };
}

function hexToRgb(hex) {
  let h = String(hex).replace('#', '');
  if (h.length === 3) h = h.split('').map(c => c + c).join('');
  const n = parseInt(h, 16);
  if (isNaN(n) || h.length !== 6) return null;
  return [(n >> 16) & 255, (n >> 8) & 255, n & 255];
}

function lerpColor(c1, c2, t) {
  const a = hexToRgb(c1), b = hexToRgb(c2);
  if (!a || !b) return c1;
  const mix = i => Math.round(a[i] + (b[i] - a[i]) * t).toString(16).padStart(2, '0');
  return '#' + mix(0) + mix(1) + mix(2);
}

/* 在两个相距最远的色标之间插入新色标（颜色取两端插值） */
function addGradientStop(stops) {
  const sorted = [...stops].sort((a, b) => a.pos - b.pos);
  if (sorted.length < 2) { stops.push({ pos: 50, color: '#ffffff' }); return; }
  let bestIdx = 0, bestGap = 0;
  for (let i = 0; i < sorted.length - 1; i++) {
    const gap = sorted[i + 1].pos - sorted[i].pos;
    if (gap > bestGap) { bestGap = gap; bestIdx = i; }
  }
  const mid = Math.round((sorted[bestIdx].pos + sorted[bestIdx + 1].pos) / 2);
  stops.push({ pos: mid, color: lerpColor(sorted[bestIdx].color, sorted[bestIdx + 1].color, 0.5) });
}

let toastTimer = null;
function toast(msg) {
  const t = $('#toast');
  t.textContent = msg;
  t.classList.add('show');
  clearTimeout(toastTimer);
  toastTimer = setTimeout(() => t.classList.remove('show'), 2200);
}

/* ==================== 常量 ==================== */
const BG_ID = '__bg__';

const CANVAS_PRESETS = [
  { label: '1:1 正方形 1080×1080', w: 1080, h: 1080 },
  { label: '3:4 竖版海报 1080×1440', w: 1080, h: 1440 },
  { label: '4:3 横版 1440×1080', w: 1440, h: 1080 },
  { label: '16:9 宽屏 1920×1080', w: 1920, h: 1080 },
  { label: '9:16 手机竖屏 1080×1920', w: 1080, h: 1920 },
  { label: '横版卡片 1200×628', w: 1200, h: 628 },
];

const FONTS = [
  { label: '微软雅黑', value: '"Microsoft YaHei", sans-serif' },
  { label: '黑体 (SimHei)', value: 'SimHei, sans-serif' },
  { label: '宋体 (SimSun)', value: 'SimSun, serif' },
  { label: '楷体 (KaiTi)', value: 'KaiTi, serif' },
  { label: '仿宋 (FangSong)', value: 'FangSong, serif' },
  { label: 'Arial', value: 'Arial, sans-serif' },
  { label: 'Helvetica', value: 'Helvetica, sans-serif' },
  { label: 'Verdana', value: 'Verdana, sans-serif' },
  { label: 'Georgia', value: 'Georgia, serif' },
  { label: 'Times New Roman', value: '"Times New Roman", serif' },
  { label: 'Courier New', value: '"Courier New", monospace' },
  { label: 'Impact', value: 'Impact, sans-serif' },
  { label: 'Comic Sans MS', value: '"Comic Sans MS", cursive' },
  { label: 'Segoe UI', value: '"Segoe UI", sans-serif' },
];

/* ==================== 状态 ==================== */
const state = {
  canvas: { w: 1080, h: 1080 },
  background: { type: 'solid', color: '#232539', angle: 135, stops: [{ pos: 0, color: '#667eea' }, { pos: 100, color: '#764ba2' }], image: null, fit: 'cover', blur: 0 },
  layers: [],
  selectedId: null,
  tool: 'select',
  focusText: false,
};

/* ==================== 全局变量 ==================== */
let canvasEl, ctx, canvasArea, layerList, propsContent, propsTitle, statusbar,
    zoomRange, zoomLabel, canvasPreset, fileInput, bgFileInput,
    btnUndo, btnRedo, toolSelect, toolText, btnZoomFit, btnExportPng, btnExportJpg,
    btnAddText, btnAddImage, btnDup, btnDel, btnLayerUp, btnLayerDown,
    btnCustomSize, btnNew, btnCenterBoth, bgThumbEl = null;

const measureCtx = document.createElement('canvas').getContext('2d');
const imageCache = new Map();

let undoStack = [], redoStack = [];
let pendingSnapshot = null, undoArmed = false;
let drag = null, dragLayerId = null, prevDnDSnapshot = null;
let zoomMode = 'fit', zoomVal = 1;

window._fileCb = null;

/* ==================== 画布与渲染 ==================== */
function fontString(layer) {
  return `${layer.italic ? 'italic ' : ''}${layer.bold ? 'bold ' : ''}${layer.fontSize}px ${layer.fontFamily}`;
}

/* 线性渐变（支持任意数量色标），坐标为绝对画布坐标 */
function makeLinearGradient(g, x, y, w, h, angle, stops) {
  const rad = angle * Math.PI / 180;
  const cx = x + w / 2, cy = y + h / 2;
  const half = Math.hypot(w, h) / 2;
  const gr = g.createLinearGradient(
    cx - Math.cos(rad) * half, cy - Math.sin(rad) * half,
    cx + Math.cos(rad) * half, cy + Math.sin(rad) * half);
  const sorted = [...stops].sort((a, b) => a.pos - b.pos);
  sorted.forEach(s => gr.addColorStop(clamp(s.pos, 0, 100) / 100, s.color));
  return gr;
}

function measureTextLayer(layer) {
  measureCtx.font = fontString(layer);
  const lines = layer.text.split('\n');
  let w = 0;
  for (const ln of lines) {
    const tw = measureCtx.measureText(ln).width;
    if (tw > w) w = tw;
  }
  const h = lines.length * layer.fontSize * layer.lineHeight;
  return { w, h, lines };
}

function getLayerBox(layer) {
  if (layer.type === 'image') return { x: layer.x, y: layer.y, w: layer.w, h: layer.h };
  const m = measureTextLayer(layer);
  const pad = (layer.strokeWidth || 0) / 2 + (layer.shadowOn ? layer.shadowBlur : 0) + 3;
  return { x: layer.x - pad, y: layer.y - pad, w: m.w + pad * 2, h: m.h + pad * 2 };
}

function getImage(src) {
  if (imageCache.has(src)) return imageCache.get(src);
  const im = new Image();
  im.onload = () => { render(); updateThumbsDebounced(); };
  im.src = src;
  imageCache.set(src, im);
  return im;
}

function drawCover(g, img, x, y, w, h) {
  const iw = img.naturalWidth || img.width, ih = img.naturalHeight || img.height;
  if (!iw || !ih) return;
  const s = Math.max(w / iw, h / ih);
  const dw = iw * s, dh = ih * s;
  g.drawImage(img, x + (w - dw) / 2, y + (h - dh) / 2, dw, dh);
}

function drawTextLayer(g, layer) {
  if (!layer.text) return;
  g.save();
  g.globalAlpha = layer.opacity;
  if (layer.blur > 0) g.filter = `blur(${layer.blur}px)`;
  g.font = fontString(layer);
  g.textBaseline = 'top';
  if (layer.shadowOn) {
    g.shadowColor = layer.shadowColor;
    g.shadowBlur = layer.shadowBlur;
    g.shadowOffsetX = 0;
    g.shadowOffsetY = Math.max(1, layer.shadowBlur * 0.35);
  }
  const m = measureTextLayer(layer);
  const lh = layer.fontSize * layer.lineHeight;
  let x0 = layer.x;
  if (layer.align === 'center') x0 += m.w / 2;
  else if (layer.align === 'right') x0 += m.w;
  g.textAlign = layer.align === 'center' ? 'center' : layer.align === 'right' ? 'right' : 'left';
  if (layer.strokeWidth > 0) {
    g.lineWidth = layer.strokeWidth;
    g.lineJoin = 'round';
    g.miterLimit = 2;
    g.strokeStyle = layer.strokeColor;
  }
  if (layer.gradientOn && layer.gradientStops && layer.gradientStops.length >= 2) {
    g.fillStyle = makeLinearGradient(g, layer.x, layer.y, m.w, m.h, layer.gradientAngle, layer.gradientStops);
  } else {
    g.fillStyle = layer.color;
  }
  m.lines.forEach((ln, i) => {
    const y = layer.y + i * lh;
    if (layer.strokeWidth > 0) g.strokeText(ln, x0, y);
    g.fillText(ln, x0, y);
  });
  g.restore();
}

function drawImageLayer(g, layer) {
  const img = getImage(layer.src);
  if (!img.complete || !img.naturalWidth) return;
  g.save();
  g.globalAlpha = layer.opacity;
  if (layer.blur > 0) g.filter = `blur(${layer.blur}px)`;
  g.drawImage(img, layer.x, layer.y, layer.w, layer.h);
  g.restore();
}

function drawBackground(g, w, h) {
  const bg = state.background;
  g.save();
  if (bg.type !== 'transparent' && bg.blur > 0) g.filter = `blur(${bg.blur}px)`;
  if (bg.type === 'solid') {
    g.fillStyle = bg.color;
    g.fillRect(0, 0, w, h);
  } else if (bg.type === 'gradient') {
    g.fillStyle = makeLinearGradient(g, 0, 0, w, h, bg.angle, bg.stops);
    g.fillRect(0, 0, w, h);
  } else if (bg.type === 'image' && bg.image) {
    const img = getImage(bg.image);
    if (img.complete && img.naturalWidth) {
      if (bg.fit === 'cover') drawCover(g, img, 0, 0, w, h);
      else g.drawImage(img, 0, 0, w, h);
    }
  }
  g.restore();
  /* transparent：什么都不画 */
}

function renderScene(g, w, h) {
  drawBackground(g, w, h);
  for (const l of state.layers) {
    if (!l.visible) continue;
    if (l.type === 'image') drawImageLayer(g, l);
    else drawTextLayer(g, l);
  }
}

function drawSelection(g) {
  const layer = selectedLayer();
  if (!layer || !layer.visible) return;
  const box = getLayerBox(layer);
  const rect = canvasEl.getBoundingClientRect();
  const s = rect.width / state.canvas.w || 1;
  g.save();
  g.strokeStyle = '#7d9bff';
  g.lineWidth = 1.5 / s;
  g.setLineDash([6 / s, 4 / s]);
  g.strokeRect(box.x, box.y, box.w, box.h);
  g.setLineDash([]);
  const hs = 12 / s;
  const corners = [[box.x, box.y], [box.x + box.w, box.y], [box.x, box.y + box.h], [box.x + box.w, box.y + box.h]];
  g.fillStyle = '#ffffff';
  for (const [cx, cy] of corners) {
    g.fillRect(cx - hs / 2, cy - hs / 2, hs, hs);
    g.strokeRect(cx - hs / 2, cy - hs / 2, hs, hs);
  }
  g.restore();
}

function render() {
  const c = canvasEl, g = ctx;
  g.clearRect(0, 0, c.width, c.height);
  renderScene(g, c.width, c.height);
  drawSelection(g);
  updateThumbsDebounced();
  updateStatus();
}

function applyCanvasSize(w, h, record) {
  if (record) pushUndo();
  state.canvas.w = w; state.canvas.h = h;
  canvasEl.width = w; canvasEl.height = h;
  applyZoom();
  render();
  updatePresetSelect();
}

function computeFitZoom() {
  const aw = canvasArea.clientWidth - 60, ah = canvasArea.clientHeight - 60;
  return clamp(Math.min(aw / state.canvas.w, ah / state.canvas.h), 0.05, 2);
}

function applyZoom() {
  const z = zoomMode === 'fit' ? computeFitZoom() : zoomVal;
  canvasEl.style.width = Math.max(1, Math.round(state.canvas.w * z)) + 'px';
  canvasEl.style.height = Math.max(1, Math.round(state.canvas.h * z)) + 'px';
  zoomLabel.textContent = zoomMode === 'fit' ? '适应' : Math.round(z * 100) + '%';
  if (zoomMode === 'manual') zoomRange.value = Math.round(zoomVal * 100);
  updateStatus();
}

function updateStatus() {
  const sel = selectedLayer();
  const z = zoomMode === 'fit' ? '适应' : Math.round(zoomVal * 100) + '%';
  statusbar.textContent =
    `画布 ${state.canvas.w}×${state.canvas.h} px · 图层 ${state.layers.length}（+背景） · ` +
    `选中 ${state.selectedId === BG_ID ? '背景' : sel ? sel.name : '无'} · 缩放 ${z}`;
}

/* ==================== 命中检测与坐标 ==================== */
function canvasPos(e) {
  const r = canvasEl.getBoundingClientRect();
  return {
    x: (e.clientX - r.left) * state.canvas.w / r.width,
    y: (e.clientY - r.top) * state.canvas.h / r.height,
  };
}

function hitTest(x, y) {
  for (let i = state.layers.length - 1; i >= 0; i--) {
    const l = state.layers[i];
    if (!l.visible) continue;
    const b = getLayerBox(l);
    if (x >= b.x && x <= b.x + b.w && y >= b.y && y <= b.y + b.h) return l;
  }
  return null;
}

function getHandleAt(x, y) {
  const layer = selectedLayer();
  if (!layer || !layer.visible) return null;
  const box = getLayerBox(layer);
  const rect = canvasEl.getBoundingClientRect();
  const s = rect.width / state.canvas.w || 1;
  const tol = 10 / s;
  const corners = [['nw', box.x, box.y], ['ne', box.x + box.w, box.y], ['sw', box.x, box.y + box.h], ['se', box.x + box.w, box.y + box.h]];
  for (const [n, cx, cy] of corners) {
    if (Math.abs(x - cx) <= tol && Math.abs(y - cy) <= tol) return n;
  }
  return null;
}

/* ==================== 选中与图层操作 ==================== */
function selectedLayer() {
  return state.layers.find(l => l.id === state.selectedId) || null;
}

function select(id) {
  flushOp();
  state.selectedId = id;
  renderLayers();
  renderProps();
  render();
}

function addTextLayerAt(x, y) {
  const n = state.layers.filter(l => l.type === 'text').length + 1;
  const layer = {
    id: uid(), type: 'text', name: `文字 ${n}`,
    text: '双击编辑文字',
    x, y,
    fontSize: Math.max(36, Math.round(state.canvas.w / 15)),
    fontFamily: '"Microsoft YaHei", sans-serif',
    color: '#ffffff', bold: false, italic: false, align: 'center',
    lineHeight: 1.2, strokeColor: '#000000', strokeWidth: 0,
    shadowOn: false, shadowBlur: 8, shadowColor: '#000000',
    opacity: 1, visible: true,
    gradientOn: false, gradientAngle: 0,
    gradientStops: [{ pos: 0, color: '#ffd166' }, { pos: 100, color: '#ef476f' }],
    blur: 0, offsetX: 0, offsetY: 0, autoCenter: false,
  };
  state.layers.push(layer);
  select(layer.id);
  return layer;
}

function addImageLayer(src, cx, cy) {
  const img = new Image();
  img.onload = () => {
    const iw = img.naturalWidth, ih = img.naturalHeight;
    let w = state.canvas.w * 0.6, h = w * ih / iw;
    if (h > state.canvas.h * 0.85) { h = state.canvas.h * 0.85; w = h * iw / ih; }
    const x = cx != null ? cx - w / 2 : (state.canvas.w - w) / 2;
    const y = cy != null ? cy - h / 2 : (state.canvas.h - h) / 2;
    const layer = {
      id: uid(), type: 'image',
      name: `图片 ${state.layers.filter(l => l.type === 'image').length + 1}`,
      src, x, y, w, h, opacity: 1, visible: true,
      blur: 0, offsetX: 0, offsetY: 0,
    };
    pushUndo();
    state.layers.push(layer);
    select(layer.id);
  };
  img.onerror = () => toast('图片读取失败，请换一个文件');
  img.src = src;
}

function deleteLayer(id) {
  const i = state.layers.findIndex(l => l.id === id);
  if (i < 0) return;
  pushUndo();
  state.layers.splice(i, 1);
  if (state.selectedId === id) state.selectedId = null;
  renderLayers(); renderProps(); render();
}

function deleteSelected() {
  if (state.selectedId === BG_ID) { toast('背景图层不能删除，可以改成「透明」'); return; }
  const l = selectedLayer();
  if (!l) { toast('请先选中一个图层'); return; }
  deleteLayer(l.id);
}

function duplicateSelected() {
  const src = selectedLayer();
  if (!src) { toast('请先选中一个图层'); return; }
  pushUndo();
  const copy = JSON.parse(JSON.stringify(src));
  copy.id = uid();
  copy.name = src.name + ' 副本';
  copy.x += 30; copy.y += 30;
  state.layers.splice(state.layers.indexOf(src) + 1, 0, copy);
  select(copy.id);
}

function toggleVisible(id) {
  const l = state.layers.find(x => x.id === id);
  if (!l) return;
  pushUndo();
  l.visible = !l.visible;
  renderLayers(); render();
}

function moveLayer(dir) {
  const l = selectedLayer();
  if (!l) return;
  const i = state.layers.indexOf(l);
  const j = i + dir; /* dir=1 上移一层（z 更高），dir=-1 下移 */
  if (j < 0 || j >= state.layers.length) return;
  pushUndo();
  state.layers.splice(i, 1);
  state.layers.splice(j, 0, l);
  renderLayers(); render();
}

/* 居中到画布（保留 X/Y 偏移） */
function centerLayer(l) {
  const ox = l.offsetX || 0, oy = l.offsetY || 0;
  if (l.type === 'image') {
    l.x = (state.canvas.w - l.w) / 2 + ox;
    l.y = (state.canvas.h - l.h) / 2 + oy;
  } else {
    const m = measureTextLayer(l);
    l.x = (state.canvas.w - m.w) / 2 + ox;
    l.y = (state.canvas.h - m.h) / 2 + oy;
  }
}

/* 文字图层开启「实时居中」后，内容/字号变化时自动重新居中 */
function maybeAutoCenter(l) {
  if (l.type === 'text' && l.autoCenter) centerLayer(l);
}

function alignSelected(mode) {
  const l = selectedLayer();
  if (!l) { toast('请先在画布或图层面板选中一个图层'); return; }
  const b = l.type === 'image' ? { w: l.w, h: l.h } : measureTextLayer(l);
  const ox = l.offsetX || 0, oy = l.offsetY || 0;
  pushUndo();
  if (mode === 'left') l.x = 0;
  if (mode === 'hcenter') l.x = (state.canvas.w - b.w) / 2 + ox;
  if (mode === 'right') l.x = state.canvas.w - b.w;
  if (mode === 'top') l.y = 0;
  if (mode === 'vcenter') l.y = (state.canvas.h - b.h) / 2 + oy;
  if (mode === 'bottom') l.y = state.canvas.h - b.h;
  if (mode === 'both') {
    l.x = (state.canvas.w - b.w) / 2 + ox;
    l.y = (state.canvas.h - b.h) / 2 + oy;
  }
  if (l.type === 'text' && l.autoCenter && ['left', 'right', 'top', 'bottom'].includes(mode)) {
    l.autoCenter = false;
    renderProps();
  }
  render();
}

/* ==================== 撤销 / 重做 ==================== */
function snapshot() {
  return JSON.stringify({ canvas: state.canvas, background: state.background, layers: state.layers });
}

function beginOp() {
  if (pendingSnapshot == null) pendingSnapshot = snapshot();
}

function endOp() {
  if (pendingSnapshot == null) return;
  if (snapshot() !== pendingSnapshot) {
    undoStack.push(pendingSnapshot);
    if (undoStack.length > 60) undoStack.shift();
    redoStack = [];
    updateUndoButtons();
  }
  pendingSnapshot = null;
}

function pushUndo() {
  undoStack.push(snapshot());
  if (undoStack.length > 60) undoStack.shift();
  redoStack = [];
  updateUndoButtons();
}

function flushOp() {
  if (undoArmed) { endOp(); undoArmed = false; }
}

function updateUndoButtons() {
  btnUndo.disabled = undoStack.length === 0;
  btnRedo.disabled = redoStack.length === 0;
}

function restore(str) {
  const s = JSON.parse(str);
  state.canvas = s.canvas;
  state.background = s.background;
  state.layers = s.layers;
  if (state.selectedId !== BG_ID && !state.layers.some(l => l.id === state.selectedId)) state.selectedId = null;
  canvasEl.width = state.canvas.w; canvasEl.height = state.canvas.h;
  applyZoom();
  render(); renderLayers(); renderProps();
}

function undo() {
  if (!undoStack.length) return;
  flushOp();
  redoStack.push(snapshot());
  restore(undoStack.pop());
  updateUndoButtons();
}

function redo() {
  if (!redoStack.length) return;
  flushOp();
  undoStack.push(snapshot());
  restore(redoStack.pop());
  updateUndoButtons();
}

/* ==================== 图层列表 UI ==================== */
function renderLayers() {
  const sel = state.selectedId;
  layerList.innerHTML = '';
  /* 列表顶部 = 最上层图层（与渲染顺序反序展示） */
  for (let i = state.layers.length - 1; i >= 0; i--) {
    const l = state.layers[i];
    const li = document.createElement('li');
    li.dataset.id = l.id;
    li.draggable = true;
    li.classList.toggle('active', l.id === sel);
    li.innerHTML =
      `<button type="button" class="icon-btn eye" title="显示/隐藏">${l.visible ? '👁' : '🚫'}</button>` +
      `<canvas class="thumb" width="80" height="80"></canvas>` +
      `<span class="lname">${escapeHtml(l.name)}</span>` +
      `<button type="button" class="icon-btn del" title="删除图层">✕</button>`;
    l._thumbEl = li.querySelector('.thumb');
    layerList.appendChild(li);
  }
  const bgLi = document.createElement('li');
  bgLi.dataset.id = BG_ID;
  bgLi.classList.toggle('active', sel === BG_ID);
  bgLi.innerHTML =
    `<button type="button" class="icon-btn eye" title="背景固定在底部">🔒</button>` +
    `<canvas class="thumb" width="80" height="80"></canvas>` +
    `<span class="lname">背景</span>` +
    `<span style="flex:none;color:var(--dim);font-size:11px">底部</span>`;
  bgThumbEl = bgLi.querySelector('.thumb');
  layerList.appendChild(bgLi);
  updateThumbsDebounced();
}

function drawThumb(c, layer) {
  const g = c.getContext('2d');
  g.clearRect(0, 0, c.width, c.height);
  if (layer.type === 'image') {
    const img = getImage(layer.src);
    if (img.complete && img.naturalWidth) drawCover(g, img, 0, 0, c.width, c.height);
    else { g.fillStyle = '#2a2f3f'; g.fillRect(0, 0, c.width, c.height); }
  } else {
    const box = measureTextLayer(layer);
    if (!box.w || !box.h) return;
    const s = Math.min(c.width / box.w, c.height / box.h) * 0.9;
    g.save();
    g.translate((c.width - box.w * s) / 2, (c.height - box.h * s) / 2);
    g.scale(s, s);
    drawTextLayer(g, { ...layer, x: 0, y: 0, opacity: 1 });
    g.restore();
  }
}

function drawBgThumb(c) {
  const g = c.getContext('2d');
  g.clearRect(0, 0, c.width, c.height);
  const bg = state.background;
  if (bg.type !== 'transparent' && bg.blur > 0) g.filter = `blur(${bg.blur}px)`;
  if (bg.type === 'solid') {
    g.fillStyle = bg.color; g.fillRect(0, 0, c.width, c.height);
  } else if (bg.type === 'gradient') {
    g.fillStyle = makeLinearGradient(g, 0, 0, c.width, c.height, bg.angle, bg.stops);
    g.fillRect(0, 0, c.width, c.height);
  } else if (bg.type === 'image' && bg.image) {
    const img = getImage(bg.image);
    if (img.complete && img.naturalWidth) drawCover(g, img, 0, 0, c.width, c.height);
  }
}

const updateThumbsDebounced = debounce(updateThumbs, 150);
function updateThumbs() {
  for (const l of state.layers) {
    if (l._thumbEl && l._thumbEl.isConnected) drawThumb(l._thumbEl, l);
  }
  if (bgThumbEl && bgThumbEl.isConnected) drawBgThumb(bgThumbEl);
}

function syncLayersFromDom() {
  const ids = [...layerList.querySelectorAll('li[data-id]')].map(li => li.dataset.id).filter(id => id !== BG_ID);
  const byId = new Map(state.layers.map(l => [l.id, l]));
  /* DOM 顺序是顶层在前，数组顺序是底层在前，需要反转 */
  const next = ids.reverse().map(id => byId.get(id)).filter(Boolean);
  if (next.length === state.layers.length) state.layers = next;
  render();
}

/* ==================== 属性面板 ==================== */
function armInput(el, fn) {
  const evt = (el.type === 'checkbox' || el.tagName === 'SELECT') ? 'change' : 'input';
  el.addEventListener('focus', () => { if (!undoArmed) { beginOp(); undoArmed = true; } });
  el.addEventListener('blur', () => { if (undoArmed) { endOp(); undoArmed = false; } });
  el.addEventListener(evt, () => fn(el.type === 'checkbox' ? el.checked : el.value));
}

function updateTag(id, v) {
  const el = propsContent.querySelector('#' + id);
  if (el) el.textContent = v;
}

/* 渲染渐变色标列表：每行 = 颜色 + 位置滑杆 */
function renderStops(container, stops, onChange) {
  container.innerHTML = '';
  const sorted = [...stops].sort((a, b) => a.pos - b.pos);
  sorted.forEach(s => {
    const row = document.createElement('div');
    row.className = 'stop-row';
    row.innerHTML =
      `<input type="color" class="stop-color" value="${escapeHtml(s.color)}">` +
      `<input type="range" class="stop-pos" min="0" max="100" step="1" value="${s.pos}">` +
      `<span class="stop-pos-label">${s.pos}%</span>`;
    const cEl = row.querySelector('.stop-color');
    const pEl = row.querySelector('.stop-pos');
    const lbl = row.querySelector('.stop-pos-label');
    armInput(cEl, v => { s.color = v; onChange(); });
    armInput(pEl, v => { s.pos = clampNum(v, 0, 100); lbl.textContent = s.pos + '%'; onChange(); });
    container.appendChild(row);
  });
}

function textPropsHTML() {
  return `
  <div class="prop"><label>文字内容（Enter 换行）</label>
    <textarea id="p-text" rows="4" spellcheck="false" placeholder="输入文字…"></textarea>
  </div>
  <div class="prop"><label>字体</label>
    <select id="p-font">${FONTS.map(f => `<option value="${escapeHtml(f.value)}">${f.label}</option>`).join('')}</select>
  </div>
  <div class="prop"><label>字号 <span class="val-tag" id="p-size-tag"></span></label>
    <input type="range" id="p-size" min="8" max="400" step="1">
  </div>
  <div class="prop-row">
    <div class="prop grow" id="p-color-row"><label>文字颜色</label><input type="color" id="p-color"></div>
    <div class="prop grow"><label>样式</label>
      <div class="seg">
        <button type="button" data-b>粗</button>
        <button type="button" data-i>斜</button>
      </div>
    </div>
  </div>
  <div class="prop"><label>填充方式</label>
    <div class="seg">
      <button type="button" data-fill="solid">纯色</button>
      <button type="button" data-fill="gradient">线性渐变</button>
    </div>
  </div>
  <div id="p-grad-block" style="display:none">
    <div class="prop"><label>渐变角度 <span class="val-tag" id="p-gradAngle-tag"></span></label>
      <input type="range" id="p-gradAngle" min="0" max="359" step="1">
    </div>
    <div class="prop"><label>渐变色（拖位置 / 点颜色修改）</label>
      <div class="stop-list" id="p-stops"></div>
      <div class="mini-btns">
        <button type="button" class="btn mini" id="p-stopAdd">＋ 添加颜色</button>
        <button type="button" class="btn mini" id="p-stopDel">－ 移除颜色</button>
      </div>
    </div>
  </div>
  <div class="prop"><label>段落对齐</label>
    <div class="seg">
      <button type="button" data-a="left">左</button>
      <button type="button" data-a="center">中</button>
      <button type="button" data-a="right">右</button>
    </div>
  </div>
  <div class="prop-row">
    <div class="prop grow"><label>描边颜色</label><input type="color" id="p-strokeColor"></div>
    <div class="prop grow"><label>描边宽度（0=无）</label><input type="number" id="p-strokeWidth" min="0" max="40" step="1"></div>
  </div>
  <div class="prop-row">
    <div class="prop grow"><label>阴影</label><label class="check"><input type="checkbox" id="p-shadowOn"> 启用</label></div>
    <div class="prop grow"><label>阴影颜色</label><input type="color" id="p-shadowColor"></div>
  </div>
  <div class="prop"><label>阴影模糊 <span class="val-tag" id="p-shadowBlur-tag"></span></label>
    <input type="range" id="p-shadowBlur" min="0" max="60" step="1">
  </div>
  <div class="prop"><label>行高 <span class="val-tag" id="p-lineHeight-tag"></span></label>
    <input type="range" id="p-lineHeight" min="1" max="2" step="0.05">
  </div>
  <div class="prop"><label>不透明度 <span class="val-tag" id="p-opacity-tag"></span></label>
    <input type="range" id="p-opacity" min="0" max="100" step="1">
  </div>
  <div class="prop"><label>定位</label>
    <button type="button" class="btn block" id="p-center">⦿ 居中到画布</button>
    <label class="check"><input type="checkbox" id="p-autoCenter"> 实时居中（编辑文字时自动保持居中）</label>
  </div>
  <div class="prop-row">
    <div class="prop grow"><label>X 偏移</label><input type="number" id="p-offsetX" step="1"></div>
    <div class="prop grow"><label>Y 偏移</label><input type="number" id="p-offsetY" step="1"></div>
  </div>
  <div class="prop-row">
    <div class="prop grow"><label>位置 X（绝对）</label><input type="number" id="p-x" step="1"></div>
    <div class="prop grow"><label>位置 Y（绝对）</label><input type="number" id="p-y" step="1"></div>
  </div>
  <div class="prop"><label>高斯模糊 <span class="val-tag" id="p-blur-tag"></span></label>
    <input type="range" id="p-blur" min="0" max="100" step="1">
  </div>
  <div class="prop"><label>图层名称</label><input type="text" id="p-name"></div>`;
}

function bindTextProps(layer) {
  const pc = propsContent;
  const $id = id => pc.querySelector(id);
  const ta = $id('#p-text'); ta.value = layer.text;
  armInput(ta, v => { layer.text = v; maybeAutoCenter(layer); render(); });

  const fontSel = $id('#p-font'); fontSel.value = layer.fontFamily;
  armInput(fontSel, v => { layer.fontFamily = v; maybeAutoCenter(layer); render(); });

  const size = $id('#p-size'); size.value = layer.fontSize;
  updateTag('p-size-tag', Math.round(layer.fontSize) + 'px');
  armInput(size, v => { layer.fontSize = clampNum(v, 8, 400); updateTag('p-size-tag', Math.round(layer.fontSize) + 'px'); maybeAutoCenter(layer); render(); });

  const color = $id('#p-color'); color.value = layer.color;
  armInput(color, v => { layer.color = v; render(); });

  const sc = $id('#p-strokeColor'); sc.value = layer.strokeColor;
  armInput(sc, v => { layer.strokeColor = v; render(); });

  const sw = $id('#p-strokeWidth'); sw.value = layer.strokeWidth;
  armInput(sw, v => { layer.strokeWidth = clampNum(v, 0, 40); render(); });

  const so = $id('#p-shadowOn'); so.checked = layer.shadowOn;
  so.addEventListener('change', () => { pushUndo(); layer.shadowOn = so.checked; render(); });

  const sbc = $id('#p-shadowColor'); sbc.value = layer.shadowColor;
  armInput(sbc, v => { layer.shadowColor = v; render(); });

  const sb = $id('#p-shadowBlur'); sb.value = layer.shadowBlur;
  updateTag('p-shadowBlur-tag', layer.shadowBlur + 'px');
  armInput(sb, v => { layer.shadowBlur = clampNum(v, 0, 60); updateTag('p-shadowBlur-tag', layer.shadowBlur + 'px'); render(); });

  const lh = $id('#p-lineHeight'); lh.value = layer.lineHeight;
  updateTag('p-lineHeight-tag', (+layer.lineHeight).toFixed(2));
  armInput(lh, v => { layer.lineHeight = clampNum(v, 1, 2); updateTag('p-lineHeight-tag', (+layer.lineHeight).toFixed(2)); maybeAutoCenter(layer); render(); });

  const op = $id('#p-opacity'); op.value = Math.round(layer.opacity * 100);
  updateTag('p-opacity-tag', Math.round(layer.opacity * 100) + '%');
  armInput(op, v => { layer.opacity = clampNum(v, 0, 100) / 100; updateTag('p-opacity-tag', Math.round(layer.opacity * 100) + '%'); render(); });

  /* 定位：居中 / 实时居中 / XY 偏移 */
  const ac = $id('#p-autoCenter'); ac.checked = !!layer.autoCenter;
  ac.addEventListener('change', () => {
    pushUndo();
    layer.autoCenter = ac.checked;
    if (layer.autoCenter) centerLayer(layer);
    render();
  });
  $id('#p-center').addEventListener('click', () => { pushUndo(); centerLayer(layer); render(); });

  const ox = $id('#p-offsetX'); ox.value = layer.offsetX || 0;
  armInput(ox, v => {
    const nv = clampNum(v, -100000, 100000);
    layer.x += nv - (layer.offsetX || 0);
    layer.offsetX = nv;
    render();
  });
  const oy = $id('#p-offsetY'); oy.value = layer.offsetY || 0;
  armInput(oy, v => {
    const nv = clampNum(v, -100000, 100000);
    layer.y += nv - (layer.offsetY || 0);
    layer.offsetY = nv;
    render();
  });

  /* 高斯模糊 */
  const bl = $id('#p-blur'); bl.value = layer.blur || 0;
  updateTag('p-blur-tag', (layer.blur || 0) + 'px');
  armInput(bl, v => { layer.blur = clampNum(v, 0, 100); updateTag('p-blur-tag', layer.blur + 'px'); render(); });

  /* 填充方式：纯色 / 线性渐变 */
  const fillBtns = pc.querySelectorAll('[data-fill]');
  const setFillUI = () => {
    fillBtns.forEach(b => b.classList.toggle('active', (b.dataset.fill === 'gradient') === layer.gradientOn));
    $id('#p-color-row').style.display = layer.gradientOn ? 'none' : '';
    $id('#p-grad-block').style.display = layer.gradientOn ? '' : 'none';
  };
  setFillUI();
  fillBtns.forEach(b => b.addEventListener('click', () => {
    pushUndo();
    layer.gradientOn = b.dataset.fill === 'gradient';
    setFillUI();
    render();
  }));

  const ga = $id('#p-gradAngle'); ga.value = layer.gradientAngle;
  updateTag('p-gradAngle-tag', layer.gradientAngle + '°');
  armInput(ga, v => { layer.gradientAngle = clampNum(v, 0, 359); updateTag('p-gradAngle-tag', layer.gradientAngle + '°'); render(); });

  const stopBox = $id('#p-stops');
  const rerenderStops = () => {
    renderStops(stopBox, layer.gradientStops, () => render());
    $id('#p-stopDel').disabled = layer.gradientStops.length <= 2;
  };
  rerenderStops();
  $id('#p-stopAdd').addEventListener('click', () => { pushUndo(); addGradientStop(layer.gradientStops); rerenderStops(); render(); });
  $id('#p-stopDel').addEventListener('click', () => {
    if (layer.gradientStops.length <= 2) return;
    pushUndo();
    const sorted = [...layer.gradientStops].sort((a, b) => a.pos - b.pos);
    const last = sorted[sorted.length - 1];
    layer.gradientStops.splice(layer.gradientStops.indexOf(last), 1);
    rerenderStops();
    render();
  });

  const px = $id('#p-x'); px.value = Math.round(layer.x);
  armInput(px, v => {
    if (layer.autoCenter && +v !== layer.x) { layer.autoCenter = false; ac.checked = false; }
    layer.x = +v;
    render();
  });

  const py = $id('#p-y'); py.value = Math.round(layer.y);
  armInput(py, v => {
    if (layer.autoCenter && +v !== layer.y) { layer.autoCenter = false; ac.checked = false; }
    layer.y = +v;
    render();
  });

  const nm = $id('#p-name'); nm.value = layer.name;
  armInput(nm, v => { layer.name = v; renderLayers(); render(); });

  const bBtn = pc.querySelector('[data-b]'); bBtn.classList.toggle('active', layer.bold);
  bBtn.addEventListener('click', () => { pushUndo(); layer.bold = !layer.bold; bBtn.classList.toggle('active', layer.bold); maybeAutoCenter(layer); render(); });

  const iBtn = pc.querySelector('[data-i]'); iBtn.classList.toggle('active', layer.italic);
  iBtn.addEventListener('click', () => { pushUndo(); layer.italic = !layer.italic; iBtn.classList.toggle('active', layer.italic); maybeAutoCenter(layer); render(); });

  const aBtns = pc.querySelectorAll('[data-a]');
  aBtns.forEach(b => {
    b.classList.toggle('active', b.dataset.a === layer.align);
    b.addEventListener('click', () => {
      pushUndo();
      layer.align = b.dataset.a;
      aBtns.forEach(x => x.classList.toggle('active', x === b));
      render();
    });
  });
}

function imagePropsHTML() {
  return `
  <div class="prop"><label>图片</label>
    <button type="button" class="btn block" id="p-replace">🖼 替换图片…</button>
  </div>
  <div class="prop"><label>定位</label>
    <button type="button" class="btn block" id="p-center">⦿ 居中到画布</button>
  </div>
  <div class="prop-row">
    <div class="prop grow"><label>X 偏移</label><input type="number" id="p-offsetX" step="1"></div>
    <div class="prop grow"><label>Y 偏移</label><input type="number" id="p-offsetY" step="1"></div>
  </div>
  <div class="prop"><label>尺寸（像素，可拉伸）</label></div>
  <div class="prop-row">
    <div class="prop grow"><label>宽 W</label><input type="number" id="p-w" min="1" step="1"></div>
    <div class="prop grow"><label>高 H</label><input type="number" id="p-h" min="1" step="1"></div>
  </div>
  <div class="prop-row">
    <div class="prop grow"><label>位置 X（绝对）</label><input type="number" id="p-x" step="1"></div>
    <div class="prop grow"><label>位置 Y（绝对）</label><input type="number" id="p-y" step="1"></div>
  </div>
  <div class="prop"><label>不透明度 <span class="val-tag" id="p-opacity-tag"></span></label>
    <input type="range" id="p-opacity" min="0" max="100" step="1">
  </div>
  <div class="prop"><label>高斯模糊 <span class="val-tag" id="p-blur-tag"></span></label>
    <input type="range" id="p-blur" min="0" max="100" step="1">
  </div>
  <div class="prop"><label>图层名称</label><input type="text" id="p-name"></div>
  <p class="hint small">提示：拖动四角手柄可等比缩放；双击画布中的图片可快速替换。</p>`;
}

function bindImageProps(layer) {
  const pc = propsContent;
  const $id = id => pc.querySelector(id);

  $id('#p-replace').addEventListener('click', () => requestImageFile(src => {
    pushUndo(); layer.src = src; render();
  }));

  $id('#p-center').addEventListener('click', () => { pushUndo(); centerLayer(layer); render(); });

  const ox = $id('#p-offsetX'); ox.value = layer.offsetX || 0;
  armInput(ox, v => {
    const nv = clampNum(v, -100000, 100000);
    layer.x += nv - (layer.offsetX || 0);
    layer.offsetX = nv;
    render();
  });
  const oy = $id('#p-offsetY'); oy.value = layer.offsetY || 0;
  armInput(oy, v => {
    const nv = clampNum(v, -100000, 100000);
    layer.y += nv - (layer.offsetY || 0);
    layer.offsetY = nv;
    render();
  });

  const bl = $id('#p-blur'); bl.value = layer.blur || 0;
  updateTag('p-blur-tag', (layer.blur || 0) + 'px');
  armInput(bl, v => { layer.blur = clampNum(v, 0, 100); updateTag('p-blur-tag', layer.blur + 'px'); render(); });

  const wI = $id('#p-w'); wI.value = Math.round(layer.w);
  armInput(wI, v => { layer.w = clampNum(v, 1, 32000); render(); });

  const hI = $id('#p-h'); hI.value = Math.round(layer.h);
  armInput(hI, v => { layer.h = clampNum(v, 1, 32000); render(); });

  const px = $id('#p-x'); px.value = Math.round(layer.x);
  armInput(px, v => { layer.x = +v; render(); });

  const py = $id('#p-y'); py.value = Math.round(layer.y);
  armInput(py, v => { layer.y = +v; render(); });

  const op = $id('#p-opacity'); op.value = Math.round(layer.opacity * 100);
  updateTag('p-opacity-tag', Math.round(layer.opacity * 100) + '%');
  armInput(op, v => { layer.opacity = clampNum(v, 0, 100) / 100; updateTag('p-opacity-tag', Math.round(layer.opacity * 100) + '%'); render(); });

  const nm = $id('#p-name'); nm.value = layer.name;
  armInput(nm, v => { layer.name = v; renderLayers(); render(); });
}

function bgPropsHTML() {
  return `
  <div class="prop"><label>背景类型</label>
    <select id="bg-type">
      <option value="solid">纯色</option>
      <option value="gradient">线性渐变</option>
      <option value="image">图片</option>
      <option value="transparent">透明</option>
    </select>
  </div>
  <div id="bg-solid" class="bg-group">
    <div class="prop"><label>颜色</label><input type="color" id="bg-color"></div>
  </div>
  <div id="bg-gradient" class="bg-group">
    <div class="prop"><label>角度 <span class="val-tag" id="bg-angle-tag"></span></label>
      <input type="range" id="bg-angle" min="0" max="359" step="1">
    </div>
    <div class="prop"><label>渐变色（拖位置 / 点颜色修改）</label>
      <div class="stop-list" id="bg-stops"></div>
      <div class="mini-btns">
        <button type="button" class="btn mini" id="bg-stopAdd">＋ 添加颜色</button>
        <button type="button" class="btn mini" id="bg-stopDel">－ 移除颜色</button>
      </div>
    </div>
  </div>
  <div id="bg-image" class="bg-group">
    <button type="button" class="btn block" id="bg-choose">🖼 选择背景图片…</button>
    <div class="prop"><label>填充方式</label>
      <select id="bg-fit">
        <option value="cover">覆盖（裁剪填充）</option>
        <option value="stretch">拉伸（可能变形）</option>
      </select>
    </div>
    <button type="button" class="btn block danger-ghost" id="bg-remove">移除背景图片</button>
  </div>
  <div class="prop" id="bg-blur-row"><label>高斯模糊 <span class="val-tag" id="bg-blur-tag"></span></label>
    <input type="range" id="bg-blur" min="0" max="100" step="1">
  </div>`;
}

function bindBgProps() {
  const bg = state.background;
  const pc = propsContent;
  const $id = id => pc.querySelector(id);

  const typeSel = $id('#bg-type'); typeSel.value = bg.type;
  const showGroups = () => {
    $id('#bg-solid').style.display = bg.type === 'solid' ? '' : 'none';
    $id('#bg-gradient').style.display = bg.type === 'gradient' ? '' : 'none';
    $id('#bg-image').style.display = bg.type === 'image' ? '' : 'none';
    $id('#bg-blur-row').style.display = bg.type === 'transparent' ? 'none' : '';
  };
  showGroups();
  typeSel.addEventListener('change', () => { flushOp(); pushUndo(); bg.type = typeSel.value; renderProps(); render(); });

  const c = $id('#bg-color'); c.value = bg.color;
  armInput(c, v => { bg.color = v; render(); });

  const a = $id('#bg-angle'); a.value = bg.angle;
  updateTag('bg-angle-tag', bg.angle + '°');
  armInput(a, v => { bg.angle = clampNum(v, 0, 359); updateTag('bg-angle-tag', bg.angle + '°'); render(); });

  const stopBox = $id('#bg-stops');
  const rerenderStops = () => {
    renderStops(stopBox, bg.stops, () => render());
    $id('#bg-stopDel').disabled = bg.stops.length <= 2;
  };
  rerenderStops();
  $id('#bg-stopAdd').addEventListener('click', () => { pushUndo(); addGradientStop(bg.stops); rerenderStops(); render(); });
  $id('#bg-stopDel').addEventListener('click', () => {
    if (bg.stops.length <= 2) return;
    pushUndo();
    const sorted = [...bg.stops].sort((x, y) => x.pos - y.pos);
    const last = sorted[sorted.length - 1];
    bg.stops.splice(bg.stops.indexOf(last), 1);
    rerenderStops();
    render();
  });

  const bl = $id('#bg-blur'); bl.value = bg.blur || 0;
  updateTag('bg-blur-tag', (bg.blur || 0) + 'px');
  armInput(bl, v => { bg.blur = clampNum(v, 0, 100); updateTag('bg-blur-tag', bg.blur + 'px'); render(); });

  const fit = $id('#bg-fit'); fit.value = bg.fit;
  fit.addEventListener('change', () => { pushUndo(); bg.fit = fit.value; render(); });

  $id('#bg-choose').addEventListener('click', () => bgFileInput.click());
  $id('#bg-remove').addEventListener('click', () => { pushUndo(); bg.image = null; render(); });
}

function renderProps() {
  const box = propsContent, t = propsTitle;
  if (state.selectedId === BG_ID) {
    t.textContent = '背景属性';
    box.innerHTML = bgPropsHTML();
    bindBgProps();
    return;
  }
  const layer = selectedLayer();
  if (!layer) {
    t.textContent = '属性';
    box.innerHTML =
      '<div class="hint">未选中任何图层。<br>· 点击画布中的图层，或在右侧图层列表中选择。<br>· 双击画布中的文字可直接编辑内容。<br>· 在图层列表中可以拖动调整上下顺序。</div>';
    return;
  }
  t.textContent = layer.type === 'text' ? '文字属性' : '图片属性';
  box.innerHTML = layer.type === 'text' ? textPropsHTML() : imagePropsHTML();
  if (layer.type === 'text') bindTextProps(layer);
  else bindImageProps(layer);
  if (state.focusText && layer.type === 'text') {
    const ta = box.querySelector('#p-text');
    if (ta) { ta.focus(); ta.setSelectionRange(ta.value.length, ta.value.length); }
    state.focusText = false;
  }
}

/* ==================== 文件读取 ==================== */
function readImageFile(file) {
  return new Promise((res, rej) => {
    const r = new FileReader();
    r.onload = () => res(r.result);
    r.onerror = rej;
    r.readAsDataURL(file);
  });
}

function requestImageFile(cb) {
  window._fileCb = cb;
  fileInput.click();
}

/* ==================== 导出 ==================== */
function exportImage(fmt) {
  const off = document.createElement('canvas');
  off.width = state.canvas.w; off.height = state.canvas.h;
  const g = off.getContext('2d');
  if (fmt === 'jpg' && state.background.type === 'transparent') {
    g.fillStyle = '#ffffff'; g.fillRect(0, 0, off.width, off.height);
  }
  renderScene(g, off.width, off.height);
  off.toBlob(blob => {
    if (!blob) { toast('导出失败'); return; }
    const a = document.createElement('a');
    a.href = URL.createObjectURL(blob);
    a.download = `canvas_${state.canvas.w}x${state.canvas.h}_${Date.now()}.${fmt === 'jpg' ? 'jpg' : 'png'}`;
    document.body.appendChild(a);
    a.click();
    a.remove();
    setTimeout(() => URL.revokeObjectURL(a.href), 5000);
    toast(`已导出 ${fmt.toUpperCase()} 图片`);
  }, fmt === 'jpg' ? 'image/jpeg' : 'image/png', 0.92);
}

/* ==================== 交互（画布鼠标） ==================== */
function updateCursor(e) {
  const r = canvasEl.getBoundingClientRect();
  const inside = e.clientX >= r.left && e.clientX <= r.right && e.clientY >= r.top && e.clientY <= r.bottom;
  if (!inside) return;
  if (state.tool === 'text') { canvasEl.style.cursor = 'crosshair'; return; }
  const p = canvasPos(e);
  const h = getHandleAt(p.x, p.y);
  if (h) { canvasEl.style.cursor = (h === 'nw' || h === 'se') ? 'nwse-resize' : 'nesw-resize'; return; }
  canvasEl.style.cursor = hitTest(p.x, p.y) ? 'move' : 'default';
}

function bindCanvasMouse() {
  canvasEl.addEventListener('mousedown', e => {
    if (e.button !== 0) return;
    const p = canvasPos(e);

    /* 文字工具：在点击处新建文字图层并立刻拖动 */
    if (state.tool === 'text') {
      pushUndo();
      const layer = addTextLayerAt(p.x, p.y);
      setTool('select');
      state.focusText = true;
      renderProps();
      drag = { mode: 'move', id: layer.id, startMX: p.x, startMY: p.y, origX: layer.x, origY: layer.y };
      canvasEl.style.cursor = 'move';
      e.preventDefault();
      return;
    }

    const h = getHandleAt(p.x, p.y);
    if (h) {
      const layer = selectedLayer();
      beginOp();
      const box = getLayerBox(layer);
      drag = {
        mode: 'resize', id: layer.id, handle: h,
        startMX: p.x, startMY: p.y,
        origX: layer.x, origY: layer.y, origW: layer.w, origH: layer.h, origFont: layer.fontSize,
        box,
        aspect: layer.w / layer.h,
        anchor: { x: h.includes('w') ? box.x + box.w : box.x, y: h.includes('n') ? box.y + box.h : box.y },
        d0: Math.hypot(p.x - (box.x + box.w / 2), p.y - (box.y + box.h / 2)),
      };
      e.preventDefault();
      return;
    }

    const hit = hitTest(p.x, p.y);
    if (hit) {
      if (state.selectedId !== hit.id) select(hit.id);
      beginOp();
      drag = { mode: 'move', id: hit.id, startMX: p.x, startMY: p.y, origX: hit.x, origY: hit.y };
      e.preventDefault();
    } else if (state.selectedId !== null) {
      select(null);
    }
  });

  window.addEventListener('mousemove', e => {
    if (!drag) { updateCursor(e); return; }
    const p = canvasPos(e);
    const layer = state.layers.find(l => l.id === drag.id);
    if (!layer) return;
    if (drag.mode === 'move') {
      layer.x = drag.origX + (p.x - drag.startMX);
      layer.y = drag.origY + (p.y - drag.startMY);
    } else if (layer.type === 'image') {
      const w = clamp(Math.abs(p.x - drag.anchor.x), 8, 32000);
      const h = w / drag.aspect;
      layer.w = w; layer.h = h;
      layer.x = p.x < drag.anchor.x ? drag.anchor.x - w : drag.anchor.x;
      layer.y = p.y < drag.anchor.y ? drag.anchor.y - h : drag.anchor.y;
    } else {
      const cx = drag.box.x + drag.box.w / 2, cy = drag.box.y + drag.box.h / 2;
      const d = Math.hypot(p.x - cx, p.y - cy);
      layer.fontSize = clamp(drag.origFont * (d / Math.max(drag.d0, 0.001)), 8, 800);
      const nb = getLayerBox(layer);
      layer.x = drag.handle.includes('w') ? drag.anchor.x - nb.w : drag.anchor.x;
      layer.y = drag.handle.includes('n') ? drag.anchor.y - nb.h : drag.anchor.y;
    }
    render();
  });

  window.addEventListener('mouseup', () => {
    if (drag) {
      /* 手动拖动/缩放文字图层后，关闭「实时居中」 */
      const l = state.layers.find(x => x.id === drag.id);
      if (l && l.type === 'text' && l.autoCenter) {
        const moved = drag.mode === 'move'
          ? (l.x !== drag.origX || l.y !== drag.origY)
          : (l.x !== drag.origX || l.y !== drag.origY || l.fontSize !== drag.origFont);
        if (moved) { l.autoCenter = false; renderProps(); }
      }
      endOp(); drag = null; canvasEl.style.cursor = state.tool === 'text' ? 'crosshair' : 'default';
    }
  });

  canvasEl.addEventListener('dblclick', e => {
    const p = canvasPos(e);
    const hit = hitTest(p.x, p.y);
    if (!hit) return;
    select(hit.id);
    if (hit.type === 'text') {
      state.focusText = true;
      renderProps();
    } else {
      requestImageFile(src => { pushUndo(); hit.src = src; render(); });
    }
  });

  canvasEl.addEventListener('contextmenu', e => e.preventDefault());
}

/* ==================== 拖放图片文件 ==================== */
function bindDragDrop() {
  canvasArea.addEventListener('dragover', e => {
    if (e.dataTransfer.types.includes('Files')) {
      e.preventDefault();
      canvasArea.classList.add('drop-hint');
    }
  });
  canvasArea.addEventListener('dragleave', e => {
    if (e.target === canvasArea) canvasArea.classList.remove('drop-hint');
  });
  canvasArea.addEventListener('drop', e => {
    e.preventDefault();
    canvasArea.classList.remove('drop-hint');
    const files = [...e.dataTransfer.files].filter(f => f.type.startsWith('image/'));
    if (!files.length) { toast('请拖入图片文件'); return; }
    const p = canvasPos(e);
    const cx = clamp(p.x, 0, state.canvas.w), cy = clamp(p.y, 0, state.canvas.h);
    files.forEach(f => readImageFile(f).then(src => addImageLayer(src, cx, cy)));
  });
}

/* ==================== 工具切换 ==================== */
function setTool(t) {
  state.tool = t;
  toolSelect.classList.toggle('active', t === 'select');
  toolText.classList.toggle('active', t === 'text');
  canvasEl.style.cursor = t === 'text' ? 'crosshair' : 'default';
}

/* ==================== 快捷键 ==================== */
function nudge(dx, dy, e) {
  const l = selectedLayer();
  if (!l) return;
  e.preventDefault();
  beginOp();
  const step = e.shiftKey ? 10 : 1;
  l.x += dx * step;
  l.y += dy * step;
  render();
  endOp();
}

function bindKeyboard() {
  window.addEventListener('keydown', e => {
    const tag = (e.target.tagName || '').toLowerCase();
    if (['input', 'textarea', 'select'].includes(tag)) return;
    const mod = e.ctrlKey || e.metaKey;
    const k = e.key.toLowerCase();
    if (mod && k === 'z') { e.preventDefault(); if (e.shiftKey) redo(); else undo(); return; }
    if (mod && k === 'y') { e.preventDefault(); redo(); return; }
    if (mod && k === 'd') { e.preventDefault(); duplicateSelected(); return; }
    switch (e.key) {
      case 'Delete': case 'Backspace': e.preventDefault(); deleteSelected(); break;
      case 'Escape': select(null); break;
      case 'v': case 'V': setTool('select'); break;
      case 't': case 'T': setTool('text'); break;
      case 'ArrowLeft': nudge(-1, 0, e); break;
      case 'ArrowRight': nudge(1, 0, e); break;
      case 'ArrowUp': nudge(0, -1, e); break;
      case 'ArrowDown': nudge(0, 1, e); break;
    }
  });
}

/* ==================== 初始化 ==================== */
function buildPresetSelect() {
  canvasPreset.innerHTML = CANVAS_PRESETS.map(p => `<option value="${p.w}x${p.h}">${p.label}</option>`).join('');
  canvasPreset.addEventListener('change', () => {
    const v = canvasPreset.value;
    if (v === 'custom') return;
    const [w, h] = v.split('x').map(Number);
    applyCanvasSize(w, h, true);
  });
}

function updatePresetSelect() {
  const found = CANVAS_PRESETS.find(p => p.w === state.canvas.w && p.h === state.canvas.h);
  if (found) { canvasPreset.value = `${found.w}x${found.h}`; return; }
  let opt = canvasPreset.querySelector('option[value="custom"]');
  if (!opt) { opt = document.createElement('option'); opt.value = 'custom'; canvasPreset.appendChild(opt); }
  opt.textContent = `${state.canvas.w}×${state.canvas.h}（自定义）`;
  canvasPreset.value = 'custom';
}

function bindAll() {
  btnUndo.addEventListener('click', undo);
  btnRedo.addEventListener('click', redo);
  toolSelect.addEventListener('click', () => setTool('select'));
  toolText.addEventListener('click', () => setTool('text'));

  btnZoomFit.addEventListener('click', () => { zoomMode = 'fit'; applyZoom(); });
  zoomRange.addEventListener('input', () => { zoomMode = 'manual'; zoomVal = +zoomRange.value / 100; applyZoom(); });

  btnExportPng.addEventListener('click', () => exportImage('png'));
  btnExportJpg.addEventListener('click', () => exportImage('jpg'));

  btnAddText.addEventListener('click', () => {
    pushUndo();
    const l = addTextLayerAt(state.canvas.w * 0.1, state.canvas.h * 0.4);
    l.autoCenter = true;
    centerLayer(l);
    state.focusText = true;
    renderProps();
    render();
  });

  btnAddImage.addEventListener('click', () => requestImageFile(src => addImageLayer(src)));
  btnDup.addEventListener('click', duplicateSelected);
  btnDel.addEventListener('click', deleteSelected);
  btnLayerUp.addEventListener('click', () => moveLayer(1));
  btnLayerDown.addEventListener('click', () => moveLayer(-1));

  btnCustomSize.addEventListener('click', () => {
    const w = parseInt(prompt('画布宽度（像素，64–8000）：', '1080') || '', 10);
    if (!w) return;
    const h = parseInt(prompt('画布高度（像素，64–8000）：', '1080') || '', 10);
    if (!h) return;
    applyCanvasSize(clampNum(w, 64, 8000), clampNum(h, 64, 8000), true);
  });

  btnNew.addEventListener('click', () => {
    if (!confirm('确定清空全部图层并恢复默认设置吗？')) return;
    pushUndo();
    state.layers = [];
    state.selectedId = null;
    state.background = { type: 'solid', color: '#232539', angle: 135, stops: [{ pos: 0, color: '#667eea' }, { pos: 100, color: '#764ba2' }], image: null, fit: 'cover', blur: 0 };
    applyCanvasSize(1080, 1080, false);
    renderLayers(); renderProps(); render();
  });

  document.querySelectorAll('.align-btn').forEach(b =>
    b.addEventListener('click', () => alignSelected(b.dataset.align)));
  btnCenterBoth.addEventListener('click', () => alignSelected('both'));

  /* 图层列表：点击 / 拖拽排序 */
  layerList.addEventListener('click', e => {
    const li = e.target.closest('li');
    if (!li) return;
    const id = li.dataset.id;
    if (e.target.classList.contains('eye')) { if (id !== BG_ID) toggleVisible(id); return; }
    if (e.target.classList.contains('del')) {
      if (id === BG_ID) toast('背景图层不能删除');
      else deleteLayer(id);
      return;
    }
    select(id);
  });

  layerList.addEventListener('dragstart', e => {
    const li = e.target.closest('li');
    if (!li || li.dataset.id === BG_ID) { e.preventDefault(); return; }
    dragLayerId = li.dataset.id;
    prevDnDSnapshot = snapshot();
    li.classList.add('dragging');
  });
  layerList.addEventListener('dragover', e => {
    if (!dragLayerId) return;
    e.preventDefault();
    const li = e.target.closest('li');
    if (!li) return;
    const dragged = layerList.querySelector('li.dragging');
    if (!dragged || li === dragged) return;
    const r = li.getBoundingClientRect();
    if (e.clientY > r.top + r.height / 2) li.insertAdjacentElement('afterend', dragged);
    else li.insertAdjacentElement('beforebegin', dragged);
  });
  layerList.addEventListener('dragend', () => {
    if (dragLayerId) {
      syncLayersFromDom();
      if (prevDnDSnapshot != null && snapshot() !== prevDnDSnapshot) {
        undoStack.push(prevDnDSnapshot);
        if (undoStack.length > 60) undoStack.shift();
        redoStack = [];
        updateUndoButtons();
      }
    }
    dragLayerId = null; prevDnDSnapshot = null;
    layerList.querySelectorAll('li.dragging').forEach(x => x.classList.remove('dragging'));
  });
  layerList.addEventListener('drop', e => e.preventDefault());

  /* 文件输入 */
  fileInput.addEventListener('change', () => {
    const files = [...fileInput.files];
    fileInput.value = '';
    if (!files.length) return;
    const cb = window._fileCb;
    window._fileCb = null;
    files.forEach((f, idx) =>
      readImageFile(f).then(src => {
        if (cb && idx === 0) cb(src);
        else addImageLayer(src);
      }));
  });

  bgFileInput.addEventListener('change', () => {
    const f = bgFileInput.files[0];
    bgFileInput.value = '';
    if (!f) return;
    readImageFile(f).then(src => {
      pushUndo();
      state.background.image = src;
      state.background.type = 'image';
      render();
      renderProps();
    });
  });

  bindCanvasMouse();
  bindDragDrop();
  bindKeyboard();

  new ResizeObserver(() => { if (zoomMode === 'fit') applyZoom(); }).observe(canvasArea);

  updateUndoButtons();
}

function init() {
  canvasEl = $('#canvas'); ctx = canvasEl.getContext('2d');
  canvasArea = $('#canvasArea');
  layerList = $('#layerList');
  propsContent = $('#propsContent'); propsTitle = $('#propsTitle');
  statusbar = $('#statusbar');
  zoomRange = $('#zoomRange'); zoomLabel = $('#zoomLabel');
  canvasPreset = $('#canvasPreset');
  fileInput = $('#fileInput'); bgFileInput = $('#bgFileInput');
  btnUndo = $('#btnUndo'); btnRedo = $('#btnRedo');
  toolSelect = $('#toolSelect'); toolText = $('#toolText');
  btnZoomFit = $('#btnZoomFit');
  btnExportPng = $('#btnExportPng'); btnExportJpg = $('#btnExportJpg');
  btnAddText = $('#btnAddText'); btnAddImage = $('#btnAddImage');
  btnDup = $('#btnDup'); btnDel = $('#btnDel');
  btnLayerUp = $('#btnLayerUp'); btnLayerDown = $('#btnLayerDown');
  btnCustomSize = $('#btnCustomSize'); btnNew = $('#btnNew');
  btnCenterBoth = $('#btnCenterBoth');

  buildPresetSelect();

  /* 示例文字图层，方便快速上手 */
  const sample = {
    id: uid(), type: 'text', name: '文字 1',
    text: '双击编辑文字',
    x: 0, y: 0,
    fontSize: 84,
    fontFamily: '"Microsoft YaHei", sans-serif',
    color: '#ffffff', bold: false, italic: false, align: 'center',
    lineHeight: 1.2, strokeColor: '#000000', strokeWidth: 0,
    shadowOn: false, shadowBlur: 8, shadowColor: '#000000',
    opacity: 1, visible: true,
    gradientOn: false, gradientAngle: 0,
    gradientStops: [{ pos: 0, color: '#ffd166' }, { pos: 100, color: '#ef476f' }],
    blur: 0, offsetX: 0, offsetY: 0, autoCenter: true,
  };
  const m = measureTextLayer(sample);
  sample.x = (state.canvas.w - m.w) / 2;
  sample.y = (state.canvas.h - m.h) / 2;
  state.layers.push(sample);

  applyCanvasSize(state.canvas.w, state.canvas.h, false);
  select(sample.id);
  setTool('select');
  bindAll();
}

init();

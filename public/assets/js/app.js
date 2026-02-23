
// ══════════════════════════════════════════════════════════════
//  CONSTANTS & STATE
// ══════════════════════════════════════════════════════════════
const KAABA = { lat: 21.4225, lng: 39.8262 };

// ── Tile cache: stores loaded bbox cells to avoid duplicate queries
// Key: "lat_lng_zoom" grid cell (0.05° grid), Value: true
const tileCache = new Set();
// All processed mosque data (keyed by OSM id)
const mosqueDB = new Map();

let tol = 15;
let map = null;
let tileLayer = null;
let renderLayers = [];
let animLayers = [];
let focusPulseLayer = null;
let focusPulseRaf = 0;
let markerClusterLayer = null;
let placeBoundaryLayer = null;
let vpDebounceTimer = null;
let vpWatchdogTimer = null;
let vpNeedsReload = false;
let isVpLoading = false;
let searchAreaAnchor = null;
let searchAreaArmed = false;
let lastSidebarVisiblePx = 0;
let heatLayer = null;
let heatVisible = false;
let scoreCardVisible = false;
let currentCity = '';
let denseModeNotified = false;
const wikidataLabelCache = new Map();
const NAME_ENRICH_KEY = 'qibla-name-enrich-v1';
const INTERIOR_KEY = 'qibla-interior-v1';
const SNAPSHOT_KEY = 'qibla-snapshots-v1';
const LANG_KEY = 'qibla-lang-v1';
const MANUAL_AXIS_KEY = 'qibla-manual-axis-v1';
const OUTDOOR_KEY = 'qibla-outdoor-v1';
const GEO_PROMPT_KEY = 'qibla-geo-prompt-v1';
const POPULARITY_KEY = 'qibla-popularity-v1';
const VISIT_TRAFFIC_KEY = 'qibla-visit-traffic-v1';
const CITY_SEARCH_HISTORY_KEY = 'qibla-city-history-v1';
const THEME_KEY = 'qibla-theme-v10';
const nameEnrichCache = new Map();
const nameEnrichQueue = [];
const nameEnrichQueued = new Set();
let nameEnrichRunning = false;
let interiorDB = {};
let analysisLayerMode = 'final'; // final | raw | interior
let snapshots = [];
let currentLang = 'tr';
let manualAxisDB = {};
const popularityCache = new Map();
const popularityInFlight = new Set();
const visitTrafficCache = new Map();
let citySearchHistory = [];
let manualCapture = { active:false, markers:[], line:null, points:[] };
let compassState = { running:false, heading:null, qibla:null, loc:null, watchId:null };
let followState = { enabled:false, watchId:null, lastFixAt:0 };
let userGeoState = { lat:null, lng:null, enabled:false, ts:0 };
let uiState = { mapSyncWithCompass:false, outdoor:false, pullRefreshing:false, sheetSnap:15, liveMapCompass:false };
let m3dState = { renderer:null, scene:null, camera:null, raf:0, obj:null };
let reverseTapState = { busy:false, lastAt:0, seq:0 };
const MOBILE_SHEET_SNAP = Object.freeze({ min:15, half:50, full:95 });
let mobileSheetSnapIdx = 1;
let mobileSheetSyncTimer = 0;
const districtBoundaryCache = new Map();
const districtState = {
  enabled: false,
  reverseBusy: false,
  lastReverseAt: 0,
  reverseSeq: 0,
  hoverName: '',
  hoverContextCity: '',
  hoverContextCountry: '',
  selectedName: '',
  selectedGeo: null,
  selectedBBox: null,
  layer: null
};
const API_RATE = {
  nominatim: { nextAt:0, cooldown:0, minInterval:1100 },
  overpass: { nextAt:0, cooldown:0, minInterval:500 }
};
const GEO_CACHE_DB = 'qibla-geo-cache-v1';
const GEO_CACHE_STORE = 'bbox';
const GEO_CACHE_TTL_MS = 1000 * 60 * 60 * 24 * 5;
let geoCacheDb = null;
let geoCacheReady = false;

function haptic(ms = 10) {
  try {
    if (navigator.vibrate) navigator.vibrate(Math.max(5, Math.min(50, ms|0)));
  } catch {}
}

function setUserGeoState(lat, lng, enabled = true) {
  if (!Number.isFinite(lat) || !Number.isFinite(lng)) return;
  userGeoState.lat = lat;
  userGeoState.lng = lng;
  userGeoState.enabled = !!enabled;
  userGeoState.ts = Date.now();
}

function applyThemeMode(mode = 'dark', persist = true) {
  const normalized = String(mode || 'dark').toLowerCase() === 'light' ? 'light' : 'dark';
  document.documentElement.classList.toggle('light-theme', normalized === 'light');
  document.documentElement.classList.toggle('dark-theme', normalized !== 'light');
  document.body.classList.toggle('light-theme', normalized === 'light');
  document.body.classList.toggle('dark-theme', normalized !== 'light');
  // Backward compatibility for previous style hooks.
  document.documentElement.classList.toggle('light-mode', normalized === 'light');
  document.body.classList.toggle('light-mode', normalized === 'light');
  if (persist) safeStorageSet(THEME_KEY, normalized);
  const btn = document.getElementById('theme-toggle-btn');
  if (btn) {
    const next = normalized === 'light' ? 'dark' : 'light';
    btn.textContent = normalized === 'light' ? '☾' : '☀';
    btn.setAttribute('aria-label', next === 'light' ? 'Açık moda geç' : 'Koyu moda geç');
    btn.setAttribute('title', next === 'light' ? 'Açık moda geç' : 'Koyu moda geç');
  }
}

function toggleThemeMode() {
  const isLight =
    document.documentElement.classList.contains('light-theme') ||
    document.body.classList.contains('light-theme') ||
    document.body.classList.contains('light-mode');
  applyThemeMode(isLight ? 'dark' : 'light', true);
}

window.toggleThemeMode = toggleThemeMode;

function safeStorageGet(key, fallback = null) {
  try {
    const raw = localStorage.getItem(key);
    return raw == null ? fallback : raw;
  } catch {
    return fallback;
  }
}

function trimObjectByCount(obj, max = 300) {
  if (!obj || typeof obj !== 'object') return obj;
  const entries = Object.entries(obj);
  if (entries.length <= max) return obj;
  entries.sort((a,b) => (b[1]?.at || b[1]?.ts || b[1]?.time || 0) - (a[1]?.at || a[1]?.ts || a[1]?.time || 0));
  return Object.fromEntries(entries.slice(0, max));
}

function storageCleanup() {
  try {
    const rawSnaps = safeStorageGet(SNAPSHOT_KEY, '[]');
    let snaps = [];
    try { snaps = JSON.parse(rawSnaps) || []; } catch {}
    if (Array.isArray(snaps) && snaps.length > 80) localStorage.setItem(SNAPSHOT_KEY, JSON.stringify(snaps.slice(-80)));

    const rawName = safeStorageGet(NAME_ENRICH_KEY, '{}');
    let nameObj = {};
    try { nameObj = JSON.parse(rawName) || {}; } catch {}
    localStorage.setItem(NAME_ENRICH_KEY, JSON.stringify(trimObjectByCount(nameObj, 600)));

    const rawInt = safeStorageGet(INTERIOR_KEY, '{}');
    let intObj = {};
    try { intObj = JSON.parse(rawInt) || {}; } catch {}
    localStorage.setItem(INTERIOR_KEY, JSON.stringify(trimObjectByCount(intObj, 220)));

    const rawManual = safeStorageGet(MANUAL_AXIS_KEY, '{}');
    let manObj = {};
    try { manObj = JSON.parse(rawManual) || {}; } catch {}
    localStorage.setItem(MANUAL_AXIS_KEY, JSON.stringify(trimObjectByCount(manObj, 380)));

    const lbKey = 'qibla-leaderboard-v2';
    const rawLb = safeStorageGet(lbKey, '[]');
    let lb = [];
    try { lb = JSON.parse(rawLb) || []; } catch {}
    if (Array.isArray(lb) && lb.length > 320) localStorage.setItem(lbKey, JSON.stringify(lb.slice(0, 320)));
  } catch {}
}

function safeStorageSet(key, value) {
  try {
    localStorage.setItem(key, value);
    return true;
  } catch {
    storageCleanup();
    try {
      localStorage.setItem(key, value);
      return true;
    } catch {
      return false;
    }
  }
}

let activeSearchController = null;

function makeAbortError(msg = 'Arama iptal edildi') {
  const err = new Error(msg);
  err.name = 'AbortError';
  return err;
}

function throwIfAborted(signal) {
  if (signal?.aborted) throw makeAbortError();
}

function waitWithAbort(ms, signal) {
  if (!ms || ms <= 0) {
    throwIfAborted(signal);
    return Promise.resolve();
  }
  return new Promise((resolve, reject) => {
    if (signal?.aborted) return reject(makeAbortError());
    const timer = setTimeout(() => {
      cleanup();
      resolve();
    }, ms);
    const onAbort = () => {
      cleanup();
      reject(makeAbortError());
    };
    const cleanup = () => {
      clearTimeout(timer);
      signal?.removeEventListener('abort', onAbort);
    };
    signal?.addEventListener('abort', onAbort, { once:true });
  });
}

function isOverlayVisible() {
  return document.getElementById('overlay')?.style.display === 'flex';
}

function syncSearchCancelUi() {
  const btn = document.getElementById('ov-cancel');
  if (!btn) return;
  btn.style.display = activeSearchController ? 'inline-flex' : 'none';
}

function cancelActiveSearch(opts = {}) {
  if (!activeSearchController) return false;
  try { activeSearchController.abort(); } catch {}
  activeSearchController = null;
  syncSearchCancelUi();
  setVpStatus('idle');
  hideMini();
  setOv(false);
  if (!opts.silent) toast('Arama iptal edildi', 1800);
  return true;
}

async function limitedFetch(url, opts = {}, policy = {}) {
  const signal = policy.signal;
  const hostKey = policy.hostKey || (String(url).includes('nominatim') ? 'nominatim' : 'overpass');
  const st = API_RATE[hostKey] || { nextAt:0, cooldown:0, minInterval:650 };
  const retries = Number.isFinite(policy.retries) ? policy.retries : 2;
  const timeoutMs = Number.isFinite(policy.timeoutMs) ? policy.timeoutMs : 30000;
  const baseBackoff = Number.isFinite(policy.backoffMs) ? policy.backoffMs : 900;
  st.minInterval = Math.max(st.minInterval || 0, policy.minInterval || st.minInterval || 450);
  API_RATE[hostKey] = st;

  for (let i = 0; i <= retries; i++) {
    throwIfAborted(signal);
    const wait = Math.max(0, (st.nextAt || 0) - Date.now());
    if (wait > 0) await waitWithAbort(wait, signal);
    const ctrl = new AbortController();
    const timer = setTimeout(() => ctrl.abort(), timeoutMs);
    const onAbort = () => ctrl.abort();
    signal?.addEventListener('abort', onAbort, { once:true });
    try {
      throwIfAborted(signal);
      const r = await fetch(url, { ...opts, signal: ctrl.signal });
      clearTimeout(timer);
      signal?.removeEventListener('abort', onAbort);
      if (r.status === 429 || r.status === 503) {
        st.cooldown = Math.min(12000, Math.max(1100, st.cooldown ? st.cooldown * 1.65 : 1200));
        st.nextAt = Date.now() + st.cooldown + Math.round(Math.random() * 350);
        if (i < retries) continue;
      } else {
        st.cooldown = Math.max(0, Math.floor((st.cooldown || 0) * 0.55));
        st.nextAt = Date.now() + st.minInterval;
      }
      return r;
    } catch (e) {
      clearTimeout(timer);
      signal?.removeEventListener('abort', onAbort);
      if (signal?.aborted) throw makeAbortError();
      if (i >= retries) throw e;
      const pause = baseBackoff * Math.pow(1.6, i) + Math.round(Math.random()*220);
      st.nextAt = Date.now() + pause;
      await waitWithAbort(pause, signal);
    }
  }
  throw new Error('Ağ isteği sınır nedeniyle başarısız');
}

async function nominatimFetchJson(url, headers = {}, policy = {}) {
  const r = await limitedFetch(url, { headers:{'User-Agent':'QiblaChecker/1.0', ...headers} }, { hostKey:'nominatim', minInterval:1100, retries:2, timeoutMs:22000, backoffMs:1100, signal:policy.signal });
  if (!r.ok) throw new Error(`Nominatim HTTP ${r.status}`);
  return r.json();
}

function districtNameFromAddress(addr = {}) {
  return (addr.city_district || addr.county || addr.township || addr.municipality || addr.state_district || addr.suburb || '').trim();
}

function districtContextCity(addr = {}) {
  return (addr.city || addr.town || addr.municipality || addr.province || addr.state || currentCity || '').trim();
}

function districtCacheKey(name, city = '', country = '') {
  return `${normalize(trLower(name || ''))}|${normalize(trLower(city || ''))}|${normalize(trLower(country || ''))}`;
}

function updateDistrictUi() {
  const btn = document.getElementById('btn-district');
  if (btn) btn.classList.toggle('active', districtState.enabled || !!districtState.selectedGeo);

  const chip = document.getElementById('district-hover-chip');
  if (chip) {
    if (!districtState.enabled) {
      chip.classList.remove('show');
    } else if (districtState.hoverName) {
      chip.textContent = `İlçe: ${districtState.hoverName} (seçmek için tıkla)`;
      chip.classList.add('show');
    } else {
      chip.textContent = 'İlçe modu: harita üzerinde gezdirin';
      chip.classList.add('show');
    }
  }

  const pill = document.getElementById('district-pill');
  const txt = document.getElementById('district-pill-text');
  if (pill && txt) {
    if (districtState.selectedName) {
      txt.textContent = `İlçe: ${districtState.selectedName}`;
      pill.classList.add('show');
    } else {
      txt.textContent = '—';
      pill.classList.remove('show');
    }
  }
}

function computeGeoBBox(geo) {
  let minLat = Infinity, minLng = Infinity, maxLat = -Infinity, maxLng = -Infinity;
  const walk = (coords) => {
    if (!Array.isArray(coords) || !coords.length) return;
    if (typeof coords[0] === 'number') {
      const lng = Number(coords[0]);
      const lat = Number(coords[1]);
      if (!Number.isFinite(lat) || !Number.isFinite(lng)) return;
      if (lat < minLat) minLat = lat;
      if (lat > maxLat) maxLat = lat;
      if (lng < minLng) minLng = lng;
      if (lng > maxLng) maxLng = lng;
      return;
    }
    coords.forEach(walk);
  };
  walk(geo?.coordinates);
  if (!Number.isFinite(minLat) || !Number.isFinite(minLng) || !Number.isFinite(maxLat) || !Number.isFinite(maxLng)) return null;
  return { minLat, minLng, maxLat, maxLng };
}

function pointInRing(lng, lat, ring = []) {
  let inside = false;
  for (let i = 0, j = ring.length - 1; i < ring.length; j = i++) {
    const xi = ring[i][0], yi = ring[i][1];
    const xj = ring[j][0], yj = ring[j][1];
    const intersect = ((yi > lat) !== (yj > lat))
      && (lng < (xj - xi) * (lat - yi) / ((yj - yi) || 1e-12) + xi);
    if (intersect) inside = !inside;
  }
  return inside;
}

function pointInGeoJson(lng, lat, geo) {
  if (!geo || !geo.type) return false;
  if (geo.type === 'Polygon') {
    const rings = geo.coordinates || [];
    if (!rings.length) return false;
    if (!pointInRing(lng, lat, rings[0])) return false;
    for (let i = 1; i < rings.length; i++) if (pointInRing(lng, lat, rings[i])) return false;
    return true;
  }
  if (geo.type === 'MultiPolygon') {
    const polys = geo.coordinates || [];
    for (const poly of polys) {
      if (!poly.length) continue;
      if (!pointInRing(lng, lat, poly[0])) continue;
      let inHole = false;
      for (let i = 1; i < poly.length; i++) if (pointInRing(lng, lat, poly[i])) { inHole = true; break; }
      if (!inHole) return true;
    }
    return false;
  }
  return false;
}

function mosqueInSelectedDistrict(m) {
  if (!districtState.selectedGeo) return true;
  const b = districtState.selectedBBox;
  if (b) {
    if (m.lat < b.minLat || m.lat > b.maxLat || m.lng < b.minLng || m.lng > b.maxLng) return false;
  }
  return pointInGeoJson(m.lng, m.lat, districtState.selectedGeo);
}

function getVisibleMosques(pad = 0.1) {
  if (!map) return [];
  const bounds = map.getBounds().pad(pad);
  let vis = [...mosqueDB.values()].filter(m => bounds.contains([m.lat, m.lng]));
  if (districtState.selectedGeo) vis = vis.filter(mosqueInSelectedDistrict);
  return vis;
}

function clearDistrictSelection(silent = false) {
  if (districtState.layer && map) {
    try { map.removeLayer(districtState.layer); } catch {}
  }
  districtState.layer = null;
  districtState.selectedName = '';
  districtState.selectedGeo = null;
  districtState.selectedBBox = null;
  updateDistrictUi();
  if (!silent) toast('İlçe filtresi temizlendi', 2200);
}

function setDistrictSelection(name, geo) {
  clearDistrictSelection(true);
  districtState.selectedName = name || '';
  districtState.selectedGeo = geo || null;
  districtState.selectedBBox = computeGeoBBox(geo);
  if (map && geo) {
    districtState.layer = L.geoJSON(geo, {
      style: {
        color: '#60a5fa',
        weight: 2,
        fillColor: '#60a5fa',
        fillOpacity: 0.08,
        dashArray: '6 4'
      }
    }).addTo(map);
    try { districtState.layer.bringToBack(); } catch {}
  }
  updateDistrictUi();
}

const TILES = {
  dark:      { url:'https://{s}.basemaps.cartocdn.com/dark_all/{z}/{x}/{y}{r}.png',         opts:{ attribution:'©OSM ©CartoDB', subdomains:'abcd', maxZoom:19 } },
  satellite: { url:'https://server.arcgisonline.com/ArcGIS/rest/services/World_Imagery/MapServer/tile/{z}/{y}/{x}', opts:{ attribution:'©Esri ©OSM', maxZoom:19 } },
  osm:       { url:'https://{s}.tile.openstreetmap.org/{z}/{x}/{y}.png',                   opts:{ attribution:'©OSM', subdomains:'abc', maxZoom:19 } }
};
let currentLayer = 'dark';

// ══════════════════════════════════════════════════════════════
//  BOOTSTRAP
// ══════════════════════════════════════════════════════════════
function loadScript(src) {
  return new Promise((res,rej) => {
    const s = document.createElement('script');
    s.src = src;
    s.async = true;
    const timer = setTimeout(() => {
      try { s.remove(); } catch {}
      rej(new Error('timeout ' + src));
    }, 9000);
    s.onload = () => { clearTimeout(timer); res(); };
    s.onerror = () => { clearTimeout(timer); rej(new Error('load failed ' + src)); };
    document.head.appendChild(s);
  });
}

async function initGeoCacheDb() {
  if (geoCacheReady || !window.indexedDB) return;
  await new Promise((resolve) => {
    try {
      const req = indexedDB.open(GEO_CACHE_DB, 1);
      req.onupgradeneeded = () => {
        const db = req.result;
        if (!db.objectStoreNames.contains(GEO_CACHE_STORE)) {
          db.createObjectStore(GEO_CACHE_STORE, { keyPath:'k' });
        }
      };
      req.onsuccess = () => {
        geoCacheDb = req.result;
        geoCacheReady = true;
        resolve();
      };
      req.onerror = () => resolve();
    } catch {
      resolve();
    }
  });
}

async function geoCacheGet(cellKey, mode = 'full') {
  if (!cellKey) return null;
  await initGeoCacheDb();
  if (!geoCacheDb) return null;
  const cacheKey = `${cellKey}:${mode}`;
  return new Promise((resolve) => {
    try {
      const tx = geoCacheDb.transaction(GEO_CACHE_STORE, 'readonly');
      const st = tx.objectStore(GEO_CACHE_STORE);
      const req = st.get(cacheKey);
      req.onsuccess = () => {
        const row = req.result;
        if (!row || !Array.isArray(row.elements)) return resolve(null);
        if (!Number.isFinite(row.ts) || (Date.now() - row.ts) > GEO_CACHE_TTL_MS) return resolve(null);
        resolve(row.elements);
      };
      req.onerror = () => resolve(null);
    } catch {
      resolve(null);
    }
  });
}

async function geoCacheSet(cellKey, elements, mode = 'full') {
  if (!cellKey || !Array.isArray(elements)) return;
  await initGeoCacheDb();
  if (!geoCacheDb) return;
  const cacheKey = `${cellKey}:${mode}`;
  try {
    const tx = geoCacheDb.transaction(GEO_CACHE_STORE, 'readwrite');
    tx.objectStore(GEO_CACHE_STORE).put({ k:cacheKey, ts:Date.now(), elements });
  } catch {}
}

async function bootstrap() {
  initGeoCacheDb();
  loadNameEnrichCache();
  loadPopularityCache();
  loadVisitTrafficCache();
  loadCitySearchHistory();
  loadInteriorDB();
  loadManualAxisDB();
  loadSnapshots();
  const langSaved = safeStorageGet(LANG_KEY, 'tr') || 'tr';
  const themeSaved = safeStorageGet(THEME_KEY, 'dark') || 'dark';
  const outdoorSaved = safeStorageGet(OUTDOOR_KEY, '0');
  applyThemeMode(themeSaved, false);
  if (String(outdoorSaved) === '1') {
    uiState.outdoor = true;
    document.body.classList.add('outdoor-mode');
  }
  document.getElementById('btn-outdoor')?.classList.toggle('active', uiState.outdoor);
  document.getElementById('mob-btn-outdoor')?.classList.toggle('active', uiState.outdoor);
  setLang(langSaved, true);
  setOv(true,'Harita yükleniyor...','Leaflet.js başlatılıyor');
  if (!window.L || !window.L.map) {
    setOv(false);
    toast(' Harita kütüphanesi bulunamadı (lokal dosya eksik)', 9000);
    return;
  }
  try {
    initMap();
  } catch (e) {
    setOv(false);
    toast(' Başlatma hatası: ' + (e?.message || 'bilinmeyen'), 9000);
    console.error(e);
  }
}

function initMap() {
  map = L.map('map', { center:[41.015,28.979], zoom:13, zoomControl:false });
  tileLayer = L.tileLayer(TILES.dark.url, TILES.dark.opts).addTo(map);
  L.control.zoom({ position:'bottomleft' }).addTo(map);

  // Kaaba marker (permanent)
  L.circleMarker([KAABA.lat,KAABA.lng],{ radius:9,fillColor:'#c9a84c',color:'#e8c97a',weight:2,fillOpacity:1 })
    .addTo(map).bindPopup('<div style="font-family:monospace;color:#c9a84c;font-weight:700"> Kâbe<br><small style="color:#888">21.4225°N 39.8262°E</small></div>');

  // ── VIEWPORT EVENTS — debounced auto-load
  map.on('moveend zoomend', () => {
    // Zoom < 11 → too wide, skip auto-load
    if (map.getZoom() < 11) { setVpStatus('idle'); hideSearchAreaButton(); return; }
    // Repaint immediately for already-cached data in current view.
    if (mosqueDB.size) renderAll();
    maybeArmSearchAreaButton();
    scheduleViewportLoad(420);
  });
  map.on('moveend zoomend', updateHashFromMap);
  map.on('dragstart', () => {
    if (followState.enabled) {
      stopFollowLock(true);
      toast('Takip kilidi manuel kaydırma ile kapatıldı', 2200);
    }
  });

  // Wire buttons
  document.getElementById('search-btn').onclick = doSearch;
  document.getElementById('loc-btn').onclick    = useMyLocation;
  document.getElementById('btn-district').onclick = toggleDistrictMode;
  document.getElementById('district-pill-clear').onclick = () => {
    clearDistrictSelection();
    renderAll();
  };
  document.getElementById('city-input').onkeydown = e => {
    if (e.key !== 'Enter') return;
    e.preventDefault();
    const dd = document.getElementById('city-smart-dd');
    const q = document.getElementById('city-input').value.trim();
    if (isLikelyMosqueQuery(q)) {
      cityDropdownIdx = -1;
      closeCitySmartDropdown();
      doSearch();
      return;
    }
    if (dd?.classList.contains('show') && cityDropdownIdx >= 0) return;
    if (dd?.classList.contains('show')) return;
    doSearch();
  };
  document.getElementById('tol').oninput = e => { tol=+e.target.value; document.getElementById('tol-val').textContent=tol+'°'; recompute(); };
  const mq = document.getElementById('mob-quick-city');
  if (mq) mq.value = document.getElementById('city-input').value || '';

  // Init mosque search
  initMosqueSearch();
  initTopSmartSearch();
  initSidebarPullToRefresh();
  initSidebarSnapSheet();

  // Close qibla panel on map click (not on marker)
  map.on('click', hideQiblaPanel);
  map.on('mousemove', onDistrictMouseMove);
  map.on('click', onDistrictMapClick);
  map.on('click', onMapReverseLookupClick);
  map.on('mouseout', () => {
    if (!districtState.enabled) return;
    districtState.hoverName = '';
    updateDistrictUi();
  });

  // Always start from clean home state on refresh/load (no hash restore, empty search).
  _hashUpdating = true;
  history.replaceState(null, '', location.pathname);
  _hashUpdating = false;
  currentCity = '';
  document.getElementById('city-input').value = '';
  if (mq) mq.value = '';
  updateDistrictUi();
  setOv(false);
  searchAreaAnchor = map.getCenter();
  hideSearchAreaButton();
  if (map.getZoom() >= 11) {
    scheduleViewportLoad(260);
  }
  startViewportWatchdog();
}

async function autoLocateOnStartup() {
  if (!navigator.geolocation) return false;
  const pref = safeStorageGet(GEO_PROMPT_KEY, '');
  if (pref === 'denied') return false;
  try {
    if (!navigator.permissions?.query) {
      const ok = await useMyLocation({ showToast:false, source:'auto' });
      safeStorageSet(GEO_PROMPT_KEY, ok ? 'granted' : 'denied');
      return ok;
    }
    const perm = await navigator.permissions.query({ name:'geolocation' });
    if (perm.state === 'granted') {
      const ok = await useMyLocation({ showToast:false, source:'auto' });
      safeStorageSet(GEO_PROMPT_KEY, ok ? 'granted' : 'denied');
      return ok;
    }
    if (perm.state === 'prompt') {
      const ok = await useMyLocation({ showToast:false, source:'auto' });
      safeStorageSet(GEO_PROMPT_KEY, ok ? 'granted' : 'denied');
      return ok;
    }
    safeStorageSet(GEO_PROMPT_KEY, 'denied');
    return false;
  } catch {
    return false;
  }
}

function toggleDistrictMode() {
  districtState.enabled = !districtState.enabled;
  districtState.hoverName = '';
  updateDistrictUi();
  toast(districtState.enabled ? 'İlçe modu aktif: harita üzerinde gezdirip tıklayın' : 'İlçe modu kapatıldı', 2200);
}

async function onDistrictMouseMove(e) {
  if (!districtState.enabled || !e?.latlng) return;
  const now = Date.now();
  if (districtState.reverseBusy || (now - districtState.lastReverseAt) < 1200) return;
  districtState.lastReverseAt = now;
  districtState.reverseBusy = true;
  const seq = ++districtState.reverseSeq;
  try {
    const { lat, lng } = e.latlng;
    const url = `https://nominatim.openstreetmap.org/reverse?lat=${lat}&lon=${lng}&format=jsonv2&zoom=12&addressdetails=1`;
    const d = await nominatimFetchJson(url, {'Accept-Language':'tr,en'});
    if (seq !== districtState.reverseSeq) return;
    const addr = d?.address || {};
    districtState.hoverName = districtNameFromAddress(addr);
    districtState.hoverContextCity = districtContextCity(addr);
    districtState.hoverContextCountry = (addr.country || '').trim();
    updateDistrictUi();
  } catch {}
  districtState.reverseBusy = false;
}

function pickDistrictPolygonResult(items = [], districtName = '', contextCity = '') {
  if (!items.length) return null;
  const dn = normalize(trLower(districtName || ''));
  const cn = normalize(trLower(contextCity || ''));
  const ranked = items.map(it => {
    const addr = it.address || {};
    const cls = trLower(it.class || '');
    const type = trLower(it.type || '');
    const disp = normalize(trLower(it.display_name || ''));
    const addrDistrict = normalize(trLower(districtNameFromAddress(addr) || ''));
    const addrCity = normalize(trLower(districtContextCity(addr) || ''));
    let s = Number(it.importance || 0) * 40;
    if (cls === 'boundary') s += 55;
    if (type === 'administrative') s += 35;
    if (addrDistrict && addrDistrict === dn) s += 120;
    if (dn && disp.includes(dn)) s += 30;
    if (cn && addrCity === cn) s += 35;
    if (cn && disp.includes(cn)) s += 20;
    if (!it.geojson) s -= 1000;
    return { it, s };
  }).sort((a,b) => b.s - a.s);
  return ranked[0]?.it || null;
}

async function fetchDistrictPolygonByName(name, contextCity = '', contextCountry = '') {
  const key = districtCacheKey(name, contextCity, contextCountry);
  if (districtBoundaryCache.has(key)) return districtBoundaryCache.get(key);
  const q = [name, contextCity, contextCountry].filter(Boolean).join(', ');
  const url = `https://nominatim.openstreetmap.org/search?format=jsonv2&limit=8&polygon_geojson=1&addressdetails=1&q=${encodeURIComponent(q)}`;
  const rows = await nominatimFetchJson(url, {'Accept-Language':'tr,en'});
  const best = pickDistrictPolygonResult(rows || [], name, contextCity);
  const geo = best?.geojson || null;
  districtBoundaryCache.set(key, geo);
  return geo;
}

async function onDistrictMapClick(e) {
  if (!districtState.enabled || !e?.latlng) return;
  const t = e?.originalEvent?.target;
  if (t && t.classList && t.classList.contains('leaflet-interactive')) return;
  if (!districtState.hoverName) {
    toast('Bu noktada ilçe algılanamadı, biraz hareket ettirip tekrar deneyin', 2400);
    return;
  }
  const name = districtState.hoverName;
  const city = districtState.hoverContextCity;
  const country = districtState.hoverContextCountry;
  showMini(`İlçe sınırı yükleniyor: ${name}`);
  try {
    const geo = await fetchDistrictPolygonByName(name, city, country);
    if (!geo) throw new Error('İlçe sınırı bulunamadı');
    setDistrictSelection(name, geo);
    renderAll();
    toast(`İlçe seçildi: ${name}`, 2400);
  } catch (err) {
    toast(`İlçe seçilemedi: ${err?.message || 'bilinmeyen hata'}`, 3200);
  }
  hideMini();
}

function switchLayer(type) {
  if (!map||type===currentLayer) return;
  currentLayer=type;
  if(tileLayer) map.removeLayer(tileLayer);
  tileLayer = L.tileLayer(TILES[type].url,TILES[type].opts).addTo(map);
  tileLayer.bringToBack();
  setLayerButtonActive(type);
}

function setLayerButtonActive(type) {
  const normalized = type === 'satellite' ? 'sat' : type;
  const ids = ['btn-'+normalized, 'mob-btn-'+normalized, 'mob-fab-'+normalized];
  ['dark','sat','osm'].forEach(key => {
    const targets = ['btn-'+key, 'mob-btn-'+key, 'mob-fab-'+key];
    targets.forEach(id => document.getElementById(id)?.classList.remove('active'));
  });
  ids.forEach(id => document.getElementById(id)?.classList.add('active'));
}

function isMosqueLikeNominatimResult(d = {}) {
  const cls = trLower(d.class || '');
  const typ = trLower(d.type || '');
  const addresstype = trLower(d.addresstype || '');
  const cat = trLower(d.category || '');
  const nameTxt = trLower([
    d.name || '',
    d.display_name || '',
    d.namedetails?.name || '',
    d.namedetails?.['name:tr'] || '',
    d.namedetails?.['name:en'] || '',
    d.namedetails?.['name:ar'] || ''
  ].join(' '));
  if (typ === 'mosque' || addresstype === 'mosque') return true;
  if (cls === 'amenity' && (typ === 'place_of_worship' || typ === 'mosque')) return true;
  if (cat === 'amenity' && (typ === 'place_of_worship' || typ === 'mosque')) return true;
  return /\b(cami|camii|mescit|mescid|mosque|masjid|džamija|dzamija)\b/.test(nameTxt);
}

function findNearestLoadedMosque(lat, lng, maxMeters = 220) {
  if (!mosqueDB.size || !Number.isFinite(lat) || !Number.isFinite(lng)) return null;
  let best = null;
  let bestDist = Infinity;
  for (const m of mosqueDB.values()) {
    const d = greatCircleM(lat, lng, m.lat, m.lng);
    if (d < bestDist) { bestDist = d; best = m; }
  }
  return best && bestDist <= maxMeters ? best : null;
}

async function onMapReverseLookupClick(e) {
  if (!map || !e?.latlng) return;
  if (districtState.enabled || manualCapture.active) return;
  const t = e?.originalEvent?.target;
  if (t && t.classList && t.classList.contains('leaflet-interactive')) return;
  const now = Date.now();
  if (reverseTapState.busy || (now - reverseTapState.lastAt) < 550) return;

  reverseTapState.busy = true;
  reverseTapState.lastAt = now;
  const seq = ++reverseTapState.seq;
  const lat = e.latlng.lat;
  const lng = e.latlng.lng;
  showMini('Nokta analizi yapılıyor...');

  try {
    const revUrl = `https://nominatim.openstreetmap.org/reverse?lat=${lat}&lon=${lng}&format=jsonv2&zoom=18&addressdetails=1&namedetails=1`;
    const rev = await nominatimFetchJson(revUrl, { 'Accept-Language':'tr,en,ar' });
    if (seq !== reverseTapState.seq) return;

    if (!isMosqueLikeNominatimResult(rev || {})) {
      const nearKnown = findNearestLoadedMosque(lat, lng, 250);
      if (nearKnown) {
        focusMapLatLng(nearKnown.lat, nearKnown.lng, Math.max(map.getZoom() || 15, 16), { duration:0.55 });
        setTimeout(() => handleMosqueClick(nearKnown), 120);
        toast('Bu noktada cami etiketi yok, en yakın cami açıldı', 2200);
      } else {
        toast('Bu noktada cami kaydı bulunamadı', 2200);
      }
      return;
    }

    const osmType = normalizeOsmType(rev?.osm_type || '');
    const osmId = String(rev?.osm_id || '').replace(/\D/g, '');
    let target = null;

    if (osmType && osmId) {
      target = findMosqueByRef(osmType, osmId);
      if (!target) {
        const items = await fetchByOsmId(osmType, osmId);
        if (seq !== reverseTapState.seq) return;
        if (Array.isArray(items) && items.length) {
          processElements(items);
          renderAll();
          target = findMosqueByRef(osmType, osmId);
        }
      }
    }

    if (!target) target = findNearestLoadedMosque(lat, lng, 220);

    if (!target) {
      const fallback = await fetchCityFallback(lat, lng);
      if (seq !== reverseTapState.seq) return;
      if (Array.isArray(fallback) && fallback.length) {
        processElements(fallback);
        renderAll();
        target = findNearestLoadedMosque(lat, lng, 260);
      }
    }

    if (target) {
      focusMapLatLng(target.lat, target.lng, Math.max(map.getZoom() || 15, 16), { duration:0.62 });
      setTimeout(() => handleMosqueClick(target), 140);
      toast('Harita tıklaması: cami analizi açıldı', 1800);
    } else {
      toast('Cami tespit edildi fakat detay verisi alınamadı', 2600);
    }
  } catch {
    toast('Nokta analizi alınamadı', 2400);
  } finally {
    hideMini();
    reverseTapState.busy = false;
  }
}

// ══════════════════════════════════════════════════════════════
//  TILE CACHE SYSTEM
// ══════════════════════════════════════════════════════════════
// Divide world into 0.08° grid cells. Track which cells are loaded.
const GRID = 0.08;

function boundsToGridCells(bounds) {
  const cells = [];
  const s = Math.floor(bounds.getSouth()/GRID)*GRID;
  const n = Math.ceil(bounds.getNorth()/GRID)*GRID;
  const w = Math.floor(bounds.getWest()/GRID)*GRID;
  const e = Math.ceil(bounds.getEast()/GRID)*GRID;
  for (let la=s; la<n; la+=GRID)
    for (let ln=w; ln<e; ln+=GRID)
      cells.push({ key:`${la.toFixed(3)}_${ln.toFixed(3)}`, lat:la+GRID/2, lng:ln+GRID/2 });
  return cells;
}

function getUncachedCells(bounds) {
  return boundsToGridCells(bounds).filter(c => !tileCache.has(c.key));
}

function hideSearchAreaButton() {
  const btn = document.getElementById('search-area-btn');
  if (!btn) return;
  btn.classList.remove('show');
  btn.classList.remove('loading');
  btn.classList.remove('armed');
  btn.disabled = false;
  btn.textContent = 'Bu alanı tara';
  searchAreaArmed = false;
}

function maybeArmSearchAreaButton() {
  const btn = document.getElementById('search-area-btn');
  if (!btn || !map || map.getZoom() < 11) return;
  const c = map.getCenter();
  if (!searchAreaAnchor) return;
  const km = greatCircleKm(c.lat, c.lng, searchAreaAnchor.lat, searchAreaAnchor.lng);
  if (!Number.isFinite(km)) return;
  const z = map.getZoom();
  const thresholdKm = z >= 15 ? 0.15 : z >= 13 ? 0.3 : 0.5;
  if (km >= thresholdKm) {
    btn.classList.add('show');
    btn.classList.add('armed');
    searchAreaArmed = true;
  }
}

async function refreshSearchArea() {
  if (!map) return;
  const btn = document.getElementById('search-area-btn');
  if (btn) {
    btn.classList.add('show', 'loading');
    btn.disabled = true;
    btn.textContent = 'Taranıyor...';
  }
  const bounds = map.getBounds();
  const cells = boundsToGridCells(bounds);
  for (const c of cells) {
    tileCache.delete(c.key);
  }
  updateCacheUI();
  searchAreaAnchor = map.getCenter();
  try {
    await loadViewport();
    toast('Bu alan güncellendi', 1400);
  } catch {}
  hideSearchAreaButton();
}

function scheduleViewportLoad(delayMs = 420, opts = {}) {
  clearTimeout(vpDebounceTimer);
  if (!map || map.getZoom() < 11) {
    setVpStatus('idle');
    return;
  }
  vpDebounceTimer = setTimeout(() => {
    if (!map || map.getZoom() < 11) {
      setVpStatus('idle');
      return;
    }
    loadViewport(opts);
  }, Math.max(0, delayMs | 0));
}

function startViewportWatchdog() {
  clearInterval(vpWatchdogTimer);
  vpWatchdogTimer = setInterval(() => {
    if (!map || document.hidden || isVpLoading || map.getZoom() < 11) return;
    const uncached = getUncachedCells(map.getBounds());
    if (uncached.length) scheduleViewportLoad(120);
  }, 2500);
}

// ══════════════════════════════════════════════════════════════
//  VIEWPORT AUTO-LOAD
// ══════════════════════════════════════════════════════════════
async function loadViewport(opts = {}) {
  const signal = opts.signal;
  throwIfAborted(signal);
  if (isVpLoading) {
    vpNeedsReload = true;
    return;
  }
  if (map.getZoom() < 11) {
    setVpStatus('idle');
    return;
  }
  const bounds = map.getBounds();
  const center = bounds.getCenter();
  const newCells = getUncachedCells(bounds).sort((a, b) => {
    const da = Math.pow(a.lat - center.lat, 2) + Math.pow(a.lng - center.lng, 2);
    const db = Math.pow(b.lat - center.lat, 2) + Math.pow(b.lng - center.lng, 2);
    return da - db;
  });
  if (!newCells.length) {
    // No new fetch needed, but viewport may have changed.
    if (mosqueDB.size) renderAll();
    setVpStatus('done');
    return;
  }

  isVpLoading = true;
  setVpStatus('loading');
  const batchSize = Number.isFinite(opts.batchSize) ? Math.max(1, opts.batchSize | 0) : 10;
  const concurrency = Number.isFinite(opts.concurrency) ? Math.max(1, opts.concurrency | 0) : 2;
  const batch = newCells.slice(0, batchSize);
  showMini(`${batch.length}/${newCells.length} alan yükleniyor...`);
  showSkeletonList();

  try {
    // Fetch per-grid-cell so moving around always loads local area deterministically.
    let cursor = 0;
    const workers = Array.from({ length: Math.min(concurrency, batch.length) }, async () => {
      while (cursor < batch.length) {
        throwIfAborted(signal);
        const c = batch[cursor++];
        const half = GRID / 2;
        const pad = GRID * 0.05;
        const s = c.lat - half - pad;
        const n = c.lat + half + pad;
        const w = c.lng - half - pad;
        const e = c.lng + half + pad;
        try {
          const zoom = map?.getZoom?.() || 13;
          // Restore full geometry from zoom 12+ so axis arrows remain visible.
          const queryMode = zoom <= 11 ? 'lite' : 'full';
          let elements = await geoCacheGet(c.key, queryMode);
          if (!elements) {
            const fetchPolicy = {
              ...(opts.fetchPolicy || { retries:1, timeoutMs:22000, backoffMs:700, minInterval:340 }),
              signal,
              queryMode
            };
            elements = await fetchBbox(s, w, n, e, fetchPolicy);
            geoCacheSet(c.key, elements, queryMode);
          }
          processElements(elements);
          tileCache.add(c.key);
        } catch (err) {
          if (err?.name === 'AbortError') throw err;
          // Keep cell uncached so it can retry on next viewport load.
          console.warn('cell fetch failed', c.key, err?.message || err);
        }
      }
    });
    await Promise.all(workers);
    throwIfAborted(signal);
    updateCacheUI();
    renderAll();
    setVpStatus('done');
    if (newCells.length > batch.length) {
      clearTimeout(vpDebounceTimer);
      vpDebounceTimer = setTimeout(loadViewport, 120);
    }
  } catch(err) {
    setVpStatus('idle');
    if (err?.name !== 'AbortError') {
      toast('Veri yüklenirken hata: '+err.message, 5000);
      console.error(err);
    }
  }

  hideMini();
  isVpLoading = false;
  if (vpNeedsReload) {
    vpNeedsReload = false;
    clearTimeout(vpDebounceTimer);
    vpDebounceTimer = setTimeout(loadViewport, 120);
  }
}

function showSkeletonList() {
  const el = document.getElementById('mosque-list');
  el.innerHTML = Array(6).fill(0).map((_,i) => `
    <div class="sk-item" style="animation-delay:${i*60}ms">
      <div class="sk-dot"></div>
      <div class="sk-line sk-name" style="width:${55+Math.random()*30|0}%"></div>
      <div class="sk-line sk-diff"></div>
    </div>`).join('');
}

// ══════════════════════════════════════════════════════════════
//  OSM API
// ══════════════════════════════════════════════════════════════
const OVERPASS_ENDPOINTS = [
  'https://overpass-api.de/api/interpreter',
  'https://overpass.kumi.systems/api/interpreter',
  'https://lz4.overpass-api.de/api/interpreter'
];

function buildMosqueQuery(s,w,n,e, mode = 'full') {
  const outLine = mode === 'lite'
    ? 'out center tags qt 3000;'
    : 'out body geom qt 3000;';
  return `[out:json][timeout:60];
(
  way["amenity"="place_of_worship"]["religion"~"muslim|islam",i](${s},${w},${n},${e});
  node["amenity"="place_of_worship"]["religion"~"muslim|islam",i](${s},${w},${n},${e});
  relation["amenity"="place_of_worship"]["religion"~"muslim|islam",i](${s},${w},${n},${e});
  way["amenity"="place_of_worship"]["denomination"~"sunni|shia|ibadi",i](${s},${w},${n},${e});
  node["amenity"="place_of_worship"]["denomination"~"sunni|shia|ibadi",i](${s},${w},${n},${e});
  relation["amenity"="place_of_worship"]["denomination"~"sunni|shia|ibadi",i](${s},${w},${n},${e});
  way["amenity"="mosque"](${s},${w},${n},${e});
  node["amenity"="mosque"](${s},${w},${n},${e});
  relation["amenity"="mosque"](${s},${w},${n},${e});
  way["building"="mosque"](${s},${w},${n},${e});
  node["building"="mosque"](${s},${w},${n},${e});
  relation["building"="mosque"](${s},${w},${n},${e});
  way["place_of_worship"="mosque"](${s},${w},${n},${e});
  node["place_of_worship"="mosque"](${s},${w},${n},${e});
  relation["place_of_worship"="mosque"](${s},${w},${n},${e});
  way["mosque"](${s},${w},${n},${e});
  node["mosque"](${s},${w},${n},${e});
  relation["mosque"](${s},${w},${n},${e});
);
${outLine}`;
}

async function fetchOverpassQuery(query, policy = {}) {
  throwIfAborted(policy.signal);
  let lastErr = null;
  for (const endpoint of OVERPASS_ENDPOINTS) {
    try {
      throwIfAborted(policy.signal);
      const r = await limitedFetch(endpoint, {
        method:'POST',
        headers:{'Content-Type':'application/x-www-form-urlencoded'},
        body:'data='+encodeURIComponent(query)
      }, {
        hostKey:'overpass',
        minInterval: Number.isFinite(policy.minInterval) ? policy.minInterval : 500,
        retries: Number.isFinite(policy.retries) ? policy.retries : 2,
        timeoutMs: Number.isFinite(policy.timeoutMs) ? policy.timeoutMs : 46000,
        backoffMs: Number.isFinite(policy.backoffMs) ? policy.backoffMs : 900,
        signal: policy.signal
      });
      if(!r.ok) throw new Error(`HTTP ${r.status} @ ${endpoint}`);
      const d = await r.json();
      return d.elements || [];
    } catch (e) {
      if (e?.name === 'AbortError') throw e;
      lastErr = e;
    }
  }
  throw new Error(lastErr?.message || 'Overpass yanıt vermedi');
}

async function fetchBbox(s,w,n,e,policy={}) {
  const mode = policy.queryMode === 'lite' ? 'lite' : 'full';
  return fetchOverpassQuery(buildMosqueQuery(s,w,n,e, mode), policy);
}

function pickBestGeocodeResult(items, name) {
  if (!items?.length) return null;
  const q = trLower(name || '').trim();
  const mosqueMode = isLikelyMosqueQuery(name);
  const ranked = items.map(it => {
    const disp = trLower(it.display_name || '');
    const type = trLower(it.type || '');
    const cls  = trLower(it.class || '');
    let score = Number(it.importance || 0) * 100;
    if (disp.startsWith(q + ',')) score += 80;
    if (disp.includes(',' + q + ',')) score += 35;
    if (disp.includes(q)) score += 18;
    if (['city','town','village','municipality','county','state','province'].includes(type)) score += mosqueMode ? 4 : 22;
    if (cls === 'place' || cls === 'boundary') score += 12;
    if (mosqueMode) {
      if (cls === 'amenity' && (type === 'place_of_worship' || type === 'mosque')) score += 60;
      if (disp.includes('cami') || disp.includes('mosque') || disp.includes('mescid') || disp.includes('mescit') || disp.includes('masjid')) score += 30;
    }
    return { it, score };
  }).sort((a,b) => b.score - a.score);
  return ranked[0]?.it || items[0];
}

async function geocode(name, opts = {}) {
  const signal = opts.signal;
  throwIfAborted(signal);
  const url = `https://nominatim.openstreetmap.org/search?q=${encodeURIComponent(name)}&format=json&limit=8&addressdetails=1`;
  const headerVariants = [
    {'Accept-Language':'tr,en','User-Agent':'QiblaChecker/1.0'},
    {'Accept-Language':'en','User-Agent':'QiblaChecker/1.0'},
    {'User-Agent':'QiblaChecker/1.0'}
  ];

  let lastErr = null;
  for (const headers of headerVariants) {
    try {
      throwIfAborted(signal);
      const d = await nominatimFetchJson(url, headers, { signal });
      const best = pickBestGeocodeResult(d, name);
      if (!best) continue;
      return {
        lat:+best.lat,
        lng:+best.lon,
        bbox: Array.isArray(best.boundingbox) ? best.boundingbox.map(Number) : null,
        osmClass: best.class || '',
        osmType: best.type || '',
        displayName: best.display_name || ''
      };
    } catch (e) {
      if (e?.name === 'AbortError') throw e;
      lastErr = e;
    }
  }
  throw new Error('Şehir bulunamadı: ' + name + (lastErr ? ` (${lastErr.message})` : ''));
}

async function fetchCityFallback(lat, lng, opts = {}) {
  const signal = opts.signal;
  throwIfAborted(signal);
  // Kademeli arama: küçük şehir merkezinden başlayıp daha geniş kutuya çıkar.
  const radii = [0.06, 0.12, 0.22, 0.35]; // ~6km, 13km, 24km, 39km (enleme göre değişir)
  const unique = new Map();

  for (const r of radii) {
    throwIfAborted(signal);
    const elements = await fetchBbox(lat-r, lng-r, lat+r, lng+r, { signal });
    for (const el of elements) {
      unique.set(`${el.type}:${el.id}`, el);
    }
    if (unique.size >= 40) break;
  }
  return [...unique.values()];
}

function parseDirectMosqueQuery(q) {
  const t = (q || '').trim();
  const osm = t.match(/^(node|way|relation)\s*[:#]?\s*(\d+)$/i);
  if (osm) return { type:'osm', osmType:osm[1].toLowerCase(), id:osm[2] };
  const qid = t.match(/^Q\d+$/i);
  if (qid) return { type:'wikidata', qid:qid[0].toUpperCase() };
  return null;
}

async function fetchByOsmId(osmType, id, opts = {}) {
  const q = `[out:json][timeout:35];${osmType}(${id});out body geom tags center;`;
  return fetchOverpassQuery(q, { signal: opts.signal });
}

const detailHydrationInFlight = new Set();
async function hydrateMosqueDetailOnDemand(m) {
  if (!m || !m.id || !m.osmType) return;
  if (m.polyCoords && m.polyCoords.length >= 4) return;
  const key = `${m.osmType}:${m.id}`;
  if (detailHydrationInFlight.has(key)) return;
  detailHydrationInFlight.add(key);
  try {
    const items = await fetchByOsmId(m.osmType, m.id);
    if (!Array.isArray(items) || !items.length) return;
    const before = mosqueDB.get(m.id);
    processElements(items);
    const after = mosqueDB.get(m.id);
    if (!after || !before) return;
    const gotGeometry = !!(after.polyCoords && after.polyCoords.length >= 4);
    if (!gotGeometry) return;
    renderAll();
    if (window._lastClickedMosque && String(window._lastClickedMosque.id) === String(after.id)) {
      window._lastClickedMosque = after;
      populateDetailPanel(after);
    }
  } catch {}
  finally {
    detailHydrationInFlight.delete(key);
  }
}

async function fetchByWikidataQid(qid, opts = {}) {
  const q = `[out:json][timeout:40];
(
  node["wikidata"="${qid}"];
  way["wikidata"="${qid}"];
  relation["wikidata"="${qid}"];
);out body geom tags center;`;
  return fetchOverpassQuery(q, { signal: opts.signal });
}

// ══════════════════════════════════════════════════════════════
//  DATA PROCESSING
// ══════════════════════════════════════════════════════════════
function processElements(elements) {
  let added = 0;
  for (const el of elements) {

    let lat0,lng0,polyCoords=null;
    if (el.type==='node') { lat0=el.lat; lng0=el.lon; }
    else if (el.type==='way'&&el.geometry) {
      const pts=el.geometry;
      lat0=pts.reduce((s,p)=>s+p.lat,0)/pts.length;
      lng0=pts.reduce((s,p)=>s+p.lon,0)/pts.length;
      polyCoords=pts.map(p=>[p.lat,p.lon]);
    } else if (el.type==='way' && el.center) {
      lat0 = el.center.lat; lng0 = el.center.lon;
    } else if (el.type==='relation' && el.geometry && el.geometry.length) {
      const pts=el.geometry;
      lat0=pts.reduce((s,p)=>s+p.lat,0)/pts.length;
      lng0=pts.reduce((s,p)=>s+p.lon,0)/pts.length;
      polyCoords=pts.map(p=>[p.lat,p.lon]);
    } else if (el.type==='relation' && el.center) {
      lat0 = el.center.lat; lng0 = el.center.lon;
    } else continue;

    const qibla = qiblaAngle(lat0,lng0);
    let axis=null, method='none';

    const dt = el.tags?.direction||el.tags?.['building:direction']||el.tags?.['roof:direction'];
    if(dt&&!isNaN(+dt)) { axis=+dt%180; method='osm-tag'; }
    else if(polyCoords&&polyCoords.length>=4) {
      const res = buildingQiblaEdge(polyCoords,qibla);
      if(res){ axis=res.angle; method='edge-analysis'; }
    }

    const fallbackName = pickNameFromTags(el.tags) || buildTagsAddressFallbackName(el.tags || {}, el.id);
    const rec = {
      id:el.id,
      osmType: el.type,
      name:fallbackName,
      nameAr: el.tags?.['name:ar']||null,
      nameTr: el.tags?.['name:tr']||null,
      lat:lat0,lng:lng0,qibla,
      baseAxis: axis,
      baseMethod: method,
      axis:null,diff:null,status:'unknown',polyCoords,method,
      startDate: el.tags?.start_date||el.tags?.['building:start_date']||null,
      tags: el.tags||{},
      geomComplexity: computeGeometryComplexity(polyCoords)
    };
    const remoteMeta = msRemoteMetaByRef.get(`${el.type}:${el.id}`);
    if (remoteMeta) {
      rec.searchMeta = { ...remoteMeta };
    }
    buildSearchIndexForMosque(rec);
    applyAxisFusion(rec);
    const existing = mosqueDB.get(el.id);
    if (existing) {
      if (remoteMeta && !existing.searchMeta) existing.searchMeta = { ...remoteMeta };
      const recScore =
        (rec.axis != null ? 120 : 0) +
        (Array.isArray(rec.polyCoords) && rec.polyCoords.length >= 4 ? 30 : 0) +
        (rec.osmType === 'way' || rec.osmType === 'relation' ? 12 : 0) +
        (rec.baseMethod === 'edge-analysis' ? 8 : 0);
      const existingScore =
        (existing.axis != null ? 120 : 0) +
        (Array.isArray(existing.polyCoords) && existing.polyCoords.length >= 4 ? 30 : 0) +
        (existing.osmType === 'way' || existing.osmType === 'relation' ? 12 : 0) +
        (existing.baseMethod === 'edge-analysis' ? 8 : 0);
      if (recScore <= existingScore) continue;
    } else {
      added++;
    }
    mosqueDB.set(el.id, rec);
    if (rec && (isPlaceholderMosqueName(rec.name) || isGenericMosqueName(rec.name))) enqueueMosqueNameEnrichment(rec);
  }
  return added;
}

function findBestMosqueByName(query) {
  const q = (query || '').trim();
  if (!q || !mosqueDB.size) return null;
  const qLow  = trLower(q);
  const qNorm = normalize(qLow);
  const words = qLow.split(/\s+/).filter(Boolean);
  let best = null;
  let bestScore = -1;
  for (const m of mosqueDB.values()) {
    const s = msMosqueScore(m, qLow, qNorm, words);
    if (s > bestScore) { bestScore = s; best = m; }
  }
  return bestScore >= 30 ? best : null;
}

// ══════════════════════════════════════════════════════════════
//  RENDER (only visible mosques for performance)
// ══════════════════════════════════════════════════════════════
function renderAll() {
  // Remove old visual layers
  renderLayers.forEach(l=>{ try{map.removeLayer(l);}catch{} });
  renderLayers=[];
  if (markerClusterLayer) {
    try { map.removeLayer(markerClusterLayer); } catch {}
    markerClusterLayer = null;
  }

  const visible = getVisibleMosques(0.1);
  const denseMode = visible.length > 700;
  const canCluster = typeof L !== 'undefined' && typeof L.markerClusterGroup === 'function';
  const useCluster = canCluster && visible.length > 140 && map.getZoom() <= 15;
  const simplifiedMode = denseMode || useCluster;
  if (useCluster) {
    markerClusterLayer = L.markerClusterGroup({
      spiderfyOnMaxZoom:true,
      showCoverageOnHover:false,
      removeOutsideVisibleBounds:true,
      disableClusteringAtZoom:16,
      chunkedLoading:true,
      maxClusterRadius:52
    });
  }
  if (denseMode && !denseModeNotified) {
    toast('Performans modu: yoğun bölgede sade çizim kullanılıyor', 3200);
    denseModeNotified = true;
  } else if (!denseMode) {
    denseModeNotified = false;
  }

  for (const m of visible) {
    const col = m.status==='correct'?'#4ade80':m.status==='wrong'?'#f87171':'#fbbf24';
    const dispAxis = getDisplayAxis(m);

    if(!simplifiedMode && m.polyCoords){
      const poly=L.polygon(m.polyCoords,{color:col,weight:1.5,fillColor:col,fillOpacity:.07,opacity:.45}).addTo(map);
      poly.on('click',()=>handleMosqueClick(m));
      renderLayers.push(poly);
    }

    // Kıble direction line (dashed gold)
    if (!simplifiedMode) {
      const qEnd=destination(m.lat,m.lng,m.qibla,200);
      renderLayers.push(L.polyline([[m.lat,m.lng],[qEnd.lat,qEnd.lng]],{color:'#c9a84c',weight:1.5,opacity:.7,dashArray:'6 5'}).addTo(map));
    }

    // Building axis arrow
    if(!simplifiedMode && dispAxis!==null){
      const fd=closestDirection(dispAxis,m.qibla);
      const e1=destination(m.lat,m.lng,fd,90);
      const e2=destination(m.lat,m.lng,(fd+180)%360,90);
      const axl=L.polyline([[e2.lat,e2.lng],[e1.lat,e1.lng]],{color:col,weight:2.5,opacity:.9}).addTo(map);
      axl.on('click',()=>handleMosqueClick(m)); renderLayers.push(axl);
      const tip=destination(m.lat,m.lng,fd,95);
      const aL=destination(tip.lat,tip.lng,(fd+145)%360,17);
      const aR=destination(tip.lat,tip.lng,(fd+215)%360,17);
      renderLayers.push(L.polygon([[tip.lat,tip.lng],[aL.lat,aL.lng],[aR.lat,aR.lng]],{color:col,fillColor:col,weight:0,fillOpacity:.9}).addTo(map));
    }

    const mk=L.circleMarker([m.lat,m.lng],{radius:5,fillColor:col,color:'#164773',weight:1.5,fillOpacity:.95});
    mk.mosque = m;
    mk.bindPopup(makePopup(m));
    mk.on('click',()=>handleMosqueClick(m));
    if (useCluster && markerClusterLayer) markerClusterLayer.addLayer(mk);
    else mk.addTo(map);
    renderLayers.push(mk);
  }
  if (useCluster && markerClusterLayer) {
    markerClusterLayer.addTo(map);
    renderLayers.push(markerClusterLayer);
  }

  updateStats();
  // Respect active mosque filter when updating list
  if (mosqueFilter) {
    applyMosqueFilter(mosqueFilter);
  } else {
    updateList(visible);
  }
  // Refresh overlays if active
  if(heatVisible) refreshHeatmap();
  if(scoreCardVisible) updateScoreCard();
  // Refresh history mode colors & modal if active
  if(typeof historyModeActive !== 'undefined' && historyModeActive) {
    enrichWithPeriod();
    applyPeriodColors();
    renderHistoryModal();
  }
}

// ══════════════════════════════════════════════════════════════
//  KIBLE GREAT-CIRCLE ANIMATION
// ══════════════════════════════════════════════════════════════
// Animation state — single source of truth for cancellation
let _animHandle = null;   // rAF handle
let _animTimer  = null;   // setTimeout handle (phase transition)

function cancelAnimation() {
  if (_animHandle) { cancelAnimationFrame(_animHandle); _animHandle = null; }
  if (_animTimer)  { clearTimeout(_animTimer);          _animTimer  = null; }
}

function animateQibla(m) {
  // ── Cancel any running animation immediately
  cancelAnimation();
  animLayers.forEach(l=>{ try{map.removeLayer(l);}catch{} });
  animLayers = [];

  const dist   = Math.round(greatCircleKm(m.lat, m.lng, KAABA.lat, KAABA.lng));
  const hasAxis = m.axis !== null;

  // ── Info panel
  document.getElementById('qp-name').textContent       = m.name;
  document.getElementById('qp-angle').textContent      = m.qibla.toFixed(2)+'°  (gerçek kıble)';
  document.getElementById('qp-diff').textContent       = m.diff!==null ? m.diff.toFixed(1)+'° sapma' : '—';
  document.getElementById('qp-dist').textContent       = dist+' km uzakta';
  document.getElementById('qp-anim-status').textContent = '● Çiziliyor...';
  document.getElementById('qibla-panel').classList.add('show');

  // ── Pre-compute points
  const qiblaPts  = greatCirclePoints(m.lat, m.lng, KAABA.lat, KAABA.lng, 120);
  let   buildPts  = [];
  if (hasAxis) {
    const faceDir  = closestDirection(m.axis, m.qibla);
    // greatCircleKm ismine karşın metre döndürür (R=6371000)
    const kabeDistM = greatCircleM(m.lat, m.lng, KAABA.lat, KAABA.lng);
    // faceDir yönünde aynı mesafede hedef nokta → büyük daire çiz
    const buildTarget = destination(m.lat, m.lng, faceDir, kabeDistM);
    buildPts = greatCirclePoints(m.lat, m.lng, buildTarget.lat, buildTarget.lng, 120);
  }

  // ── Create Leaflet layers upfront
  const qibleLine = L.polyline([], { color:'#c9a84c', weight:2.5, opacity:.9, dashArray:'8 5' }).addTo(map);
  animLayers.push(qibleLine);

  let buildLine = null;
  if (hasAxis) {
    buildLine = L.polyline([], { color:'#7c6ad8', weight:3, opacity:.95 }).addTo(map);
    animLayers.push(buildLine);
  }

  const center = L.circleMarker([m.lat,m.lng],{
    radius:9, fillColor:'#ffffff', color:'#c9a84c', weight:2, fillOpacity:.9
  }).addTo(map);
  animLayers.push(center);

  // ── rAF-based sequential animator
  // animatePoints(pts, layer, speed, onDone)
  // speed = points per second
  function animatePoints(pts, layer, speed, onDone) {
    let idx      = 0;
    let lastTime = null;
    let accum    = 0;

    function frame(ts) {
      if (lastTime === null) lastTime = ts;
      const dt = ts - lastTime;
      lastTime = ts;
      accum += dt * speed / 1000; // how many points to advance

      const steps = Math.floor(accum);
      accum -= steps;

      for (let s = 0; s < steps && idx < pts.length; s++, idx++) {
        layer.addLatLng(pts[idx]);
      }

      if (idx < pts.length) {
        _animHandle = requestAnimationFrame(frame);
      } else {
        _animHandle = null;
        onDone();
      }
    }
    _animHandle = requestAnimationFrame(frame);
  }

  // ── Phase 1: draw building axis (purple)
  function phase1() {
    if (!hasAxis) { phase2(); return; }

    animatePoints(buildPts, buildLine, 180, () => {
      // Arrowhead at tip
      const last = buildPts[buildPts.length-1];
      const prev = buildPts[Math.max(0, buildPts.length-4)];
      const bear = bearing(prev[0],prev[1],last[0],last[1]);
      const aL   = destination(last[0],last[1],(bear+150)%360, 60);
      const aR   = destination(last[0],last[1],(bear+210)%360, 60);
      animLayers.push(
        L.polygon([[last[0],last[1]],[aL.lat,aL.lng],[aR.lat,aR.lng]],
          {color:'#7c6ad8',fillColor:'#7c6ad8',weight:0,fillOpacity:.95}).addTo(map)
      );
      document.getElementById('qp-anim-status').textContent = ' Gerçek yön — şimdi kıble...';
      _animTimer = setTimeout(phase2, 250);
    });
  }

  // ── Phase 2: draw great circle to Kaaba (gold)
  function phase2() {
    // Variable speed: fast at start, slower as it approaches
    animatePoints(qiblaPts, qibleLine, 160, () => {
      // Arrowhead at Kaaba
      const last = qiblaPts[qiblaPts.length-1];
      const prev = qiblaPts[Math.max(0, qiblaPts.length-4)];
      const bear = bearing(prev[0],prev[1],last[0],last[1]);
      const aL   = destination(last[0],last[1],(bear+150)%360, 25000);
      const aR   = destination(last[0],last[1],(bear+210)%360, 25000);
      animLayers.push(
        L.polygon([[last[0],last[1]],[aL.lat,aL.lng],[aR.lat,aR.lng]],
          {color:'#c9a84c',fillColor:'#c9a84c',weight:0,fillOpacity:.95}).addTo(map)
      );
      const diffStr = m.diff!==null ? `${m.diff.toFixed(1)}° sapma` : 'veri yok';
      document.getElementById('qp-anim-status').textContent = ` Tamamlandı — ${diffStr}`;
      if (hasAxis) drawDiffArc(m);
    });
  }

  phase1();
}

function clearFocusPulse() {
  if (focusPulseRaf) {
    try { cancelAnimationFrame(focusPulseRaf); } catch {}
    focusPulseRaf = 0;
  }
  if (focusPulseLayer && map) {
    try { map.removeLayer(focusPulseLayer); } catch {}
  }
  focusPulseLayer = null;
}

function pulseMosqueFocus(m, opts = {}) {
  if (!map || !m || !Number.isFinite(m.lat) || !Number.isFinite(m.lng)) return;
  clearFocusPulse();
  const baseCol = m.status==='correct' ? '#4ade80' : m.status==='wrong' ? '#f87171' : '#fbbf24';
  const waveMs = Number.isFinite(opts.waveMs) ? Math.max(500, opts.waveMs) : 1200;
  const totalMs = Number.isFinite(opts.totalMs) ? Math.max(waveMs, opts.totalMs) : 1800;
  const start = performance.now();
  focusPulseLayer = L.circleMarker([m.lat, m.lng], {
    radius: 8,
    color: baseCol,
    weight: 2,
    opacity: 0.9,
    fillColor: baseCol,
    fillOpacity: 0.08
  }).addTo(map);

  const tick = (now) => {
    if (!focusPulseLayer) return;
    const elapsed = now - start;
    const local = elapsed % waveMs;
    const t = local / waveMs;
    const ease = 1 - Math.pow(1 - t, 3);
    const radius = 8 + ease * 28;
    const opacity = Math.max(0, 0.9 - ease * 0.9);
    try {
      focusPulseLayer.setRadius(radius);
      focusPulseLayer.setStyle({
        opacity,
        fillOpacity: Math.max(0, 0.22 - ease * 0.22)
      });
    } catch {}

    if (elapsed >= totalMs) {
      clearFocusPulse();
      return;
    }
    focusPulseRaf = requestAnimationFrame(tick);
  };
  focusPulseRaf = requestAnimationFrame(tick);
}

// Düz çizgi boyunca ara noktalar (bina yönü için)
function linearPoints(lat1,lng1,lat2,lng2,n=60){
  const pts=[];
  for(let i=0;i<=n;i++){
    const t=i/n;
    pts.push([lat1+(lat2-lat1)*t, lng1+(lng2-lng1)*t]);
  }
  return pts;
}

// Açı farkını görsel yay olarak çiz
function drawDiffArc(m){
  if(m.diff===null||m.axis===null) return;
  const faceDir = closestDirection(m.axis, m.qibla);
  const r = 300; // metre
  const steps = 24;
  // Arc from faceDir to qibla (shortest path)
  let start = faceDir, end = m.qibla;
  // Go the short way
  let delta = ((end - start) + 360) % 360;
  if (delta > 180) delta -= 360;
  const arcPts = [];
  for(let i=0;i<=steps;i++){
    const ang = start + (delta * i/steps);
    const p = destination(m.lat, m.lng, ang, r);
    arcPts.push([p.lat, p.lng]);
  }
  const col = m.diff <= tol ? 'rgba(74,222,128,0.6)' : 'rgba(248,113,113,0.6)';
  animLayers.push(L.polyline(arcPts,{color:col,weight:3,opacity:.8}).addTo(map));
  // Açı etiketi ortasında
  const midAng = start + delta/2;
  const midPt = destination(m.lat, m.lng, midAng, r*1.35);
  animLayers.push(L.marker([midPt.lat,midPt.lng],{
    icon: L.divIcon({
      className:'',
      html:`<div style="background:rgba(22,71,115,.85);border:1px solid ${m.diff<=tol?'#4ade80':'#f87171'};color:${m.diff<=tol?'#4ade80':'#f87171'};font-family:monospace;font-size:11px;font-weight:700;padding:2px 7px;border-radius:4px;white-space:nowrap">${m.diff.toFixed(1)}°</div>`,
      iconAnchor:[20,10]
    })
  }).addTo(map));
  animLayers.push(...animLayers.slice(-1));
}

function hideQiblaPanel() {
  document.getElementById('qibla-panel').classList.remove('show');
  cancelAnimation();
  animLayers.forEach(l=>{ try{map.removeLayer(l);}catch{} });
  animLayers=[];
}

// ══════════════════════════════════════════════════════════════
//  MATH
// ══════════════════════════════════════════════════════════════
const toRad=d=>d*Math.PI/180, toDeg=r=>r*180/Math.PI;
const escHtml = s => String(s ?? '')
  .replace(/&/g,'&amp;')
  .replace(/</g,'&lt;')
  .replace(/>/g,'&gt;')
  .replace(/"/g,'&quot;')
  .replace(/'/g,'&#39;');

function isLikelyMosqueQuery(q) {
  const t = trLower(q || '');
  return /\b(cami|camii|mescid|mescit|mosque|masjid)\b/.test(t);
}

function pickNameFromTags(tags = {}) {
  const nameKeys = [
    'name:tr','name:bs','name:hr','name:sr','name:sr-Latn','name:sr-Cyrl',
    'name','official_name','short_name','name:en','name:ar',
    'loc_name','alt_name','old_name','int_name'
  ];
  for (const k of nameKeys) {
    const v = tags[k];
    if (typeof v === 'string' && v.trim()) return v.trim();
  }
  if (typeof tags.wikipedia === 'string' && tags.wikipedia.includes(':')) {
    const title = tags.wikipedia.split(':').slice(1).join(':').replace(/_/g, ' ').trim();
    if (title) return title;
  }
  const area = tags['addr:suburb'] || tags['addr:neighbourhood'] || tags['addr:quarter'] || tags['addr:village'] || tags['addr:hamlet'];
  if (typeof area === 'string' && area.trim()) return `${area.trim()} Camii`;
  return null;
}

function pickBestNamedetailName(namedetails = {}) {
  const order = ['name:bs','name:hr','name:sr','name:sr-Latn','name:tr','name:en','name'];
  for (const k of order) {
    const v = namedetails[k];
    if (typeof v === 'string' && v.trim()) return v.trim();
  }
  for (const [k,v] of Object.entries(namedetails || {})) {
    if (/^name(:|$)/i.test(k) && typeof v === 'string' && v.trim()) return v.trim();
  }
  return null;
}

function buildAddressBasedMosqueName(addr = {}) {
  const place = addr.suburb || addr.neighbourhood || addr.quarter || addr.village || addr.hamlet || addr.city_district || addr.town || addr.city;
  if (!place || typeof place !== 'string') return null;
  const base = place.trim();
  if (!base) return null;
  const country = trLower(addr.country || '');
  if (/(bosnia|bosna|hersek|hercegovina)/.test(country)) return `${base} Dzamija`;
  return `${base} Camii`;
}

function buildTagsAddressFallbackName(tags = {}, osmId = '') {
  const addr = {
    suburb: tags['addr:suburb'],
    neighbourhood: tags['addr:neighbourhood'],
    quarter: tags['addr:quarter'],
    village: tags['addr:village'],
    hamlet: tags['addr:hamlet'],
    city_district: tags['addr:city_district'] || tags['addr:district'],
    town: tags['addr:town'],
    city: tags['addr:city'],
    country: tags['addr:country']
  };
  const byAddr = buildAddressBasedMosqueName(addr);
  if (byAddr) return byAddr;
  const area = tags['addr:place'] || tags['addr:street'] || tags['addr:county'] || tags['addr:state'];
  if (typeof area === 'string' && area.trim()) return `${area.trim()} Camii`;
  return `OSM Cami #${osmId}`;
}

async function fetchWikidataLabel(qid) {
  if (!/^Q\d+$/i.test(String(qid || '').trim())) return null;
  const key = String(qid).toUpperCase();
  if (wikidataLabelCache.has(key)) return wikidataLabelCache.get(key);
  try {
    const api = `https://www.wikidata.org/w/api.php?action=wbgetentities&ids=${encodeURIComponent(key)}&props=labels&languages=tr|en&format=json&origin=*`;
    const r = await fetch(api);
    const d = await r.json();
    const ent = d?.entities?.[key];
    const label = ent?.labels?.tr?.value || ent?.labels?.en?.value || null;
    wikidataLabelCache.set(key, label);
    return label;
  } catch {
    wikidataLabelCache.set(key, null);
    return null;
  }
}

function isPlaceholderMosqueName(name) {
  const t = trLower(name || '').trim();
  return !t || t === 'isimsiz cami' || t.startsWith('isimsiz cami (#') || t.startsWith('osm cami #');
}

function isGenericMosqueName(name) {
  const t = trLower(String(name || '').trim());
  return /^(cami|camii|mosque|masjid|mescit|mescid|cuma camii|dzamija|džamija)$/.test(t);
}

function loadNameEnrichCache() {
  try {
    const raw = safeStorageGet(NAME_ENRICH_KEY, null);
    if (!raw) return;
    const parsed = JSON.parse(raw);
    if (!parsed || typeof parsed !== 'object') return;
    Object.entries(parsed).forEach(([k,v]) => {
      if (v && typeof v.name === 'string') nameEnrichCache.set(k, v);
    });
  } catch {}
}

function saveNameEnrichCache() {
  try {
    const obj = {};
    nameEnrichCache.forEach((v,k) => { obj[k] = v; });
    safeStorageSet(NAME_ENRICH_KEY, JSON.stringify(obj));
  } catch {}
}

function loadPopularityCache() {
  try {
    const raw = safeStorageGet(POPULARITY_KEY, null);
    if (!raw) return;
    const parsed = JSON.parse(raw);
    if (!parsed || typeof parsed !== 'object') return;
    Object.entries(parsed).forEach(([k,v]) => {
      if (!v || typeof v !== 'object') return;
      if (!Number.isFinite(v.views) || !Number.isFinite(v.ts)) return;
      popularityCache.set(k, { views: Math.max(0, Math.round(v.views)), ts: v.ts });
    });
  } catch {}
}

function savePopularityCache() {
  try {
    const obj = {};
    popularityCache.forEach((v,k) => { obj[k] = v; });
    safeStorageSet(POPULARITY_KEY, JSON.stringify(obj));
  } catch {}
}

function loadVisitTrafficCache() {
  try {
    const raw = safeStorageGet(VISIT_TRAFFIC_KEY, null);
    if (!raw) return;
    const parsed = JSON.parse(raw);
    if (!parsed || typeof parsed !== 'object') return;
    Object.entries(parsed).forEach(([k,v]) => {
      if (!v || typeof v !== 'object') return;
      if (!Number.isFinite(v.count) || !Number.isFinite(v.ts)) return;
      visitTrafficCache.set(k, { count: Math.max(0, Math.round(v.count)), ts: v.ts });
    });
  } catch {}
}

function saveVisitTrafficCache() {
  try {
    const obj = {};
    visitTrafficCache.forEach((v,k) => { obj[k] = v; });
    safeStorageSet(VISIT_TRAFFIC_KEY, JSON.stringify(obj));
  } catch {}
}

function getVisitTrafficCacheKey(m) {
  if (!m) return '';
  const raw = getMosqueKey(m);
  return raw ? `mosque:${raw}` : '';
}

function getVisitTrafficCount(m) {
  const key = getVisitTrafficCacheKey(m);
  if (!key) return 0;
  const rec = visitTrafficCache.get(key);
  return rec && Number.isFinite(rec.count) ? rec.count : 0;
}

function getVisitTrafficRecord(m) {
  const key = getVisitTrafficCacheKey(m);
  if (!key) return null;
  const rec = visitTrafficCache.get(key);
  if (!rec || !Number.isFinite(rec.count)) return null;
  return { count: Math.max(0, rec.count), ts: Number.isFinite(rec.ts) ? rec.ts : 0 };
}

function bumpVisitTrafficCount(m) {
  const key = getVisitTrafficCacheKey(m);
  if (!key) return;
  const prev = visitTrafficCache.get(key);
  const nextCount = Math.max(1, (prev?.count || 0) + 1);
  visitTrafficCache.set(key, { count: nextCount, ts: Date.now() });
  saveVisitTrafficCache();
}

function loadCitySearchHistory() {
  try {
    const raw = safeStorageGet(CITY_SEARCH_HISTORY_KEY, '[]');
    const arr = JSON.parse(raw);
    if (!Array.isArray(arr)) return;
    citySearchHistory = arr
      .filter(x => x && typeof x === 'object' && (x.query || x.title))
      .map(x => ({
        query: String(x.query || '').trim(),
        title: String(x.title || x.query || '').trim(),
        subtitle: String(x.subtitle || '').trim(),
        kind: x.kind === 'mosque' ? 'mosque' : 'place',
        lat: Number(x.lat),
        lng: Number(x.lng),
        ts: Number.isFinite(x.ts) ? x.ts : 0,
        count: Number.isFinite(x.count) ? Math.max(1, Math.round(x.count)) : 1,
        osmType: normalizeOsmType(x.osmType),
        osmId: String(x.osmId || '').replace(/\D/g,''),
        bbox: Array.isArray(x.bbox) && x.bbox.length === 4 ? x.bbox.map(Number) : null
      }))
      .sort((a,b) => (b.ts - a.ts) || (b.count - a.count))
      .slice(0, 40);
  } catch {
    citySearchHistory = [];
  }
}

function saveCitySearchHistory() {
  try {
    safeStorageSet(CITY_SEARCH_HISTORY_KEY, JSON.stringify(citySearchHistory.slice(0, 40)));
  } catch {}
}

function removeCitySearchHistoryEntry(key) {
  if (!key) return;
  citySearchHistory = citySearchHistory.filter(x => citySearchHistoryKey(x) !== key);
  saveCitySearchHistory();
}

function clearCitySearchHistory() {
  citySearchHistory = [];
  saveCitySearchHistory();
}

function citySearchHistoryKey(rec = {}) {
  if (rec.osmType && rec.osmId) return `${rec.kind || 'place'}:${rec.osmType}:${rec.osmId}`;
  const seed = normalize(trLower(rec.title || rec.query || ''));
  return `${rec.kind || 'place'}:${seed}`;
}

function bumpCitySearchHistory(rec = {}) {
  const query = String(rec.query || rec.title || '').trim();
  if (!query) return;
  const item = {
    query,
    title: String(rec.title || query).trim(),
    subtitle: String(rec.subtitle || '').trim(),
    kind: rec.kind === 'mosque' ? 'mosque' : 'place',
    lat: Number(rec.lat),
    lng: Number(rec.lng),
    ts: Date.now(),
    count: 1,
    osmType: normalizeOsmType(rec.osmType),
    osmId: String(rec.osmId || '').replace(/\D/g,''),
    bbox: Array.isArray(rec.bbox) && rec.bbox.length === 4 ? rec.bbox.map(Number) : null
  };
  const key = citySearchHistoryKey(item);
  const idx = citySearchHistory.findIndex(x => citySearchHistoryKey(x) === key);
  if (idx >= 0) {
    const prev = citySearchHistory[idx];
    item.count = Math.max(1, (prev.count || 0) + 1);
    if (!item.subtitle) item.subtitle = prev.subtitle || '';
    if (!Number.isFinite(item.lat)) item.lat = prev.lat;
    if (!Number.isFinite(item.lng)) item.lng = prev.lng;
    if (!item.osmType) item.osmType = prev.osmType || '';
    if (!item.osmId) item.osmId = prev.osmId || '';
    if (!item.bbox) item.bbox = prev.bbox || null;
    citySearchHistory.splice(idx, 1);
  }
  citySearchHistory.unshift(item);
  citySearchHistory = citySearchHistory.slice(0, 40);
  saveCitySearchHistory();
}

function enrichCacheKey(m) {
  return `${m.osmType || 'way'}:${m.id}`;
}

async function fetchOverpassNearbyNameCandidates(m, radiusM = 120) {
  const q = `[out:json][timeout:30];
(
  node(around:${radiusM},${m.lat},${m.lng})["amenity"="place_of_worship"]["~"^name(:.*)?$"~"."] ;
  way(around:${radiusM},${m.lat},${m.lng})["amenity"="place_of_worship"]["~"^name(:.*)?$"~"."] ;
  relation(around:${radiusM},${m.lat},${m.lng})["amenity"="place_of_worship"]["~"^name(:.*)?$"~"."] ;
  node(around:${radiusM},${m.lat},${m.lng})["amenity"="mosque"]["~"^name(:.*)?$"~"."] ;
  way(around:${radiusM},${m.lat},${m.lng})["amenity"="mosque"]["~"^name(:.*)?$"~"."] ;
  relation(around:${radiusM},${m.lat},${m.lng})["amenity"="mosque"]["~"^name(:.*)?$"~"."] ;
  node(around:${radiusM},${m.lat},${m.lng})["building"="mosque"]["~"^name(:.*)?$"~"."] ;
  way(around:${radiusM},${m.lat},${m.lng})["building"="mosque"]["~"^name(:.*)?$"~"."] ;
  relation(around:${radiusM},${m.lat},${m.lng})["building"="mosque"]["~"^name(:.*)?$"~"."] ;
);
out center tags 120;`;
  const els = await fetchOverpassQuery(q);
  const out = [];
  for (const el of els) {
    const tags = el.tags || {};
    const nm = pickNameFromTags(tags);
    if (!nm || isGenericMosqueName(nm)) continue;
    const lat = el.type === 'node' ? el.lat : el.center?.lat;
    const lng = el.type === 'node' ? el.lon : el.center?.lon;
    if (!Number.isFinite(lat) || !Number.isFinite(lng)) continue;
    const d = greatCircleM(m.lat, m.lng, lat, lng);
    const same = (String(el.id) === String(m.id));
    out.push({ name:nm, source:'overpass-near', dist:d, sameId:same });
  }
  return out;
}

async function fetchNominatimReverseCandidate(m) {
  const url = `https://nominatim.openstreetmap.org/reverse?lat=${m.lat}&lon=${m.lng}&format=jsonv2&zoom=18&addressdetails=1&namedetails=1`;
  try {
    const d = await nominatimFetchJson(url, {'Accept-Language':'bs,hr,sr,en,tr'});
    const cls = trLower(d.class || '');
    const type = trLower(d.type || '');
    const nm = pickBestNamedetailName(d.namedetails || {}) || String(d.name || d.display_name || '').split(',')[0].trim();
    if (!nm || isGenericMosqueName(nm)) return null;
    return { name:nm, source:'nominatim-reverse', cls, type, address:d.address || {} };
  } catch {
    return null;
  }
}

async function fetchNominatimNearbyCandidates(m) {
  const span = 0.003; // ~300m
  const left = (m.lng - span).toFixed(6);
  const right = (m.lng + span).toFixed(6);
  const top = (m.lat + span).toFixed(6);
  const bottom = (m.lat - span).toFixed(6);
  const terms = ['mosque','masjid','džamija','dzamija','cami'];
  const out = [];
  const seen = new Set();
  try {
    for (const term of terms) {
      const url = `https://nominatim.openstreetmap.org/search?format=jsonv2&q=${encodeURIComponent(term)}&limit=8&bounded=1&viewbox=${left},${top},${right},${bottom}&addressdetails=1&namedetails=1`;
      const d = await nominatimFetchJson(url, {'Accept-Language':'bs,hr,sr,en,tr'});
      for (const it of (d || [])) {
        const nm = pickBestNamedetailName(it.namedetails || {}) || String(it.name || it.display_name || '').split(',')[0].trim();
        if (!nm || isGenericMosqueName(nm)) continue;
        const lat = +it.lat, lng = +it.lon;
        if (!Number.isFinite(lat) || !Number.isFinite(lng)) continue;
        const k = `${nm}|${lat.toFixed(5)}|${lng.toFixed(5)}`;
        if (seen.has(k)) continue;
        seen.add(k);
        out.push({ name:nm, source:'nominatim-near', dist:greatCircleM(m.lat,m.lng,lat,lng), cls:trLower(it.class||''), type:trLower(it.type||'') });
      }
    }
    return out;
  } catch {
    return [];
  }
}

function scoreNameCandidate(c) {
  let s = 0;
  if (c.source === 'wikidata') s += 72;
  if (c.source === 'address-synth') s += 30;
  if (c.source === 'overpass-near') {
    if (c.sameId) s += 140;
    else if (c.dist <= 20) s += 95;
    else if (c.dist <= 45) s += 78;
    else if (c.dist <= 90) s += 60;
    else s += 45;
  }
  if (c.source === 'nominatim-reverse') {
    s += 42;
    if (c.cls === 'amenity' && (c.type === 'place_of_worship' || c.type === 'mosque')) s += 35;
  }
  if (c.source === 'nominatim-near') {
    s += c.dist <= 25 ? 45 : c.dist <= 60 ? 35 : 20;
    if (c.cls === 'amenity' && (c.type === 'place_of_worship' || c.type === 'mosque')) s += 20;
  }
  if (isGenericMosqueName(c.name)) s -= 55;
  if (c.name.length < 4) s -= 18;
  return s;
}

async function resolveMosqueNameFromSources(m) {
  const candidates = [];
  const wd = m.tags?.wikidata ? await fetchWikidataLabel(m.tags.wikidata) : null;
  if (wd) candidates.push({ name:wd, source:'wikidata' });
  const rev = await fetchNominatimReverseCandidate(m);
  if (rev) candidates.push(rev);
  const nearNom = await fetchNominatimNearbyCandidates(m);
  nearNom.forEach(x => candidates.push(x));
  for (const r of [60, 140, 260]) {
    const nearOv = await fetchOverpassNearbyNameCandidates(m, r);
    nearOv.forEach(x => candidates.push(x));
    if (candidates.some(c => c.source === 'overpass-near' && c.sameId)) break;
  }
  if (rev?.address) {
    const synth = buildAddressBasedMosqueName(rev.address);
    if (synth) candidates.push({ name:synth, source:'address-synth', cls:'synthetic', type:'synthetic' });
  }
  if (!candidates.length) return null;

  const best = candidates
    .map(c => ({...c, score:scoreNameCandidate(c)}))
    .sort((a,b) => b.score - a.score)[0];
  if (!best || (best.source === 'address-synth' ? best.score < 28 : best.score < 45)) return null;
  return { name: best.name.trim(), source: best.source, score: best.score };
}

function applyResolvedNameToMosque(m, resolved) {
  if (!m || !resolved?.name) return false;
  const newName = resolved.name.trim();
  if (!newName || isGenericMosqueName(newName)) return false;
  const changed = m.name !== newName;
  m.name = newName;
  if (!m.tags) m.tags = {};
  m.tags.name = m.tags.name || newName;
  m.tags['name:source'] = resolved.source;
  buildSearchIndexForMosque(m);
  if (changed) {
    const key = enrichCacheKey(m);
    nameEnrichCache.set(key, { name:newName, source:resolved.source, at:Date.now() });
    saveNameEnrichCache();
  }
  return changed;
}

async function enrichMosqueName(m, opts = {}) {
  if (!m) return null;
  const force = !!opts.force;
  const key = enrichCacheKey(m);
  const cached = nameEnrichCache.get(key);
  if (cached && cached.name && !force) {
    applyResolvedNameToMosque(m, { name:cached.name, source:cached.source || 'cache' });
    return m.name;
  }
  if (!force && !isPlaceholderMosqueName(m.name) && !isGenericMosqueName(m.name)) return m.name;
  const resolved = await resolveMosqueNameFromSources(m);
  if (!resolved) return null;
  applyResolvedNameToMosque(m, resolved);
  return m.name;
}

function enqueueMosqueNameEnrichment(m) {
  if (!m || (!isPlaceholderMosqueName(m.name) && !isGenericMosqueName(m.name))) return;
  const key = enrichCacheKey(m);
  if (nameEnrichQueued.has(key)) return;
  nameEnrichQueued.add(key);
  nameEnrichQueue.push(m);
  runMosqueNameEnrichmentQueue();
}

async function runMosqueNameEnrichmentQueue() {
  if (nameEnrichRunning) return;
  nameEnrichRunning = true;
  while (nameEnrichQueue.length) {
    const m = nameEnrichQueue.shift();
    const key = enrichCacheKey(m);
    try {
      const before = m.name;
      await enrichMosqueName(m);
      if (m.name !== before && map && mosqueDB.size) {
        const bounds = map.getBounds().pad(0.1);
        const visible = [...mosqueDB.values()].filter(x => bounds.contains([x.lat, x.lng]));
        if (mosqueFilter) applyMosqueFilter(mosqueFilter);
        else updateList(visible);
      }
    } catch {}
    nameEnrichQueued.delete(key);
    await new Promise(r => setTimeout(r, 250));
  }
  nameEnrichRunning = false;
}

function boostNameEnrichment(maxItems = 90) {
  const targets = [...mosqueDB.values()]
    .filter(m => isPlaceholderMosqueName(m.name) || isGenericMosqueName(m.name))
    .sort((a,b) => {
      const da = greatCircleM(a.lat, a.lng, map.getCenter().lat, map.getCenter().lng);
      const db = greatCircleM(b.lat, b.lng, map.getCenter().lat, map.getCenter().lng);
      return da - db;
    })
    .slice(0, maxItems);
  targets.forEach(m => enqueueMosqueNameEnrichment(m));
}

function countUnresolvedMosqueNames() {
  let unresolved = 0;
  for (const m of mosqueDB.values()) {
    if (isPlaceholderMosqueName(m.name) || isGenericMosqueName(m.name)) unresolved++;
  }
  return unresolved;
}

function triggerAggressiveNameEnrichment() {
  if (!mosqueDB.size) return;
  const unresolved = countUnresolvedMosqueNames();
  if (unresolved < 6) return;
  const maxItems = unresolved > 320 ? 240 : unresolved > 160 ? 170 : unresolved > 80 ? 120 : 80;
  const queuedBefore = nameEnrichQueue.length;
  boostNameEnrichment(maxItems);
  const queuedAfter = nameEnrichQueue.length;
  if (queuedAfter > queuedBefore) {
    toast(`İsim zenginleştirme aktif: ${unresolved} kayıt için arka planda isim aranıyor`, 4200);
  }
}

function loadInteriorDB() {
  try {
    const raw = safeStorageGet(INTERIOR_KEY, null);
    interiorDB = raw ? JSON.parse(raw) : {};
    if (!interiorDB || typeof interiorDB !== 'object') interiorDB = {};
  } catch { interiorDB = {}; }
}

function loadSnapshots() {
  try {
    const raw = safeStorageGet(SNAPSHOT_KEY, null);
    snapshots = raw ? JSON.parse(raw) : [];
    if (!Array.isArray(snapshots)) snapshots = [];
  } catch { snapshots = []; }
}

function saveSnapshot() {
  const all = [...mosqueDB.values()];
  const withData = all.filter(m => m.diff != null);
  const correct = withData.filter(m => m.diff <= tol).length;
  const lowConf = all.filter(m => (m.confidence || 0) < 55).length;
  const snap = {
    city: currentCity,
    ts: Date.now(),
    total: all.length,
    withData: withData.length,
    pct: withData.length ? Math.round(correct / withData.length * 100) : null,
    lowConf
  };
  snapshots.push(snap);
  snapshots = snapshots.slice(-50);
  try { safeStorageSet(SNAPSHOT_KEY, JSON.stringify(snapshots)); } catch {}
}

function saveInteriorDB() {
  try { safeStorageSet(INTERIOR_KEY, JSON.stringify(interiorDB)); } catch {}
}

function loadManualAxisDB() {
  try {
    const raw = safeStorageGet(MANUAL_AXIS_KEY, null);
    manualAxisDB = raw ? JSON.parse(raw) : {};
    if (!manualAxisDB || typeof manualAxisDB !== 'object') manualAxisDB = {};
  } catch { manualAxisDB = {}; }
}

function saveManualAxisDB() {
  try { safeStorageSet(MANUAL_AXIS_KEY, JSON.stringify(manualAxisDB)); } catch {}
}

function getManualAxisRecord(m) {
  return manualAxisDB[getMosqueKey(m)] || null;
}

function aiModerateManualAxis(m, axis180) {
  const reasons = [];
  let score = 0.5;
  if (!Number.isFinite(axis180)) return { status:'rejected', score:0, reasons:['axis_nan'] };

  const base = m.baseAxis;
  const interiorAxis = getInteriorAxis(m);
  const diffQ = angDiff180(m.qibla % 180, axis180);
  const diffBase = base!=null ? angDiff180(base, axis180) : null;
  const diffInt = interiorAxis!=null ? angDiff180(interiorAxis, axis180) : null;

  if (diffQ <= 35) { score += 0.22; reasons.push('close_to_qibla'); }
  else if (diffQ <= 55) { score += 0.1; reasons.push('moderate_qibla_alignment'); }
  else { score -= 0.18; reasons.push('far_from_qibla'); }

  if (diffBase!=null) {
    if (diffBase <= 18) { score += 0.16; reasons.push('consistent_with_building'); }
    else if (diffBase > 70) { score -= 0.14; reasons.push('conflicts_building_axis'); }
  }
  if (diffInt!=null) {
    if (diffInt <= 14) { score += 0.26; reasons.push('consistent_with_interior'); }
    else if (diffInt > 65) { score -= 0.2; reasons.push('conflicts_interior_evidence'); }
  }

  if ((m.fusion?.interiorCount || 0) >= 2) score += 0.06;
  if (m.convertedFrom?.converted) score -= 0.04;

  score = Math.max(0, Math.min(1, score));
  let status = 'accepted';
  if (score < 0.42) status = 'rejected';
  else if (score < 0.57) status = 'pending';
  return { status, score, reasons };
}

function applyManualAxisSubmission(m, axis180, source = 'map-2point') {
  const moderation = aiModerateManualAxis(m, axis180);
  const key = getMosqueKey(m);
  manualAxisDB[key] = {
    axis: axis180,
    source,
    ts: Date.now(),
    moderation
  };
  saveManualAxisDB();
  applyAxisFusion(m);
  return moderation;
}

function setAxisMode(mode) {
  analysisLayerMode = mode;
  ['final','raw','interior'].forEach(k => {
    const el = document.getElementById('axis-'+k);
    if (el) el.classList.toggle('active', k===mode);
  });
  renderAll();
  if (window._lastClickedMosque) populateDetailPanel(window._lastClickedMosque);
}

const I18N = {
  tr: {
    title:'Kıble Dedektörü', searchPlaceholder:'Şehir adı...', searchBtn:'Ara',
    toolsHeat:' Isı', toolsScore:' Skor', toolsCompare:' Karşılaştır',
    toolsHistory:' Tarih', toolsRank:' Sıralama', toolsLoc:' Konum',
    toolsExport:' Export', toolsBiz:' Gelir', toolsLab:' Lab', toolsCompass:' Pusula',
    toolsFollow:' Takip', toolsNearby:' Yakın', toolsOutdoor:' Outdoor'
  },
  en: {
    title:'Qibla Detector', searchPlaceholder:'City name...', searchBtn:'Search',
    toolsHeat:' Heat', toolsScore:' Score', toolsCompare:' Compare',
    toolsHistory:' History', toolsRank:' Ranking', toolsLoc:' My Location',
    toolsExport:' Export', toolsBiz:' Revenue', toolsLab:' Lab', toolsCompass:' Compass',
    toolsFollow:' Follow', toolsNearby:' Nearby', toolsOutdoor:' Outdoor'
  }
};

function setLang(lang, silent=false) {
  currentLang = lang === 'en' ? 'en' : 'tr';
  safeStorageSet(LANG_KEY, currentLang);
  const t = I18N[currentLang];
  document.documentElement.lang = currentLang;
  const tt = (id, txt, prop='textContent') => { const el = document.getElementById(id); if (el) el[prop] = txt; };
  tt('search-btn', t.searchBtn);
  tt('btn-heat', t.toolsHeat);
  tt('btn-score', t.toolsScore);
  tt('btn-compare', t.toolsCompare);
  tt('btn-history', t.toolsHistory);
  tt('btn-lb', t.toolsRank);
  tt('loc-btn', t.toolsLoc);
  tt('btn-export', t.toolsExport);
  tt('btn-biz', t.toolsBiz);
  tt('btn-lab', t.toolsLab);
  tt('btn-compass', t.toolsCompass);
  tt('btn-follow', t.toolsFollow);
  tt('btn-nearby', t.toolsNearby);
  tt('btn-outdoor', t.toolsOutdoor);
  const cityInput = document.getElementById('city-input');
  if (cityInput) cityInput.placeholder = t.searchPlaceholder;
  const logo = document.querySelector('.logo-title');
  if (logo) logo.textContent = t.title;
  document.getElementById('lang-tr')?.classList.toggle('active', currentLang==='tr');
  document.getElementById('lang-en')?.classList.toggle('active', currentLang==='en');
  if (dpOpen && window._lastClickedMosque) populateDetailPanel(window._lastClickedMosque);
  if (!silent) toast(currentLang==='tr' ? 'Dil Türkçe' : 'Language set to English', 1400);
}

function getMosqueKey(m) {
  return `${m.osmType || 'way'}:${m.id}`;
}

function getInteriorEvidenceList(m) {
  const arr = interiorDB[getMosqueKey(m)];
  return Array.isArray(arr) ? arr : [];
}

function toAxis180(v) {
  const n = ((+v % 180) + 180) % 180;
  return Number.isFinite(n) ? n : null;
}

function weightedAxisMean180(items) {
  let x = 0, y = 0, wSum = 0;
  for (const it of items) {
    const a = toAxis180(it.axis);
    const w = Math.max(0, Number(it.weight) || 0);
    if (a === null || !w) continue;
    const r = toRad(a * 2);
    x += Math.cos(r) * w;
    y += Math.sin(r) * w;
    wSum += w;
  }
  if (!wSum) return { axis:null, reliability:0 };
  const ang = ((toDeg(Math.atan2(y, x)) / 2) + 180) % 180;
  const rel = Math.sqrt(x*x + y*y) / wSum;
  return { axis:ang, reliability:rel };
}

function parseDirectionalTag(tags = {}) {
  const keys = ['qibla:direction','prayer:direction','mihrab:direction','direction','building:direction','roof:direction'];
  for (const k of keys) {
    const v = tags[k];
    if (v == null) continue;
    const num = Number(v);
    if (Number.isFinite(num)) return toAxis180(num);
  }
  return null;
}

function detectConversionInfo(tags = {}) {
  const checks = [
    'building:former_use','was:building','was:amenity','old_religion','former_religion',
    'historic:religion','description','note','source'
  ];
  let raw = '';
  for (const k of checks) if (tags[k]) raw += ' ' + String(tags[k]);
  const hay = trLower(raw);
  const prev = tags['building:former_use'] || tags['was:building'] || tags['old_religion'] || tags['former_religion'] || '';
  const hit = /(church|kilise|synagogue|sinagog|temple|tapinak|tapınak|cathedral|chapel|monastery|manastir|manastır)/.test(hay);
  if (!hit && !prev) return null;
  return {
    converted: true,
    previous: String(prev || 'unknown'),
    evidence: raw.trim().slice(0,220)
  };
}

function computeConfidenceScore(m) {
  const manualRec = getManualAxisRecord(m);
  let score = 45;
  if (m.baseMethod === 'osm-tag') score += 20;
  else if (m.baseMethod === 'edge-analysis') score += 12;
  if (m.fusion?.mode === 'hybrid-interior') score += 16;
  if (m.fusion?.mode === 'interior-only') score += 12;
  score += Math.round((m.fusion?.reliability || 0) * 12);
  if ((m.fusion?.interiorCount || 0) >= 2) score += 8;
  if (m.name && !isPlaceholderMosqueName(m.name) && !isGenericMosqueName(m.name)) score += 6;
  if (m.diff == null) score -= 18;
  if (m.convertedFrom?.converted) score -= 6;
  if ((m.geomComplexity || 0) > 0.62) score -= 8;
  else if ((m.geomComplexity || 0) > 0.46) score -= 4;
  if (manualRec?.moderation?.status === 'accepted') score += 6;
  if (manualRec?.moderation?.status === 'rejected') score -= 8;
  score = Math.max(0, Math.min(100, score));
  m.confidence = score;
  m.confidenceBand = score >= 80 ? 'high' : score >= 55 ? 'medium' : 'low';
  m.qualityBadges = [
    m.confidenceBand === 'high' ? 'High Confidence' : m.confidenceBand === 'medium' ? 'Medium Confidence' : 'Low Confidence',
    m.fusion?.mode || 'none',
    m.convertedFrom?.converted ? 'Converted Structure' : 'Native Mosque',
    (m.geomComplexity || 0) > 0.62 ? 'Complex Geometry' : (m.geomComplexity || 0) > 0.46 ? 'Irregular Geometry' : 'Simple Geometry',
    isPlaceholderMosqueName(m.name) ? 'Name Missing' : 'Name OK',
    manualRec?.moderation?.status ? `Manual:${manualRec.moderation.status}` : 'Manual:none'
  ];
  return score;
}

function getInteriorAxis(m) {
  const interior = getInteriorEvidenceList(m);
  if (!interior.length) return null;
  const local = weightedAxisMean180(interior.map(ev => ({ axis:ev.axis, weight:Math.max(0.2, Number(ev.confidence)||0.6) })));
  return local.axis;
}

function applyAxisFusion(m) {
  const candidates = [];
  const manualRec = getManualAxisRecord(m);
  const tagAxis = parseDirectionalTag(m.tags || {});
  if (tagAxis !== null) candidates.push({ axis:tagAxis, weight:0.95, label:'osm-direction' });
  if (m.baseAxis !== null && m.baseAxis !== undefined) {
    const w = m.baseMethod === 'osm-tag' ? 0.85 : 0.62;
    candidates.push({ axis:m.baseAxis, weight:w, label:m.baseMethod || 'building' });
  }
  const interior = getInteriorEvidenceList(m);
  if (interior.length) {
    const local = weightedAxisMean180(interior.map(ev => ({ axis:ev.axis, weight:Math.max(0.2, Number(ev.confidence)||0.6) })));
    if (local.axis !== null) candidates.push({ axis:local.axis, weight:0.55 + 0.45*local.reliability, label:'interior' });
  }
  if (manualRec?.axis != null && manualRec?.moderation?.status === 'accepted') {
    const mw = 0.9 + 0.1 * (manualRec.moderation.score || 0.5);
    candidates.push({ axis:manualRec.axis, weight:mw, label:'manual-accepted' });
  }

  const fused = weightedAxisMean180(candidates);
  if (fused.axis === null) {
    m.axis = null;
    m.diff = null;
    m.status = 'unknown';
    m.method = m.baseMethod || 'none';
    m.fusion = { mode:'none', reliability:0, candidates:0 };
    m.convertedFrom = detectConversionInfo(m.tags || {});
    computeConfidenceScore(m);
    return m;
  }

  m.axis = fused.axis;
  m.diff = angDiff180(m.qibla % 180, m.axis);
  m.status = m.diff <= tol ? 'correct' : 'wrong';
  const hasInterior = interior.length > 0;
  const hasBase = m.baseAxis !== null && m.baseAxis !== undefined;
  m.method = hasInterior && hasBase ? 'hybrid-interior' : hasInterior ? 'interior-only' : (m.baseMethod || 'fused');
  m.fusion = {
    mode: m.method,
    reliability: fused.reliability,
    candidates: candidates.length,
    interiorCount: interior.length,
    manualStatus: manualRec?.moderation?.status || 'none'
  };
  m.convertedFrom = detectConversionInfo(m.tags || {});
  computeConfidenceScore(m);
  return m;
}

function getDisplayAxis(m) {
  if (analysisLayerMode === 'raw') return m.baseAxis ?? null;
  if (analysisLayerMode === 'interior') return getInteriorAxis(m);
  return m.axis;
}

const interiorPhotoCache = new Map();
function looksInteriorText(t) {
  return /(interior|inside|prayer|hall|mihrab|musalla|mushalla|iç|ic mekan|salah|namaz)/i.test(String(t || ''));
}

async function fetchCommonsInteriorByCategory(catName) {
  if (!catName) return [];
  const clean = String(catName).replace(/^Category:/i,'').trim();
  const api = `https://commons.wikimedia.org/w/api.php?action=query&list=categorymembers&cmtitle=Category:${encodeURIComponent(clean)}&cmnamespace=6&cmlimit=40&format=json&origin=*`;
  const r = await fetch(api);
  const d = await r.json();
  const files = (d?.query?.categorymembers || []).filter(x => looksInteriorText(x.title));
  if (!files.length) return [];
  const titles = files.slice(0,8).map(x=>x.title).join('|');
  const api2 = `https://commons.wikimedia.org/w/api.php?action=query&titles=${encodeURIComponent(titles)}&prop=imageinfo&iiprop=url&format=json&origin=*`;
  const r2 = await fetch(api2); const d2 = await r2.json();
  const pages = d2?.query?.pages || {};
  return Object.values(pages).map(p => p?.imageinfo?.[0]?.url).filter(Boolean);
}

async function fetchCommonsInteriorBySearch(term) {
  const q = `${term} mosque interior`;
  const api = `https://commons.wikimedia.org/w/api.php?action=query&generator=search&gsrsearch=${encodeURIComponent(q)}&gsrnamespace=6&gsrlimit=10&prop=imageinfo&iiprop=url&format=json&origin=*`;
  const r = await fetch(api); const d = await r.json();
  const pages = d?.query?.pages || {};
  return Object.values(pages)
    .filter(p => looksInteriorText(p.title))
    .map(p => p?.imageinfo?.[0]?.url)
    .filter(Boolean);
}

async function resolveInteriorPhotos(m) {
  const key = getMosqueKey(m);
  if (interiorPhotoCache.has(key)) return interiorPhotoCache.get(key);
  const out = [];
  try {
    const wm = m.tags?.wikimedia_commons || '';
    if (/^Category:/i.test(wm)) {
      const a = await fetchCommonsInteriorByCategory(wm);
      a.forEach(url => out.push({ url, source:'commons-category' }));
    }
  } catch {}
  try {
    const b = await fetchCommonsInteriorBySearch(m.name || '');
    b.forEach(url => out.push({ url, source:'commons-search' }));
  } catch {}
  const uniq = [];
  const seen = new Set();
  for (const p of out) {
    if (!p?.url || seen.has(p.url)) continue;
    seen.add(p.url);
    uniq.push(p);
    if (uniq.length >= 8) break;
  }
  interiorPhotoCache.set(key, uniq);
  return uniq;
}

function qiblaAngle(lat,lng){
  const p1=toRad(lat),p2=toRad(KAABA.lat),dl=toRad(KAABA.lng-lng);
  return(toDeg(Math.atan2(Math.sin(dl)*Math.cos(p2),Math.cos(p1)*Math.sin(p2)-Math.sin(p1)*Math.cos(p2)*Math.cos(dl)))+360)%360;
}

function greatCircleM(lat1,lng1,lat2,lng2){
  const R=6371000;
  const p1=toRad(lat1),p2=toRad(lat2),dp=toRad(lat2-lat1),dl=toRad(lng2-lng1);
  const a=Math.sin(dp/2)**2+Math.cos(p1)*Math.cos(p2)*Math.sin(dl/2)**2;
  return R*2*Math.atan2(Math.sqrt(a),Math.sqrt(1-a));
}
function greatCircleKm(lat1,lng1,lat2,lng2){ return greatCircleM(lat1,lng1,lat2,lng2)/1000; }

function greatCirclePoints(lat1,lng1,lat2,lng2,n=100){
  // Slerp-based great circle interpolation
  const p1=toRad(lat1),l1=toRad(lng1),p2=toRad(lat2),l2=toRad(lng2);
  // Convert to cartesian
  const cart=([p,l])=>[Math.cos(p)*Math.cos(l),Math.cos(p)*Math.sin(l),Math.sin(p)];
  const A=cart([p1,l1]),B=cart([p2,l2]);
  const dot=A[0]*B[0]+A[1]*B[1]+A[2]*B[2];
  const omega=Math.acos(Math.min(1,Math.max(-1,dot)));
  const pts=[];
  for(let i=0;i<=n;i++){
    const t=i/n;
    const s=Math.sin(omega)>1e-10 ? 1/Math.sin(omega) : 1;
    const sa=Math.sin((1-t)*omega)*s, sb=Math.sin(t*omega)*s;
    const x=sa*A[0]+sb*B[0], y=sa*A[1]+sb*B[1], z=sa*A[2]+sb*B[2];
    const lat=toDeg(Math.atan2(z,Math.sqrt(x*x+y*y)));
    const lng=toDeg(Math.atan2(y,x));
    pts.push([lat,lng]);
  }
  return pts;
}

function bearing(lat1,lng1,lat2,lng2){
  const p1=toRad(lat1),p2=toRad(lat2),dl=toRad(lng2-lng1);
  return(toDeg(Math.atan2(Math.sin(dl)*Math.cos(p2),Math.cos(p1)*Math.sin(p2)-Math.sin(p1)*Math.cos(p2)*Math.cos(dl)))+360)%360;
}

function buildingQiblaEdge(polyCoords,qibla){
  if(!polyCoords||polyCoords.length<4) return null;
  const edges=[];
  for(let i=0;i<polyCoords.length-1;i++){
    const[lat1,lng1]=polyCoords[i],[lat2,lng2]=polyCoords[i+1];
    const dx=(lng2-lng1)*Math.cos(toRad((lat1+lat2)/2))*111320;
    const dy=(lat2-lat1)*111320;
    const len=Math.sqrt(dx*dx+dy*dy);
    if(len<0.5) continue;
    const angle=(toDeg(Math.atan2(dx,dy))+360)%180;
    edges.push({angle,len});
  }
  if(!edges.length) return null;
  const bins=new Array(36).fill(0);
  for(const{angle,len}of edges){
    const b=Math.floor(angle/5)%36;
    bins[b]+=len; bins[(b+1)%36]+=len*.3; bins[(b+35)%36]+=len*.3;
  }
  let maxBin=0;
  for(let i=1;i<36;i++) if(bins[i]>bins[maxBin]) maxBin=i;
  const dir1=maxBin*5;
  let secondBin=0;
  for(let i=0;i<36;i++){
    const d=Math.min(Math.abs(i-maxBin),36-Math.abs(i-maxBin));
    if(d>=3&&bins[i]>bins[secondBin]) secondBin=i;
  }
  const dir2=secondBin*5;
  const qU=qibla%180;
  const d1=angDiff180(dir1,qU),d2=angDiff180(dir2,qU);
  return{angle:d1<=d2?dir1:dir2,diff:Math.min(d1,d2)};
}

function angDiff180(a,b){ const d=Math.abs(((a-b)%180+180)%180); return Math.min(d,180-d); }

function computeGeometryComplexity(polyCoords) {
  if (!Array.isArray(polyCoords) || polyCoords.length < 4) return 0;
  const pts = polyCoords;
  const edges = [];
  for (let i = 0; i < pts.length - 1; i++) {
    const a = pts[i], b = pts[i+1];
    const dx = (b[1]-a[1]) * Math.cos(toRad((a[0]+b[0])/2)) * 111320;
    const dy = (b[0]-a[0]) * 111320;
    const len = Math.sqrt(dx*dx + dy*dy);
    if (len < 0.7) continue;
    const ang = (toDeg(Math.atan2(dx,dy)) + 360) % 180;
    edges.push({len, ang});
  }
  if (edges.length < 3) return 0;
  const total = edges.reduce((s,e) => s + e.len, 0) || 1;
  const bins = new Array(18).fill(0);
  edges.forEach(e => { bins[Math.floor(e.ang / 10) % 18] += e.len; });
  const entropy = -bins.reduce((s,v) => {
    if (!v) return s;
    const p = v / total;
    return s + p * Math.log2(p);
  }, 0) / Math.log2(18);
  const vertexPenalty = Math.min(1, Math.max(0, (pts.length - 6) / 18));
  return Math.max(0, Math.min(1, entropy * 0.72 + vertexPenalty * 0.28));
}

function destination(lat,lng,bearing,distM){
  const R=6371000,d=distM/R,t=toRad(bearing),p1=toRad(lat),l1=toRad(lng);
  const sp2=Math.sin(p1)*Math.cos(d)+Math.cos(p1)*Math.sin(d)*Math.cos(t);
  const p2=Math.asin(sp2);
  return{lat:toDeg(p2),lng:toDeg(l1+Math.atan2(Math.sin(t)*Math.sin(d)*Math.cos(p1),Math.cos(d)-Math.sin(p1)*sp2))};
}

function closestDirection(axisDeg,targetBearing){
  const d1=axisDeg,d2=(axisDeg+180)%360;
  const a1=Math.min(Math.abs(((d1-targetBearing)+360)%360),Math.abs(((d1-targetBearing)-360)%360));
  const a2=Math.min(Math.abs(((d2-targetBearing)+360)%360),Math.abs(((d2-targetBearing)-360)%360));
  return a1<=a2?d1:d2;
}

function isArabicText(s) {
  return /[\u0600-\u06FF]/.test(String(s || ''));
}

function uniqNonEmpty(vals) {
  const out = [];
  const seen = new Set();
  for (const v of vals || []) {
    const t = String(v || '').trim();
    if (!t) continue;
    const k = trLower(t);
    if (seen.has(k)) continue;
    seen.add(k);
    out.push(t);
  }
  return out;
}

function pickLocalizedMosqueNames(m, tags = {}) {
  const trCands = uniqNonEmpty([m?.nameTr, tags['name:tr'], tags['official_name:tr'], tags['alt_name:tr']]);
  const enCands = uniqNonEmpty([tags['name:en'], tags['official_name:en'], tags['alt_name:en']]);
  const arCands = uniqNonEmpty([m?.nameAr, tags['name:ar']]);
  const generic = uniqNonEmpty([m?.name, tags.name, tags.official_name, tags.int_name, tags.alt_name]);
  const latinGeneric = generic.filter(x => !isArabicText(x));

  const primaryPool = currentLang === 'en'
    ? [...enCands, ...latinGeneric, ...trCands, ...generic, ...arCands]
    : [...trCands, ...latinGeneric, ...enCands, ...generic, ...arCands];
  const primary = primaryPool[0] || m?.name || `OSM Cami #${m?.id ?? '?'}`;

  const arName = arCands.find(x => trLower(x) !== trLower(primary)) || '';
  return { primary, arName };
}

// ══════════════════════════════════════════════════════════════
//  UI
// ══════════════════════════════════════════════════════════════
function makePopup(m){
  const tags = m.tags || {};
  const names = pickLocalizedMosqueNames(m, tags);
  const s=m.status==='correct'?'<span style="color:#4ade80"> Doğru yön</span>':
          m.status==='wrong'?'<span style="color:#f87171"> Sapma var</span>':
          '<span style="color:#fbbf24"> Veri yok</span>';
  const meth=
    m.method==='edge-analysis'?'Kenar analizi':
    m.method==='osm-tag'?'OSM etiketi':
    m.method==='hybrid-interior'?'Hibrit (iç mekan+bina)':
    m.method==='interior-only'?'İç mekan kanıtı':
    m.method==='fused'?'Birleşik':
    '—';
  const dist=greatCircleKm(m.lat,m.lng,KAABA.lat,KAABA.lng).toFixed(0);
  // Store mosque in global registry so popup button can find it by id
  window._popupRegistry = window._popupRegistry || {};
  window._popupRegistry[m.id] = m;
  return`<div class="p-name">${escHtml(names.primary)}</div>
    <div class="p-row"><span class="p-k">Durum</span><span class="p-v">${s}</span></div>
    <div class="p-row"><span class="p-k">Güven</span><span class="p-v">${m.confidence ?? '—'}/100</span></div>
    <div class="p-row"><span class="p-k">Kıble açısı</span><span class="p-v">${m.qibla.toFixed(1)}°</span></div>
    ${m.axis!==null?`<div class="p-row"><span class="p-k">Bina yönü</span><span class="p-v">${m.axis.toFixed(1)}°</span></div>`:''}
    <div class="p-row"><span class="p-k">Sapma</span><span class="p-v">${m.diff!==null?m.diff.toFixed(1)+'°':'—'}</span></div>
    ${m.convertedFrom?.converted?`<div class="p-row"><span class="p-k">Yapı geçmişi</span><span class="p-v" style="color:#fbbf24">Dönüştürülmüş olabilir</span></div>`:''}
    <div class="p-row"><span class="p-k">Kabe mesafesi</span><span class="p-v">${dist} km</span></div>
    <div class="p-method">Yöntem: ${meth}</div>
    <button class="p-anim-btn" onclick="animateFromPopup(${m.id})"> Büyük Daire Animasyonu</button>`;
}

// Store last clicked for popup button
let _lastClickedMosque = null;

// Called by popup button — looks up mosque by id from registry or mosqueDB
function animateFromPopup(id) {
  // OSM ids are numbers; try both numeric and string lookup
  const numId = typeof id === 'string' ? parseInt(id) : id;
  const m = mosqueDB.get(numId) || mosqueDB.get(String(numId))
         || [...mosqueDB.values()].find(x => x.id == id);
  if (!m) { console.warn('animateFromPopup: mosque not found', id); return; }
  map.closePopup();
  // Small delay to let popup close before animating
  setTimeout(() => handleMosqueClick(m), 80);
}

function popMarkerForMosque(m) {
  if (!m || !Array.isArray(renderLayers)) return;
  for (const layer of renderLayers) {
    if (!layer || !layer.mosque || layer.mosque.id !== m.id) continue;
    if (typeof layer.setRadius === 'function') {
      try {
        layer.setRadius(7);
        setTimeout(() => { try { layer.setRadius(5); } catch {} }, 180);
      } catch {}
    }
    if (layer._path && layer._path.classList) {
      try {
        layer._path.classList.remove('marker-pop');
        void layer._path.offsetWidth;
        layer._path.classList.add('marker-pop');
      } catch {}
    }
    break;
  }
}

function getMarkerLayerByMosqueId(id) {
  for (const layer of renderLayers) {
    if (!layer || !layer.mosque || String(layer.mosque.id) !== String(id)) continue;
    if (typeof layer.setRadius === 'function') return layer;
  }
  return null;
}

function setMarkerHoverForMosque(m, active = true) {
  if (!m) return;
  const layer = getMarkerLayerByMosqueId(m.id);
  if (!layer) return;
  try {
    layer.setRadius(active ? 8 : 5);
  } catch {}
  if (layer._path?.classList) {
    if (active) layer._path.classList.add('marker-hover');
    else layer._path.classList.remove('marker-hover');
  }
}

function handleMosqueClick(m) {
  window._lastClickedMosque = m;
  document.querySelectorAll('.m-item').forEach(el=>el.classList.remove('active'));
  const el=document.getElementById('mi-'+m.id);
  if(el){el.classList.add('active');el.scrollIntoView({block:'nearest',behavior:'smooth'});}
  if (m.status === 'wrong') haptic(20);
  popMarkerForMosque(m);
  pulseMosqueFocus(m);
  ensureSelectedMosqueVisibleOnMobile(m, { animate:true });
  animateQibla(m);
  openDetailPanel(m);
  hydrateMosqueDetailOnDemand(m);
}

function animateCounter(el, target) {
  const start = parseInt(el.textContent) || 0;
  if (start === target) return;
  const dur = 400, step = 16;
  const steps = dur / step;
  let cur = 0;
  el.classList.add('updated');
  setTimeout(()=>el.classList.remove('updated'), 400);
  const id = setInterval(() => {
    cur++;
    el.textContent = Math.round(start + (target - start) * (cur/steps));
    if (cur >= steps) { el.textContent = target; clearInterval(id); }
  }, step);
}

function updateStats(){
  const vis = getVisibleMosques(0.1);
  if (vis.length) {
    animateCounter(document.getElementById('s-total'), vis.length);
    animateCounter(document.getElementById('s-ok'),    vis.filter(m=>m.status==='correct').length);
    animateCounter(document.getElementById('s-bad'),   vis.filter(m=>m.status==='wrong').length);
    animateCounter(document.getElementById('s-unk'),   vis.filter(m=>m.status==='unknown').length);
  } else {
    ['s-total','s-ok','s-bad','s-unk'].forEach(id=>document.getElementById(id).textContent='—');
  }
  updateSidebarSnapPanels();
}

function getLoadedStats() {
  const all = [...mosqueDB.values()];
  const withData = all.filter(m => m.diff !== null);
  const ok = withData.filter(m => m.diff <= tol);
  const pct = withData.length ? Math.round((ok.length / withData.length) * 100) : null;
  const avg = withData.length ? withData.reduce((s,m)=>s+m.diff,0)/withData.length : null;
  const max = withData.length ? Math.max(...withData.map(m=>m.diff)) : null;
  return { total: all.length, withData: withData.length, pct, avg, max };
}

function drawSidebarRadar(stats) {
  const cv = document.getElementById('sb-radar');
  if (!cv) return;
  const ctx = cv.getContext('2d');
  const W = cv.width, H = cv.height, cx = W/2, cy = H/2, r = 42;
  ctx.clearRect(0,0,W,H);
  for (let ring=1; ring<=3; ring++) {
    ctx.beginPath();
    for (let i=0; i<3; i++) {
      const a = (i/3)*Math.PI*2 - Math.PI/2;
      const x = cx + Math.cos(a)*r*(ring/3);
      const y = cy + Math.sin(a)*r*(ring/3);
      i===0 ? ctx.moveTo(x,y) : ctx.lineTo(x,y);
    }
    ctx.closePath();
    ctx.strokeStyle = '#6a9ec9';
    ctx.lineWidth = 1;
    ctx.stroke();
  }
  const acc = (stats.pct ?? 0) / 100;
  const cov = stats.total ? (stats.withData / stats.total) : 0;
  const dev = stats.avg != null ? Math.max(0, Math.min(1, (90 - stats.avg) / 90)) : 0;
  const vals = [acc, cov, dev];
  ctx.beginPath();
  for (let i=0; i<3; i++) {
    const a = (i/3)*Math.PI*2 - Math.PI/2;
    const x = cx + Math.cos(a)*r*vals[i];
    const y = cy + Math.sin(a)*r*vals[i];
    i===0 ? ctx.moveTo(x,y) : ctx.lineTo(x,y);
  }
  ctx.closePath();
  ctx.fillStyle = 'rgba(201,168,76,.18)';
  ctx.fill();
  ctx.strokeStyle = '#c9a84c';
  ctx.lineWidth = 2;
  ctx.stroke();
}

function updateSidebarSnapPanels() {
  if (window.innerWidth > 768) return;
  const stats = getLoadedStats();
  const city = currentCity || '—';
  const selected = window._lastClickedMosque || null;
  const miniCity = document.getElementById('sb-mini-city');
  const miniScore = document.getElementById('sb-mini-score');
  const miniSub = document.getElementById('sb-mini-sub');
  if (selected) {
    if (miniCity) miniCity.textContent = selected.name || city;
    if (miniScore) miniScore.textContent = selected.diff != null ? `${selected.diff.toFixed(1)}°` : (stats.pct != null ? `${stats.pct}%` : '—');
    if (miniSub) {
      const state =
        selected.status === 'correct' ? 'Doğru yön' :
        selected.status === 'wrong' ? 'Sapma var' : 'Veri yok';
      miniSub.textContent = `${state} · Kıble ${selected.qibla.toFixed(1)}°`;
    }
  } else {
    if (miniCity) miniCity.textContent = city;
    if (miniScore) miniScore.textContent = stats.pct != null ? `${stats.pct}%` : '—';
    if (miniSub) miniSub.textContent = stats.total ? `${stats.total} cami · tolerans ${tol}°` : 'Veri bekleniyor';
  }
  const st = (id,v) => { const el=document.getElementById(id); if (el) el.textContent = v; };
  st('sb-m-total', stats.total ? stats.total.toLocaleString() : '—');
  st('sb-m-pct', stats.pct != null ? `${stats.pct}%` : '—');
  st('sb-m-avg', stats.avg != null ? `${stats.avg.toFixed(1)}°` : '—');
  st('sb-m-max', stats.max != null ? `${stats.max.toFixed(1)}°` : '—');
  drawSidebarRadar(stats);
}

function rankVisibleMosquesByQuery(list, q) {
  const qLow = trLower(q || '');
  const qNorm = normalize(qLow);
  const words = qLow.split(/\s+/).filter(w => w.length > 0);
  return [...(list || [])]
    .map(m => {
      const s = msMosqueScore(m, qLow, qNorm, words);
      const p = computeMosquePopularityScore(m);
      const d = computeMosqueProximityScore(m);
      return { m, rank: s + p + d, s, p, d };
    })
    .filter(x => x.s > 0)
    .sort((a,b) => b.rank - a.rank || b.p - a.p || b.s - a.s)
    .map(x => x.m);
}

function getNearestSuggestionMosques(limit = 3) {
  if (!mosqueDB.size) return [];
  const center = map?.getCenter?.();
  const refLat = Number.isFinite(center?.lat) ? center.lat : (Number.isFinite(userGeoState.lat) ? userGeoState.lat : null);
  const refLng = Number.isFinite(center?.lng) ? center.lng : (Number.isFinite(userGeoState.lng) ? userGeoState.lng : null);
  if (!Number.isFinite(refLat) || !Number.isFinite(refLng)) return [];
  return [...mosqueDB.values()]
    .map(m => ({ m, d: greatCircleM(refLat, refLng, m.lat, m.lng) }))
    .sort((a,b) => a.d - b.d)
    .slice(0, Math.max(1, limit))
    .map(x => x.m);
}

function focusSuggestedMosque(id) {
  const m = mosqueDB.get(id) || mosqueDB.get(Number(id)) || [...mosqueDB.values()].find(x => String(x.id) === String(id));
  if (!m) return;
  focusMapLatLng(m.lat, m.lng, Math.max(map?.getZoom?.() || 15, 16), { duration:0.58 });
  setTimeout(() => handleMosqueClick(m), 120);
}

window.focusSuggestedMosque = focusSuggestedMosque;

function renderEmptyMosqueState(el) {
  const nearby = getNearestSuggestionMosques(3);
  if (!nearby.length) {
    el.innerHTML = '<div class="empty"><div class="empty-icon"></div><div>Cami bulunamadı</div></div>';
    return;
  }
  const c = map?.getCenter?.() || { lat:nearby[0].lat, lng:nearby[0].lng };
  const list = nearby.map(m => {
    const km = (greatCircleM(c.lat, c.lng, m.lat, m.lng) / 1000).toFixed(1);
    return `<button class="empty-suggest-item" onclick="focusSuggestedMosque('${String(m.id).replace(/'/g, '&#39;')}')">
      <span class="empty-suggest-name">${escHtml(m.name)}</span>
      <span class="empty-suggest-meta">${escHtml(getMosqueHierarchyLine(m))} · ~${km} km</span>
    </button>`;
  }).join('');
  el.innerHTML = `<div class="empty empty-rich">
    <div class="empty-icon"></div>
    <div class="empty-title">Bu alanda cami bulunamadı</div>
    <div class="empty-sub">Yakındaki camiler:</div>
    <div class="empty-suggest-list">${list}</div>
  </div>`;
}

function updateList(visible){
  const el=document.getElementById('mosque-list');
  if(!visible.length){renderEmptyMosqueState(el);document.getElementById('sb-count').textContent='';return;}
  document.getElementById('sb-count').textContent=visible.length;
  const hasQuery = !!(mosqueFilter && mosqueFilter.trim().length > 1);
  const sorted = hasQuery
    ? rankVisibleMosquesByQuery(visible, mosqueFilter)
    : [...visible].sort((a,b)=>({wrong:0,unknown:1,correct:2}[a.status]-{wrong:0,unknown:1,correct:2}[b.status]));
  const frag=document.createDocumentFragment();
  if (hasQuery) {
    const grouped = new Map();
    for (const m of sorted) {
      const key = getSearchProvinceLabel(m);
      if (!grouped.has(key)) grouped.set(key, []);
      grouped.get(key).push(m);
    }
    [...grouped.entries()]
      .sort((a,b) => b[1].length - a[1].length || a[0].localeCompare(b[0], 'tr'))
      .forEach(([province, items]) => {
        const hdr = document.createElement('div');
        hdr.className = 'm-group-hdr';
        hdr.textContent = `${province} (${items.length})`;
        frag.appendChild(hdr);
        items.forEach((m,i) => {
          const col=m.status==='correct'?'#4ade80':m.status==='wrong'?'#f87171':'#fbbf24';
          const div=document.createElement('div');
          div.className='m-item';div.id='mi-'+m.id;
          div.style.animationDelay = Math.min(i*18, 300)+'ms';
          const convMark = m.convertedFrom?.converted ? ' →' : '';
          div.innerHTML=`<div class="m-dot" style="background:${col};box-shadow:0 0 4px ${col}"></div>
            <div class="m-info"><div class="m-name">${escHtml(m.name)}${convMark}</div>
            <div class="m-sub">${escHtml(getMosqueHierarchyLine(m))}</div></div>
            <div class="m-diff" style="color:${col}">${m.diff!==null?m.diff.toFixed(1)+'°':'—'}</div>`;
          div.onclick=()=>handleMosqueClick(m);
          div.onmouseenter=()=>setMarkerHoverForMosque(m,true);
          div.onmouseleave=()=>setMarkerHoverForMosque(m,false);
          div.onfocus=()=>setMarkerHoverForMosque(m,true);
          div.onblur=()=>setMarkerHoverForMosque(m,false);
          frag.appendChild(div);
        });
      });
  } else {
    sorted.forEach((m,i)=>{
      const col=m.status==='correct'?'#4ade80':m.status==='wrong'?'#f87171':'#fbbf24';
      const div=document.createElement('div');
      div.className='m-item';div.id='mi-'+m.id;
      div.style.animationDelay = Math.min(i*18, 300)+'ms';
      const convMark = m.convertedFrom?.converted ? ' →' : '';
      div.innerHTML=`<div class="m-dot" style="background:${col};box-shadow:0 0 4px ${col}"></div>
        <div class="m-info"><div class="m-name">${escHtml(m.name)}${convMark}</div>
        <div class="m-sub">Kıble:${m.qibla.toFixed(1)}°${m.axis!==null?' | Bina:'+m.axis.toFixed(1)+'°':''}</div></div>
        <div class="m-diff" style="color:${col}">${m.diff!==null?m.diff.toFixed(1)+'°':'—'}</div>`;
      div.onclick=()=>handleMosqueClick(m);
      div.onmouseenter=()=>setMarkerHoverForMosque(m,true);
      div.onmouseleave=()=>setMarkerHoverForMosque(m,false);
      div.onfocus=()=>setMarkerHoverForMosque(m,true);
      div.onblur=()=>setMarkerHoverForMosque(m,false);
      frag.appendChild(div);
    });
  }
  el.innerHTML='';el.appendChild(frag);
}

function recompute(){
  if(!mosqueDB.size) return;
  mosqueDB.forEach(m=>applyAxisFusion(m));
  renderAll();
  if(heatVisible) refreshHeatmap();
  if(scoreCardVisible) updateScoreCard();
  // Re-render comparison with updated tolerance
  const overlay = document.getElementById('cmp-overlay');
  if(overlay && overlay.classList.contains('show')) renderCompare();
  // History: reset period cache so next enrichWithPeriod re-runs (tol change affects correct/wrong)
  if(typeof historyModeActive !== 'undefined' && historyModeActive) {
    renderHistoryModal();
  }
}

// ══════════════════════════════════════════════════════════════
//  HEATMAP (Adım 2)
// ══════════════════════════════════════════════════════════════
async function loadLeafletHeat() {
  if(window.L && L.heatLayer) return; // already loaded
  return new Promise((res,rej)=>{
    const s=document.createElement('script');
    s.src='https://unpkg.com/leaflet.heat@0.2.0/dist/leaflet-heat.js';
    s.onload=res; s.onerror=rej;
    document.head.appendChild(s);
  });
}

async function toggleHeatmap() {
  const btn = document.getElementById('btn-heat');
  if(heatVisible){
    // Turn off
    if(heatLayer){ try{map.removeLayer(heatLayer);}catch{} heatLayer=null; }
    heatVisible=false;
    btn.classList.remove('active');
    return;
  }
  // Turn on
  try {
    await loadLeafletHeat();
  } catch {
    toast('Isı haritası yüklenemedi',4000); return;
  }
  heatVisible=true;
  btn.classList.add('active');
  refreshHeatmap();
}

function refreshHeatmap(){
  if(!heatVisible || !window.L || !L.heatLayer) return;
  if(heatLayer){ try{map.removeLayer(heatLayer);}catch{} heatLayer=null; }

  const bounds = map.getBounds().pad(0.15);
  const points = [];

  [...mosqueDB.values()]
    .filter(m=>bounds.contains([m.lat,m.lng]) && m.diff!==null)
    .forEach(m=>{
      // Intensity: normalize diff to 0-1 range (0°=cool, 90°=hot)
      // We want to show WHERE sapma is concentrated — high diff = hot
      const intensity = Math.min(m.diff / 45, 1.0);
      points.push([m.lat, m.lng, intensity]);
    });

  if(!points.length) return;

  heatLayer = L.heatLayer(points, {
    radius: 35,
    blur: 25,
    maxZoom: 17,
    max: 1.0,
    gradient: {
      0.0: '#1a3a2a',   // very dark green (perfect)
      0.2: '#4ade80',   // green (good)
      0.4: '#fbbf24',   // amber (marginal)
      0.7: '#f87171',   // red (bad)
      1.0: '#dc2626'    // deep red (very bad)
    }
  }).addTo(map);
  heatLayer.bringToFront();
}

// Auto-refresh heatmap when map moves
// (wired into loadViewport → renderAll)

// ══════════════════════════════════════════════════════════════
//  SCORE CARD (Adım 2)
// ══════════════════════════════════════════════════════════════
function toggleScoreCard() {
  scoreCardVisible = !scoreCardVisible;
  const card = document.getElementById('score-card');
  const btn = document.getElementById('btn-score');
  card.classList.toggle('show', scoreCardVisible);
  btn.classList.toggle('active', scoreCardVisible);
  if(scoreCardVisible) updateScoreCard();
}

function updateScoreCard(){
  const bounds = map.getBounds().pad(0.1);
  const visible = [...mosqueDB.values()].filter(m=>bounds.contains([m.lat,m.lng]));
  const withData = visible.filter(m=>m.diff!==null);
  const correct = visible.filter(m=>m.status==='correct');
  const wrong   = visible.filter(m=>m.status==='wrong');
  const unknown = visible.filter(m=>m.status==='unknown');

  const total = withData.length;
  const pct = total > 0 ? Math.round((correct.length / total) * 100) : null;

  // City name
  document.getElementById('sc-city').textContent = currentCity;
  document.getElementById('sc-tol-val').textContent = tol+'°';

  // Percentage
  document.getElementById('sc-pct').textContent = pct !== null ? pct+'%' : '—';

  // Grade
  const gradeEl = document.getElementById('sc-grade');
  let grade='—', gradeClass='';
  if(pct!==null){
    if(pct>=85){grade='A — Mükemmel';gradeClass='A';}
    else if(pct>=65){grade='B — İyi';gradeClass='B';}
    else if(pct>=45){grade='C — Orta';gradeClass='C';}
    else{grade='D — Zayıf';gradeClass='D';}
  }
  gradeEl.textContent=grade;
  gradeEl.className='sc-grade'+(gradeClass?' '+gradeClass:'');

  // Stats
  document.getElementById('sc-ok').textContent  = correct.length;
  document.getElementById('sc-bad').textContent = wrong.length;
  document.getElementById('sc-unk').textContent = unknown.length;

  if(withData.length){
    const diffs = withData.map(m=>m.diff);
    const avg = diffs.reduce((a,b)=>a+b,0)/diffs.length;
    const maxD = Math.max(...diffs);
    const minD = Math.min(...diffs);
    document.getElementById('sc-avg').textContent = avg.toFixed(1)+'°';
    document.getElementById('sc-max').textContent = maxD.toFixed(1)+'°';
    document.getElementById('sc-min').textContent = minD.toFixed(1)+'°';

    // Best (smallest diff) and worst (largest diff) with data
    const sorted = [...withData].sort((a,b)=>a.diff-b.diff);
    document.getElementById('sc-best').textContent  = sorted[0].name+' ('+sorted[0].diff.toFixed(1)+'°)';
    document.getElementById('sc-worst').textContent = sorted[sorted.length-1].name+' ('+sorted[sorted.length-1].diff.toFixed(1)+'°)';
  } else {
    ['sc-avg','sc-max','sc-min','sc-best','sc-worst'].forEach(id=>document.getElementById(id).textContent='—');
  }

  // Donut chart (canvas)
  drawDonut(correct.length, wrong.length, unknown.length, pct);
}

function drawDonut(ok, bad, unk, pct){
  const canvas = document.getElementById('sc-donut');
  const ctx = canvas.getContext('2d');
  const cx=55, cy=55, r=44, inner=30;
  ctx.clearRect(0,0,110,110);

  const total = ok+bad+unk;
  if(!total){ 
    ctx.beginPath(); ctx.arc(cx,cy,r,0,Math.PI*2); 
    ctx.strokeStyle='#6a9ec9'; ctx.lineWidth=14; ctx.stroke(); 
    return; 
  }

  const slices = [
    { val:ok,  color:'#4ade80' },
    { val:bad, color:'#f87171' },
    { val:unk, color:'#fbbf24' }
  ].filter(s=>s.val>0);

  let angle = -Math.PI/2;
  for(const s of slices){
    const sweep = (s.val/total) * Math.PI*2;
    ctx.beginPath();
    ctx.moveTo(cx,cy);
    ctx.arc(cx,cy,r,angle,angle+sweep);
    ctx.closePath();
    ctx.fillStyle = s.color+'33'; // very subtle fill
    ctx.fill();
    // Arc stroke (thick ring)
    ctx.beginPath();
    ctx.arc(cx,cy,r-7, angle, angle+sweep);
    ctx.strokeStyle = s.color;
    ctx.lineWidth = 13;
    ctx.lineCap = 'butt';
    ctx.stroke();
    angle += sweep;
  }

  // Gap lines between slices
  ctx.strokeStyle='#164773';
  ctx.lineWidth=2;
  angle=-Math.PI/2;
  for(const s of slices){
    const sweep=(s.val/total)*Math.PI*2;
    ctx.beginPath();
    ctx.moveTo(cx+Math.cos(angle)*(r-14), cy+Math.sin(angle)*(r-14));
    ctx.lineTo(cx+Math.cos(angle)*r, cy+Math.sin(angle)*r);
    ctx.stroke();
    angle+=sweep;
  }
}

// ══════════════════════════════════════════════════════════════
//  MOSQUE SEARCH
// ══════════════════════════════════════════════════════════════
let mosqueFilter = '';        // active filter query
let msDropdownIdx = -1;       // keyboard navigation index
let cityDropdownIdx = -1;
let citySuggestController = null;
let citySuggestSeq = 0;
let msGeoProbePending = false;
let msGeoProbeAt = 0;
let msScopeViewportOnly = true;
let msRemoteLookupPending = false;
let msRemoteLookupKey = '';
const msRemoteLookupMissAt = new Map();
const LANDMARK_ALIAS_GROUPS = [
  { key:'sultanahmet', aliases:['sultanahmet camii','sultan ahmet camii','sultan ahmed mosque','blue mosque','the blue mosque','sultanahmet mosque'] },
  { key:'ayasofya', aliases:['ayasofya','ayasofya camii','hagia sophia','aya sofya'] },
  { key:'fatih', aliases:['fatih camii','fatih mosque','fatih mosque istanbul'] },
  { key:'suleymaniye', aliases:['suleymaniye camii','süleymaniye camii','suleymaniye mosque'] },
  { key:'eyup_sultan', aliases:['eyup sultan camii','eyüp sultan camii','eyup sultan mosque'] },
  { key:'selimiye_edirne', aliases:['selimiye camii edirne','selimiye mosque edirne','edirne selimiye'] },
  { key:'ulu_cami_bursa', aliases:['bursa ulu camii','ulu cami bursa','grand mosque of bursa'] },
  { key:'kocatepe', aliases:['kocatepe camii','kocatepe mosque'] },
  { key:'camlica', aliases:['camlica camii','çamlıca camii','buyuk camlica camii','büyük çamlıca camii'] },
  { key:'nabawi', aliases:['mescid-i nebevi','masjid an nabawi','al-masjid an-nabawi','prophets mosque','prophet mosque medina'] },
  { key:'aqsa', aliases:['mescid-i aksa','masjid al aqsa','al-aqsa mosque','aqsa mosque'] },
  { key:'hassan_ii', aliases:['hassan ii mosque','hassan 2 mosque','cami hassan ii'] },
  { key:'sheikh_zayed', aliases:['sheikh zayed grand mosque','sheikh zayed mosque','zayed grand mosque'] },
  { key:'badshahi', aliases:['badshahi mosque','badshahi masjid'] },
  { key:'faisal_islamabad', aliases:['faisal mosque','faisal masjid islamabad'] },
  { key:'istiqlal_jakarta', aliases:['istiqlal mosque','masjid istiqlal'] },
  { key:'putra', aliases:['putra mosque','masjid putra'] },
  { key:'national_malaysia', aliases:['national mosque malaysia','masjid negara'] },
  { key:'baiturrahman', aliases:['baiturrahman grand mosque','masjid raya baiturrahman'] },
  { key:'blue_mosque_yerevan', aliases:['blue mosque yerevan','gok jami yerevan','gök cami yerevan'] }
];
const LANDMARK_ALIAS_COMPILED = LANDMARK_ALIAS_GROUPS.map(g => ({
  key: g.key,
  aliasesNorm: [...new Set((g.aliases || []).map(a => normalize(trLower(a))).filter(Boolean))]
}));
const msRemoteMetaByRef = new Map();
const PLACE_SUGGEST_CACHE = new Map();

function uniqueNameList(arr) {
  const out = [];
  const seen = new Set();
  for (const raw of arr || []) {
    const v = String(raw || '').trim();
    if (!v) continue;
    const key = trLower(v);
    if (seen.has(key)) continue;
    seen.add(key);
    out.push(v);
  }
  return out;
}

function findAliasGroupsForQuery(qNorm) {
  if (!qNorm) return [];
  const out = new Set();
  for (const g of LANDMARK_ALIAS_COMPILED) {
    for (const a of g.aliasesNorm) {
      if (a === qNorm || a.startsWith(qNorm) || qNorm.startsWith(a) || a.includes(` ${qNorm}`) || qNorm.includes(` ${a}`)) {
        out.add(g.key);
        break;
      }
    }
  }
  return [...out];
}

function gatherMosqueNameVariants(m) {
  const tags = m?.tags || {};
  const wikipediaTitle = (typeof tags.wikipedia === 'string' && tags.wikipedia.includes(':'))
    ? tags.wikipedia.split(':').slice(1).join(':').replace(/_/g, ' ').trim()
    : '';
  const wdLabel = tags.wikidata ? wikidataLabelCache.get(String(tags.wikidata).toUpperCase()) : null;
  return uniqueNameList([
    m?.name, m?.nameTr, m?.nameAr,
    tags['name'], tags['name:tr'], tags['name:en'], tags['name:ar'],
    tags['official_name'], tags['short_name'], tags['alt_name'], tags['old_name'],
    tags['loc_name'], tags['int_name'], tags['operator'], wikipediaTitle, wdLabel
  ]);
}

function buildSearchIndexForMosque(m) {
  if (!m) return;
  const variants = gatherMosqueNameVariants(m);
  const namesLow = variants.map(v => trLower(v));
  const namesNorm = namesLow.map(v => normalize(v));
  const tokenSet = new Set();
  for (const n of namesLow) {
    const toks = n.split(/[^a-z0-9ığüşöçâêîû]+/i).filter(t => t.length > 1);
    for (const t of toks) {
      tokenSet.add(t);
      tokenSet.add(normalize(t));
    }
  }
  const aliasGroups = [];
  for (const g of LANDMARK_ALIAS_COMPILED) {
    const hit = g.aliasesNorm.some(alias =>
      namesNorm.some(n => n === alias || n.includes(alias) || (n.length >= 8 && alias.includes(n)))
    );
    if (hit) aliasGroups.push(g.key);
  }
  m.searchIndex = {
    variants,
    namesLow,
    namesNorm,
    tokens: [...tokenSet],
    aliasGroups
  };
}

function initMosqueSearch() {
  const input    = document.getElementById('mosque-search');
  const dropdown = document.getElementById('ms-dropdown');
  const clearBtn = document.getElementById('ms-clear');
  const scopeChk = document.getElementById('ms-scope-only');

  let debounceTimer = null;

  input.addEventListener('input', () => {
    const q = input.value; // don't trim yet — let user type spaces
    clearBtn.classList.toggle('show', q.length > 0);
    input.classList.toggle('has-value', q.length > 0);
    msDropdownIdx = -1;

    clearTimeout(debounceTimer);

    if (!q.trim()) {
      dropdown.classList.remove('show');
      if (mosqueFilter) { mosqueFilter = ''; applyMosqueFilter(''); }
      return;
    }

    // Debounce 80ms so rapid typing doesn't stutter
    debounceTimer = setTimeout(() => showMosqueDropdown(q.trim()), 80);
  });

  input.addEventListener('keydown', e => {
    if (e.key === 'ArrowDown' || e.key === 'ArrowUp') {
      e.preventDefault();
      e.stopPropagation();
      const items = dropdown.querySelectorAll('.ms-item');
      if (!items.length) return;
      if (e.key === 'ArrowDown') msDropdownIdx = Math.min(msDropdownIdx + 1, items.length - 1);
      else                        msDropdownIdx = Math.max(msDropdownIdx - 1, 0);
      items.forEach((el,i) => el.classList.toggle('focused', i === msDropdownIdx));
      if (items[msDropdownIdx]) items[msDropdownIdx].scrollIntoView({block:'nearest'});
    } else if (e.key === 'Enter') {
      e.preventDefault();
      e.stopPropagation();
      const items = dropdown.querySelectorAll('.ms-item');
      if (msDropdownIdx >= 0 && items[msDropdownIdx]) {
        items[msDropdownIdx].click();
      } else if (input.value.trim()) {
        applyMosqueFilter(input.value.trim());
        dropdown.classList.remove('show');
      }
    } else if (e.key === 'Escape') {
      e.stopPropagation();
      dropdown.classList.remove('show');
      input.blur();
    } else if (e.key === '/') {
      // Don't let global '/' shortcut steal focus when already in mosque-search
      e.stopPropagation();
    }
  });

  document.addEventListener('click', e => {
    if (!e.target.closest('#ms-wrap')) dropdown.classList.remove('show');
  });

  scopeChk?.addEventListener('change', () => {
    msScopeViewportOnly = !!scopeChk.checked;
    const q = input.value.trim();
    if (q) showMosqueDropdown(q);
    const cq = document.getElementById('city-input')?.value?.trim();
    if (cq) showCitySmartDropdown(cq);
  });
}

function initTopSmartSearch() {
  const input = document.getElementById('city-input');
  const dd = document.getElementById('city-smart-dd');
  if (!input || !dd) return;
  let t = null;
  input.addEventListener('input', () => {
    const q = input.value.trim();
    cityDropdownIdx = -1;
    clearTimeout(t);
    if (!q) { showCityFocusDropdown(); return; }
    t = setTimeout(() => showCitySmartDropdown(q), 300);
  });
  input.addEventListener('focus', () => {
    const q = input.value.trim();
    if (!q) showCityFocusDropdown();
  });
  input.addEventListener('keydown', e => {
    if (!dd.classList.contains('show')) return;
    const items = dd.querySelectorAll('.ms-item');
    if (!items.length) return;
    if (e.key === 'ArrowDown' || e.key === 'ArrowUp') {
      e.preventDefault();
      if (e.key === 'ArrowDown') cityDropdownIdx = Math.min(cityDropdownIdx + 1, items.length - 1);
      else cityDropdownIdx = Math.max(cityDropdownIdx - 1, 0);
      items.forEach((el,i) => el.classList.toggle('focused', i === cityDropdownIdx));
      items[cityDropdownIdx]?.scrollIntoView({ block:'nearest' });
    } else if (e.key === 'Escape') {
      closeCitySmartDropdown();
    } else if (e.key === 'Enter') {
      const q = input.value.trim();
      if (!q) {
        e.preventDefault();
        if (cityDropdownIdx < 0) items[0]?.click();
        else items[cityDropdownIdx]?.click();
        return;
      }
      if (isLikelyMosqueQuery(q)) {
        e.preventDefault();
        cityDropdownIdx = -1;
        closeCitySmartDropdown();
        doSearch();
        return;
      }
      if (cityDropdownIdx < 0 && items.length === 1) {
        e.preventDefault();
        items[0]?.click();
        return;
      }
      if (cityDropdownIdx < 0) {
        const best = pickBestCitySuggestionFromDropdown(q);
        if (best) {
          e.preventDefault();
          best.click();
          return;
        }
      }
      if (cityDropdownIdx >= 0) {
        e.preventDefault();
        items[cityDropdownIdx]?.click();
      }
    }
  });
  document.addEventListener('click', e => {
    if (!e.target.closest('.search-box')) closeCitySmartDropdown();
  });
}

function findMosqueByRef(osmType, osmId) {
  const t = normalizeOsmType(osmType);
  const id = String(osmId || '').replace(/\D/g,'');
  if (!id) return null;
  for (const m of mosqueDB.values()) {
    const mt = normalizeOsmType(m.osmType || 'way');
    if (mt === t && String(m.id) === id) return m;
  }
  return null;
}

function isElementVisibleOnLayout(el) {
  if (!el) return false;
  const cs = getComputedStyle(el);
  if (cs.display === 'none' || cs.visibility === 'hidden') return false;
  const r = el.getBoundingClientRect();
  return r.width > 0 && r.height > 0;
}

function getMapFocusPadding(extra = {}) {
  const pad = { top: 16, right: 16, bottom: 16, left: 16 };
  if (!map) return { ...pad, ...extra };

  const header = document.querySelector('header');
  if (isElementVisibleOnLayout(header)) pad.top += Math.round(header.getBoundingClientRect().height);

  const stats = document.querySelector('.stats-bar');
  if (isElementVisibleOnLayout(stats)) pad.top += Math.round(stats.getBoundingClientRect().height);

  const floatingSearch = document.querySelector('.floating-search');
  if (isElementVisibleOnLayout(floatingSearch)) pad.top += Math.round(floatingSearch.getBoundingClientRect().height) + 8;

  if (window.innerWidth <= 768) {
    const mobBottom = document.getElementById('mob-bottom-bar');
    if (isElementVisibleOnLayout(mobBottom)) pad.bottom += Math.round(mobBottom.getBoundingClientRect().height) + 8;

    const sheetVisible = getMobileSheetVisiblePx();
    if (sheetVisible > 0) pad.bottom += Math.min(Math.round(sheetVisible + 12), Math.round(window.innerHeight * 0.75));
  } else {
    const sidebar = document.querySelector('.sidebar');
    if (isElementVisibleOnLayout(sidebar)) pad.right += Math.round(sidebar.getBoundingClientRect().width) + 12;

    const dp = document.getElementById('dp-panel');
    if (dp?.classList.contains('open') && isElementVisibleOnLayout(dp)) {
      pad.right += Math.round(dp.getBoundingClientRect().width) + 8;
    }
  }

  return {
    top: Math.max(0, Math.round(pad.top + (extra.top || 0))),
    right: Math.max(0, Math.round(pad.right + (extra.right || 0))),
    bottom: Math.max(0, Math.round(pad.bottom + (extra.bottom || 0))),
    left: Math.max(0, Math.round(pad.left + (extra.left || 0)))
  };
}

function focusMapLatLng(lat, lng, zoom, opts = {}) {
  if (!map || !Number.isFinite(lat) || !Number.isFinite(lng)) return;
  const targetZoom = Number.isFinite(zoom) ? zoom : (map.getZoom() || 14);
  const pad = getMapFocusPadding(opts.padding || {});
  const size = map.getSize();
  const safeW = Math.max(40, size.x - pad.left - pad.right);
  const safeH = Math.max(40, size.y - pad.top - pad.bottom);
  const safeCenterX = pad.left + safeW / 2;
  const safeCenterY = pad.top + safeH / 2;
  const targetPt = map.project([lat, lng], targetZoom);
  const centerPt = L.point(
    targetPt.x - (safeCenterX - size.x / 2),
    targetPt.y - (safeCenterY - size.y / 2)
  );
  const adjustedCenter = map.unproject(centerPt, targetZoom);
  const animate = opts.animate !== false;
  const duration = Number.isFinite(opts.duration) ? opts.duration : 0.62;

  if (opts.fly !== false && typeof map.flyTo === 'function') {
    map.flyTo(adjustedCenter, targetZoom, { animate, duration });
  } else {
    map.setView(adjustedCenter, targetZoom, { animate });
  }

  if (opts.keepVisible !== false && typeof map.panInside === 'function') {
    const enforce = () => {
      try {
        map.panInside([lat, lng], {
          paddingTopLeft: L.point(Math.max(0, pad.left - 6), Math.max(0, pad.top - 6)),
          paddingBottomRight: L.point(Math.max(0, pad.right - 6), Math.max(0, pad.bottom - 6)),
          animate: false
        });
      } catch {}
    };
    map.once('moveend', enforce);
    setTimeout(enforce, Math.round(duration * 1000) + 90);
  }
}

function fitBoundsWithUiPadding(bounds, opts = {}) {
  if (!map || !bounds) return;
  const pad = getMapFocusPadding(opts.padding || {});
  map.fitBounds(bounds, {
    paddingTopLeft: [pad.left, pad.top],
    paddingBottomRight: [pad.right, pad.bottom],
    animate: opts.animate !== false,
    maxZoom: opts.maxZoom
  });
}

function selectCityHistoryEntry(rec) {
  if (!rec || !map) return;
  const input = document.getElementById('city-input');
  if (input) input.value = rec.query || rec.title || '';
  closeCitySmartDropdown();
  if (rec.kind === 'mosque' && rec.osmId) {
    const m = findMosqueByRef(rec.osmType, rec.osmId);
    if (m) {
      selectMosque(m);
      return;
    }
  }
  if (Number.isFinite(rec.lat) && Number.isFinite(rec.lng)) {
    focusMapLatLng(rec.lat, rec.lng, rec.kind === 'mosque' ? Math.max(map.getZoom() || 15, 16) : 14, { duration:0.6 });
    map.once('moveend', () => scheduleViewportLoad(80));
    if (rec.kind !== 'mosque' && rec.bbox && rec.bbox.every(Number.isFinite)) {
      highlightPlaceBoundary(rec);
    }
    bumpCitySearchHistory(rec);
    return;
  }
  doSearch();
}

function showCityFocusDropdown() {
  const dd = document.getElementById('city-smart-dd');
  if (!dd) return;
  cityDropdownIdx = -1;
  const history = citySearchHistory.slice(0, 8);
  const nearbyMosques = getVisibleMosques(0.1)
    .map(m => ({ m, rank:(computeMosqueProximityScore(m) + computeMosquePopularityScore(m)) }))
    .sort((a,b) => b.rank - a.rank)
    .slice(0, 4)
    .map(x => x.m);
  if (!history.length && !nearbyMosques.length) {
    dd.innerHTML = `<div class="ms-no-result">Arama geçmişiniz burada görünecek</div>`;
    dd.classList.add('show');
    return;
  }
  const frag = document.createDocumentFragment();
  if (history.length) {
    const hdr = document.createElement('div');
    hdr.className = 'ms-group-hdr';
    hdr.innerHTML = `<span class="ms-group-ic">H</span>Geçmiş Aramalar
      <button class="ms-group-act" type="button" onclick="clearCitySearchHistory();showCityFocusDropdown()">Temizle</button>`;
    frag.appendChild(hdr);
    history.forEach(rec => {
      const recKey = citySearchHistoryKey(rec);
      const div = document.createElement('div');
      div.className = 'ms-item';
      div.dataset.kind = rec.kind;
      div.dataset.group = 'history';
      div.innerHTML = `
        <div class="ms-item-dot" style="background:${rec.kind === 'mosque' ? '#4ade80' : '#60a5fa'}"></div>
        <div class="ms-item-info">
          <div class="ms-item-name"><span class="ms-item-ic">${rec.kind === 'mosque' ? 'M' : 'P'}</span>${escHtml(rec.title || rec.query)}</div>
          <div class="ms-item-sub">${escHtml(rec.subtitle || 'Son arama')}</div>
        </div>
        <div class="ms-item-diff" style="color:var(--gold)">${Math.max(1, rec.count || 1)}x</div>
        <button class="ms-item-del" type="button" title="Kaydı sil" aria-label="Kaydı sil">×</button>`;
      const delBtn = div.querySelector('.ms-item-del');
      delBtn?.addEventListener('click', (e) => {
        e.preventDefault();
        e.stopPropagation();
        removeCitySearchHistoryEntry(recKey);
        showCityFocusDropdown();
      });
      div.onclick = () => selectCityHistoryEntry(rec);
      frag.appendChild(div);
    });
  }
  if (nearbyMosques.length) {
    const hdr = document.createElement('div');
    hdr.className = 'ms-group-hdr';
    hdr.innerHTML = `<span class="ms-group-ic">N</span>Haritadaki Yakın Camiler`;
    frag.appendChild(hdr);
    nearbyMosques.forEach(m => {
      const dist = getUserDistanceLabel(m);
      const div = document.createElement('div');
      div.className = 'ms-item';
      div.dataset.kind = 'mosque';
      div.dataset.group = 'nearby';
      div.innerHTML = `
        <div class="ms-item-dot" style="background:#4ade80"></div>
        <div class="ms-item-info">
          <div class="ms-item-name"><span class="ms-item-ic">M</span>${escHtml(m.name)}</div>
          <div class="ms-item-sub">${escHtml(getMosqueHierarchyLine(m))}</div>
        </div>
        <div class="ms-item-diff" style="color:var(--gold)">${escHtml(dist || 'yakın')}</div>`;
      div.onclick = () => selectMosque(m);
      frag.appendChild(div);
    });
  }
  dd.innerHTML = '';
  dd.appendChild(frag);
  dd.classList.add('show');
}

function pickBestCitySuggestionFromDropdown(q) {
  const dd = document.getElementById('city-smart-dd');
  if (!dd) return null;
  const items = [...dd.querySelectorAll('.ms-item')];
  if (!items.length) return null;
  if (items.length === 1) return items[0];
  const qLow = trLower(String(q || '').trim());
  const qNorm = normalize(qLow);
  const words = qNorm.split(/\s+/).filter(Boolean);
  let best = null;
  let bestScore = -1;
  for (const it of items) {
    const nameEl = it.querySelector('.ms-item-name');
    const name = trLower((nameEl?.textContent || '').trim());
    const norm = normalize(name);
    let s = 0;
    if (name === qLow) s += 220;
    else if (norm === qNorm) s += 200;
    else if (name.startsWith(qLow)) s += 160;
    else if (norm.startsWith(qNorm)) s += 145;
    else if (name.includes(qLow)) s += 120;
    else if (norm.includes(qNorm)) s += 95;
    const matchedWords = words.filter(w => norm.includes(w)).length;
    s += matchedWords * 20;
    if (it.dataset.kind === 'mosque') s += 16;
    if (it.dataset.group === 'history') s += 10;
    if (it.dataset.group === 'nearby') s += 6;
    if (s > bestScore) {
      bestScore = s;
      best = it;
    }
  }
  return bestScore >= 110 ? best : null;
}

// Scoring function for a single mosque against query
function msMosqueScore(m, qLow, qNorm, words) {
  if (!m.searchIndex) buildSearchIndexForMosque(m);
  const names = m.searchIndex?.namesLow || [trLower(m.name || '')];
  const namesNorm = m.searchIndex?.namesNorm || names.map(n => normalize(n));
  const tokenSet = new Set(m.searchIndex?.tokens || []);
  const mosqueAliasGroups = new Set(m.searchIndex?.aliasGroups || []);
  const queryAliasGroups = findAliasGroupsForQuery(qNorm);
  const genericWords = new Set(['cami','camii','mescit','mescid','mosque','masjid']);
  const normalizedWords = words.map(w => normalize(trLower(w || ''))).filter(Boolean);
  const strongWords = normalizedWords.filter(w => w.length > 1 && !genericWords.has(w));

  let best = 0;
  for (const n of names) {
    const nn = normalize(n);
    if      (n === qLow)                                       best = Math.max(best, 100);
    else if (n.startsWith(qLow))                               best = Math.max(best, 85);
    else if (n.split(/\s+/).some(w => w === qLow))             best = Math.max(best, 80);
    else if (n.split(/\s+/).some(w => w.startsWith(qLow)))     best = Math.max(best, 65);
    else if (n.includes(qLow))                                 best = Math.max(best, 50);
    else if (nn.includes(qNorm))                               best = Math.max(best, 35);
  }

  // Multi-word: all words must appear somewhere in any name
  if (best === 0 && words.length > 1) {
    const baseWords = strongWords.length ? strongWords : normalizedWords;
    const allMatch = baseWords.length && baseWords.every(w =>
      tokenSet.has(w) ||
      namesNorm.some(n => n.includes(w))
    );
    if (allMatch) best = 34;
    else {
      // Partial: at least one strong word must match; generic-only hits are ignored.
      const anyStrongMatch = strongWords.some(w =>
        tokenSet.has(w) || namesNorm.some(n => n.includes(w))
      );
      if (anyStrongMatch) {
        best = 14;
        const hasGenericHit = normalizedWords.some(w => genericWords.has(w));
        if (hasGenericHit) best += 8;
      }
    }
  }

  if (queryAliasGroups.length && mosqueAliasGroups.size) {
    const aliasHit = queryAliasGroups.some(g => mosqueAliasGroups.has(g));
    if (aliasHit) best = Math.max(best, 160);
  }
  if (best > 0 && mosqueAliasGroups.size) {
    best += Math.min(14, mosqueAliasGroups.size * 4);
  }

  return best;
}

function computeMosquePopularityScore(m) {
  const tags = m?.tags || {};
  let score = 0;
  const visitTraffic = getVisitTrafficCount(m);
  const aliasCount = Array.isArray(m?.searchIndex?.aliasGroups) ? m.searchIndex.aliasGroups.length : 0;
  if (aliasCount) score += Math.min(20, aliasCount * 6);
  if (typeof tags.wikipedia === 'string' && tags.wikipedia.trim()) score += 10;
  if (typeof tags.wikidata === 'string' && tags.wikidata.trim()) score += 12;
  if (typeof tags.historic === 'string' && tags.historic.trim()) score += 8;
  if (typeof tags.heritage === 'string' && tags.heritage.trim()) score += 8;
  if (trLower(tags.tourism || '') === 'attraction') score += 6;
  if (trLower(tags.place || '') === 'landmark') score += 6;
  if (!isPlaceholderMosqueName(m?.name) && !isGenericMosqueName(m?.name)) score += 4;
  if (visitTraffic > 0) {
    score += Math.min(36, Math.log10(visitTraffic + 1) * 18);
  }
  if (Number.isFinite(m?.popularityViews) && m.popularityViews > 0) {
    score += Math.min(44, Math.log10(m.popularityViews + 10) * 12);
  }
  return Math.min(84, score);
}

function getMosqueWikiTag(m) {
  const t = m?.tags || {};
  const wiki = String(t.wikipedia || '').trim();
  if (!wiki) return '';
  if (!wiki.includes(':')) return `tr:${wiki}`;
  return wiki;
}

function wikiPopularityCacheKey(wikiTag) {
  return `wiki:${wikiTag}`;
}

function getCachedWikiViews(wikiTag) {
  if (!wikiTag) return null;
  const key = wikiPopularityCacheKey(wikiTag);
  const cached = popularityCache.get(key);
  if (!cached) return null;
  const age = Date.now() - cached.ts;
  if (age > 1000 * 60 * 60 * 24 * 7) return null;
  return cached.views;
}

async function fetchWikiMonthlyViews(wikiTag) {
  const [langRaw, ...titleParts] = wikiTag.split(':');
  const lang = (langRaw || 'tr').trim().toLowerCase();
  const title = titleParts.join(':').trim();
  if (!title) return 0;
  const api = `https://${lang}.wikipedia.org/w/api.php?action=query&titles=${encodeURIComponent(title)}&prop=pageviews&format=json&origin=*`;
  const r = await fetch(api);
  if (!r.ok) return 0;
  const d = await r.json();
  const pages = d?.query?.pages || {};
  const page = Object.values(pages)[0];
  const pv = page?.pageviews || {};
  const vals = Object.values(pv).map(v => Number(v)).filter(Number.isFinite).slice(-30);
  return vals.reduce((s, v) => s + v, 0);
}

async function hydrateMosquePopularity(m) {
  const wikiTag = getMosqueWikiTag(m);
  if (!wikiTag) return 0;
  const cacheHit = getCachedWikiViews(wikiTag);
  if (cacheHit != null) {
    m.popularityViews = cacheHit;
    return cacheHit;
  }
  const key = wikiPopularityCacheKey(wikiTag);
  if (popularityInFlight.has(key)) return m.popularityViews || 0;
  popularityInFlight.add(key);
  try {
    const views = await fetchWikiMonthlyViews(wikiTag);
    if (Number.isFinite(views) && views >= 0) {
      popularityCache.set(key, { views: Math.round(views), ts: Date.now() });
      m.popularityViews = Math.round(views);
      savePopularityCache();
      return m.popularityViews;
    }
  } catch {}
  finally {
    popularityInFlight.delete(key);
  }
  return 0;
}

function queuePopularityHydration(candidates = [], rerender) {
  const list = [...new Set((candidates || []).map(x => x?.m || x).filter(Boolean))]
    .filter(m => getMosqueWikiTag(m))
    .slice(0, 8);
  if (!list.length) return;
  const before = new Map(list.map(m => [getMosqueKey(m), Number(m.popularityViews) || 0]));
  Promise.all(list.map(m => hydrateMosquePopularity(m))).then(() => {
    const changed = list.some(m => {
      const key = getMosqueKey(m);
      const prev = before.get(key) || 0;
      const now = Number(m.popularityViews) || 0;
      return now !== prev;
    });
    if (!changed) return;
    try { if (typeof rerender === 'function') rerender(); } catch {}
  }).catch(() => {});
}

function pickAddressAdmin(address = {}) {
  const city = String(
    address.city || address.town || address.municipality || address.county || address.state_district || ''
  ).trim();
  const province = String(
    address.state || address.province || address.region || address.county || ''
  ).trim();
  const country = String(address.country || '').trim();
  return { city, province, country };
}

function getMosqueAdminBucket(m) {
  const t = m?.tags || {};
  const meta = m?.searchMeta || {};
  const city = String(
    t['addr:city'] || t['addr:town'] || t['is_in:city'] || meta.city || ''
  ).trim();
  const province = String(
    t['addr:province'] || t['addr:state'] || t['is_in:state'] || meta.province || city || currentCity || ''
  ).trim();
  return { city, province, country: String(meta.country || '').trim() };
}

function getSearchProvinceLabel(m) {
  const admin = getMosqueAdminBucket(m);
  const raw = admin.province || admin.city || currentCity || 'Diğer';
  return String(raw).toLocaleUpperCase('tr-TR');
}

function computeMosqueProximityScore(m) {
  if (!userGeoState.enabled || !Number.isFinite(userGeoState.lat) || !Number.isFinite(userGeoState.lng)) return 0;
  const km = greatCircleKm(userGeoState.lat, userGeoState.lng, m.lat, m.lng);
  if (!Number.isFinite(km)) return 0;
  if (km <= 0.25) return 18;
  if (km <= 1) return 14;
  if (km <= 3) return 10;
  if (km <= 8) return 6;
  if (km <= 20) return 3;
  return 0;
}

function computeMosqueDistanceKm(m) {
  if (!userGeoState.enabled || !Number.isFinite(userGeoState.lat) || !Number.isFinite(userGeoState.lng)) return Infinity;
  const km = greatCircleKm(userGeoState.lat, userGeoState.lng, m.lat, m.lng);
  return Number.isFinite(km) ? km : Infinity;
}

function computeMosqueImportanceScore(m) {
  const imp = Number(m?.searchMeta?.importance);
  if (!Number.isFinite(imp) || imp <= 0) return 0;
  return Math.max(0, Math.min(24, imp * 28));
}

function msEditDistance(a, b) {
  const s = String(a || '');
  const t = String(b || '');
  if (!s) return t.length;
  if (!t) return s.length;
  const dp = Array.from({ length: s.length + 1 }, () => new Array(t.length + 1).fill(0));
  for (let i = 0; i <= s.length; i++) dp[i][0] = i;
  for (let j = 0; j <= t.length; j++) dp[0][j] = j;
  for (let i = 1; i <= s.length; i++) {
    for (let j = 1; j <= t.length; j++) {
      const c = s[i - 1] === t[j - 1] ? 0 : 1;
      dp[i][j] = Math.min(
        dp[i - 1][j] + 1,
        dp[i][j - 1] + 1,
        dp[i - 1][j - 1] + c
      );
    }
  }
  return dp[s.length][t.length];
}

function suggestClosestMosqueQuery(qNorm) {
  if (!qNorm || qNorm.length < 3 || !mosqueDB.size) return null;
  let best = null;
  let bestDist = Infinity;
  for (const m of mosqueDB.values()) {
    if (!m.searchIndex) buildSearchIndexForMosque(m);
    const names = m.searchIndex?.namesNorm || [];
    for (const n of names) {
      if (!n || n.length < 3) continue;
      const d = msEditDistance(qNorm, n);
      if (d < bestDist) {
        bestDist = d;
        best = m.name || n;
      }
      if (bestDist === 1) break;
    }
    if (bestDist === 1) break;
  }
  if (!best) return null;
  const maxAllowed = Math.max(1, Math.floor(qNorm.length * 0.34));
  return bestDist <= maxAllowed ? best : null;
}

function applySuggestedMosqueQuery(text) {
  const input = document.getElementById('mosque-search');
  if (!input) return;
  input.value = text;
  input.classList.add('has-value');
  document.getElementById('ms-clear')?.classList.add('show');
  showMosqueDropdown(text);
}

function rankMosqueCandidates(q, limit = 15, opts = {}) {
  const qLow  = trLower(q);
  const qNorm = normalize(qLow);
  const words = qLow.split(/\s+/).filter(w => w.length > 0);
  const strongWords = strongQueryWords(q);
  const ambiguousQuery = isAmbiguousMosqueQuery(q);
  const scopeViewportOnly = typeof opts.scopeViewportOnly === 'boolean' ? opts.scopeViewportOnly : msScopeViewportOnly;
  const bounds = map?.getBounds?.()?.pad?.(0.08) || null;
  const scored = [];
  for (const m of mosqueDB.values()) {
    const textScore = msMosqueScore(m, qLow, qNorm, words);
    if (textScore <= 0) continue;
    if (!m.searchIndex) buildSearchIndexForMosque(m);
    const namesNorm = m.searchIndex?.namesNorm || [normalize(trLower(m.name || ''))];
    if (strongWords.length >= 2) {
      const matchCount = strongWords.filter(w => namesNorm.some(n => n === w || n.includes(w))).length;
      if (matchCount === 0) continue;
      if (matchCount < strongWords.length && textScore < 45) continue;
    }
    const inView = bounds ? bounds.contains([m.lat, m.lng]) : false;
    const popScore = computeMosquePopularityScore(m);
    const proxScore = computeMosqueProximityScore(m);
    const impScore = computeMosqueImportanceScore(m);
    const proxWeight = ambiguousQuery ? 3.2 : 1;
    const viewportBonus = !bounds ? 0 : (inView ? (scopeViewportOnly ? 45 : 18) : (scopeViewportOnly ? -50 : 0));
    const rankScore = textScore + popScore + impScore + (proxScore * proxWeight) + viewportBonus;
    scored.push({ m, s:textScore, p:popScore, d:proxScore, imp:impScore, inView, rank:rankScore });
  }
  const ranked = scopeViewportOnly && bounds
    ? scored.filter(x => x.inView).sort((a,b) => b.rank - a.rank || b.s - a.s)
    : scored.sort((a,b) => b.rank - a.rank || (b.inView - a.inView) || (b.s - a.s));
  return { ranked: ranked.slice(0, limit), qLow, qNorm, words, bounds };
}

function strongQueryWords(query) {
  const generic = new Set(['cami','camii','mescit','mescid','mosque','masjid']);
  return normalize(trLower(query || ''))
    .split(/[^a-z0-9ığüşöçâêîû]+/i)
    .filter(w => w.length > 1 && !generic.has(w));
}

function isAmbiguousMosqueQuery(query) {
  if (!isLikelyMosqueQuery(query)) return false;
  const strong = strongQueryWords(query);
  return strong.length <= 1;
}

function isStrongSmartSelection(query, smart, aliasHints = []) {
  if (!query || !smart?.m) return false;
  if (aliasHints.length && smart.s >= 120) return true;
  if (smart.s < 80) return false;
  if (!smart.m.searchIndex) buildSearchIndexForMosque(smart.m);
  const namesNorm = smart.m.searchIndex?.namesNorm || [normalize(trLower(smart.m.name || ''))];
  const words = strongQueryWords(query);
  if (!words.length) return false;
  return words.every(w => namesNorm.some(n => n === w || n.includes(w)));
}

function toOsmType(v) {
  const t = trLower(String(v || '').trim());
  if (t === 'n' || t === 'node') return 'node';
  if (t === 'w' || t === 'way') return 'way';
  if (t === 'r' || t === 'relation') return 'relation';
  return null;
}

function isLikelyMosqueHit(it) {
  const cls = trLower(it?.class || '');
  const typ = trLower(it?.type || '');
  const disp = trLower(it?.display_name || '');
  const extr = it?.extratags || {};
  const rel = trLower(extr.religion || extr['building:religion'] || extr.denomination || '');
  if (rel && /(muslim|islam|sunni|shia|ibadi)/.test(rel)) return true;
  if (cls === 'amenity' && (typ === 'place_of_worship' || typ === 'mosque')) return true;
  if (cls === 'building' && typ === 'mosque') return true;
  return /\b(cami|camii|mosque|masjid|mescid|mescit|džamija|dzamija)\b/.test(disp);
}

function nominatimViewboxParams(bounds, bounded = true) {
  if (!bounds) return '';
  const left = bounds.getWest().toFixed(6);
  const top = bounds.getNorth().toFixed(6);
  const right = bounds.getEast().toFixed(6);
  const bottom = bounds.getSouth().toFixed(6);
  return `&viewbox=${left},${top},${right},${bottom}${bounded ? '&bounded=1' : ''}`;
}

function normalizeOsmType(raw) {
  const t = String(raw || '').trim().toLowerCase();
  if (t === 'n' || t === 'node') return 'node';
  if (t === 'w' || t === 'way') return 'way';
  if (t === 'r' || t === 'relation') return 'relation';
  return '';
}

function getSuggestCacheKey(q, bounds) {
  const b = bounds
    ? `${bounds.getSouth().toFixed(3)}:${bounds.getWest().toFixed(3)}:${bounds.getNorth().toFixed(3)}:${bounds.getEast().toFixed(3)}`
    : 'global';
  return `${normalize(trLower(q || ''))}|${b}`;
}

function inBoundsSafe(bounds, lat, lng) {
  if (!bounds || !Number.isFinite(lat) || !Number.isFinite(lng)) return false;
  try { return bounds.contains([lat, lng]); } catch { return false; }
}

function textScoreForSuggestion(query, label) {
  const q = normalize(trLower(query || ''));
  const l = normalize(trLower(label || ''));
  if (!q || !l) return 0;
  if (l === q) return 120;
  if (l.startsWith(q)) return 95;
  if (l.includes(` ${q}`)) return 70;
  if (l.includes(q)) return 48;
  return 0;
}

function computeSuggestionScore(item, query, bounds) {
  const text = textScoreForSuggestion(query, item.title || item.subtitle || '');
  const imp = Number.isFinite(item.importance) ? Math.max(0, Math.min(1, item.importance)) * 55 : 0;
  const vp = inBoundsSafe(bounds, item.lat, item.lng) ? 45 : 0;
  let prox = 0;
  if (userGeoState.enabled && Number.isFinite(userGeoState.lat) && Number.isFinite(userGeoState.lng)) {
    const km = greatCircleKm(userGeoState.lat, userGeoState.lng, item.lat, item.lng);
    if (Number.isFinite(km)) prox = Math.max(0, 42 - Math.min(42, km * 3.5));
  }
  const mosqueBoost = item.kind === 'mosque' ? 18 : 0;
  return text + imp + vp + prox + mosqueBoost;
}

async function fetchPhotonPlaceSuggestions(query, bounds, signal) {
  const center = map?.getCenter?.();
  const params = new URLSearchParams({
    q: query,
    limit: '10',
    lang: currentLang === 'en' ? 'en' : 'tr'
  });
  if (center && Number.isFinite(center.lat) && Number.isFinite(center.lng)) {
    params.set('lat', String(center.lat));
    params.set('lon', String(center.lng));
  }
  const url = `https://photon.komoot.io/api/?${params.toString()}`;
  const data = await limitedFetch(url, {}, {
    hostKey:'nominatim',
    minInterval:700,
    retries:1,
    timeoutMs:9000,
    backoffMs:500,
    signal
  }).then(r => r.ok ? r.json() : Promise.reject(new Error(`HTTP ${r.status}`)));
  const features = Array.isArray(data?.features) ? data.features : [];
  return features.map((f) => {
    const p = f?.properties || {};
    const coords = Array.isArray(f?.geometry?.coordinates) ? f.geometry.coordinates : [];
    const lng = Number(coords[0]);
    const lat = Number(coords[1]);
    if (!Number.isFinite(lat) || !Number.isFinite(lng)) return null;
    const name = String(p.name || p.street || p.city || p.state || '').trim();
    const city = String(p.city || p.county || p.district || '').trim();
    const state = String(p.state || '').trim();
    const country = String(p.country || '').trim();
    const osmType = normalizeOsmType(p.osm_type);
    const osmId = String(p.osm_id || '').replace(/\D/g,'');
    const kind = isLikelyMosqueQuery(name) || /(mosque|cami|mescid|mescit|masjid)/i.test(String(p.osm_value || '')) ? 'mosque' : 'place';
    return {
      source:'photon',
      lat, lng,
      title:name || city || state || country || 'Bilinmeyen',
      subtitle:[city, state, country].filter(Boolean).join(', '),
      importance:Number.isFinite(+p.importance) ? +p.importance : 0,
      kind,
      osmType,
      osmId,
      bbox:null
    };
  }).filter(Boolean);
}

async function fetchNominatimPlaceSuggestions(query, bounds, signal) {
  const vb = nominatimViewboxParams(bounds, false);
  const url = `https://nominatim.openstreetmap.org/search?format=jsonv2&limit=10&addressdetails=1&extratags=1&q=${encodeURIComponent(query)}${vb}`;
  const rows = await nominatimFetchJson(url, {'Accept-Language':'tr,en'}, { signal });
  return (rows || []).map((r) => {
    const lat = Number(r.lat), lng = Number(r.lon);
    if (!Number.isFinite(lat) || !Number.isFinite(lng)) return null;
    const parts = String(r.display_name || '').split(',');
    const title = String(parts[0] || r.name || '').trim() || 'Bilinmeyen';
    const subtitle = parts.slice(1,4).map(s => s.trim()).filter(Boolean).join(', ');
    const bbox = Array.isArray(r.boundingbox) && r.boundingbox.length === 4
      ? [Number(r.boundingbox[0]), Number(r.boundingbox[1]), Number(r.boundingbox[2]), Number(r.boundingbox[3])]
      : null;
    const osmType = normalizeOsmType(r.osm_type);
    const osmId = String(r.osm_id || '').replace(/\D/g,'');
    const kind = isLikelyMosqueHit(r) ? 'mosque' : 'place';
    return {
      source:'nominatim',
      lat, lng,
      title,
      subtitle,
      importance:Number.isFinite(+r.importance) ? +r.importance : 0,
      kind,
      osmType,
      osmId,
      bbox
    };
  }).filter(Boolean);
}

async function fetchPlaceSuggestions(query, bounds, signal) {
  const key = getSuggestCacheKey(query, bounds);
  const cached = PLACE_SUGGEST_CACHE.get(key);
  if (cached && (Date.now() - cached.ts) < 45000) return cached.items;
  let photon = [];
  let nom = [];
  try { photon = await fetchPhotonPlaceSuggestions(query, bounds, signal); } catch {}
  try { nom = await fetchNominatimPlaceSuggestions(query, bounds, signal); } catch {}
  const merged = [...photon, ...nom];
  const dedupe = new Map();
  for (const it of merged) {
    const k = it.osmType && it.osmId
      ? `${it.osmType}:${it.osmId}`
      : `${normalize(trLower(it.title))}:${it.lat.toFixed(4)}:${it.lng.toFixed(4)}`;
    if (!dedupe.has(k)) dedupe.set(k, it);
  }
  const out = [...dedupe.values()]
    .map(it => ({ ...it, score:computeSuggestionScore(it, query, bounds) }))
    .sort((a,b) => b.score - a.score)
    .slice(0, 12);
  PLACE_SUGGEST_CACHE.set(key, { ts:Date.now(), items:out });
  return out;
}

async function fetchNominatimMosqueRefs(query, bounds, bounded = true, limit = 12) {
  const vb = nominatimViewboxParams(bounds, bounded);
  const url = `https://nominatim.openstreetmap.org/search?format=jsonv2&limit=${limit}&addressdetails=1&extratags=1&q=${encodeURIComponent(query)}${vb}`;
  const data = await nominatimFetchJson(url, {'Accept-Language':'tr,en'});
  const refs = [];
  for (const it of (data || [])) {
    if (!isLikelyMosqueHit(it)) continue;
    const osmType = toOsmType(it.osm_type);
    const id = String(it.osm_id || '').replace(/\D/g, '');
    if (!osmType || !id) continue;
    const admin = pickAddressAdmin(it.address || {});
    refs.push({
      osmType,
      id,
      city: admin.city,
      province: admin.province,
      country: admin.country,
      displayName: it.display_name || '',
      importance: Number.isFinite(+it.importance) ? +it.importance : 0
    });
  }
  return refs;
}

async function fetchByOsmRefs(refs) {
  const groups = { node:[], way:[], relation:[] };
  for (const r of refs || []) {
    if (!r?.osmType || !r?.id) continue;
    groups[r.osmType]?.push(String(r.id));
  }
  const uniq = t => [...new Set(groups[t])].slice(0, 40);
  const nodes = uniq('node');
  const ways = uniq('way');
  const rels = uniq('relation');
  if (!nodes.length && !ways.length && !rels.length) return [];
  const parts = [];
  if (nodes.length) parts.push(`node(id:${nodes.join(',')});`);
  if (ways.length) parts.push(`way(id:${ways.join(',')});`);
  if (rels.length) parts.push(`relation(id:${rels.join(',')});`);
  const q = `[out:json][timeout:45];(${parts.join('')});out body geom tags center;`;
  return fetchOverpassQuery(q);
}

async function triggerRemoteMosqueLookup(query, qNorm, bounds, opts = {}) {
  if (!query || !qNorm || qNorm.length < 3) return 0;
  if (msRemoteLookupPending && msRemoteLookupKey === qNorm) return 0;
  const missAt = msRemoteLookupMissAt.get(qNorm);
  if (missAt && Date.now() - missAt < 120000) return 0;
  msRemoteLookupPending = true;
  msRemoteLookupKey = qNorm;
  try {
    const refsMap = new Map();
    const boundedRefs = await fetchNominatimMosqueRefs(query, bounds, true, 16).catch(() => []);
    boundedRefs.forEach(r => refsMap.set(`${r.osmType}:${r.id}`, r));

    if (!refsMap.size || !msScopeViewportOnly || opts.preferGlobal) {
      const globalRefs = await fetchNominatimMosqueRefs(`${query} mosque`, null, false, 14).catch(() => []);
      globalRefs.forEach(r => refsMap.set(`${r.osmType}:${r.id}`, r));
    }

    if (!refsMap.size) {
      msRemoteLookupMissAt.set(qNorm, Date.now());
      return 0;
    }

    refsMap.forEach((r, key) => {
      msRemoteMetaByRef.set(key, {
        city:r.city || '',
        province:r.province || '',
        country:r.country || '',
        displayName:r.displayName || '',
        importance:Number.isFinite(r.importance) ? r.importance : 0
      });
    });

    const elements = await fetchByOsmRefs([...refsMap.values()]);
    const added = processElements(elements);
    if (!added) msRemoteLookupMissAt.set(qNorm, Date.now());
    return added;
  } catch {
    return 0;
  } finally {
    msRemoteLookupPending = false;
    msRemoteLookupKey = '';
  }
}

function getMosqueHierarchyLine(m) {
  const t = m?.tags || {};
  const admin = getMosqueAdminBucket(m);
  const n1 = t['addr:suburb'] || t['addr:neighbourhood'] || t['addr:quarter'] || t['addr:hamlet'] || t['addr:village'] || t['addr:city_district'] || '';
  const n2 = t['addr:district'] || t['addr:township'] || '';
  const n3 = admin.city || '';
  const n4 = admin.province || '';
  const n5 = admin.country || '';
  const parts = [n1, n2, n3, n4, n5].map(x => String(x || '').trim()).filter(Boolean);
  if (parts.length) return parts.join(', ');
  return 'Mahalle / ilçe / şehir bilgisi yok';
}

function getUserDistanceLabel(m) {
  if (!userGeoState.enabled || !Number.isFinite(userGeoState.lat) || !Number.isFinite(userGeoState.lng)) return '';
  const km = greatCircleKm(userGeoState.lat, userGeoState.lng, m.lat, m.lng);
  if (!Number.isFinite(km)) return '';
  if (km < 1) return `${Math.max(50, Math.round(km * 1000))} m`;
  return `${km.toFixed(km < 10 ? 1 : 0)} km`;
}

function buildSearchResultGroups(ranked = [], q = '') {
  const src = [...(ranked || [])];
  if (!src.length) return [];
  const used = new Set();
  const groups = [];

  const history = src
    .map(x => ({ ...x, visit:getVisitTrafficRecord(x.m) }))
    .filter(x => x.visit && x.visit.count > 0)
    .sort((a,b) => (b.visit.ts - a.visit.ts) || (b.visit.count - a.visit.count) || (b.rank - a.rank))
    .slice(0, 6);
  if (history.length) {
    history.forEach(x => used.add(getMosqueKey(x.m)));
    groups.push({ title:'Geçmiş Aramalar ve Analizler', items:history });
  }

  if (userGeoState.enabled && Number.isFinite(userGeoState.lat) && Number.isFinite(userGeoState.lng)) {
    const nearby = src
      .filter(x => !used.has(getMosqueKey(x.m)))
      .map(x => ({ ...x, km:computeMosqueDistanceKm(x.m) }))
      .filter(x => Number.isFinite(x.km))
      .sort((a,b) => a.km - b.km || b.rank - a.rank)
      .slice(0, 3);
    if (nearby.length) {
      nearby.forEach(x => used.add(getMosqueKey(x.m)));
      groups.push({ title:'Yakınınızdakiler', items:nearby });
    }
  }

  const global = src.filter(x => !used.has(getMosqueKey(x.m)));
  if (global.length) groups.push({ title:'Küresel Sonuçlar', items:global });
  return groups;
}

async function probeUserGeoForSearch(currentQuery) {
  if (msGeoProbePending) return;
  if (!navigator.geolocation) return;
  if (Date.now() - msGeoProbeAt < 45000) return;
  msGeoProbePending = true;
  try {
    if (navigator.permissions?.query) {
      const perm = await navigator.permissions.query({ name:'geolocation' });
      if (perm.state !== 'granted') return;
    } else if (!userGeoState.enabled) {
      return;
    }
    const pos = await getCurrentPositionAsync({ enableHighAccuracy:false, timeout:4500, maximumAge:300000 });
    setUserGeoState(pos.coords.latitude, pos.coords.longitude, true);
    const inputVal = document.getElementById('mosque-search')?.value?.trim();
    if (inputVal && inputVal === currentQuery) showMosqueDropdown(inputVal);
  } catch {
    // Silent fail: dropdown should continue without distance.
  } finally {
    msGeoProbeAt = Date.now();
    msGeoProbePending = false;
  }
}

function showMosqueDropdown(q) {
  const dropdown = document.getElementById('ms-dropdown');
  probeUserGeoForSearch(q);

  if (!mosqueDB || !mosqueDB.size) {
    dropdown.innerHTML = '<div class="ms-no-result">Henüz veri yüklenmedi — bir şehir arayın</div>';
    dropdown.classList.add('show');
    return;
  }

  const { ranked, qNorm, bounds } = rankMosqueCandidates(q, 24);
  const top = ranked;
  const ambiguousQuery = isAmbiguousMosqueQuery(q);
  queuePopularityHydration(top, () => {
    const qNow = document.getElementById('mosque-search')?.value?.trim();
    if (qNow === q) showMosqueDropdown(q);
  });
  if (ambiguousQuery && top.length > 0 && top.length < 18 && !msRemoteLookupPending) {
    triggerRemoteMosqueLookup(q, qNorm, bounds, { preferGlobal:true }).then(added => {
      const cur = document.getElementById('mosque-search')?.value?.trim();
      if (cur === q && added > 0) showMosqueDropdown(q);
    }).catch(() => {});
  }

  if (!top.length) {
    const scopeMsg = msScopeViewportOnly ? ' (mevcut harita alanında)' : '';
    const alt = suggestClosestMosqueQuery(qNorm);
    dropdown.innerHTML = `<div class="ms-no-result">"${escHtml(q)}" için sonuç bulunamadı${scopeMsg}${
      alt ? `<br><button class="ms-suggest-btn" onclick="applySuggestedMosqueQuery('${escHtml(alt).replace(/'/g, '&#39;')}')">Bunu mu demek istediniz: ${escHtml(alt)}?</button>` : ''
    }<br><span style="opacity:.75">Dış kaynakta aranıyor...</span></div>`;
    dropdown.classList.add('show');
    triggerRemoteMosqueLookup(q, qNorm, bounds, { preferGlobal: !msScopeViewportOnly }).then(added => {
      const current = document.getElementById('mosque-search')?.value?.trim();
      if (current !== q) return;
      if (added > 0) {
        showMosqueDropdown(q);
        return;
      }
      const scopeMsg2 = msScopeViewportOnly ? ' (mevcut harita alanında)' : '';
      const alt2 = suggestClosestMosqueQuery(qNorm);
      dropdown.innerHTML = `<div class="ms-no-result">"${escHtml(q)}" için sonuç bulunamadı${scopeMsg2}${
        alt2 ? `<br><button class="ms-suggest-btn" onclick="applySuggestedMosqueQuery('${escHtml(alt2).replace(/'/g, '&#39;')}')">Bunu mu demek istediniz: ${escHtml(alt2)}?</button>` : ''
      }</div>`;
      dropdown.classList.add('show');
    });
    return;
  }

  const frag = document.createDocumentFragment();
  const groups = buildSearchResultGroups(top, q);
  for (const group of groups) {
    const hdr = document.createElement('div');
    hdr.className = 'ms-group-hdr';
    hdr.textContent = group.title;
    frag.appendChild(hdr);
    group.items.sort((a,b) => b.rank - a.rank || b.p - a.p || b.s - a.s);
    group.items.forEach(({m, p, d, inView}) => {
      const col = m.status==='correct'?'#4ade80':m.status==='wrong'?'#f87171':'#fbbf24';
      const addressLine = getMosqueHierarchyLine(m);
      const userDistance = getUserDistanceLabel(m);
      const rightBadge = userDistance ? `${userDistance} yakınınızda` : (m.diff!==null ? m.diff.toFixed(1)+'°' : '—');
      const badges = [];
      if (p >= 14) badges.push('<span class="ms-badge pop">Popüler</span>');
      if (d >= 10) badges.push('<span class="ms-badge near">Yakında</span>');
      if (inView) badges.push('<span class="ms-badge view">Bu bölgede</span>');
      if (group.title === 'Geçmiş Aramalar ve Analizler') badges.push('<span class="ms-badge near">Geçmiş</span>');
      const div = document.createElement('div');
      div.className = 'ms-item';
      div.innerHTML = `
        <div class="ms-item-dot" style="background:${col};box-shadow:0 0 4px ${col}"></div>
        <div class="ms-item-info">
          <div class="ms-item-name">${highlightMatch(m.name, q)}</div>
          <div class="ms-item-sub">${escHtml(addressLine)}</div>
          ${badges.length ? `<div class="ms-badges">${badges.join('')}</div>` : ''}
          <div class="ms-item-sub meta">Kıble:${m.qibla.toFixed(1)}°${m.diff!==null?' | '+m.diff.toFixed(1)+'° sapma':''}</div>
        </div>
        <div class="ms-item-diff" style="color:${userDistance ? 'var(--gold)' : col}">${escHtml(rightBadge)}</div>`;
      div.onclick = () => selectMosque(m);
      frag.appendChild(div);
    });
  }

  // "Filter all" footer
  const total = ranked.length;
  if (total > 0) {
    const footer = document.createElement('div');
    footer.style.cssText = 'padding:7px 12px;font-size:10px;color:var(--muted);cursor:pointer;border-top:1px solid var(--border);text-align:center;';
    footer.textContent = `"${q}" — ${total} sonuç — tümünü listede filtrele →`;
    footer.onmouseenter = () => footer.style.color = 'var(--gold)';
    footer.onmouseleave = () => footer.style.color = 'var(--muted)';
    footer.onclick = () => { applyMosqueFilter(q); dropdown.classList.remove('show'); };
    frag.appendChild(footer);
  }

  dropdown.innerHTML = '';
  dropdown.appendChild(frag);
  dropdown.classList.add('show');
}

function closeCitySmartDropdown() {
  const dd = document.getElementById('city-smart-dd');
  if (!dd) return;
  dd.classList.remove('show');
  cityDropdownIdx = -1;
  if (citySuggestController) {
    try { citySuggestController.abort(); } catch {}
    citySuggestController = null;
  }
}

function clearPlaceBoundaryHighlight() {
  if (!placeBoundaryLayer || !map) return;
  try { map.removeLayer(placeBoundaryLayer); } catch {}
  placeBoundaryLayer = null;
}

function osmTypeToNominatimToken(osmType) {
  const t = normalizeOsmType(osmType);
  if (t === 'node') return 'N';
  if (t === 'way') return 'W';
  if (t === 'relation') return 'R';
  return '';
}

async function highlightPlaceBoundary(item) {
  if (!map || !item || item.kind === 'mosque') { clearPlaceBoundaryHighlight(); return; }
  clearPlaceBoundaryHighlight();
  const token = osmTypeToNominatimToken(item.osmType);
  const id = String(item.osmId || '').replace(/\D/g, '');
  if (!token || !id) return;
  try {
    const url = `https://nominatim.openstreetmap.org/lookup?format=jsonv2&polygon_geojson=1&osm_ids=${token}${id}`;
    const rows = await nominatimFetchJson(url, {'Accept-Language':'tr,en'});
    const geo = rows?.[0]?.geojson;
    if (!geo) return;
    placeBoundaryLayer = L.geoJSON(geo, {
      style: {
        color: '#c9a84c',
        weight: 2,
        opacity: 0.9,
        fillColor: '#c9a84c',
        fillOpacity: 0.08
      }
    }).addTo(map);
    try {
      const b = placeBoundaryLayer.getBounds?.();
      if (b?.isValid?.()) fitBoundsWithUiPadding(b.pad(0.12));
    } catch {}
  } catch {}
}

function selectPlaceSuggestion(item) {
  if (!item || !map) return;
  document.getElementById('city-input').value = item.title || '';
  bumpCitySearchHistory({
    query: item.title || '',
    title: item.title || '',
    subtitle: item.subtitle || '',
    kind: item.kind || 'place',
    lat: item.lat,
    lng: item.lng,
    osmType: item.osmType,
    osmId: item.osmId,
    bbox: item.bbox
  });
  closeCitySmartDropdown();
  const isMosque = item.kind === 'mosque';
  const zoom = isMosque ? 17 : 14;
  if (Array.isArray(item.bbox) && item.bbox.length === 4 && item.bbox.every(Number.isFinite) && !isMosque) {
    const s = item.bbox[0], n = item.bbox[1], w = item.bbox[2], e = item.bbox[3];
    if (Math.abs(n - s) > 0.001 && Math.abs(e - w) > 0.001) fitBoundsWithUiPadding([[s, w], [n, e]]);
    else focusMapLatLng(item.lat, item.lng, zoom, { duration:0.6 });
  } else {
    focusMapLatLng(item.lat, item.lng, zoom, { duration:0.6 });
  }
  map.once('moveend', () => scheduleViewportLoad(80));
  if (isMosque) {
    clearPlaceBoundaryHighlight();
    const q = item.title || document.getElementById('city-input').value.trim();
    if (q) {
      document.getElementById('mosque-search').value = q;
      document.getElementById('mosque-search').classList.add('has-value');
      document.getElementById('ms-clear').classList.add('show');
      applyMosqueFilter(q);
    }
  } else {
    highlightPlaceBoundary(item);
  }
}

function citySuggestionGroupId(title = '') {
  const t = trLower(title);
  if (t.includes('geçmiş')) return 'history';
  if (t.includes('yakın')) return 'nearby';
  return 'global';
}

function citySuggestionIcon(kind = '', groupId = 'global') {
  if (groupId === 'history') return 'H';
  if (kind === 'mosque') return 'M';
  return 'P';
}

async function showCitySmartDropdown(q) {
  const dd = document.getElementById('city-smart-dd');
  if (!dd) return;
  if (!q || q.length < 2) { closeCitySmartDropdown(); return; }
  if (isLikelyMosqueQuery(q) && !mosqueDB.size) {
    dd.innerHTML = `<div class="ms-no-result">Önce haritadan veri yüklenmeli</div>`;
    dd.classList.add('show');
    return;
  }
  if (!isLikelyMosqueQuery(q)) {
    if (citySuggestController) {
      try { citySuggestController.abort(); } catch {}
    }
    citySuggestController = new AbortController();
    const seq = ++citySuggestSeq;
    const signal = citySuggestController.signal;
    const bounds = map?.getBounds?.()?.pad?.(0.08) || null;
    dd.innerHTML = `<div class="ms-no-result">"${escHtml(q)}" aranıyor...</div>`;
    dd.classList.add('show');
    let items = [];
    try {
      items = await fetchPlaceSuggestions(q, bounds, signal);
    } catch (err) {
      if (err?.name === 'AbortError') return;
    }
    if (seq !== citySuggestSeq) return;
    if (!items.length) {
      dd.innerHTML = `<div class="ms-no-result">"${escHtml(q)}" için öneri yok</div>`;
      dd.classList.add('show');
      return;
    }
    const frag = document.createDocumentFragment();
    const recents = [];
    const nearby = [];
    const global = [];
    for (const it of items) {
      const dist = computeMosqueDistanceKm(it);
      const rec = { ...it, dist };
      const localHist = it.osmType && it.osmId
        ? getVisitTrafficRecord({ osmType:it.osmType, id:it.osmId })
        : null;
      if (localHist && localHist.count > 0) recents.push(rec);
      else if (Number.isFinite(dist) && dist < 8) nearby.push(rec);
      else global.push(rec);
    }
    const groups = [
      { title:'Geçmiş Aramalar ve Analizler', items:recents.slice(0,4) },
      { title:'Yakınınızdakiler', items:nearby.slice(0,4) },
      { title:'Küresel Sonuçlar', items:global.slice(0,8) }
    ].filter(g => g.items.length);
    groups.forEach((g) => {
      const groupId = citySuggestionGroupId(g.title);
      const hdr = document.createElement('div');
      hdr.className = 'ms-group-hdr';
      hdr.innerHTML = `<span class="ms-group-ic">${groupId === 'history' ? 'H' : groupId === 'nearby' ? 'N' : 'G'}</span>${escHtml(g.title)}`;
      frag.appendChild(hdr);
      g.items.forEach((it) => {
        const rightBadge = Number.isFinite(it.dist) ? `${getUserDistanceLabel(it)} yakınınızda` : '—';
        const dotCol = it.kind === 'mosque' ? '#4ade80' : '#60a5fa';
        const icon = citySuggestionIcon(it.kind, groupId);
        const div = document.createElement('div');
        div.className = 'ms-item';
        div.dataset.kind = it.kind || 'place';
        div.dataset.group = groupId;
        div.innerHTML = `
          <div class="ms-item-dot" style="background:${dotCol};box-shadow:0 0 4px ${dotCol}"></div>
          <div class="ms-item-info">
            <div class="ms-item-name"><span class="ms-item-ic">${icon}</span>${highlightMatch(it.title, q)}</div>
            <div class="ms-item-sub">${escHtml(it.subtitle || '')}</div>
          </div>
          <div class="ms-item-diff" style="color:var(--gold)">${escHtml(rightBadge)}</div>`;
        div.onclick = () => selectPlaceSuggestion(it);
        frag.appendChild(div);
      });
    });
    dd.innerHTML = '';
    dd.appendChild(frag);
    dd.classList.add('show');
    return;
  }
  const { ranked, qNorm, bounds } = rankMosqueCandidates(q, 24, { scopeViewportOnly:false });
  queuePopularityHydration(ranked, () => {
    const cur = document.getElementById('city-input')?.value?.trim();
    if (cur === q) showCitySmartDropdown(q);
  });
  if (!ranked.length) {
    dd.innerHTML = `<div class="ms-no-result">"${escHtml(q)}" için öneri yok</div>`;
    dd.classList.add('show');
    triggerRemoteMosqueLookup(q, qNorm, bounds, { preferGlobal:true }).then(added => {
      const cur = document.getElementById('city-input')?.value?.trim();
      if (cur !== q || added <= 0) return;
      showCitySmartDropdown(q);
    });
    return;
  }
  const frag = document.createDocumentFragment();
  const groups = buildSearchResultGroups(ranked, q);
  for (const group of groups) {
    const groupId = citySuggestionGroupId(group.title);
    const hdr = document.createElement('div');
    hdr.className = 'ms-group-hdr';
    hdr.innerHTML = `<span class="ms-group-ic">${groupId === 'history' ? 'H' : groupId === 'nearby' ? 'N' : 'G'}</span>${escHtml(group.title)}`;
    frag.appendChild(hdr);
    group.items.sort((a,b) => b.rank - a.rank || b.p - a.p || b.s - a.s);
    group.items.forEach(({m, p, d, inView}) => {
      const col = m.status==='correct'?'#4ade80':m.status==='wrong'?'#f87171':'#fbbf24';
      const addressLine = getMosqueHierarchyLine(m);
      const userDistance = getUserDistanceLabel(m);
      const rightBadge = userDistance ? `${userDistance} yakınınızda` : (m.diff!==null ? m.diff.toFixed(1)+'°' : '—');
      const badges = [];
      if (p >= 14) badges.push('<span class="ms-badge pop">Popüler</span>');
      if (d >= 10) badges.push('<span class="ms-badge near">Yakında</span>');
      if (inView) badges.push('<span class="ms-badge view">Bu bölgede</span>');
      if (group.title === 'Geçmiş Aramalar ve Analizler') badges.push('<span class="ms-badge near">Geçmiş</span>');
      const div = document.createElement('div');
      div.className = 'ms-item';
      div.dataset.kind = 'mosque';
      div.dataset.group = groupId;
      div.innerHTML = `
        <div class="ms-item-dot" style="background:${col};box-shadow:0 0 4px ${col}"></div>
        <div class="ms-item-info">
          <div class="ms-item-name"><span class="ms-item-ic">M</span>${highlightMatch(m.name, q)}</div>
          <div class="ms-item-sub">${escHtml(addressLine)}</div>
          ${badges.length ? `<div class="ms-badges">${badges.join('')}</div>` : ''}
        </div>
        <div class="ms-item-diff" style="color:${userDistance ? 'var(--gold)' : col}">${escHtml(rightBadge)}</div>`;
      div.onclick = () => {
        document.getElementById('city-input').value = m.name;
        closeCitySmartDropdown();
        selectMosque(m);
      };
      frag.appendChild(div);
    });
  }
  dd.innerHTML = '';
  dd.appendChild(frag);
  dd.classList.add('show');
}

// Navigate to mosque on map + highlight
function selectMosque(m) {
  bumpVisitTrafficCount(m);
  bumpCitySearchHistory({
    query: m.name,
    title: m.name,
    subtitle: getMosqueHierarchyLine(m),
    kind: 'mosque',
    lat: m.lat,
    lng: m.lng,
    osmType: m.osmType || 'way',
    osmId: m.id
  });
  const dropdown = document.getElementById('ms-dropdown');
  dropdown.classList.remove('show');
  document.getElementById('city-input').value = m.name;
  closeCitySmartDropdown();
  const targetZoom = Math.max(map.getZoom(), 17);
  mosqueFilter = '';
  document.getElementById('ms-banner').classList.remove('show');
  map.once('moveend', () => {
    scheduleViewportLoad(80);
    setTimeout(() => handleMosqueClick(m), 120);
  });
  focusMapLatLng(m.lat, m.lng, targetZoom, { duration:0.65 });
}

// Filter the sidebar list + show banner
function applyMosqueFilter(q) {
  mosqueFilter = q;
  const banner  = document.getElementById('ms-banner');
  const visible = getVisibleMosques(0.1);

  if (!q) {
    banner.classList.remove('show');
    updateList(visible);
    return;
  }

  const filtered = rankVisibleMosquesByQuery(visible, q);

  document.getElementById('ms-banner-text').textContent = `"${q}" — ${filtered.length} sonuç`;
  banner.classList.add('show');
  updateList(filtered);
}

function clearMosqueSearch() {
  document.getElementById('mosque-search').value = '';
  document.getElementById('mosque-search').classList.remove('has-value');
  document.getElementById('ms-clear').classList.remove('show');
  document.getElementById('ms-dropdown').classList.remove('show');
  mosqueFilter = '';
  document.getElementById('ms-banner').classList.remove('show');
  // Restore full list
  if (mosqueDB.size && map) {
    const visible = getVisibleMosques(0.1);
    updateList(visible);
  }
}

// Highlight matching substrings (supports multi-word)
function highlightMatch(name, q) {
  if (!q || !name) return escHtml(name || '');
  const words = trLower(q).split(/\s+/).filter(w => w.length > 1);
  if (!words.length) return escHtml(name);

  // Build a char-level "highlight" map
  const lower = trLower(name);
  const marked = new Uint8Array(name.length); // 1 = highlighted

  for (const w of words) {
    let pos = 0;
    while (pos < lower.length) {
      const idx = lower.indexOf(w, pos);
      if (idx < 0) break;
      for (let i = idx; i < Math.min(idx + w.length, name.length); i++) marked[i] = 1;
      pos = idx + 1;
    }
    // Normalized fallback
    if (!marked.some(Boolean)) {
      const normName = normalize(lower);
      const normW    = normalize(w);
      let p = 0;
      while (p < normName.length) {
        const idx = normName.indexOf(normW, p);
        if (idx < 0) break;
        for (let i = idx; i < Math.min(idx + normW.length, name.length); i++) marked[i] = 1;
        p = idx + 1;
      }
    }
  }

  // Build output string from mark map
  let out = '', inMark = false;
  for (let i = 0; i < name.length; i++) {
    if (marked[i] && !inMark) { out += '<mark>'; inMark = true; }
    if (!marked[i] && inMark) { out += '</mark>'; inMark = false; }
    out += escHtml(name[i]);
  }
  if (inMark) out += '</mark>';
  return out || escHtml(name);
}

// Turkish-aware lowercase (fixes İ→i, I→ı issues)
function trLower(s) {
  return s.replace(/İ/g,'i').replace(/I/g,'ı')
          .replace(/Ğ/g,'ğ').replace(/Ü/g,'ü')
          .replace(/Ş/g,'ş').replace(/Ö/g,'ö')
          .replace(/Ç/g,'ç').toLowerCase();
}

// Normalize Turkish chars for fuzzy matching (ı→i, ğ→g etc.)
function normalize(s) {
  return s.replace(/ı/g,'i').replace(/ğ/g,'g').replace(/ü/g,'u')
          .replace(/ş/g,'s').replace(/ö/g,'o').replace(/ç/g,'c')
          .replace(/İ/g,'i').replace(/Ğ/g,'g').replace(/Ü/g,'u')
          .replace(/Ş/g,'s').replace(/Ö/g,'o').replace(/Ç/g,'c');
}

// ── Status indicators
function setVpStatus(s){
  const dot=document.getElementById('vp-dot'),lbl=document.getElementById('vp-label');
  const box=document.getElementById('live-vp-badge') || document.querySelector('.vp-status');
  dot.className='vp-dot'+(s==='loading'?' loading':s==='done'?' done':'');
  if (box) box.className=`live-vp-badge ${s==='loading'?'loading':s==='done'?'done':'idle'}`;
  lbl.textContent=s==='loading'?'Canlı yükleniyor':s==='done'?'Canlı güncel':'Canlı hazır';
}
function updateCacheUI(){
  const count = tileCache.size;
  const cacheEl = document.getElementById('cache-count');
  if (cacheEl) cacheEl.textContent = count;
  const metaEl = document.getElementById('vp-meta');
  if (metaEl) metaEl.textContent = `Cache: ${count} tile`;
}
function showMini(t){ document.getElementById('mini-text').textContent=t; document.getElementById('mini-loader').classList.add('show'); }
function hideMini(){ document.getElementById('mini-loader').classList.remove('show'); }

function setOv(show,text='',sub=''){
  document.getElementById('overlay').style.display=show?'flex':'none';
  if(show){
    document.getElementById('ov-text').textContent=text;
    document.getElementById('ov-sub').textContent=sub;
  }
  syncSearchCancelUi();
}
function toast(msg,ms=5000){
  const t=document.getElementById('toast');
  t.textContent=msg;
  t.classList.add('show');
  if (/(hata|error||başarısız|failed)/i.test(String(msg || ''))) haptic(10);
  setTimeout(()=>t.classList.remove('show'),ms);
}

// ══════════════════════════════════════════════════════════════
//  SEARCH & LOAD
// ══════════════════════════════════════════════════════════════
async function doSearch(){
  if(!map) return;
  const v=document.getElementById('city-input').value.trim();
  if(!v) return;
  if (activeSearchController) cancelActiveSearch({ silent:true });
  const searchCtrl = new AbortController();
  activeSearchController = searchCtrl;
  const searchSignal = searchCtrl.signal;
  syncSearchCancelUi();
  closeCitySmartDropdown();
  const mq = document.getElementById('mob-quick-city');
  if (mq) mq.value = v;
  const mosqueMode = isLikelyMosqueQuery(v);
  const aliasHints = findAliasGroupsForQuery(normalize(trLower(v)));
  const smart = rankMosqueCandidates(v, 1, { scopeViewportOnly:false }).ranked[0] || null;
  if (!mosqueMode && smart && isStrongSmartSelection(v, smart, aliasHints)) {
    selectMosque(smart.m);
    return;
  }
  const direct = parseDirectMosqueQuery(v);
  try{
    throwIfAborted(searchSignal);
    clearDistrictSelection(true);
    updateDistrictUi();
    if (mosqueMode && !direct) {
      const local = rankMosqueCandidates(v, 250, { scopeViewportOnly:false }).ranked;
      if (local.length) {
        document.getElementById('mosque-search').value = v;
        document.getElementById('mosque-search').classList.add('has-value');
        document.getElementById('ms-clear').classList.add('show');
        applyMosqueFilter(v);
        showMosqueDropdown(v);
        queuePopularityHydration(local, () => {
          if (mosqueFilter === v) applyMosqueFilter(v);
          const qNow = document.getElementById('mosque-search')?.value?.trim();
          if (qNow === v) showMosqueDropdown(v);
        });
        toast(`"${v}" için ${local.length} cami listelendi`, 2200);
        setOv(false);
        return;
      }
      setOv(true, `"${v}" aranıyor...`, 'Cami verisi dış kaynaklarda taranıyor');
      const added = await triggerRemoteMosqueLookup(v, normalize(trLower(v)), map?.getBounds?.(), { preferGlobal:true });
      throwIfAborted(searchSignal);
      if (added > 0) {
        const found = rankMosqueCandidates(v, 250, { scopeViewportOnly:false }).ranked;
        if (found.length) {
          document.getElementById('mosque-search').value = v;
          document.getElementById('mosque-search').classList.add('has-value');
          document.getElementById('ms-clear').classList.add('show');
          applyMosqueFilter(v);
          showMosqueDropdown(v);
          queuePopularityHydration(found, () => {
            if (mosqueFilter === v) applyMosqueFilter(v);
            const qNow = document.getElementById('mosque-search')?.value?.trim();
            if (qNow === v) showMosqueDropdown(v);
          });
          toast(`"${v}" için ${found.length} cami listelendi`, 2400);
          setOv(false);
          return;
        }
      }
      setOv(false);
    }
    if (direct) {
      setOv(true, `"${v}" aranıyor...`, 'Doğrudan kayıt sorgusu');
      tileCache.clear(); updateCacheUI();
      mosqueDB.clear();
      renderLayers.forEach(l=>{ try{map.removeLayer(l);}catch{} }); renderLayers=[];
      const items = direct.type === 'osm'
        ? await fetchByOsmId(direct.osmType, direct.id, { signal:searchSignal })
        : await fetchByWikidataQid(direct.qid, { signal:searchSignal });
      throwIfAborted(searchSignal);
      processElements(items || []);
      if (mosqueDB.size) {
        const first = [...mosqueDB.values()][0];
        focusMapLatLng(first.lat, first.lng, 18, { fly:false });
        renderAll();
        triggerAggressiveNameEnrichment();
        setTimeout(() => handleMosqueClick(first), 120);
        toast(`${mosqueDB.size} kayıt bulundu`, 2500);
      } else {
        toast('Doğrudan sorguda kayıt bulunamadı', 3500);
      }
      setOv(false);
      return;
    }

    setOv(true,`"${v}" aranıyor...`,'Koordinatlar alınıyor');
    const loc=await geocode(v, { signal:searchSignal });
    throwIfAborted(searchSignal);
    bumpCitySearchHistory({
      query: v,
      title: v,
      subtitle: 'Şehir/Bölge araması',
      kind: mosqueMode ? 'mosque' : 'place',
      lat: loc.lat,
      lng: loc.lng,
      bbox: loc.bbox
    });
    currentCity = v;
    if (mosqueMode) {
      focusMapLatLng(loc.lat, loc.lng, 17, { fly:false });
    } else if (loc.bbox && loc.bbox.length === 4 && loc.bbox.every(Number.isFinite)) {
      const s = loc.bbox[0], n = loc.bbox[1], w = loc.bbox[2], e = loc.bbox[3];
      if (Math.abs(n-s) > 0.001 && Math.abs(e-w) > 0.001) fitBoundsWithUiPadding([[s,w],[n,e]]);
      else focusMapLatLng(loc.lat, loc.lng, 14, { fly:false });
    } else {
      focusMapLatLng(loc.lat, loc.lng, 14, { fly:false });
    }
    searchAreaAnchor = { lat:loc.lat, lng:loc.lng };
    hideSearchAreaButton();
    // Clear cache for fresh city load
    tileCache.clear(); updateCacheUI();
    mosqueDB.clear();
    renderLayers.forEach(l=>{ try{map.removeLayer(l);}catch{} }); renderLayers=[];
    if(heatLayer){ try{map.removeLayer(heatLayer);}catch{} heatLayer=null; }
    // İlk viewport yüklemesi
    setOv(true,`"${v}" yükleniyor...`,'Harita görünümündeki camiler alınıyor');
    await loadViewport({
      signal: searchSignal,
      batchSize: 12,
      concurrency: 3,
      fetchPolicy: { retries:1, timeoutMs:18000, backoffMs:650, minInterval:320, signal: searchSignal }
    });
    throwIfAborted(searchSignal);

    if (mosqueMode && !mosqueDB.size) {
      // Spesifik cami adı aramasında dar çevrede yoğun dene
      const near = await fetchCityFallback(loc.lat, loc.lng, { signal:searchSignal });
      throwIfAborted(searchSignal);
      if (near.length) {
        processElements(near);
        renderAll();
      }
    }

    // Fallback: görünümde hiç veri gelmezse şehir merkezi etrafında genişleyerek dene.
    if (!mosqueDB.size) {
      setOv(true,`"${v}" için geniş arama...`,'Farklı etiketler ve daha geniş alan taranıyor');
      const fallback = await fetchCityFallback(loc.lat, loc.lng, { signal:searchSignal });
      throwIfAborted(searchSignal);
      if (fallback.length) {
        processElements(fallback);
        renderAll();
      }
    }

    // Sorgu bir cami adıysa en iyi eşleşmeyi odakla
    if (mosqueMode && mosqueDB.size) {
      const best = findBestMosqueByName(v);
      if (best) {
        focusMapLatLng(best.lat, best.lng, Math.max(map.getZoom(), 17));
        setTimeout(() => handleMosqueClick(best), 140);
      }
    }
    if (mosqueDB.size) triggerAggressiveNameEnrichment();

    setOv(false);
    if (!mosqueDB.size) {
      toast('Bu şehir için OSM üzerinde cami verisi bulunamadı. Yazımı/ülke adını kontrol edin.', 7000);
    } else {
      haptic(20);
      toast(`${mosqueDB.size} cami kaydı yüklendi`, 2800);
      saveSnapshot();
    }
    updateHashFromMap();
  } catch(e){
    if (e?.name === 'AbortError') {
      setOv(false);
      return;
    }
    setOv(false);
    toast('Hata: '+e.message,7000);
    console.error(e);
  } finally {
    if (activeSearchController === searchCtrl) {
      activeSearchController = null;
      syncSearchCancelUi();
    }
  }
}

function geoErrorMessage(err) {
  if (!err || typeof err.code !== 'number') return 'Konum alınamadı';
  if (err.code === 1) return 'Konum izni kapalı. Tarayıcıdan konum iznini açın.';
  if (err.code === 2) return 'Konum kaynağı bulunamadı (GPS/ağ).';
  if (err.code === 3) return 'Konum isteği zaman aşımına uğradı.';
  return 'Konum alınamadı';
}

function getCurrentPositionAsync(options) {
  return new Promise((resolve, reject) => {
    navigator.geolocation.getCurrentPosition(resolve, reject, options);
  });
}

function watchPositionFirstFixAsync(options = {}, hardTimeoutMs = 22000) {
  return new Promise((resolve, reject) => {
    let done = false;
    const finish = (fn, payload) => {
      if (done) return;
      done = true;
      try { navigator.geolocation.clearWatch(watchId); } catch {}
      clearTimeout(timer);
      fn(payload);
    };
    const watchId = navigator.geolocation.watchPosition(
      pos => finish(resolve, pos),
      err => {
        if (err?.code === 1) finish(reject, err);
      },
      options
    );
    const timer = setTimeout(() => finish(reject, { code:3, message:'watch timeout' }), hardTimeoutMs);
  });
}

async function useMyLocation(opts = {}){
  const showToast = opts.showToast !== false;
  const zoom = Number.isFinite(opts.zoom) ? opts.zoom : 14;
  const source = opts.source || 'manual';
  if(!navigator.geolocation){
    if (showToast) toast('Konum desteklenmiyor');
    return false;
  }
  try {
    let pos = null;
    try {
      pos = await getCurrentPositionAsync({ enableHighAccuracy:true, timeout:12000, maximumAge:120000 });
    } catch (e1) {
      // Fallback: lower accuracy but wider timeout works better on some mobile networks.
      if (e1?.code === 2 || e1?.code === 3) {
        try {
          pos = await getCurrentPositionAsync({ enableHighAccuracy:false, timeout:22000, maximumAge:600000 });
        } catch {
          // Last fallback: wait for first watchPosition fix.
          pos = await watchPositionFirstFixAsync({ enableHighAccuracy:false, maximumAge:0, timeout:15000 }, 24000);
        }
      } else {
        throw e1;
      }
    }
    if(!map) return false;
    setUserGeoState(pos.coords.latitude, pos.coords.longitude, true);
    focusMapLatLng(pos.coords.latitude, pos.coords.longitude, zoom, { fly:false });
    tileCache.clear(); mosqueDB.clear();
    renderLayers.forEach(l=>{ try{map.removeLayer(l);}catch{} }); renderLayers=[];
    updateCacheUI();
    await loadViewport();
    if (showToast && source === 'manual') toast('Konum tespit edildi', 1800);
    return true;
  } catch (err) {
    if (source === 'auto' && err?.code === 1) safeStorageSet(GEO_PROMPT_KEY, 'denied');
    if (showToast) toast(geoErrorMessage(err), 3600);
    return false;
  }
}

async function resetToHome() {
  if (!map) return;
  try {
    if (followState.enabled) stopFollowLock(true);
    if (dpOpen) closeDetailPanel();
    closeMobDrawer?.();
    clearMosqueSearch?.();
    clearDistrictSelection?.(true);
    districtState.enabled = false;
    updateDistrictUi?.();
    hideQiblaPanel?.();
    map.closePopup();
    document.getElementById('city-input').value = '';
    const mq = document.getElementById('mob-quick-city');
    if (mq) mq.value = '';
    currentCity = '';
    tileCache.clear();
    mosqueDB.clear();
    renderLayers.forEach(l=>{ try{map.removeLayer(l);}catch{} });
    renderLayers = [];
    if(heatLayer){ try{map.removeLayer(heatLayer);}catch{} heatLayer=null; }
    updateCacheUI();
    _hashUpdating = true;
    history.replaceState(null, '', location.pathname);
    map.setView([41.015, 28.979], 13, { animate:true });
    _hashUpdating = false;
    clearTimeout(vpDebounceTimer);
    scheduleViewportLoad(280);
    toast('Ana sayfa sıfırlandı', 1800);
  } catch {}
}

function toggleOutdoorMode() {
  uiState.outdoor = !uiState.outdoor;
  document.body.classList.toggle('outdoor-mode', uiState.outdoor);
  document.getElementById('btn-outdoor')?.classList.toggle('active', uiState.outdoor);
  document.getElementById('mob-btn-outdoor')?.classList.toggle('active', uiState.outdoor);
  safeStorageSet(OUTDOOR_KEY, uiState.outdoor ? '1' : '0');
  toast(uiState.outdoor ? 'Outdoor mod aktif' : 'Outdoor mod kapatıldı', 1800);
}

function updateFollowUi() {
  document.getElementById('btn-follow')?.classList.toggle('active', followState.enabled);
  document.getElementById('mob-btn-follow')?.classList.toggle('active', followState.enabled);
}

function stopFollowLock(silent = false) {
  if (followState.watchId != null && navigator.geolocation) {
    navigator.geolocation.clearWatch(followState.watchId);
  }
  followState.watchId = null;
  followState.enabled = false;
  updateFollowUi();
  if (!silent) toast('Takip kilidi kapatıldı', 1800);
}

function startFollowLock() {
  if (!navigator.geolocation) { toast('Konum desteği yok', 2200); return; }
  if (followState.enabled) return;
  followState.enabled = true;
  updateFollowUi();
  followState.watchId = navigator.geolocation.watchPosition(pos => {
    if (!map) return;
    followState.lastFixAt = Date.now();
    const lat = pos.coords.latitude;
    const lng = pos.coords.longitude;
    setUserGeoState(lat, lng, true);
    const z = Math.max(16, map.getZoom() || 16);
    map.setView([lat, lng], z, { animate:false });
  }, () => {
    stopFollowLock(true);
    toast('Takip için konum alınamadı', 2600);
  }, { enableHighAccuracy:true, maximumAge:5000, timeout:12000 });
  toast('Takip kilidi aktif: manuel kaydırınca kapanır', 2200);
}

function toggleFollowLock() {
  if (followState.enabled) stopFollowLock();
  else startFollowLock();
}

function toggleMapCompassSync() {
  uiState.mapSyncWithCompass = !uiState.mapSyncWithCompass;
  if (!uiState.mapSyncWithCompass && uiState.liveMapCompass) uiState.liveMapCompass = false;
  document.getElementById('btn-map-sync')?.classList.toggle('active', uiState.mapSyncWithCompass);
  if (!uiState.mapSyncWithCompass) applyMapHeadingRotation(null);
  toast(uiState.mapSyncWithCompass ? 'Pusula-harita senkronu aktif' : 'Pusula-harita senkronu kapalı', 1800);
  updateCompassFabUi();
}

function applyMapHeadingRotation(heading) {
  if (!map) return;
  const paneNames = ['tilePane', 'overlayPane', 'shadowPane', 'markerPane', 'popupPane'];
  paneNames.forEach(name => {
    const pane = map[name] || map['_' + name];
    if (!pane || !pane.style) return;
    const raw = pane.style.transform || '';
    const base = raw.replace(/\s?rotate\([^)]*\)/g, '');
    if (!uiState.mapSyncWithCompass || heading == null) {
      pane.style.transform = base;
      return;
    }
    pane.style.transform = `${base} rotate(${-heading.toFixed(1)}deg)`;
  });
}

function isCompassModalOpen() {
  return document.getElementById('cmps-overlay')?.classList.contains('show');
}

function updateCompassFabUi() {
  document.getElementById('compass-fab')?.classList.toggle('active', !!uiState.liveMapCompass);
}

async function toggleLiveMapCompass() {
  if (uiState.liveMapCompass) {
    uiState.liveMapCompass = false;
    uiState.mapSyncWithCompass = false;
    document.getElementById('btn-map-sync')?.classList.remove('active');
    applyMapHeadingRotation(null);
    if (!isCompassModalOpen()) stopCompass();
    updateCompassFabUi();
    toast('Canlı pusula modu kapatıldı', 1600);
    return;
  }
  const granted = await requestCompassPermission();
  if (!granted) {
    uiState.liveMapCompass = false;
    uiState.mapSyncWithCompass = false;
    updateCompassFabUi();
    return;
  }
  uiState.liveMapCompass = true;
  uiState.mapSyncWithCompass = true;
  document.getElementById('btn-map-sync')?.classList.add('active');
  updateCompassFabUi();
  toast('Canlı pusula modu aktif', 1600);
}

async function loadNearbyCitySuggestions(showToastMsg = true) {
  const list = document.getElementById('city-suggest-list');
  if (!list) return;
  if (!navigator.geolocation) {
    if (showToastMsg) toast('Yakın şehir önerileri için konum desteği yok', 2600);
    return;
  }
  try {
    const pos = await new Promise((res, rej) => navigator.geolocation.getCurrentPosition(res, rej, { enableHighAccuracy:false, timeout:9000, maximumAge:150000 }));
    const lat = pos.coords.latitude, lng = pos.coords.longitude;
    const probes = [
      [lat, lng], [lat + 0.28, lng], [lat - 0.28, lng], [lat, lng + 0.35], [lat, lng - 0.35]
    ];
    const out = [];
    const seen = new Set();
    for (const [la, ln] of probes) {
      const url = `https://nominatim.openstreetmap.org/reverse?lat=${la}&lon=${ln}&format=jsonv2&zoom=10&addressdetails=1`;
      let d = null;
      try { d = await nominatimFetchJson(url, {'Accept-Language':'tr,en'}); } catch {}
      const a = d?.address || {};
      const cands = [a.city, a.town, a.county, a.state, a.village].filter(Boolean);
      for (const c of cands) {
        const k = trLower(String(c));
        if (seen.has(k)) continue;
        seen.add(k);
        out.push(String(c));
      }
    }
    list.innerHTML = out.slice(0, 10).map(x => `<option value="${escHtml(x)}"></option>`).join('');
    if (showToastMsg) toast(out.length ? `Yakın şehir önerileri güncellendi (${out.length})` : 'Yakın şehir önerisi bulunamadı', 2300);
  } catch {
    if (showToastMsg) toast('Yakın şehir önerisi alınamadı', 2200);
  }
}

async function refreshCurrentViewport() {
  if (!map || !mosqueDB.size) return;
  if (uiState.pullRefreshing) return;
  uiState.pullRefreshing = true;
  const ind = document.getElementById('sb-pull-indicator');
  if (ind) { ind.textContent = 'Yenileniyor...'; ind.classList.add('show','visible'); }
  tileCache.clear();
  updateCacheUI();
  await loadViewport();
  recompute();
  if (ind) {
    setTimeout(() => {
      ind.classList.remove('visible');
      setTimeout(() => ind.classList.remove('show'), 180);
      ind.textContent = 'Bırakınca yenilenecek';
    }, 380);
  }
  uiState.pullRefreshing = false;
  toast('Veriler güncellendi', 1600);
}

function initSidebarPullToRefresh() {
  const listEl = document.getElementById('mosque-list');
  const ind = document.getElementById('sb-pull-indicator');
  if (!listEl || !ind) return;
  let sy = 0, pulling = false;
  listEl.addEventListener('touchstart', e => {
    if (window.innerWidth > 768) return;
    if (listEl.scrollTop > 0) return;
    sy = e.touches[0].clientY;
    pulling = true;
  }, {passive:true});
  listEl.addEventListener('touchmove', e => {
    if (!pulling) return;
    const dy = e.touches[0].clientY - sy;
    if (dy > 8) {
      ind.classList.add('show');
      ind.classList.toggle('visible', dy > 34);
      ind.textContent = dy > 76 ? 'Bırakınca yenilenecek' : 'Aşağı çek...';
    }
  }, {passive:true});
  listEl.addEventListener('touchend', async e => {
    if (!pulling) return;
    const dy = e.changedTouches[0].clientY - sy;
    pulling = false;
    if (dy > 76) await refreshCurrentViewport();
    else {
      ind.classList.remove('visible');
      setTimeout(() => ind.classList.remove('show'), 160);
      ind.textContent = 'Bırakınca yenilenecek';
    }
  }, {passive:true});
}

function setSidebarSnap(vh) {
  const sb = document.querySelector('.sidebar');
  if (!sb || window.innerWidth > 768) return;
  uiState.sheetSnap = Math.max(MOBILE_SHEET_SNAP.min, Math.min(MOBILE_SHEET_SNAP.full, vh));
  sb.style.setProperty('--sheet-snap', uiState.sheetSnap);
  const snapState = uiState.sheetSnap <= 30 ? 'min' : uiState.sheetSnap <= 72 ? 'half' : 'full';
  sb.setAttribute('data-snap', snapState);
  mobileSheetSnapIdx = snapState === 'min' ? 0 : snapState === 'half' ? 1 : 2;
  updateSidebarSnapPanels();
  syncMobileMapLayout();
}

function getMobileSheetVisiblePx() {
  if (window.innerWidth > 768) return 0;
  const sb = document.querySelector('.sidebar');
  if (!sb) return 0;
  const cs = getComputedStyle(sb);
  if (cs.display === 'none' || cs.visibility === 'hidden') return 0;
  return Math.round(window.innerHeight * (uiState.sheetSnap / 100));
}

function ensureSelectedMosqueVisibleOnMobile(m, opts = {}) {
  if (!map || !m || window.innerWidth > 768) return;
  const dp = document.getElementById('dp-panel');
  if (dp?.classList.contains('open')) return;
  const sheetPx = getMobileSheetVisiblePx();
  if (sheetPx < 8) return;
  const zoom = map.getZoom();
  const size = map.getSize();
  const markerPt = map.project([m.lat, m.lng], zoom);
  const centerPt = map.project(map.getCenter(), zoom);
  const markerScreenY = markerPt.y - centerPt.y + (size.y / 2);
  const topOfSheetY = size.y - sheetPx;
  const desiredY = Math.min(size.y * 0.42, Math.max(84, topOfSheetY - 36));
  if (markerScreenY <= topOfSheetY - 18 && markerScreenY >= 52) return;
  const nextCenterPt = L.point(centerPt.x, markerPt.y + (size.y / 2) - desiredY);
  const nextCenter = map.unproject(nextCenterPt, zoom);
  map.panTo(nextCenter, { animate: opts.animate !== false, duration:0.38, noMoveStart:true });
}

function syncMobileMapLayout() {
  if (!map) return;
  if (mobileSheetSyncTimer) clearTimeout(mobileSheetSyncTimer);
  const apply = (animate = false) => {
    const cont = map.getContainer?.();
    if (!cont) return;
    const px = getMobileSheetVisiblePx();
    const changed = Math.abs(px - lastSidebarVisiblePx);
    lastSidebarVisiblePx = px;
    cont.style.setProperty('--mobile-sheet-offset', `${Math.max(74, px + 10)}px`);
    if (window._lastClickedMosque && changed >= 8) {
      ensureSelectedMosqueVisibleOnMobile(window._lastClickedMosque, { animate });
    }
  };
  apply(false);
  mobileSheetSyncTimer = setTimeout(() => apply(true), 320);
}

function initSidebarSnapSheet() {
  const sb = document.querySelector('.sidebar');
  const head = document.getElementById('sb-head-handle');
  if (!sb || !head) return;
  const snaps = [MOBILE_SHEET_SNAP.min, MOBILE_SHEET_SNAP.half, MOBILE_SHEET_SNAP.full];
  mobileSheetSnapIdx = Math.max(0, Math.min(snaps.length - 1, mobileSheetSnapIdx));
  setSidebarSnap(snaps[mobileSheetSnapIdx]);
  head.onclick = () => {
    if (window.innerWidth > 768) return;
    mobileSheetSnapIdx = (mobileSheetSnapIdx + 1) % snaps.length;
    setSidebarSnap(snaps[mobileSheetSnapIdx]);
  };
  let sy = 0;
  head.addEventListener('touchstart', e => { sy = e.touches[0].clientY; }, {passive:true});
  head.addEventListener('touchend', e => {
    if (window.innerWidth > 768) return;
    const dy = e.changedTouches[0].clientY - sy;
    if (dy < -30) mobileSheetSnapIdx = Math.min(snaps.length - 1, mobileSheetSnapIdx + 1);
    if (dy > 30) mobileSheetSnapIdx = Math.max(0, mobileSheetSnapIdx - 1);
    setSidebarSnap(snaps[mobileSheetSnapIdx]);
  }, {passive:true});
  if (!initSidebarSnapSheet._boundResize) {
    window.addEventListener('resize', () => syncMobileMapLayout());
    window.addEventListener('orientationchange', () => setTimeout(() => syncMobileMapLayout(), 160));
    initSidebarSnapSheet._boundResize = true;
  }
}

window.addEventListener('DOMContentLoaded', bootstrap);



// ══════════════════════════════════════════════════════════════
//  COMPARISON MODE (Adım 3)
// ══════════════════════════════════════════════════════════════
const compareDBA = new Map();
const compareDBB = new Map();
const compareAreaTotals = { a:null, b:null };
const comparePlaceMeta = { a:null, b:null };
const compareLoaded = { a:false, b:false };

function openCompare() {
  document.getElementById('cmp-overlay').classList.add('show');
  document.getElementById('btn-compare').classList.add('active');
  document.getElementById('cmp-a-name').textContent = comparePlaceMeta.a?.label || '—';
  document.getElementById('cmp-b-name').textContent = comparePlaceMeta.b?.label || '—';
  document.getElementById('cmp-tol').textContent = tol + '°';
  const aInput = document.getElementById('cmp-a-input');
  if (aInput && !aInput.value && currentCity) aInput.value = currentCity;
  if (compareLoaded.a || compareLoaded.b) renderCompare();
}

function closeCompare() {
  document.getElementById('cmp-overlay').classList.remove('show');
  document.getElementById('btn-compare').classList.remove('active');
}

function cmpOverlayClick(e) {
  if (e.target === document.getElementById('cmp-overlay')) closeCompare();
}

function compareLevelLabel(level) {
  return level === 'district' ? 'İlçe' : 'Şehir';
}

function scoreCompareGeocode(item, query, level = 'city') {
  const q = trLower(query || '');
  const disp = trLower(item.display_name || '');
  const type = trLower(item.type || '');
  const cls = trLower(item.class || '');
  const addr = item.address || {};
  let s = Number(item.importance || 0) * 100;
  if (disp.includes(q)) s += 20;
  if (disp.startsWith(q + ',')) s += 35;
  if (cls === 'boundary' || cls === 'place') s += 18;
  const cityTypes = new Set(['city','town','village','municipality','county','state','province']);
  const districtTypes = new Set(['district','city_district','borough','suburb','quarter','neighbourhood']);
  if (level === 'district') {
    if (districtTypes.has(type)) s += 65;
    if (addr.city_district || addr.district || addr.suburb || addr.neighbourhood || addr.quarter) s += 24;
  } else {
    if (cityTypes.has(type)) s += 65;
    if (addr.city || addr.town || addr.county || addr.state || addr.province) s += 24;
  }
  return s;
}

function normalizeComparePlace(item, level) {
  const address = item?.address || {};
  const city = address.city || address.town || address.county || address.state || address.province || '';
  const district = address.city_district || address.district || address.suburb || address.neighbourhood || address.quarter || '';
  const levelVal = level || 'city';
  const label = levelVal === 'district'
    ? [district, city].filter(Boolean).join(', ') || (item.display_name || '').split(',').slice(0,2).join(',').trim()
    : city || (item.display_name || '').split(',')[0].trim();
  return {
    query: item.display_name || '',
    level: levelVal,
    label: label || '—',
    city,
    district,
    country: address.country || '',
    lat: +item.lat,
    lng: +item.lon,
    bbox: Array.isArray(item.boundingbox) ? item.boundingbox.map(Number) : null,
    osmType: String(item.osm_type || '').toLowerCase(),
    osmClass: String(item.class || '').toLowerCase(),
    osmId: Number(item.osm_id),
    rawType: String(item.type || '').toLowerCase()
  };
}

async function geocodeComparePlace(name, level = 'city') {
  const url = `https://nominatim.openstreetmap.org/search?q=${encodeURIComponent(name)}&format=jsonv2&limit=12&addressdetails=1`;
  const data = await nominatimFetchJson(url, {'Accept-Language':'tr,en'});
  if (!Array.isArray(data) || !data.length) throw new Error('Yer bulunamadı');
  const ranked = data.map(it => ({ it, s: scoreCompareGeocode(it, name, level) })).sort((a,b) => b.s - a.s);
  return normalizeComparePlace(ranked[0].it, level);
}

function overpassAreaIdFromPlace(place) {
  if (!place || !Number.isFinite(place.osmId)) return null;
  if (place.osmType === 'relation') return 3600000000 + place.osmId;
  if (place.osmType === 'way') return 2400000000 + place.osmId;
  return null;
}

function parseOverpassCountTotal(elements = []) {
  const countEl = (elements || []).find(x => x?.type === 'count') || (elements || [])[0];
  const tags = countEl?.tags || {};
  const direct = Number(tags.total);
  if (Number.isFinite(direct)) return direct;
  const sum = Number(tags.nodes || 0) + Number(tags.ways || 0) + Number(tags.relations || 0);
  return Number.isFinite(sum) ? sum : null;
}

function buildMosqueCountAreaQuery(areaId) {
  return `[out:json][timeout:75];
area(${areaId})->.a;
(
  nwr["amenity"="place_of_worship"]["religion"~"muslim|islam",i](area.a);
  nwr["amenity"="mosque"](area.a);
  nwr["building"="mosque"](area.a);
  nwr["place_of_worship"="mosque"](area.a);
  nwr["mosque"](area.a);
);
out count;`;
}

function buildMosqueCountBboxQuery(s,w,n,e) {
  return `[out:json][timeout:60];
(
  nwr["amenity"="place_of_worship"]["religion"~"muslim|islam",i](${s},${w},${n},${e});
  nwr["amenity"="mosque"](${s},${w},${n},${e});
  nwr["building"="mosque"](${s},${w},${n},${e});
  nwr["place_of_worship"="mosque"](${s},${w},${n},${e});
  nwr["mosque"](${s},${w},${n},${e});
);
out count;`;
}

async function fetchAreaMosqueTotal(place) {
  const areaId = overpassAreaIdFromPlace(place);
  if (areaId) {
    const els = await fetchOverpassQuery(buildMosqueCountAreaQuery(areaId), { retries:1, timeoutMs:30000, minInterval:320, backoffMs:700 });
    const total = parseOverpassCountTotal(els);
    if (Number.isFinite(total)) return total;
  }
  if (Array.isArray(place.bbox) && place.bbox.length === 4) {
    const [s,n,w,e] = place.bbox;
    const els = await fetchOverpassQuery(buildMosqueCountBboxQuery(s,w,n,e), { retries:1, timeoutMs:26000, minInterval:320, backoffMs:700 });
    const total = parseOverpassCountTotal(els);
    if (Number.isFinite(total)) return total;
  }
  return null;
}

// Compute score stats from a Map of mosques
function computeStats(db) {
  const all = [...db.values()];
  const withData = all.filter(m => m.diff !== null);
  const correct  = withData.filter(m => m.diff <= tol);
  const wrong    = withData.filter(m => m.diff > tol);
  const unknown  = all.filter(m => m.diff === null);
  const pct = withData.length ? Math.round(correct.length / withData.length * 100) : null;
  const diffs = withData.map(m => m.diff);
  const avg = diffs.length ? diffs.reduce((a,b)=>a+b,0)/diffs.length : null;
  const max = diffs.length ? Math.max(...diffs) : null;
  const min = diffs.length ? Math.min(...diffs) : null;
  const sorted = [...diffs].sort((a,b)=>a-b);
  const median = sorted.length ? sorted[Math.floor(sorted.length/2)] : null;
  const perfect = withData.filter(m => m.diff < 5).length;
  const grade = pct===null?'—':pct>=85?'A':pct>=65?'B':pct>=45?'C':'D';
  return { all:all.length, withData:withData.length, correct:correct.length, wrong:wrong.length,
           unknown:unknown.length, pct, avg, max, min, median, perfect, grade };
}

function processElementsToCompareMap(elements, outMap) {
  outMap.clear();
  for (const el of elements || []) {
    let lat0 = null, lng0 = null, polyCoords = null;
    if (el.type === 'node') {
      lat0 = el.lat; lng0 = el.lon;
    } else if ((el.type === 'way' || el.type === 'relation') && Array.isArray(el.geometry) && el.geometry.length >= 2) {
      const pts = el.geometry;
      lat0 = pts.reduce((s,p)=>s+p.lat,0)/pts.length;
      lng0 = pts.reduce((s,p)=>s+p.lon,0)/pts.length;
      polyCoords = pts.map(p => [p.lat, p.lon]);
    } else if ((el.type === 'way' || el.type === 'relation') && el.center) {
      lat0 = el.center.lat; lng0 = el.center.lon;
    }
    if (!Number.isFinite(lat0) || !Number.isFinite(lng0)) continue;
    const qibla = qiblaAngle(lat0, lng0);
    let axis = null, diff = null, method = 'none';
    const tags = el.tags || {};
    const dt = tags.direction || tags['building:direction'];
    if (dt && !isNaN(+dt)) {
      axis = (+dt % 180 + 180) % 180;
      diff = angDiff180(qibla % 180, axis);
      method = 'osm-tag';
    } else if (polyCoords && polyCoords.length >= 4) {
      const res = buildingQiblaEdge(polyCoords, qibla);
      if (res) { axis = res.angle; diff = res.diff; method = 'edge-analysis'; }
    }
    outMap.set(`${el.type}:${el.id}`, {
      id: el.id,
      osmType: el.type,
      name: pickNameFromTags(tags) || buildTagsAddressFallbackName(tags, el.id),
      lat: lat0,
      lng: lng0,
      qibla, axis, diff, method,
      status: diff!==null ? (diff<=tol ? 'correct' : 'wrong') : 'unknown'
    });
  }
}

async function fetchCompareSide(side) {
  const input = document.getElementById(`cmp-${side}-input`);
  const levelEl = document.getElementById(`cmp-${side}-level`);
  const statusEl = document.getElementById(`cmp-${side}-status`);
  const nameEl = document.getElementById(`cmp-${side}-name`);
  const btn = document.getElementById(`cmp-${side}-fetch-btn`);
  const v = input?.value?.trim() || '';
  const level = levelEl?.value === 'district' ? 'district' : 'city';
  if (!v || !btn || !statusEl || !nameEl) return;

  const mapRef = side === 'a' ? compareDBA : compareDBB;
  btn.disabled = true;
  statusEl.textContent = 'Koordinatlar alınıyor...';
  document.getElementById('cmp-progress-wrap').style.display = 'block';
  document.getElementById('cmp-progress-bar').style.width = '10%';
  document.getElementById('cmp-progress-label').textContent = `${side.toUpperCase()} · "${v}" aranıyor...`;
  document.getElementById('cmp-results').style.display = 'none';

  try {
    const place = await geocodeComparePlace(v, level);
    comparePlaceMeta[side] = place;
    nameEl.textContent = place.label;

    document.getElementById('cmp-progress-bar').style.width = '35%';
    document.getElementById('cmp-progress-label').textContent = `${side.toUpperCase()} · Toplam cami sayısı hesaplanıyor...`;

    const totalPromise = fetchAreaMosqueTotal(place).catch(() => null);
    const r = level === 'district' ? 0.022 : 0.036;
    const elements = await fetchBbox(place.lat-r, place.lng-r, place.lat+r, place.lng+r, { retries:1, timeoutMs:22000, backoffMs:650, minInterval:320 });
    document.getElementById('cmp-progress-bar').style.width = '75%';
    document.getElementById('cmp-progress-label').textContent = `${side.toUpperCase()} · ${elements.length} kayıt işleniyor...`;

    processElementsToCompareMap(elements, mapRef);
    compareAreaTotals[side] = await totalPromise;
    compareLoaded[side] = true;
    statusEl.textContent = ` ${compareLevelLabel(level)} yüklendi · analiz:${mapRef.size} · toplam:${compareAreaTotals[side] ?? '—'}`;

    document.getElementById('cmp-progress-bar').style.width = '100%';
    await new Promise(r => setTimeout(r, 280));
    document.getElementById('cmp-progress-wrap').style.display = 'none';
    renderCompare();
  } catch (err) {
    document.getElementById('cmp-progress-wrap').style.display = 'none';
    statusEl.textContent = ' Hata: ' + err.message;
    toast('Karşılaştırma yüklenirken hata: ' + err.message, 5000);
  }
  btn.disabled = false;
}

function clearCompareSide(side) {
  const mapRef = side === 'a' ? compareDBA : compareDBB;
  mapRef.clear();
  compareAreaTotals[side] = null;
  comparePlaceMeta[side] = null;
  compareLoaded[side] = false;
  const nameEl = document.getElementById(`cmp-${side}-name`);
  const statusEl = document.getElementById(`cmp-${side}-status`);
  const input = document.getElementById(`cmp-${side}-input`);
  if (nameEl) nameEl.textContent = '—';
  if (statusEl) statusEl.textContent = '';
  if (input) input.value = '';
  renderCompare();
}

function fillScoreBlock(ab, city, st) {
  document.getElementById(`cmp-${ab}-pct`).textContent  = st.pct!==null ? st.pct+'%' : '—';
  document.getElementById(`cmp-${ab}-label`).textContent = city;
  const g = document.getElementById(`cmp-${ab}-grade`);
  g.textContent = st.grade==='—'?'':
    st.grade==='A'?'A — Mükemmel':st.grade==='B'?'B — İyi':st.grade==='C'?'C — Orta':'D — Zayıf';
  g.className = 'cmp-score-grade'+(st.grade!=='—'?' '+st.grade:'');
  drawSmallDonut(`cmp-${ab}-donut`, st, ab==='a'?'#60a5fa':'#f472b6');
}

function buildBarRow(m) {
  const div = document.createElement('div');
  div.className = 'cmp-bar-row';
  const aVal = m.a ?? 0, bVal = m.b ?? 0;
  const maxVal = Math.max(aVal, bVal, 1);
  const aPct = Math.round(aVal/maxVal*100), bPct = Math.round(bVal/maxVal*100);
  const aWin = m.higherBetter===null ? null : (m.higherBetter ? aVal>=bVal : aVal<=bVal);
  const aC = aWin===null?'rgba(255,255,255,.50)':aWin?'#60a5fa':'#60a5fa66';
  const bC = aWin===null?'rgba(255,255,255,.50)':!aWin?'#f472b6':'#f472b666';
  div.innerHTML = `
    <div class="cmp-bar-label">${m.label}</div>
    <div>
      <div style="font-size:9px;color:rgba(255,255,255,.50);margin-bottom:3px">A: ${m.a!==null&&m.a!==undefined?m.a+(m.unit):'—'}</div>
      <div class="cmp-bar-outer"><div class="cmp-bar-inner" style="width:${aPct}%;background:${aC}">${aPct>20?m.a+(m.unit):''}</div></div>
    </div>
    <div>
      <div style="font-size:9px;color:rgba(255,255,255,.50);margin-bottom:3px">B: ${m.b!==null&&m.b!==undefined?m.b+(m.unit):'—'}</div>
      <div class="cmp-bar-outer"><div class="cmp-bar-inner" style="width:${bPct}%;background:${bC}">${bPct>20?m.b+(m.unit):''}</div></div>
    </div>`;
  return div;
}

function drawSmallDonut(canvasId, st, color) {
  const canvas = document.getElementById(canvasId);
  if (!canvas) return;
  const ctx = canvas.getContext('2d');
  ctx.clearRect(0,0,80,80);
  const cx=40, cy=40, r=34;
  if (!st.withData) {
    ctx.beginPath(); ctx.arc(cx,cy,r,0,Math.PI*2);
    ctx.strokeStyle='#6a9ec9'; ctx.lineWidth=10; ctx.stroke(); return;
  }
  const slices = [
    {val:st.correct, color:color},
    {val:st.wrong,   color:color+'44'},
    {val:st.unknown, color:'#6a9ec9'}
  ].filter(s=>s.val>0);
  let angle = -Math.PI/2;
  const total = st.all;
  for (const s of slices) {
    const sw = (s.val/total)*Math.PI*2;
    ctx.beginPath(); ctx.arc(cx,cy,r,angle,angle+sw);
    ctx.strokeStyle=s.color; ctx.lineWidth=10; ctx.lineCap='butt'; ctx.stroke();
    angle+=sw;
  }
}

function drawRadar(stA, stB) {
  const canvas = document.getElementById('cmp-radar');
  if (!canvas) return;
  const ctx = canvas.getContext('2d');
  ctx.clearRect(0,0,200,200);
  const cx=100, cy=100, r=72;
  // 5 axes: Doğruluk, Mükemmel<5°, Düşük Sapma, Veri Kapsamı, Düşük Maks
  const axes = ['Doğruluk','Mükemmel','Düşük Ort.','Kapsam','Düşük Maks'];
  const n = axes.length;

  function normalize(val, min, max) {
    if (val===null||val===undefined) return 0;
    return Math.max(0, Math.min(1, (val-min)/(max-min)));
  }

  const aScores = [
    normalize(stA.pct,0,100),
    normalize(stA.perfect,0,Math.max(stA.perfect,stB?.perfect??0,1)),
    normalize(stA.avg!==null?90-stA.avg:0,0,90),
    normalize(stA.withData,0,Math.max(stA.withData,stB?.withData??0,1)),
    normalize(stA.max!==null?90-stA.max:0,0,90),
  ];
  const bScores = stB ? [
    normalize(stB.pct,0,100),
    normalize(stB.perfect,0,Math.max(stA.perfect,stB.perfect,1)),
    normalize(stB.avg!==null?90-stB.avg:0,0,90),
    normalize(stB.withData,0,Math.max(stA.withData,stB.withData,1)),
    normalize(stB.max!==null?90-stB.max:0,0,90),
  ] : null;

  // Draw grid rings
  for (let ring=1; ring<=4; ring++) {
    ctx.beginPath();
    for (let i=0; i<n; i++) {
      const angle = (i/n)*Math.PI*2 - Math.PI/2;
      const x = cx + Math.cos(angle)*r*(ring/4);
      const y = cy + Math.sin(angle)*r*(ring/4);
      i===0 ? ctx.moveTo(x,y) : ctx.lineTo(x,y);
    }
    ctx.closePath();
    ctx.strokeStyle = '#6a9ec9'; ctx.lineWidth=1; ctx.stroke();
  }

  // Draw axes
  for (let i=0; i<n; i++) {
    const angle = (i/n)*Math.PI*2 - Math.PI/2;
    ctx.beginPath();
    ctx.moveTo(cx, cy);
    ctx.lineTo(cx+Math.cos(angle)*r, cy+Math.sin(angle)*r);
    ctx.strokeStyle='#6a9ec9'; ctx.lineWidth=1; ctx.stroke();
    // Labels
    const lx = cx+Math.cos(angle)*(r+14), ly = cy+Math.sin(angle)*(r+14);
    ctx.fillStyle='rgba(255,255,255,.50)'; ctx.font='9px Manrope,monospace';
    ctx.textAlign='center'; ctx.textBaseline='middle';
    ctx.fillText(axes[i], lx, ly);
  }

  // Draw city B polygon first (under A)
  if (bScores) {
    ctx.beginPath();
    for (let i=0; i<n; i++) {
      const angle = (i/n)*Math.PI*2 - Math.PI/2;
      const x = cx + Math.cos(angle)*r*bScores[i];
      const y = cy + Math.sin(angle)*r*bScores[i];
      i===0 ? ctx.moveTo(x,y) : ctx.lineTo(x,y);
    }
    ctx.closePath();
    ctx.fillStyle='rgba(244,114,182,.12)'; ctx.fill();
    ctx.strokeStyle='#f472b6'; ctx.lineWidth=2; ctx.stroke();
  }

  // Draw city A polygon
  ctx.beginPath();
  for (let i=0; i<n; i++) {
    const angle = (i/n)*Math.PI*2 - Math.PI/2;
    const x = cx + Math.cos(angle)*r*aScores[i];
    const y = cy + Math.sin(angle)*r*aScores[i];
    i===0 ? ctx.moveTo(x,y) : ctx.lineTo(x,y);
  }
  ctx.closePath();
  ctx.fillStyle='rgba(96,165,250,.12)'; ctx.fill();
  ctx.strokeStyle='#60a5fa'; ctx.lineWidth=2; ctx.stroke();

  // Dots
  [aScores, bScores].forEach((scores, si) => {
    if (!scores) return;
    const col = si===0?'#60a5fa':'#f472b6';
    scores.forEach((v,i) => {
      const angle = (i/n)*Math.PI*2 - Math.PI/2;
      ctx.beginPath();
      ctx.arc(cx+Math.cos(angle)*r*v, cy+Math.sin(angle)*r*v, 3, 0, Math.PI*2);
      ctx.fillStyle=col; ctx.fill();
    });
  });
}

// Re-render comparison when tolerance changes or new data comes
// (called from recompute when modal is open)

function renderCompare() {
  if (!compareLoaded.a && !compareLoaded.b) {
    document.getElementById('cmp-results').style.display = 'none';
    return;
  }
  const stA = compareLoaded.a ? computeStats(compareDBA) : computeStats(new Map());
  const stB = compareLoaded.b ? computeStats(compareDBB) : null;
  const nameA = comparePlaceMeta.a?.label || 'A';
  const nameB = comparePlaceMeta.b?.label || 'B';

  document.getElementById('cmp-results').style.display = 'flex';
  document.getElementById('cmp-tol').textContent = tol + '°';
  document.getElementById('cmp-a-name').textContent = compareLoaded.a ? nameA : '—';
  document.getElementById('cmp-b-name').textContent = compareLoaded.b ? nameB : '—';

  // ── Score blocks
  fillScoreBlock('a', compareLoaded.a ? nameA : '—', stA);
  fillScoreBlock('b', compareLoaded.b ? nameB : '—', stB || computeStats(new Map()));

  // ── Winner badge
  const badge = document.getElementById('cmp-winner-badge');
  if (stB && stA.pct !== null && stB.pct !== null) {
    const diff = stA.pct - stB.pct;
    if (Math.abs(diff) <= 2)     { badge.textContent = ' Beraberlik';    badge.className = 'cmp-winner-badge tie'; }
    else if (diff > 0)           { badge.textContent = ` ${nameA} önde`; badge.className = 'cmp-winner-badge a'; }
    else                         { badge.textContent = ` ${nameB} önde`; badge.className = 'cmp-winner-badge b'; }
  } else {
    badge.textContent = compareLoaded.a && !compareLoaded.b ? 'B bekleniyor →' : (!compareLoaded.a && compareLoaded.b ? 'A bekleniyor →' : '');
    badge.className = 'cmp-winner-badge tie';
  }

  // ── Radar chart
  drawRadar(stA, stB);

  // ── Bar metrics
  const barsEl = document.getElementById('cmp-bars');
  barsEl.innerHTML = '';
  const metrics = [
    { label:'Doğruluk %',   a:stA.pct,     b:stB?.pct,     unit:'%', higherBetter:true  },
    { label:'Ort. Sapma',   a:stA.avg!==null?+stA.avg.toFixed(1):null, b:stB?.avg!==null?+stB.avg.toFixed(1):null, unit:'°', higherBetter:false },
    { label:'Maks. Sapma',  a:stA.max!==null?+stA.max.toFixed(1):null, b:stB?.max!==null?+stB.max.toFixed(1):null, unit:'°', higherBetter:false },
    { label:'Mükemmel <5°', a:stA.perfect,  b:stB?.perfect, unit:'', higherBetter:true  },
    { label:'Analiz Cami',  a:stA.all,      b:stB?.all,     unit:'', higherBetter:null  },
    { label:'Toplam Cami (OSM Alan)', a:compareAreaTotals.a, b:compareAreaTotals.b, unit:'', higherBetter:null  },
  ];
  metrics.forEach(m => barsEl.appendChild(buildBarRow(m)));

  // ── Detail table
  const tbl = document.getElementById('cmp-table');
  const fmtPct = v => v!==null&&v!==undefined ? v+'%' : '—';
  const fmtDeg = v => v!==null&&v!==undefined ? v.toFixed(1)+'°' : '—';
  const rows = [
    ['Bölge',          compareLoaded.a ? nameA : '—',              compareLoaded.b ? nameB : '—'],
    ['Bölge Tipi',     comparePlaceMeta.a?.level === 'district' ? 'İlçe' : (compareLoaded.a ? 'Şehir' : '—'), comparePlaceMeta.b?.level === 'district' ? 'İlçe' : (compareLoaded.b ? 'Şehir' : '—')],
    ['Toplam Cami (OSM Alan)', compareAreaTotals.a ?? '—', compareAreaTotals.b ?? '—'],
    ['Analiz Cami',    stA.all,                  stB?.all    ?? '—'],
    ['Veri Olan',      stA.withData,             stB?.withData ?? '—'],
    ['Doğru Yön',      stA.correct,              stB?.correct  ?? '—'],
    ['Sapma Var',      stA.wrong,                stB?.wrong    ?? '—'],
    ['Veri Yok',       stA.unknown,              stB?.unknown  ?? '—'],
    ['Doğruluk',       fmtPct(stA.pct),          fmtPct(stB?.pct)],
    ['Not',            stA.grade,                stB?.grade    ?? '—'],
    ['Ort. Sapma',     fmtDeg(stA.avg),          fmtDeg(stB?.avg)],
    ['Medyan Sapma',   fmtDeg(stA.median),       fmtDeg(stB?.median)],
    ['Min. Sapma',     fmtDeg(stA.min),          fmtDeg(stB?.min)],
    ['Maks. Sapma',    fmtDeg(stA.max),          fmtDeg(stB?.max)],
    ['Mükemmel (<5°)', stA.perfect,              stB?.perfect  ?? '—'],
  ];

  // Highlight winner in each numeric row
  const numericRows = new Set(['Toplam Cami','Veri Olan','Doğru Yön','Mükemmel (<5°)']);
  const lowerBetterRows = new Set(['Ort. Sapma','Medyan Sapma','Min. Sapma','Maks. Sapma','Sapma Var']);

  tbl.innerHTML = `<table class="cmp-tbl">
    <thead>
      <tr>
        <th>Metrik</th>
        <th style="color:#60a5fa">A: ${escHtml(compareLoaded.a ? nameA : '—')}</th>
        <th style="color:#f472b6">B: ${escHtml(compareLoaded.b ? nameB : '—')}</th>
      </tr>
    </thead>
    <tbody>
      ${rows.map(([label, va, vb]) => {
        let aStyle = 'color:#e8e4d8', bStyle = 'color:#e8e4d8';
        if (stB) {
          const aNum = parseFloat(va), bNum = parseFloat(vb);
          if (!isNaN(aNum) && !isNaN(bNum) && aNum !== bNum) {
            const aWins = lowerBetterRows.has(label) ? aNum < bNum : aNum > bNum;
            if (aWins) { aStyle='color:#60a5fa;font-weight:700'; bStyle='color:rgba(255,255,255,.50)'; }
            else       { bStyle='color:#f472b6;font-weight:700'; aStyle='color:rgba(255,255,255,.50)'; }
          }
        }
        return `<tr>
          <td style="color:rgba(255,255,255,.50)">${escHtml(label)}</td>
          <td style="${aStyle}">${escHtml(va)}</td>
          <td style="${bStyle}">${escHtml(vb)}</td>
        </tr>`;
      }).join('')}
    </tbody>
  </table>`;
}



// ══════════════════════════════════════════════════════════════
//  HISTORICAL ANALYSIS (Adım 4)
// ══════════════════════════════════════════════════════════════

// Period definitions
const PERIODS = {
  ottoman: { label:'Osmanlı',      range:[0,    1922], color:'#a78bfa', cls:'ottoman' },
  early:   { label:'Erken Cum.',   range:[1923, 1950], color:'#fbbf24', cls:'early'   },
  mid:     { label:'Orta Dönem',   range:[1951, 2000], color:'#60a5fa', cls:'mid'     },
  modern:  { label:'Modern',       range:[2001, 9999], color:'#4ade80', cls:'modern'  },
  unknown: { label:'Bilinmiyor',   range:null,         color:'rgba(255,255,255,.50)', cls:'unknown' },
};

let historyModeActive = false;
let histPeriodFilter = 'all';

// Parse OSM date tags to year (handles "1453", "1453-04", "1890s", "ca.1800" etc.)
function parseYear(tag) {
  if (!tag) return null;
  const clean = String(tag).replace(/[caCa. ]/g,'');
  // try full match
  const m = clean.match(/(\d{4})/);
  if (m) {
    const y = parseInt(m[1]);
    return (y > 600 && y <= 2030) ? y : null;
  }
  return null;
}

function classifyPeriod(year) {
  if (year === null) return 'unknown';
  if (year <= 1922) return 'ottoman';
  if (year <= 1950) return 'early';
  if (year <= 2000) return 'mid';
  return 'modern';
}

function getPeriodColor(period) {
  return PERIODS[period]?.color ?? 'rgba(255,255,255,.50)';
}

// Enrich each mosque in DB with period info
function enrichWithPeriod() {
  mosqueDB.forEach(m => {
    if (m.period !== undefined) return; // already done
    const year = parseYear(m.startDate);
    m.year = year;
    m.period = classifyPeriod(year);
  });
}

function toggleHistoryMode() {
  historyModeActive = !historyModeActive;
  const btn = document.getElementById('btn-history');
  btn.classList.toggle('active', historyModeActive);

  if (historyModeActive) {
    document.getElementById('hist-overlay').classList.add('show');
    enrichWithPeriod();
    renderHistoryModal();
    // Switch map colors to period mode
    applyPeriodColors();
  } else {
    closeHistoryMode();
  }
}

function closeHistoryMode() {
  historyModeActive = false;
  document.getElementById('hist-overlay').classList.remove('show');
  document.getElementById('btn-history').classList.remove('active');
  histPeriodFilter = 'all';
  // Restore normal colors
  renderAll();
}

function histOverlayClick(e) {
  if (e.target === document.getElementById('hist-overlay')) closeHistoryMode();
}

// Re-color map markers by period instead of correct/wrong
function applyPeriodColors() {
  enrichWithPeriod();
  // Re-render with period colors override
  renderLayers.forEach(l => { try{map.removeLayer(l);}catch{} });
  renderLayers = [];

  const bounds = map.getBounds().pad(0.1);
  const visible = [...mosqueDB.values()].filter(m => bounds.contains([m.lat, m.lng]));

  for (const m of visible) {
    const col = getPeriodColor(m.period);
    const dimmed = histPeriodFilter !== 'all' && m.period !== histPeriodFilter;
    const opacity = dimmed ? 0.12 : 0.95;

    if (m.polyCoords) {
      const poly = L.polygon(m.polyCoords, {
        color:col, weight:1.5, fillColor:col, fillOpacity:dimmed?0.02:0.08, opacity:dimmed?0.15:0.45
      }).addTo(map);
      poly.on('click', () => handleMosqueClick(m));
      renderLayers.push(poly);
    }

    const qEnd = destination(m.lat, m.lng, m.qibla, 200);
    renderLayers.push(L.polyline([[m.lat,m.lng],[qEnd.lat,qEnd.lng]], {
      color:'#c9a84c', weight:1.5, opacity:dimmed?0.08:0.5, dashArray:'6 5'
    }).addTo(map));

    if (m.axis !== null && !dimmed) {
      const fd = closestDirection(m.axis, m.qibla);
      const e1 = destination(m.lat, m.lng, fd, 90);
      const e2 = destination(m.lat, m.lng, (fd+180)%360, 90);
      renderLayers.push(L.polyline([[e2.lat,e2.lng],[e1.lat,e1.lng]], {
        color:col, weight:2.5, opacity:0.9
      }).addTo(map));
    }

    const mk = L.circleMarker([m.lat,m.lng], {
      radius:5, fillColor:col, color:'#164773', weight:1.5, fillOpacity:opacity
    }).addTo(map);
    mk.mosque = m;
    mk.bindPopup(makeHistoryPopup(m));
    mk.on('click', () => handleMosqueClick(m));
    renderLayers.push(mk);
  }
}

function makeHistoryPopup(m) {
  const col = getPeriodColor(m.period);
  const period = PERIODS[m.period];
  const yearStr = m.year ? m.year + ' yılı' : 'Tarih bilinmiyor';
  const statusStr = m.status==='correct'?' Doğru':m.status==='wrong'?' Sapma':' Veri yok';
  return `<div class="p-name">${escHtml(m.name)}</div>
    <div class="p-row"><span class="p-k">Dönem</span><span style="color:${col};font-weight:700">${period.label}</span></div>
    <div class="p-row"><span class="p-k">İnşaat</span><span class="p-v">${yearStr}</span></div>
    <div class="p-row"><span class="p-k">Durum</span><span class="p-v">${statusStr}</span></div>
    <div class="p-row"><span class="p-k">Kıble</span><span class="p-v">${m.qibla.toFixed(1)}°</span></div>
    ${m.diff!==null?`<div class="p-row"><span class="p-k">Sapma</span><span class="p-v">${m.diff.toFixed(1)}°</span></div>`:''}
    <button class="p-anim-btn" onclick="animateFromPopup(${m.id})"> Büyük Daire Animasyonu</button>`;
}

// Compute per-period stats
function computePeriodStats() {
  const stats = {};
  for (const key of Object.keys(PERIODS)) {
    stats[key] = { count:0, withData:0, correct:0, wrong:0, diffs:[], years:[] };
  }
  mosqueDB.forEach(m => {
    const s = stats[m.period];
    s.count++;
    if (m.diff !== null) {
      s.withData++;
      if (m.status === 'correct') s.correct++;
      else s.wrong++;
      s.diffs.push(m.diff);
    }
    if (m.year) s.years.push(m.year);
  });
  // Compute derived
  for (const key of Object.keys(stats)) {
    const s = stats[key];
    s.pct = s.withData ? Math.round(s.correct / s.withData * 100) : null;
    s.avg = s.diffs.length ? s.diffs.reduce((a,b)=>a+b,0)/s.diffs.length : null;
    s.max = s.diffs.length ? Math.max(...s.diffs) : null;
    const sorted = [...s.diffs].sort((a,b)=>a-b);
    s.median = sorted.length ? sorted[Math.floor(sorted.length/2)] : null;
    s.yearMin = s.years.length ? Math.min(...s.years) : null;
    s.yearMax = s.years.length ? Math.max(...s.years) : null;
  }
  return stats;
}

function renderHistoryModal() {
  enrichWithPeriod();
  const stats = computePeriodStats();
  histPeriodFilter = histPeriodFilter || 'all';
  updateHistChips();
  renderHistCards(stats);
  drawHistBarChart(stats);
  drawHistScatter();
  renderHistTable(stats);
  renderHistList();
}

function updateHistChips() {
  document.querySelectorAll('.hist-chip').forEach(c => {
    c.classList.toggle('active', c.dataset.period === histPeriodFilter);
  });
}

function filterPeriod(period) {
  histPeriodFilter = period;
  updateHistChips();
  renderHistList();
  if (historyModeActive) applyPeriodColors();
  // Highlight selected card
  document.querySelectorAll('.hist-card').forEach(c => {
    c.style.transform = c.dataset.period === period || period === 'all' ? '' : 'scale(.97)';
    c.style.opacity = c.dataset.period === period || period === 'all' ? '1' : '.45';
  });
}

function renderHistCards(stats) {
  const el = document.getElementById('hist-cards');
  const order = ['ottoman','early','mid','modern','unknown'];
  el.innerHTML = order.map(key => {
    const s = stats[key];
    const p = PERIODS[key];
    const pctStr = s.pct !== null ? s.pct + '%' : '—';
    const avgStr = s.avg !== null ? s.avg.toFixed(1) + '° ort.' : 'veri yok';
    return `<div class="hist-card ${key}" data-period="${key}" onclick="filterPeriod('${key}')" style="cursor:pointer">
      <div class="hist-card-period">${p.label}</div>
      <div class="hist-card-count">${s.count}</div>
      <div class="hist-card-pct">${pctStr} doğru</div>
      <div class="hist-card-avg">${avgStr}</div>
    </div>`;
  }).join('');
}

function drawHistBarChart(stats) {
  const canvas = document.getElementById('hist-chart');
  canvas.width = canvas.offsetWidth || 800;
  const ctx = canvas.getContext('2d');
  ctx.clearRect(0,0,canvas.width,canvas.height);

  const order = ['ottoman','early','mid','modern'];
  const W = canvas.width, H = canvas.height;
  const pad = {l:50, r:20, t:16, b:36};
  const chartW = W - pad.l - pad.r;
  const chartH = H - pad.t - pad.b;
  const barW = Math.floor(chartW / order.length * 0.55);
  const gap = Math.floor(chartW / order.length);

  // Grid lines
  for (let pct = 0; pct <= 100; pct += 25) {
    const y = pad.t + chartH - (pct/100)*chartH;
    ctx.strokeStyle = '#275d8d'; ctx.lineWidth = 1;
    ctx.beginPath(); ctx.moveTo(pad.l, y); ctx.lineTo(W-pad.r, y); ctx.stroke();
    ctx.fillStyle = 'rgba(255,255,255,.50)'; ctx.font = '9px Manrope,monospace';
    ctx.textAlign = 'right';
    ctx.fillText(pct+'%', pad.l-6, y+3);
  }

  order.forEach((key, i) => {
    const s = stats[key];
    const p = PERIODS[key];
    const x = pad.l + i*gap + (gap - barW)/2;
    const pct = s.pct ?? 0;
    const barH = (pct/100) * chartH;
    const y = pad.t + chartH - barH;

    // Bar background
    ctx.fillStyle = '#225786';
    ctx.fillRect(x, pad.t, barW, chartH);

    // Bar fill with gradient
    const grad = ctx.createLinearGradient(x, y, x, pad.t+chartH);
    grad.addColorStop(0, p.color);
    grad.addColorStop(1, p.color+'55');
    ctx.fillStyle = grad;
    ctx.fillRect(x, y, barW, barH);

    // Average deviation overlay (secondary bar, red scale)
    if (s.avg !== null) {
      const avgNorm = Math.min(s.avg / 45, 1);
      const avgBarH = avgNorm * chartH;
      ctx.fillStyle = 'rgba(248,113,113,0.25)';
      ctx.fillRect(x + barW + 3, pad.t + chartH - avgBarH, 5, avgBarH);
    }

    // Label
    ctx.fillStyle = '#e8e4d8'; ctx.font = 'bold 11px Manrope,monospace';
    ctx.textAlign = 'center';
    if (pct > 0) ctx.fillText(pct+'%', x + barW/2, y - 5);

    // Period name
    ctx.fillStyle = p.color; ctx.font = '9px Manrope,monospace';
    ctx.fillText(p.label, x + barW/2, H - 6);

    // Count
    ctx.fillStyle = 'rgba(255,255,255,.50)'; ctx.font = '8px Manrope,monospace';
    ctx.fillText('n='+s.count, x + barW/2, H - 18);
  });

  // Legend: red bar = avg deviation
  ctx.fillStyle = 'rgba(248,113,113,0.5)';
  ctx.fillRect(pad.l, pad.t + 2, 8, 8);
  ctx.fillStyle = 'rgba(255,255,255,.50)'; ctx.font = '8px Manrope,monospace'; ctx.textAlign = 'left';
  ctx.fillText('■ ort. sapma (yardımcı)', pad.l + 12, pad.t + 10);
}

function drawHistScatter() {
  const canvas = document.getElementById('hist-scatter');
  canvas.width = canvas.offsetWidth || 800;
  const ctx = canvas.getContext('2d');
  ctx.clearRect(0, 0, canvas.width, canvas.height);

  // Collect points: {year, diff, period}
  const points = [];
  mosqueDB.forEach(m => {
    if (m.year && m.diff !== null) points.push({year:m.year, diff:m.diff, period:m.period});
  });
  if (!points.length) {
    ctx.fillStyle = 'rgba(255,255,255,.50)'; ctx.font = '11px Manrope,monospace'; ctx.textAlign = 'center';
    ctx.fillText('Tarih + sapma verisi olan cami bulunamadı', canvas.width/2, canvas.height/2);
    return;
  }

  const W = canvas.width, H = canvas.height;
  const pad = {l:44, r:16, t:12, b:30};
  const chartW = W-pad.l-pad.r, chartH = H-pad.t-pad.b;

  const years = points.map(p=>p.year);
  const minY = Math.min(...years), maxY = Math.max(...years, minY+1);
  const maxDiff = Math.max(...points.map(p=>p.diff), 1);

  // Grid
  for (let d=0; d<=45; d+=15) {
    const y = pad.t + chartH - (d/maxDiff)*chartH;
    ctx.strokeStyle='#275d8d'; ctx.lineWidth=1;
    ctx.beginPath(); ctx.moveTo(pad.l,y); ctx.lineTo(W-pad.r,y); ctx.stroke();
    ctx.fillStyle='rgba(255,255,255,.50)'; ctx.font='8px Manrope,monospace'; ctx.textAlign='right';
    ctx.fillText(d+'°', pad.l-4, y+3);
  }

  // Tolerance line
  const tolY = pad.t + chartH - (tol/maxDiff)*chartH;
  ctx.strokeStyle='rgba(201,168,76,.35)'; ctx.lineWidth=1; ctx.setLineDash([4,4]);
  ctx.beginPath(); ctx.moveTo(pad.l,tolY); ctx.lineTo(W-pad.r,tolY); ctx.stroke();
  ctx.setLineDash([]);
  ctx.fillStyle='rgba(201,168,76,.5)'; ctx.font='8px Manrope,monospace'; ctx.textAlign='left';
  ctx.fillText('tolerans '+tol+'°', pad.l+4, tolY-3);

  // X axis years
  const yearStep = Math.ceil((maxY-minY)/5 / 50)*50 || 50;
  for (let y=Math.ceil(minY/yearStep)*yearStep; y<=maxY; y+=yearStep) {
    const x = pad.l + ((y-minY)/(maxY-minY))*chartW;
    ctx.fillStyle='rgba(255,255,255,.50)'; ctx.font='8px Manrope,monospace'; ctx.textAlign='center';
    ctx.fillText(y, x, H-6);
  }

  // Points
  for (const pt of points) {
    const x = pad.l + ((pt.year-minY)/Math.max(maxY-minY,1))*chartW;
    const y = pad.t + chartH - (pt.diff/maxDiff)*chartH;
    const col = getPeriodColor(pt.period);
    ctx.beginPath(); ctx.arc(x, y, 3.5, 0, Math.PI*2);
    ctx.fillStyle = col+'cc'; ctx.fill();
    ctx.strokeStyle = col; ctx.lineWidth = 0.8; ctx.stroke();
  }

  // Trend line (linear regression)
  if (points.length > 3) {
    const n = points.length;
    const sx = points.reduce((a,p)=>a+p.year,0);
    const sy = points.reduce((a,p)=>a+p.diff,0);
    const sxy = points.reduce((a,p)=>a+p.year*p.diff,0);
    const sxx = points.reduce((a,p)=>a+p.year*p.year,0);
    const slope = (n*sxy - sx*sy) / (n*sxx - sx*sx);
    const intercept = (sy - slope*sx) / n;
    const x1=pad.l, y1=pad.t+chartH-(((slope*minY+intercept)/maxDiff)*chartH);
    const x2=W-pad.r, y2=pad.t+chartH-(((slope*maxY+intercept)/maxDiff)*chartH);
    ctx.strokeStyle='rgba(255,255,255,.2)'; ctx.lineWidth=1.5; ctx.setLineDash([3,5]);
    ctx.beginPath(); ctx.moveTo(x1,y1); ctx.lineTo(x2,y2); ctx.stroke();
    ctx.setLineDash([]);
    // Trend direction label
    const trendDir = slope > 0.01 ? '↑ Sapma artıyor' : slope < -0.01 ? '↓ Sapma azalıyor' : '→ Sabit';
    ctx.fillStyle='rgba(255,255,255,.5)'; ctx.font='9px Manrope,monospace'; ctx.textAlign='right';
    ctx.fillText(trendDir, W-pad.r-4, pad.t+10);
  }
}

function renderHistTable(stats) {
  const el = document.getElementById('hist-table');
  const order = ['ottoman','early','mid','modern','unknown'];
  el.innerHTML = `<table class="hist-tbl">
    <thead><tr>
      <th>Dönem</th><th>Tarih Aralığı</th><th>Cami</th>
      <th>Doğruluk</th><th>Ort. Sapma</th><th>Med. Sapma</th><th>Maks.</th>
    </tr></thead>
    <tbody>${order.map(key => {
      const s = stats[key]; const p = PERIODS[key];
      const range = key==='unknown' ? '—' :
        (s.yearMin && s.yearMax ? s.yearMin+(s.yearMin!==s.yearMax?'–'+s.yearMax:'') : p.range?p.range[0]+'–'+(p.range[1]===9999?'bugün':p.range[1]):'—');
      return `<tr>
        <td><span class="hist-period-badge ${key}">${p.label}</span></td>
        <td style="color:rgba(255,255,255,.50)">${range}</td>
        <td>${s.count}</td>
        <td style="color:${p.color};font-weight:700">${s.pct!==null?s.pct+'%':'—'}</td>
        <td>${s.avg!==null?s.avg.toFixed(1)+'°':'—'}</td>
        <td>${s.median!==null?s.median.toFixed(1)+'°':'—'}</td>
        <td style="color:#f87171">${s.max!==null?s.max.toFixed(1)+'°':'—'}</td>
      </tr>`;
    }).join('')}</tbody>
  </table>`;
}

function renderHistList() {
  const el = document.getElementById('hist-list');
  const label = document.getElementById('hist-list-label');
  const period = histPeriodFilter;

  let items = [...mosqueDB.values()];
  if (period !== 'all') items = items.filter(m => m.period === period);

  // Sort by diff descending (worst first), then unknown, then no year
  items.sort((a,b) => {
    if (a.diff===null && b.diff!==null) return 1;
    if (a.diff!==null && b.diff===null) return -1;
    if (a.diff===null && b.diff===null) return 0;
    return b.diff - a.diff;
  });

  const periodLabel = period === 'all' ? 'tüm dönemler' : PERIODS[period].label;
  label.textContent = `${periodLabel} — ${items.length} cami (en kötüden iyiye)`;

  if (!items.length) {
    el.innerHTML = '<div style="color:rgba(255,255,255,.50);font-size:11px;padding:12px">Bu dönemde cami bulunamadı</div>';
    return;
  }

  el.innerHTML = items.slice(0, 80).map(m => {
    const col = m.status==='correct'?'#4ade80':m.status==='wrong'?'#f87171':'#fbbf24';
    const pCol = getPeriodColor(m.period);
    const yearStr = m.year ? m.year : '?';
    return `<div class="hist-list-item" onclick="focusAndAnimate(${m.lat},${m.lng},'${m.id}')">
      <div class="hist-list-dot" style="background:${pCol}"></div>
      <div class="hist-list-name">${escHtml(m.name)}</div>
      <div class="hist-list-year" style="color:${pCol}">${yearStr}</div>
      <div class="hist-list-diff" style="color:${col}">${m.diff!==null?m.diff.toFixed(1)+'°':'—'}</div>
    </div>`;
  }).join('');
}

function focusAndAnimate(lat, lng, id) {
  const m = mosqueDB.get(id) || [...mosqueDB.values()].find(x=>String(x.id)===String(id));
  if (!m) return;
  focusMapLatLng(lat, lng, 17);
  handleMosqueClick(m);
}

// History mode is integrated directly into renderAll() and recompute()
// via typeof historyModeActive checks above.

// Canvas resize: redraw charts when modal becomes visible
document.getElementById('hist-modal').addEventListener('click', () => {
  // noop — charts draw on open
});



// ══════════════════════════════════════════════════════════════
//  EXPORT & HASH ROUTING (Adım 8)
// ══════════════════════════════════════════════════════════════

// ── Hash routing: #cityname/lat/lng/zoom
// Format: #istanbul/41.015/28.979/14  (URL-encoded city name)

let _hashUpdating = false; // prevent feedback loop

function buildShareUrl() {
  if (!map) return location.href;
  const c = map.getCenter();
  const z = map.getZoom();
  const city = encodeURIComponent(currentCity || '');
  const hash = `${city}/${c.lat.toFixed(4)}/${c.lng.toFixed(4)}/${z}`;
  return `${location.origin}${location.pathname}#${hash}`;
}

function updateHashFromMap() {
  if (!map || _hashUpdating) return;
  const c = map.getCenter();
  const z = map.getZoom();
  const city = encodeURIComponent(currentCity || '');
  const hash = `${city}/${c.lat.toFixed(4)}/${c.lng.toFixed(4)}/${z}`;
  history.replaceState(null, '', `#${hash}`);
}

function parseHash() {
  const hash = location.hash.slice(1);
  if (!hash) return null;
  const parts = hash.split('/');
  if (parts.length < 4) return null;
  try {
    return {
      city: decodeURIComponent(parts[0]),
      lat:  parseFloat(parts[1]),
      lng:  parseFloat(parts[2]),
      zoom: parseInt(parts[3])
    };
  } catch { return null; }
}

// ── Export modal
function openExport() {
  document.getElementById('exp-overlay').classList.add('show');
  document.getElementById('btn-export').classList.add('active');
  // Fill share URL
  document.getElementById('exp-url-input').value = buildShareUrl();
  // Fill summary
  renderExportSummary();
}

function closeExport() {
  document.getElementById('exp-overlay').classList.remove('show');
  document.getElementById('btn-export').classList.remove('active');
}

function expOverlayClick(e) {
  if (e.target === document.getElementById('exp-overlay')) closeExport();
}

// ── Business / monetization modal (no-auth flows)
function openBiz() {
  document.getElementById('biz-overlay').classList.add('show');
  document.getElementById('btn-biz').classList.add('active');
}

function closeBiz() {
  document.getElementById('biz-overlay').classList.remove('show');
  document.getElementById('btn-biz').classList.remove('active');
}

function bizOverlayClick(e) {
  if (e.target === document.getElementById('biz-overlay')) closeBiz();
}

function openLab() {
  document.getElementById('lab-overlay').classList.add('show');
  document.getElementById('btn-lab').classList.add('active');
  renderLab();
}
function closeLab() {
  document.getElementById('lab-overlay').classList.remove('show');
  document.getElementById('btn-lab').classList.remove('active');
}
function labOverlayClick(e) {
  if (e.target === document.getElementById('lab-overlay')) closeLab();
}

function generateInsights() {
  const all = [...mosqueDB.values()];
  if (!all.length) return [];
  const withData = all.filter(m => m.diff != null);
  const avg = withData.length ? (withData.reduce((s,m)=>s+m.diff,0)/withData.length) : null;
  const low = all.filter(m => (m.confidence || 0) < 55).length;
  const converted = all.filter(m => m.convertedFrom?.converted).length;
  const unnamed = all.filter(m => isPlaceholderMosqueName(m.name)).length;
  const manualPending = all.filter(m => getManualAxisRecord(m)?.moderation?.status === 'pending').length;
  return [
    ['Toplam cami', all.length],
    ['Veri kapsama', withData.length ? `${Math.round(withData.length/all.length*100)}%` : '0%'],
    ['Ort. sapma', avg != null ? `${avg.toFixed(1)}°` : '—'],
    ['Düşük güven', low],
    ['Dönüştürülmüş olası', converted],
    ['İsimsiz', unnamed],
    ['Manuel beklemede', manualPending]
  ];
}

function renderLab() {
  const insights = generateInsights();
  const iEl = document.getElementById('lab-insights');
  iEl.innerHTML = insights.map(([k,v]) => `<div class="lab-row"><span class="lab-k">${escHtml(k)}</span><span class="lab-v">${escHtml(v)}</span></div>`).join('');

  const queue = [...mosqueDB.values()]
    .filter(m => (m.confidence || 0) < 55 || isPlaceholderMosqueName(m.name) || m.convertedFrom?.converted || getManualAxisRecord(m)?.moderation?.status === 'pending')
    .sort((a,b) => (a.confidence || 0) - (b.confidence || 0))
    .slice(0, 20);
  const qEl = document.getElementById('lab-queue');
  if (!queue.length) qEl.innerHTML = '<div class="lab-row"><span class="lab-k">Kuyruk boş</span><span class="lab-v"></span></div>';
  else qEl.innerHTML = queue.map(m => `<div class="lab-row"><span class="lab-k">${escHtml(m.name)}</span><span class="lab-v">${m.confidence || 0}/100</span></div>`).join('');

  const sEl = document.getElementById('lab-snapshots');
  const recent = snapshots.slice().reverse().slice(0, 12);
  if (!recent.length) sEl.innerHTML = '<div class="lab-row"><span class="lab-k">Geçmiş yok</span><span class="lab-v">—</span></div>';
  else sEl.innerHTML = recent.map(s => `<div class="lab-row"><span class="lab-k">${escHtml(s.city)} · ${new Date(s.ts).toLocaleDateString('tr-TR')}</span><span class="lab-v">${s.pct ?? '—'}%</span></div>`).join('');
}

function bizSendLead() {
  const name = document.getElementById('biz-name').value.trim();
  const company = document.getElementById('biz-company').value.trim();
  const email = document.getElementById('biz-email').value.trim();
  const msg = document.getElementById('biz-msg').value.trim();
  const subject = encodeURIComponent('Kıble Dedektörü B2B / White-Label Talebi');
  const body = encodeURIComponent(
    `Ad Soyad: ${name || '-'}\n` +
    `Kurum: ${company || '-'}\n` +
    `E-posta: ${email || '-'}\n` +
    `\nİhtiyaç:\n${msg || '-'}\n` +
    `\nNot: Talep web formundan oluşturuldu.`
  );
  location.href = `mailto:sales@qibla-checker.app?subject=${subject}&body=${body}`;
}

function renderExportSummary() {
  const all = [...mosqueDB.values()];
  const withData = all.filter(m => m.diff !== null);
  const correct  = withData.filter(m => m.diff <= tol);
  const pct = withData.length ? Math.round(correct.length/withData.length*100) : null;

  document.getElementById('exp-summary').innerHTML = `
    <div class="exp-sum-card">
      <div class="exp-sum-val">${all.length}</div>
      <div class="exp-sum-lbl">Toplam Cami</div>
    </div>
    <div class="exp-sum-card">
      <div class="exp-sum-val" style="color:${pct!==null?(pct>=70?'#4ade80':pct>=40?'#fbbf24':'#f87171'):'rgba(255,255,255,.50)'}">${pct!==null?pct+'%':'—'}</div>
      <div class="exp-sum-lbl">Doğruluk</div>
    </div>
    <div class="exp-sum-card">
      <div class="exp-sum-val">${currentCity||'—'}</div>
      <div class="exp-sum-lbl">Şehir</div>
    </div>
  `;
}

function copyShareUrl() {
  const url = buildShareUrl();
  navigator.clipboard?.writeText(url).then(() => {
    const btn = document.getElementById('exp-copy-url');
    btn.textContent = ' Kopyalandı';
    btn.classList.add('copied');
    setTimeout(() => { btn.textContent = 'Kopyala'; btn.classList.remove('copied'); }, 2200);
  }).catch(() => {
    // Fallback: select the input
    document.getElementById('exp-url-input').select();
    document.execCommand('copy');
  });
}

// ── JSON export
function exportJSON() {
  const data = {
    meta: {
      city: currentCity,
      exportDate: new Date().toISOString(),
      tolerance: tol,
      source: 'OpenStreetMap',
      total: mosqueDB.size
    },
    mosques: [...mosqueDB.values()].map(m => ({
      id: m.id,
      osmType: m.osmType||'way',
      name: m.name,
      lat: m.lat,
      lng: m.lng,
      qiblaAngle: m.qibla,
      buildingAxis: m.axis,
      deviation: m.diff,
      status: m.status,
      method: m.method,
      constructionYear: m.year||null,
      period: m.period||null,
      tags: m.tags||{}
    }))
  };

  download(
    JSON.stringify(data, null, 2),
    `qibla-${slugify(currentCity)}-${dateStr()}.json`,
    'application/json'
  );
  toast(' JSON indirildi', 3000);
}

// ── CSV export
function exportCSV() {
  const headers = ['id','name','lat','lng','qibla_angle','building_axis','deviation_deg',
                   'status','method','construction_year','period'];
  const rows = [...mosqueDB.values()].map(m => [
    m.id,
    csvEsc(m.name),
    m.lat.toFixed(6),
    m.lng.toFixed(6),
    m.qibla.toFixed(2),
    m.axis!==null?m.axis.toFixed(2):'',
    m.diff!==null?m.diff.toFixed(2):'',
    m.status,
    m.method,
    m.year||'',
    m.period||''
  ]);

  const csv = [headers, ...rows].map(r => r.join(',')).join('\n');
  download(
    '\uFEFF' + csv, // BOM for Excel UTF-8
    `qibla-${slugify(currentCity)}-${dateStr()}.csv`,
    'text/csv;charset=utf-8'
  );
  toast(' CSV indirildi — Excel\'de açabilirsiniz', 3000);
}

// ── GeoJSON export
function exportGeoJSON() {
  const geojson = {
    type: 'FeatureCollection',
    metadata: {
      city: currentCity,
      exportDate: new Date().toISOString(),
      tolerance: tol
    },
    features: [...mosqueDB.values()].map(m => ({
      type: 'Feature',
      geometry: { type: 'Point', coordinates: [m.lng, m.lat] },
      properties: {
        id: m.id,
        name: m.name,
        qibla_angle: m.qibla,
        building_axis: m.axis,
        deviation_deg: m.diff,
        status: m.status,
        method: m.method,
        year: m.year||null,
        period: m.period||null,
        // Colour for QGIS styling
        fill_color: m.status==='correct'?'#4ade80':m.status==='wrong'?'#f87171':'#fbbf24'
      }
    }))
  };

  download(
    JSON.stringify(geojson, null, 2),
    `qibla-${slugify(currentCity)}-${dateStr()}.geojson`,
    'application/geo+json'
  );
  toast(' GeoJSON indirildi', 3000);
}

// ── HTML Report (opens in new tab)
function exportReport() {
  const all = [...mosqueDB.values()];
  const withData = all.filter(m => m.diff !== null);
  const correct  = withData.filter(m => m.diff <= tol);
  const wrong    = withData.filter(m => m.diff > tol);
  const pct = withData.length ? Math.round(correct.length/withData.length*100) : null;
  const avg = withData.length ? withData.reduce((s,m)=>s+m.diff,0)/withData.length : null;
  const grade = pct===null?'—':pct>=85?'A':pct>=65?'B':pct>=45?'C':'D';
  const gradeCol = {A:'#4ade80',B:'#a3e635',C:'#fbbf24',D:'#f87171','—':'rgba(255,255,255,.50)'}[grade];

  // Worst 15
  const worst = [...withData].sort((a,b)=>b.diff-a.diff).slice(0,15);
  // Best 10
  const best  = [...withData].sort((a,b)=>a.diff-b.diff).slice(0,10);

  const html = `<!DOCTYPE html>
<html lang="tr"><head><meta charset="UTF-8">
<title>Kıble Analiz Raporu — ${currentCity}</title>
<style>
*{margin:0;padding:0;box-sizing:border-box;}
body{font-family:'Segoe UI',sans-serif;background:#164773;color:#e8e4d8;padding:32px;max-width:900px;margin:0 auto;}
h1{font-size:24px;color:#c9a84c;margin-bottom:4px;}
.subtitle{color:rgba(255,255,255,.50);font-size:13px;margin-bottom:28px;}
.cards{display:grid;grid-template-columns:repeat(4,1fr);gap:12px;margin-bottom:28px;}
.card{background:#1b4f7f;border:1px solid #6a9ec9;border-radius:10px;padding:16px;text-align:center;}
.card-val{font-size:28px;font-weight:700;color:#c9a84c;}
.card-lbl{font-size:10px;color:rgba(255,255,255,.50);text-transform:uppercase;letter-spacing:.1em;margin-top:4px;}
h2{font-size:14px;color:#c9a84c;margin:22px 0 10px;letter-spacing:.08em;text-transform:uppercase;}
table{width:100%;border-collapse:collapse;font-size:12px;}
th{text-align:left;padding:8px 10px;background:#1b4f7f;color:rgba(255,255,255,.50);font-weight:500;border-bottom:1px solid #6a9ec9;}
td{padding:7px 10px;border-bottom:1px solid rgba(42,42,58,.4);color:#e8e4d8;}
.ok{color:#4ade80;font-weight:700;} .bad{color:#f87171;font-weight:700;} .unk{color:#fbbf24;}
.grade{display:inline-block;padding:2px 10px;border-radius:10px;font-weight:700;background:rgba(255,255,255,.07);}
footer{margin-top:32px;padding-top:12px;border-top:1px solid #6a9ec9;font-size:10px;color:rgba(255,255,255,.50);}
</style></head><body>
<h1> Kıble Analiz Raporu</h1>
<div class="subtitle">${currentCity} · ${new Date().toLocaleDateString('tr-TR',{day:'numeric',month:'long',year:'numeric'})} · Tolerans: ${tol}°</div>

<div class="cards">
  <div class="card"><div class="card-val">${all.length}</div><div class="card-lbl">Toplam Cami</div></div>
  <div class="card"><div class="card-val" style="color:${pct!==null?(pct>=70?'#4ade80':pct>=40?'#fbbf24':'#f87171'):'rgba(255,255,255,.50)'}">${pct!==null?pct+'%':'—'}</div><div class="card-lbl">Doğruluk</div></div>
  <div class="card"><div class="card-val" style="color:${gradeCol}">${grade}</div><div class="card-lbl">Not</div></div>
  <div class="card"><div class="card-val">${avg!==null?avg.toFixed(1)+'°':'—'}</div><div class="card-lbl">Ort. Sapma</div></div>
</div>

<h2>En Fazla Sapma Gösteren 15 Cami</h2>
<table>
  <thead><tr><th>#</th><th>Cami Adı</th><th>Kıble</th><th>Bina Yönü</th><th>Sapma</th><th>Durum</th></tr></thead>
  <tbody>${worst.map((m,i)=>`<tr>
    <td>${i+1}</td>
    <td>${escHtml(m.name)}</td>
    <td>${m.qibla.toFixed(1)}°</td>
    <td>${m.axis!==null?m.axis.toFixed(1)+'°':'—'}</td>
    <td class="bad">${m.diff.toFixed(1)}°</td>
    <td class="bad"> Sapma</td>
  </tr>`).join('')}</tbody>
</table>

<h2>En İyi 10 Cami (Kıbleye En Yakın)</h2>
<table>
  <thead><tr><th>#</th><th>Cami Adı</th><th>Kıble</th><th>Bina Yönü</th><th>Sapma</th><th>Durum</th></tr></thead>
  <tbody>${best.map((m,i)=>`<tr>
    <td>${i+1}</td>
    <td>${escHtml(m.name)}</td>
    <td>${m.qibla.toFixed(1)}°</td>
    <td>${m.axis!==null?m.axis.toFixed(1)+'°':'—'}</td>
    <td class="ok">${m.diff.toFixed(1)}°</td>
    <td class="ok"> Doğru</td>
  </tr>`).join('')}</tbody>
</table>

<footer>Veri: OpenStreetMap katkıcıları · ODbL · Kıble Dedektörü ile üretildi · ${new Date().toISOString()}</footer>
</body></html>`;

  const blob = new Blob([html], {type:'text/html;charset=utf-8'});
  const url  = URL.createObjectURL(blob);
  window.open(url, '_blank');
  setTimeout(()=>URL.revokeObjectURL(url), 60000);
  toast(' Rapor yeni sekmede açıldı', 3000);
}

function buildScoreCardCanvas() {
  const all = [...mosqueDB.values()];
  const withData = all.filter(m => m.diff !== null);
  const ok = withData.filter(m => m.diff <= tol).length;
  const pct = withData.length ? Math.round(ok / withData.length * 100) : 0;
  const avg = withData.length ? (withData.reduce((s,m)=>s+m.diff,0)/withData.length) : null;
  const cv = document.createElement('canvas');
  cv.width = 1080; cv.height = 1080;
  const ctx = cv.getContext('2d');
  const bg = ctx.createLinearGradient(0,0,1080,1080);
  bg.addColorStop(0, '#0f1018');
  bg.addColorStop(1, '#255b89');
  ctx.fillStyle = bg;
  ctx.fillRect(0,0,1080,1080);
  ctx.fillStyle = '#c9a84c';
  ctx.font = '700 64px "Manrope", monospace';
  ctx.fillText('Qibla Checker Score', 80, 120);
  ctx.fillStyle = '#e8e4d8';
  ctx.font = '700 120px "Manrope", monospace';
  ctx.fillText(`${pct}%`, 80, 300);
  ctx.font = '500 44px "Manrope", monospace';
  ctx.fillStyle = 'rgba(255,255,255,.50)';
  ctx.fillText(currentCity || 'City', 80, 365);
  ctx.fillStyle = '#d1d5db';
  ctx.font = '500 34px "Manrope", monospace';
  ctx.fillText(`Total mosques: ${all.length}`, 80, 460);
  ctx.fillText(`With axis data: ${withData.length}`, 80, 518);
  ctx.fillText(`Tolerance: ${tol}°`, 80, 576);
  ctx.fillText(`Average deviation: ${avg != null ? avg.toFixed(1)+'°' : '—'}`, 80, 634);
  ctx.fillStyle = '#6b7280';
  ctx.font = '400 26px "Manrope", monospace';
  ctx.fillText(new Date().toLocaleString('tr-TR'), 80, 990);
  return cv;
}

async function shareScoreCard() {
  if (!mosqueDB.size) { toast('Paylaşım için önce veri yükleyin', 2200); return; }
  const cv = buildScoreCardCanvas();
  const blob = await new Promise(res => cv.toBlob(res, 'image/png'));
  if (!blob) { toast('Skor kartı üretilemedi', 2200); return; }
  const file = new File([blob], `qibla-score-${slugify(currentCity)}-${dateStr()}.png`, {type:'image/png'});
  if (navigator.share && navigator.canShare && navigator.canShare({ files:[file] })) {
    try {
      await navigator.share({ title:`Qibla Score - ${currentCity}`, text:`${currentCity} kıble skoru`, files:[file] });
      toast('Skor kartı paylaşıldı', 1800);
      return;
    } catch {}
  }
  download(blob, file.name, 'image/png');
  toast('Skor kartı indirildi (paylaşım fallback)', 2300);
}

// ── Helpers
function download(content, filename, type) {
  const blob = content instanceof Blob ? content : new Blob([content], {type});
  const url  = URL.createObjectURL(blob);
  const a    = document.createElement('a');
  a.href = url; a.download = filename;
  document.body.appendChild(a); a.click();
  document.body.removeChild(a);
  setTimeout(()=>URL.revokeObjectURL(url), 10000);
}

function slugify(s) {
  return (s||'sehir').toLowerCase()
    .replace(/ı/g,'i').replace(/ğ/g,'g').replace(/ü/g,'u')
    .replace(/ş/g,'s').replace(/ö/g,'o').replace(/ç/g,'c')
    .replace(/İ/g,'i').replace(/\s+/g,'-').replace(/[^a-z0-9-]/g,'');
}

function dateStr() {
  return new Date().toISOString().slice(0,10);
}

function csvEsc(s) {
  if (s==null) return '';
  s = String(s);
  if (s.includes(',') || s.includes('"') || s.includes('\n'))
    return '"' + s.replace(/"/g,'""') + '"';
  return s;
}

// Add 'E' shortcut for export
// (handled in UX script via keydown)



// ══════════════════════════════════════════════════════════════
//  UX & KEYBOARD SHORTCUTS (Adım 7)
// ══════════════════════════════════════════════════════════════

// ── Keyboard shortcut helpers
function isInputFocused() {
  const tag = document.activeElement?.tagName;
  return tag === 'INPUT' || tag === 'TEXTAREA' || document.activeElement?.isContentEditable;
}

function anyModalOpen() {
  return document.getElementById('hist-overlay')?.classList.contains('show') ||
         document.getElementById('cmp-overlay')?.classList.contains('show') ||
         document.getElementById('lb-overlay')?.classList.contains('show')  ||
         document.getElementById('lab-overlay')?.classList.contains('show') ||
         document.getElementById('cmps-overlay')?.classList.contains('show') ||
         document.getElementById('m3d-overlay')?.classList.contains('show') ||
         document.getElementById('biz-overlay')?.classList.contains('show') ||
         document.getElementById('ks-overlay')?.classList.contains('show');
}

// Navigate cami list with arrow keys
let mosqueNavIdx = -1;

function mosqueNavStep(dir) {
  const items = [...document.querySelectorAll('.m-item')];
  if (!items.length) return;
  mosqueNavIdx = Math.max(0, Math.min(items.length-1, mosqueNavIdx + dir));
  items.forEach((el,i) => el.classList.toggle('active', i === mosqueNavIdx));
  const active = items[mosqueNavIdx];
  if (active) {
    active.scrollIntoView({block:'nearest', behavior:'smooth'});
    // Find mosque by id
    const id = active.id.replace('mi-','');
    const numId = parseInt(id);
    const m = mosqueDB.get(numId) || mosqueDB.get(id);
    if (m) handleMosqueClick(m);
  }
}

// Global keydown handler
document.addEventListener('keydown', e => {
  // Always: Esc closes everything
  if (e.key === 'Escape') {
    if (isOverlayVisible() && activeSearchController) {
      e.preventDefault();
      cancelActiveSearch();
      return;
    }
    if (document.getElementById('ks-overlay').classList.contains('show')) { closeShortcuts(); return; }
    if (document.getElementById('lab-overlay').classList.contains('show')) { closeLab(); return; }
    if (document.getElementById('cmps-overlay').classList.contains('show')) { closeCompass(); return; }
    if (document.getElementById('m3d-overlay').classList.contains('show')) { close3D(); return; }
    if (document.getElementById('biz-overlay').classList.contains('show')) { closeBiz(); return; }
    if (anyModalOpen()) return; // let each modal handle its own Esc
    if (dpOpen) { closeDetailPanel(); return; }
    if (document.getElementById('ms-dropdown').classList.contains('show')) {
      document.getElementById('ms-dropdown').classList.remove('show'); return;
    }
    return;
  }

  // Skip if input is focused or a modal is open (except help)
  // Respect native OS/browser shortcuts (copy/paste/cut etc.)
  if (e.metaKey || e.ctrlKey || e.altKey) return;
  if (isInputFocused()) return;

  switch(e.key) {
    case '?':
      e.preventDefault();
      openShortcuts(); break;

    case '/':
      e.preventDefault();
      document.getElementById('city-input').focus();
      document.getElementById('city-input').select(); break;

    case 'h': case 'H':
      if (!anyModalOpen()) { e.preventDefault(); toggleHeatmap(); } break;

    case 's': case 'S':
      if (!anyModalOpen()) { e.preventDefault(); toggleScoreCard(); } break;

    case 't': case 'T':
      if (!anyModalOpen()) { e.preventDefault(); toggleHistoryMode(); } break;

    case 'l': case 'L':
      if (!anyModalOpen()) { e.preventDefault(); openLeaderboard(); } break;

    case 'p': case 'P':
      if (!anyModalOpen()) { e.preventDefault(); openBiz(); } break;

    case 'q': case 'Q':
      if (!anyModalOpen()) { e.preventDefault(); openLab(); } break;

    case 'o': case 'O':
      if (!anyModalOpen()) { e.preventDefault(); openCompass(); } break;

    case 'e': case 'E':
      if (!anyModalOpen()) { e.preventDefault(); openExport(); } break;

    case 'g': case 'G':
      if (!anyModalOpen()) { e.preventDefault(); useMyLocation(); } break;

    case 'd': case 'D':
      if (dpOpen) { e.preventDefault(); closeDetailPanel(); } break;

    case 'ArrowRight':
      if (!anyModalOpen() && !dpOpen) { e.preventDefault(); mosqueNavStep(1); }
      else if (dpOpen) { e.preventDefault(); mosqueNavStep(1); } break;

    case 'ArrowLeft':
      if (!anyModalOpen() && !dpOpen) { e.preventDefault(); mosqueNavStep(-1); }
      else if (dpOpen) { e.preventDefault(); mosqueNavStep(-1); } break;

    case '+': case '=':
      if (!anyModalOpen()) {
        e.preventDefault();
        const tolInput = document.getElementById('tol');
        tolInput.value = Math.min(45, parseInt(tolInput.value)+5);
        tolInput.dispatchEvent(new Event('input'));
      } break;

    case '-':
      if (!anyModalOpen()) {
        e.preventDefault();
        const tolInput = document.getElementById('tol');
        tolInput.value = Math.max(5, parseInt(tolInput.value)-5);
        tolInput.dispatchEvent(new Event('input'));
      } break;
  }
});

// ── Shortcuts modal
function openShortcuts() {
  document.getElementById('ks-overlay').classList.add('show');
}
function closeShortcuts() {
  document.getElementById('ks-overlay').classList.remove('show');
}
function ksOverlayClick(e) {
  if (e.target === document.getElementById('ks-overlay')) closeShortcuts();
}

// ── Mobile drawer
function openMobDrawer() {
  document.getElementById('mob-drawer').classList.add('open');
  document.getElementById('mob-backdrop').classList.add('show');
}
function closeMobDrawer() {
  document.getElementById('mob-drawer').classList.remove('open');
  document.getElementById('mob-backdrop').classList.remove('show');
}
function syncMobileQuickBarVisibility() {
  const bar = document.getElementById('mob-bottom-bar');
  if (!bar) return;
  const mobileLike = (window.innerWidth <= 900) && (window.matchMedia('(pointer: coarse)').matches || window.innerWidth <= 768);
  bar.style.display = mobileLike ? 'flex' : 'none';
}
function mobSearch() {
  const v = document.getElementById('mob-city-input').value.trim();
  if (!v) return;
  document.getElementById('city-input').value = v;
  closeMobDrawer();
  doSearch();
}
function mobQuickSearch() {
  const v = document.getElementById('mob-quick-city')?.value.trim();
  if (!v) return;
  document.getElementById('city-input').value = v;
  doSearch();
}
document.getElementById('mob-city-input').addEventListener('keydown', e => {
  if (e.key === 'Enter') mobSearch();
});
document.getElementById('mob-quick-city')?.addEventListener('keydown', e => {
  if (e.key === 'Enter') mobQuickSearch();
});
window.addEventListener('resize', syncMobileQuickBarVisibility);
window.addEventListener('orientationchange', syncMobileQuickBarVisibility);
setTimeout(syncMobileQuickBarVisibility, 0);

// Sync mobile layer buttons with desktop
const _origSwitchLayer = switchLayer;
window.switchLayer = function(type) {
  _origSwitchLayer(type);
  setLayerButtonActive(type);
};

// ── Touch swipe to close detail panel on mobile
(function() {
  let startY = 0, startX = 0;
  const panel = document.getElementById('dp-panel');

  panel.addEventListener('touchstart', e => {
    startY = e.touches[0].clientY;
    startX = e.touches[0].clientX;
  }, {passive:true});

  panel.addEventListener('touchend', e => {
    if (window.innerWidth > 768) return;
    const dy = e.changedTouches[0].clientY - startY;
    const dx = e.changedTouches[0].clientX - startX;
    // Swipe down on mobile (full-width panel)
    if (dy > 80 && Math.abs(dx) < Math.abs(dy)) closeDetailPanel();
  }, {passive:true});
})();

// ── Mark newly loaded mosque markers with a brief pulse
// (applied via CSS class added in renderAll override)
const _uxRenderAll = renderAll;
window.renderAll = function() {
  _uxRenderAll();
};

// ── Show shortcut hint toast on first load
(function(){
  const KEY='qibla-ks-hint-shown';
  if(!safeStorageGet(KEY, null)){
    setTimeout(()=>toast(' Klavye kısayolları için ? tuşuna basın',5000),3000);
    safeStorageSet(KEY,'1');
  }
})();



// ══════════════════════════════════════════════════════════════
//  DETAIL PANEL (Adım 6)
// ══════════════════════════════════════════════════════════════

let dpOpen = false;
let dpPopulateToken = 0;
const mosquePlaceCache = new Map();

function extractPlaceFromAddress(addr = {}) {
  if (!addr || typeof addr !== 'object') return { city:'', district:'' };
  const city = String(
    addr.city || addr.town || addr.county || addr.province || addr.state || addr.municipality || ''
  ).trim();
  const district = String(
    addr.city_district || addr.district || addr.suburb || addr.neighbourhood || addr.quarter || addr.borough || ''
  ).trim();
  return { city, district };
}

function extractPlaceFromTags(tags = {}) {
  const city = String(
    tags['addr:city'] || tags['addr:town'] || tags['addr:county'] || tags['addr:province'] || tags['addr:state'] || ''
  ).trim();
  const district = String(
    tags['addr:district'] || tags['addr:city_district'] || tags['addr:suburb'] || tags['addr:neighbourhood'] || tags['addr:quarter'] || ''
  ).trim();
  return { city, district };
}

function formatPlaceLine(city, district) {
  if (city && district) return `${district} / ${city}`;
  if (city) return city;
  if (district) return district;
  return currentLang === 'en' ? 'District/city unavailable' : 'İlçe/şehir bilgisi bulunamadı';
}

async function resolveMosquePlace(m, tags = {}) {
  const fromTags = extractPlaceFromTags(tags);
  if (fromTags.city || fromTags.district) return fromTags;
  const key = `${(m.osmType || 'way')}:${m.id}`;
  if (mosquePlaceCache.has(key)) return mosquePlaceCache.get(key);
  try {
    const langHdr = currentLang === 'en' ? 'en,tr,ar' : 'tr,en,ar';
    const url = `https://nominatim.openstreetmap.org/reverse?lat=${m.lat}&lon=${m.lng}&format=jsonv2&zoom=14&addressdetails=1`;
    const data = await nominatimFetchJson(url, {'Accept-Language': langHdr});
    const place = extractPlaceFromAddress(data?.address || {});
    mosquePlaceCache.set(key, place);
    return place;
  } catch {
    const none = { city:'', district:'' };
    mosquePlaceCache.set(key, none);
    return none;
  }
}

function openDetailPanel(m) {
  dpOpen = true;
  document.getElementById('dp-panel').classList.add('open');
  document.getElementById('dp-backdrop').classList.add('show');
  populateDetailPanel(m);
}

function closeDetailPanel() {
  dpOpen = false;
  document.getElementById('dp-panel').classList.remove('open');
  document.getElementById('dp-backdrop').classList.remove('show');
}

// ESC closes panel
document.addEventListener('keydown', e => {
  if (e.key === 'Escape' && dpOpen) closeDetailPanel();
});

function populateDetailPanel(m) {
  const tags = m.tags || {};
  const token = ++dpPopulateToken;
  const names = pickLocalizedMosqueNames(m, tags);

  // ── Name & coords
  document.getElementById('dp-name').textContent = names.primary;
  const ar = names.arName;
  const arEl = document.getElementById('dp-name-ar');
  arEl.textContent = ar;
  arEl.style.display = ar ? '' : 'none';
  const placeEl = document.getElementById('dp-place');
  const placeFromTags = extractPlaceFromTags(tags);
  placeEl.textContent = formatPlaceLine(placeFromTags.city, placeFromTags.district);
  document.getElementById('dp-coords').textContent =
    `${m.lat.toFixed(5)}°N  ${m.lng.toFixed(5)}°E  ·  OSM ${m.osmType||'way'} #${m.id}`;

  // ── Status ribbon
  const col = m.status==='correct'?'#4ade80':m.status==='wrong'?'#f87171':'#fbbf24';
  const statusLabel = m.status==='correct'?' Doğru Yön':m.status==='wrong'?' Sapma Var':' Veri Yok';
  document.getElementById('dp-status-badge').innerHTML =
    `<span class="dp-status-badge ${m.status}">${statusLabel}</span>`;
  document.getElementById('dp-qibla-val').textContent = m.qibla.toFixed(1)+'°';
  document.getElementById('dp-axis-val').textContent  = m.axis!==null ? m.axis.toFixed(1)+'°' : '—';
  const diffEl = document.getElementById('dp-diff-val');
  diffEl.textContent = m.diff!==null ? m.diff.toFixed(1)+'°' : '—';
  diffEl.style.color = m.diff!==null ? col : 'rgba(255,255,255,.50)';
  document.getElementById('dp-dist-val').textContent =
    Math.round(greatCircleKm(m.lat, m.lng, 21.4225, 39.8262)) + ' km';

  if (!(placeFromTags.city || placeFromTags.district)) {
    resolveMosquePlace(m, tags).then(resolved => {
      if (token === dpPopulateToken && window._lastClickedMosque?.id == m.id) {
        placeEl.textContent = formatPlaceLine(resolved.city, resolved.district);
      }
    });
  }

  // ── Photo
  loadPhoto(m, tags);

  // ── Compass
  drawDetailCompass(m);
  renderInteriorSection(m, tags);
  renderExplainability(m);

  // ── Qibla stats
  const methLabel = {
    'edge-analysis':'Kenar Analizi (PCA)',
    'osm-tag':'OSM direction tag',
    'hybrid-interior':'Hibrit (Bina + İç Mekan)',
    'interior-only':'İç Mekan Kanıtı',
    'fused':'Birleşik',
    'none':'—'
  }[m.method] || m.method;
  const buildDate = tags.start_date || tags['building:start_date'];
  const fusionRel = m.fusion?.reliability!=null ? Math.round(m.fusion.reliability*100)+'%' : '—';
  const interiorCount = m.fusion?.interiorCount || getInteriorEvidenceList(m).length;
  const conv = m.convertedFrom?.converted ? 'Evet (olası)' : 'Hayır';
  document.getElementById('dp-qibla-stats').innerHTML = `
    <div class="dp-qs-row"><span class="dp-qs-k">Hesaplama yöntemi</span><span class="dp-qs-v">${escHtml(methLabel)}</span></div>
    <div class="dp-qs-row"><span class="dp-qs-k">Kabe yönü (büyük daire)</span><span class="dp-qs-v">${m.qibla.toFixed(2)}°</span></div>
    ${m.baseAxis!==null&&m.baseAxis!==undefined?`<div class="dp-qs-row"><span class="dp-qs-k">Bina ekseni (ham)</span><span class="dp-qs-v">${m.baseAxis.toFixed(2)}°</span></div>`:''}
    ${m.axis!==null?`<div class="dp-qs-row"><span class="dp-qs-k">Nihai eksen</span><span class="dp-qs-v">${m.axis.toFixed(2)}°</span></div>`:''}
    ${m.diff!==null?`<div class="dp-qs-row"><span class="dp-qs-k">Kıble sapması</span><span class="dp-qs-v" style="color:${col}">${m.diff.toFixed(2)}°</span></div>`:''}
    <div class="dp-qs-row"><span class="dp-qs-k">Füzyon güveni</span><span class="dp-qs-v">${fusionRel}</span></div>
    <div class="dp-qs-row"><span class="dp-qs-k">Model güven puanı</span><span class="dp-qs-v">${m.confidence ?? '—'}/100</span></div>
    <div class="dp-qs-row"><span class="dp-qs-k">İç kanıt adedi</span><span class="dp-qs-v">${interiorCount}</span></div>
    <div class="dp-qs-row"><span class="dp-qs-k">Dönüştürülmüş yapı</span><span class="dp-qs-v">${conv}</span></div>
    ${m.diff!==null?`<div class="dp-qs-row"><span class="dp-qs-k">Değerlendirme</span><span class="dp-qs-v" style="color:${col}">${m.diff<=5?'Mükemmel (<5°)':m.diff<=tol?'Kabul edilebilir':'Düzeltilmeli'}</span></div>`:''}
    ${buildDate?`<div class="dp-qs-row"><span class="dp-qs-k">İnşaat tarihi</span><span class="dp-qs-v">${escHtml(buildDate)}</span></div>`:''}
  `;

  // ── Wikipedia
  loadWikipedia(m, tags);

  // ── OSM Tags table
  renderTagsTable(tags);

  // ── Action buttons
  renderActions(m, tags);

  // İsim generic/eksikse panel açıkken güçlü kaynaklardan yeniden çöz.
  if (isPlaceholderMosqueName(m.name) || isGenericMosqueName(m.name)) {
    enrichMosqueName(m, { force:true }).then(() => {
      if (token !== dpPopulateToken || window._lastClickedMosque?.id != m.id) return;
      if (isPlaceholderMosqueName(m.name) || isGenericMosqueName(m.name)) return;
      document.getElementById('dp-name').textContent = m.name;
      const bounds = map?.getBounds?.().pad(0.1);
      if (bounds) {
        const visible = [...mosqueDB.values()].filter(x => bounds.contains([x.lat, x.lng]));
        if (mosqueFilter) applyMosqueFilter(mosqueFilter);
        else updateList(visible);
      }
      // İsim netleşince foto eşleşmesi de daha güvenli hale gelir; yeniden dene.
      loadPhoto(m, m.tags || {});
    }).catch(()=>{});
  }
}

// ── Photo loader
async function loadPhoto(m, tags) {
  const wrap = document.getElementById('dp-photo-wrap');
  const img  = document.getElementById('dp-photo');
  const cred = document.getElementById('dp-photo-credit');

  wrap.style.display = 'none';

  // 1. wikimedia_commons tag
  const wmc = tags.wikimedia_commons || tags.image;
  if (wmc) {
    const url = await resolveWikimediaUrl(wmc);
    if (url) { img.src = url; wrap.style.display = ''; cred.textContent = '© Wikimedia Commons'; return; }
  }

  // 2. wikipedia tag → try Wikimedia page image
  const wiki = tags.wikipedia;
  if (wiki) {
    const url = await fetchWikiPageImage(wiki);
    if (url) { img.src = url; wrap.style.display = ''; cred.textContent = '© Wikipedia'; return; }
  }

  // 3. wikidata P18 image
  const wd = String(tags.wikidata || '').trim();
  if (wd) {
    const url = await fetchWikidataImageUrl(wd);
    if (url) { img.src = url; wrap.style.display = ''; cred.textContent = '© Wikimedia (Wikidata)'; return; }
  }

  // 4. Commons category fallback
  if (wmc && /^Category:/i.test(wmc)) {
    const url = await fetchCommonsCategoryImage(wmc);
    if (url) { img.src = url; wrap.style.display = ''; cred.textContent = '© Wikimedia Commons'; return; }
  }

  // 5. Name/location based Commons search fallback
  if (!canUseLoosePhotoFallback(m, tags)) return;
  const fallback = await fetchCommonsFallbackPhoto(m, tags);
  if (fallback?.url) {
    img.src = fallback.url;
    wrap.style.display = '';
    cred.textContent = fallback.source || '© Wikimedia Commons';
    return;
  }
}

async function resolveWikimediaUrl(val) {
  try {
    // If it's already a URL
    if (val.startsWith('http')) return val;
    // Extract filename from "File:Xxxx.jpg" or plain filename
    const file = val.replace(/^(File:|Dosya:)/i,'').replace(/^Category:.*/,'').trim();
    if (!file || /^Category/i.test(val)) return null;
    const api = `https://commons.wikimedia.org/w/api.php?action=query&titles=File:${encodeURIComponent(file)}&prop=imageinfo&iiprop=url&format=json&origin=*`;
    const r = await fetch(api);
    const d = await r.json();
    const pages = d.query?.pages;
    if (!pages) return null;
    const page = Object.values(pages)[0];
    return page?.imageinfo?.[0]?.url || null;
  } catch { return null; }
}

async function fetchWikiPageImage(wikiTag) {
  try {
    // Format: "tr:Cami adı" or "en:Mosque name"
    const [lang, ...titleParts] = wikiTag.includes(':') ? wikiTag.split(':') : ['tr', wikiTag];
    const title = titleParts.join(':');
    const api = `https://${lang}.wikipedia.org/w/api.php?action=query&titles=${encodeURIComponent(title)}&prop=pageimages&pithumbsize=600&format=json&origin=*`;
    const r = await fetch(api);
    const d = await r.json();
    const pages = d.query?.pages;
    if (!pages) return null;
    const page = Object.values(pages)[0];
    return page?.thumbnail?.source || null;
  } catch { return null; }
}

async function fetchWikidataImageUrl(qid) {
  try {
    const id = String(qid || '').trim().toUpperCase();
    if (!/^Q\d+$/.test(id)) return null;
    const api = `https://www.wikidata.org/w/api.php?action=wbgetentities&ids=${encodeURIComponent(id)}&props=claims&format=json&origin=*`;
    const r = await fetch(api);
    if (!r.ok) return null;
    const d = await r.json();
    const entity = d?.entities?.[id];
    const claim = entity?.claims?.P18?.[0];
    const file = claim?.mainsnak?.datavalue?.value;
    if (!file || typeof file !== 'string') return null;
    return await resolveWikimediaUrl(`File:${file}`);
  } catch { return null; }
}

async function fetchCommonsCategoryImage(catName) {
  try {
    const clean = String(catName || '').replace(/^Category:/i,'').trim();
    if (!clean) return null;
    const api = `https://commons.wikimedia.org/w/api.php?action=query&list=categorymembers&cmtitle=Category:${encodeURIComponent(clean)}&cmnamespace=6&cmlimit=20&format=json&origin=*`;
    const r = await fetch(api);
    if (!r.ok) return null;
    const d = await r.json();
    const files = d?.query?.categorymembers || [];
    if (!files.length) return null;
    const title = files[0]?.title;
    if (!title) return null;
    return await resolveWikimediaUrl(title);
  } catch { return null; }
}

function buildPhotoFallbackTerms(m, tags = {}) {
  const t = tags || {};
  const city = String(t['addr:city'] || t['addr:town'] || t['is_in:city'] || m?.searchMeta?.city || '').trim();
  const province = String(t['addr:state'] || t['addr:province'] || t['is_in:state'] || m?.searchMeta?.province || '').trim();
  const wikiTitle = String(t.wikipedia || '').includes(':')
    ? String(t.wikipedia).split(':').slice(1).join(':').replace(/_/g, ' ').trim()
    : '';
  const base = [m?.name, wikiTitle].map(x => String(x || '').trim()).filter(Boolean);
  const out = [];
  for (const b of base) {
    out.push(`${b} mosque`);
    out.push(`${b} camii`);
    if (city) out.push(`${b} ${city} mosque`);
    if (province && province !== city) out.push(`${b} ${province} mosque`);
  }
  const seen = new Set();
  return out.filter(x => {
    const k = normalize(trLower(x || ''));
    if (!k || seen.has(k)) return false;
    seen.add(k);
    return true;
  }).slice(0, 8);
}

function tokenizePhotoTokens(text) {
  return normalize(trLower(String(text || '')))
    .split(/[^a-z0-9ığüşöçâêîû]+/i)
    .map(s => s.trim())
    .filter(s => s.length > 2);
}

function getPhotoContext(m, tags = {}) {
  const t = tags || {};
  const wikiTitle = String(t.wikipedia || '').includes(':')
    ? String(t.wikipedia).split(':').slice(1).join(':').replace(/_/g, ' ').trim()
    : '';
  const city = String(t['addr:city'] || t['addr:town'] || t['is_in:city'] || m?.searchMeta?.city || '').trim();
  const district = String(t['addr:district'] || t['addr:suburb'] || t['addr:neighbourhood'] || '').trim();
  const province = String(t['addr:state'] || t['addr:province'] || t['is_in:state'] || m?.searchMeta?.province || '').trim();
  const generic = new Set(['cami','camii','mescit','mescid','mosque','masjid']);
  const nameTokens = [...new Set(tokenizePhotoTokens(`${m?.name || ''} ${wikiTitle}`).filter(tk => !generic.has(tk)))];
  const locTokens = [...new Set(tokenizePhotoTokens(`${city} ${district} ${province}`).filter(tk => !generic.has(tk)))];
  return { nameTokens, locTokens, hasStrongName: nameTokens.some(tk => tk.length >= 4) };
}

function canUseLoosePhotoFallback(m, tags = {}) {
  if (!m) return false;
  if (isPlaceholderMosqueName(m.name) || isGenericMosqueName(m.name)) return false;
  const ctx = getPhotoContext(m, tags);
  return ctx.hasStrongName;
}

function scoreCommonsTitleRelevance(title, ctx) {
  const txt = normalize(trLower(String(title || '').replace(/^file:/i, '').replace(/_/g, ' ')));
  if (!txt) return { score:0, matchedName:0 };
  const mosqueHint = /(cami|camii|mosque|masjid|mescit|mescid)/.test(txt) ? 8 : 0;
  let matchedName = 0;
  let matchedLoc = 0;
  for (const tk of ctx.nameTokens) {
    if (tk && txt.includes(tk)) matchedName++;
  }
  for (const tk of ctx.locTokens) {
    if (tk && txt.includes(tk)) matchedLoc++;
  }
  const score = (matchedName * 24) + (matchedLoc * 9) + mosqueHint;
  return { score, matchedName };
}

async function fetchCommonsBySearchTerm(term, ctx) {
  try {
    const api = `https://commons.wikimedia.org/w/api.php?action=query&generator=search&gsrsearch=${encodeURIComponent(term)}&gsrnamespace=6&gsrlimit=8&prop=imageinfo&iiprop=url&format=json&origin=*`;
    const r = await fetch(api);
    if (!r.ok) return null;
    const d = await r.json();
    const pages = Object.values(d?.query?.pages || {});
    let best = null;
    for (const p of pages) {
      const title = String(p?.title || '');
      const isPhotoLike = /\.(jpg|jpeg|png|webp)$/i.test(title);
      const url = p?.imageinfo?.[0]?.url;
      if (!url || !isPhotoLike) continue;
      const rel = scoreCommonsTitleRelevance(title, ctx);
      if (rel.matchedName < 1) continue;
      if (!best || rel.score > best.score) best = { url, score:rel.score };
    }
    return best && best.score >= 24 ? best.url : null;
  } catch { return null; }
}

async function fetchCommonsFallbackPhoto(m, tags) {
  const ctx = getPhotoContext(m, tags);
  const terms = buildPhotoFallbackTerms(m, tags);
  for (const term of terms) {
    const url = await fetchCommonsBySearchTerm(term, ctx);
    if (url) return { url, source:'© Wikimedia Commons (search)' };
  }
  return null;
}

// ── Wikipedia summary
async function loadWikipedia(m, tags) {
  const sec = document.getElementById('dp-wiki-section');
  const body = document.getElementById('dp-wiki-body');
  const link = document.getElementById('dp-wiki-link');
  sec.style.display = 'none';

  const wiki = tags.wikipedia;
  if (!wiki) return;

  try {
    const [lang, ...titleParts] = wiki.includes(':') ? wiki.split(':') : ['tr', wiki];
    const title = titleParts.join(':');
    const api = `https://${lang}.wikipedia.org/w/api.php?action=query&titles=${encodeURIComponent(title)}&prop=extracts&exintro=true&exchars=600&format=json&origin=*`;
    const r = await fetch(api);
    const d = await r.json();
    const pages = d.query?.pages;
    if (!pages) return;
    const page = Object.values(pages)[0];
    if (!page?.extract) return;

    // Strip HTML tags for clean text
    const clean = page.extract.replace(/<[^>]+>/g,'').replace(/\n+/g,' ').trim();
    if (!clean) return;

    body.textContent = clean;
    link.href = `https://${lang}.wikipedia.org/wiki/${encodeURIComponent(title)}`;
    link.textContent = `Wikipedia'da oku (${lang}) →`;
    sec.style.display = '';
  } catch { sec.style.display = 'none'; }
}

// ── Compass canvas
function drawDetailCompass(m) {
  const canvas = document.getElementById('dp-compass');
  const ctx = canvas.getContext('2d');
  const cx = 60, cy = 60, r = 52;
  ctx.clearRect(0, 0, 120, 120);

  // Outer ring
  ctx.beginPath(); ctx.arc(cx,cy,r,0,Math.PI*2);
  ctx.strokeStyle = '#6a9ec9'; ctx.lineWidth = 1.5; ctx.stroke();

  // Cardinal labels
  const cardinals = [['K',0],['D',90],['G',180],['B',270]];
  ctx.font = '8px Manrope,monospace'; ctx.fillStyle = 'rgba(255,255,255,.50)'; ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
  cardinals.forEach(([lbl, deg]) => {
    const rad = (deg - 90) * Math.PI / 180;
    ctx.fillText(lbl, cx + (r-8)*Math.cos(rad), cy + (r-8)*Math.sin(rad));
  });

  // Tick marks
  for (let d=0; d<360; d+=30) {
    const rad = (d-90)*Math.PI/180;
    const len = d%90===0 ? 7 : 4;
    ctx.beginPath();
    ctx.moveTo(cx+(r-2)*Math.cos(rad), cy+(r-2)*Math.sin(rad));
    ctx.lineTo(cx+(r-2-len)*Math.cos(rad), cy+(r-2-len)*Math.sin(rad));
    ctx.strokeStyle = '#84b3d7'; ctx.lineWidth = 1; ctx.stroke();
  }

  // Qibla direction (gold dashed)
  const qRad = (m.qibla - 90) * Math.PI / 180;
  ctx.beginPath();
  ctx.moveTo(cx, cy);
  ctx.lineTo(cx + (r-12)*Math.cos(qRad), cy + (r-12)*Math.sin(qRad));
  ctx.strokeStyle = '#c9a84c'; ctx.lineWidth = 2; ctx.setLineDash([4,3]); ctx.stroke();
  ctx.setLineDash([]);
  // Qibla arrowhead
  drawArrow(ctx, cx, cy, qRad, r-12, '#c9a84c', 2);

  // Building axis (colored by status)
  if (m.axis !== null) {
    const col = m.status==='correct'?'#4ade80':m.status==='wrong'?'#f87171':'#fbbf24';
    const fd = closestDirection(m.axis, m.qibla);
    const bRad = (fd - 90) * Math.PI / 180;
    // Draw full axis (both directions)
    const bRad2 = bRad + Math.PI;
    ctx.beginPath();
    ctx.moveTo(cx + (r-18)*Math.cos(bRad2), cy + (r-18)*Math.sin(bRad2));
    ctx.lineTo(cx + (r-18)*Math.cos(bRad),  cy + (r-18)*Math.sin(bRad));
    ctx.strokeStyle = col; ctx.lineWidth = 2.5; ctx.stroke();
    drawArrow(ctx, cx, cy, bRad, r-18, col, 2.5);
  }

  // Center dot
  ctx.beginPath(); ctx.arc(cx,cy,3,0,Math.PI*2);
  ctx.fillStyle = '#e8e4d8'; ctx.fill();

  // Legend
  ctx.font = '7px Manrope,monospace'; ctx.textAlign = 'left'; ctx.textBaseline = 'middle';
  ctx.fillStyle = '#c9a84c'; ctx.fillRect(4,108,12,2);
  ctx.fillStyle = '#c9a84c'; ctx.fillText('Kıble', 19, 109);
  if (m.axis !== null) {
    const col = m.status==='correct'?'#4ade80':m.status==='wrong'?'#f87171':'#fbbf24';
    ctx.fillStyle = col; ctx.fillRect(60,108,12,2);
    ctx.fillStyle = col; ctx.fillText('Bina', 75, 109);
  }
}

function drawArrow(ctx, cx, cy, angleRad, dist, color, lw) {
  const tipX = cx + dist*Math.cos(angleRad);
  const tipY = cy + dist*Math.sin(angleRad);
  const headLen = 7;
  const headAngle = 0.45;
  ctx.beginPath();
  ctx.moveTo(tipX - headLen*Math.cos(angleRad-headAngle), tipY - headLen*Math.sin(angleRad-headAngle));
  ctx.lineTo(tipX, tipY);
  ctx.lineTo(tipX - headLen*Math.cos(angleRad+headAngle), tipY - headLen*Math.sin(angleRad+headAngle));
  ctx.strokeStyle = color; ctx.lineWidth = lw; ctx.stroke();
}

// ── Tags table
const DP_TAG_PRIORITY = ['name','name:tr','name:ar','name:en','amenity','religion','denomination',
  'start_date','building:start_date','architect','heritage','wikipedia','wikidata',
  'wikimedia_commons','image','website','phone','addr:street','addr:city','operator',
  'building','building:levels','capacity','access','opening_hours'];

function renderTagsTable(tags) {
  const el = document.getElementById('dp-tags');
  const title = document.getElementById('dp-tags-title');
  const allKeys = Object.keys(tags);
  if (!allKeys.length) { el.innerHTML='<div style="color:rgba(255,255,255,.50);font-size:11px">Etiket bulunamadı</div>'; return; }

  // Sort: priority first, then alphabetical
  const sorted = [...allKeys].sort((a,b) => {
    const ai = DP_TAG_PRIORITY.indexOf(a), bi = DP_TAG_PRIORITY.indexOf(b);
    if (ai>=0 && bi>=0) return ai-bi;
    if (ai>=0) return -1;
    if (bi>=0) return 1;
    return a.localeCompare(b);
  });

  title.textContent = `OSM Etiketleri (${allKeys.length})`;

  el.innerHTML = sorted.map(k => {
    let v = escHtml(tags[k]);
    // Linkify URLs
    if (typeof tags[k] === 'string' && /^https?:\/\//i.test(tags[k])) {
      const url = tags[k];
      const short = url.length>40 ? url.slice(0,40)+'…' : url;
      v = `<a href="${escHtml(url)}" target="_blank" rel="noopener">${escHtml(short)}</a>`;
    }
    // Wikipedia: linkify
    if (k === 'wikipedia' && typeof tags[k] === 'string') {
      const [rawLang,...tp] = tags[k].split(':');
      const lang = /^[a-z-]{2,12}$/i.test(rawLang) ? rawLang.toLowerCase() : 'tr';
      const title2 = tp.join(':');
      v = `<a href="https://${lang}.wikipedia.org/wiki/${encodeURIComponent(title2)}" target="_blank" rel="noopener">${escHtml(tags[k])}</a>`;
    }
    if (k === 'wikidata' && typeof tags[k] === 'string') {
      v = `<a href="https://www.wikidata.org/wiki/${encodeURIComponent(tags[k])}" target="_blank" rel="noopener">${escHtml(tags[k])}</a>`;
    }
    return `<div class="dp-tag-row"><span class="dp-tag-k">${escHtml(k)}</span><span class="dp-tag-v">${v}</span></div>`;
  }).join('');
}

async function renderInteriorSection(m, tags) {
  const gallery = document.getElementById('dp-int-gallery');
  const meta = document.getElementById('dp-int-meta');
  const evList = document.getElementById('dp-int-ev-list');
  const axisInput = document.getElementById('dp-int-axis');
  const axisVal = document.getElementById('dp-int-axis-val');
  const urlInput = document.getElementById('dp-int-url');
  const noteInput = document.getElementById('dp-int-note');

  axisInput.value = Math.round((m.axis ?? m.qibla) % 180);
  axisVal.textContent = axisInput.value + '°';
  urlInput.value = '';
  noteInput.value = '';

  gallery.innerHTML = '<div class="dp-int-meta">İç mekan görselleri aranıyor...</div>';
  meta.textContent = '';
  const photos = await resolveInteriorPhotos(m);
  if (!photos.length) {
    gallery.innerHTML = '<div class="dp-int-meta">Otomatik iç mekan görseli bulunamadı. URL ile manuel kanıt ekleyebilirsiniz.</div>';
  } else {
    gallery.innerHTML = photos.map((p,i) => `
      <div class="dp-int-thumb" onclick="window.open('${escHtml(p.url)}','_blank')">
        <img src="${escHtml(p.url)}" alt="Interior ${i+1}"/>
        <span>${p.source==='commons-category'?'Commons':'Arama'}</span>
      </div>
    `).join('');
  }

  const list = getInteriorEvidenceList(m);
  const manualRec = getManualAxisRecord(m);
  meta.textContent = list.length
    ? `Kaydedilmiş iç mekan kanıtı: ${list.length} · Son güncelleme: ${new Date(list[list.length-1].ts).toLocaleString('tr-TR')}`
    : 'Henüz iç mekan yön kanıtı kaydedilmedi.';

  evList.innerHTML = list.length
    ? list.map((ev, idx) => `
      <div class="dp-int-ev-row">
        <div class="dp-int-ev-main">
          ${Number(ev.axis).toFixed(1)}° · Güven ${(Number(ev.confidence||0)*100|0)}%
          <div class="dp-int-ev-sub">${escHtml(ev.note || ev.sourceUrl || 'manuel giriş')}</div>
        </div>
        <button class="dp-int-ev-del" onclick="removeInteriorEvidence(${idx})">Sil</button>
      </div>
    `).join('')
    : '<div class="dp-int-meta">Kanıt listesi boş.</div>';

  if (manualRec?.axis != null) {
    const mod = manualRec.moderation || {};
    const row = document.createElement('div');
    row.className = 'dp-int-ev-row';
    row.innerHTML = `
      <div class="dp-int-ev-main">
        Manuel aks: ${Number(manualRec.axis).toFixed(1)}° · AI: ${(mod.status || 'none').toUpperCase()}
        <div class="dp-int-ev-sub">Skor: ${mod.score!=null ? (mod.score*100|0)+'%' : '—'} · ${new Date(manualRec.ts || Date.now()).toLocaleString('tr-TR')}</div>
      </div>
      <button class="dp-int-ev-del" onclick="deleteManualAxis()">Sil</button>
    `;
    evList.appendChild(row);
  }
  if (manualRec?.axis != null) {
    const mod = manualRec.moderation || {};
    setManualStatus(`Kayıtlı: ${Number(manualRec.axis).toFixed(1)}° · AI ${String(mod.status || 'none').toUpperCase()}`);
  } else {
    setManualStatus('Hazır');
  }
}

function saveInteriorEvidence() {
  const m = window._lastClickedMosque;
  if (!m) return;
  const axis = toAxis180(document.getElementById('dp-int-axis').value);
  const confidence = Math.min(1, Math.max(0.2, Number(document.getElementById('dp-int-conf').value) || 0.75));
  const sourceUrl = document.getElementById('dp-int-url').value.trim();
  const note = document.getElementById('dp-int-note').value.trim();
  const key = getMosqueKey(m);
  const list = getInteriorEvidenceList(m);
  list.push({
    axis,
    confidence,
    sourceUrl,
    note,
    ts: Date.now(),
    source: 'manual'
  });
  interiorDB[key] = list.slice(-12);
  saveInteriorDB();
  applyAxisFusion(m);
  renderAll();
  populateDetailPanel(m);
  toast('İç mekan kanıtı kaydedildi, analiz güncellendi', 2600);
}

function removeInteriorEvidence(idx) {
  const m = window._lastClickedMosque;
  if (!m) return;
  const key = getMosqueKey(m);
  const list = getInteriorEvidenceList(m);
  if (idx < 0 || idx >= list.length) return;
  list.splice(idx, 1);
  interiorDB[key] = list;
  saveInteriorDB();
  applyAxisFusion(m);
  renderAll();
  populateDetailPanel(m);
  toast('İç mekan kanıtı kaldırıldı', 2200);
}

function deleteManualAxis() {
  const m = window._lastClickedMosque;
  if (!m) return;
  delete manualAxisDB[getMosqueKey(m)];
  saveManualAxisDB();
  applyAxisFusion(m);
  renderAll();
  populateDetailPanel(m);
  toast('Manuel aks kaydı silindi', 2000);
}

function renderExplainability(m) {
  const el = document.getElementById('dp-explain');
  if (!el) return;
  const badges = (m.qualityBadges || []).map(b => `<span class="badge">${escHtml(b)}</span>`).join(' ');
  const interiorAxis = getInteriorAxis(m);
  const manualRec = getManualAxisRecord(m);
  const items = [
    ['Nihai yöntem', m.method || '—'],
    ['Füzyon güveni', m.fusion?.reliability!=null ? `${Math.round(m.fusion.reliability*100)}%` : '—'],
    ['Geometri karmaşıklığı', m.geomComplexity!=null ? `${Math.round(m.geomComplexity*100)}%` : '—'],
    ['Kanıt sayısı', String(m.fusion?.candidates ?? 0)],
    ['Ham eksen', m.baseAxis!=null ? `${m.baseAxis.toFixed(2)}°` : '—'],
    ['İç eksen', interiorAxis!=null ? `${interiorAxis.toFixed(2)}°` : '—'],
    ['Dönüşüm ipucu', m.convertedFrom?.converted ? (m.convertedFrom.previous || 'var') : 'yok'],
    ['AI manuel moderasyon', manualRec?.moderation?.status || 'none']
  ];
  el.innerHTML = `
    <div class="lab-row"><span class="lab-k">Kalite Rozetleri</span><span class="lab-v">${badges || '—'}</span></div>
    ${items.map(([k,v]) => `<div class="lab-row"><span class="lab-k">${escHtml(k)}</span><span class="lab-v">${escHtml(v)}</span></div>`).join('')}
    ${m.convertedFrom?.evidence ? `<div class="lab-row"><span class="lab-k">Dönüşüm kanıtı</span><span class="lab-v">${escHtml(m.convertedFrom.evidence)}</span></div>` : ''}
    ${manualRec?.moderation?.reasons?.length ? `<div class="lab-row"><span class="lab-k">AI notları</span><span class="lab-v">${escHtml(manualRec.moderation.reasons.join(', '))}</span></div>` : ''}
  `;
}

// ── Action buttons
function renderActions(m, tags) {
  const el = document.getElementById('dp-actions');
  const osmUrl = `https://www.openstreetmap.org/${m.osmType||'way'}/${m.id}`;
  const editUrl = `https://www.openstreetmap.org/edit?${m.osmType||'way'}=${m.id}`;
  const gmUrl   = `https://www.google.com/maps?q=${m.lat},${m.lng}`;
  const coordStr= `${m.lat.toFixed(6)}, ${m.lng.toFixed(6)}`;

  let wikiAction = '';
  if (typeof tags.wikipedia === 'string' && tags.wikipedia.includes(':')) {
    const [rawLang, ...rest] = tags.wikipedia.split(':');
    const lang = /^[a-z-]{2,12}$/i.test(rawLang) ? rawLang.toLowerCase() : 'tr';
    const title = rest.join(':').trim();
    if (title) {
      wikiAction = `<a class="dp-action-btn" href="https://${lang}.wikipedia.org/wiki/${encodeURIComponent(title)}" target="_blank" rel="noopener"> Wikipedia</a>`;
    }
  }

  el.innerHTML = `
    <button class="dp-action-btn" onclick="focusMosqueOnMap()"> Haritada Göster</button>
    <button class="dp-action-btn anim" onclick="closeDetailPanel();if(window._lastClickedMosque)animateQibla(window._lastClickedMosque)"> Büyük Daire</button>
    <button class="dp-action-btn" onclick="enrichSelectedMosqueName(true)"> İsmi Bul</button>
    <button class="dp-action-btn" onclick="open3D()"> 3D Analiz</button>
    <a class="dp-action-btn" href="${osmUrl}" target="_blank" rel="noopener"> OSM'de Gör</a>
    <a class="dp-action-btn" href="${editUrl}" target="_blank" rel="noopener"> OSM'de Düzenle</a>
    <a class="dp-action-btn" href="${gmUrl}" target="_blank" rel="noopener"> Google Maps</a>
    <button class="dp-action-btn" onclick="navigator.clipboard?.writeText('${coordStr}').then(()=>toast('Koordinat kopyalandı'))"> Koordinat Kopyala</button>
    ${wikiAction}
  `;
}

function focusMosqueOnMap() {
  const m = window._lastClickedMosque;
  if (!m || !map) return;
  closeDetailPanel();
  focusMapLatLng(m.lat, m.lng, Math.max(map.getZoom() || 15, 16), { duration: 0.7 });
  setTimeout(() => {
    const marker = renderLayers.find(layer => layer?.mosque?.id == m.id);
    if (marker?.openPopup) marker.openPopup();
  }, 450);
}

async function enrichSelectedMosqueName(force = false) {
  const m = window._lastClickedMosque;
  if (!m) return;
  const old = m.name;
  toast('İsim kaynakları karşılaştırılıyor...', 1800);
  try {
    const resolved = await enrichMosqueName(m, { force });
    if (resolved && resolved !== old) {
      populateDetailPanel(m);
      const bounds = map?.getBounds?.().pad(0.1);
      if (bounds) {
        const visible = [...mosqueDB.values()].filter(x => bounds.contains([x.lat, x.lng]));
        updateList(visible);
      }
      toast(`İsim güncellendi: ${resolved}`, 2800);
    } else if (resolved) {
      toast(`İsim doğrulandı: ${resolved}`, 2400);
    } else {
      toast('Ek kaynaklarda kesin isim bulunamadı', 2600);
    }
  } catch (e) {
    toast('İsim çözümleme başarısız: ' + (e?.message || 'bilinmeyen hata'), 3200);
  }
}

function setManualStatus(msg) {
  const el = document.getElementById('dp-manual-status');
  if (el) el.textContent = msg;
}

function clearManualCaptureVisuals() {
  manualCapture.markers.forEach(mk => { try { map.removeLayer(mk); } catch {} });
  manualCapture.markers = [];
  if (manualCapture.line) { try { map.removeLayer(manualCapture.line); } catch {} }
  manualCapture.line = null;
  manualCapture.points = [];
}

function cancelManualAxisCapture() {
  if (!map) return;
  manualCapture.active = false;
  map.off('click', onManualMapClick);
  clearManualCaptureVisuals();
  setManualStatus('İptal edildi');
}

function startManualAxisCapture() {
  const m = window._lastClickedMosque;
  if (!m || !map) { toast('Önce bir cami seçin', 2000); return; }
  cancelManualAxisCapture();
  manualCapture.active = true;
  setManualStatus('Haritada 1. noktayı seçin');
  map.on('click', onManualMapClick);
}

function onManualMapClick(e) {
  if (!manualCapture.active) return;
  const p = [e.latlng.lat, e.latlng.lng];
  manualCapture.points.push(p);
  const mk = L.circleMarker(p, { radius:6, color:'#fff', weight:1.5, fillColor:'#c9a84c', fillOpacity:1 }).addTo(map);
  manualCapture.markers.push(mk);
  if (manualCapture.points.length === 1) {
    setManualStatus('2. noktayı seçin');
    return;
  }
  const [a,b] = manualCapture.points;
  manualCapture.line = L.polyline([a,b], { color:'#c9a84c', weight:3, dashArray:'6 4' }).addTo(map);
  const brg = bearing(a[0], a[1], b[0], b[1]);
  const axis = toAxis180(brg);
  const m = window._lastClickedMosque;
  const mod = applyManualAxisSubmission(m, axis, 'map-2point');
  setManualStatus(`AI: ${mod.status.toUpperCase()} · skor ${(mod.score*100|0)}% · aks ${axis.toFixed(1)}°`);
  manualCapture.active = false;
  map.off('click', onManualMapClick);
  renderAll();
  populateDetailPanel(m);
  toast(`Manuel aks ${mod.status === 'accepted' ? 'kabul edildi' : mod.status === 'pending' ? 'incelemeye alındı' : 'reddedildi'}`, 2800);
}

function compassOverlayClick(e) {
  if (e.target === document.getElementById('cmps-overlay')) closeCompass();
}

function openCompass() {
  document.getElementById('cmps-overlay').classList.add('show');
  document.getElementById('btn-compass')?.classList.add('active');
  document.getElementById('btn-map-sync')?.classList.toggle('active', uiState.mapSyncWithCompass);
  startCompass();
}
function closeCompass() {
  document.getElementById('cmps-overlay').classList.remove('show');
  document.getElementById('btn-compass')?.classList.remove('active');
  if (!uiState.liveMapCompass) stopCompass();
  if (uiState.mapSyncWithCompass && !uiState.liveMapCompass) {
    uiState.mapSyncWithCompass = false;
    document.getElementById('btn-map-sync')?.classList.remove('active');
    applyMapHeadingRotation(null);
  }
  updateCompassFabUi();
}

async function requestCompassPermission() {
  try {
    if (typeof DeviceOrientationEvent !== 'undefined' && typeof DeviceOrientationEvent.requestPermission === 'function') {
      const p = await DeviceOrientationEvent.requestPermission();
      if (p !== 'granted') { toast('Sensör izni verilmedi', 2200); return false; }
    }
    startCompass();
    return true;
  } catch {
    toast('Sensör izni alınamadı', 2200);
    return false;
  }
}

function refreshCompassLocation() {
  if (!navigator.geolocation) return;
  navigator.geolocation.getCurrentPosition(pos => {
    setUserGeoState(pos.coords.latitude, pos.coords.longitude, true);
    compassState.loc = { lat: pos.coords.latitude, lng: pos.coords.longitude };
    compassState.qibla = qiblaAngle(compassState.loc.lat, compassState.loc.lng);
    drawCompass();
  }, () => {
    const c = map?.getCenter?.();
    if (c) {
      compassState.loc = { lat:c.lat, lng:c.lng };
      compassState.qibla = qiblaAngle(c.lat, c.lng);
      drawCompass();
    }
  }, { enableHighAccuracy:true, timeout:8000 });
}

function onDeviceOrientation(ev) {
  const raw = ev.webkitCompassHeading != null ? ev.webkitCompassHeading : (ev.absolute ? ev.alpha : null);
  if (raw == null) return;
  compassState.heading = (360 - raw + 360) % 360;
  applyMapHeadingRotation(compassState.heading);
  drawCompass();
}

function startCompass() {
  if (compassState.running) return;
  compassState.running = true;
  refreshCompassLocation();
  window.addEventListener('deviceorientation', onDeviceOrientation, true);
  drawCompass();
}

function stopCompass() {
  compassState.running = false;
  window.removeEventListener('deviceorientation', onDeviceOrientation, true);
}

function drawCompass() {
  const cv = document.getElementById('cmps-canvas');
  const rows = document.getElementById('cmps-rows');
  if (!cv || !rows) return;
  const ctx = cv.getContext('2d');
  const W = cv.width, H = cv.height, cx=W/2, cy=H/2, r=110;
  ctx.clearRect(0,0,W,H);
  ctx.beginPath(); ctx.arc(cx,cy,r,0,Math.PI*2); ctx.fillStyle='#1b4f7f'; ctx.fill();
  ctx.strokeStyle='#6a9ec9'; ctx.lineWidth=2; ctx.stroke();
  for (let d=0; d<360; d+=15) {
    const rr = toRad(d-90);
    const len = d%90===0?14:d%45===0?10:6;
    ctx.beginPath();
    ctx.moveTo(cx+Math.cos(rr)*(r-2), cy+Math.sin(rr)*(r-2));
    ctx.lineTo(cx+Math.cos(rr)*(r-len), cy+Math.sin(rr)*(r-len));
    ctx.strokeStyle = '#84b3d7'; ctx.lineWidth=1; ctx.stroke();
  }
  const heading = compassState.heading;
  const qibla = compassState.qibla;
  if (heading != null) {
    const h = toRad(heading-90);
    ctx.beginPath(); ctx.moveTo(cx,cy);
    ctx.lineTo(cx+Math.cos(h)*(r-28), cy+Math.sin(h)*(r-28));
    ctx.strokeStyle='#60a5fa'; ctx.lineWidth=3; ctx.stroke();
  }
  if (qibla != null) {
    const q = toRad(qibla-90);
    ctx.beginPath(); ctx.moveTo(cx,cy);
    ctx.lineTo(cx+Math.cos(q)*(r-20), cy+Math.sin(q)*(r-20));
    ctx.strokeStyle='#c9a84c'; ctx.lineWidth=3; ctx.setLineDash([6,4]); ctx.stroke(); ctx.setLineDash([]);
  }
  ctx.beginPath(); ctx.arc(cx,cy,4,0,Math.PI*2); ctx.fillStyle='#e8e4d8'; ctx.fill();

  const diff = (heading != null && qibla != null)
    ? Math.min(Math.abs(((qibla-heading)+360)%360), Math.abs(((heading-qibla)+360)%360)).toFixed(1)+'°'
    : '—';
  rows.innerHTML = `
    <div class="lab-row"><span class="lab-k">Cihaz yönü</span><span class="lab-v">${heading!=null?heading.toFixed(1)+'°':'—'}</span></div>
    <div class="lab-row"><span class="lab-k">Kıble yönü</span><span class="lab-v">${qibla!=null?qibla.toFixed(1)+'°':'—'}</span></div>
    <div class="lab-row"><span class="lab-k">Anlık fark</span><span class="lab-v">${diff}</span></div>
    <div class="lab-row"><span class="lab-k">Harita senkronu</span><span class="lab-v">${uiState.mapSyncWithCompass ? 'Açık' : 'Kapalı'}</span></div>
    <div class="lab-row"><span class="lab-k">Konum</span><span class="lab-v">${compassState.loc ? `${compassState.loc.lat.toFixed(4)}, ${compassState.loc.lng.toFixed(4)}` : '—'}</span></div>
  `;
}

function m3dOverlayClick(e) {
  if (e.target === document.getElementById('m3d-overlay')) close3D();
}

async function loadThree() {
  if (window.THREE) return;
  await loadScript('https://unpkg.com/three@0.160.0/build/three.min.js');
}

function dispose3D() {
  if (m3dState.raf) cancelAnimationFrame(m3dState.raf);
  m3dState.raf = 0;
  if (m3dState.renderer) {
    try { m3dState.renderer.dispose(); } catch {}
  }
  m3dState = { renderer:null, scene:null, camera:null, raf:0, obj:null };
}

async function open3D() {
  const m = window._lastClickedMosque;
  if (!m) { toast('Önce bir cami seçin', 2200); return; }
  document.getElementById('m3d-overlay').classList.add('show');
  await loadThree();
  render3DScene(m);
}

function close3D() {
  document.getElementById('m3d-overlay').classList.remove('show');
  dispose3D();
}

function render3DScene(m) {
  const canvas = document.getElementById('m3d-canvas');
  const side = document.getElementById('m3d-side');
  if (!canvas || !window.THREE) return;
  dispose3D();
  const THREE = window.THREE;
  const w = canvas.clientWidth || 700;
  const h = canvas.clientHeight || 420;
  const renderer = new THREE.WebGLRenderer({ canvas, antialias:true });
  renderer.setSize(w, h, false);
  const scene = new THREE.Scene();
  scene.background = new THREE.Color(0x255b89);
  const camera = new THREE.PerspectiveCamera(45, w/h, 1, 5000);
  camera.position.set(0, 180, 300);
  camera.lookAt(0, 0, 0);
  const amb = new THREE.AmbientLight(0xffffff, 0.7);
  scene.add(amb);
  const dir = new THREE.DirectionalLight(0xffffff, 0.8);
  dir.position.set(120, 220, 80);
  scene.add(dir);

  const grid = new THREE.GridHelper(360, 18, 0x333344, 0x1d1d2a);
  scene.add(grid);

  let obj = null;
  if (m.polyCoords && m.polyCoords.length >= 4) {
    const lat0 = m.lat, lng0 = m.lng;
    const pts = m.polyCoords.map(([la,ln]) => ({
      x:(ln-lng0) * Math.cos(toRad(lat0)) * 111320,
      z:(la-lat0) * 111320
    }));
    const shape = new THREE.Shape();
    shape.moveTo(pts[0].x, pts[0].z);
    for (let i=1; i<pts.length; i++) shape.lineTo(pts[i].x, pts[i].z);
    const geo = new THREE.ExtrudeGeometry(shape, { depth:22, bevelEnabled:false });
    geo.rotateX(-Math.PI/2);
    geo.translate(0, 0, 0);
    const mat = new THREE.MeshStandardMaterial({ color:0x4b5563, metalness:0.1, roughness:0.85 });
    obj = new THREE.Mesh(geo, mat);
    scene.add(obj);
  } else {
    const geo = new THREE.BoxGeometry(70, 22, 45);
    const mat = new THREE.MeshStandardMaterial({ color:0x4b5563 });
    obj = new THREE.Mesh(geo, mat);
    scene.add(obj);
  }

  const qDir = m.qibla;
  const aDir = m.axis ?? m.baseAxis;
  const mkLine = (deg, color, len, y=12) => {
    if (deg == null) return null;
    const r = toRad(deg);
    const p2 = new THREE.Vector3(Math.sin(r)*len, y, Math.cos(r)*len);
    const g = new THREE.BufferGeometry().setFromPoints([new THREE.Vector3(0,y,0), p2]);
    const mat = new THREE.LineBasicMaterial({ color });
    const line = new THREE.Line(g, mat);
    scene.add(line);
    return line;
  };
  mkLine(qDir, 0xc9a84c, 140, 15);
  mkLine(aDir, 0x7c6ad8, 120, 13);
  const iAxis = getInteriorAxis(m);
  mkLine(iAxis, 0x4ade80, 100, 11);

  side.innerHTML = `
    <div class="lab-row"><span class="lab-k">Cami</span><span class="lab-v">${escHtml(m.name)}</span></div>
    <div class="lab-row"><span class="lab-k">Kıble</span><span class="lab-v">${m.qibla.toFixed(2)}°</span></div>
    <div class="lab-row"><span class="lab-k">Nihai aks</span><span class="lab-v">${m.axis!=null?m.axis.toFixed(2)+'°':'—'}</span></div>
    <div class="lab-row"><span class="lab-k">İç aks</span><span class="lab-v">${iAxis!=null?iAxis.toFixed(2)+'°':'—'}</span></div>
    <div class="lab-row"><span class="lab-k">Sapma</span><span class="lab-v">${m.diff!=null?m.diff.toFixed(2)+'°':'—'}</span></div>
    <div class="lab-row"><span class="lab-k">Güven</span><span class="lab-v">${m.confidence ?? '—'}/100</span></div>
  `;

  const tick = () => {
    if (obj) obj.rotation.y += 0.004;
    renderer.render(scene, camera);
    m3dState.raf = requestAnimationFrame(tick);
  };
  m3dState = { renderer, scene, camera, raf:0, obj };
  tick();
}



// ══════════════════════════════════════════════════════════════
//  LEADERBOARD (Adım 5)
// ══════════════════════════════════════════════════════════════

const LB_KEY = 'qibla-leaderboard-v2';
const LB_MODE_KEY = 'qibla-leaderboard-mode-v1';

// Pre-seeded cities with approximate data (will be replaced when user analyses them)
const LB_SEEDS = [
  { city:'İstanbul',  country:'Türkiye',  region:'turkey'  },
  { city:'Ankara',    country:'Türkiye',  region:'turkey'  },
  { city:'İzmir',     country:'Türkiye',  region:'turkey'  },
  { city:'Konya',     country:'Türkiye',  region:'turkey'  },
  { city:'Bursa',     country:'Türkiye',  region:'turkey'  },
  { city:'Cairo',     country:'Mısır',    region:'mideast' },
  { city:'Istanbul',  country:'Türkiye',  region:'turkey'  },
  { city:'Tehran',    country:'İran',     region:'mideast' },
  { city:'Baghdad',   country:'Irak',     region:'mideast' },
  { city:'Riyadh',    country:'S.Arabistan', region:'mideast' },
  { city:'Dubai',     country:'BAE',      region:'mideast' },
  { city:'Karachi',   country:'Pakistan', region:'asia'    },
  { city:'Lahore',    country:'Pakistan', region:'asia'    },
  { city:'Dhaka',     country:'Bangladeş',region:'asia'    },
  { city:'Jakarta',   country:'Endonezya',region:'asia'    },
  { city:'Casablanca',country:'Fas',      region:'africa'  },
  { city:'Lagos',     country:'Nijerya',  region:'africa'  },
  { city:'London',    country:'İngiltere',region:'europe'  },
  { city:'Berlin',    country:'Almanya',  region:'europe'  },
  { city:'Paris',     country:'Fransa',   region:'europe'  },
];

let lbData = [];       // array of entry objects
let lbRegion = 'all';
let lbSort = 'pct';
let lbDataset = safeStorageGet(LB_MODE_KEY, 'qibla') === 'admin' ? 'admin' : 'qibla';

// Entry schema:
// { city, country, region, pct, grade, count, withData, avg, min, max, median, perfect, lat, lng, analysedAt, tol }

function lbLoad() {
  try { lbData = JSON.parse(safeStorageGet(LB_KEY, '[]')) || []; } catch { lbData = []; }
}

function lbSave() {
  try { safeStorageSet(LB_KEY, JSON.stringify(lbData)); } catch {}
}

function lbFindEntry(city) {
  return lbData.find(e => trLower(e.city) === trLower(city));
}

function lbUpsert(entry) {
  const idx = lbData.findIndex(e => trLower(e.city) === trLower(entry.city));
  if (idx >= 0) lbData[idx] = entry;
  else lbData.push(entry);
  lbSave();
}

function lbDelete(city) {
  lbData = lbData.filter(e => trLower(e.city) !== trLower(city));
  lbSave();
}

function lbClearAll() {
  if (!confirm('Tüm sıralama verileri silinecek. Emin misiniz?')) return;
  lbData = [];
  lbSave();
  renderLeaderboard();
}

// Detect region from country/city name heuristic
function detectRegion(city, country) {
  const c = trLower(country || '');
  const ci = trLower(city || '');
  if (/turkiye|turkey|türkiye/.test(c+ci)) return 'turkey';
  if (/misir|egypt|irak|iraq|iran|suriye|syria|suudi|saudi|kuveyt|kuwait|katar|qatar|bae|uae|ürdün|jordan|lübnan|lebanon|yemen|oman/.test(c)) return 'mideast';
  if (/pakistan|hindistan|india|banglades|endonezya|indonesia|malezya|malaysia|afganistan|afghanistan/.test(c)) return 'asia';
  if (/fas|morocco|nijerya|nigeria|tanzanya|tanzania|kenya|senegal|tunus|tunisia|libya|cezayir|algeria|etiyopya|ethiopia/.test(c)) return 'africa';
  if (/ingiltere|england|uk|almanya|germany|fransa|france|hollanda|netherlands|ispanya|spain|italya|italy|belcika|belgium/.test(c)) return 'europe';
  return 'other';
}

function gradeColor(grade) {
  return grade==='A'?'#4ade80':grade==='B'?'#a3e635':grade==='C'?'#fbbf24':grade==='D'?'#f87171':'rgba(255,255,255,.50)';
}

function pctColor(pct) {
  if (pct === null) return 'rgba(255,255,255,.50)';
  if (pct >= 80) return '#4ade80';
  if (pct >= 60) return '#a3e635';
  if (pct >= 40) return '#fbbf24';
  return '#f87171';
}

// ── Open / close
function openLeaderboard() {
  lbLoad();
  document.getElementById('lb-overlay').classList.add('show');
  document.getElementById('btn-lb').classList.add('active');
  lbSetDataset(lbDataset, true);
  renderLeaderboard();
}

function closeLeaderboard() {
  document.getElementById('lb-overlay').classList.remove('show');
  document.getElementById('btn-lb').classList.remove('active');
}

function lbOverlayClick(e) {
  if (e.target === document.getElementById('lb-overlay')) closeLeaderboard();
}

// ── Filters & sort
function lbSetRegion(r) {
  lbRegion = r;
  document.querySelectorAll('.lb-filter').forEach(b => b.classList.toggle('active', b.dataset.region === r));
  renderLeaderboard();
}

function lbSetSort(s) {
  lbSort = s;
  document.querySelectorAll('.lb-sort').forEach(b => b.classList.toggle('active', b.dataset.sort === s));
  renderLeaderboard();
}

function lbSetDataset(mode, silent = false) {
  lbDataset = mode === 'admin' ? 'admin' : 'qibla';
  safeStorageSet(LB_MODE_KEY, lbDataset);
  if (lbDataset === 'admin' && (lbSort === 'pct' || lbSort === 'avg')) lbSort = 'count';
  if (lbDataset === 'qibla' && lbSort === 'count') lbSort = 'pct';
  document.querySelectorAll('.lb-mode').forEach(b => b.classList.toggle('active', b.dataset.mode === lbDataset));
  document.querySelectorAll('.lb-sort').forEach(b => b.classList.toggle('active', b.dataset.sort === lbSort));
  const input = document.getElementById('lb-city-input');
  const addBtn = document.getElementById('lb-add-btn');
  if (input) {
    input.placeholder = lbDataset === 'admin'
      ? 'İl/Eyalet yaz... (örn: Konya Province, Türkiye)'
      : 'Şehir ekle... (örn: Konya, Cairo, Lahore)';
  }
  if (addBtn) addBtn.textContent = lbDataset === 'admin' ? '+ Sayımı Çek' : '+ Analiz Et';
  if (!silent) renderLeaderboard();
}

function lbSelectAdminResult(items = []) {
  if (!items.length) return null;
  const prefType = new Set(['administrative','state','province','region','county','municipality']);
  const ranked = items.map(it => {
    let s = 0;
    const cls = trLower(it.class || '');
    const type = trLower(it.type || '');
    const osmType = trLower(it.osm_type || '');
    if (cls === 'boundary') s += 65;
    if (prefType.has(type)) s += 55;
    if (osmType === 'relation') s += 48;
    else if (osmType === 'way') s += 28;
    s += Number(it.importance || 0) * 30;
    return { it, s };
  }).sort((a,b) => b.s - a.s);
  return ranked[0]?.it || items[0];
}

function parseOverpassCount(elements = []) {
  const c = elements.find(x => x.type === 'count');
  const total = Number(c?.tags?.total ?? 0);
  return Number.isFinite(total) ? total : 0;
}

async function fetchMosqueCountByAreaId(areaId) {
  const q = `[out:json][timeout:90];
area(${areaId})->.a;
(
  nwr["amenity"="place_of_worship"]["religion"~"muslim|islam",i](area.a);
  nwr["amenity"="mosque"](area.a);
  nwr["building"="mosque"](area.a);
  nwr["place_of_worship"="mosque"](area.a);
  nwr["mosque"](area.a);
);
out count;`;
  const els = await fetchOverpassQuery(q);
  return parseOverpassCount(els);
}

async function fetchMosqueCountByBbox(s, w, n, e) {
  const q = `[out:json][timeout:90];
(
  nwr["amenity"="place_of_worship"]["religion"~"muslim|islam",i](${s},${w},${n},${e});
  nwr["amenity"="mosque"](${s},${w},${n},${e});
  nwr["building"="mosque"](${s},${w},${n},${e});
  nwr["place_of_worship"="mosque"](${s},${w},${n},${e});
  nwr["mosque"](${s},${w},${n},${e});
);
out count;`;
  const els = await fetchOverpassQuery(q);
  return parseOverpassCount(els);
}

async function lbCountAdminArea(queryText) {
  const btn = document.getElementById('lb-add-btn');
  btn.disabled = true;
  const pw = document.getElementById('lb-progress-wrap');
  const pb = document.getElementById('lb-progress-bar');
  const pl = document.getElementById('lb-progress-label');
  pw.style.display = 'flex';
  pb.style.width = '8%';
  pl.textContent = `"${queryText}" sınırı aranıyor...`;
  try {
    const url = `https://nominatim.openstreetmap.org/search?q=${encodeURIComponent(queryText)}&format=jsonv2&limit=8&addressdetails=1`;
    const hits = await nominatimFetchJson(url, {'Accept-Language':'tr,en'});
    const best = lbSelectAdminResult(hits || []);
    if (!best) throw new Error('İl/eyalet bulunamadı');
    pb.style.width = '40%';
    pl.textContent = 'Sınır bulundu, sayı çekiliyor...';

    const osmType = trLower(best.osm_type || '');
    const osmId = Number(best.osm_id);
    let total = 0;
    if (Number.isFinite(osmId) && (osmType === 'relation' || osmType === 'way')) {
      const areaId = (osmType === 'relation' ? 3600000000 : 2400000000) + osmId;
      total = await fetchMosqueCountByAreaId(areaId);
    } else if (Array.isArray(best.boundingbox) && best.boundingbox.length === 4) {
      const s = Number(best.boundingbox[0]), n = Number(best.boundingbox[1]);
      const w = Number(best.boundingbox[2]), e = Number(best.boundingbox[3]);
      total = await fetchMosqueCountByBbox(s, w, n, e);
    } else {
      throw new Error('Alan sınırı okunamadı');
    }

    pb.style.width = '90%';
    const addr = best.address || {};
    const cityLike = addr.state || addr.county || addr.province || String(best.display_name || '').split(',')[0].trim() || queryText;
    const country = addr.country || '';
    const name = country ? `${cityLike} (${country})` : cityLike;
    const entry = {
      city: name,
      country,
      region: detectRegion(cityLike, country),
      pct: null,
      grade: '—',
      count: total,
      withData: null,
      avg: null, min: null, max: null, median: null, perfect: null,
      lat: Number(best.lat), lng: Number(best.lon),
      analysedAt: new Date().toISOString(),
      tol,
      mode: 'admin-count',
      source: 'overpass-area'
    };
    lbUpsert(entry);
    pb.style.width = '100%';
    pl.textContent = ` ${name}: ${total.toLocaleString()} kayıt`;
    await new Promise(res => setTimeout(res, 550));
    pw.style.display = 'none';
    renderLeaderboard();
    toast(` ${name} sayımı tamamlandı: ${total.toLocaleString()}`, 3600);
  } catch (err) {
    pw.style.display = 'none';
    toast(' İl sayımı hatası: ' + (err?.message || 'bilinmeyen hata'), 5200);
  }
  btn.disabled = false;
}

// ── Filtered + sorted data
function lbFiltered() {
  let d = lbData.filter(e => (lbDataset === 'admin' ? e.mode === 'admin-count' : e.mode !== 'admin-count'));
  if (lbRegion !== 'all') d = d.filter(e => e.region === lbRegion);
  return d.slice().sort((a, b) => {
    if (lbDataset === 'admin') {
      if (lbSort === 'name') return trLower(a.city).localeCompare(trLower(b.city));
      return (b.count||0) - (a.count||0);
    }
    if (lbSort === 'pct') {
      if (a.pct === null && b.pct === null) return 0;
      if (a.pct === null) return 1;
      if (b.pct === null) return -1;
      return b.pct - a.pct;
    }
    if (lbSort === 'count') return (b.count||0) - (a.count||0);
    if (lbSort === 'avg') {
      if (a.avg === null && b.avg === null) return 0;
      if (a.avg === null) return 1;
      if (b.avg === null) return -1;
      return a.avg - b.avg; // lower avg = better
    }
    if (lbSort === 'name') return trLower(a.city).localeCompare(trLower(b.city));
    return 0;
  });
}

// ── Render
function renderLeaderboard() {
  const filtered = lbFiltered();
  lbSetDataset(lbDataset, true);

  const hCity = document.getElementById('lb-h-city');
  const hBar = document.getElementById('lb-h-bar');
  const hPct = document.getElementById('lb-h-pct');
  const hNote = document.getElementById('lb-h-note');
  const hCount = document.getElementById('lb-h-count');
  const hAvg = document.getElementById('lb-h-avg');
  if (lbDataset === 'admin') {
    if (hCity) hCity.textContent = 'İl/Bölge';
    if (hBar) hBar.textContent = 'Yoğunluk';
    if (hPct) hPct.textContent = '—';
    if (hNote) hNote.textContent = 'Tür';
    if (hCount) hCount.textContent = 'Cami+Mescit';
    if (hAvg) hAvg.textContent = 'Kaynak';
  } else {
    if (hCity) hCity.textContent = 'Şehir';
    if (hBar) hBar.textContent = 'Doğruluk';
    if (hPct) hPct.textContent = '%';
    if (hNote) hNote.textContent = 'Not';
    if (hCount) hCount.textContent = 'Cami';
    if (hAvg) hAvg.textContent = 'Ort.Sap.';
  }

  // Summary strip
  const summary = document.getElementById('lb-summary');
  if (lbDataset === 'admin') {
    const adminRows = lbData.filter(e => e.mode === 'admin-count');
    const total = adminRows.length;
    const totalMosques = adminRows.reduce((s, e) => s + (e.count||0), 0);
    const top = adminRows.slice().sort((a,b)=>(b.count||0)-(a.count||0))[0];
    const avgCount = total ? Math.round(totalMosques / total) : null;
    summary.innerHTML = `
      <div class="lb-sum-item"><div class="lb-sum-val">${total}</div><div class="lb-sum-lbl">İl/Bölge</div></div>
      <div class="lb-sum-item"><div class="lb-sum-val">${totalMosques.toLocaleString()}</div><div class="lb-sum-lbl">Toplam Cami+Mescit</div></div>
      <div class="lb-sum-item"><div class="lb-sum-val">${top ? escHtml(top.city) : '—'}</div><div class="lb-sum-lbl">En Yüksek Bölge</div></div>
      <div class="lb-sum-item"><div class="lb-sum-val">${avgCount!==null?avgCount.toLocaleString():'—'}</div><div class="lb-sum-lbl">Ort. Bölge Sayısı</div></div>
    `;
  } else {
    const qRows = lbData.filter(e => e.mode !== 'admin-count');
    const total = qRows.length;
    const analysed = qRows.filter(e => e.pct !== null).length;
    const totalMosques = qRows.reduce((s, e) => s + (e.count||0), 0);
    const avgPct = analysed ? Math.round(qRows.filter(e=>e.pct!==null).reduce((s,e)=>s+e.pct,0)/analysed) : null;
    summary.innerHTML = `
      <div class="lb-sum-item"><div class="lb-sum-val">${total}</div><div class="lb-sum-lbl">Şehir</div></div>
      <div class="lb-sum-item"><div class="lb-sum-val">${analysed}</div><div class="lb-sum-lbl">Analiz Edildi</div></div>
      <div class="lb-sum-item"><div class="lb-sum-val">${totalMosques.toLocaleString()}</div><div class="lb-sum-lbl">Toplam Cami</div></div>
      <div class="lb-sum-item"><div class="lb-sum-val" style="color:${pctColor(avgPct)}">${avgPct!==null?avgPct+'%':'—'}</div><div class="lb-sum-lbl">Ort. Doğruluk</div></div>
    `;
  }

  // Updated timestamp
  const latestDate = lbData.map(e=>e.analysedAt).filter(Boolean).sort().reverse()[0];
  document.getElementById('lb-updated').textContent = latestDate
    ? 'Son güncelleme: ' + new Date(latestDate).toLocaleDateString('tr-TR')
    : '';

  // Rows
  const container = document.getElementById('lb-rows');
  if (!filtered.length) {
    container.innerHTML = `<div class="lb-empty">
      <div class="lb-empty-icon"></div>
      <div>${lbData.length===0
        ? 'Henüz şehir yok — yukarıdan bir şehir ekleyin!'
        : 'Bu bölgede şehir bulunamadı'}</div>
      ${lbData.length===0?`<div style="color:rgba(255,255,255,.50);font-size:11px;margin-top:8px">Örnek: İstanbul, Cairo, Karachi, Jakarta</div>`:''}
    </div>`;
    return;
  }

  const bestVal = lbDataset === 'admin'
    ? Math.max(...filtered.map(e=>e.count||0), 1)
    : Math.max(...filtered.map(e=>e.pct??0), 1);

  container.innerHTML = filtered.map((e, i) => {
    const rank = i + 1;
    const rankClass = rank===1?'lb-rank-1':rank===2?'lb-rank-2':rank===3?'lb-rank-3':'lb-rank-n';
    const rankIcon = rank===1?'':rank===2?'':rank===3?'':rank;
    const col = lbDataset === 'admin' ? '#60a5fa' : pctColor(e.pct);
    const barW = lbDataset === 'admin'
      ? Math.round(((e.count||0) / bestVal) * 100)
      : (e.pct !== null ? Math.round((e.pct/100)*100) : 0);
    const isCurrentCity = trLower(e.city) === trLower(currentCity);
    const needsAnalysis = e.pct === null;
    const dateStr = e.analysedAt ? new Date(e.analysedAt).toLocaleDateString('tr-TR',{day:'2-digit',month:'2-digit',year:'2-digit'}) : '—';
    const citySafe = escHtml(e.city);
    const countrySafe = escHtml(e.country || '');
    const cityEnc = encodeURIComponent(e.city);

    return `<div class="lb-row${isCurrentCity?' current-city':''}${needsAnalysis?' needs-analysis':''}"
         onclick="lbGoCity('${cityEnc}','${e.lat||''}','${e.lng||''}')">
      <span class="lbt-rank ${rankClass}">${rankIcon}</span>
      <span class="lbt-city">
        <span class="lb-city-name">${citySafe}${isCurrentCity?' <span style="font-size:9px;color:#c9a84c">●</span>':''}</span>
        <span class="lb-city-country">${countrySafe} ${e.region?'· '+regionLabel(e.region):''}</span>
      </span>
      <span class="lbt-bar">
        ${e.pct!==null
          ? `<div class="lb-bar-track"><div class="lb-bar-fill" style="width:${barW}%;background:${col}"></div></div>`
          : `<span style="font-size:9px;color:rgba(255,255,255,.50)">analiz bekleniyor</span>`}
      </span>
      <span class="lbt-pct" style="color:${col}">${lbDataset==='admin'?'—':(e.pct!==null?e.pct+'%':'—')}</span>
      <span class="lbt-not">${lbDataset==='admin'?'İl/State':(e.grade&&e.grade!=='—'?`<span style="color:${gradeColor(e.grade)};font-weight:700">${e.grade}</span>`:'—')}</span>
      <span class="lbt-count">${(e.count||0).toLocaleString()}</span>
      <span class="lbt-avg">${lbDataset==='admin'?(e.source || 'overpass'):(e.avg!==null?e.avg.toFixed(1)+'°':'—')}</span>
      <span class="lbt-date">${dateStr}</span>
      <span class="lbt-act">
        ${needsAnalysis
          ? `<button class="lb-act-btn" onclick="event.stopPropagation();${lbDataset==='admin'?'lbCountAdminArea':'lbAnalyseCity'}(decodeURIComponent('${cityEnc}'))">▶ Analiz</button>`
          : `<button class="lb-act-btn" onclick="event.stopPropagation();${lbDataset==='admin'?'lbCountAdminArea':'lbAnalyseCity'}(decodeURIComponent('${cityEnc}'))">↺</button>`}
        <button class="lb-act-btn danger" onclick="event.stopPropagation();lbRemove(decodeURIComponent('${cityEnc}'))"></button>
      </span>
    </div>`;
  }).join('');
}

function regionLabel(r) {
  return {turkey:'Türkiye',mideast:'Orta Doğu',asia:'Güney Asya',africa:'Afrika',europe:'Avrupa',other:'Diğer'}[r]||r;
}

// ── Navigate to city on map
function lbGoCity(cityEnc, lat, lng) {
  const city = decodeURIComponent(cityEnc);
  if (lat && lng) {
    focusMapLatLng(+lat, +lng, 13);
  }
  closeLeaderboard();
  document.getElementById('city-input').value = city;
  doSearch();
}

// ── Remove entry
function lbRemove(city) {
  lbDelete(city);
  renderLeaderboard();
}

// ── Add city via input
async function lbAddCity() {
  const input = document.getElementById('lb-city-input');
  const city = input.value.trim();
  if (!city) return;
  input.value = '';
  if (lbDataset === 'admin') await lbCountAdminArea(city);
  else await lbAnalyseCity(city);
}

// ── Core: analyse a city and store result
async function lbAnalyseCity(city) {
  const btn = document.getElementById('lb-add-btn');
  btn.disabled = true;

  // Show progress
  const pw = document.getElementById('lb-progress-wrap');
  const pb = document.getElementById('lb-progress-bar');
  const pl = document.getElementById('lb-progress-label');
  pw.style.display = 'flex';
  pb.style.width = '5%';
  pl.textContent = `"${city}" analiz ediliyor...`;

  try {
    pb.style.width = '15%'; pl.textContent = 'Koordinatlar alınıyor...';
    const loc = await geocode(city);

    pb.style.width = '35%'; pl.textContent = 'Camiler yükleniyor...';
    const r = 0.072; // ~8km radius
    const elements = await fetchBbox(loc.lat-r, loc.lng-r, loc.lat+r, loc.lng+r);

    pb.style.width = '75%'; pl.textContent = `${elements.length} cami işleniyor...`;
    await new Promise(res => setTimeout(res, 20));

    // Analyse into temp map
    const tempDB = new Map();
    for (const el of elements) {
      let lat0, lng0, polyCoords = null;
      if (el.type==='node') { lat0=el.lat; lng0=el.lon; }
      else if (el.type==='way'&&el.geometry) {
        const pts=el.geometry;
        lat0=pts.reduce((s,p)=>s+p.lat,0)/pts.length;
        lng0=pts.reduce((s,p)=>s+p.lon,0)/pts.length;
        polyCoords=pts.map(p=>[p.lat,p.lon]);
      } else continue;

      const qibla = qiblaAngle(lat0, lng0);
      let axis=null, diff=null;
      const dt = el.tags?.direction||el.tags?.['building:direction'];
      if (dt&&!isNaN(+dt)) { axis=+dt%180; diff=angDiff180(qibla%180,axis); }
      else if (polyCoords&&polyCoords.length>=4) {
        const res = buildingQiblaEdge(polyCoords, qibla);
        if (res) { axis=res.angle; diff=res.diff; }
      }
      tempDB.set(el.id, {
        diff, status: diff!==null?(diff<=tol?'correct':'wrong'):'unknown'
      });
    }

    pb.style.width = '90%'; pl.textContent = 'Skor hesaplanıyor...';
    const st = computeStats(tempDB);

    // Detect country & region from nominatim display_name
    let country = '', region = 'other';
    try {
      const geoData = await nominatimFetchJson(`https://nominatim.openstreetmap.org/search?q=${encodeURIComponent(city)}&format=json&limit=1&addressdetails=1`, {'Accept-Language':'tr'});
      if (geoData[0]?.address) {
        country = geoData[0].address.country || '';
        region = detectRegion(city, country);
      }
    } catch {}

    const entry = {
      city, country, region,
      pct: st.pct, grade: st.grade,
      count: st.all, withData: st.withData,
      avg: st.avg, min: st.min, max: st.max, median: st.median, perfect: st.perfect,
      lat: loc.lat, lng: loc.lng,
      analysedAt: new Date().toISOString(),
      tol
    };

    lbUpsert(entry);
    pb.style.width = '100%'; pl.textContent = ` ${city} eklendi`;
    await new Promise(res => setTimeout(res, 600));
    pw.style.display = 'none';
    renderLeaderboard();
    toast(` ${city} sıralamaya eklendi — ${st.pct!==null?st.pct+'% doğru':'veri yetersiz'}`, 4000);

  } catch(err) {
    pw.style.display = 'none';
    toast(' ' + err.message, 6000);
    console.error(err);
  }

  btn.disabled = false;
}

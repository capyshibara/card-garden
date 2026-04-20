import { initializeApp } from "https://www.gstatic.com/firebasejs/12.12.0/firebase-app.js";
import { getAuth, GoogleAuthProvider, signInWithPopup, signInWithRedirect, getRedirectResult, onAuthStateChanged, signOut, setPersistence, browserLocalPersistence } from "https://www.gstatic.com/firebasejs/12.12.0/firebase-auth.js";
import { getFirestore, collection, doc, getDocs, setDoc, onSnapshot, writeBatch } from "https://www.gstatic.com/firebasejs/12.12.0/firebase-firestore.js";
import { marked } from "https://cdn.jsdelivr.net/npm/marked/lib/marked.esm.js";

const CARDS_KEY = "cg-v15-cards";
const CARDS_BACKUP_KEY = "cg-v15-cards-backup";
const UI_KEY = "cg-v15-ui";
const CLOUD_KEY = "cg-v15-cloud";
const MIGRATED_USERS_KEY = "cg-v40-migrated-users";

const LEGACY_SOURCES = [
  "cg-v14-cards",
  "cg-v14-cards-backup",
  "card-garden-v13-app",
  "card-garden-v13-app-backup",
  "card-garden-v10-app",
  "card-garden-v10-app-backup",
  "card-garden-v8-app",
  "card-garden-v8-app-backup",
  "card-garden-v7-cards",
  "card-garden-v6"
];

const STATUS_VALUES = ["To learn", "Learning", "Learnt"];
const UI_DEFAULTS = { tab: "home", dismissedIds: [] };
const FIREBASE_CONFIG = {
  apiKey: "AIzaSyDdCD-08K9L25KGdMxFh1OB_V-akFaAQaA",
  authDomain: "card-garden-d6c8f.firebaseapp.com",
  projectId: "card-garden-d6c8f",
  storageBucket: "card-garden-d6c8f.firebasestorage.app",
  messagingSenderId: "69133538887",
  appId: "1:69133538887:web:865e372186a94d268c0362"
};

const APP_VERSION = "Card Garden v51";
const AUTH_REDIRECT_FLAG = "cg-auth-redirect-pending";

marked.setOptions({ gfm: true, breaks: true });

let firebaseApp = null;
let firebaseAuth = null;
let firestoreDb = null;
let unsubscribeCloud = null;
let cloudReady = false;
let cloudSyncing = false;
let authReady = false;
let remoteCardIds = new Set();
let stampFaceObserver = null;

function cryptoSafeId() {
  return (window.crypto && crypto.randomUUID) ? crypto.randomUUID() : String(Date.now() + Math.random());
}

function safeParse(json) {
  try { return JSON.parse(json); } catch { return null; }
}

function escapeHtml(text) {
  return String(text || "")
    .replaceAll("&", "&amp;")
    .replaceAll("<", "&lt;")
    .replaceAll(">", "&gt;")
    .replaceAll('"', "&quot;")
    .replaceAll("'", "&#39;");
}

function stripHtml(html) {
  const div = document.createElement("div");
  div.innerHTML = html || "";
  return div.textContent || div.innerText || "";
}

function cssEscape(value) {
  return String(value || "").replace(/["\\]/g, "\\$&");
}

function preview(html, max = 220) {
  const text = stripHtml(html).replace(/\s+/g, " ").trim();
  return text.length > max ? text.slice(0, max).trim() + "…" : text;
}

function firstLine(html) {
  const text = stripHtml(html || "");
  return text.split("\n").find(Boolean) || text;
}

function detectLikelyHtml(text = "") {
  return /<\/?[a-z][\s\S]*>/i.test(String(text || ""));
}

function normalizeTextSource(value) {
  return typeof value === "string" ? value.replace(/\r\n?/g, "\n") : "";
}

function sanitizeStyleValue(styleText = "") {
  const allowedProps = new Set(["font-size", "font-family", "text-align"]);
  return String(styleText)
    .split(";")
    .map(part => part.trim())
    .filter(Boolean)
    .map(part => {
      const idx = part.indexOf(":");
      if (idx === -1) return null;
      const prop = part.slice(0, idx).trim().toLowerCase();
      const value = part.slice(idx + 1).trim();
      if (!allowedProps.has(prop)) return null;
      if (/url\(|expression\(|javascript:/i.test(value)) return null;
      return `${prop}:${value}`;
    })
    .filter(Boolean)
    .join("; ");
}

function sanitizeRichHtml(html = "") {
  const template = document.createElement("template");
  template.innerHTML = String(html || "");

  const allowedTags = new Set([
    "p", "br", "strong", "em", "b", "i", "u", "s",
    "ul", "ol", "li", "blockquote", "code", "pre",
    "a", "span", "font", "div", "h1", "h2", "h3", "h4", "h5", "h6", "hr"
  ]);
  const blockedTags = new Set(["script", "style", "iframe", "object", "embed", "link", "meta"]);

  function clean(node) {
    if (node.nodeType === Node.TEXT_NODE) return;
    if (node.nodeType !== Node.ELEMENT_NODE) {
      node.remove();
      return;
    }

    const tag = node.tagName.toLowerCase();
    if (blockedTags.has(tag)) {
      node.remove();
      return;
    }

    if (!allowedTags.has(tag)) {
      const fragment = document.createDocumentFragment();
      [...node.childNodes].forEach(child => {
        clean(child);
        fragment.appendChild(child);
      });
      node.replaceWith(fragment);
      return;
    }

    [...node.attributes].forEach(attr => {
      const name = attr.name.toLowerCase();
      const value = attr.value || "";
      if (name.startsWith("on")) {
        node.removeAttribute(attr.name);
        return;
      }
      if (name === "style") {
        const safeStyle = sanitizeStyleValue(value);
        if (safeStyle) node.setAttribute("style", safeStyle);
        else node.removeAttribute("style");
        return;
      }
      if (tag === "a" && name === "href") {
        if (/^(https?:|mailto:|tel:|#)/i.test(value.trim())) {
          node.setAttribute("href", value.trim());
          node.setAttribute("target", "_blank");
          node.setAttribute("rel", "noopener noreferrer");
        } else {
          node.removeAttribute("href");
        }
        return;
      }
      if (tag === "font" && (name === "size" || name === "face" || name === "color")) return;
      if (["class", "id", "title", "aria-label", "role", "data-placeholder"].includes(name)) return;
      node.removeAttribute(attr.name);
    });

    [...node.childNodes].forEach(clean);
  }

  [...template.content.childNodes].forEach(clean);
  return template.innerHTML;
}

function plaintextToHtml(text = "") {
  const normalized = normalizeTextSource(text).trim();
  if (!normalized) return "";
  return normalized
    .split(/\n{2,}/)
    .map(block => `<p>${escapeHtml(block).replace(/\n/g, "<br>")}</p>`)
    .join("");
}

function markdownToHtml(markdown = "") {
  const rendered = marked.parse(normalizeTextSource(markdown || ""));
  return sanitizeRichHtml(rendered);
}

function sourceTextToHtml(text = "", explicitFormat = "") {
  const source = normalizeTextSource(text);
  const format = String(explicitFormat || "").toLowerCase();
  if (!source.trim()) return "";
  if (format === "html" || format === "richtext") return sanitizeRichHtml(source);
  if (format === "plain" || format === "text") return plaintextToHtml(source);
  if (format === "markdown" || format === "md") return markdownToHtml(source);
  if (detectLikelyHtml(source)) return sanitizeRichHtml(source);
  return markdownToHtml(source);
}

function normalizeEditorHtml(html) {
  const normalized = String(html || "")
    .replace(/<div><br><\/div>/gi, "<p><br></p>")
    .replace(/<div>/gi, "<p>")
    .replace(/<\/div>/gi, "</p>")
    .trim();
  return sanitizeRichHtml(normalized);
}

function parseLabels(raw) {
  if (Array.isArray(raw)) return raw.map(v => String(v || "").trim()).filter(Boolean);
  if (typeof raw === "string") {
    return raw
      .split(/[;,\n]/)
      .map(v => v.trim())
      .filter(Boolean);
  }
  return [];
}

function labelsTextFromRaw(raw) {
  return parseLabels(raw).join(", ");
}

function getFirstString(raw, keys = []) {
  for (const key of keys) {
    if (typeof raw?.[key] === "string" && raw[key].trim()) return raw[key];
  }
  return "";
}

function normalizeStoredContent(rawValue, rawFormat = "") {
  if (typeof rawValue !== "string") return "";
  return sourceTextToHtml(rawValue, rawFormat || (detectLikelyHtml(rawValue) ? "html" : "plain"));
}

function normalizeCard(raw = {}, index = 0) {
  const labels = parseLabels(raw.labels?.length ? raw.labels : (raw.label || raw.tags || raw.category || ""));
  const status = STATUS_VALUES.includes(raw.status) ? raw.status : "Learning";
  const frontSource = getFirstString(raw, ["frontHtml", "frontRich", "frontMarkdown", "frontMd", "frontText", "front", "question", "prompt", "term", "title"]);
  const backSource = getFirstString(raw, ["backHtml", "backRich", "backMarkdown", "backMd", "backText", "back", "answer", "response", "definition", "content"]);
  const frontFormat = raw.frontHtml || raw.frontRich ? "html" : (raw.frontMarkdown || raw.frontMd ? "markdown" : raw.frontFormat || "");
  const backFormat = raw.backHtml || raw.backRich ? "html" : (raw.backMarkdown || raw.backMd ? "markdown" : raw.backFormat || "");

  return {
    id: String(raw.id || cryptoSafeId()),
    front: normalizeStoredContent(frontSource, frontFormat),
    back: normalizeStoredContent(backSource, backFormat),
    labels,
    status,
    position: Number.isFinite(raw.position) ? Number(raw.position) : index + 1,
    createdAt: typeof raw.createdAt === "string" ? raw.createdAt : new Date().toISOString(),
    updatedAt: typeof raw.updatedAt === "string" ? raw.updatedAt : new Date().toISOString()
  };
}

function reindexCards(cards) {
  return cards
    .slice()
    .sort((a, b) => (a.position - b.position) || a.createdAt.localeCompare(b.createdAt))
    .map((card, index) => ({ ...card, position: index + 1 }));
}

function sortCardsByPosition(cards = state.cards) {
  return cards.slice().sort((a, b) => a.position - b.position || a.createdAt.localeCompare(b.createdAt));
}

function normalizeCloud(raw = {}) {
  const cfg = raw.config || {};
  return {
    enabled: Boolean(raw.enabled),
    config: {
      apiKey: typeof cfg.apiKey === "string" ? cfg.apiKey.trim() : "",
      authDomain: typeof cfg.authDomain === "string" ? cfg.authDomain.trim() : "",
      projectId: typeof cfg.projectId === "string" ? cfg.projectId.trim() : "",
      storageBucket: typeof cfg.storageBucket === "string" ? cfg.storageBucket.trim() : "",
      messagingSenderId: typeof cfg.messagingSenderId === "string" ? cfg.messagingSenderId.trim() : "",
      appId: typeof cfg.appId === "string" ? cfg.appId.trim() : ""
    }
  };
}

function normalizeUI(raw = {}) {
  return {
    tab: ["home", "cards", "metrics"].includes(raw.tab) ? raw.tab : UI_DEFAULTS.tab,
    dismissedIds: Array.isArray(raw.dismissedIds) ? raw.dismissedIds.filter(Boolean) : []
  };
}

function loadCards() {
  const primary = safeParse(localStorage.getItem(CARDS_KEY));
  if (Array.isArray(primary)) return reindexCards(primary.map((c, i) => normalizeCard(c, i)));

  const backup = safeParse(localStorage.getItem(CARDS_BACKUP_KEY));
  if (Array.isArray(backup)) {
    const restored = reindexCards(backup.map((c, i) => normalizeCard(c, i)));
    localStorage.setItem(CARDS_KEY, JSON.stringify(restored));
    return restored;
  }

  for (const key of LEGACY_SOURCES) {
    const parsed = safeParse(localStorage.getItem(key));
    if (!parsed) continue;
    const list = Array.isArray(parsed) ? parsed : (Array.isArray(parsed.cards) ? parsed.cards : null);
    if (!list) continue;
    const migrated = reindexCards(list.map((c, i) => normalizeCard(c, i)));
    localStorage.setItem(CARDS_KEY, JSON.stringify(migrated));
    localStorage.setItem(CARDS_BACKUP_KEY, JSON.stringify(migrated));
    return migrated;
  }

  return [];
}

function loadUI() {
  return normalizeUI(safeParse(localStorage.getItem(UI_KEY)) || {});
}

function loadCloud() {
  return { enabled: true, config: { ...FIREBASE_CONFIG } };
}

function loadMigratedUsers() {
  const saved = safeParse(localStorage.getItem(MIGRATED_USERS_KEY));
  return Array.isArray(saved) ? new Set(saved.filter(Boolean)) : new Set();
}

function persistMigratedUsers() {
  localStorage.setItem(MIGRATED_USERS_KEY, JSON.stringify([...state.migratedUserIds]));
}

function emptyImportDraft() {
  return { rawText: "", sourceName: "", items: [] };
}

const uiState = loadUI();

let state = {
  tab: uiState.tab,
  route: "root",
  selectedId: null,
  cards: loadCards(),
  dismissedIds: new Set(uiState.dismissedIds),
  flippedIds: new Set(),
  formLabels: [],
  cardsSelectionMode: false,
  selectedCardIds: new Set(),
  importDraft: emptyImportDraft(),
  cloud: loadCloud(),
  user: null,
  migratedUserIds: loadMigratedUsers(),
  cardFilters: { statuses: [], labels: [] },
  filterModalOpen: false
};

function persistCardsLocal() {
  const cards = reindexCards(state.cards.map((card, index) => normalizeCard(card, index)));
  state.cards = cards;
  const serialized = JSON.stringify(cards);
  localStorage.setItem(CARDS_KEY, serialized);
  localStorage.setItem(CARDS_BACKUP_KEY, serialized);
}

function persistUI() {
  localStorage.setItem(UI_KEY, JSON.stringify({
    tab: state.tab,
    dismissedIds: [...state.dismissedIds]
  }));
}

function persistCloudConfig() {
  localStorage.setItem(CLOUD_KEY, JSON.stringify({ enabled: true, config: { ...FIREBASE_CONFIG } }));
}

function persistLocalAll() {
  persistCardsLocal();
  persistUI();
  persistCloudConfig();
}

document.addEventListener("visibilitychange", () => {
  if (document.visibilityState === "hidden") persistLocalAll();
});
window.addEventListener("pagehide", persistLocalAll);
window.addEventListener("beforeunload", persistLocalAll);

function hasCloudConfig(cfg = FIREBASE_CONFIG) {
  return Boolean(cfg.apiKey && cfg.authDomain && cfg.projectId && cfg.appId);
}

function ensureFirebase() {
  if (firebaseApp) return;
  firebaseApp = initializeApp(FIREBASE_CONFIG);
  firebaseAuth = getAuth(firebaseApp);
  firestoreDb = getFirestore(firebaseApp);
}

async function configureAuthPersistence() {
  ensureFirebase();
  try {
    await setPersistence(firebaseAuth, browserLocalPersistence);
  } catch (error) {
    console.warn("Could not set auth persistence", error);
  }
}

function isMobileDevice() {
  const ua = navigator.userAgent || "";
  return /iPhone|iPad|iPod|Android/i.test(ua);
}

function isLegacyMobileRedirectPreferred() {
  const ua = navigator.userAgent || "";
  return /iPhone|iPad|iPod|Android/i.test(ua);
}

function cardsCollectionRef(userId) {
  return collection(firestoreDb, "users", userId, "cards");
}

async function stopCloud() {
  if (unsubscribeCloud) {
    unsubscribeCloud();
    unsubscribeCloud = null;
  }
  cloudReady = false;
  remoteCardIds = new Set();
}

async function writeAllCardsForUser(userId) {
  if (!firestoreDb || !userId) return;
  const cardsRef = cardsCollectionRef(userId);
  const currentIds = new Set(state.cards.map(card => card.id));
  const batch = writeBatch(firestoreDb);

  remoteCardIds.forEach(cardId => {
    if (!currentIds.has(cardId)) batch.delete(doc(firestoreDb, "users", userId, "cards", cardId));
  });

  state.cards.forEach((card, index) => {
    const normalized = normalizeCard({ ...card, position: index + 1 }, index);
    batch.set(doc(firestoreDb, "users", userId, "cards", normalized.id), normalized, { merge: true });
  });

  await batch.commit();
  remoteCardIds = currentIds;
}

async function migrateLocalCardsIfNeeded(user) {
  if (!user || !state.cards.length || state.migratedUserIds.has(user.uid)) return;
  const cardsRef = cardsCollectionRef(user.uid);
  const existing = await getDocs(cardsRef);
  if (!existing.empty) {
    remoteCardIds = new Set(existing.docs.map(item => item.id));
    state.migratedUserIds.add(user.uid);
    persistMigratedUsers();
    return;
  }
  await writeAllCardsForUser(user.uid);
  state.migratedUserIds.add(user.uid);
  persistMigratedUsers();
}

async function startCloud(user) {
  await stopCloud();
  if (!user) return;
  ensureFirebase();
  const cardsRef = cardsCollectionRef(user.uid);
  const first = await getDocs(cardsRef);
  remoteCardIds = new Set(first.docs.map(item => item.id));
  if (first.empty) {
    await migrateLocalCardsIfNeeded(user);
  }
  unsubscribeCloud = onSnapshot(cardsRef, (snap) => {
    cloudReady = true;
    remoteCardIds = new Set(snap.docs.map(item => item.id));
    state.cards = reindexCards(snap.docs.map((item, index) => normalizeCard(item.data(), index)));
    persistCardsLocal();
    render();
  }, (error) => {
    console.error(error);
    cloudReady = false;
    showToast("Sync error");
    render();
  });
}

async function persistCloudCards() {
  if (!state.user || !firestoreDb) return;
  cloudSyncing = true;
  render();
  try {
    await writeAllCardsForUser(state.user.uid);
  } finally {
    cloudSyncing = false;
    render();
  }
}

async function persistCardsEverywhere() {
  persistCardsLocal();
  await persistCloudCards();
}

const appEl = document.getElementById("app");
const titleEl = document.getElementById("headerTitle");
const eyebrowEl = document.getElementById("headerEyebrow");
const backButton = document.getElementById("backButton");
const toastEl = document.getElementById("toast");
const navItems = [...document.querySelectorAll(".nav-item")];
const topbarActions = document.getElementById("topbarActions");

function clearCardSelection() {
  state.cardsSelectionMode = false;
  state.selectedCardIds.clear();
}

function resetImportDraft() {
  state.importDraft = emptyImportDraft();
}

document.querySelector(".bottom-nav").addEventListener("click", (e) => {
  const btn = e.target.closest(".nav-item");
  if (!btn) return;
  state.tab = btn.dataset.tab;
  state.route = "root";
  state.selectedId = null;
  clearCardSelection();
  if (state.tab !== "cards") resetImportDraft();
  persistUI();
  render();
});

backButton.addEventListener("click", () => {
  if (state.route === "import") resetImportDraft();
  state.route = "root";
  state.selectedId = null;
  render();
});

topbarActions.addEventListener("click", async (e) => {
  const action = e.target.closest("[data-action]");
  if (!action) return;
  const type = action.dataset.action;
  if (type === "open-create") return openCreate();
  if (type === "sign-in-google") return signInWithGoogle();
  if (type === "sign-out") return signOutUser();
  if (type === "reset-form") return resetForm();
  if (type === "open-import") return openImport();
  if (type === "open-filter-modal") {
    state.filterModalOpen = true;
    render();
    return;
  }
  if (type === "sign-in-google") return signInWithGoogle();
  if (type === "sign-out") return signOutUser();
  if (type === "toggle-card-selection-mode") {
    state.cardsSelectionMode = !state.cardsSelectionMode;
    if (!state.cardsSelectionMode) state.selectedCardIds.clear();
    render();
    return;
  }
  if (type === "cancel-card-selection") {
    clearCardSelection();
    render();
    return;
  }
  if (type === "select-all-cards") {
    selectAllCards();
    render();
    return;
  }
  if (type === "deselect-all-cards") {
    state.selectedCardIds.clear();
    render();
    return;
  }
  if (type === "delete-selected-cards") {
    await deleteSelectedCards();
  }
});


function exportJsonFromState() {
  const data = Array.isArray(state.cards) ? state.cards : [];
  if (!data.length) {
    showToast("No cards to export");
    return;
  }
  const blob = new Blob([JSON.stringify(data, null, 2)], { type: "application/json" });
  const url = URL.createObjectURL(blob);
  const a = document.createElement("a");
  a.href = url;
  a.download = "card-garden.json";
  document.body.appendChild(a);
  a.click();
  setTimeout(() => {
    URL.revokeObjectURL(url);
    a.remove();
  }, 300);
  showToast("JSON exported");
}

appEl.addEventListener("click", async (e) => {
  const action = e.target.closest("[data-action]");
  if (!action) return;
  const type = action.dataset.action;
  const id = action.dataset.id;

  if (type === "dismiss-home-card") {
    e.preventDefault();
    e.stopPropagation();
    return handleHomeCardDismiss(id);
  }
  if (type === "open-filter-modal") {
    state.filterModalOpen = true;
    render();
    return;
  }
  if (type === "close-filter-modal") {
    state.filterModalOpen = false;
    render();
    return;
  }
  if (type === "clear-card-filters") {
    state.cardFilters = { statuses: [], labels: [] };
    state.filterModalOpen = false;
    render();
    return;
  }
  if (type === "clear-filter-form") {
    const form = document.getElementById("cardFilterForm");
    if (form) {
      form.querySelectorAll('input[name="filter-status"], input[name="filter-label"]').forEach(input => {
        input.checked = false;
      });
      syncFilterDraftUi();
    }
    return;
  }
  if (type === "noop-filter-modal") {
    return;
  }
  if (type === "open-create") return openCreate();
  if (type === "sign-in-google") return signInWithGoogle();
  if (type === "sign-out") return signOutUser();
  if (type === "open-detail") return openDetail(id);
  if (type === "open-edit") return openEdit(id);
  if (type === "home-card-tap") return handleHomeCardTap(id, e);
  if (type === "restart-home") {
    state.dismissedIds.clear();
    state.flippedIds.clear();
    persistUI();
    render();
    return;
  }
  if (type === "flip-detail-card") {
    const detailCard = document.getElementById("detailFlipCard");
    if (detailCard) detailCard.classList.toggle("flipped");
    return;
  }
  if (type === "set-status") return setStatus(id, action.dataset.status);
  if (type === "delete-card") return deleteCard(id);
  if (type === "move-up") return moveCard(id, -1);
  if (type === "move-down") return moveCard(id, 1);
  if (type === "remove-form-label") return removeFormLabel(action.dataset.label);
  if (type === "save-cloud-config") return saveCloudConfig();
  if (type === "disable-cloud") return disableCloud();

  if (type === "toggle-card-selection" || type === "toggle-card-selection-row") {
    toggleCardSelection(id);
    render();
    return;
  }
  if (type === "select-all-cards") {
    selectAllCards();
    render();
    return;
  }
  if (type === "deselect-all-cards") {
    state.selectedCardIds.clear();
    render();
    return;
  }
  if (type === "delete-selected-cards") return deleteSelectedCards();

  if (type === "choose-import-file") {
    document.getElementById("importFileInput")?.click();
    return;
  }
  if (type === "parse-import-json") return parseImportFromTextarea();
  if (type === "clear-import-draft") {
    resetImportDraft();
    render();
    return;
  }
  if (type === "toggle-import-select" || type === "toggle-import-select-row") {
    toggleImportSelection(id);
    render();
    return;
  }
  if (type === "select-all-import") {
    selectAllImportItems(true);
    render();
    return;
  }
  if (type === "deselect-all-import") {
    selectAllImportItems(false);
    render();
    return;
  }
  if (type === "import-selected-cards") return importSelectedCards();
  if (type === "export-json") return exportJsonFromState();
});

appEl.addEventListener("change", async (e) => {
  if (e.target.id === "importFileInput") {
    await handleImportFileChosen(e.target);
    return;
  }
  const checkbox = e.target.closest("[data-action='toggle-card-selection']");
  if (checkbox) {
    toggleCardSelection(checkbox.dataset.id, checkbox.checked);
    return;
  }
  const importCheckbox = e.target.closest("[data-action='toggle-import-select']");
  if (importCheckbox) {
    toggleImportSelection(importCheckbox.dataset.id, importCheckbox.checked);
  }
  if (e.target.matches('input[name="filter-status"], input[name="filter-label"]')) {
    syncFilterDraftUi();
  }
});

appEl.addEventListener("keydown", (e) => {
  if (e.target.id === "labelInput" && e.key === "Enter") {
    e.preventDefault();
    addFormLabel();
  }
});

appEl.addEventListener("submit", async (e) => {
  if (e.target.matches("#cardFilterForm")) {
    e.preventDefault();
    applyCardFiltersFromForm();
    return;
  }
  if (!e.target.matches("#cardForm")) return;
  e.preventDefault();

  const labelInput = document.getElementById("labelInput");
  if (labelInput && labelInput.value.trim()) addFormLabel();

  const frontEditor = document.getElementById("frontEditor");
  const backEditor = document.getElementById("backEditor");
  const front = normalizeEditorHtml(frontEditor?.innerHTML || "");
  const back = normalizeEditorHtml(backEditor?.innerHTML || "");
  const frontText = stripHtml(front).trim();
  const backText = stripHtml(back).trim();

  if (!frontText || !backText) {
    showToast("Please fill both sides");
    return;
  }

  const now = new Date().toISOString();

  if (state.route === "edit" && state.selectedId) {
    const card = state.cards.find(item => item.id === state.selectedId);
    if (!card) return;
    card.front = front;
    card.back = back;
    card.labels = [...state.formLabels];
    card.updatedAt = now;
    await persistCardsEverywhere();
    state.route = "detail";
    render();
    showToast("Card updated");
    return;
  }

  const nextPosition = state.cards.length ? Math.max(...state.cards.map(c => Number(c.position) || 0)) + 1 : 1;
  const card = normalizeCard({
    id: cryptoSafeId(),
    front,
    back,
    frontFormat: "html",
    backFormat: "html",
    labels: [...state.formLabels],
    status: "Learning",
    position: nextPosition,
    createdAt: now,
    updatedAt: now
  }, nextPosition - 1);

  state.cards.push(card);
  await persistCardsEverywhere();
  state.formLabels = [];
  state.route = "root";
  state.tab = "cards";
  state.selectedId = null;
  clearCardSelection();
  render();
  showToast("Card created");
});

function openCreate() {
  state.tab = "cards";
  state.route = "create";
  state.selectedId = null;
  state.formLabels = [];
  clearCardSelection();
  render();
}

function openImport() {
  state.tab = "cards";
  state.route = "import";
  state.selectedId = null;
  clearCardSelection();
  render();
}

function openDetail(id) {
  clearCardSelection();
  state.route = "detail";
  state.selectedId = id;
  render();
}

function openEdit(id) {
  const card = state.cards.find(item => item.id === id);
  if (!card) return;
  clearCardSelection();
  state.route = "edit";
  state.selectedId = id;
  state.formLabels = [...card.labels];
  render();
}

function handleHomeCardTap(id, event) {
  if (event?.target?.closest(".home-dismiss")) return;
  const cardEl = appEl.querySelector(`.home-card-shell[data-id="${cssEscape(id)}"] .home-card`);
  if (!cardEl) return;
  if (state.flippedIds.has(id)) {
    state.flippedIds.delete(id);
    cardEl.classList.remove("flipped");
  } else {
    state.flippedIds.add(id);
    cardEl.classList.add("flipped");
  }
}

function handleHomeCardDismiss(id) {
  const cardShell = appEl.querySelector(`.home-card-shell[data-id="${cssEscape(id)}"]`);
  state.dismissedIds.add(id);
  state.flippedIds.delete(id);
  persistUI();
  if (cardShell) {
    cardShell.classList.add("is-hidden");
    setTimeout(() => renderHome(), 340);
    return;
  }
  renderHome();
}

function syncHomeCardState() {
  const cardShells = appEl.querySelectorAll(".home-card-shell");
  cardShells.forEach(shell => {
    const id = shell.dataset.id;
    const innerCard = shell.querySelector(".home-card");
    if (!innerCard) return;
    innerCard.classList.toggle("flipped", state.flippedIds.has(id));
    shell.classList.toggle("is-hidden", state.dismissedIds.has(id));
  });
}

function addFormLabel() {
  const input = document.getElementById("labelInput");
  const container = document.getElementById("formLabels");
  if (!input || !container) return;
  const value = input.value.trim();
  if (!value) return;
  const exists = state.formLabels.some(label => label.toLowerCase() === value.toLowerCase());
  if (!exists) state.formLabels.push(value);
  input.value = "";
  container.innerHTML = renderLabels(state.formLabels, true);
}

function removeFormLabel(labelValue) {
  state.formLabels = state.formLabels.filter(label => label !== labelValue);
  const container = document.getElementById("formLabels");
  if (container) container.innerHTML = renderLabels(state.formLabels, true);
}

async function setStatus(id, status) {
  const card = state.cards.find(item => item.id === id);
  if (!card || !STATUS_VALUES.includes(status)) return;
  card.status = status;
  card.updatedAt = new Date().toISOString();
  await persistCardsEverywhere();
  render();
  showToast("Status updated");
}

async function moveCard(id, direction) {
  const ordered = sortCardsByPosition(state.cards);
  const index = ordered.findIndex(card => card.id === id);
  const swapIndex = index + direction;
  if (index < 0 || swapIndex < 0 || swapIndex >= ordered.length) return;
  const currentPosition = ordered[index].position;
  ordered[index].position = ordered[swapIndex].position;
  ordered[swapIndex].position = currentPosition;
  state.cards = reindexCards(ordered);
  await persistCardsEverywhere();
  render();
}

async function deleteCard(id) {
  const ok = window.confirm("Delete this card permanently?");
  if (!ok) return;
  deleteCardsByIds([id]);
  await persistCardsEverywhere();
  persistUI();
  render();
  showToast("Card deleted");
}

function deleteCardsByIds(ids = []) {
  const idSet = new Set(ids);
  state.cards = reindexCards(state.cards.filter(card => !idSet.has(card.id)));
  ids.forEach(id => {
    state.dismissedIds.delete(id);
    state.flippedIds.delete(id);
    state.selectedCardIds.delete(id);
  });
  if (state.selectedId && idSet.has(state.selectedId)) {
    state.selectedId = null;
    state.route = "root";
  }
}

function toggleCardSelection(id, forcedValue = null) {
  if (!state.cardsSelectionMode) return;
  const nextValue = forcedValue == null ? !state.selectedCardIds.has(id) : Boolean(forcedValue);
  if (nextValue) state.selectedCardIds.add(id);
  else state.selectedCardIds.delete(id);
}

function selectAllCards() {
  state.cardsSelectionMode = true;
  state.selectedCardIds = new Set(getFilteredCards(sortCardsByPosition(state.cards)).map(card => card.id));
}

async function deleteSelectedCards() {
  if (!state.selectedCardIds.size) {
    showToast("Select cards first");
    return;
  }
  const ok = window.confirm(`Delete ${state.selectedCardIds.size} selected card${state.selectedCardIds.size > 1 ? "s" : ""}?`);
  if (!ok) return;
  deleteCardsByIds([...state.selectedCardIds]);
  clearCardSelection();
  await persistCardsEverywhere();
  persistUI();
  render();
  showToast("Selected cards deleted");
}

async function saveCloudConfig() { return; }

function disableCloud() { return; }

function resetForm() {
  state.formLabels = [];
  const labelInput = document.getElementById("labelInput");
  const frontEditor = document.getElementById("frontEditor");
  const backEditor = document.getElementById("backEditor");
  const container = document.getElementById("formLabels");
  if (labelInput) labelInput.value = "";
  if (frontEditor) frontEditor.innerHTML = "";
  if (backEditor) backEditor.innerHTML = "";
  if (container) container.innerHTML = "";
  if (frontEditor) frontEditor.focus();
}


async function signInWithGoogle() {
  try {
    ensureFirebase();
    await configureAuthPersistence();
    const provider = new GoogleAuthProvider();
    provider.setCustomParameters({ prompt: "select_account" });
    setLoadingVisible(true, "Opening Google sign-in…");

    try {
      await signInWithPopup(firebaseAuth, provider);
      sessionStorage.removeItem(AUTH_REDIRECT_FLAG);
      setLoadingVisible(false);
      return;
    } catch (popupError) {
      const popupFallbackCodes = new Set([
        "auth/popup-blocked",
        "auth/cancelled-popup-request",
        "auth/popup-closed-by-user",
        "auth/operation-not-supported-in-this-environment"
      ]);
      if (!popupFallbackCodes.has(popupError?.code) && !isMobileDevice()) {
        throw popupError;
      }
      sessionStorage.setItem(AUTH_REDIRECT_FLAG, "1");
      setLoadingVisible(true, "Redirecting to Google…");
      await signInWithRedirect(firebaseAuth, provider);
      return;
    }
  } catch (error) {
    console.error(error);
    sessionStorage.removeItem(AUTH_REDIRECT_FLAG);
    setLoadingVisible(false);
    showToast("Google sign-in failed");
  }
}

async function signOutUser() {
  if (!firebaseAuth) return;
  try {
    await signOut(firebaseAuth);
    clearCardSelection();
    state.route = "root";
    state.selectedId = null;
    state.dismissedIds.clear();
    state.flippedIds.clear();
    showToast("Signed out");
  } catch (error) {
    console.error(error);
    showToast("Sign-out failed");
  }
}

function cloudStatusText() {
  if (!state.cloud.enabled || !hasCloudConfig()) return "Local only";
  if (cloudSyncing) return "Syncing…";
  return cloudReady ? "Cloud connected" : "Connecting…";
}

function labelToneClass(label = "") {
  const text = label.trim().toLowerCase();
  let hash = 0;
  for (let i = 0; i < text.length; i += 1) hash = (hash * 31 + text.charCodeAt(i)) % 10;
  return `tone-${Math.abs(hash % 10)}`;
}

function renderLabel(label, previewMode = false) {
  if (!label) return "";
  const escaped = escapeHtml(label);
  return previewMode
    ? `<span class="label-stamp label-preview ${labelToneClass(label)}"><span>${escaped}</span><button class="label-remove" type="button" data-action="remove-form-label" data-label="${escaped}">×</button></span>`
    : `<span class="label-stamp ${labelToneClass(label)}">${escaped}</span>`;
}

function renderLabels(labels = [], previewMode = false) {
  return labels.map(label => renderLabel(label, previewMode)).join("");
}

function statusClass(status) {
  return status.toLowerCase().replace(/\s+/g, "-");
}

function formatEditor(command, editorId, value = null) {
  const editor = document.getElementById(editorId);
  if (!editor) return;
  editor.focus();
  document.execCommand(command, false, value);
}

function extractImportCards(parsed) {
  if (Array.isArray(parsed)) return parsed;
  if (Array.isArray(parsed.cards)) return parsed.cards;
  if (Array.isArray(parsed.flashcards)) return parsed.flashcards;
  if (Array.isArray(parsed.data)) return parsed.data;
  if (Array.isArray(parsed.items)) return parsed.items;
  if (Array.isArray(parsed.deck)) return parsed.deck;
  if (typeof parsed === "object" && parsed && (
    getFirstString(parsed, ["front", "question", "prompt", "term", "title", "frontMarkdown", "frontHtml"]) ||
    getFirstString(parsed, ["back", "answer", "response", "definition", "content", "backMarkdown", "backHtml"])
  )) {
    return [parsed];
  }
  return [];
}

function normalizeImportItem(raw = {}, index = 0) {
  const frontSource = getFirstString(raw, ["frontMarkdown", "frontMd", "frontHtml", "frontRich", "frontText", "front", "question", "prompt", "term", "title"]);
  const backSource = getFirstString(raw, ["backMarkdown", "backMd", "backHtml", "backRich", "backText", "back", "answer", "response", "definition", "content"]);
  const labelsSource = raw.labels ?? raw.tags ?? raw.label ?? raw.category ?? raw.categories ?? raw.deck ?? "";
  const status = STATUS_VALUES.includes(raw.status) ? raw.status : "Learning";
  return {
    importId: `import-${index}-${cryptoSafeId()}`,
    selected: true,
    frontSource: normalizeTextSource(frontSource),
    backSource: normalizeTextSource(backSource),
    labelsText: labelsTextFromRaw(labelsSource),
    status
  };
}

function parseImportItemsFromText(rawText) {
  const parsed = safeParse(rawText);
  if (!parsed) throw new Error("Import failed: check JSON format");
  const items = extractImportCards(parsed).map((item, index) => normalizeImportItem(item, index));
  if (!items.length) throw new Error("No cards found in this JSON");
  return items;
}

function syncImportItemsFromDom() {
  if (state.route !== "import" || !state.importDraft.items.length) return;
  state.importDraft.items = state.importDraft.items.map(item => {
    const frontSource = document.getElementById(`import-front-${item.importId}`)?.value ?? item.frontSource;
    const backSource = document.getElementById(`import-back-${item.importId}`)?.value ?? item.backSource;
    const labelsText = document.getElementById(`import-labels-${item.importId}`)?.value ?? item.labelsText;
    const status = document.getElementById(`import-status-${item.importId}`)?.value ?? item.status;
    const selected = document.getElementById(`import-select-${item.importId}`)?.checked ?? item.selected;
    return {
      ...item,
      frontSource: normalizeTextSource(frontSource),
      backSource: normalizeTextSource(backSource),
      labelsText: normalizeTextSource(labelsText),
      status: STATUS_VALUES.includes(status) ? status : "Learning",
      selected: Boolean(selected)
    };
  });
}

function parseImportFromTextarea() {
  const textarea = document.getElementById("importJsonInput");
  const rawText = textarea?.value || state.importDraft.rawText || "";
  if (!rawText.trim()) {
    showToast("Paste JSON first");
    return;
  }
  try {
    const items = parseImportItemsFromText(rawText);
    state.importDraft = {
      rawText,
      sourceName: state.importDraft.sourceName,
      items
    };
    render();
    showToast(`${items.length} card${items.length > 1 ? "s" : ""} ready to import`);
  } catch (error) {
    console.error(error);
    showToast(error.message || "Import failed");
  }
}

async function handleImportFileChosen(input) {
  const file = input?.files?.[0];
  if (!file) return;
  const text = await file.text();
  state.importDraft.rawText = text;
  state.importDraft.sourceName = file.name;
  try {
    const items = parseImportItemsFromText(text);
    state.importDraft.items = items;
    render();
    showToast(`${items.length} card${items.length > 1 ? "s" : ""} loaded from file`);
  } catch (error) {
    console.error(error);
    render();
    showToast(error.message || "Import failed");
  } finally {
    input.value = "";
  }
}

function toggleImportSelection(importId, forcedValue = null) {
  syncImportItemsFromDom();
  state.importDraft.items = state.importDraft.items.map(item => {
    if (item.importId !== importId) return item;
    const nextValue = forcedValue == null ? !item.selected : Boolean(forcedValue);
    return { ...item, selected: nextValue };
  });
}

function selectAllImportItems(selected) {
  syncImportItemsFromDom();
  state.importDraft.items = state.importDraft.items.map(item => ({ ...item, selected: Boolean(selected) }));
}

async function importSelectedCards() {
  syncImportItemsFromDom();
  const chosen = state.importDraft.items.filter(item => item.selected);
  if (!chosen.length) {
    showToast("Select at least one card");
    return;
  }

  const now = new Date().toISOString();
  let nextPosition = state.cards.length ? Math.max(...state.cards.map(c => Number(c.position) || 0)) : 0;
  const importedCards = chosen
    .map(item => {
      const front = sourceTextToHtml(item.frontSource, detectLikelyHtml(item.frontSource) ? "html" : "markdown");
      const back = sourceTextToHtml(item.backSource, detectLikelyHtml(item.backSource) ? "html" : "markdown");
      if (!stripHtml(front).trim() || !stripHtml(back).trim()) return null;
      nextPosition += 1;
      return normalizeCard({
        id: cryptoSafeId(),
        front,
        back,
        frontFormat: "html",
        backFormat: "html",
        labels: parseLabels(item.labelsText),
        status: item.status,
        position: nextPosition,
        createdAt: now,
        updatedAt: now
      }, nextPosition - 1);
    })
    .filter(Boolean);

  if (!importedCards.length) {
    showToast("Nothing valid to import");
    return;
  }

  state.cards.push(...importedCards);
  await persistCardsEverywhere();
  resetImportDraft();
  state.route = "root";
  state.tab = "cards";
  render();
  showToast(`${importedCards.length} card${importedCards.length > 1 ? "s" : ""} imported`);
}

function updateHeader() {
  topbarActions.innerHTML = "";

  if (!authReady) {
    eyebrowEl.textContent = "Connecting";
    titleEl.textContent = "Card Garden";
  } else if (!state.user) {
    eyebrowEl.textContent = "Private study library";
    titleEl.textContent = "Sign in";
  } else if (state.route === "detail") {
    eyebrowEl.textContent = "Review and update";
    titleEl.textContent = "Card details";
  } else if (state.route === "edit") {
    eyebrowEl.textContent = "Create and manage";
    titleEl.textContent = "Edit card";
    topbarActions.innerHTML = `<button class="plus-button" data-action="reset-form" aria-label="Clear form">+</button>`;
  } else if (state.route === "import") {
    eyebrowEl.textContent = "Paste or load JSON";
    titleEl.textContent = "Import cards";
  } else if (state.tab === "home") {
    eyebrowEl.textContent = "A calm study space";
    titleEl.textContent = "Learn";
  } else if (state.tab === "cards" && state.route === "create") {
    eyebrowEl.textContent = "Create and manage";
    titleEl.textContent = "Create a card";
    topbarActions.innerHTML = `<button class="plus-button" data-action="reset-form" aria-label="Clear form">+</button>`;
  } else if (state.tab === "cards") {
    eyebrowEl.textContent = "Create and manage";
    titleEl.textContent = "Cards";
    topbarActions.innerHTML = `
      <button class="header-action-btn" data-action="open-import">Import</button>
      ${state.cards.length ? `<button class="header-action-btn" data-action="toggle-card-selection-mode">${state.cardsSelectionMode ? "Done" : "Select"}</button>` : ""}
      ${state.cards.length ? `<button class="header-action-btn" data-action="open-filter-modal">Filter</button>` : ""}
      <button class="plus-button" data-action="open-create" aria-label="Create a card">+</button>
    `;
  } else {
    eyebrowEl.textContent = "Your card health";
    titleEl.textContent = "Stats";
  }

  if (authReady && state.user && state.tab === "metrics" && state.route === "root") {
    topbarActions.insertAdjacentHTML("beforeend", `<button class="header-action-btn" data-action="sign-out">Sign out</button>`);
  }

  backButton.hidden = state.route === "root" || !state.user;
  navItems.forEach(item => item.classList.toggle("active", item.dataset.tab === state.tab));
}

function render() {
  updateHeader();
  if (!authReady) return renderAuthLoading();
  if (!state.user) return renderAuthScreen();
  if (state.route === "detail" && state.selectedId && !state.cards.some(card => card.id === state.selectedId)) {
    state.route = "root";
    state.selectedId = null;
  }
  if (state.tab === "home") return renderHome();
  if (state.tab === "cards" && state.route === "import") return renderImport();
  if (state.tab === "cards" && (state.route === "create" || state.route === "edit")) return renderCardForm(state.route);
  if (state.route === "detail") return renderDetail();
  if (state.tab === "cards") return renderCards();
  return renderMetrics();
}

function renderAuthLoading() {
  appEl.innerHTML = `
    <section class="panel empty-panel fade-in">
      <div class="empty-box">
        <h2>Loading your library…</h2>
        <div class="muted">Checking your sign-in state.</div>
      </div>
    </section>
  `;
}

function renderAuthScreen() {
  appEl.innerHTML = `
    <section class="panel empty-panel fade-in auth-panel">
      <div class="empty-box">
        <h2>Your cards, private to you</h2>
        <div class="muted">Sign in with Google to create, import, and sync your own flashcards across devices.</div>
        <div class="empty-actions">
          <button class="primary-button" data-action="sign-in-google">Continue with Google</button>
        </div>
      </div>
    </section>
  `;
}

function renderHome() {
  const activeCards = sortCardsByPosition(state.cards)
    .filter(card => card.status === "Learning")
    .filter(card => !state.dismissedIds.has(card.id))
    .slice(0, 3);

  if (!activeCards.length) {
    appEl.innerHTML = `
      <section class="panel empty-panel fade-in">
        <div class="empty-box">
          <h2>All done!</h2>
          <div class="empty-actions">
            <button class="secondary-button" data-action="restart-home">Start learning</button>
          </div>
        </div>
      </section>
    `;
    return;
  }

  appEl.innerHTML = `
    <section class="panel stack-wrap fade-in">
      <div class="stack-area">
        ${activeCards.map(card => `
          <div class="home-card-shell" data-id="${card.id}">
            <button class="home-dismiss" type="button" data-action="dismiss-home-card" data-id="${card.id}" aria-label="Dismiss this card">×</button>
            <div class="home-card" role="button" tabindex="0" data-action="home-card-tap" data-id="${card.id}">
              <article class="card-face front home-face stamp-face" data-stamp-tone="learn-front" data-stamp-perf="12" data-stamp-padding="24">
                <div class="stamp-shell"></div>
                <div class="stamp-content stamp-content-home">
                  <div class="face-text rich-content">${card.front}</div>
                  <div class="home-labels-row">${renderLabels(card.labels)}</div>
                </div>
              </article>
              <article class="card-face back home-face stamp-face" data-stamp-tone="learn-back" data-stamp-perf="12" data-stamp-padding="24">
                <div class="stamp-shell"></div>
                <div class="stamp-content stamp-content-home">
                  <div class="face-text rich-content">${card.back}</div>
                  <div class="home-labels-row">${renderLabels(card.labels)}</div>
                </div>
              </article>
            </div>
          </div>
        `).join("")}
      </div>
    </section>
  `;
  syncHomeCardState();
  applyStampFaces();
}


function getUniqueFilterLabels() {
  return [...new Set(state.cards.flatMap(card => Array.isArray(card.labels) ? card.labels : []))]
    .filter(Boolean)
    .sort((a, b) => a.localeCompare(b));
}

function hasActiveCardFilters() {
  return state.cardFilters.statuses.length > 0 || state.cardFilters.labels.length > 0;
}

function getFilteredCards(cards = sortCardsByPosition(state.cards)) {
  const statuses = state.cardFilters.statuses;
  const labels = state.cardFilters.labels;
  return cards.filter(card => {
    const statusMatch = !statuses.length || statuses.includes(card.status);
    const cardLabels = Array.isArray(card.labels) ? card.labels : [];
    const labelMatch = !labels.length || labels.some(label => cardLabels.includes(label));
    return statusMatch && labelMatch;
  });
}

function renderFilterSummary(filteredCount, totalCount) {
  if (!hasActiveCardFilters()) return "";
  const parts = [];
  if (state.cardFilters.statuses.length) parts.push(`Status(${state.cardFilters.statuses.length})`);
  if (state.cardFilters.labels.length) parts.push(`Labels(${state.cardFilters.labels.length})`);
  return `
    <div class="filter-summary-row">
      <div class="filter-summary-text">Filtered by: ${parts.join(" • ")}</div>
      <button class="text-button" data-action="clear-card-filters">Clear filters</button>
    </div>
    <div class="filter-count-note">${filteredCount} shown • ${totalCount} total</div>
  `;
}

function renderFilterModal() {
  if (!state.filterModalOpen) return "";
  const labels = getUniqueFilterLabels();
  return `
    <div class="filter-modal-backdrop" data-action="close-filter-modal">
      <div class="filter-modal-card" data-action="noop-filter-modal">
        <div class="filter-modal-head">
          <h2 class="panel-title">Filter cards</h2>
          <button class="icon-button" data-action="close-filter-modal" aria-label="Close filter">×</button>
        </div>

        <form id="cardFilterForm" class="filter-form">
          <div class="filter-section">
            <div class="field-label">Status</div>
            <div class="filter-chip-group">
              ${STATUS_VALUES.map(status => `
                <label class="filter-chip-option">
                  <input type="checkbox" name="filter-status" value="${escapeHtml(status)}" ${state.cardFilters.statuses.includes(status) ? "checked" : ""} />
                  <span class="filter-chip">${escapeHtml(status)}</span>
                </label>
              `).join("")}
            </div>
          </div>

          <div class="filter-section">
            <div class="field-label">Labels</div>
            <details class="filter-dropdown">
              <summary class="filter-dropdown-summary">
                <span id="filterLabelsSummary">${state.cardFilters.labels.length ? `${state.cardFilters.labels.length} label${state.cardFilters.labels.length > 1 ? "s" : ""} selected` : "Select labels"}</span>
              </summary>
              <div class="filter-dropdown-menu">
                ${labels.length ? labels.map(label => `
                  <label class="filter-check-option">
                    <input type="checkbox" name="filter-label" value="${escapeHtml(label)}" ${state.cardFilters.labels.includes(label) ? "checked" : ""} />
                    <span>${escapeHtml(label)}</span>
                  </label>
                `).join("") : `<div class="filter-empty-note">No labels available</div>`}
              </div>
            </details>
          </div>

          <div class="filter-rule-note">Within the same field: OR • Across fields: AND</div>

          <div class="filter-actions">
            <button type="button" class="secondary-button slim-button" data-action="clear-filter-form">Clear all</button>
            <button type="submit" class="secondary-button slim-button primary-button">Apply filters</button>
          </div>
        </form>
      </div>
    </div>
  `;
}


function syncFilterDraftUi() {
  const summaryEl = document.getElementById("filterLabelsSummary");
  const form = document.getElementById("cardFilterForm");
  if (!summaryEl || !form) return;
  const checkedLabels = form.querySelectorAll('input[name="filter-label"]:checked').length;
  summaryEl.textContent = checkedLabels ? `${checkedLabels} label${checkedLabels > 1 ? "s" : ""} selected` : "Select labels";
}

function applyCardFiltersFromForm() {
  const form = document.getElementById("cardFilterForm");
  if (!form) return;
  const statusValues = [...form.querySelectorAll('input[name="filter-status"]:checked')].map(input => input.value);
  const labelValues = [...form.querySelectorAll('input[name="filter-label"]:checked')].map(input => input.value);
  state.cardFilters = { statuses: statusValues, labels: labelValues };
  state.filterModalOpen = false;
  render();
}


function renderCardsToolbar(cards, totalCount = cards.length) {
  const countLabel = hasActiveCardFilters()
    ? `${cards.length} card${cards.length !== 1 ? "s" : ""}`
    : `${cards.length} card${cards.length !== 1 ? "s" : ""}`;

  if (!state.cardsSelectionMode) {
    return `
      <div class="cards-toolbar cards-toolbar-summary-only">
        <div class="muted">${countLabel}</div>
      </div>
      ${renderFilterSummary(cards.length, totalCount)}
    `;
  }

  return `
    <div class="cards-toolbar is-selection">
      <div class="muted">${state.selectedCardIds.size} selected</div>
      <div class="cards-toolbar-actions">
        <button class="secondary-button slim-button" data-action="select-all-cards">Select all</button>
        <button class="secondary-button slim-button" data-action="deselect-all-cards">Deselect all</button>
        <button class="secondary-button slim-button danger-button" data-action="delete-selected-cards">Delete selected</button>
      </div>
    </div>
    ${renderFilterSummary(cards.length, totalCount)}
  `;
}

function renderCards() {
  const allCards = sortCardsByPosition(state.cards);
  const cards = getFilteredCards(allCards);

  if (!allCards.length) {
    appEl.innerHTML = `
      <section class="panel empty-panel fade-in">
        <div class="empty-box">
          <h2>Let’s create a new card</h2>
          <div class="muted">Use Import above or create one manually.</div>
          <div class="empty-actions">
            <button class="center-plus" data-action="open-create" aria-label="Create a card">+</button>
          </div>
        </div>
      </section>
    `;
    return;
  }

  if (!cards.length) {
    appEl.innerHTML = `
      <section class="panel fade-in">
        ${renderCardsToolbar(cards, allCards.length)}
        <div class="empty-filter-state">
          <h2>No cards match this filter</h2>
          <div class="muted">Try a different combination of status and labels.</div>
          <div class="empty-actions">
            <button class="secondary-button" data-action="clear-card-filters">Clear filters</button>
          </div>
        </div>
      </section>
      ${renderFilterModal()}
    `;
    return;
  }

  appEl.innerHTML = `
    <section class="panel fade-in">
      ${renderCardsToolbar(cards, allCards.length)}
      ${cards.map((card, index) => `
        <div class="list-card ${state.cardsSelectionMode ? "is-select-mode" : ""}">
          <div class="list-card-head">
            ${state.cardsSelectionMode ? `
              <label class="list-check-wrap" aria-label="Select this card">
                <input
                  class="list-check"
                  type="checkbox"
                  id="card-select-${card.id}"
                  data-action="toggle-card-selection"
                  data-id="${card.id}"
                  ${state.selectedCardIds.has(card.id) ? "checked" : ""}
                />
                <span></span>
              </label>
            ` : ""}
            <button class="list-card-main" data-action="${state.cardsSelectionMode ? "toggle-card-selection-row" : "open-detail"}" data-id="${card.id}">
              <div class="row">
                <div class="list-title">${escapeHtml(preview(firstLine(card.front), 72))}</div>
              </div>
              <div class="list-preview">${escapeHtml(preview(card.front, 170))}</div>
              <div class="label-row">${renderLabels(card.labels)}</div>
              <div class="list-status-row"><span class="status-chip ${statusClass(card.status)}">${card.status}</span></div>
            </button>
            ${state.cardsSelectionMode ? "" : `
              <div class="list-card-actions">
                <button class="icon-ghost" data-action="move-up" data-id="${card.id}" aria-label="Move up" ${index === 0 ? "disabled" : ""}>↑</button>
                <button class="icon-ghost" data-action="move-down" data-id="${card.id}" aria-label="Move down" ${index === cards.length - 1 ? "disabled" : ""}>↓</button>
              </div>
            `}
          </div>
        </div>
      `).join("")}
    </section>
    ${renderFilterModal()}
  `;
}

function renderCardForm(mode) {
  const isEdit = mode === "edit";
  const card = isEdit ? state.cards.find(item => item.id === state.selectedId) : null;
  if (isEdit && !card) {
    state.route = "root";
    state.selectedId = null;
    return render();
  }
  const frontContent = isEdit ? card.front : "";
  const backContent = isEdit ? card.back : "";
  if (isEdit && (!state.formLabels || !state.formLabels.length) && card.labels.length) {
    state.formLabels = [...card.labels];
  }
  appEl.innerHTML = `
    <section class="panel form-panel fade-in">
      <form id="cardForm" novalidate>
        <div class="field labels-field">
          <label class="field-label" for="labelInput">Labels</label>
          <input id="labelInput" class="label-input" type="text" placeholder="Type a label and press Enter" maxlength="60" />
          <div class="form-labels" id="formLabels">${renderLabels(state.formLabels, true)}</div>
        </div>

        <div class="field front-field">
          <label class="field-label">Front</label>
          <div class="editor-shell front-shell">
            <div class="toolbar">
              <button class="tool-btn" type="button" onclick="window.formatEditor('bold','frontEditor')"><strong>B</strong></button>
              <button class="tool-btn" type="button" onclick="window.formatEditor('italic','frontEditor')"><em>I</em></button>
              <button class="tool-btn" type="button" onclick="window.formatEditor('insertUnorderedList','frontEditor')">•</button>
              <button class="tool-btn" type="button" onclick="window.formatEditor('insertOrderedList','frontEditor')">1.</button>
              <select class="toolbar-select" onchange="window.formatEditor('fontName','frontEditor',this.value)">
                <option value="Inter">Inter</option>
                <option value="Cormorant Garamond">Cormorant</option>
              </select>
              <select class="toolbar-select" onchange="window.formatEditor('fontSize','frontEditor',this.value)">
                <option value="3">Text</option>
                <option value="4">Large</option>
                <option value="5">XL</option>
              </select>
            </div>
            <div id="frontEditor" class="editor rich-content" contenteditable="true" data-placeholder="Type or paste the front side. Basic formatting is supported.">${frontContent}</div>
          </div>
        </div>

        <div class="field back-field">
          <label class="field-label">Back</label>
          <div class="editor-shell back-shell">
            <div class="toolbar">
              <button class="tool-btn" type="button" onclick="window.formatEditor('bold','backEditor')"><strong>B</strong></button>
              <button class="tool-btn" type="button" onclick="window.formatEditor('italic','backEditor')"><em>I</em></button>
              <button class="tool-btn" type="button" onclick="window.formatEditor('insertUnorderedList','backEditor')">•</button>
              <button class="tool-btn" type="button" onclick="window.formatEditor('insertOrderedList','backEditor')">1.</button>
              <select class="toolbar-select" onchange="window.formatEditor('fontName','backEditor',this.value)">
                <option value="Inter">Inter</option>
                <option value="Cormorant Garamond">Cormorant</option>
              </select>
              <select class="toolbar-select" onchange="window.formatEditor('fontSize','backEditor',this.value)">
                <option value="3">Text</option>
                <option value="4">Large</option>
                <option value="5">XL</option>
              </select>
            </div>
            <div id="backEditor" class="editor rich-content" contenteditable="true" data-placeholder="Type or paste the back side. Basic formatting is supported.">${backContent}</div>
          </div>
        </div>

        <div class="save-row">
          <button class="primary-button" type="submit">Save</button>
        </div>
      </form>
    </section>
  `;
}

function renderImportItem(item, index) {
  const frontPreview = sourceTextToHtml(item.frontSource, detectLikelyHtml(item.frontSource) ? "html" : "markdown");
  const backPreview = sourceTextToHtml(item.backSource, detectLikelyHtml(item.backSource) ? "html" : "markdown");
  const summaryTitle = escapeHtml(preview(frontPreview || "Untitled", 90) || `Imported card ${index + 1}`);

  return `
    <details class="import-card" ${index < 2 ? "open" : ""}>
      <summary class="import-card-summary">
        <div class="import-summary-left">
          <label class="list-check-wrap import-check-wrap" aria-label="Select this import card">
            <input
              class="list-check"
              type="checkbox"
              id="import-select-${item.importId}"
              data-action="toggle-import-select"
              data-id="${item.importId}"
              ${item.selected ? "checked" : ""}
            />
            <span></span>
          </label>
          <div>
            <div class="import-card-title">${summaryTitle}</div>
            <div class="muted">Card ${index + 1}</div>
          </div>
        </div>
        <span class="status-chip ${statusClass(item.status)}">${item.status}</span>
      </summary>

      <div class="import-card-body">
        <div class="import-field-row">
          <div class="field">
            <label class="field-label" for="import-status-${item.importId}">Status</label>
            <select class="import-select" id="import-status-${item.importId}">
              ${STATUS_VALUES.map(status => `<option value="${status}" ${status === item.status ? "selected" : ""}>${status}</option>`).join("")}
            </select>
          </div>
          <div class="field">
            <label class="field-label" for="import-labels-${item.importId}">Labels</label>
            <input class="label-input" id="import-labels-${item.importId}" value="${escapeHtml(item.labelsText)}" placeholder="Comma separated labels" />
          </div>
        </div>

        <div class="import-grid">
          <div class="field">
            <label class="field-label" for="import-front-${item.importId}">Front source</label>
            <textarea class="import-textarea" id="import-front-${item.importId}" placeholder="Markdown or HTML supported">${escapeHtml(item.frontSource)}</textarea>
          </div>
          <div class="field">
            <label class="field-label" for="import-back-${item.importId}">Back source</label>
            <textarea class="import-textarea" id="import-back-${item.importId}" placeholder="Markdown or HTML supported">${escapeHtml(item.backSource)}</textarea>
          </div>
        </div>

        <div class="import-grid preview-grid">
          <div class="import-preview-card">
            <div class="field-label">Front preview</div>
            <div class="import-preview rich-content">${frontPreview}</div>
          </div>
          <div class="import-preview-card">
            <div class="field-label">Back preview</div>
            <div class="import-preview rich-content">${backPreview}</div>
          </div>
        </div>
      </div>
    </details>
  `;
}

function renderImport() {
  const selectedCount = state.importDraft.items.filter(item => item.selected).length;
  appEl.innerHTML = `
    <section class="panel import-panel fade-in">
      <div class="field">
        <label class="field-label" for="importJsonInput">Paste JSON</label>
        <textarea class="import-json-input" id="importJsonInput" placeholder='Paste an array of cards or an object with a "cards" array'>${escapeHtml(state.importDraft.rawText)}</textarea>
        <div class="cards-toolbar-actions">
          <button class="secondary-button slim-button" data-action="parse-import-json">Preview import</button>
          <button class="secondary-button slim-button" data-action="choose-import-file">Choose file</button>
          <button class="secondary-button slim-button" data-action="clear-import-draft">Clear</button>
        </div>
        <input id="importFileInput" type="file" accept="application/json,.json,text/json" hidden />
        <div class="note-text">Markdown and HTML are both supported on import. Lists and bullets are preserved.</div>
      </div>

      ${state.importDraft.items.length ? `
        <div class="import-toolbar">
          <div>
            <div class="panel-title">${state.importDraft.items.length} detected</div>
            <div class="muted">${selectedCount} selected${state.importDraft.sourceName ? ` • ${escapeHtml(state.importDraft.sourceName)}` : ""}</div>
          </div>
          <div class="cards-toolbar-actions">
            <button class="secondary-button slim-button" data-action="select-all-import">Select all</button>
            <button class="secondary-button slim-button" data-action="deselect-all-import">Deselect all</button>
            <button class="primary-button slim-button" data-action="import-selected-cards">Import selected</button>
          </div>
        </div>

        <div class="import-list">
          ${state.importDraft.items.map((item, index) => renderImportItem(item, index)).join("")}
        </div>
      ` : `
        <div class="import-empty muted">Paste JSON or choose a file, then preview before importing.</div>
      `}
    </section>
  `;
}

function renderMetrics() {
  const learning = state.cards.filter(card => card.status === "Learning").length;
  const learnt = state.cards.filter(card => card.status === "Learnt").length;
  const toLearn = state.cards.filter(card => card.status === "To learn").length;
  appEl.innerHTML = `
    <section class="panel fade-in">
      <div class="metrics-grid">
        <div class="metric-card total">
          <div class="muted">Total cards</div>
          <div class="metric-value">${state.cards.length}</div>
        </div>
        <div class="metric-card">
          <div class="muted">Learning</div>
          <div class="metric-value">${learning}</div>
        </div>
        <div class="metric-card">
          <div class="muted">To learn</div>
          <div class="metric-value">${toLearn}</div>
        </div>
        <div class="metric-card">
          <div class="muted">Learnt</div>
          <div class="metric-value">${learnt}</div>
        </div>
        <div class="metric-card">
          <div class="muted">Signed in as</div>
          <div class="metric-value metric-user">${escapeHtml(state.user?.displayName || state.user?.email || "Google user")}</div>
        </div>
      </div>
      <div class="version-note">Card Garden v51<br>@capyshibara</div>
      <div class="metrics-actions">
        <button class="secondary-button" data-action="export-json">Export JSON</button>
      </div>
    </section>
  `;
}

function renderDetail() {
  const card = state.cards.find(item => item.id === state.selectedId);
  if (!card) {
    state.route = "root";
    state.selectedId = null;
    return render();
  }
  appEl.innerHTML = `
    <section class="panel detail-panel fade-in">
      <div class="detail-card-frame">
        <div class="detail-card" id="detailFlipCard" data-action="flip-detail-card" aria-label="Flip card">
          <article class="card-face front stamp-face" data-stamp-tone="detail-front" data-stamp-perf="12" data-stamp-padding="26">
            <div class="stamp-shell"></div>
            <div class="stamp-content stamp-content-detail">
              <div class="face-text rich-content">${card.front}</div>
              <div class="face-labels">${renderLabels(card.labels)}</div>
            </div>
          </article>
          <article class="card-face back stamp-face" data-stamp-tone="detail-back" data-stamp-perf="12" data-stamp-padding="26">
            <div class="stamp-shell"></div>
            <div class="stamp-content stamp-content-detail">
              <div class="face-text rich-content">${card.back}</div>
              <div class="face-labels">${renderLabels(card.labels)}</div>
            </div>
          </article>
        </div>
      </div>

      <div class="detail-toolbar">
        <div class="detail-toolbar-left">
          ${STATUS_VALUES.map(status => `<button class="status-pill ${statusClass(status)} ${status === card.status ? "is-active" : ""}" data-action="set-status" data-id="${card.id}" data-status="${status}">${status}</button>`).join("")}
        </div>
        <div class="detail-toolbar-right">
          <button class="icon-ghost" data-action="open-edit" data-id="${card.id}" aria-label="Edit">✎</button>
          <button class="icon-ghost" data-action="delete-card" data-id="${card.id}" aria-label="Delete permanently">✕</button>
        </div>
      </div>
    </section>
  `;
  applyStampFaces();
}

function createStampSVG({ width, height, perf, outerFill, innerFill, padding }) {
  const r = perf / 2;
  const innerInset = Math.max(padding - 10, perf + 6);
  const bodyX = r;
  const bodyY = r;
  const bodyW = width - r * 2;
  const bodyH = height - r * 2;
  const rx = Math.max(16, perf * 1.0);

  const ns = "http://www.w3.org/2000/svg";
  const svg = document.createElementNS(ns, "svg");
  svg.setAttribute("viewBox", `0 0 ${width} ${height}`);
  svg.setAttribute("width", "100%");
  svg.setAttribute("height", "100%");
  svg.setAttribute("preserveAspectRatio", "none");

  const shell = document.createElementNS(ns, "g");
  shell.setAttribute("fill", outerFill);
  shell.setAttribute("stroke", "none");

  const rect = document.createElementNS(ns, "rect");
  rect.setAttribute("x", bodyX);
  rect.setAttribute("y", bodyY);
  rect.setAttribute("width", bodyW);
  rect.setAttribute("height", bodyH);
  rect.setAttribute("rx", rx);
  rect.setAttribute("ry", rx);
  shell.appendChild(rect);

  const positions = [];
  for (let x = r; x <= width - r + 0.1; x += perf) {
    positions.push({ x, y: r });
    positions.push({ x, y: height - r });
  }
  for (let y = r + perf; y <= height - r - perf + 0.1; y += perf) {
    positions.push({ x: r, y });
    positions.push({ x: width - r, y });
  }

  positions.forEach(({ x, y }) => {
    const c = document.createElementNS(ns, "circle");
    c.setAttribute("cx", x);
    c.setAttribute("cy", y);
    c.setAttribute("r", r);
    shell.appendChild(c);
  });

  const inner = document.createElementNS(ns, "rect");
  inner.setAttribute("x", innerInset);
  inner.setAttribute("y", innerInset);
  inner.setAttribute("width", Math.max(10, width - innerInset * 2));
  inner.setAttribute("height", Math.max(10, height - innerInset * 2));
  inner.setAttribute("rx", Math.max(14, rx - 6));
  inner.setAttribute("ry", Math.max(14, rx - 6));
  inner.setAttribute("fill", innerFill);
  inner.setAttribute("stroke", "none");

  svg.appendChild(shell);
  svg.appendChild(inner);
  return { svg, innerInset };
}

function stampToneColors(tone) {
  const map = {
    "learn-front": { outer: "#FAFAF7", inner: "#F0F0EB" },
    "learn-back": { outer: "#FAFAF7", inner: "#F0F0EB" },
    "detail-front": { outer: "#FAFAF7", inner: "#F0F0EB" },
    "detail-back": { outer: "#FAFAF7", inner: "#F0F0EB" }
  };
  return map[tone] || map["learn-front"];
}

function renderStampFace(face) {
  const shellSlot = face.querySelector(".stamp-shell");
  const content = face.querySelector(".stamp-content");
  if (!shellSlot || !content) return;

  const perf = Number(face.dataset.stampPerf || 12);
  const padding = Number(face.dataset.stampPadding || 28);
  const width = Math.max(280, Math.round(face.clientWidth));
  const height = Math.max(280, Math.round(face.clientHeight));
  const colors = stampToneColors(face.dataset.stampTone);

  const { svg, innerInset } = createStampSVG({
    width,
    height,
    perf,
    outerFill: colors.outer,
    innerFill: colors.inner,
    padding
  });

  shellSlot.innerHTML = "";
  shellSlot.appendChild(svg);
  content.style.padding = `${innerInset + 16}px`;
}

function applyStampFaces() {
  const faces = appEl.querySelectorAll(".stamp-face");
  faces.forEach(renderStampFace);

  if (!stampFaceObserver) {
    stampFaceObserver = new ResizeObserver((entries) => {
      entries.forEach((entry) => {
        if (entry.target.classList.contains("stamp-face")) renderStampFace(entry.target);
      });
    });
  }

  faces.forEach((face) => stampFaceObserver.observe(face));
}


function setLoadingVisible(visible, message = "Signing you in…") {
  const overlay = document.getElementById("loadingOverlay");
  const text = document.getElementById("loadingText");
  if (text) text.textContent = message;
  if (overlay) overlay.hidden = !visible;
}

function showToast(text) {
  toastEl.textContent = text;
  toastEl.classList.add("show");
  clearTimeout(showToast.timer);
  showToast.timer = setTimeout(() => toastEl.classList.remove("show"), 1800);
}

window.formatEditor = formatEditor;

async function initAuth() {
  ensureFirebase();
  await configureAuthPersistence();

  if (sessionStorage.getItem(AUTH_REDIRECT_FLAG)) {
    setLoadingVisible(true, "Signing you in…");
  }

  try {
    await getRedirectResult(firebaseAuth);
  } catch (error) {
    console.error(error);
  }

  onAuthStateChanged(firebaseAuth, async (user) => {
    state.user = user;
    authReady = true;
    state.route = "root";
    state.selectedId = null;
    clearCardSelection();

    if (user) {
      sessionStorage.removeItem(AUTH_REDIRECT_FLAG);
      setLoadingVisible(true, "Loading your cards…");
      await startCloud(user);
      setLoadingVisible(false);
    } else {
      await stopCloud();
      state.cards = loadCards();
      if (!sessionStorage.getItem(AUTH_REDIRECT_FLAG)) {
        setLoadingVisible(false);
      }
    }
    render();
  });

  render();
}

initAuth();

function openAIModal(){ document.getElementById("aiModal").classList.add("show"); }
function closeAIModal(){ document.getElementById("aiModal").classList.remove("show"); }

async function generateAI(){
  const topic=document.getElementById("aiTopic").value;
  const difficulty=document.getElementById("aiDifficulty").value;
  const count=document.getElementById("aiCount").value;

  const res=await fetch("YOUR_FUNCTION_URL",{
    method:"POST",
    headers:{"Content-Type":"application/json"},
    body:JSON.stringify({topic,difficulty,count})
  });

  const cards=await res.json();

  if(window.openImportPreview){
    openImportPreview(cards);
  } else {
    alert("Generated but preview hook not found");
  }

  closeAIModal();
}

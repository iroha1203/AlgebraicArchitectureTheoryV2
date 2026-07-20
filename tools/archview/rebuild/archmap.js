const ARCHMAP_SCHEMA = "archmap/v0.5.4";
const ATOM_KINDS = new Set([
  "component", "relation", "capability", "state", "effect",
  "authority", "contract", "semantic", "runtime",
]);
const CANONICAL_DOCTRINE = Object.freeze({
  doctrineId: "doctrine:aat-canonical@1",
  fingerprint: "sha256:aat-canonical-doctrine-schema052",
  components: Object.freeze(["V", "Gamma", "R", "rho", "E", "N"]),
});
const DIAGNOSTIC_TOKENS = new Set(["mismatch", "obstruction", "obstructive", "violation", "violate", "violated", "violates", "violating", "risk", "risky", "debt", "unsafe", "lawful", "nonzero", "failure", "fail", "failed", "failing"]);

export class ArchMapValidationError extends Error {
  constructor(issues) {
    super(issues.map((issue) => issue.message).join(" "));
    this.name = "ArchMapValidationError";
    this.issues = Object.freeze(issues.map((issue) => Object.freeze({ ...issue })));
  }
}

function isRecord(value) {
  return value !== null && typeof value === "object" && !Array.isArray(value);
}

function issue(path, message, value = null) {
  return { path, message, value };
}

function rejectUnknownFields(value, allowed, path, issues) {
  for (const key of Object.keys(value)) {
    if (!allowed.has(key)) issues.push(issue(`${path}.${key}`, `Unknown field ${path}.${key}.`));
  }
}

function requireString(value, path, issues) {
  if (typeof value !== "string" || value.trim() === "") {
    issues.push(issue(path, `${path} must be a non-empty string.`, value));
    return false;
  }
  return true;
}

function optionalString(value, path, issues) {
  if (value !== undefined && typeof value !== "string") issues.push(issue(path, `${path} must be a string.`, value));
}

function stringArray(value, path, issues) {
  if (value === undefined) return [];
  if (!Array.isArray(value)) {
    issues.push(issue(path, `${path} must be an array.`, value));
    return [];
  }
  const result = [];
  value.forEach((entry, index) => {
    if (typeof entry !== "string" || entry.trim() === "") issues.push(issue(`${path}[${index}]`, `${path}[${index}] must be a non-empty string.`, entry));
    else result.push(entry);
  });
  return result;
}

function uniqueIds(rows, path, issues) {
  const seen = new Set();
  for (const row of rows) {
    if (typeof row?.id !== "string" || row.id.trim() === "") continue;
    if (seen.has(row.id)) issues.push(issue(`${path}[].id`, `${path} id ${row.id} must be unique.`, row.id));
    seen.add(row.id);
  }
}

function hasDiagnosticShortcut(value) {
  if (typeof value !== "string") return false;
  const parts = value.replace(/([a-z0-9])([A-Z])/g, "$1 $2").toLowerCase().split(/[^a-z0-9]+/).filter(Boolean);
  return parts.some((part) => DIAGNOSTIC_TOKENS.has(part)) || parts.some((part, index) => part === "non" && parts[index + 1] === "zero");
}

function validateDoctrine(value, issues) {
  if (value === undefined) return;
  if (!isRecord(value)) {
    issues.push(issue("extractionDoctrineRef", "extractionDoctrineRef must be an object.", value));
    return;
  }
  rejectUnknownFields(value, new Set(["doctrineId", "fingerprint", "components"]), "extractionDoctrineRef", issues);
  if (value.doctrineId !== CANONICAL_DOCTRINE.doctrineId) issues.push(issue("extractionDoctrineRef.doctrineId", "ArchMap must use the fixed AAT canonical doctrine.", value.doctrineId));
  if (value.fingerprint !== CANONICAL_DOCTRINE.fingerprint) issues.push(issue("extractionDoctrineRef.fingerprint", "ArchMap must use the fixed canonical doctrine fingerprint.", value.fingerprint));
  if (!Array.isArray(value.components) || value.components.join("\u0000") !== CANONICAL_DOCTRINE.components.join("\u0000")) {
    issues.push(issue("extractionDoctrineRef.components", "ArchMap must use the fixed canonical doctrine components in order.", value.components));
  }
}

function validateSource(source, path, issues) {
  if (!isRecord(source)) {
    issues.push(issue(path, `${path} must be an object.`, source));
    return;
  }
  rejectUnknownFields(source, new Set(["kind", "path", "source", "symbol", "line", "section", "traceId"]), path, issues);
  requireString(source.kind, `${path}.kind`, issues);
  for (const field of ["path", "source", "symbol", "section", "traceId"]) optionalString(source[field], `${path}.${field}`, issues);
  if (source.line !== undefined && (!Number.isInteger(source.line) || source.line < 0)) {
    issues.push(issue(`${path}.line`, `${path}.line must be a non-negative integer.`, source.line));
  }
}

function validateAtom(atom, index, issues) {
  const path = `atoms[${index}]`;
  if (!isRecord(atom)) {
    issues.push(issue(path, `${path} must be an object.`, atom));
    return;
  }
  rejectUnknownFields(atom, new Set(["id", "kind", "subject", "axis", "predicate", "object", "refs", "label"]), path, issues);
  requireString(atom.id, `${path}.id`, issues);
  if (requireString(atom.kind, `${path}.kind`, issues) && !ATOM_KINDS.has(atom.kind)) {
    issues.push(issue(`${path}.kind`, `${path}.kind is not in the declared AAT Atom vocabulary.`, atom.kind));
  }
  requireString(atom.subject, `${path}.subject`, issues);
  requireString(atom.axis, `${path}.axis`, issues);
  optionalString(atom.predicate, `${path}.predicate`, issues);
  optionalString(atom.object, `${path}.object`, issues);
  optionalString(atom.label, `${path}.label`, issues);
  stringArray(atom.refs, `${path}.refs`, issues);
  if (hasDiagnosticShortcut(atom.id) || hasDiagnosticShortcut(atom.predicate)) {
    issues.push(issue(path, `${path} must not pre-author an ArchSig diagnostic conclusion.`));
  }
}

function validateContext(context, index, issues) {
  const path = `contexts[${index}]`;
  if (!isRecord(context)) {
    issues.push(issue(path, `${path} must be an object.`, context));
    return;
  }
  rejectUnknownFields(context, new Set(["id", "atoms", "restrictsTo", "refs", "label"]), path, issues);
  requireString(context.id, `${path}.id`, issues);
  stringArray(context.atoms, `${path}.atoms`, issues);
  stringArray(context.restrictsTo, `${path}.restrictsTo`, issues);
  stringArray(context.refs, `${path}.refs`, issues);
  optionalString(context.label, `${path}.label`, issues);
}

function validateCover(cover, index, issues) {
  const path = `covers[${index}]`;
  if (!isRecord(cover)) {
    issues.push(issue(path, `${path} must be an object.`, cover));
    return;
  }
  rejectUnknownFields(cover, new Set(["id", "contexts", "refs", "label"]), path, issues);
  requireString(cover.id, `${path}.id`, issues);
  stringArray(cover.contexts, `${path}.contexts`, issues);
  stringArray(cover.refs, `${path}.refs`, issues);
  optionalString(cover.label, `${path}.label`, issues);
}

function sorted(values, key = (value) => value.id) {
  return [...values].sort((left, right) => key(left).localeCompare(key(right)));
}

export function buildArchMapIndex(document) {
  const errors = [];
  if (!isRecord(document)) throw new ArchMapValidationError([issue("$", "ArchMap root must be an object.", document)]);
  rejectUnknownFields(document, new Set(["schema", "id", "extractionDoctrineRef", "sources", "atoms", "contexts", "covers"]), "$", errors);
  if (document.schema !== ARCHMAP_SCHEMA) errors.push(issue("schema", `schema must be ${ARCHMAP_SCHEMA}.`, document.schema));
  requireString(document.id, "id", errors);
  validateDoctrine(document.extractionDoctrineRef, errors);

  const sources = document.sources === undefined ? {} : document.sources;
  const atoms = document.atoms === undefined ? [] : document.atoms;
  const contexts = document.contexts === undefined ? [] : document.contexts;
  const covers = document.covers === undefined ? [] : document.covers;
  if (!isRecord(sources)) errors.push(issue("sources", "sources must be an object keyed by source id.", sources));
  if (!Array.isArray(atoms)) errors.push(issue("atoms", "atoms must be an array.", atoms));
  if (!Array.isArray(contexts)) errors.push(issue("contexts", "contexts must be an array.", contexts));
  if (!Array.isArray(covers)) errors.push(issue("covers", "covers must be an array.", covers));

  if (isRecord(sources)) Object.entries(sources).forEach(([id, source]) => validateSource(source, `sources.${id}`, errors));
  if (Array.isArray(atoms)) atoms.forEach((atom, index) => validateAtom(atom, index, errors));
  if (Array.isArray(contexts)) contexts.forEach((context, index) => validateContext(context, index, errors));
  if (Array.isArray(covers)) covers.forEach((cover, index) => validateCover(cover, index, errors));
  if (Array.isArray(atoms)) uniqueIds(atoms, "atoms", errors);
  if (Array.isArray(contexts)) uniqueIds(contexts, "contexts", errors);
  if (Array.isArray(covers)) uniqueIds(covers, "covers", errors);
  if (Array.isArray(contexts) && contexts.length) {
    for (const context of contexts) {
      if (isRecord(context) && Array.isArray(context.atoms) && context.atoms.length === 0) errors.push(issue(`contexts.${context.id}.atoms`, "Context must observe an explicit Atom subfamily."));
    }
    const graph = new Map(contexts.filter(isRecord).map((context) => [context.id, context.restrictsTo || []]));
    const reachesCycle = (start, current, path = new Set()) => {
      if (path.has(current)) return current === start;
      const nextPath = new Set(path).add(current);
      return (graph.get(current) || []).some((target) => target === start || reachesCycle(start, target, nextPath));
    };
    for (const contextId of graph.keys()) {
      if (reachesCycle(contextId, contextId)) errors.push(issue(`contexts.${contextId}.restrictsTo`, "Context restriction relation must be acyclic."));
    }
  }
  if (Array.isArray(covers)) {
    for (const cover of covers) {
      if (isRecord(cover) && Array.isArray(cover.contexts) && cover.contexts.length === 0) errors.push(issue(`covers.${cover.id}.contexts`, "Cover must select a finite Context family."));
    }
  }
  if (errors.length) throw new ArchMapValidationError(errors);

  const sourcesById = new Map(Object.entries(sources));
  const atomsById = new Map(atoms.map((atom) => [atom.id, atom]));
  const contextsById = new Map(contexts.map((context) => [context.id, context]));
  const coversById = new Map(covers.map((cover) => [cover.id, cover]));
  const unresolved = [];
  const recordMissing = (path, ref, target) => unresolved.push(issue(path, `${ref} does not resolve to ${target}.`, ref));

  for (const [sourceId, source] of sourcesById) {
    if (source.source && !sourcesById.has(source.source)) recordMissing(`sources.${sourceId}.source`, source.source, "sources");
  }
  for (const atom of atoms) {
    for (const ref of atom.refs || []) if (!sourcesById.has(ref)) recordMissing(`atoms.${atom.id}.refs`, ref, "sources");
  }
  for (const context of contexts) {
    for (const ref of context.atoms || []) if (!atomsById.has(ref)) recordMissing(`contexts.${context.id}.atoms`, ref, "atoms");
    for (const ref of context.restrictsTo || []) if (!contextsById.has(ref)) recordMissing(`contexts.${context.id}.restrictsTo`, ref, "contexts");
    for (const ref of context.refs || []) if (!sourcesById.has(ref)) recordMissing(`contexts.${context.id}.refs`, ref, "sources");
  }
  for (const cover of covers) {
    for (const ref of cover.contexts || []) if (!contextsById.has(ref)) recordMissing(`covers.${cover.id}.contexts`, ref, "contexts");
    for (const ref of cover.refs || []) if (!sourcesById.has(ref)) recordMissing(`covers.${cover.id}.refs`, ref, "sources");
  }

  const contextIdsByAtom = new Map();
  for (const context of contexts) {
    for (const atomId of context.atoms || []) {
      if (!atomsById.has(atomId)) continue;
      const memberships = contextIdsByAtom.get(atomId) || [];
      memberships.push(context.id);
      contextIdsByAtom.set(atomId, memberships);
    }
  }

  const counts = Object.freeze({ sources: sourcesById.size, atoms: atomsById.size, contexts: contextsById.size, covers: coversById.size });
  return Object.freeze({
    schema: document.schema,
    id: document.id,
    counts,
    empty: counts.sources === 0 && counts.atoms === 0 && counts.contexts === 0 && counts.covers === 0,
    sources: Object.freeze(sorted([...sourcesById], ([id]) => id)),
    atoms: Object.freeze(sorted(atoms)),
    contexts: Object.freeze(sorted(contexts)),
    covers: Object.freeze(sorted(covers)),
    sourcesById,
    atomsById,
    contextsById,
    coversById,
    contextIdsByAtom,
    unresolved: Object.freeze(unresolved.map((entry) => Object.freeze(entry))),
  });
}

export function parseArchMap(text) {
  let document;
  try {
    document = JSON.parse(text);
  } catch (error) {
    throw new ArchMapValidationError([issue("$", `ArchMap is not valid JSON: ${error.message}`)]);
  }
  return buildArchMapIndex(document);
}

export async function loadArchMapFromUrl(url) {
  const response = await fetch(url, { headers: { Accept: "application/json" } });
  if (!response.ok) throw new Error(`ArchMap request failed with HTTP ${response.status}.`);
  return parseArchMap(await response.text());
}

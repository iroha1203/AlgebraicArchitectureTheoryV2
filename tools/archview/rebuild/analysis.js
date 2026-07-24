const FILES = Object.freeze({
  manifest: "archsig-run-manifest.json",
  normalized: "normalized-archmap.json",
  packet: "archsig-measurement-packet.json",
  summary: "archsig-analysis-summary.json",
  insight: "archsig-insight-report.json",
  comparison: "archsig-comparison-report.json",
  gate: "archsig-gate-report.json",
});

const SCHEMAS = Object.freeze({
  manifest: "archsig-run-manifest/v0.5.4",
  normalized: "normalized-archmap/v0.5.4",
  packet: "archsig-measurement-packet/v0.5.4",
  summary: "archsig-analysis-summary/v0.5.4",
  insight: "archsig-insight-report/v0.5.4",
  comparison: "archsig-comparison-report/v0.5.4",
  gate: "archsig-gate-report/v0.5.4",
});

const REQUIRED = Object.freeze(["manifest", "normalized", "packet", "summary", "insight"]);
const COMPARISON_DISCIPLINE = "Comparison is a record-level juxtaposition of two ArchSig runs. It does not claim causal repair, semantic equivalence, or preserved obstruction identity; a class-zero reading is available only under a checked coarse-to-fine refinement contract.";
const COMPARISON_CONCLUSIONS = new Set(["NO_NEW_MEASURED_OBSTRUCTION_RECORDED", "MEASURED_OBSTRUCTION_RECORDED_AFTER_CHANGE", "MEASURED_OBSTRUCTION_NO_LONGER_RECORDED_AFTER_CHANGE", "RUNS_NOT_COMPARABLE_WITHOUT_COMPARISON_DATA"]);
const COMPARISON_TRANSITIONS = new Set(["new_recorded_row", "removed_recorded_row", "measured_obstruction_no_longer_recorded", "measured_obstruction_recorded_after_change", "preexisting_recorded_row", "other_transition"]);
const RAW_CANONICAL = new WeakMap();

export class AnalysisValidationError extends Error {
  constructor(status, issues) {
    super(issues.map((entry) => entry.message).join(" "));
    this.name = "AnalysisValidationError";
    this.status = status;
    this.issues = Object.freeze(issues.map((entry) => Object.freeze({ ...entry })));
  }
}

function isRecord(value) {
  return value !== null && typeof value === "object" && !Array.isArray(value);
}

function issue(path, message, expected = null, received = null) {
  return { path, message, expected, received };
}

function requireRecord(value, path, issues) {
  if (!isRecord(value)) issues.push(issue(path, `${path} must be an object.`));
  return isRecord(value);
}

function requireString(value, path, issues) {
  if (typeof value !== "string" || value.length === 0) issues.push(issue(path, `${path} must be a non-empty string.`));
  return typeof value === "string" && value.length > 0;
}

function requireArray(value, path, issues) {
  if (!Array.isArray(value)) issues.push(issue(path, `${path} must be an array.`));
  return Array.isArray(value);
}

function requireStringArray(value, path, issues) {
  if (!requireArray(value, path, issues)) return;
  value.forEach((entry, position) => requireString(entry, `${path}[${position}]`, issues));
}

function requireObjectArray(value, path, requiredStrings, issues) {
  if (!requireArray(value, path, issues)) return;
  value.forEach((entry, position) => {
    const rowPath = `${path}[${position}]`;
    if (!requireRecord(entry, rowPath, issues)) return;
    requiredStrings.forEach((field) => requireString(entry[field], `${rowPath}.${field}`, issues));
  });
}

function validateArtifactRows(packet, summary, insight, issues) {
  requireObjectArray(packet.structuralVerdict, `${FILES.packet}.structuralVerdict`, ["verdictRef", "evaluator", "law", "verdict"], issues);
  (packet.structuralVerdict || []).forEach((row, position) => {
    const path = `${FILES.packet}.structuralVerdict[${position}]`;
    if (!isRecord(row)) return;
    if (!new Set(["measured_zero", "measured_nonzero", "unmeasured", "unknown", "not_computed"]).has(row.verdict)) issues.push(issue(`${path}.verdict`, `${path}.verdict is not an ArchSig structural verdict.`, null, row.verdict));
    if (requireRecord(row.target, `${path}.target`, issues)) {
      for (const field of ["kind", "coverRef", "coefficient", "classRef"]) requireString(row.target[field], `${path}.target.${field}`, issues);
      requireRecord(row.target.scopeSize, `${path}.target.scopeSize`, issues);
    }
    if (requireRecord(row.verdictData, `${path}.verdictData`, issues)) {
      for (const field of ["inScope", "zero", "nonZero"]) if (typeof row.verdictData[field] !== "boolean") issues.push(issue(`${path}.verdictData.${field}`, `${path}.verdictData.${field} must be boolean.`));
      requireString(row.verdictData.methodStatus, `${path}.verdictData.methodStatus`, issues);
      const expectedFlags = {
        measured_zero: { inScope: true, zero: true, nonZero: false },
        measured_nonzero: { inScope: true, zero: false, nonZero: true },
        unmeasured: { zero: false, nonZero: false },
        unknown: { zero: false, nonZero: false },
        not_computed: { zero: false, nonZero: false },
      }[row.verdict];
      for (const [field, expected] of Object.entries(expectedFlags || {})) if (row.verdictData[field] !== expected) issues.push(issue(`${path}.verdictData.${field}`, `${path}.verdictData.${field} contradicts verdict ${row.verdict}.`, expected, row.verdictData[field]));
    }
    if (requireRecord(row.evidence, `${path}.evidence`, issues)) for (const field of ["computedInvariantRefs", "sourceRefs"]) requireStringArray(row.evidence[field], `${path}.evidence.${field}`, issues);
  });
  requireObjectArray(packet.computedInvariants, `${FILES.packet}.computedInvariants`, ["invariantId", "kind"], issues);
  requireObjectArray(packet.analyticReadings, `${FILES.packet}.analyticReadings`, ["readingId", "evaluator", "claimStatus", "fidelity"], issues);
  requireObjectArray(packet.assumptions, `${FILES.packet}.assumptions`, ["assumptionId", "theoremRef", "assumption", "status"], issues);
  requireObjectArray(packet.suppliedData, `${FILES.packet}.suppliedData`, ["suppliedId", "kind", "sourceArtifactRef"], issues);
  requireObjectArray(packet.boundaryStatements, `${FILES.packet}.boundaryStatements`, ["id", "kind", "reason", "text"], issues);
  requireObjectArray(insight.insightCards, `${FILES.insight}.insightCards`, ["id", "kind", "title", "oneLine"], issues);
  (insight.insightCards || []).forEach((row, position) => {
    if (!isRecord(row) || !requireRecord(row.evidence, `${FILES.insight}.insightCards[${position}].evidence`, issues)) return;
    for (const field of ["structuralVerdictRefs", "computedInvariantRefs", "analyticReadingRefs", "assumptionRefs", "sourceRefs", "atomRefs", "contextRefs", "coverRefs", "evaluatorRefs"]) requireStringArray(row.evidence[field], `${FILES.insight}.insightCards[${position}].evidence.${field}`, issues);
  });
  requireObjectArray(insight.actionQueue, `${FILES.insight}.actionQueue`, ["id", "kind", "title", "reason"], issues);
  const uniqueField = (rows, field, path) => {
    const seen = new Set();
    (rows || []).forEach((row, position) => {
      const value = row?.[field];
      if (typeof value !== "string") return;
      if (seen.has(value)) issues.push(issue(`${path}[${position}].${field}`, `${path}.${field} values must be unique.`, null, value));
      seen.add(value);
    });
    return seen;
  };
  const verdictRefs = uniqueField(packet.structuralVerdict, "verdictRef", `${FILES.packet}.structuralVerdict`);
  const invariantRefs = uniqueField(packet.computedInvariants, "invariantId", `${FILES.packet}.computedInvariants`);
  const readingRefs = uniqueField(packet.analyticReadings, "readingId", `${FILES.packet}.analyticReadings`);
  const assumptionRefs = uniqueField(packet.assumptions, "assumptionId", `${FILES.packet}.assumptions`);
  (packet.assumptions || []).forEach((row) => { if (typeof row?.theoremRef === "string") assumptionRefs.add(row.theoremRef); });
  uniqueField(packet.suppliedData, "suppliedId", `${FILES.packet}.suppliedData`);
  uniqueField(packet.boundaryStatements, "id", `${FILES.packet}.boundaryStatements`);
  uniqueField(insight.insightCards, "id", `${FILES.insight}.insightCards`);
  uniqueField(insight.actionQueue, "id", `${FILES.insight}.actionQueue`);
  const evaluatorRefs = new Set([...(packet.structuralVerdict || []), ...(packet.computedInvariants || []), ...(packet.analyticReadings || [])].map((row) => row?.evaluator).filter((value) => typeof value === "string"));
  const requireExistingRefs = (refs, known, path, label) => (refs || []).forEach((ref, position) => {
    if (!known.has(ref)) issues.push(issue(`${path}[${position}]`, `${ref} does not identify a ${label} in the loaded measurement packet.`, null, ref));
  });
  (packet.structuralVerdict || []).forEach((row, position) => requireExistingRefs(row?.evidence?.computedInvariantRefs, invariantRefs, `${FILES.packet}.structuralVerdict[${position}].evidence.computedInvariantRefs`, "computed invariant"));
  (insight.insightCards || []).forEach((row, position) => {
    const evidence = row?.evidence;
    if (!isRecord(evidence)) return;
    const path = `${FILES.insight}.insightCards[${position}].evidence`;
    requireExistingRefs(evidence.structuralVerdictRefs, verdictRefs, `${path}.structuralVerdictRefs`, "structural verdict");
    requireExistingRefs(evidence.computedInvariantRefs, invariantRefs, `${path}.computedInvariantRefs`, "computed invariant");
    requireExistingRefs(evidence.analyticReadingRefs, readingRefs, `${path}.analyticReadingRefs`, "analytic reading");
    requireExistingRefs(evidence.assumptionRefs, assumptionRefs, `${path}.assumptionRefs`, "valid assumption or theorem reference");
    requireExistingRefs(evidence.evaluatorRefs, evaluatorRefs, `${path}.evaluatorRefs`, "measurement evaluator");
  });
  const verdicts = packet.structuralVerdict || [];
  const expectedCounts = {
    rowCount: verdicts.length,
    measuredNonzeroCount: verdicts.filter((row) => row?.verdict === "measured_nonzero").length,
    unmeasuredCount: verdicts.filter((row) => row?.verdict === "unmeasured").length,
    nonTerminalCount: verdicts.filter((row) => ["unmeasured", "unknown", "not_computed"].includes(row?.verdict)).length,
  };
  for (const [field, expected] of Object.entries(expectedCounts)) if (summary.structuralVerdictSummary?.[field] !== expected) issues.push(issue(`${FILES.summary}.structuralVerdictSummary.${field}`, `Summary ${field} does not match the measurement packet.`, expected, summary.structuralVerdictSummary?.[field]));
  const assumptionCounts = {
    checkedCount: packet.assumptions.filter((row) => row?.status === "checked").length,
    assumedCount: packet.assumptions.filter((row) => row?.status === "assumed").length,
    violatedCount: packet.assumptions.filter((row) => row?.status === "violated").length,
  };
  for (const [field, expected] of Object.entries(assumptionCounts)) if (summary.assumptionSummary?.[field] !== expected) issues.push(issue(`${FILES.summary}.assumptionSummary.${field}`, `Summary ${field} does not match the assumption ledger.`, expected, summary.assumptionSummary?.[field]));
}

function validateReferenceShapes(value, path, issues) {
  if (Array.isArray(value)) return value.forEach((entry, position) => validateReferenceShapes(entry, `${path}[${position}]`, issues));
  if (!isRecord(value)) return;
  if (typeof value.edgeId === "string" && Object.hasOwn(value, "sectionObservation")) {
    if (!["observed", "not_observed"].includes(value.sectionObservation)) issues.push(issue(`${path}.sectionObservation`, `${path}.sectionObservation is not an ArchSig observation state.`, null, value.sectionObservation));
    if (value.sectionObservation === "observed" && ![0, 1, "0", "1"].includes(value.value)) issues.push(issue(`${path}.value`, `${path}.value must be 0 or 1 for an observed F2 relation.`, "0 or 1", value.value));
  }
  for (const [key, child] of Object.entries(value)) {
    const childPath = `${path}.${key}`;
    if (REF_FIELDS[key] || key === "targetRefs" || key === "edgeRefs" || key === "unobservedEdgeRefs") {
      requireStringArray(child, childPath, issues);
      continue;
    }
    if (SINGLE_REF_FIELDS[key] && child !== null && child !== undefined && typeof child !== "string") {
      issues.push(issue(childPath, `${childPath} must be a string when present.`));
      continue;
    }
    validateReferenceShapes(child, childPath, issues);
  }
}

function deriveConclusion(packet) {
  const verdicts = packet.structuralVerdict;
  const has = (evaluator, verdict, law = null) => verdicts.some((row) => row.evaluator === evaluator && row.verdict === verdict && (law === null || row.law === law));
  if (has("ag.saga-descent", "measured_nonzero", "saga.residual-class")) return "MEASURED_NONGLUING_RESIDUAL_CLASS";
  if (has("ag.saga-descent", "measured_nonzero", "saga.residual-boundary-membership")) return "MEASURED_NONGLUING_RESIDUAL";
  if (has("ag.saga-descent", "measured_zero", "saga.global-coherence")) return "REPAIR_GLUES_WITHIN_SELECTED_COMPLEX";
  if (packet.computedInvariants.some((row) => row.evaluator === "ag.cech-obstruction" && row.theorem12_4Discharge?.coverShapeExcludesGluingObstruction === true)) return "COVER_SHAPE_EXCLUDES_GLUING_OBSTRUCTION";
  if (has("ag.cech-obstruction", "measured_nonzero")) return "MEASURED_H1_OBSTRUCTION_UNDER_PROFILE";
  if (has("ag.square-free-repair", "measured_nonzero") && packet.computedInvariants.some((row) => row.evaluator === "ag.square-free-repair" && row.alexanderDualRepair?.minimalHittingSets?.length > 0)) return "REPAIR_TARGETS_IDENTIFIED";
  if (verdicts.some((row) => row.verdict === "measured_nonzero")) return "MEASURED_AG_OBSTRUCTION_UNDER_PROFILE";
  if (has("ag.cech-obstruction", "measured_zero")) return "NO_MEASURED_H1_OBSTRUCTION_UNDER_PROFILE";
  return "AG_MEASUREMENT_FOUNDATION_READY_UNDER_PROFILE";
}

function requireDigestEntry(value, path, issues) {
  if (!requireRecord(value, path, issues)) return;
  requireString(value.path, `${path}.path`, issues);
  if (typeof value.sha256 !== "string" || !/^[0-9a-f]{64}$/.test(value.sha256)) issues.push(issue(`${path}.sha256`, `${path}.sha256 must be a lowercase SHA-256 digest.`));
}

function validateInputDigests(value, path, issues) {
  if (!requireRecord(value, path, issues)) return;
  for (const key of ["archmap", "lawPolicy", "lawSurface", "measurementProfile"]) requireDigestEntry(value[key], `${path}.${key}`, issues);
  if (requireArray(value.measurementProfiles, `${path}.measurementProfiles`, issues)) {
    if (!value.measurementProfiles.length) issues.push(issue(`${path}.measurementProfiles`, "At least one MeasurementProfile digest is required."));
    value.measurementProfiles.forEach((entry, position) => requireDigestEntry(entry, `${path}.measurementProfiles[${position}]`, issues));
  }
  for (const key of ["profileFingerprint", "siteCoverDigest"]) {
    if (!requireRecord(value[key], `${path}.${key}`, issues) || typeof value[key].sha256 !== "string" || !/^[0-9a-f]{64}$/.test(value[key].sha256)) issues.push(issue(`${path}.${key}.sha256`, `${path}.${key}.sha256 must be a lowercase SHA-256 digest.`));
  }
}

function validateMeasurementProfile(profile, path, issues) {
  if (!requireRecord(profile, path, issues)) return;
  if (profile.schema !== "measurement-profile/v0.5.4") issues.push(issue(`${path}.schema`, "Measurement packet profile must use measurement-profile/v0.5.4.", "measurement-profile/v0.5.4", profile.schema));
  for (const field of ["profileId", "siteRef", "coverRef", "coefficient", "effCoeff", "resolutionSelector", "domain", "zeroPredicate", "nonZeroPredicate", "certSelector", "verdictDiscipline"]) requireString(profile[field], `${path}.${field}`, issues);
  if (requireRecord(profile.finiteBounds, `${path}.finiteBounds`, issues)) {
    for (const field of ["maxSquareFreeWitnessVariables", "maxCoherenceContexts", "maxTorWitnessVariables", "maxBoundaryResidueVariables", "maxLaplacianCells", "maxPeriodCycles", "maxTransferTargets"]) {
      if (!Number.isInteger(profile.finiteBounds[field]) || profile.finiteBounds[field] < 0) issues.push(issue(`${path}.finiteBounds.${field}`, `${path}.finiteBounds.${field} must be a non-negative integer.`));
    }
  }
}

export function canonicalJson(value) {
  if (isRecord(value) || Array.isArray(value)) {
    const rawCanonical = RAW_CANONICAL.get(value);
    if (rawCanonical !== undefined) return rawCanonical;
  }
  if (Array.isArray(value)) return `[${value.map(canonicalJson).join(",")}]`;
  if (isRecord(value)) {
    return `{${Object.keys(value).sort().map((key) => `${JSON.stringify(key)}:${canonicalJson(value[key])}`).join(",")}}`;
  }
  return JSON.stringify(value);
}

function deepFreeze(value) {
  if (!isRecord(value) && !Array.isArray(value)) return value;
  Object.values(value).forEach(deepFreeze);
  return Object.freeze(value);
}

function readonlyMap(map) {
  return Object.freeze(new Proxy(map, {
    get(target, property) {
      if (["set", "delete", "clear"].includes(property)) return () => { throw new TypeError("Accepted analysis identity bridges are read-only."); };
      const value = Reflect.get(target, property, target);
      return typeof value === "function" ? value.bind(target) : value;
    },
  }));
}

function cloneDocuments(documents) {
  const clone = structuredClone(documents);
  for (const name of Object.keys(FILES)) {
    const canonical = documents?.[name] && RAW_CANONICAL.get(documents[name]);
    if (canonical !== undefined && clone[name]) RAW_CANONICAL.set(clone[name], canonical);
  }
  return clone;
}

export async function sha256Hex(value) {
  const bytes = new TextEncoder().encode(typeof value === "string" ? value : canonicalJson(value));
  const digest = await crypto.subtle.digest("SHA-256", bytes);
  return [...new Uint8Array(digest)].map((byte) => byte.toString(16).padStart(2, "0")).join("");
}

function validateRoot(name, document, issues) {
  if (!requireRecord(document, FILES[name], issues)) return;
  if (document.schema !== SCHEMAS[name]) {
    issues.push(issue(`${FILES[name]}.schema`, `${FILES[name]} must use ${SCHEMAS[name]}.`, SCHEMAS[name], document.schema));
  }
}

function validateCoreShape(documents, issues) {
  const { manifest, normalized, packet, summary, insight } = documents;
  for (const name of REQUIRED) validateRoot(name, documents[name], issues);
  if (issues.length) return;

  requireString(manifest.runId, `${FILES.manifest}.runId`, issues);
  requireString(manifest.toolVersion, `${FILES.manifest}.toolVersion`, issues);
  validateInputDigests(manifest.inputDigests, `${FILES.manifest}.inputDigests`, issues);
  requireRecord(manifest.componentFingerprints, `${FILES.manifest}.componentFingerprints`, issues);
  requireRecord(manifest.artifactLinks, `${FILES.manifest}.artifactLinks`, issues);
  requireArray(manifest.generatedArtifacts, `${FILES.manifest}.generatedArtifacts`, issues);
  requireRecord(manifest.validationResultSummary, `${FILES.manifest}.validationResultSummary`, issues);
  for (const field of ["archmapInputPath", "lawPolicyInputPath", "lawSurfaceInputPath", "measurementProfileInputPath", "rawArtifactRetention"]) requireString(manifest[field], `${FILES.manifest}.${field}`, issues);
  requireArray(manifest.measurementProfileInputPaths, `${FILES.manifest}.measurementProfileInputPaths`, issues);
  requireArray(manifest.omittedArtifacts, `${FILES.manifest}.omittedArtifacts`, issues);
  requireRecord(manifest.validationReports, `${FILES.manifest}.validationReports`, issues);
  requireArray(manifest.nonConclusions, `${FILES.manifest}.nonConclusions`, issues);
  if (manifest.commandName !== "analyze" || manifest.mode !== "measurement") {
    issues.push(issue(FILES.manifest, "The run manifest must describe a completed analyze measurement run.", "analyze / measurement", `${manifest.commandName} / ${manifest.mode}`));
  }
  if (manifest.validationResultSummary?.analysis?.result !== "pass") {
    issues.push(issue(`${FILES.manifest}.validationResultSummary.analysis.result`, "The analysis validation result must be pass.", "pass", manifest.validationResultSummary?.analysis?.result));
  }
  for (const [link, filename] of [["measurementPacket", FILES.packet], ["summary", FILES.summary], ["insightReport", FILES.insight]]) {
    if (manifest.artifactLinks?.[link] !== filename) issues.push(issue(`${FILES.manifest}.artifactLinks.${link}`, `Manifest ${link} must resolve to ${filename}.`, filename, manifest.artifactLinks?.[link]));
  }
  for (const name of ["normalized", "packet", "summary", "insight", "manifest"]) {
    if (!manifest.generatedArtifacts.includes(FILES[name])) issues.push(issue(`${FILES.manifest}.generatedArtifacts`, `${FILES[name]} must be declared by the run manifest.`, FILES[name], null));
  }

  requireArray(normalized.atoms, `${FILES.normalized}.atoms`, issues);
  requireArray(normalized.contexts, `${FILES.normalized}.contexts`, issues);
  requireArray(normalized.covers, `${FILES.normalized}.covers`, issues);
  if (Array.isArray(normalized.atoms) && Array.isArray(normalized.contexts) && Array.isArray(normalized.covers)) validateNormalizedRows(normalized, issues);
  requireString(normalized.sourceArchmapId, `${FILES.normalized}.sourceArchmapId`, issues);
  requireString(packet.packetId, `${FILES.packet}.packetId`, issues);
  validateMeasurementProfile(packet.profile, `${FILES.packet}.profile`, issues);
  requireArray(packet.structuralVerdict, `${FILES.packet}.structuralVerdict`, issues);
  requireArray(packet.computedInvariants, `${FILES.packet}.computedInvariants`, issues);
  for (const field of ["analyticReadings", "assumptions", "suppliedData", "boundaryStatements", "nonConclusions"]) requireArray(packet[field], `${FILES.packet}.${field}`, issues);
  requireString(summary.profileRef, `${FILES.summary}.profileRef`, issues);
  requireRecord(summary.structuralVerdictSummary, `${FILES.summary}.structuralVerdictSummary`, issues);
  requireString(summary.conclusion, `${FILES.summary}.conclusion`, issues);
  requireArray(summary.nonConclusions, `${FILES.summary}.nonConclusions`, issues);
  if (summary.measurementPacketSchema !== SCHEMAS.packet) issues.push(issue(`${FILES.summary}.measurementPacketSchema`, `Summary must reference ${SCHEMAS.packet}.`, SCHEMAS.packet, summary.measurementPacketSchema));
  for (const field of ["assumptionSummary", "insightArtifacts", "readThisFirst", "translationRule", "componentFingerprints"]) requireRecord(summary[field], `${FILES.summary}.${field}`, issues);
  requireArray(summary.translationRuleTable, `${FILES.summary}.translationRuleTable`, issues);
  requireString(insight.reportId, `${FILES.insight}.reportId`, issues);
  if (insight.sourcePacketRef !== FILES.packet) issues.push(issue(`${FILES.insight}.sourcePacketRef`, `Insight report must reference ${FILES.packet}.`, FILES.packet, insight.sourcePacketRef));
  requireArray(insight.insightCards, `${FILES.insight}.insightCards`, issues);
  requireArray(insight.actionQueue, `${FILES.insight}.actionQueue`, issues);
  requireArray(insight.nonConclusions, `${FILES.insight}.nonConclusions`, issues);
  requireString(insight.generatedAt, `${FILES.insight}.generatedAt`, issues);
  for (const field of ["boundaryDigest", "claimValidation", "componentFingerprints", "copyBlocks", "gluingGeometry", "headline", "omittedDetailCounts", "outputArtifacts", "readThisFirst"]) requireRecord(insight[field], `${FILES.insight}.${field}`, issues);
  for (const field of ["guidedTours", "rankingBasis", "viewerVisualScenes"]) requireArray(insight[field], `${FILES.insight}.${field}`, issues);
  validateArtifactRows(packet, summary, insight, issues);
  validateReferenceShapes(packet, FILES.packet, issues);
  validateReferenceShapes(insight, FILES.insight, issues);
  const expectedConclusion = deriveConclusion(packet);
  for (const [path, received] of [
    [`${FILES.summary}.conclusion`, summary.conclusion],
    [`${FILES.summary}.readThisFirst.conclusion`, summary.readThisFirst?.conclusion],
    [`${FILES.insight}.readThisFirst.conclusion`, insight.readThisFirst?.conclusion],
    [`${FILES.insight}.headline.conclusionCode`, insight.headline?.conclusionCode],
  ]) if (received !== expectedConclusion) issues.push(issue(path, `${path} does not match the conclusion derived from the measurement packet.`, expectedConclusion, received));
}

function validateRunIdentity(documents, issues) {
  const manifest = documents.manifest;
  const expectedDigests = canonicalJson(manifest.inputDigests);
  for (const name of ["normalized", "packet", "summary", "insight"]) {
    const artifact = documents[name];
    if (artifact.runId !== manifest.runId) issues.push(issue(`${FILES[name]}.runId`, `${FILES[name]} belongs to a different run.`, manifest.runId, artifact.runId));
    if (artifact.toolVersion !== manifest.toolVersion) issues.push(issue(`${FILES[name]}.toolVersion`, `${FILES[name]} was produced by a different tool version.`, manifest.toolVersion, artifact.toolVersion));
    if (canonicalJson(artifact.inputDigests) !== expectedDigests) issues.push(issue(`${FILES[name]}.inputDigests`, `${FILES[name]} input digests do not match the run manifest.`));
  }
  if (documents.summary.profileRef !== documents.packet.profile?.profileId) {
    issues.push(issue(`${FILES.summary}.profileRef`, "Summary profileRef does not match the measurement packet profile.", documents.packet.profile?.profileId, documents.summary.profileRef));
  }
  if (documents.normalized.sourceArchmapRef !== documents.manifest.archmapInputPath) issues.push(issue(`${FILES.normalized}.sourceArchmapRef`, "Normalized ArchMap source reference does not match the run manifest.", documents.manifest.archmapInputPath, documents.normalized.sourceArchmapRef));
}

function bridgeRows(rows, sourceKey, normalizedKey, rawMap, filename, issues) {
  const normalizedToSource = new Map();
  const seenSources = new Set();
  rows.forEach((row, position) => {
    const path = `${filename}.${normalizedKey}[${position}]`;
    if (!isRecord(row) || !requireString(row[sourceKey], `${path}.${sourceKey}`, issues) || !requireString(row[normalizedKey], `${path}.${normalizedKey}`, issues)) return;
    if (!rawMap.has(row[sourceKey])) issues.push(issue(`${path}.${sourceKey}`, `${row[sourceKey]} does not resolve to the loaded ArchMap.`, null, row[sourceKey]));
    if (seenSources.has(row[sourceKey])) issues.push(issue(`${path}.${sourceKey}`, `${row[sourceKey]} has more than one normalized row.`));
    if (normalizedToSource.has(row[normalizedKey])) issues.push(issue(`${path}.${normalizedKey}`, `${row[normalizedKey]} is not a unique normalized id.`));
    seenSources.add(row[sourceKey]);
    normalizedToSource.set(row[normalizedKey], row[sourceKey]);
  });
  for (const rawId of rawMap.keys()) if (!seenSources.has(rawId)) issues.push(issue(filename, `${rawId} has no normalized identity row.`, rawId, null));
  return normalizedToSource;
}

function validateNormalizedRows(normalized, issues) {
  normalized.atoms.forEach((row, position) => {
    const path = `${FILES.normalized}.atoms[${position}]`;
    for (const field of ["atomKind", "subject", "axis", "predicate", "normalizationStatus"]) requireString(row?.[field], `${path}.${field}`, issues);
    requireArray(row?.sourceRefs, `${path}.sourceRefs`, issues);
    requireArray(row?.contextMemberships, `${path}.contextMemberships`, issues);
  });
  normalized.contexts.forEach((row, position) => {
    const path = `${FILES.normalized}.contexts[${position}]`;
    for (const field of ["atomIds", "restrictsTo", "sourceRefs"]) requireArray(row?.[field], `${path}.${field}`, issues);
    requireString(row?.posetStatus, `${path}.posetStatus`, issues);
  });
  normalized.covers.forEach((row, position) => {
    const path = `${FILES.normalized}.covers[${position}]`;
    for (const field of ["contextIds", "sourceRefs"]) requireArray(row?.[field], `${path}.${field}`, issues);
    requireString(row?.coverageStatus, `${path}.coverageStatus`, issues);
  });
}

function validateNormalizedBridge(normalized, index, issues) {
  if (normalized.sourceArchmapId !== index.id) issues.push(issue(`${FILES.normalized}.sourceArchmapId`, "Normalized ArchMap identifies a different source ArchMap.", index.id, normalized.sourceArchmapId));
  if (normalized.normalizerId !== "archmap-schema052-finite-poset-site@1") issues.push(issue(`${FILES.normalized}.normalizerId`, "Normalized ArchMap must identify the existing deterministic ArchSig normalizer.", "archmap-schema052-finite-poset-site@1", normalized.normalizerId));
  const prefixed = (prefix, id) => id.startsWith(`${prefix}:`) ? id : `${prefix}:${id}`;
  const sortedUnique = (values) => [...new Set(values || [])].sort();
  const memberships = new Map();
  for (const context of index.contexts) for (const atomId of context.atoms || []) memberships.set(atomId, [...(memberships.get(atomId) || []), prefixed("ctx", context.id)]);
  const expectedAtoms = [...index.atoms].map((atom) => ({
    sourceAtomId: atom.id,
    normalizedAtomId: prefixed("atom", atom.id),
    atomKind: atom.kind,
    subject: atom.subject,
    axis: atom.axis,
    predicate: atom.predicate || atom.kind,
    ...(atom.object === undefined ? {} : { object: atom.object }),
    sourceRefs: sortedUnique(atom.refs),
    contextMemberships: sortedUnique(memberships.get(atom.id)),
    normalizationStatus: "normalized",
  })).sort((left, right) => left.normalizedAtomId < right.normalizedAtomId ? -1 : left.normalizedAtomId > right.normalizedAtomId ? 1 : 0);
  const expectedContexts = [...index.contexts].map((context) => ({
    sourceContextId: context.id,
    normalizedContextId: prefixed("ctx", context.id),
    atomIds: sortedUnique((context.atoms || []).map((id) => prefixed("atom", id))),
    restrictsTo: sortedUnique((context.restrictsTo || []).map((id) => prefixed("ctx", id))),
    sourceRefs: sortedUnique(context.refs),
    posetStatus: "finiteObserved",
  })).sort((left, right) => left.normalizedContextId < right.normalizedContextId ? -1 : left.normalizedContextId > right.normalizedContextId ? 1 : 0);
  const expectedCovers = [...index.covers].map((cover) => ({
    sourceCoverId: cover.id,
    normalizedCoverId: prefixed("cover", cover.id),
    contextIds: sortedUnique((cover.contexts || []).map((id) => prefixed("ctx", id))),
    sourceRefs: sortedUnique(cover.refs),
    coverageStatus: "selectedCandidate",
  })).sort((left, right) => left.normalizedCoverId < right.normalizedCoverId ? -1 : left.normalizedCoverId > right.normalizedCoverId ? 1 : 0);
  for (const [field, expected] of [["atoms", expectedAtoms], ["contexts", expectedContexts], ["covers", expectedCovers]]) {
    if (canonicalJson(normalized[field]) !== canonicalJson(expected)) issues.push(issue(`${FILES.normalized}.${field}`, `Normalized ${field} do not match the deterministic ArchSig projection of the loaded ArchMap.`));
  }
  const raw = JSON.parse(index.canonicalJson);
  const expectedDoctrine = raw.extractionDoctrineRef || {
    doctrineId: "doctrine:aat-canonical@1",
    fingerprint: "sha256:aat-canonical-doctrine-schema052",
    components: ["V", "Gamma", "R", "rho", "E", "N"],
  };
  if (canonicalJson(normalized.extractionDoctrineRef) !== canonicalJson(expectedDoctrine)) issues.push(issue(`${FILES.normalized}.extractionDoctrineRef`, "Normalized extraction doctrine does not match the loaded ArchMap."));
  const expectedSummary = {
    atomCount: expectedAtoms.length,
    normalizedAtomCount: expectedAtoms.length,
    contextCount: expectedContexts.length,
    coverCount: expectedCovers.length,
    doctrineFingerprint: raw.extractionDoctrineRef?.fingerprint || "sha256:aat-canonical-doctrine-schema052",
  };
  if (canonicalJson(normalized.summary) !== canonicalJson(expectedSummary)) issues.push(issue(`${FILES.normalized}.summary`, "Normalized summary does not match the loaded ArchMap."));
  return Object.freeze({
    atoms: bridgeRows(normalized.atoms, "sourceAtomId", "normalizedAtomId", index.atomsById, FILES.normalized, issues),
    contexts: bridgeRows(normalized.contexts, "sourceContextId", "normalizedContextId", index.contextsById, FILES.normalized, issues),
    covers: bridgeRows(normalized.covers, "sourceCoverId", "normalizedCoverId", index.coversById, FILES.normalized, issues),
  });
}

const REF_FIELDS = Object.freeze({
  atomRefs: "atoms", supportAtomRefs: "atoms", mismatchSupportRefs: "atoms", sharedAtomRefs: "atoms",
  atomObservationRefs: "atoms", concreteSupportRefs: "atoms", fromAtomRefs: "atoms", rawAtomRefs: "atoms", witnessSupportRefs: "atoms",
  contextRefs: "contexts", sourceRefs: "sources", coverRefs: "covers",
});
const SINGLE_REF_FIELDS = Object.freeze({
  atomRef: "atoms", supportAtomRef: "atoms", boundaryAtomRef: "atoms", cochainAtomRef: "atoms", dOmegaAtomRef: "atoms", witnessAtomRef: "atoms",
  contextRef: "contexts",
  sourceContextRef: "contexts", targetContextRef: "contexts", coverRef: "covers", selectedCoverRef: "covers",
});

function resolves(ref, kind, index, bridges) {
  const rawMap = kind === "sources" ? index.sourcesById : index[`${kind}ById`];
  return rawMap.has(ref) || bridges[kind]?.has(ref);
}

function collectUnresolved(value, path, index, bridges, unresolved) {
  if (typeof value === "string") {
    const edge = value.match(/^(ctx:[^>]+)->(ctx:.+)$/);
    if (edge) {
      const source = bridges.contexts.get(edge[1]) || edge[1];
      const target = bridges.contexts.get(edge[2]) || edge[2];
      const context = index.contextsById.get(source);
      if (!context || !index.contextsById.has(target) || !(context.restrictsTo || []).includes(target)) unresolved.push(issue(path, `${value} does not resolve to an explicit ArchMap Context relation.`, null, value));
      return;
    }
    const kind = value.startsWith("atom:") ? "atoms" : value.startsWith("ctx:") ? "contexts" : value.startsWith("cover:") ? "covers" : value.startsWith("src:") ? "sources" : null;
    if (kind && !resolves(value, kind, index, bridges)) unresolved.push(issue(path, `${value} does not resolve through the loaded ArchMap or normalized identity bridge.`, null, value));
    return;
  }
  if (Array.isArray(value)) return value.forEach((entry, position) => collectUnresolved(entry, `${path}[${position}]`, index, bridges, unresolved));
  if (!isRecord(value)) return;
  for (const [key, child] of Object.entries(value)) {
    const childPath = `${path}.${key}`;
    if ((key === "edgeRefs" || key === "unobservedEdgeRefs") && Array.isArray(child)) {
      child.forEach((ref, position) => {
        const match = typeof ref === "string" && ref.match(/^(ctx:[^>]+)->(ctx:.+)$/);
        if (!match) { unresolved.push(issue(`${childPath}[${position}]`, `${ref} is not an explicit Context relation.`)); return; }
        const source = bridges.contexts.get(match[1]) || match[1];
        const target = bridges.contexts.get(match[2]) || match[2];
        const context = index.contextsById.get(source);
        const endpointsResolve = context && index.contextsById.has(target);
        const relationResolves = (context?.restrictsTo || []).includes(target);
        if (!endpointsResolve || !relationResolves) unresolved.push(issue(`${childPath}[${position}]`, `${ref} does not resolve to ${key === "edgeRefs" ? "an explicit ArchMap Context relation" : "loaded ArchMap Contexts"}.`, null, ref));
      });
      continue;
    }
    const kind = REF_FIELDS[key];
    if (kind && Array.isArray(child)) {
      child.forEach((ref, position) => {
        if (typeof ref === "string" && !resolves(ref, kind, index, bridges)) unresolved.push(issue(`${childPath}[${position}]`, `${ref} does not resolve through the loaded ArchMap or normalized identity bridge.`, null, ref));
      });
      continue;
    }
    const singleKind = SINGLE_REF_FIELDS[key];
    if (singleKind && typeof child === "string") {
      if (!resolves(child, singleKind, index, bridges)) unresolved.push(issue(childPath, `${child} does not resolve through the loaded ArchMap or normalized identity bridge.`, null, child));
      continue;
    }
    if (key === "targetRefs" && Array.isArray(child)) {
      child.forEach((ref, position) => {
        if (typeof ref !== "string") return;
        const kind = ref.startsWith("atom:") ? "atoms" : ref.startsWith("ctx:") ? "contexts" : ref.startsWith("cover:") ? "covers" : ref.startsWith("src:") ? "sources" : null;
        if (kind && !resolves(ref, kind, index, bridges)) unresolved.push(issue(`${childPath}[${position}]`, `${ref} does not resolve through the loaded ArchMap or normalized identity bridge.`, null, ref));
      });
      continue;
    }
    collectUnresolved(child, childPath, index, bridges, unresolved);
  }
}

function collectNamedRefs(value, names, output = []) {
  if (Array.isArray(value)) {
    value.forEach((entry) => collectNamedRefs(entry, names, output));
    return output;
  }
  if (!isRecord(value)) return output;
  for (const [key, child] of Object.entries(value)) {
    if (names.has(key)) {
      if (Array.isArray(child)) output.push(...child.filter((entry) => typeof entry === "string"));
      else if (typeof child === "string") output.push(child);
    }
    collectNamedRefs(child, names, output);
  }
  return output;
}

function comparisonRowKey(row) {
  const evaluator = row?.evaluator || "unknown-evaluator";
  const law = row?.law || "unknown-law";
  let target;
  if (isRecord(row?.target)) {
    target = { ...row.target };
    delete target.classRef;
    target = JSON.parse(canonicalJson(target));
  } else {
    target = row?.verdictRef || row?.structuralVerdictRef || row?.verdictData?.methodStatus || row?.methodStatus || "unknown-target";
  }
  return `${evaluator}|${law}|${typeof target === "string" ? target : canonicalJson(target)}`;
}

function gateVerdictRows(packet) {
  const structural = packet.structuralVerdict || [];
  const boundariesByScope = new Map();
  (packet.boundaryStatements || []).forEach((row) => (row?.scopeRefs || []).forEach((ref) => {
    const kinds = boundariesByScope.get(ref) || new Set();
    kinds.add(row.kind);
    boundariesByScope.set(ref, kinds);
  }));
  const analyticSilence = structural.length ? [] : (packet.analyticReadings || []).filter((row) => boundariesByScope.get(row.readingId)?.has("silence_by_design")).map((row) => ({
    verdictRef: row.readingId, evaluator: row.evaluator, law: row.evaluator, verdict: "not_computed", verdictData: { methodStatus: "analytic_reading_silence_by_design" }, dependsOnAssumptions: [],
  }));
  const comparisonSilence = (packet.computedInvariants || []).filter((row) => row.evaluator === "ag.saga-comparison" && row.status === "silence_by_design" && boundariesByScope.get(row.invariantId)?.has("silence_by_design")).map((row) => ({
    verdictRef: row.invariantId, evaluator: row.evaluator, law: row.evaluator, verdict: "not_computed", verdictData: { methodStatus: row.reason }, dependsOnAssumptions: [],
  }));
  return [...structural, ...analyticSilence, ...(structural.length || analyticSilence.length ? comparisonSilence : [])];
}

function validateFindingProvenance(documents, index, bridges, issues) {
  const packet = documents.packet;
  const verdictByRef = new Map(packet.structuralVerdict.map((row) => [row.verdictRef, row]));
  const invariantByRef = new Map(packet.computedInvariants.map((row) => [row.invariantId, row]));
  const rawRef = (ref, kind) => bridges[kind]?.get(ref) || ref;
  (documents.insight.insightCards || []).forEach((card, position) => {
    const evidence = card?.evidence;
    if (!isRecord(evidence) || !(evidence.structuralVerdictRefs || []).length) return;
    const path = `${FILES.insight}.insightCards[${position}].evidence`;
    const rows = evidence.structuralVerdictRefs.map((ref) => verdictByRef.get(ref)).filter(Boolean);
    const rowInvariants = rows.flatMap((row) => {
      const certInvariant = row.verdictData?.certRef?.startsWith("computedInvariants/") ? row.verdictData.certRef.slice("computedInvariants/".length) : null;
      const explicitRefs = new Set(row.evidence?.computedInvariantRefs || []);
      return packet.computedInvariants.filter((invariant) => explicitRefs.has(invariant.invariantId) || invariant.invariantId === certInvariant);
    });
    const allowedInvariantRefs = new Set(rowInvariants.map((row) => row.invariantId));
    const cardInvariantRefs = new Set(evidence.computedInvariantRefs || []);
    rows.forEach((row) => {
      if (!(evidence.evaluatorRefs || []).includes(row.evaluator)) issues.push(issue(`${path}.evaluatorRefs`, `Finding does not preserve evaluator provenance for ${row.verdictRef}.`, row.evaluator, evidence.evaluatorRefs));
      (row.evidence?.computedInvariantRefs || []).forEach((ref) => { if (!cardInvariantRefs.has(ref)) issues.push(issue(`${path}.computedInvariantRefs`, `Finding omits a computed invariant cited by ${row.verdictRef}.`, ref, evidence.computedInvariantRefs)); });
    });
    (evidence.computedInvariantRefs || []).forEach((ref, refPosition) => { if (!allowedInvariantRefs.has(ref)) issues.push(issue(`${path}.computedInvariantRefs[${refPosition}]`, `Finding invariant is not derived from its selected structural verdict row.`, null, ref)); });
    const selectedInvariants = (evidence.computedInvariantRefs || []).map((ref) => invariantByRef.get(ref)).filter(Boolean);
    const explicitRowSources = new Set(rows.flatMap((row) => row.evidence?.sourceRefs || []));
    const allowedAtoms = new Set(collectNamedRefs(selectedInvariants, new Set(["supportAtomRefs", "mismatchSupportRefs", "witnessSupportRefs", "atomRefs", "atomRef"])).map((ref) => rawRef(ref, "atoms")));
    (evidence.atomRefs || []).forEach((ref, refPosition) => { if (!allowedAtoms.has(rawRef(ref, "atoms"))) issues.push(issue(`${path}.atomRefs[${refPosition}]`, `Finding Atom is not supported by an explicit selected verdict or invariant reference.`, null, ref)); });
    const allowedContexts = new Set(collectNamedRefs(selectedInvariants, new Set(["contextRefs", "contextRef", "selectedContexts", "sourceContext", "targetContext"])).map((ref) => rawRef(ref, "contexts")));
    collectNamedRefs(selectedInvariants, new Set(["edgeId", "edgeRefs", "unobservedEdgeRefs"])).forEach((edge) => {
      const match = edge.match(/^(ctx:[^>]+)->(ctx:.+)$/);
      if (match) { allowedContexts.add(rawRef(match[1], "contexts")); allowedContexts.add(rawRef(match[2], "contexts")); }
    });
    allowedAtoms.forEach((atomId) => (index.contextIdsByAtom.get(atomId) || []).forEach((contextId) => allowedContexts.add(contextId)));
    (evidence.contextRefs || []).forEach((ref, refPosition) => { if (!allowedContexts.has(rawRef(ref, "contexts"))) issues.push(issue(`${path}.contextRefs[${refPosition}]`, `Finding Context is not supported by its selected verdict evidence.`, null, ref)); });
    const allowedSources = new Set([...explicitRowSources, ...collectNamedRefs(selectedInvariants, new Set(["sourceRefs", "sourceRef"]))]);
    allowedAtoms.forEach((atomId) => (index.atomsById.get(atomId)?.refs || []).forEach((sourceRef) => allowedSources.add(sourceRef)));
    const selectedCover = rawRef(packet.profile.coverRef, "covers");
    (evidence.coverRefs || []).forEach((ref, refPosition) => { if (rawRef(ref, "covers") !== selectedCover) issues.push(issue(`${path}.coverRefs[${refPosition}]`, `Finding Cover does not match the selected measurement profile Cover.`, selectedCover, ref)); });
    (evidence.sourceRefs || []).forEach((ref, refPosition) => { if (!allowedSources.has(ref)) issues.push(issue(`${path}.sourceRefs[${refPosition}]`, `Finding source is not supported by its selected verdict evidence.`, null, ref)); });
  });
}

function validateNormalizedReferences(normalized, index, bridges, unresolved) {
  normalized.atoms.forEach((row, position) => {
    (row.sourceRefs || []).forEach((ref, refPosition) => { if (!resolves(ref, "sources", index, bridges)) unresolved.push(issue(`${FILES.normalized}.atoms[${position}].sourceRefs[${refPosition}]`, `${ref} does not resolve to an ArchMap source.`)); });
    (row.contextMemberships || []).forEach((ref, refPosition) => { if (!resolves(ref, "contexts", index, bridges)) unresolved.push(issue(`${FILES.normalized}.atoms[${position}].contextMemberships[${refPosition}]`, `${ref} does not resolve through the normalized Context bridge.`)); });
  });
  normalized.contexts.forEach((row, position) => {
    for (const [field, kind] of [["atomIds", "atoms"], ["restrictsTo", "contexts"], ["sourceRefs", "sources"]]) {
      (row[field] || []).forEach((ref, refPosition) => { if (!resolves(ref, kind, index, bridges)) unresolved.push(issue(`${FILES.normalized}.contexts[${position}].${field}[${refPosition}]`, `${ref} does not resolve through the normalized identity bridge.`)); });
    }
  });
  normalized.covers.forEach((row, position) => {
    for (const [field, kind] of [["contextIds", "contexts"], ["sourceRefs", "sources"]]) {
      (row[field] || []).forEach((ref, refPosition) => { if (!resolves(ref, kind, index, bridges)) unresolved.push(issue(`${FILES.normalized}.covers[${position}].${field}[${refPosition}]`, `${ref} does not resolve through the normalized identity bridge.`)); });
    }
  });
}

function validateOptionalArtifacts(documents, issues) {
  for (const name of ["comparison", "gate"]) if (documents[name] !== undefined) validateRoot(name, documents[name], issues);
  if (isRecord(documents.gate)) {
    requireString(documents.gate.toolVersion, `${FILES.gate}.toolVersion`, issues);
    requireString(documents.gate.decision, `${FILES.gate}.decision`, issues);
    if (!new Set(["PASS_WITHIN_GATE_POLICY", "BLOCKED_BY_GATE_POLICY", "NOT_EVALUABLE"]).has(documents.gate.decision)) issues.push(issue(`${FILES.gate}.decision`, "Gate decision is not an ArchSig gate decision.", null, documents.gate.decision));
    requireRecord(documents.gate.inputDigests, `${FILES.gate}.inputDigests`, issues);
    requireDigestEntry(documents.gate.inputDigests?.measurementPacket, `${FILES.gate}.inputDigests.measurementPacket`, issues);
    requireDigestEntry(documents.gate.inputDigests?.gatePolicy, `${FILES.gate}.inputDigests.gatePolicy`, issues);
    for (const field of ["ruleOutcomes", "nonConclusions"]) requireArray(documents.gate[field], `${FILES.gate}.${field}`, issues);
    requireObjectArray(documents.gate.ruleOutcomes, `${FILES.gate}.ruleOutcomes`, [], issues);
    if (documents.gate.decision === "NOT_EVALUABLE") {
      requireString(documents.gate.reason, `${FILES.gate}.reason`, issues);
      if ((documents.gate.ruleOutcomes || []).length) issues.push(issue(`${FILES.gate}.ruleOutcomes`, "A NOT_EVALUABLE gate report cannot contain evaluated rule outcomes."));
    } else {
      requireObjectArray(documents.gate.policyValidation, `${FILES.gate}.policyValidation`, ["id", "result"], issues);
      if (!(documents.gate.policyValidation || []).length) issues.push(issue(`${FILES.gate}.policyValidation`, "An evaluated gate report must contain policy validation checks."));
      requireObjectArray(documents.gate.ruleOutcomes, `${FILES.gate}.ruleOutcomes`, ["ruleId", "scope", "status"], issues);
      if (!(documents.gate.ruleOutcomes || []).length) issues.push(issue(`${FILES.gate}.ruleOutcomes`, "An evaluated gate report must contain rule outcomes."));
      (documents.gate.ruleOutcomes || []).forEach((row, position) => {
        const path = `${FILES.gate}.ruleOutcomes[${position}]`;
        if (!new Set(["absolute", "introduced-by-change"]).has(row?.scope)) issues.push(issue(`${path}.scope`, "Gate rule scope is not in the producer vocabulary.", null, row?.scope));
        if (!new Set(["evaluated", "not_applicable"]).has(row?.status)) issues.push(issue(`${path}.status`, "Gate rule status is not in the producer vocabulary.", null, row?.status));
        if (row?.status === "evaluated") requireObjectArray(row.appliedMapping, `${path}.appliedMapping`, ["action"], issues);
        if (row?.scope === "introduced-by-change" && row?.status === "evaluated" && !documents.comparison) issues.push(issue(`${path}.status`, "An introduced-by-change rule can be evaluated only when a comparison report is supplied.", "not_applicable", row.status));
        if (row?.status === "not_applicable") {
          if (row.scope !== "introduced-by-change") issues.push(issue(`${path}.scope`, "Only introduced-by-change rules can be not_applicable.", "introduced-by-change", row.scope));
          requireString(row.reason, `${path}.reason`, issues);
          if (row.appliedMapping !== undefined) issues.push(issue(`${path}.appliedMapping`, "A not_applicable gate outcome cannot contain applied mappings."));
          if (documents.comparison) issues.push(issue(`${path}.status`, "An introduced-by-change rule must be evaluated when a comparison report is supplied.", "evaluated", row.status));
        }
      });
      (documents.gate.policyValidation || []).forEach((check, position) => { if (check?.result !== "pass") issues.push(issue(`${FILES.gate}.policyValidation[${position}].result`, "An evaluated gate report requires passing policy validation checks.", "pass", check?.result)); });
      const actions = (documents.gate.ruleOutcomes || []).flatMap((row) => row?.appliedMapping || []).map((row) => row?.action);
      actions.forEach((action, position) => { if (!new Set(["pass", "pass_with_boundary", "block"]).has(action)) issues.push(issue(`${FILES.gate}.ruleOutcomes.appliedMapping[${position}].action`, "Gate action is not in the closed ArchSig action vocabulary.", null, action)); });
      const expectedDecision = actions.includes("block") ? "BLOCKED_BY_GATE_POLICY" : "PASS_WITHIN_GATE_POLICY";
      if (documents.gate.decision !== expectedDecision) issues.push(issue(`${FILES.gate}.decision`, "Gate decision does not match its applied rule actions.", expectedDecision, documents.gate.decision));
    }
  }
  if (isRecord(documents.comparison)) {
    requireString(documents.comparison.toolVersion, `${FILES.comparison}.toolVersion`, issues);
    requireString(documents.comparison.conclusionCode, `${FILES.comparison}.conclusionCode`, issues);
    if (!COMPARISON_CONCLUSIONS.has(documents.comparison.conclusionCode)) issues.push(issue(`${FILES.comparison}.conclusionCode`, "Comparison conclusionCode is not an ArchSig comparison conclusion.", null, documents.comparison.conclusionCode));
    if (requireRecord(documents.comparison.inputDigests, `${FILES.comparison}.inputDigests`, issues)) {
      requireRecord(documents.comparison.inputDigests.baseRun, `${FILES.comparison}.inputDigests.baseRun`, issues);
      requireRecord(documents.comparison.inputDigests.headRun, `${FILES.comparison}.inputDigests.headRun`, issues);
    }
    requireRecord(documents.comparison.comparability, `${FILES.comparison}.comparability`, issues);
    requireString(documents.comparison.discipline, `${FILES.comparison}.discipline`, issues);
    if (documents.comparison.discipline !== COMPARISON_DISCIPLINE) issues.push(issue(`${FILES.comparison}.discipline`, "Comparison discipline does not match the ArchSig record discipline.", COMPARISON_DISCIPLINE, documents.comparison.discipline));
    if (!new Set(["identical", "verdict-row", "not-comparable"]).has(documents.comparison.comparability?.level)) issues.push(issue(`${FILES.comparison}.comparability.level`, "Comparison comparability level is not supported.", null, documents.comparison.comparability?.level));
    requireRecord(documents.comparison.artifactRefs, `${FILES.comparison}.artifactRefs`, issues);
    requireRecord(documents.comparison.independentConclusions, `${FILES.comparison}.independentConclusions`, issues);
    requireArray(documents.comparison.verdictTransitions, `${FILES.comparison}.verdictTransitions`, issues);
    requireArray(documents.comparison.boundaryStatements, `${FILES.comparison}.boundaryStatements`, issues);
    requireRecord(documents.comparison.classTransport, `${FILES.comparison}.classTransport`, issues);
    requireArray(documents.comparison.nonConclusions, `${FILES.comparison}.nonConclusions`, issues);
    requireObjectArray(documents.comparison.verdictTransitions, `${FILES.comparison}.verdictTransitions`, [], issues);
    requireObjectArray(documents.comparison.boundaryStatements, `${FILES.comparison}.boundaryStatements`, [], issues);
    const transitionKeys = new Set();
    (documents.comparison.verdictTransitions || []).forEach((row, position) => {
      if (!isRecord(row)) return;
      const path = `${FILES.comparison}.verdictTransitions[${position}]`;
      for (const field of ["rowKey", "baseVerdict", "headVerdict", "transition", "introducedByChangeCategory", "discipline"]) requireString(row[field], `${path}.${field}`, issues);
      if (!COMPARISON_TRANSITIONS.has(row.transition)) issues.push(issue(`${path}.transition`, "Comparison transition is not an ArchSig record transition.", null, row.transition));
      for (const field of ["baseVerdict", "headVerdict"]) if (!new Set(["measured_zero", "measured_nonzero", "unmeasured", "unknown", "not_computed", "absent"]).has(row[field])) issues.push(issue(`${path}.${field}`, `Comparison ${field} is not a structural verdict or absent.`, null, row[field]));
      if (row.discipline !== COMPARISON_DISCIPLINE) issues.push(issue(`${path}.discipline`, "Comparison transition discipline does not match the ArchSig record discipline.", COMPARISON_DISCIPLINE, row.discipline));
      const expectedCategory = ({ new_recorded_row: "new", removed_recorded_row: "removed", measured_obstruction_no_longer_recorded: "cleared", measured_obstruction_recorded_after_change: "new", preexisting_recorded_row: "preexisting", other_transition: "other" })[row.transition];
      if (row.introducedByChangeCategory !== expectedCategory) issues.push(issue(`${path}.introducedByChangeCategory`, "Comparison change category does not match its transition.", expectedCategory, row.introducedByChangeCategory));
      for (const field of ["baseRowRef", "headRowRef"]) if (row[field] !== null && row[field] !== undefined) requireString(row[field], `${path}.${field}`, issues);
      requireObjectArray(row.deltaRefs, `${path}.deltaRefs`, ["diffRef", "op", "kind", "id"], issues);
      (row.deltaRefs || []).forEach((delta, deltaPosition) => {
        if (!isRecord(delta)) return;
        if (!["added", "removed", "modified"].includes(delta.op)) issues.push(issue(`${path}.deltaRefs[${deltaPosition}].op`, "Comparison delta op is not supported.", null, delta.op));
        if (!["sources", "atoms", "contexts", "covers"].includes(delta.kind)) issues.push(issue(`${path}.deltaRefs[${deltaPosition}].kind`, "Comparison delta kind is not supported.", null, delta.kind));
        const expectedDiffRef = `archmap-diff/${delta.kind}/${delta.op}/${delta.id}`;
        if (delta.diffRef !== expectedDiffRef) issues.push(issue(`${path}.deltaRefs[${deltaPosition}].diffRef`, "Comparison diffRef does not match kind, op, and id.", expectedDiffRef, delta.diffRef));
      });
      if (typeof row.rowKey === "string" && transitionKeys.has(row.rowKey)) issues.push(issue(`${path}.rowKey`, "Comparison verdict transition rowKey values must be unique.", null, row.rowKey));
      transitionKeys.add(row.rowKey);
    });
    const coverChanged = (documents.comparison.boundaryStatements || []).some((row) => row?.kind === "cover_changed_between_runs");
    const notComparable = documents.comparison.comparability?.level === "not-comparable";
    (documents.comparison.verdictTransitions || []).forEach((row, position) => {
      if (!isRecord(row)) return;
      const expectedTransition = notComparable || coverChanged ? "other_transition"
        : row.baseVerdict === "absent" ? "new_recorded_row"
        : row.headVerdict === "absent" ? "removed_recorded_row"
        : row.baseVerdict === "measured_nonzero" && row.headVerdict === "measured_zero" ? "measured_obstruction_no_longer_recorded"
        : row.baseVerdict === "measured_zero" && row.headVerdict === "measured_nonzero" ? "measured_obstruction_recorded_after_change"
        : row.baseVerdict === row.headVerdict ? "preexisting_recorded_row" : "other_transition";
      if (row.transition !== expectedTransition) issues.push(issue(`${FILES.comparison}.verdictTransitions[${position}].transition`, "Comparison transition does not match its declared verdict pair and comparability.", expectedTransition, row.transition));
    });
    const transitions = documents.comparison.verdictTransitions || [];
    const expectedConclusion = notComparable ? "RUNS_NOT_COMPARABLE_WITHOUT_COMPARISON_DATA"
      : transitions.some((row) => row?.transition === "measured_obstruction_recorded_after_change") ? "MEASURED_OBSTRUCTION_RECORDED_AFTER_CHANGE"
      : transitions.some((row) => row?.transition === "measured_obstruction_no_longer_recorded") ? "MEASURED_OBSTRUCTION_NO_LONGER_RECORDED_AFTER_CHANGE"
      : "NO_NEW_MEASURED_OBSTRUCTION_RECORDED";
    if (documents.comparison.conclusionCode !== expectedConclusion) issues.push(issue(`${FILES.comparison}.conclusionCode`, "Comparison conclusionCode does not match its record transitions.", expectedConclusion, documents.comparison.conclusionCode));
  }
}

function validateComponentFingerprints(documents, issues) {
  const digests = documents.manifest.inputDigests;
  const expected = {
    lawPolicy: `sha256:${digests.lawPolicy.sha256}`,
    lawSurface: `sha256:${digests.lawSurface.sha256}`,
    measurementProfile: `sha256:${digests.measurementProfile.sha256}`,
  };
  const expectedJson = canonicalJson(expected);
  for (const name of ["manifest", "normalized", "packet", "summary", "insight"]) {
    if (canonicalJson(documents[name].componentFingerprints) !== expectedJson) issues.push(issue(`${FILES[name]}.componentFingerprints`, `${FILES[name]} component fingerprints do not match the input artifacts.`, expectedJson, canonicalJson(documents[name].componentFingerprints)));
  }
}

function validateComparisonRun(run, path, issues) {
  requireString(run.path, `${path}.path`, issues);
  requireString(run.runId, `${path}.runId`, issues);
  requireString(run.toolVersion, `${path}.toolVersion`, issues);
  requireDigestEntry(run.archmap, `${path}.archmap`, issues);
  requireDigestEntry(run.lawPolicy, `${path}.lawPolicy`, issues);
  requireRecord(run.componentFingerprints, `${path}.componentFingerprints`, issues);
  for (const field of ["profileFingerprint", "siteCoverDigest"]) {
    if (!requireRecord(run[field], `${path}.${field}`, issues) || typeof run[field].sha256 !== "string" || !/^[0-9a-f]{64}$/.test(run[field].sha256)) issues.push(issue(`${path}.${field}.sha256`, `${path}.${field}.sha256 must be a lowercase SHA-256 digest.`));
  }
  requireDigestEntry(run.measurementPacket, `${path}.measurementPacket`, issues);
}

export async function validateAnalysisBundle(documents, architectureIndex) {
  if (!architectureIndex) throw new AnalysisValidationError("mismatch", [issue("archmap", "Load an ArchMap before loading ArchSig analysis.")]);
  const missing = REQUIRED.filter((name) => !isRecord(documents?.[name]));
  if (missing.length) throw new AnalysisValidationError("malformed", missing.map((name) => issue(FILES[name], `${FILES[name]} is required for a measurement run.`)));
  documents = cloneDocuments(documents);

  const shapeIssues = [];
  validateCoreShape(documents, shapeIssues);
  validateOptionalArtifacts(documents, shapeIssues);
  if (shapeIssues.length) throw new AnalysisValidationError("malformed", shapeIssues);

  const mismatch = [];
  validateRunIdentity(documents, mismatch);
  validateComponentFingerprints(documents, mismatch);
  const artifactArchmapDigest = documents.manifest.inputDigests?.archmap?.sha256;
  const currentArchmapDigest = await sha256Hex(architectureIndex.canonicalJson);
  if (!/^[0-9a-f]{64}$/.test(artifactArchmapDigest || "")) mismatch.push(issue(`${FILES.manifest}.inputDigests.archmap.sha256`, "Manifest ArchMap digest must be a lowercase SHA-256 digest.", null, artifactArchmapDigest));
  else if (artifactArchmapDigest !== currentArchmapDigest) mismatch.push(issue(`${FILES.manifest}.inputDigests.archmap.sha256`, "The measurement run was not produced from the loaded ArchMap.", currentArchmapDigest, artifactArchmapDigest));
  const runSeed = [
    documents.manifest.inputDigests.archmap.sha256,
    documents.manifest.inputDigests.lawPolicy.sha256,
    documents.manifest.inputDigests.lawSurface.sha256,
    ...documents.manifest.inputDigests.measurementProfiles.map((entry) => entry.sha256),
    ...(documents.manifest.inputDigests.residualPacket?.sha256 ? [documents.manifest.inputDigests.residualPacket.sha256] : []),
    documents.manifest.toolVersion,
  ].join("|");
  const expectedRunId = `run:${(await sha256Hex(runSeed)).slice(0, 12)}`;
  if (documents.manifest.runId !== expectedRunId && !documents.manifest.runId.match(new RegExp(`^${expectedRunId}-stamp:[0-9]+$`))) mismatch.push(issue(`${FILES.manifest}.runId`, "Run id is not derived from the declared analyze inputs and tool version.", expectedRunId, documents.manifest.runId));
  if (mismatch.length) throw new AnalysisValidationError("mismatch", mismatch);

  const unresolved = [];
  const bridges = validateNormalizedBridge(documents.normalized, architectureIndex, unresolved);
  validateNormalizedReferences(documents.normalized, architectureIndex, bridges, unresolved);
  collectUnresolved(documents.packet, FILES.packet, architectureIndex, bridges, unresolved);
  collectUnresolved(documents.insight, FILES.insight, architectureIndex, bridges, unresolved);
  validateFindingProvenance(documents, architectureIndex, bridges, unresolved);
  if (unresolved.length) throw new AnalysisValidationError("unresolved", unresolved);

  const packetDigest = await sha256Hex(documents.packet);
  for (const name of ["gate", "comparison"]) {
    if (documents[name]?.toolVersion !== undefined && documents[name].toolVersion !== documents.manifest.toolVersion) {
      throw new AnalysisValidationError("mismatch", [issue(`${FILES[name]}.toolVersion`, `${FILES[name]} was produced by a different tool version.`, documents.manifest.toolVersion, documents[name].toolVersion)]);
    }
  }
  if (documents.gate?.inputDigests?.measurementPacket?.sha256 && documents.gate.inputDigests.measurementPacket.sha256 !== packetDigest) {
    throw new AnalysisValidationError("mismatch", [issue(`${FILES.gate}.inputDigests.measurementPacket.sha256`, "Gate report packet digest does not match the loaded measurement packet.", packetDigest, documents.gate.inputDigests.measurementPacket.sha256)]);
  }
  let comparisonSides = [];
  if (documents.comparison) {
    const runs = [documents.comparison.inputDigests?.baseRun, documents.comparison.inputDigests?.headRun].filter(isRecord);
    const comparisonShapeIssues = [];
    runs.forEach((run, position) => validateComparisonRun(run, `${FILES.comparison}.inputDigests.${position ? "headRun" : "baseRun"}`, comparisonShapeIssues));
    if (comparisonShapeIssues.length) throw new AnalysisValidationError("malformed", comparisonShapeIssues);
    const [baseRun, headRun] = runs;
    const sameToolVersion = baseRun.toolVersion === headRun.toolVersion;
    const sameArchmapDigest = baseRun.archmap?.sha256 === headRun.archmap?.sha256;
    const sameLawPolicyDigest = baseRun.lawPolicy?.sha256 === headRun.lawPolicy?.sha256;
    const sameProfileFingerprint = baseRun.profileFingerprint?.sha256 === headRun.profileFingerprint?.sha256;
    const sameSiteCoverDigest = baseRun.siteCoverDigest?.sha256 === headRun.siteCoverDigest?.sha256;
    const sameComponentFingerprints = canonicalJson(baseRun.componentFingerprints) === canonicalJson(headRun.componentFingerprints);
    const sameLawSurfaceFingerprint = baseRun.componentFingerprints?.lawSurface !== undefined && baseRun.componentFingerprints?.lawSurface === headRun.componentFingerprints?.lawSurface;
    const expectedComparability = sameToolVersion && sameArchmapDigest && sameLawPolicyDigest && sameProfileFingerprint && sameComponentFingerprints ? "identical"
      : sameToolVersion && sameProfileFingerprint && sameSiteCoverDigest && sameLawSurfaceFingerprint && sameComponentFingerprints ? "verdict-row" : "not-comparable";
    const comparisonConsistencyIssues = [];
    if (documents.comparison.comparability.level !== expectedComparability) comparisonConsistencyIssues.push(issue(`${FILES.comparison}.comparability.level`, "Comparison comparability does not match its run digests.", expectedComparability, documents.comparison.comparability.level));
    for (const [field, expected] of Object.entries({ sameToolVersion, sameArchmapDigest, sameLawPolicyDigest, sameProfileFingerprint, sameComponentFingerprints, sameLawSurfaceFingerprint, sameSiteCoverDigest })) {
      if (documents.comparison.comparability[field] !== undefined && documents.comparison.comparability[field] !== expected) comparisonConsistencyIssues.push(issue(`${FILES.comparison}.comparability.${field}`, `Comparison ${field} does not match its run digests.`, expected, documents.comparison.comparability[field]));
    }
    if (comparisonConsistencyIssues.length) throw new AnalysisValidationError("mismatch", comparisonConsistencyIssues);
    const compatibleSides = runs.map((run, position) => ({ run, side: position ? "head" : "base" })).filter(({ run }) => run.runId === documents.manifest.runId
      && run.toolVersion === documents.manifest.toolVersion
      && run.archmap?.sha256 === currentArchmapDigest
      && run.lawPolicy?.sha256 === documents.manifest.inputDigests.lawPolicy.sha256
      && run.profileFingerprint?.sha256 === documents.manifest.inputDigests.profileFingerprint.sha256
      && run.siteCoverDigest?.sha256 === documents.manifest.inputDigests.siteCoverDigest.sha256
      && canonicalJson(run.componentFingerprints) === canonicalJson(documents.manifest.componentFingerprints)
      && run.measurementPacket?.sha256 === packetDigest);
    if (!compatibleSides.length) throw new AnalysisValidationError("mismatch", [issue(`${FILES.comparison}.inputDigests`, "Comparison report does not bind either run to the loaded measurement run.")]);
    if (documents.gate && !compatibleSides.some(({ side }) => side === "head")) throw new AnalysisValidationError("mismatch", [issue(`${FILES.comparison}.inputDigests.headRun`, "A gate-bound comparison must bind its complete head run to the loaded measurement run.")]);
    comparisonSides = compatibleSides.map(({ side }) => side);
    const verdictByRef = new Map(documents.packet.structuralVerdict.map((row) => [row.verdictRef, row]));
    const verdictByKey = new Map(documents.packet.structuralVerdict.map((row) => [comparisonRowKey(row), row]));
    const transitionByKey = new Map(documents.comparison.verdictTransitions.map((row) => [row.rowKey, row]));
    const transitionIssues = [];
    compatibleSides.forEach(({ side }) => {
      verdictByKey.forEach((row, rowKey) => {
        const transition = transitionByKey.get(rowKey);
        if (!transition) transitionIssues.push(issue(`${FILES.comparison}.verdictTransitions`, `Comparison omits a ${side} structural verdict row from the loaded packet.`, rowKey, null));
        else if (transition[`${side}RowRef`] !== row.verdictRef) transitionIssues.push(issue(`${FILES.comparison}.verdictTransitions.${rowKey}.${side}RowRef`, `Comparison ${side} row ref does not match the loaded packet row key.`, row.verdictRef, transition[`${side}RowRef`]));
      });
    });
    if (compatibleSides.length === 2) documents.comparison.verdictTransitions.forEach((row, position) => {
      if (!verdictByKey.has(row.rowKey)) transitionIssues.push(issue(`${FILES.comparison}.verdictTransitions[${position}].rowKey`, "Comparison contains a row outside both loaded packet sides.", null, row.rowKey));
    });
    documents.comparison.verdictTransitions.forEach((transition, position) => {
      const path = `${FILES.comparison}.verdictTransitions[${position}]`;
      compatibleSides.forEach(({ side }) => {
        const rowRef = transition[`${side}RowRef`];
        const declaredVerdict = transition[`${side}Verdict`];
        if (rowRef === null || rowRef === undefined) {
          if (declaredVerdict !== "absent") transitionIssues.push(issue(`${path}.${side}Verdict`, `Comparison ${side} verdict must be absent when its row ref is absent.`, "absent", declaredVerdict));
          return;
        }
        const packetRow = verdictByRef.get(rowRef);
        if (!packetRow) transitionIssues.push(issue(`${path}.${side}RowRef`, `Comparison ${side} row does not identify a structural verdict in the loaded packet.`, null, rowRef));
        else if (packetRow.verdict !== declaredVerdict) transitionIssues.push(issue(`${path}.${side}Verdict`, `Comparison ${side} verdict does not match the loaded packet row.`, packetRow.verdict, declaredVerdict));
      });
      (transition.deltaRefs || []).forEach((delta, deltaPosition) => {
        const belongsToLoadedSide = compatibleSides.some(({ side }) => delta.op === "modified" || (side === "base" && delta.op === "removed") || (side === "head" && delta.op === "added"));
        if (belongsToLoadedSide && !resolves(delta.id, delta.kind, architectureIndex, bridges)) transitionIssues.push(issue(`${path}.deltaRefs[${deltaPosition}].id`, `Comparison delta does not resolve on the loaded run side.`, null, delta.id));
      });
    });
    if (transitionIssues.length) throw new AnalysisValidationError("mismatch", transitionIssues);
  }
  const comparisonDigest = documents.comparison ? await sha256Hex(documents.comparison) : null;
  const gateComparisonDigest = documents.gate?.inputDigests?.comparisonReport;
  if (documents.gate && documents.comparison) {
    if (!isRecord(gateComparisonDigest) || gateComparisonDigest.sha256 !== comparisonDigest) throw new AnalysisValidationError("mismatch", [issue(`${FILES.gate}.inputDigests.comparisonReport`, "Gate report comparison digest does not match the loaded comparison report.", comparisonDigest, gateComparisonDigest?.sha256)]);
    if (documents.comparison.inputDigests.headRun.measurementPacket.sha256 !== packetDigest) throw new AnalysisValidationError("mismatch", [issue(`${FILES.comparison}.inputDigests.headRun.measurementPacket.sha256`, "A gate-bound comparison must identify the loaded packet as its head run.", packetDigest, documents.comparison.inputDigests.headRun.measurementPacket.sha256)]);
  } else if (isRecord(gateComparisonDigest)) {
    throw new AnalysisValidationError("mismatch", [issue(`${FILES.gate}.inputDigests.comparisonReport`, "Gate report references a comparison report that was not loaded.")]);
  }
  if (documents.gate && documents.gate.decision !== "NOT_EVALUABLE") {
    const gateIssues = [];
    const verdictByRef = new Map(gateVerdictRows(documents.packet).map((row) => [row.verdictRef, row]));
    const transitionByKey = new Map((documents.comparison?.verdictTransitions || []).map((row) => [row.rowKey, row]));
    const violatedAssumptions = new Set((documents.packet.assumptions || []).filter((row) => row.status === "violated").map((row) => row.assumptionId));
    (documents.gate.ruleOutcomes || []).forEach((outcome, outcomePosition) => {
      if (outcome.status !== "evaluated") return;
      const mappings = outcome.appliedMapping || [];
      const path = `${FILES.gate}.ruleOutcomes[${outcomePosition}].appliedMapping`;
      const mappingIds = mappings.map((mapping) => outcome.scope === "absolute" ? mapping.rowRef : mapping.rowKey);
      if (new Set(mappingIds).size !== mappingIds.length) gateIssues.push(issue(path, "Gate outcome mappings must identify each row exactly once.", null, mappingIds));
      if (outcome.scope === "absolute" && mappings.length !== verdictByRef.size) gateIssues.push(issue(path, "An absolute gate outcome must map every producer gate row.", verdictByRef.size, mappings.length));
      if (outcome.scope === "introduced-by-change" && mappings.length !== transitionByKey.size) gateIssues.push(issue(path, "An introduced-by-change outcome must map every loaded comparison transition.", transitionByKey.size, mappings.length));
      mappings.forEach((mapping, mappingPosition) => {
        if (outcome.scope === "absolute") {
          const row = verdictByRef.get(mapping.rowRef);
          if (!row) gateIssues.push(issue(`${path}[${mappingPosition}].rowRef`, "Gate mapping does not identify a producer gate row.", null, mapping.rowRef));
          else if (mapping.verdict !== row.verdict) gateIssues.push(issue(`${path}[${mappingPosition}].verdict`, "Gate mapping verdict does not match its loaded structural verdict.", row.verdict, mapping.verdict));
          else {
            const expectedMappingKey = (row.dependsOnAssumptions || []).some((ref) => violatedAssumptions.has(ref)) ? "violated_assumption_dependency" : row.verdict;
            if (mapping.mappingKey !== expectedMappingKey) gateIssues.push(issue(`${path}[${mappingPosition}].mappingKey`, "Gate mapping key does not match the producer row classification.", expectedMappingKey, mapping.mappingKey));
          }
        } else if (outcome.scope === "introduced-by-change") {
          const transition = transitionByKey.get(mapping.rowKey);
          if (!transition) gateIssues.push(issue(`${path}[${mappingPosition}].rowKey`, "Gate mapping does not identify a loaded comparison transition.", null, mapping.rowKey));
          else {
            if (mapping.transition !== transition.transition) gateIssues.push(issue(`${path}[${mappingPosition}].transition`, "Gate mapping transition does not match the comparison report.", transition.transition, mapping.transition));
            if (mapping.mappingKey !== transition.introducedByChangeCategory) gateIssues.push(issue(`${path}[${mappingPosition}].mappingKey`, "Gate mapping key does not match the comparison category.", transition.introducedByChangeCategory, mapping.mappingKey));
          }
        }
      });
    });
    if (gateIssues.length) throw new AnalysisValidationError("mismatch", gateIssues);
  }
  const acceptedBridges = Object.freeze(Object.fromEntries(Object.entries(bridges).map(([kind, map]) => [kind, readonlyMap(map)])));
  return deepFreeze({
    runId: documents.manifest.runId,
    toolVersion: documents.manifest.toolVersion,
    profileRef: documents.summary.profileRef,
    archmapDigest: currentArchmapDigest,
    packetDigest,
    comparisonSides,
    bridges: acceptedBridges,
    artifacts: Object.fromEntries(Object.entries(documents).filter(([, value]) => value !== undefined)),
  });
}

function parseDocument(text, filename) {
  try {
    let position = 0;
    const whitespace = () => { while (/\s/.test(text[position] || "")) position += 1; };
    const stringToken = () => {
      const start = position;
      if (text[position++] !== '"') throw new SyntaxError(`Expected string at ${start}`);
      while (position < text.length) {
        if (text[position] === "\\") { position += 2; continue; }
        if (text[position++] === '"') {
          const token = text.slice(start, position);
          return { value: JSON.parse(token), canonical: JSON.stringify(JSON.parse(token)) };
        }
      }
      throw new SyntaxError(`Unterminated string at ${start}`);
    };
    const scan = () => {
      whitespace();
      if (text[position] === "{") {
        position += 1;
        const rows = [];
        const keys = new Set();
        whitespace();
        if (text[position] === "}") { position += 1; return "{}"; }
        while (true) {
          whitespace();
          const key = stringToken();
          if (keys.has(key.value)) throw new SyntaxError(`Duplicate object key ${key.value}`);
          keys.add(key.value);
          whitespace();
          if (text[position++] !== ":") throw new SyntaxError(`Expected colon at ${position - 1}`);
          rows.push([key.canonical, scan()]);
          whitespace();
          const separator = text[position++];
          if (separator === "}") break;
          if (separator !== ",") throw new SyntaxError(`Expected comma at ${position - 1}`);
        }
        rows.sort((left, right) => left[0] < right[0] ? -1 : left[0] > right[0] ? 1 : 0);
        return `{${rows.map(([key, value]) => `${key}:${value}`).join(",")}}`;
      }
      if (text[position] === "[") {
        position += 1;
        const values = [];
        whitespace();
        if (text[position] === "]") { position += 1; return "[]"; }
        while (true) {
          values.push(scan());
          whitespace();
          const separator = text[position++];
          if (separator === "]") break;
          if (separator !== ",") throw new SyntaxError(`Expected comma at ${position - 1}`);
        }
        return `[${values.join(",")}]`;
      }
      if (text[position] === '"') return stringToken().canonical;
      const primitive = text.slice(position).match(/^(?:-?(?:0|[1-9][0-9]*)(?:\.[0-9]+)?(?:[eE][+-]?[0-9]+)?|true|false|null)/)?.[0];
      if (!primitive) throw new SyntaxError(`Invalid value at ${position}`);
      position += primitive.length;
      if (!/^-?[0-9]/.test(primitive)) return primitive;
      if (!/[.eE]/.test(primitive)) {
        const integer = BigInt(primitive);
        if (integer > BigInt(Number.MAX_SAFE_INTEGER) || integer < BigInt(Number.MIN_SAFE_INTEGER)) throw new SyntaxError(`Integer outside the browser's exact range at ${position - primitive.length}`);
        return integer.toString();
      }
      const number = Number(primitive);
      if (!Number.isFinite(number)) throw new SyntaxError(`Non-finite number at ${position - primitive.length}`);
      if (Object.is(number, -0)) return "-0.0";
      if (number === 0) return "0.0";
      const exponent = Math.floor(Math.log10(Math.abs(number)));
      if (exponent >= -5 && exponent <= 15) {
        const fixed = number.toString();
        return Number.isInteger(number) ? `${fixed}.0` : fixed;
      }
      return number.toExponential().replace(/e([+-])0+([0-9])/, "e$1$2");
    };
    const canonical = scan();
    whitespace();
    if (position !== text.length) throw new SyntaxError(`Unexpected input at ${position}`);
    const document = JSON.parse(text);
    if (isRecord(document) || Array.isArray(document)) RAW_CANONICAL.set(document, canonical);
    return document;
  } catch (error) { throw new AnalysisValidationError("malformed", [issue(filename, `${filename} is not valid JSON: ${error.message}`)]); }
}

export async function documentsFromFiles(fileList) {
  const byName = new Map();
  let selectedDirectory = null;
  for (const file of fileList) {
    const relativePath = file.webkitRelativePath || file.name;
    const parts = relativePath.split("/");
    const directory = parts.slice(0, -1).join("/");
    if (Object.values(FILES).includes(file.name)) {
      if (selectedDirectory === null) selectedDirectory = directory;
      else if (directory !== selectedDirectory) throw new AnalysisValidationError("malformed", [issue(file.name, "ArchSig artifacts must come from one run directory.", selectedDirectory, directory)]);
    }
    const depth = parts.length;
    const current = byName.get(file.name);
    if (!current || depth < current.depth) byName.set(file.name, { file, depth });
    else if (depth === current.depth) throw new AnalysisValidationError("malformed", [issue(file.name, `${file.name} occurs more than once at the run-directory level.`)]);
  }
  const documents = {};
  for (const [name, filename] of Object.entries(FILES)) {
    const selected = byName.get(filename);
    if (selected) documents[name] = parseDocument(await selected.file.text(), filename);
  }
  return documents;
}

export async function documentsFromUrl(directoryUrl) {
  const base = directoryUrl.endsWith("/") ? directoryUrl : `${directoryUrl}/`;
  const documents = {};
  for (const [name, filename] of Object.entries(FILES)) {
    const requestedUrl = new URL(filename, base);
    const response = await fetch(requestedUrl, { headers: { Accept: "application/json" } });
    if (response.redirected || response.url !== requestedUrl.href) throw new AnalysisValidationError("mismatch", [issue(filename, `${filename} must not redirect outside the selected run directory.`, requestedUrl.href, response.url)]);
    if (!response.ok) {
      if (!REQUIRED.includes(name) && response.status === 404) continue;
      throw new AnalysisValidationError("malformed", [issue(filename, `${filename} request failed with HTTP ${response.status}.`)]);
    }
    documents[name] = parseDocument(await response.text(), filename);
  }
  return documents;
}

export { FILES as ANALYSIS_FILES };

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
  if (Array.isArray(value)) return `[${value.map(canonicalJson).join(",")}]`;
  if (isRecord(value)) {
    return `{${Object.keys(value).sort().map((key) => `${JSON.stringify(key)}:${canonicalJson(value[key])}`).join(",")}}`;
  }
  return JSON.stringify(value);
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
  return Object.freeze({
    atoms: bridgeRows(normalized.atoms, "sourceAtomId", "normalizedAtomId", index.atomsById, FILES.normalized, issues),
    contexts: bridgeRows(normalized.contexts, "sourceContextId", "normalizedContextId", index.contextsById, FILES.normalized, issues),
    covers: bridgeRows(normalized.covers, "sourceCoverId", "normalizedCoverId", index.coversById, FILES.normalized, issues),
  });
}

const REF_FIELDS = Object.freeze({
  atomRefs: "atoms", supportAtomRefs: "atoms", mismatchSupportRefs: "atoms", sharedAtomRefs: "atoms", pairingAtomRefs: "atoms",
  contextRefs: "contexts", sourceRefs: "sources", coverRefs: "covers",
});
const SINGLE_REF_FIELDS = Object.freeze({
  atomRef: "atoms", supportAtomRef: "atoms", contextRef: "contexts",
  sourceContextRef: "contexts", targetContextRef: "contexts", coverRef: "covers", selectedCoverRef: "covers",
});

function resolves(ref, kind, index, bridges) {
  const rawMap = kind === "sources" ? index.sourcesById : index[`${kind}ById`];
  return rawMap.has(ref) || bridges[kind]?.has(ref);
}

function collectUnresolved(value, path, index, bridges, unresolved) {
  if (Array.isArray(value)) return value.forEach((entry, position) => collectUnresolved(entry, `${path}[${position}]`, index, bridges, unresolved));
  if (!isRecord(value)) return;
  for (const [key, child] of Object.entries(value)) {
    const childPath = `${path}.${key}`;
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
    requireRecord(documents.gate.inputDigests, `${FILES.gate}.inputDigests`, issues);
    requireDigestEntry(documents.gate.inputDigests?.measurementPacket, `${FILES.gate}.inputDigests.measurementPacket`, issues);
    requireDigestEntry(documents.gate.inputDigests?.gatePolicy, `${FILES.gate}.inputDigests.gatePolicy`, issues);
    for (const field of ["policyValidation", "ruleOutcomes", "nonConclusions"]) requireArray(documents.gate[field], `${FILES.gate}.${field}`, issues);
  }
  if (isRecord(documents.comparison)) {
    requireString(documents.comparison.toolVersion, `${FILES.comparison}.toolVersion`, issues);
    if (requireRecord(documents.comparison.inputDigests, `${FILES.comparison}.inputDigests`, issues)) {
      requireRecord(documents.comparison.inputDigests.baseRun, `${FILES.comparison}.inputDigests.baseRun`, issues);
      requireRecord(documents.comparison.inputDigests.headRun, `${FILES.comparison}.inputDigests.headRun`, issues);
    }
    requireRecord(documents.comparison.comparability, `${FILES.comparison}.comparability`, issues);
    requireString(documents.comparison.discipline, `${FILES.comparison}.discipline`, issues);
    requireRecord(documents.comparison.artifactRefs, `${FILES.comparison}.artifactRefs`, issues);
    requireRecord(documents.comparison.independentConclusions, `${FILES.comparison}.independentConclusions`, issues);
    requireArray(documents.comparison.verdictTransitions, `${FILES.comparison}.verdictTransitions`, issues);
    requireArray(documents.comparison.boundaryStatements, `${FILES.comparison}.boundaryStatements`, issues);
    requireRecord(documents.comparison.classTransport, `${FILES.comparison}.classTransport`, issues);
    requireArray(documents.comparison.nonConclusions, `${FILES.comparison}.nonConclusions`, issues);
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
  if (documents.comparison) {
    const runs = [documents.comparison.inputDigests?.baseRun, documents.comparison.inputDigests?.headRun].filter(isRecord);
    const comparisonShapeIssues = [];
    runs.forEach((run, position) => validateComparisonRun(run, `${FILES.comparison}.inputDigests.${position ? "headRun" : "baseRun"}`, comparisonShapeIssues));
    if (comparisonShapeIssues.length) throw new AnalysisValidationError("malformed", comparisonShapeIssues);
    const compatible = runs.some((run) => run.runId === documents.manifest.runId && run.archmap?.sha256 === currentArchmapDigest && run.measurementPacket?.sha256 === packetDigest);
    if (!compatible) throw new AnalysisValidationError("mismatch", [issue(`${FILES.comparison}.inputDigests`, "Comparison report does not bind either run to the loaded measurement run.")]);
  }
  const comparisonDigest = documents.comparison ? await sha256Hex(documents.comparison) : null;
  const gateComparisonDigest = documents.gate?.inputDigests?.comparisonReport;
  if (documents.gate && documents.comparison) {
    if (!isRecord(gateComparisonDigest) || gateComparisonDigest.sha256 !== comparisonDigest) throw new AnalysisValidationError("mismatch", [issue(`${FILES.gate}.inputDigests.comparisonReport`, "Gate report comparison digest does not match the loaded comparison report.", comparisonDigest, gateComparisonDigest?.sha256)]);
  } else if (isRecord(gateComparisonDigest)) {
    throw new AnalysisValidationError("mismatch", [issue(`${FILES.gate}.inputDigests.comparisonReport`, "Gate report references a comparison report that was not loaded.")]);
  }
  return Object.freeze({
    runId: documents.manifest.runId,
    toolVersion: documents.manifest.toolVersion,
    profileRef: documents.summary.profileRef,
    archmapDigest: currentArchmapDigest,
    packetDigest,
    bridges,
    artifacts: Object.freeze(Object.fromEntries(Object.entries(documents).filter(([, value]) => value !== undefined))),
  });
}

function parseDocument(text, filename) {
  try { return JSON.parse(text); }
  catch (error) { throw new AnalysisValidationError("malformed", [issue(filename, `${filename} is not valid JSON: ${error.message}`)]); }
}

export async function documentsFromFiles(fileList) {
  const byName = new Map();
  for (const file of fileList) {
    const depth = (file.webkitRelativePath || file.name).split("/").length;
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

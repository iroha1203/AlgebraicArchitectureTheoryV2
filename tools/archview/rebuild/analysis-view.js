function isRecord(value) {
  return value !== null && typeof value === "object" && !Array.isArray(value);
}

function unique(values) {
  return [...new Set(values.filter((value) => typeof value === "string" && value.length))].sort();
}

function rawRef(ref, kind, bridges) {
  return bridges?.[kind]?.get(ref) || ref;
}

function resolveRefs(refs, kind, index, bridges) {
  const map = index[`${kind}ById`];
  return unique((refs || []).map((ref) => rawRef(ref, kind, bridges)).filter((ref) => map.has(ref)));
}

function verdictState(rows) {
  const verdicts = rows.map((row) => row.verdict);
  if (verdicts.includes("measured_nonzero")) return "measured_nonzero";
  if (verdicts.includes("measured_zero")) return "measured_zero";
  if (verdicts.includes("unknown")) return "unknown";
  if (verdicts.includes("not_computed")) return "not_computed";
  return verdicts.includes("unmeasured") ? "unmeasured" : "informational";
}

function stateLabel(state) {
  return ({
    measured_nonzero: "Measured nonzero",
    measured_zero: "Measured zero",
    unmeasured: "Unmeasured",
    unknown: "Unknown",
    not_computed: "Not computed",
    informational: "Inspection finding",
  })[state];
}

function sourceLanding(index, sourceId) {
  const origin = index.sourcesById.get(sourceId);
  if (!origin) return { sourceId, path: null, symbol: null, line: null, resolution: "UNRESOLVED" };
  let current = origin;
  let path = current.path || null;
  const seen = new Set([sourceId]);
  while (!path && current.source && index.sourcesById.has(current.source) && !seen.has(current.source)) {
    seen.add(current.source);
    current = index.sourcesById.get(current.source);
    path = current.path || null;
  }
  const symbol = origin.symbol || current.symbol || origin.section || current.section || null;
  const method = origin.method || current.method || null;
  const line = origin.line ?? current.line ?? null;
  const resolution = path && method ? "METHOD LEVEL" : path && symbol && line !== null ? "SYMBOL + LINE LEVEL — METHOD GRANULARITY UNAVAILABLE" : path && symbol ? "SYMBOL LEVEL — METHOD GRANULARITY UNAVAILABLE" : path && line !== null ? "LINE LEVEL — METHOD GRANULARITY UNAVAILABLE" : path ? "FILE LEVEL — METHOD GRANULARITY UNAVAILABLE" : "UNRESOLVED";
  return { sourceId, path, symbol: method || symbol, line, resolution };
}

function explicitRepairAtomRefs(card, index, bridges) {
  const rows = [card.nextAction].filter(isRecord).filter((row) => row.kind === "repair_candidate");
  return resolveRefs(rows.flatMap((row) => row.targetRefs || row.atomRefs || []), "atoms", index, bridges);
}

function boundaryContextRefs(edgeRefs, index, bridges) {
  const refs = [];
  for (const edge of edgeRefs) {
    const match = edge.match(/^(ctx:[^>]+)->(ctx:.+)$/);
    if (match) refs.push(rawRef(match[1], "contexts", bridges), rawRef(match[2], "contexts", bridges));
  }
  return unique(refs.filter((ref) => index.contextsById.has(ref)));
}

function normalizedEdges(edgeRefs, index, bridges) {
  return unique(edgeRefs.map((edge) => {
    const match = edge.match(/^(ctx:[^>]+)->(ctx:.+)$/);
    if (!match) return null;
    const source = rawRef(match[1], "contexts", bridges);
    const target = rawRef(match[2], "contexts", bridges);
    return index.contextsById.get(source)?.restrictsTo?.includes(target) ? `${source}->${target}` : null;
  }));
}

function collectRelationEvidence(invariants, index, bridges) {
  const output = { relation: [], agreement: [], mismatch: [], unmeasured: [] };
  const projections = (invariant) => [invariant.coverNerveProjection, invariant.representation?.coverNerveProjection].filter(isRecord);
  for (const invariant of invariants) {
    for (const projection of projections(invariant)) {
      for (const row of projection.edges || []) {
        const [edge] = normalizedEdges([row?.edgeId], index, bridges);
        if (!edge) continue;
        output.relation.push(edge);
        if (row.sectionObservation === "not_observed") output.unmeasured.push(edge);
        else if (row.sectionObservation === "observed" && (row.value === 0 || row.value === "0")) output.agreement.push(edge);
        else if (row.sectionObservation === "observed" && (row.value === 1 || row.value === "1")) output.mismatch.push(edge);
      }
      for (const face of projection.faces || []) output.relation.push(...normalizedEdges(face?.edgeRefs || [], index, bridges));
    }
    for (const classSupport of [invariant.classSupport, invariant.representation?.classSupport].filter(isRecord)) {
      const edges = normalizedEdges(classSupport.edgeRefs || [], index, bridges);
      output.relation.push(...edges);
      output.mismatch.push(...edges);
    }
    for (const refs of [invariant.unobservedEdgeRefs, invariant.representation?.unobservedEdgeRefs]) {
      const edges = normalizedEdges(refs || [], index, bridges);
      output.relation.push(...edges);
      output.unmeasured.push(...edges);
    }
  }
  return output;
}

function classifiedTargets({ directSourceRefs, supportAtomIds, boundaryContextIds, repairAtomIds, validatedAtomIds }, index) {
  const records = [];
  const add = (classification, sourceId, atomId = null, contextId = null) => {
    if (!index.sourcesById.has(sourceId)) return;
    const key = `${classification}|${sourceId}|${atomId || ""}|${contextId || ""}`;
    if (records.some((record) => record.key === key)) return;
    records.push({ key, classification, sourceId, atomId, contextId, ...sourceLanding(index, sourceId) });
  };
  directSourceRefs.forEach((sourceId) => add("DIRECT EVIDENCE", sourceId));
  supportAtomIds.forEach((atomId) => (index.atomsById.get(atomId)?.refs || []).forEach((sourceId) => add("DIRECT EVIDENCE", sourceId, atomId)));
  boundaryContextIds.forEach((contextId) => (index.contextsById.get(contextId)?.refs || []).forEach((sourceId) => add("BOUNDARY PARTICIPANT", sourceId, null, contextId)));
  repairAtomIds.forEach((atomId) => (index.atomsById.get(atomId)?.refs || []).forEach((sourceId) => add(validatedAtomIds.includes(atomId) ? "VALIDATED IN HYPOTHETICAL TARGET" : "CANDIDATE CHANGE POINT", sourceId, atomId)));
  return records.sort((left, right) => `${left.classification}|${left.path || ""}|${left.symbol || ""}|${left.line ?? ""}|${left.sourceId}`.localeCompare(`${right.classification}|${right.path || ""}|${right.symbol || ""}|${right.line ?? ""}|${right.sourceId}`));
}

function buildFinding(card, position, bundle, index) {
  const packet = bundle.artifacts.packet;
  const insight = bundle.artifacts.insight;
  const evidence = isRecord(card.evidence) ? card.evidence : {};
  const verdictByRef = new Map(packet.structuralVerdict.map((row) => [row.verdictRef, row]));
  const verdictRows = (evidence.structuralVerdictRefs || []).map((ref) => verdictByRef.get(ref)).filter(Boolean);
  const effectiveRows = verdictRows;
  const state = verdictState(effectiveRows);
  const bridges = bundle.bridges;
  const supportAtomIds = resolveRefs(evidence.atomRefs || [], "atoms", index, bridges);
  const supportContextIds = unique([
    ...resolveRefs(evidence.contextRefs || [], "contexts", index, bridges),
    ...supportAtomIds.flatMap((atomId) => index.contextIdsByAtom.get(atomId) || []),
  ]);
  const supportCoverIds = resolveRefs(evidence.coverRefs || [], "covers", index, bridges);
  const directSourceRefs = resolveRefs(evidence.sourceRefs || [], "sources", index, bridges);
  const rowInvariantRefs = new Set(verdictRows.flatMap((row) => row.evidence?.computedInvariantRefs || []));
  const invariantRefs = new Set((evidence.computedInvariantRefs || []).filter((ref) => !verdictRows.length || rowInvariantRefs.has(ref)));
  const invariants = packet.computedInvariants.filter((row) => invariantRefs.has(row.invariantId));
  const relationEvidence = collectRelationEvidence(invariants, index, bridges);
  const relationRefs = unique(relationEvidence.relation);
  const unobservedEdgeRefs = unique(relationEvidence.unmeasured);
  const mismatchEdgeRefs = unique(relationEvidence.mismatch).filter((edge) => !unobservedEdgeRefs.includes(edge));
  const agreementEdgeRefs = unique(relationEvidence.agreement).filter((edge) => !unobservedEdgeRefs.includes(edge) && !mismatchEdgeRefs.includes(edge));
  const edgeRefs = relationRefs.filter((edge) => !unobservedEdgeRefs.includes(edge));
  const boundaryContextIds = boundaryContextRefs(mismatchEdgeRefs, index, bridges);
  const repairAtomIds = explicitRepairAtomRefs(card, index, bridges);
  const validatedAtomIds = [];
  const validated = false;
  const sourceTargets = classifiedTargets({ directSourceRefs, supportAtomIds, boundaryContextIds, repairAtomIds, validatedAtomIds }, index);
  const unmeasuredRows = effectiveRows.filter((row) => ["unmeasured", "unknown", "not_computed"].includes(row.verdict));
  return Object.freeze({
    id: card.id || `finding:${position + 1}`,
    artifactPath: `archsig-insight-report.json#/insightCards/${position}`,
    title: card.title || card.oneLine || `Finding ${position + 1}`,
    summary: card.oneLine || card.whyItMatters || "ArchSig supplied an inspection finding.",
    state,
    stateLabel: stateLabel(state),
    conclusionCode: bundle.artifacts.summary.conclusion,
    supportAtomIds: Object.freeze(supportAtomIds),
    supportContextIds: Object.freeze(supportContextIds),
    supportCoverIds: Object.freeze(supportCoverIds),
    edgeRefs: Object.freeze(edgeRefs),
    agreementEdgeRefs: Object.freeze(agreementEdgeRefs),
    mismatchEdgeRefs: Object.freeze(mismatchEdgeRefs),
    unobservedEdgeRefs: Object.freeze(unobservedEdgeRefs),
    relationRefs: Object.freeze(relationRefs),
    boundaryContextIds: Object.freeze(boundaryContextIds),
    directSourceRefs: Object.freeze(directSourceRefs),
    repairAtomIds: Object.freeze(repairAtomIds),
    validatedAtomIds: Object.freeze(validatedAtomIds),
    validated,
    unmeasuredRows: Object.freeze(unmeasuredRows),
    sourceTargets: Object.freeze(sourceTargets.map(Object.freeze)),
    localFacts: Object.freeze(supportAtomIds.map((atomId) => index.atomsById.get(atomId)).filter(Boolean).map((atom) => Object.freeze({ atomId: atom.id, fact: [atom.subject, atom.predicate, atom.object].filter(Boolean).join(" "), contexts: Object.freeze(index.contextIdsByAtom.get(atom.id) || []) }))),
  });
}

export function buildAnalysisView(bundle, index) {
  if (!bundle || !index) return Object.freeze({ findings: Object.freeze([]), gate: null, comparison: null });
  const insight = bundle.artifacts.insight;
  const cards = insight.insightCards || [];
  const findings = cards.map((card, position) => buildFinding(card, position, bundle, index));
  return Object.freeze({
    findings: Object.freeze(findings),
    gate: bundle.artifacts.gate ? Object.freeze({ decision: bundle.artifacts.gate.decision, blocked: bundle.artifacts.gate.decision === "BLOCKED_BY_GATE_POLICY", evaluable: bundle.artifacts.gate.decision !== "NOT_EVALUABLE" }) : null,
    comparison: bundle.artifacts.comparison ? Object.freeze({ conclusionCode: bundle.artifacts.comparison.conclusionCode || null, transitions: Object.freeze(bundle.artifacts.comparison.verdictTransitions || []) }) : null,
  });
}

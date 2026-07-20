function byId(left, right) {
  return left.id.localeCompare(right.id);
}

function freezePoint(x, y, z) {
  return Object.freeze({ x, y, z });
}

function restrictionDepths(contexts, contextIds) {
  const memo = new Map();
  const depthOf = (contextId, trail = new Set()) => {
    if (memo.has(contextId)) return memo.get(contextId);
    if (trail.has(contextId)) return 0;
    const context = contexts.get(contextId);
    const targets = [...new Set(context?.restrictsTo || [])].filter((target) => contextIds.has(target)).sort();
    const depth = targets.length ? 1 + Math.max(...targets.map((target) => depthOf(target, new Set(trail).add(contextId)))) : 0;
    memo.set(contextId, depth);
    return depth;
  };
  for (const contextId of [...contextIds].sort()) depthOf(contextId);
  return memo;
}

function subjectGroups(index, context) {
  const groups = new Map();
  for (const atomId of new Set(context.atoms || [])) {
    const atom = index.atomsById.get(atomId);
    if (!atom) continue;
    const atoms = groups.get(atom.subject) || [];
    atoms.push(atom);
    groups.set(atom.subject, atoms);
  }
  return [...groups]
    .sort(([left], [right]) => left.localeCompare(right))
    .map(([subject, atoms]) => Object.freeze({ subject, atoms: Object.freeze([...atoms].sort(byId)) }));
}

export function buildArchitectureLayout(index, coverId = null) {
  if (!index || index.empty) {
    return Object.freeze({ coverId: null, contexts: Object.freeze([]), subjects: Object.freeze([]), atoms: Object.freeze([]), restrictions: Object.freeze([]), sharedSupports: Object.freeze([]), signature: "empty" });
  }

  const cover = index.coversById.get(coverId) || index.covers[0] || null;
  if (!cover) {
    return Object.freeze({ coverId: null, contexts: Object.freeze([]), subjects: Object.freeze([]), atoms: Object.freeze([]), restrictions: Object.freeze([]), sharedSupports: Object.freeze([]), signature: "no-cover" });
  }
  const contextIds = new Set((cover.contexts || []).filter((id) => index.contextsById.has(id)));
  const contexts = index.contexts.filter((context) => contextIds.has(context.id));
  const depths = restrictionDepths(index.contextsById, contextIds);
  const rowsByDepth = new Map();
  for (const context of contexts) {
    const depth = depths.get(context.id) || 0;
    const row = rowsByDepth.get(depth) || [];
    row.push(context);
    rowsByDepth.set(depth, row);
  }
  for (const row of rowsByDepth.values()) row.sort(byId);

  const contextLayouts = [];
  const subjectLayouts = [];
  const atomLayouts = [];
  const contextPosition = new Map();
  const sortedDepths = [...rowsByDepth.keys()].sort((left, right) => right - left);
  for (const depth of sortedDepths) {
    const row = rowsByDepth.get(depth);
    row.forEach((context, rowIndex) => {
      const groups = subjectGroups(index, context);
      const atomCount = groups.reduce((sum, group) => sum + group.atoms.length, 0);
      const area = 34 + atomCount * 8;
      const width = Math.sqrt(area * 1.35);
      const height = area / width;
      const position = freezePoint((depth - (sortedDepths.length - 1) / 2) * -10.5, 0.08, (rowIndex - (row.length - 1) / 2) * 10.2);
      contextPosition.set(context.id, position);
      contextLayouts.push(Object.freeze({ id: context.id, label: context.label || context.id, depth, atomCount, sourceCount: new Set((context.refs || []).filter((ref) => index.sourcesById.has(ref))).size, width, height, position }));

      groups.forEach((group, groupIndex) => {
        const groupX = position.x + (groupIndex - (groups.length - 1) / 2) * 2.25;
        const subjectPosition = freezePoint(groupX, 0.34, position.z);
        subjectLayouts.push(Object.freeze({ id: `${context.id}::${group.subject}`, contextId: context.id, subject: group.subject, atomIds: Object.freeze(group.atoms.map((atom) => atom.id)), position: subjectPosition }));
        group.atoms.forEach((atom, atomIndex) => {
          atomLayouts.push(Object.freeze({
            id: `${context.id}::${atom.id}`,
            contextId: context.id,
            subject: atom.subject,
            atomId: atom.id,
            kind: atom.kind,
            position: freezePoint(groupX, 0.76, position.z + (atomIndex - (group.atoms.length - 1) / 2) * 1.25),
          }));
        });
      });
    });
  }

  const restrictions = contexts.flatMap((context) => [...new Set(context.restrictsTo || [])]
    .filter((targetId) => contextIds.has(targetId))
    .sort()
    .map((targetId) => Object.freeze({ id: `${context.id}->${targetId}`, sourceId: context.id, targetId, source: contextPosition.get(context.id), target: contextPosition.get(targetId) })));

  const memberships = new Map();
  for (const context of contexts) {
    for (const atomId of new Set(context.atoms || [])) {
      if (!index.atomsById.has(atomId)) continue;
      const values = memberships.get(atomId) || [];
      values.push(context.id);
      memberships.set(atomId, values);
    }
  }
  const sharedSupports = [...memberships]
    .filter(([, values]) => values.length > 1)
    .sort(([left], [right]) => left.localeCompare(right))
    .map(([atomId, values]) => {
      const contextIdsForAtom = [...values].sort();
      const points = contextIdsForAtom.map((id) => contextPosition.get(id));
      const position = freezePoint(
        points.reduce((sum, point) => sum + point.x, 0) / points.length,
        0.22,
        points.reduce((sum, point) => sum + point.z, 0) / points.length
      );
      return Object.freeze({ id: `shared::${atomId}`, atomId, contextIds: Object.freeze(contextIdsForAtom), position });
    });

  contextLayouts.sort(byId);
  subjectLayouts.sort(byId);
  atomLayouts.sort(byId);
  restrictions.sort(byId);
  const signature = JSON.stringify({
    coverId: cover?.id || null,
    contexts: contextLayouts.map(({ id, depth, atomCount, sourceCount, width, height, position }) => ({ id, depth, atomCount, sourceCount, width, height, position })),
    subjects: subjectLayouts.map(({ id, position, atomIds }) => ({ id, position, atomIds })),
    atoms: atomLayouts.map(({ id, atomId, kind, position }) => ({ id, atomId, kind, position })),
    restrictions: restrictions.map(({ id }) => id),
    sharedSupports: sharedSupports.map(({ atomId, contextIds, position }) => ({ atomId, contextIds, position })),
  });
  return Object.freeze({
    coverId: cover?.id || null,
    contexts: Object.freeze(contextLayouts),
    subjects: Object.freeze(subjectLayouts),
    atoms: Object.freeze(atomLayouts),
    restrictions: Object.freeze(restrictions),
    sharedSupports: Object.freeze(sharedSupports),
    signature,
  });
}

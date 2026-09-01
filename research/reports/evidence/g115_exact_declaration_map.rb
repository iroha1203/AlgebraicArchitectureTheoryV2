require 'digest'

unless ARGV.length == 2
  warn 'usage: g115_exact_declaration_map.rb REPORT REPO_ROOT'
  exit 2
end
report_path = ARGV.fetch(0)
repo_root = ARGV.fetch(1)
report = File.read(report_path)

occurrences = []
all_targets = []
cycle_records = []
claim_records = []
provenance_records = []

sections = report.split(/^## Cycle /).drop(1)
expected_cycles = (1..83).to_a - [28, 65]
accepted_sections = sections.select { |section| section[/\A(\d+)/, 1].to_i <= 83 }
cycle_numbers = accepted_sections.map { |section| section[/\A(\d+)/, 1]&.to_i }
unless cycle_numbers == expected_cycles
  warn "accepted-cycle manifest mismatch; expected #{expected_cycles.join(',')}; " \
    "got #{cycle_numbers.compact.join(',')}"
  exit 1
end

accepted_sections.each do |section|
  cycle = section[/\A(\d+)/, 1].to_i
  target_entries = section.scan(/^  lean_targets: \[(.*)\]$/).flat_map do |match|
    match.first.empty? ? [] : match.first.split(',', -1).map(&:strip)
  end
  invalid_targets = target_entries.reject do |path|
    path.end_with?('.lean') && path.match?(/\A[A-Za-z0-9_.'\/-]+\z/)
  end
  unless invalid_targets.empty?
    warn "invalid lean_targets cycle=#{cycle} #{invalid_targets.join('|')}"
    exit 1
  end
  targets = target_entries.map do |path|
    path.start_with?('research/', 'Formal/') ? path : "research/lean/#{path}"
  end
  artifacts = section.scan(/^  lean_artifacts: \[(.*)\]$/).flat_map do |match|
    match.first.empty? ? [] : match.first.split(',', -1).map(&:strip)
  end
  invalid_artifacts = artifacts.reject do |name|
    name.match?(/\A[A-Za-z_][A-Za-z0-9_'.]*\z/)
  end
  unless invalid_artifacts.empty?
    warn "invalid lean_artifacts cycle=#{cycle} #{invalid_artifacts.join('|')}"
    exit 1
  end
  section.scan(/^    (theorem_names|principal_theorem_names): \[(.*)\]$/).each do |field, body|
    entries = body.empty? ? [] : body.split(',', -1).map(&:strip)
    invalid_claims = entries.reject do |name|
      name.start_with?('planned ') || name.match?(/\A[A-Za-z_][A-Za-z0-9_'.]*\z/)
    end
    unless invalid_claims.empty?
      warn "invalid #{field} cycle=#{cycle} #{invalid_claims.join('|')}"
      exit 1
    end
    entries.each { |name| claim_records << [cycle, field, name] }
  end
  lines = section.lines
  lines.each_with_index do |line, index|
    match = line.match(/\A(\s+)(source_sha256|validation_refs):/)
    next unless match

    indent = match[1].length
    block = [line.strip]
    cursor = index + 1
    while cursor < lines.length
      child = lines[cursor]
      break unless child.strip.empty? || child[/\A\s*/].length > indent

      block << child.strip unless child.strip.empty?
      cursor += 1
    end
    provenance_records << [cycle, match[2], block.join('|')]
  end
  all_targets.concat(targets)
  artifacts.each { |name| occurrences << [cycle, name, targets] }
  cycle_records << [cycle, targets, artifacts]
end

all_targets.uniq!
manifest = cycle_records.map do |cycle, targets, artifacts|
  "cycle=#{cycle}\ntargets=#{targets.join('|')}\nartifacts=#{artifacts.join('|')}"
end.join("\n---\n")
manifest_sha256 = Digest::SHA256.hexdigest(manifest)
expected_manifest_sha256 = '2b31e4c59f8e58c96ad6b8dcc3aa18879608c13127d1ef0a874a82a625524c44'
unless manifest_sha256 == expected_manifest_sha256 &&
    occurrences.length == 1066 &&
    occurrences.map { |_cycle, name, _targets| name }.uniq.length == 1063 &&
    all_targets.length == 80
  warn "input manifest mismatch sha256=#{manifest_sha256} occurrences=#{occurrences.length} " \
    "identities=#{occurrences.map { |_cycle, name, _targets| name }.uniq.length} " \
    "targets=#{all_targets.length}"
  exit 1
end
claim_manifest = claim_records.map do |cycle, field, name|
  "cycle=#{cycle}|field=#{field}|name=#{name}"
end.join("\n")
claim_manifest_sha256 = Digest::SHA256.hexdigest(claim_manifest)
expected_claim_manifest_sha256 = '19ace3fad97e92c04fee690cf9a9ea6913157320158046055a68c04ae51eda30'
unless claim_manifest_sha256 == expected_claim_manifest_sha256
  warn "claim manifest mismatch sha256=#{claim_manifest_sha256} entries=#{claim_records.length}"
  exit 1
end
provenance_manifest = provenance_records.map do |cycle, field, value|
  "cycle=#{cycle}|field=#{field}|value=#{value}"
end.join("\n")
provenance_manifest_sha256 = Digest::SHA256.hexdigest(provenance_manifest)
expected_provenance_manifest_sha256 = 'de6c74feeec5e51e1dcb266c3fdc696750d77339143c58024b6043d44633a661'
unless provenance_manifest_sha256 == expected_provenance_manifest_sha256
  warn "provenance manifest mismatch sha256=#{provenance_manifest_sha256} records=#{provenance_records.length}"
  exit 1
end
file_text = {}
all_targets.each { |path| file_text[path] = File.read(File.join(repo_root, path)) }

ROOT_NAMESPACE = 'AAT.AG.DoctrineFiberProduct'

def lean_code_only(text)
  bytes = text.bytes
  output = Array.new(bytes.length, 32)
  index = 0
  state = :code
  block_depth = 0
  raw_hash_count = nil

  while index < bytes.length
    byte = bytes[index]
    pair = bytes[index, 2]
    triple = bytes[index, 3]
    case state
    when :code
      if pair == [47, 45] # /-
        block_depth = 1
        state = :block_comment
        index += 2
      elsif pair == [45, 45] # --
        state = :line_comment
        index += 2
      elsif byte == 114 # r followed by zero or more # and a quote
        raw_end = index + 1
        raw_end += 1 while bytes[raw_end] == 35
        if bytes[raw_end] == 34
          raw_hash_count = raw_end - index - 1
          state = :raw_string
          index = raw_end + 1
        else
          output[index] = byte
          index += 1
        end
      elsif triple == [34, 34, 34]
        state = :multiline_string
        index += 3
      elsif byte == 34 # "
        state = :string
        index += 1
      else
        output[index] = byte
        index += 1
      end
    when :line_comment
      if byte == 10
        output[index] = byte
        state = :code
      end
      index += 1
    when :block_comment
      if pair == [47, 45]
        block_depth += 1
        index += 2
      elsif pair == [45, 47]
        block_depth -= 1
        state = :code if block_depth.zero?
        index += 2
      else
        output[index] = byte if byte == 10
        index += 1
      end
    when :string
      if byte == 92 # backslash escape
        index += [2, bytes.length - index].min
      elsif byte == 34
        state = :code
        index += 1
      else
        output[index] = byte if byte == 10
        index += 1
      end
    when :multiline_string
      if triple == [34, 34, 34]
        state = :code
        index += 3
      else
        output[index] = byte if byte == 10
        index += 1
      end
    when :raw_string
      delimiter = [34] + Array.new(raw_hash_count, 35)
      if bytes[index, delimiter.length] == delimiter
        state = :code
        raw_hash_count = nil
        index += delimiter.length
      else
        output[index] = byte if byte == 10
        index += 1
      end
    end
  end

  unless [:code, :line_comment].include?(state)
    raise ArgumentError, "unterminated Lean lexical state #{state}"
  end

  output.pack('C*').force_encoding(text.encoding)
end

def source_declarations(text)
  text = lean_code_only(text)
  scope = []
  declarations = []
  structure_scope = nil
  inductive_scope = nil

  text.each_line do |line|
    code = line.sub(/--.*$/, '')
    stripped = code.strip.sub(/\A(?:@\[[^\]]*\]\s*)+/, '')
    modifiers = []
    while (modifier = stripped.match(/\A(noncomputable|private|protected|local|scoped|partial|unsafe)\s+/))
      modifiers << modifier[1]
      stripped = stripped.delete_prefix(modifier[0])
    end
    declaration_kind = ->(base) { (modifiers + [base]).join('_') }

    if (match = stripped.match(/\Anamespace\s+([A-Za-z_][A-Za-z0-9_'.]*)\z/))
      scope << [:namespace, match[1]]
      structure_scope = nil
      inductive_scope = nil
      next
    elsif (match = stripped.match(/\A(?:section|noncomputable section)(?:\s+([A-Za-z_][A-Za-z0-9_']*))?\z/))
      scope << [:section, match[1]]
      structure_scope = nil
      inductive_scope = nil
      next
    elsif (match = stripped.match(/\Aend(?:\s+([A-Za-z_][A-Za-z0-9_'.]*))?\z/))
      raise ArgumentError, "unmatched end #{match[1]}" if scope.empty?

      expected = scope.last[1]
      if match[1] && match[1] != expected
        raise ArgumentError, "mismatched end #{match[1]}; expected #{expected || 'anonymous section'}"
      end
      scope.pop
      structure_scope = nil
      inductive_scope = nil
      next
    end

    namespace = scope.filter_map { |kind, name| name if kind == :namespace }.join('.')
    if (match = stripped.match(/\A(?:structure|class)\s+([A-Za-z_][A-Za-z0-9_'.]*)\b/))
      declared = [namespace, match[1]].reject(&:empty?).join('.')
      kind = declaration_kind.call(stripped.start_with?('class') ? 'class' : 'structure')
      declarations << [declared, kind]
      structure_scope = declared
      inductive_scope = nil
      next
    end
    if (match = stripped.match(/\Ainductive\s+([A-Za-z_][A-Za-z0-9_'.]*)\b/))
      declared = [namespace, match[1]].reject(&:empty?).join('.')
      declarations << [declared, declaration_kind.call('inductive')]
      structure_scope = nil
      inductive_scope = declared
      next
    end
    if inductive_scope && (match = line.match(/\A\s*\|\s*([A-Za-z_][A-Za-z0-9_']*)\b/))
      declarations << ["#{inductive_scope}.#{match[1]}", 'constructor']
      next
    end
    if (match = stripped.match(/\A(?:def|abbrev|theorem|lemma|opaque|axiom|constant)\s+([A-Za-z_][A-Za-z0-9_'.]*)\b/))
      kind = declaration_kind.call(stripped[/\A([A-Za-z]+)/, 1])
      declarations << [[namespace, match[1]].reject(&:empty?).join('.'), kind]
      structure_scope = nil
      inductive_scope = nil
      next
    end
    if (match = stripped.match(/\Ainstance\s+([A-Za-z_][A-Za-z0-9_'.]*)\b/))
      declarations << [
        [namespace, match[1]].reject(&:empty?).join('.'),
        declaration_kind.call('instance')
      ]
      structure_scope = nil
      inductive_scope = nil
      next
    end
    if structure_scope && (match = line.match(/\A\s{2,}([A-Za-z_][A-Za-z0-9_']*)\s*:(?!=)/))
      declarations << ["#{structure_scope}.#{match[1]}", 'field']
    elsif !line.match?(/\A\s/) && !stripped.empty?
      structure_scope = nil
      inductive_scope = nil
    end
  end

  unless scope.empty?
    kind, name = scope.last
    raise ArgumentError, "unterminated #{kind} #{name || 'anonymous'}"
  end

  duplicates = declarations.group_by(&:first).select { |_name, entries| entries.length > 1 }
  unless duplicates.empty?
    raise ArgumentError, "duplicate source declaration #{duplicates.keys.sort.join('|')}"
  end

  declarations
end

lexer_probe = <<~'LEAN'
  namespace AAT.AG.DoctrineFiberProduct
  /- outer
    /- theorem BogusNested : True := by trivial -/
    theorem BogusOuter : True := by trivial
  -/
  def probeString := "theorem BogusString : True"
  def probeMultiline := """
    theorem BogusMultiline : True
  """
  def probeRaw := r#"
    "theorem BogusRaw : True"
  "#
  theorem RealProbe : True := by trivial
  axiom RealAxiom : True
  local instance RealLocalInstance : Inhabited Bool := inferInstance
  inductive RealInductive
    | actual
  end AAT.AG.DoctrineFiberProduct
LEAN
unless source_declarations(lexer_probe) == [
    ['AAT.AG.DoctrineFiberProduct.probeString', 'def'],
    ['AAT.AG.DoctrineFiberProduct.probeMultiline', 'def'],
    ['AAT.AG.DoctrineFiberProduct.probeRaw', 'def'],
    ['AAT.AG.DoctrineFiberProduct.RealProbe', 'theorem'],
    ['AAT.AG.DoctrineFiberProduct.RealAxiom', 'axiom'],
    ['AAT.AG.DoctrineFiberProduct.RealLocalInstance', 'local_instance'],
    ['AAT.AG.DoctrineFiberProduct.RealInductive', 'inductive'],
    ['AAT.AG.DoctrineFiberProduct.RealInductive.actual', 'constructor']
  ]
  warn 'internal Lean lexer regression probe failed'
  exit 1
end

def relative_identity(name)
  prefix = "#{ROOT_NAMESPACE}."
  name.delete_prefix(prefix)
end

begin
  code_text = file_text.transform_values { |text| lean_code_only(text) }
rescue ArgumentError => error
  warn "SOURCE_PARSE_ERROR #{error.message}"
  exit 1
end
quotation_files = code_text.filter_map { |path, text| path if text.include?('`') }
unless quotation_files.empty?
  quotation_files.each { |path| warn "SYNTAX_QUOTATION #{path}" }
  exit 1
end
escaped_identifier_files = code_text.filter_map do |path, text|
  path if text.include?('«') || text.include?('»')
end
unless escaped_identifier_files.empty?
  escaped_identifier_files.each { |path| warn "ESCAPED_IDENTIFIER #{path}" }
  exit 1
end
begin
  source_declaration_names = file_text.transform_values { |text| source_declarations(text) }
rescue ArgumentError => error
  warn "SOURCE_PARSE_ERROR #{error.message}"
  exit 1
end
file_sha256 = file_text.transform_values { |text| Digest::SHA256.hexdigest(text) }
outside_root = source_declaration_names.flat_map do |path, names|
  names.reject { |name, _kind| name.start_with?("#{ROOT_NAMESPACE}.") }
    .map { |name, _kind| [path, name] }
end
unless outside_root.empty?
  outside_root.each { |path, name| warn "OUTSIDE_ROOT #{name}@#{path}" }
  exit 1
end
file_declarations = source_declaration_names.transform_values do |names|
  names.to_h { |name, kind| [relative_identity(name), kind] }
end

resolved = {}
resolved_kinds = {}
resolved_occurrences = []
unresolved = []
ambiguous = []

occurrences.each do |cycle, name, targets|
  matches = targets.flat_map do |path|
    file_declarations.fetch(path).filter_map do |identity, kind|
      [identity, path, kind] if identity == name || identity.end_with?(".#{name}")
    end
  end
  matches.uniq!
  if matches.length == 1
    identity, path, kind = matches.first
    resolved[identity] = path
    resolved_kinds[identity] = kind
    resolved_occurrences << [cycle, name, identity, kind, path]
  elsif matches.empty?
    unresolved << [cycle, name, targets]
  else
    ambiguous << [cycle, name, matches.map { |identity, path, kind| "#{identity}:#{kind}@#{path}" }]
  end
end

unless unresolved.empty? && ambiguous.empty?
  unresolved.each do |cycle, name, targets|
    warn "UNRESOLVED cycle=#{cycle} #{name} targets=#{targets.join('|')}"
  end
  ambiguous.each do |cycle, name, matches|
    warn "AMBIGUOUS cycle=#{cycle} #{name} matches=#{matches.join('|')}"
  end
  exit 1
end

resolved_manifest = resolved_occurrences.map do |cycle, report_name, identity, kind, path|
  "cycle=#{cycle}|report=#{report_name}|identity=#{identity}|kind=#{kind}|module=#{path}"
end.join("\n")
resolved_manifest_sha256 = Digest::SHA256.hexdigest(resolved_manifest)
expected_resolved_manifest_sha256 = '274037f43519768ca7cc5b7e5df733e4da6f5530358708be27a74abfc50ddebe'
unless resolved_manifest_sha256 == expected_resolved_manifest_sha256
  warn "resolved manifest mismatch sha256=#{resolved_manifest_sha256}"
  exit 1
end
claim_resolutions = claim_records.filter_map do |cycle, field, name|
  next if name.start_with?('planned ')

  matches = resolved.keys.select do |identity|
    identity == name || identity.end_with?(".#{name}")
  end
  unless matches.length == 1
    warn "CLAIM_RESOLUTION cycle=#{cycle} field=#{field} name=#{name} matches=#{matches.join('|')}"
    exit 1
  end
  [cycle, field, name, matches.first]
end
claim_resolution_manifest = claim_resolutions.map do |cycle, field, name, identity|
  "cycle=#{cycle}|field=#{field}|name=#{name}|identity=#{identity}"
end.join("\n")
claim_resolution_manifest_sha256 = Digest::SHA256.hexdigest(claim_resolution_manifest)
expected_claim_resolution_manifest_sha256 = 'e4444c10f8a2ffc0be62f93565384a75d0e71029519b0c30f95814d7d932216c'
unless claim_resolution_manifest_sha256 == expected_claim_resolution_manifest_sha256
  warn "claim resolution manifest mismatch sha256=#{claim_resolution_manifest_sha256}"
  exit 1
end

grouped = Hash.new { |hash, key| hash[key] = [] }
resolved.each { |name, path| grouped[path] << name }
output = []
output << "map_type: g115_exact_declaration_map"
output << "goal_revision: 9"
output << "artifact_semantics: canonical_source_declaration_identities_from_accepted_cycles_1_through_83"
output << "identity_root: #{ROOT_NAMESPACE}"
output << "identity_resolution: cycle_local_qualified_suffix_with_locked_canonical_identity_module_and_declaration_kind"
output << "identity_kind_manifest_sha256: #{resolved_manifest_sha256}"
output << "claim_manifest_sha256: #{claim_manifest_sha256}"
output << "claim_resolution_manifest_sha256: #{claim_resolution_manifest_sha256}"
output << "acceptance_provenance_manifest_sha256: #{provenance_manifest_sha256}"
output << "source_lexer: nested_block_comment_line_comment_escaped_string_multiline_string_raw_string_syntax_quotation_and_escaped_identifier_fail_closed"
output << "input_manifest_sha256: #{manifest_sha256}"
output << "verification_scope: source_identity_kind_claim_and_reported_acceptance_provenance_with_same_byte_snapshot_module_hash"
output << "head_oid_binding: deferred_to_schema_complete_same_head_final_packet"
output << "lean_acceptance_provenance: source_sha256_and_validation_refs_projection_hash_locked_for_accepted_cycles"
output << "module_root: research/lean/ResearchLean/AG/DoctrineFiberProduct/"
output << "module_hash: sha256_of_same_in_memory_source_bytes_used_for_identity_resolution"
output << "generator: research/reports/evidence/g115_exact_declaration_map.rb"
output << "---"
output << "# artifacts=#{occurrences.map { |_c, name, _t| name }.uniq.length}"
output << "# targets=#{all_targets.length}"
output << "# resolved=#{resolved.length}"
output << "# unresolved=#{unresolved.length}"
output << "# ambiguous=#{ambiguous.length}"
output << "# ---MAP---"
grouped.sort.each do |path, names|
  module_name = path.sub(%r{\Aresearch/lean/ResearchLean/AG/DoctrineFiberProduct/}, '')
  output << "- module: #{module_name}"
  output << "  head_sha256: #{file_sha256.fetch(path)}"
  output << "  declarations: [#{names.sort.join(', ')}]"
  output << "  declaration_kinds: [#{names.sort.map { |name| "#{name}=#{resolved_kinds.fetch(name)}" }.join(', ')}]"
end
STDOUT.write(output.join("\n") + "\n")

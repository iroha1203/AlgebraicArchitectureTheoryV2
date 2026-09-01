require 'digest'
require 'open3'
require 'tempfile'

unless ARGV.length == 2 || (ARGV.length == 3 && ARGV[2] == '--lean-audit')
  warn 'usage: g115_exact_declaration_map.rb REPORT REPO_ROOT [--lean-audit]'
  exit 2
end
report_path = ARGV.fetch(0)
repo_root = ARGV.fetch(1)
output_mode = ARGV[2] == '--lean-audit' ? :lean_audit : :map
report = File.read(report_path)

occurrences = []
all_targets = []
cycle_records = []

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
  targets = section.scan(/^  lean_targets: \[(.*)\]$/).flat_map do |match|
    match.first.split(',').map(&:strip).select { |path| path.end_with?('.lean') }
  end.map do |path|
    path.start_with?('research/', 'Formal/') ? path : "research/lean/#{path}"
  end
  artifacts = section.scan(/^  lean_artifacts: \[(.*)\]$/).flat_map do |match|
    match.first.split(',').map(&:strip)
  end.reject do |name|
    name.empty? || name.start_with?('planned ') ||
      !name.match?(/\A[A-Za-z_][A-Za-z0-9_'.]*\z/)
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
expected_manifest_sha256 = '9880b63cf3a688c9ab6a1fc6f51f8771994a3bdd3589d3d6e119e3f8a2b1809e'
unless manifest_sha256 == expected_manifest_sha256 &&
    occurrences.length == 1028 &&
    occurrences.map { |_cycle, name, _targets| name }.uniq.length == 1025 &&
    all_targets.length == 80
  warn "input manifest mismatch sha256=#{manifest_sha256} occurrences=#{occurrences.length} " \
    "identities=#{occurrences.map { |_cycle, name, _targets| name }.uniq.length} " \
    "targets=#{all_targets.length}"
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
    end
  end

  output.pack('C*').force_encoding(text.encoding)
end

def source_declarations(text)
  text = lean_code_only(text)
  scope = []
  declarations = []
  structure_scope = nil

  text.each_line do |line|
    code = line.sub(/--.*$/, '')
    stripped = code.strip.sub(/\A(?:@\[[^\]]*\]\s*)+/, '')
    stripped = stripped.sub(/\A(?:(?:noncomputable|private|protected)\s+)+/, '')

    if (match = stripped.match(/\Anamespace\s+([A-Za-z_][A-Za-z0-9_'.]*)\z/))
      scope << [:namespace, match[1]]
      structure_scope = nil
      next
    elsif stripped.match?(/\A(?:section|noncomputable section)(?:\s+[A-Za-z_][A-Za-z0-9_']*)?\z/)
      scope << [:section, nil]
      structure_scope = nil
      next
    elsif stripped.match?(/\Aend(?:\s+[A-Za-z_][A-Za-z0-9_'.]*)?\z/)
      scope.pop
      structure_scope = nil
      next
    end

    namespace = scope.filter_map { |kind, name| name if kind == :namespace }.join('.')
    if (match = stripped.match(/\A(?:structure|class)\s+([A-Za-z_][A-Za-z0-9_'.]*)\b/))
      declared = [namespace, match[1]].reject(&:empty?).join('.')
      declarations << declared
      structure_scope = declared
      next
    end
    if (match = stripped.match(/\A(?:def|abbrev|theorem|lemma|opaque)\s+([A-Za-z_][A-Za-z0-9_'.]*)\b/))
      declarations << [namespace, match[1]].reject(&:empty?).join('.')
      structure_scope = nil
      next
    end
    if structure_scope && (match = line.match(/\A\s{2,}([A-Za-z_][A-Za-z0-9_']*)\s*:/))
      declarations << "#{structure_scope}.#{match[1]}"
    elsif !line.match?(/\A\s/) && !stripped.empty?
      structure_scope = nil
    end
  end

  declarations.uniq
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
  theorem RealProbe : True := by trivial
  end AAT.AG.DoctrineFiberProduct
LEAN
unless source_declarations(lexer_probe) == [
    'AAT.AG.DoctrineFiberProduct.probeString',
    'AAT.AG.DoctrineFiberProduct.probeMultiline',
    'AAT.AG.DoctrineFiberProduct.RealProbe'
  ]
  warn 'internal Lean lexer regression probe failed'
  exit 1
end

def relative_identity(name)
  prefix = "#{ROOT_NAMESPACE}."
  name.start_with?(prefix) ? name.delete_prefix(prefix) : name
end

file_declarations = file_text.transform_values do |text|
  source_declarations(text).map { |name| relative_identity(name) }
end

resolved = {}
unresolved = []
ambiguous = []

occurrences.each do |cycle, name, targets|
  matches = targets.flat_map do |path|
    file_declarations.fetch(path).filter_map do |identity|
      [identity, path] if identity == name || identity.end_with?(".#{name}")
    end
  end
  matches.uniq!
  if matches.length == 1
    identity, path = matches.first
    resolved[identity] = path
  elsif matches.empty?
    unresolved << [cycle, name, targets]
  else
    ambiguous << [cycle, name, matches.map { |identity, path| "#{identity}@#{path}" }]
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

lean_audit_source = all_targets.sort.map do |path|
  module_name = path.delete_prefix('research/lean/').delete_suffix('.lean').tr('/', '.')
  "import #{module_name}"
end.join("\n")
lean_audit_source += "\n\n"
lean_audit_source += resolved.keys.sort.map do |name|
  "#check #{ROOT_NAMESPACE}.#{name}"
end.join("\n")
lean_audit_source += "\n"

if output_mode == :lean_audit
  print lean_audit_source
  exit
end

expected_lean_audit_output_sha256 =
  '605c1208efaa6ee56fb870678dfe9ef3f9a13a09e441659402f4e9f1a9ec8151'
lean_audit_output = nil
Tempfile.create(['G115ExactDeclarationIdentityAudit', '.lean']) do |audit_file|
  audit_file.write(lean_audit_source)
  audit_file.flush
  lean_audit_output, status = Open3.capture2e(
    'lake', 'env', 'lean', audit_file.path,
    chdir: File.join(repo_root, 'research/lean')
  )
  unless status.success?
    warn lean_audit_output
    warn "fully qualified Lean identity audit failed with exit #{status.exitstatus}"
    exit 1
  end
end
lean_audit_output_sha256 = Digest::SHA256.hexdigest(lean_audit_output)
unless lean_audit_output_sha256 == expected_lean_audit_output_sha256
  warn "Lean identity audit output hash mismatch: #{lean_audit_output_sha256}"
  exit 1
end

puts "map_type: g115_exact_declaration_map"
puts "goal_revision: 9"
puts "artifact_semantics: canonical_namespace_qualified_current_declaration_identities_from_accepted_cycles_1_through_83"
puts "identity_root: #{ROOT_NAMESPACE}"
puts "identity_resolution: source_namespace_stack_and_exact_qualified_suffix_then_focused_lean_check"
puts "source_lexer: nested_block_comment_line_comment_escaped_string_and_multiline_string_aware"
puts "input_manifest_sha256: #{manifest_sha256}"
puts "lean_identity_audit_output_sha256: #{lean_audit_output_sha256}"
puts "module_root: research/lean/ResearchLean/AG/DoctrineFiberProduct/"
puts "module_hash: sha256_of_current_worktree_file_content"
puts "generator: research/reports/evidence/g115_exact_declaration_map.rb"
puts "---"
puts "# artifacts=#{occurrences.map { |_c, name, _t| name }.uniq.length}"
puts "# targets=#{all_targets.length}"
puts "# resolved=#{resolved.length}"
puts "# unresolved=#{unresolved.length}"
unresolved.each { |cycle, name, targets| puts "# UNRESOLVED cycle=#{cycle} #{name} targets=#{targets.join('|')}" }
puts "# ambiguous=#{ambiguous.length}"
ambiguous.each { |cycle, name, matches| puts "# AMBIGUOUS cycle=#{cycle} #{name} matches=#{matches.join('|')}" }
puts "# ---MAP---"

grouped = Hash.new { |hash, key| hash[key] = [] }
resolved.each { |name, path| grouped[path] << name }
grouped.sort.each do |path, names|
  sha = Digest::SHA256.file(File.join(repo_root, path)).hexdigest
  module_name = path.sub(%r{\Aresearch/lean/ResearchLean/AG/DoctrineFiberProduct/}, '')
  puts "- module: #{module_name}"
  puts "  head_sha256: #{sha}"
  puts "  declarations: [#{names.sort.join(', ')}]"
end

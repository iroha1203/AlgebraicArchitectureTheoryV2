require 'digest'

report_path = ARGV.fetch(0)
repo_root = ARGV.fetch(1)
unless ARGV.length == 2 || (ARGV.length == 3 && ARGV[2] == '--lean-audit')
  warn 'usage: g115_exact_declaration_map.rb REPORT REPO_ROOT [--lean-audit]'
  exit 2
end
output_mode = ARGV[2] == '--lean-audit' ? :lean_audit : :map
report = File.read(report_path)

occurrences = []
all_targets = []

report.split(/^## Cycle /).drop(1).each do |section|
  cycle = section[/\A(\d+)/, 1].to_i
  next if cycle > 83
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
end

all_targets.uniq!
file_text = {}
all_targets.each { |path| file_text[path] = File.read(File.join(repo_root, path)) }

ROOT_NAMESPACE = 'AAT.AG.DoctrineFiberProduct'

def source_declarations(text)
  text = text.gsub(/\/-.*?-\//m, '')
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
  if matches.empty?
    matches = all_targets.flat_map do |path|
      file_declarations.fetch(path).filter_map do |identity|
        [identity, path] if identity == name || identity.end_with?(".#{name}")
      end
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

if output_mode == :lean_audit
  all_targets.sort.each do |path|
    module_name = path.delete_prefix('research/lean/').delete_suffix('.lean').tr('/', '.')
    puts "import #{module_name}"
  end
  puts
  resolved.keys.sort.each { |name| puts "#check #{ROOT_NAMESPACE}.#{name}" }
  exit
end

puts "map_type: g115_exact_declaration_map"
puts "goal_revision: 9"
puts "artifact_semantics: canonical_namespace_qualified_current_declaration_identities_from_accepted_cycles_1_through_83"
puts "identity_root: #{ROOT_NAMESPACE}"
puts "identity_resolution: source_namespace_stack_and_exact_qualified_suffix_then_focused_lean_check"
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

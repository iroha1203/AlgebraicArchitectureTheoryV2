require 'digest'

report_path = ARGV.fetch(0)
repo_root = ARGV.fetch(1)
part_index = (ARGV[2] || '1').to_i
part_count = (ARGV[3] || '1').to_i
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

def declaration_score(text, local)
  escaped = Regexp.escape(local)
  patterns = [
    /(?:structure|class|def|abbrev|theorem|lemma|instance)\s+(?:[A-Za-z0-9_'.]+\.)?#{escaped}\b/m,
    /^\s*#{escaped}\s*:/m,
    /(?:structure|class|def|abbrev|theorem|lemma|instance)\s*\n\s*(?:[A-Za-z0-9_'.]+\.)?#{escaped}\b/m
  ]
  patterns.each_with_index.sum { |pattern, index| text.match?(pattern) ? (3 - index) : 0 }
end

resolved = {}
unresolved = []
ambiguous = []

occurrences.each do |cycle, name, targets|
  next if resolved.key?(name)
  local = name.split('.').last
  candidates = targets.select { |path| file_text[path]&.include?(local) }
  candidates = all_targets.select { |path| file_text[path]&.include?(local) } if candidates.empty?
  scored = candidates.map { |path| [path, declaration_score(file_text[path], local)] }
  max_score = scored.map(&:last).max || 0
  best = scored.select { |_path, score| score == max_score && score > 0 }.map(&:first)
  if best.length == 1
    resolved[name] = best.first
  elsif candidates.length == 1
    resolved[name] = candidates.first
  elsif best.empty?
    unresolved << [cycle, name, targets]
  else
    # Prefer a file assigned to the same cycle; if still tied, leave fail-closed.
    same_cycle = best & targets
    if same_cycle.length == 1
      resolved[name] = same_cycle.first
    else
      ambiguous << [cycle, name, best]
    end
  end
end

{
  'UpperGeometryCompatibleProblemInputData.CanonicalAuthoredPairedRestrictedPoint' =>
    'research/lean/ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCanonicalAuthoredPairedRestrictedPoint.lean',
  'UpperGeometryCompatibleProblemInputData.GeneratedPairedRestrictedPoint' =>
    'research/lean/ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCanonicalAuthoredPairedRestrictedPoint.lean'
}.each do |name, path|
  resolved[name] = path
  ambiguous.reject! { |_cycle, ambiguous_name, _paths| ambiguous_name == name }
end

puts "# artifacts=#{occurrences.map { |_c, name, _t| name }.uniq.length}"
puts "# targets=#{all_targets.length}"
puts "# resolved=#{resolved.length}"
puts "# unresolved=#{unresolved.length}"
unresolved.each { |cycle, name, targets| puts "# UNRESOLVED cycle=#{cycle} #{name} targets=#{targets.join('|')}" }
puts "# ambiguous=#{ambiguous.length}"
ambiguous.each { |cycle, name, paths| puts "# AMBIGUOUS cycle=#{cycle} #{name} paths=#{paths.join('|')}" }
puts "# ---MAP---"

grouped = Hash.new { |hash, key| hash[key] = [] }
resolved.each { |name, path| grouped[path] << name }
sorted_groups = grouped.sort
slice_size = (sorted_groups.length.to_f / part_count).ceil
selected_groups = sorted_groups.slice((part_index - 1) * slice_size, slice_size) || []
selected_groups.each do |path, names|
  sha = Digest::SHA256.file(File.join(repo_root, path)).hexdigest
  puts "- module: #{path}"
  puts "  head_sha256: #{sha}"
  puts "  declarations: [#{names.sort.join(', ')}]"
end

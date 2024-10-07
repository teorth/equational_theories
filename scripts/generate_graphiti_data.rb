# lake exe extract_implications --json equational_theories > /tmp/implications.json
# ruby scripts/generate_graphiti_data.rb /tmp/implications.json > home_page/graphiti/graph.json
# python -m http.server 8000 --directory home_page/graphiti

require 'json'
require File.join(__dir__, 'graph')

if ARGV.length != 1
  $stderr.puts "Usage: scripts/generate_graphiti_data.rb <implications json>"
  exit 1
end


equations = {}
File.read(File.join(__dir__, '../equational_theories/AllEquations.lean')).split("\n").each { |s|
  if s =~ /equation\s*(\d+)\s*:=\s*(.+)/
    equations[$1.to_i] = $2
  end
}
File.read(File.join(__dir__, '../equational_theories/Equations.lean')).split("\n").each { |s|
  if s =~ /abbrev Equation(\d+).*: G, (.+)/ || s =~ /equation\s*(\d+)\s*:=\s*(.+)/
    if !equations[$1.to_i]
      equations[$1.to_i] = $2
    elsif equations[$1.to_i] != $2
      $stderr.puts "Equations don't match? #{$1} / #{equations[$1.to_i]} / #{$2}"
      exit 1
    end
  end
}

implications_graph = Graph.from_json(ARGV[0])
condensed_graph, node_to_scc_map, scc_to_node_map = implications_graph.condensation

condensed_closure = condensed_graph.transitive_closure

condensed = {}
condensed_closure.adj_list.each { |k, v| condensed[k] = v.to_a }

puts JSON.generate({
  "timestamp" => Time.now.utc.to_i,
  "commit_hash" => `git rev-parse HEAD`.chomp,
  "condensed_graph" => condensed,
  "scc_to_node_map" => scc_to_node_map,
  "node_to_scc_map" => node_to_scc_map,
  "equations" => equations
})

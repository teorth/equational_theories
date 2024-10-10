# lake exe extract_implications --json equational_theories > /tmp/implications.json
# lake exe extract_implications unknowns > /tmp/unknowns.json
# ruby scripts/generate_graphiti_data.rb /tmp/implications.json /tmp/unknowns.json > home_page/graphiti/graph.json
# python -m http.server 8000 --directory home_page/graphiti

require 'json'
require File.join(__dir__, 'graph')

if ARGV.length != 2
  $stderr.puts "Usage: scripts/generate_graphiti_data.rb <implications json> <unknowns json>"
  exit 1
end


equations = {}
["1_999", "1000_1999", "2000_2999", "3000_3999", "4000_4694"].each { |i|
  File.read(File.join(__dir__, "../equational_theories/Equations/Eqns#{i}.lean")).split("\n").each { |s|
    if s =~ /equation\s*(\d+)\s*:=\s*(.+)/
      equations[$1.to_i] = $2
    end
  }
}
File.read(File.join(__dir__, '../equational_theories/Equations/Basic.lean')).split("\n").each { |s|
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

unknowns = {}
JSON.parse(File.read(ARGV[1])).each { |unknown|
  unknown_lhs_eq = unknown["lhs"][8, unknown["lhs"].length].to_i
  unknown_rhs_eq = unknown["rhs"][8, unknown["rhs"].length].to_i

  unknown_lhs_scc = node_to_scc_map[unknown_lhs_eq]
  unknown_rhs_scc = node_to_scc_map[unknown_rhs_eq]

  if !unknown_lhs_scc || !unknown_rhs_scc
    $stderr.puts "Unknown LHS/RHS mapping to SCC"
    exit 1
  end

  unknowns[unknown_lhs_scc] ||= []
  unknowns[unknown_lhs_scc] << unknown_rhs_scc
}

puts JSON.generate({
  "timestamp" => Time.now.utc.to_i,
  "commit_hash" => `git rev-parse HEAD`.chomp,
  "condensed_graph" => condensed,
  "scc_to_node_map" => scc_to_node_map,
  "node_to_scc_map" => node_to_scc_map,
  "equations" => equations,
  "unknowns" => unknowns
})

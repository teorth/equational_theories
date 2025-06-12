# See .github/workflows/blueprint-paper.yml for proper invocation to generate graphiti data. Then run:
# python -m http.server 8000 --directory home_page/graphiti

require 'json'
require File.join(__dir__, 'graph')
require File.join(__dir__, 'find_equation_id')

if ARGV.length != 5
  $stderr.puts "Usage: scripts/generate_graphiti_data.rb <duals json> <implications json> <unknowns json> <finite implications json> <finite unknowns json>"
  exit 1
end

duals = JSON.parse(File.read(ARGV[0]))

equations = {}

for i in 1..4694
    eq = Equation.from_id(i)
    equations[i] = eq.to_s
end

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

def graph2map(g)
  out = {}
  g.adj_list.each { |k, v| out[k] = v.to_a.sort }

  out
end

def gen_graph(imp_file, unknowns_file)
  implications_graph = Graph.from_json_array(JSON.parse(File.read(imp_file))["implications"])
  condensed_graph, node_to_scc_map, scc_to_node_map = implications_graph.condensation

  unknowns = Graph.new
  Graph.from_json_array(JSON.parse(File.read(unknowns_file))).adj_list.each { |v1, list|
    list.each { |v2|
      v1_scc = node_to_scc_map[v1]
      v2_scc = node_to_scc_map[v2]

      if !v1_scc || !v2_scc
        $stderr.puts "Unknown LHS/RHS mapping to SCC"
        exit 1
      end

      unknowns.add_edge(v1_scc, v2_scc)
    }
  }

  scc_to_node_map.keys.each { |k| scc_to_node_map[k].sort! }

  {
    "condensed_graph" => graph2map(condensed_graph),
    "scc_to_node_map" => scc_to_node_map,
    "node_to_scc_map" => node_to_scc_map,
    "unknowns" => graph2map(unknowns),
  }
end

puts JSON.generate({
  "timestamp" => Time.now.utc.to_i,
  "commit_hash" => `git rev-parse HEAD`.chomp,
  "equations" => equations,
  "duals" => duals,
  "general_graph" => gen_graph(ARGV[1], ARGV[2]),
  "finite_graph" => gen_graph(ARGV[3], ARGV[4]),
})

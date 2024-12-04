# To generate the prerequisite data, see the commands regarding `/tmp/raw_data` in .github/workflows/blueprint.yml

require 'json'

require File.join(__dir__, 'graph')

def number_with_commas(number)
  number.to_s.reverse.scan(/\d{1,3}/).join(",").reverse
end

# The ruby Graph code is not aware of dual-reduction, so where possible operate over the closure
# to make sure we take that data into account.
def compute_closure_graph_data(path, out={})
  json = JSON.load(File.open(path))

  implications = Graph.from_json_array(json["implications"])
  implications.filter! { |eq_num| eq_num >= 1 && eq_num <= 4694 }

  sccs = implications.scc
  out["equiv_classes_of_1"] = sccs.count { |e| e.length == 1 }
  out["equiv_classes_gt_1"] = sccs.count { |e| e.length > 1 }
  out["largest_equiv_class_size"] = sccs.map { |e| e.length }.max

#  self_implications = 1.upto(4694).map { |a| [a, a] }
#  out["implication_closure_edges_no_selfimplications"] = (implications.edges - self_implications).length
#  out["implication_closure_edges_with_selfimplications"] = (implications.edges | self_implications).length
#  out["refutation_closure_edges"] = json["nonimplications"].count { |x| x["lhs"][8,8].to_i <= 4694 && x["rhs"][8,8].to_i <= 4694 }

  condensed_graph, node_to_scc_map, scc_to_node_map = implications.condensation
  out["condensed_vertices"] = condensed_graph.vertices.length
  out["condensed_edges"] = condensed_graph.edges.length
  out["condensed_reduced_edges"] = condensed_graph.step_reduction.edges.length

  out["minimal_equivalent_graph_edges"] = implications.transitive_reduction.edges.length

=begin
  # Alternatively could be computed
  condensed_edges = condensed_graph.edges.length
  scc_size1 = scc_to_node_map.filter { |k, v| v.length == 1 }.length
  puts "(Computed) MEQ edges: #{condensed_edges + (4694 - scc_size1)}"
=end

  out
end

def compute_raw_data(path, out = {})
  json = JSON.load(File.open(path))

  out["theorems_implications"] = json.count { |e|
    e["proven"] == true && e["variant"]["implication"] != nil && e["variant"]["implication"]["lhs"][8,8].to_i <= 4694 && e["variant"]["implication"]["rhs"][8,8].to_i <= 4694
  }
  out["theorems_refutations"] = json.count { |e|
    e["proven"] == true && e["variant"]["facts"] != nil && e["variant"]["facts"]["refuted"].count { |s| s[8,8].to_i <= 4694 } >= 1 && e["variant"]["facts"]["satisfied"].count { |s| s[8,8].to_i <= 4694 } >= 1
  }
end

general = {}
compute_closure_graph_data("/tmp/raw_data/general_implications_closure.json", general)
compute_raw_data("/tmp/raw_data/general_raw_full_entries.json", general)

finite = {}
compute_closure_graph_data("/tmp/raw_data/finite_implications_closure.json", finite)
compute_raw_data("/tmp/raw_data/finite_raw_full_entries.json", finite)

fields = [
#  [ "implication_closure_edges_no_selfimplications", "Implications in the transitive closure (without self-implications)" ],
#  [ "implication_closure_edges_with_selfimplications", "Implications in the transitive closure (with self-implications)" ],
#  [ "refutation_closure_edges", "Refutations in the transitive closure" ],

  [ "theorems_implications", "Implication theorems<br>Note: The difference from explicit implications is due to duplicates" ],
  [ "theorems_refutations", "Refutation theorems<br>Note: The difference from explicit refutations is that a single theorem can satisfy M equations and refute N equations, explicit refutations is the sum of all M*N, and this is the count of individual such theorems." ],

  [ "condensed_vertices", "Equivalence classes" ],

  [ "equiv_classes_of_1", "Equivalence classes of size = 1" ],
  [ "equiv_classes_gt_1", "Equivalence classes of size > 1" ],
  [ "largest_equiv_class_size", "Size of the largest equivalence class" ],

  [ "condensed_edges", "Transitively closed implications between equivalence classes" ],
  [ "condensed_reduced_edges", "Transitively reduced implications between equivalence classes" ],
  [ "minimal_equivalent_graph_edges", "Edges in the minimal equivalent graph, this is the optimally minimal number of edges to represent the implication graph making use of transitivity, but not dual relations" ],
]

puts "## Graph info"
puts
puts "The following information is derived from graphs without sporadic equations (equations of order > 4) included."
puts
puts "| | General graph | Finite graph |"
puts "| -- | -- | -- |"
fields.each { |field, description|
  if !general[field] || !finite[field]
    $stderr.puts "Missing #{field}!"
    exit 1
  end
  puts "| #{description} | #{number_with_commas(general[field])} | #{number_with_commas(finite[field])} |"
}
puts

# lake exe extract_implications --json equational_theories | ruby -rjson -e 'JSON.parse($stdin.read)["implications"].each { |s| puts s["lhs"][8,10] + "," + s["rhs"][8,10] }' | sort -u > /tmp/implications.csv
# ruby scripts/generate_graphviz_graph.rb /tmp/implications.csv > graph.dot
# dot -T svg -o graph.svg graph.dot
#
# Note: there are also options to limit the number of variables or operations in the generated graph,
# or delete Equation 1 and the Equation 2 equivalence class.
#
# In order to reduce the cleanest looking graph, this tools generates a transitive closure and then
# reduces it to get a graph with minimal edges. That causes generation to be slow.

require 'optparse'
require File.join(__dir__, 'graph')

options = {}
opt_parser= OptionParser.new do |opt|
  opt.banner = "Usage: generate_graphviz_graph [options] <graph csv file>"

  opt.on('--limit-variables NUM') { |o| options[:limit_variables] = o.to_i }
  opt.on('--limit-operations NUM') { |o| options[:limit_operations] = o.to_i }
  opt.on('--remove-eq1', 'Remove Equation1 from the output') { |o| options[:remove_eq1] = true }
  opt.on('--remove-eq2', 'Remove the entire Equation2 equivalence class from the output') { |o| options[:remove_eq2] = true }
end

opt_parser.parse!

if ARGV.length != 1
  $stderr.puts "Missing argument"
  $stderr.puts opt_parser
  exit 1
end

equations_file = File.read(File.join(__dir__, '../equational_theories/AllEquations.lean'))

equations = {}
equations_file.split("\n").each { |s|
  if s =~ /equation (\d+) := (.+)/
    equations[$1.to_i] = $2
  end
}

graph = Graph.new
File.read(ARGV[0]).split("\n").each { |s|
  a,b = s.split(",")
  graph.add_edge(a.to_i, b.to_i)
}

all_vertices = Set.new graph.adj_list.keys
graph.adj_list.each { |k, v| all_vertices += v }
vertices_to_delete = []
if options[:limit_variables]
  vertices_to_delete.concat all_vertices.filter { |k|
    equations[k].scan(/[xyzwvu]/).uniq.length > options[:limit_variables]
  }
end
if options[:limit_operations]
  vertices_to_delete.concat all_vertices.filter { |k|
    equations[k].count("∘") > options[:limit_operations]
  }
end
if options[:remove_eq1]
  vertices_to_delete << 1
end
if options[:remove_eq2]
  vertices_to_delete.concat graph.scc.filter { |scc| scc.include? 2 }[0]
end

# Reducing first improves the speed of the closure
graph = graph.transitive_reduction
graph = graph.transitive_closure
if vertices_to_delete.length > 0
  vertices_to_delete = Set.new vertices_to_delete

  # If we're deleting elements, we want to compute the deletions over the closure to
  # avoid breaking up SCCs and having to do DFS to discover all children of deleted vrtices

  # For every vertex we delete, we want to connect it's ancestors to it's children
  vertices_to_delete.each { |v| graph.adj_list.delete(v) }
  graph.adj_list.keys.each { |v| graph.adj_list[v] -= vertices_to_delete }
end

graph = graph.transitive_reduction

# Manual Graph condensation
sccs = graph.scc
condensed_graph = Graph.new
scc_map = {}
scc_reverse_map = {}

sccs.each_with_index { |scc, idx|
  scc_reverse_map["SCC#{idx}"] = scc.sort
  scc.each { |node|
    scc.each { |node| scc_map[node] = "SCC#{idx}" }
  }
}

graph.adj_list.each { |u, neighbors|
  neighbors.each { |v|
    next if scc_map[u] == scc_map[v]  # Skip edges within the same SCC
    condensed_graph.add_edge(scc_map[u], scc_map[v])
  }
}

# Condensation finished, generate graphviz data

puts "digraph G {"

def name(nodes)
  if nodes.length == 1
    "Eq #{nodes[0]}"
  else
    "Eqs #{nodes[0]}, ..."
  end
end

scc_reverse_map.each { |scc_name, nodes|
  print "  #{scc_name} ["
  nodes

    inbound = condensed_graph.adj_list.filter { |k, v| v.include? scc_name }.length
    outbound = condensed_graph.adj_list[scc_name].length

  if nodes.length == 1
    print "shape=box, label=\"#{name(nodes)}\\n#{equations[nodes[0]]}\""

    print ",tooltip=\"inbound edges: #{inbound}  outbound edges: #{outbound}\""
  else
    print "shape=circle, label=\"#{name(nodes)} (#{nodes.length} equations)\\n#{equations[nodes[0]]}\""
    print ",tooltip=\"inbound edges: #{inbound}  outbound edges: #{outbound}\\n"
    print "Equations " + nodes.map(&:to_s).join(', ') + "\\n"
    nodes.each_with_index { |n, idx| print "\\n" if idx != 0; print "#{equations[n]}" }
    print "\""
  end

  if ([2, 3, 4, 5, 6, 7, 8, 23, 38, 39, 40, 41, 42, 43, 45, 46, 168, 387, 4512, 4513, 4522, 4564, 4579, 4582] & nodes).length != 0
    print ", style=filled, fillcolor=green, color=black"
  end
  puts "];"
}

condensed_graph.adj_list.each { |node, neighbors|
  neighbors.each { |neighbor|
    puts "  #{neighbor} -> #{node} [tooltip=\"#{name(scc_reverse_map[neighbor])} -> #{name(scc_reverse_map[node])}\"];"
  }
}

puts "}"

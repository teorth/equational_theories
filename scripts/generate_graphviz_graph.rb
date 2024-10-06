# lake exe extract_implications --json equational_theories | ruby -rjson -e 'JSON.parse($stdin.read)["implications"].each { |s| puts s["lhs"][8,10] + "," + s["rhs"][8,10] }' | sort -u > /tmp/implications.csv
# ruby scripts/generate_graphviz_graph.rb /tmp/implications.csv > graph.dot
# dot -T svg -o graph.svg graph.dot
#
# Note: there are also options to limit the number of variables or operations in the generated graph,
# delete Equation 1 and the Equation 2 equivalence class, or limit to the Subgraph.
#
# In order to produce the cleanest looking graph, this tools generates a transitive closure and then
# reduces it to get a graph with minimal edges (the minimum equivalent graph). That causes generation
# to be slow.

require 'optparse'
require File.join(__dir__, 'graph')

SUBGRAPH = [1, 2, 3, 4, 5, 6, 7, 8, 23, 38, 39, 40, 41, 42, 43, 45, 46, 168, 387, 4512, 4513, 4522, 4564, 4579, 4582]

options = {}
opt_parser= OptionParser.new do |opt|
  opt.banner = "Usage: generate_graphviz_graph [options] <implications csv file>"

  opt.on('--limit-variables NUM') { |o| options[:limit_variables] = o.to_i }
  opt.on('--limit-operations NUM') { |o| options[:limit_operations] = o.to_i }
  opt.on('--limit-to-subgraph', 'Limit to Subgraph nodes') { |o| options[:limit_to_subgraph] = true }
  opt.on('--remove-eq1', 'Remove Equation1 from the output') { |o| options[:remove_eq1] = true }
  opt.on('--remove-eq2', 'Remove the entire Equation2 equivalence class from the output') { |o| options[:remove_eq2] = true }
end

opt_parser.parse!

if ARGV.length != 1
  $stderr.puts "Missing argument"
  $stderr.puts opt_parser
  exit 1
end

$equations = {}
File.read(File.join(__dir__, '../equational_theories/AllEquations.lean')).split("\n").each { |s|
  if s =~ /equation (\d+) := (.+)/
    $equations[$1.to_i] = $2
  end
}
File.read(File.join(__dir__, '../equational_theories/Equations.lean')).split("\n").each { |s|
  if s =~ /abbrev Equation(\d+).*: G, (.+)/
    if !$equations[$1.to_i]
      $equations[$1.to_i] = $2
    elsif $equations[$1.to_i] != $2
      $stderr.puts "Equations don't match? #{$1} / #{$equations[$1.to_i]} / #{$2}"
      exit 1
    end
  end
}

implications_graph = Graph.from_csv(ARGV[0])

vertices_to_delete = []
if options[:limit_variables]
  vertices_to_delete.concat implications_graph.vertices.filter { |k|
    if !$equations[k]
      $stderr.puts "Did not see equation for #{k}?!"
      exit 1
    end
    $equations[k].scan(/[xyzwvu]/).uniq.length > options[:limit_variables]
  }
end
if options[:limit_operations]
  vertices_to_delete.concat implications_graph.vertices.filter { |k|
    if !$equations[k]
      $stderr.puts "Did not see equation for #{k}?!"
      exit 1
    end
    $equations[k].count("◇") > options[:limit_operations]
  }
end
if options[:remove_eq1]
  vertices_to_delete << 1
end
if options[:remove_eq2]
  vertices_to_delete.concat implications_graph.scc.filter { |scc| scc.include? 2 }[0]
end
if options[:limit_to_subgraph]
  vertices_to_delete.concat (implications_graph.vertices.to_a - SUBGRAPH)
end

# Reducing first improves the speed of the closure
implications_graph = implications_graph.transitive_reduction
implications_graph = implications_graph.transitive_closure
if vertices_to_delete.length > 0
  vertices_to_delete = Set.new vertices_to_delete

  # If we're deleting elements, we want to compute the deletions over the closure to
  # avoid breaking up SCCs and having to do DFS to discover all children of deleted vrtices

  # For every vertex we delete, we want to connect it's ancestors to it's children
  vertices_to_delete.each { |v| implications_graph.adj_list.delete(v) }
  implications_graph.adj_list.keys.each { |v| implications_graph.adj_list[v] -= vertices_to_delete }
end

implications_graph = implications_graph.transitive_reduction

# Manual Graph condensation
sccs = implications_graph.scc
condensed_implications_graph = Graph.new
scc_map = {}
scc_reverse_map = {}

sccs.each_with_index { |scc, idx|
  scc_reverse_map["SCC#{idx}"] = scc.sort
  scc.each { |node|
    scc.each { |node| scc_map[node] = "SCC#{idx}" }
  }
}

implications_graph.adj_list.each { |u, neighbors|
  neighbors.each { |v|
    next if scc_map[u] == scc_map[v]  # Skip edges within the same SCC
    condensed_implications_graph.add_edge(scc_map[u], scc_map[v])
  }
}

# Condensation finished, generate graphviz data

reverse_map = {}
condensed_implications_graph.vertices.each { |node|
  if condensed_implications_graph.adj_list[node]
    condensed_implications_graph.adj_list[node].each { |v|
      reverse_map[v] ||= Set.new []
      reverse_map[v] << node
    }
  end
}

roots = reverse_map.keys.filter { |v| condensed_implications_graph.adj_list[v].length == 0 }
if !roots || roots.length == 0
  $stderr.puts "Failed to find a root in the graph?!"
  exit 1
end

puts <<-END
graph G {
  layout = dot
  rankdir = TB
  graph [ pad="0.2", ranksep="0.75", nodesep="0.35" ];
  node [ shape="none" ]

END

def name(nodes)
  nodes.sort!
  equations = nodes.map { |n|
    "#{$equations[n]} (#{n})"
  }

  if equations.length > 5
    equations = equations[0,4] + ["... [#{nodes.length} total equations]"]
  end

  equations.join("\\n")
end

scc_reverse_map.each { |scc_name, nodes|
  print "  #{scc_name} ["
  print "label=\"#{name(nodes)}\""
  if nodes.length > 1
    print ",shape=Mrecord"
  else
    if !options[:limit_to_subgraph]
      print ",shape=box"
    end
  end

  if roots.include?(scc_name)
    print ",root=true"
  end
  puts "]"
}

condensed_implications_graph.adj_list.each { |node, neighbors|
  neighbors.each { |neighbor|

    puts "  #{neighbor} -- #{node};"
  }
}

puts "}"

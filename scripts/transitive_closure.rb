# Given as an input a CSV of "1,2" pairs of implications, this generates their transitive
# closure, e.g. all of the implications that can be derived from these implications (e.g.
# A->B->C implies A->C). This algorithm is slow so it should preferably be used with inputs
# that have been transitively reduced (see scripts/transitive_reduction.rb)

require File.join(__dir__, 'graph')

graph = Graph.new
File.read(ARGV[0]).split("\n").each { |s|
  a,b = s.split(",")
  graph.add_edge(a.to_i, b.to_i)
}

maximal_graph = graph.transitive_closure
maximal_graph.print_graph

# Given as an input a CSV of "1,2" pairs of implications, this generates their transitive
# reduction, e.g. the minimal set of implications necessary to prove all of them (e.g. if
# A->B->C is proven, then A->C does not need to be included.)

require File.join(__dir__, 'graph')

graph = Graph.new
File.read(ARGV[0]).split("\n").each { |s|
  a,b = s.split(",")
  graph.add_edge(a.to_i, b.to_i)
}

min_graph = graph.transitive_reduction
min_graph.print_graph

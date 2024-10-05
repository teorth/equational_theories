require 'json'

# Given as an input the JSON produced by `lake exe extract_implications --json`, outputs
# a transitive reduction of the non-implications

require File.join(__dir__, 'graph')

graph = Graph.new
data = JSON.parse(File.read(ARGV[0]))
data["implications"].each { |s|
  graph.add_edge([false, s["rhs"][8,10].to_i], [false, s["lhs"][8,10].to_i])
  graph.add_edge([true, s["rhs"][8,10].to_i], [true, s["lhs"][8,10].to_i])
}
data["nonimplications"].each { |s|
  graph.add_edge([false, s["lhs"][8,10].to_i], [true, s["rhs"][8,10].to_i])
}

min_graph = graph.transitive_reduction
min_graph.adj_list.each do |(ut, u), neighbors|
  neighbors.each do |vt, v|
    puts "#{u},#{v}" if !ut && vt
  end
end

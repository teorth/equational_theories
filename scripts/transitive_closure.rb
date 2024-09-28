class Graph
  attr_accessor :adj_list

  def initialize
    @adj_list = Hash.new { |h, k| h[k] = Set.new([]) }
  end

  def add_edge(u, v)
    @adj_list[u] << v
  end

  def dfs(vertex, visited, reachable)
    visited[vertex] = true
    @adj_list[vertex].each do |neighbor|
      unless reachable.include?(neighbor)
        reachable << neighbor
      end
      dfs(neighbor, visited, reachable) unless visited[neighbor]
    end
  end

  def transitive_closure
    closure_graph = Hash.new { |h, k| h[k] = Set.new([]) }
    @adj_list.keys.each do |vertex|
      visited = Hash.new(false)
      reachable = []
      dfs(vertex, visited, reachable)
      closure_graph[vertex] = reachable
    end
    closure_graph
  end

  def print_graph(graph)
    graph.each do |u, neighbors|
      neighbors.each do |v|
        puts "#{u},#{v}" unless u == v
      end
    end
  end
end

graph = Graph.new
File.read(ARGV[0]).split("\n").each { |s|
  a,b = s.split(",")
  graph.add_edge(a.to_i, b.to_i)
}

maximal_graph = graph.transitive_closure
graph.print_graph(maximal_graph)

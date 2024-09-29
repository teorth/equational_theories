require 'set'

class Graph
  attr_accessor :adj_list

  def initialize
    @adj_list = Hash.new { |h, k| h[k] = Set.new([]) }
  end

  def add_edge(u, v)
    @adj_list[u] << v unless @adj_list[u].include?(v) # Prevent duplicate edges
  end

  def transitive_reduction
    reduced_graph = Graph.new

    # Add all edges first
    @adj_list.each do |u, neighbors|
      neighbors.each do |v|
        reduced_graph.add_edge(u, v)
      end
    end

    # For each edge, check if there is an alternative path
    @adj_list.each do |u, neighbors|
      neighbors.each do |v|
        next if u == v # Ignore self-loops

        # Remove edge u -> v and check for any path from u to v
        reduced_graph.adj_list[u].delete(v)

        # Perform a depth-first search (DFS) to see if v is reachable from u
        reachable = dfs(u, v, reduced_graph)
        reduced_graph.add_edge(u, v) unless reachable # Re-add the edge if v is not reachable
      end
    end

    reduced_graph
  end

  def dfs(start, goal, graph, visited = Set.new)
    return true if start == goal
    return false if visited.include?(start)

    visited.add(start)
    graph.adj_list[start].each do |neighbor|
      return true if dfs(neighbor, goal, graph, visited)
    end

    false
  end

  def print_graph
    @adj_list.each do |u, neighbors|
      neighbors.each do |v|
        puts "#{u},#{v}"
      end
    end
  end
end

# Example usage:
graph = Graph.new
File.read(ARGV[0]).split("\n").each { |s|
  a,b = s.split(",")
  graph.add_edge(a.to_i, b.to_i)
}

# Print the original graph
#puts "Original Graph:"
#graph.print_graph

reduced_graph = graph.transitive_reduction

# Print the reduced graph
#puts "\nReduced Graph:"
reduced_graph.print_graph


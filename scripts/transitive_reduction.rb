# Given as an input a CSV of "1,2" pairs of implications, this generates their transitive
# reduction, e.g. the minimal set of implications necessary to prove all of them (e.g. if
# A->B->C is proven, then A->C does not need to be included.)
#
# This implementation uses an algorithm optimized to parsing large cyclic graphs, e.g.
# condensing the initial graph to an acyclic graph, transitively reducing that, and then
# uncondensing and transitively reducing that again. Cyclic graphs are otherwise slow to
# transitively reduce.
#
# Note that this implementation is not totally optimal because finding a minimal graph
# requires finding a hamiltonian cycle (NP) during uncondensing, but in practice this
# did not appear to be a problem when used with large (~1m implications) data sets.

class Graph
  attr_accessor :adj_list

  def initialize
    @adj_list = Hash.new { |hash, key| hash[key] = Set.new([]) }
  end

  def add_edge(from, to)
    @adj_list[from] << to
  end

  # Single-elements are also counted as SCCs
  def scc
    index = 0
    stack = []
    lowlink = {}
    index_map = {}
    on_stack = {}
    sccs = []

    @adj_list.keys.each { |v|
      strongconnect(v, index, stack, lowlink, index_map, on_stack, sccs) unless index_map[v]
    }

    (@adj_list.keys - index_map.keys).each { |v|
      sccs << [v] unless sccs.any? { |scc| scc.include?(v) }
    }

    sccs
  end

  def strongconnect(v, index, stack, lowlink, index_map, on_stack, sccs)
    index_map[v] = index
    lowlink[v] = index
    index += 1
    stack.push(v)
    on_stack[v] = true

    @adj_list[v].each { |w|
      if !index_map[w]
        strongconnect(w, index, stack, lowlink, index_map, on_stack, sccs)
        lowlink[v] = [lowlink[v], lowlink[w]].min
      elsif on_stack[w]
        lowlink[v] = [lowlink[v], index_map[w]].min
      end
    }

    if lowlink[v] == index_map[v]
      current_scc = []
      while stack.last != v
        w = stack.pop
        on_stack[w] = false
        current_scc << w
      end
      w = stack.pop
      on_stack[w] = false
      current_scc << w
      sccs << current_scc
    end
  end

  def condensation
    sccs = scc
    condensed_graph = Graph.new
    scc_map = {}

    sccs.each_with_index { |scc, idx|
      scc.each { |node| scc_map[node] = "SCC#{idx}" }
    }

    @adj_list.each { |u, neighbors|
      neighbors.each { |v|
        next if scc_map[u] == scc_map[v]  # Skip edges within the same SCC
        condensed_graph.add_edge(scc_map[u], scc_map[v])
      }
    }

    condensed_graph
  end

  def uncondensation(original_graph, scc_map)
    uncondensed_graph = Graph.new

    scc_map.each { |scc_name, nodes|
      if nodes.length > 1
        failed = false
        # For SCCs with multiple nodes, try to add them in a naive hamiltonian cycle.
        # If the SCCs isn't fully connected and that fails, then fall back to adding all
        # of it's edges to the uncondensed graph
        nodes.each_index { |idx|
          next_in_chain = nil
          if idx+1 < nodes.length
            next_in_chain = nodes[idx+1]
          else
            next_in_chain = nodes[0]
          end

          if original_graph.adj_list[nodes[idx]].include?(next_in_chain)
            uncondensed_graph.add_edge(nodes[idx], next_in_chain)
          else
            failed = true
            break
          end
        }

        if failed
          nodes.each { |n1|
            original_graph.adj_list[n1].each { |n2|
              uncondensed_graph.add_edge(n1, n2)
            }
          }
        end
      end
    }

    # Now add edges between different SCCs based on the condensed graph's edges
    @adj_list.each { |u, neighbors|
      neighbors.each { |v|
        # Find an edge from the original source SCC to the target SCC, and re-add it.
        found = false
        scc_map[u].each { |source_node|
          scc_map[v].each { |target_node|
            if original_graph.adj_list[source_node].include?(target_node)
              uncondensed_graph.add_edge(source_node, target_node)
              found = true
              break
            end
          }
          break if found
        }

        if !found
          $stderr.puts "Failed to find src->target edge while uncondensing! #{u} -> #{v}"
          exit 1
        end
      }
    }

    uncondensed_graph
  end

  def transitive_reduction
    reduced_graph = Graph.new

    @adj_list.each { |u, neighbors|
      neighbors.each { |v|
        reduced_graph.add_edge(u, v)
      }
    }

    # For each edge, check if there is an alternative path
    @adj_list.each { |u, neighbors|
      neighbors.each { |v|
        next if u == v # Ignore self-loops

        reduced_graph.adj_list[u].delete(v)

        reachable = dfs(u, v, reduced_graph)
        reduced_graph.add_edge(u, v) unless reachable # Re-add the edge if v is not reachable
      }
    }

    reduced_graph
  end

  def dfs(start, goal, graph, visited = Set.new)
    return true if start == goal
    return false if visited.include?(start)

    visited.add(start)
    graph.adj_list[start].each { |neighbor|
      return true if dfs(neighbor, goal, graph, visited)
    }

    false
  end

  def reduce
    condensed_graph = condensation
    #$stderr.puts "Condensed vertices: #{condensed_graph.adj_list.size}"
    #$stderr.puts "Condensed edges: #{condensed_graph.adj_list.values.map(&:size).inject(0, &:+)}"
    reduced_condensed = condensed_graph.transitive_reduction

    sccs = scc
    scc_map = {}
    sccs.each_with_index { |scc, idx|
      scc_map["SCC#{idx}"] = scc
    }

    uncondensed = condensed_graph.uncondensation(self, scc_map)
    #$stderr.puts "Uncondensed vertices: #{uncondensed.adj_list.size}"
    #$stderr.puts "Uncondensed edges: #{uncondensed.adj_list.values.map(&:size).inject(0, &:+)}"
    uncondensed.transitive_reduction
  end
end

graph = Graph.new
File.read(ARGV[0]).split("\n").each { |s|
  a,b = s.split(",")
  graph.add_edge(a.to_i, b.to_i)
}

min_graph = graph.reduce
min_graph.adj_list.each { |node, neighbors|
  neighbors.each { |neighbor|
    if node == neighbor
      $stderr.puts "Should not be possible!"
      exit 1
    end
    puts "#{node},#{neighbor}"
  }
}

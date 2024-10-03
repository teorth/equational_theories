require 'set'

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
      strongconnect(v, stack, lowlink, index_map, on_stack, sccs) unless index_map[v]
    }

    (@adj_list.keys - index_map.keys).each { |v|
      sccs << [v] unless sccs.any? { |scc| scc.include?(v) }
    }

    sccs
  end

  def strongconnect(v, stack, lowlink, index_map, on_stack, sccs)
    index = index_map.length
    index_map[v] = index
    lowlink[v] = index
    stack.push(v)
    on_stack[v] = true

    @adj_list[v].each { |w|
      if !index_map[w]
        strongconnect(w, stack, lowlink, index_map, on_stack, sccs)
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

  # This implementation uses an algorithm optimized to parsing large cyclic graphs, e.g.
  # condensing the initial graph to an acyclic graph, transitively reducing that, and then
  # uncondensing and transitively reducing that again. Cyclic graphs are otherwise slow to
  # transitively reduce.
  #
  # Note that this implementation is not totally optimal because finding a minimal graph
  # requires finding a hamiltonian cycle (NP) during uncondensing, e.g. it only generates
  # the reduction actually reachable from the original data set. For the optimal reduction,
  # one must run reduce -> closure -> reduce.
  def transitive_reduction 
    condensed_graph = condensation
    $stderr.puts "Condensed vertices: #{condensed_graph.adj_list.size}"
    $stderr.puts "Condensed edges: #{condensed_graph.adj_list.values.map(&:size).inject(0, &:+)}"
    reduced_condensed = condensed_graph.step_reduction

    sccs = scc
    scc_map = {}
    sccs.each_with_index { |scc, idx|
      scc_map["SCC#{idx}"] = scc
    }

    uncondensed = condensed_graph.uncondensation(self, scc_map)
    $stderr.puts "Uncondensed vertices: #{uncondensed.adj_list.size}"
    $stderr.puts "Uncondensed edges: #{uncondensed.adj_list.values.map(&:size).inject(0, &:+)}"
    uncondensed.step_reduction
  end

  def transitive_closure
    closure_graph = Graph.new
    @adj_list.keys.each do |vertex|
      visited = Hash.new(false)
      reachable = []
      closure_dfs(vertex, visited, reachable)
      closure_graph.adj_list[vertex] = Set.new reachable
    end
    closure_graph
  end

  def closure_dfs(vertex, visited, reachable)
    visited[vertex] = true
    @adj_list[vertex].each do |neighbor|
      unless reachable.include?(neighbor)
        reachable << neighbor
      end
      closure_dfs(neighbor, visited, reachable) unless visited[neighbor]
    end
  end

  # Should only be used on condensed graphs
  def step_reduction
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

        reachable = step_reduction_dfs(u, v, reduced_graph)
        reduced_graph.add_edge(u, v) unless reachable # Re-add the edge if v is not reachable
      }
    }

    reduced_graph
  end

  def step_reduction_dfs(start, goal, graph, visited = Set.new)
    return true if start == goal
    return false if visited.include?(start)

    visited.add(start)
    graph.adj_list[start].each { |neighbor|
      return true if step_reduction_dfs(neighbor, goal, graph, visited)
    }

    false
  end

  def print_graph
    adj_list.each do |u, neighbors|
      neighbors.each do |v|
        puts "#{u},#{v}" unless u == v
      end
    end
  end
end

if __FILE__ == $0
  graph = Graph.new
  File.read(ARGV[0]).split("\n").each { |s|
    a,b = s.split(",")
    graph.add_edge(a.to_i, b.to_i)
  }

  min_graph = graph.transitive_reduction
  min_graph.print_graph
end

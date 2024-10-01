# Replace auto-generated sorry's with a proof by implication traversal

if ARGV.length != 2
  $stderr.puts "Usage: <lean file> <reduced graph>"
  exit 1
end

class Graph
  attr_accessor :adj_list

  def initialize
    @adj_list = Hash.new { |h, k| h[k] = Set.new([]) }
  end

  def add_edge(u, v)
    @adj_list[u] << v
  end

  def bfs(start, goal)
    # Initialize a queue for BFS and a hash to track visited nodes
    queue = [[start]] # Each element is a path
    visited = { start => true } # Track visited nodes

    while queue.any?
      # Dequeue the first path
      path = queue.shift
      node = path.last

      # Check if we reached the goal
      return path if node == goal

      # Explore each neighbor of the current node
      @adj_list[node].each do |neighbor|
        unless visited[neighbor]
          visited[neighbor] = true
          # Create a new path that includes the neighbor
          new_path = path + [neighbor]
          queue << new_path # Enqueue the new path
        end
      end
    end

    nil # Return nil if no path is found
  end
end

graph = Graph.new
File.read(ARGV[1]).split("\n").each { |s|
  a,b = s.split(",")
  graph.add_edge(a.to_i, b.to_i)
}

equation_to_namespace = {}
Dir["equational_theories/**/*.lean"].each { |path|
  cur_namespace = nil
  File.open(path) { |f|
    while f.gets
      if $_ =~ /namespace (.+)/
        cur_namespace = $1
      elsif $_ =~ /theorem (Equation\d+_implies_Equation\d+)/
        equation_to_namespace[$1] = cur_namespace
      end
    end
  }
}

File.open(ARGV[0]) { |f|
  puts <<-END
import equational_theories.Generated.SimpleRewrites
import equational_theories.Generated.Constant
import equational_theories.Generated.Singleton
import equational_theories.Generated.TrivialBruteforce
import equational_theories.Generated.FinitePoly
import equational_theories.Subgraph
END
  cur_theorem = nil
  while f.gets
    if $_ =~ /^theorem Equation(\d+)_implies_Equation/
      puts "@[equational_result]"
      cur_theorem = $1.to_i
    end

    if $_ =~ /have eq(\d+) (.+) := by sorry/
      path = graph.bfs(cur_theorem, $1.to_i)
      if !path
        $stderr.puts "Failed to find path? #{path}"
        exit 1
      end

      #puts "  /- #{path.inspect} -/"
      puts "  have eq#{$1.to_i} #{$2} := by"

      last_node = path[0]
      path[0, path.length-1].each_with_index { |h, i|
        eqname = "Equation#{h}_implies_Equation#{path[i+1]}"
        namespace = equation_to_namespace[eqname]
        if !namespace
          $stderr.puts "Missing namespace for #{eqname}"
          exit 1
        end
        puts "    apply #{namespace}.#{eqname} at h"
      }
      puts "    apply h"

    else
      puts $_
    end
  end
}

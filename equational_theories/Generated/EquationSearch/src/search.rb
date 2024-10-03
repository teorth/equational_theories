# Very rudimentary equational reasoning based on direct string substitution. By
# consuming the graph of known implications, we can 'reason' from a given hypothesis
# by performing legal substitutions.
#
# This tools searches by equivalence class/strongly-connected component in the implication
# graph. It picks an SCC as a hypothesis, searches outwards from all goals and hypotheses
# in that SCC to see if they meet in the middle somewhere. This has the advantage of allowing
# the search depth to be adjusted based on the sizes of the hypothesis SCC/goal list.
#
# Inspired by the following proof:
# theorem Equation387_implies_Equation43 (G: Type*) [Magma G] (h: Equation387 G) : Equation43 G := by
#   have idem (x : G) : (x ◇ x) ◇ (x ◇ x) = (x ◇ x) := by rw [← h, ← h]
#   have comm (x y : G) : (x ◇ x) ◇ y = y ◇ (x ◇ x) := by rw [← idem, ← h, idem]
#   have op_idem (x y : G) : (x ◇ x) ◇ (y ◇ y) = x ◇ y := by rw [← h, ← h]
#   exact fun _ _ ↦ by rw [← op_idem, comm, op_idem]
#
#  Equation 43: x ◇ y = y ◇ x
#  Equation 387: x ◇ y = (y ◇ y) ◇ x
#
#  Equation 3659: x ◇ x = (x ◇ x) ◇ (x ◇ x)
#  Equation 4482: (x ◇ x) ◇ y = y ◇ (x ◇ x)
#  Equation 3715: x ◇ y = (x ◇ x) ◇ (y ◇ y)

# Generate all possible rebinding permutatuions, e.g. x ◇ y -> z ◇ w and add them to the search
# space. Reaches new proofs, at the cost of a large increase in the search space.
GENERATE_PERMUTATIONS = true
# Match sub-expressions of the LHS/RHS and not just the entire LHS/RHS. Only does so for a subset of
# all possible substitutions.
SUB_EXPR_MATCHING = true
TOTAL_SEARCH_DEPTH = 4
BRANCHING_FACTOR = 50          # TODO: Actually measure this

# Go above what's in equational to allow equations with 4 operations on one side and 3 on the other.
SEARCH_MAX_EQUATION_OPERATIONS_ALLOWED = 9
SEARCH_MAX_EXPR_OPERATIONS_ALLOWED = 5


require File.join(__dir__, '../../../../scripts/graph')

STRICT_ERROR_CHECKING=true
VERBOSE = false
ALL_VARIABLES = ['x','y','z','w','u','v']
VAR_NAMES = 'xyzwuv'
# TODO: Could just be an array access
VAR_NAME_TO_IDX = { "x" => 0, "y" => 1, "z" => 2, "w" => 3, "u" => 4, "v" => 5 }

def for_each_subexpr(str)
  subexpr_start = []
  str.length.times { |i|
    if str[i] == '('
      subexpr_start.push(i+1)
    elsif str[i] == ')'
      start_of_expr = subexpr_start.pop
      yield(start_of_expr, i)
    end
  }
end

def expr_variables(expr)
  vars = ""
  expr.split('').uniq & ALL_VARIABLES
end

def expr_operations(expr)
  expr.count("◇")
end

# Replacing an expression on the LHS or RHS could require changing variables names on one (or both) sides.
def rebind(lhs, rhs, left, next_expr)
  # We could modify these later and don't want to modify the callers
  lhs = lhs.dup
  rhs = rhs.dup
  next_expr = next_expr.dup

  lhs_vars = expr_variables(lhs)
  rhs_vars = expr_variables(rhs)
  next_expr_vars = expr_variables(next_expr)

  if left
    # Do this to support `x op y -> y op y` and `x op y op z -> x op z op x`
    binding_table = {}
    binding_table_free_idx = 0
    next_expr.length.times { |i|
      if next_expr[i] == '(' || next_expr[i] == ')' || next_expr[i] == ' ' || next_expr[i] == '◇'
        next
      else
        var_idx = VAR_NAME_TO_IDX[next_expr[i]]
        if !binding_table[var_idx]
          binding_table[var_idx] = binding_table_free_idx
          binding_table_free_idx += 1
          if binding_table_free_idx > 5
            return [nil, nil]
          end
        end

        next_expr[i] = VAR_NAMES[binding_table[var_idx]]
      end
    }

    max_bound_variable = [lhs_vars.length, next_expr_vars.length].min
    next_free_idx = next_expr_vars.length
    free_map = {}

    rhs.length.times { |i|
      if rhs[i] == '(' || rhs[i] == ')' || rhs[i] == ' ' || rhs[i] == '◇'
        next
      else
        var_idx = VAR_NAME_TO_IDX[rhs[i]]
        if binding_table[var_idx] && lhs_vars.include?(rhs[i])
          rhs[i] = VAR_NAMES[binding_table[var_idx]]
          var_idx = VAR_NAME_TO_IDX[rhs[i]]
        else
          if !free_map[var_idx]
            free_map[var_idx] = next_free_idx
            next_free_idx += 1
            if next_free_idx > 5
              return [nil, nil]
            end
          end

          rhs[i] = VAR_NAMES[free_map[var_idx]]
        end
      end
    }

    return [next_expr, rhs]
  else
    next_free_idx = lhs_vars.length
    free_map = {}

    next_expr.length.times { |i|
      if next_expr[i] == '(' || next_expr[i] == ')' || next_expr[i] == ' ' || next_expr[i] == '◇'
        next
      else
        var_idx = VAR_NAME_TO_IDX[next_expr[i]]
        if !lhs_vars.include?(next_expr[i]) || !rhs_vars.include?(next_expr[i])
          if !free_map[var_idx]
            free_map[var_idx] = next_free_idx
            next_free_idx += 1
            if next_free_idx > 5
              return [nil, nil]
            end
          end

          next_expr[i] = VAR_NAMES[free_map[var_idx]]
        end
      end
    }

    return [lhs, next_expr]
  end
end

raise "Error" unless rebind("x ◇ x", "(x ◇ y) ◇ z", true, "x ◇ y")[1] == "(x ◇ z) ◇ w"
raise "Error" unless rebind("x ◇ y", "(x ◇ z) ◇ w", true, "x ◇ x")[1] == "(x ◇ y) ◇ z"
raise "Error" unless rebind("x ◇ y", "(x ◇ y) ◇ z", true, "x ◇ x")[1] == "(x ◇ y) ◇ z"
raise "Error" unless rebind("x ◇ y", "y ◇ (x ◇ z)", true, "(x ◇ x) ◇ (y ◇ z)")[1] == "y ◇ (x ◇ w)"
raise "Error" unless rebind("x ◇ y", "(z ◇ y) ◇ x", true, "((x ◇ y) ◇ x) ◇ x")[1] == "(z ◇ y) ◇ x"
raise "Error" unless rebind("x ◇ y", "y ◇ (x ◇ z)", true, "y ◇ y") == ['x ◇ x', 'x ◇ (y ◇ z)']
raise "Error" unless rebind("x ◇ (y ◇ z)", "(z ◇ w) ◇ x", true, "(x ◇ z) ◇ x") == ["(x ◇ y) ◇ x", "(y ◇ z) ◇ x"]
raise "Error" unless rebind("x ◇ (y ◇ x)", "(x ◇ z) ◇ x", true, "y ◇ (z ◇ y)") == ["x ◇ (y ◇ x)", "(z ◇ w) ◇ z"]
raise "Error" unless rebind("x ◇ (y ◇ z)", "(y ◇ w) ◇ y", true, "x ◇ (y ◇ x)") == ["x ◇ (y ◇ x)", "(y ◇ z) ◇ y"]
raise "Error" unless rebind("x ◇ (y ◇ x)", "(y ◇ z) ◇ y", true, "y ◇ (z ◇ y)") == ["x ◇ (y ◇ x)", "(x ◇ z) ◇ x"]

raise "Error" unless rebind("x ◇ y", "(x ◇ y) ◇ z", false, "x ◇ y") == ["x ◇ y", "x ◇ y"]
raise "Error" unless rebind("x ◇ y", "(x ◇ y) ◇ z", false, "y") == ["x ◇ y", "y"]
raise "Error" unless rebind("x ◇ y", "x", false, "x ◇ y") == ["x ◇ y", "x ◇ z"]
raise "Error" unless rebind("x ◇ y", "(x ◇ y) ◇ z", false, "x ◇ w") == ["x ◇ y", "x ◇ z"]
raise "Error" unless rebind("x", "(x ◇ x) ◇ y", false, "(x ◇ z) ◇ y") == ["x", "(x ◇ y) ◇ z"]

def permutations_recurse(lhs, rhs, decl_vars, unbound_vars, binding, &block)
  if decl_vars.length == 0
    new_lhs, new_rhs = lhs.dup, rhs.dup
    new_lhs.length.times { |i| new_lhs[i] = binding[new_lhs[i]] if binding[new_lhs[i]] }
    new_rhs.length.times { |i| new_rhs[i] = binding[new_rhs[i]] if binding[new_rhs[i]] }
    block.call(new_lhs, new_rhs)
    return
  end

  var = decl_vars[0]
  unbound_vars.each { |new_var|
    binding[var] = new_var

    permutations_recurse(lhs, rhs, decl_vars[1, decl_vars.length - 1], unbound_vars, binding, &block)

    binding.delete(var)
  }
end

def expr_permutations(lhs, rhs, &block)
  variables = (expr_variables(lhs) + expr_variables(rhs)).uniq

  permutations_recurse(lhs, rhs, variables, ALL_VARIABLES, {}, &block)
end

def read_csv(filename)
  graph = {}
  File.open(filename) { |f|
    while f.gets
      a,b = $_.split(",")
      graph[a.to_i] ||= Hash.new()
      graph[a.to_i][b.to_i] = true
    end
  }

  graph
end

if ARGV.length != 2
  $stderr.puts "Usage: search <closure> <refutations>"
  exit 1
end

$equations_num_to_str = {}
$equations_str_to_num = {}
equations_file = File.read(File.join(__dir__, "../../../AllEquations.lean"))

equations_file.split("\n").each { |s|
  if s =~ /equation (\d+) := (.+)/
    num = $1.to_i
    eq = $2.gsub(/^\s+/, "").gsub(/\s+$/, "")

    # Whitespace could be bad, make sure we trim.
    $equations_num_to_str[num] = eq
    $equations_str_to_num[eq] = num
  end
}

$implies = Graph.from_csv(ARGV[0])
$not_implies = Graph.from_csv(ARGV[1])

2.upto(4694) { |n| $implies.add_edge(n, 1) }
2.upto(4694) { |n| $implies.add_edge(n, n) }

$expressions = {}
$equations_num_to_str.each { |num, str|
  lhs, rhs = str.split(" = ")

  lhs_vars = expr_variables(lhs)
  rhs_vars = expr_variables(rhs)

  $expressions[lhs] ||= Set.new
  $expressions[lhs] << { num: num, left: true, expr: rhs }

  $expressions[rhs] ||= Set.new
  $expressions[rhs] << { num: num, left: false, expr: lhs }

  if GENERATE_PERMUTATIONS
    expr_permutations(lhs, rhs) { |perm_lhs, perm_rhs|
      $expressions[perm_lhs] ||= Set.new
      $expressions[perm_lhs] << { num: num, left: true, expr: perm_rhs }

      $expressions[perm_rhs] ||= Set.new
      $expressions[perm_rhs] << { num: num, left: false, expr: perm_lhs }
    } if lhs.length == 1 && rhs.length == 1
  end
}

# TODO: Have a locally filtered @implies here that gets rid of anything this search doesn't need.
class Search
  PATH_TYPE_END = -3
  PATH_TYPE_START = -2
  PATH_TYPE_SYMM = -1
  PATH_TYPE_SUBSTITUTION = 0

  def initialize(hypothesis_scc)
    @hypothesis_scc = hypothesis_scc

    @refuted_by = Set.new []
    ($implies.adj_list.keys - @hypothesis_scc).each { |k|
      if ($not_implies.adj_list[k] & @hypothesis_scc).length != 0
        @refuted_by << k
      end
    }

    @refutes = Set.new []
    @hypothesis_scc.each { |v| @refutes += $not_implies.adj_list[v] }

    @goals = $implies.adj_list.keys - (@refutes + $implies.adj_list[@hypothesis_scc.to_a[0]]).to_a

    @implied_expressions = {}
    $expressions.each { |expr, set|
      set.each { |repl_expr|
        if $implies.adj_list[hypothesis_scc[0]].include?(repl_expr[:num])
          @implied_expressions[expr] ||= Set.new []
          @implied_expressions[expr] << repl_expr
        end
      }
    }

    @best_proof = {}
  end

  def already_proven
    return @goals.length == 0
  end

  def search
    # Calculate optimal search depth from both sides.
    fewer_goal_steps = Math.log(@goals.length.to_f / @hypothesis_scc.length) / Math.log(BRANCHING_FACTOR)
    goal_depth = [TOTAL_SEARCH_DEPTH/2.0 - fewer_goal_steps, 0].max.round
    hypothesis_depth = TOTAL_SEARCH_DEPTH - goal_depth

    $stderr.puts "SCC size: #{@hypothesis_scc.length}  SCC element: #{@hypothesis_scc.sort[0]}  Implies: #{$implies.adj_list[@hypothesis_scc[0]].length}  Refuted by: #{@refuted_by.length}  Refutes: #{@refutes.length}  Goals: #{@goals.length}  Goal depth: #{goal_depth}  Hypothesis depth: #{hypothesis_depth}"

    @visited = {}
    @goals.each { |goal|
      __search(*$equations_num_to_str[goal].split(" = "), [ [ PATH_TYPE_END, goal ] ], goal_depth, true)
    }

    @hypothesis_scc.each { |hypothesis|
      __search(*$equations_num_to_str[hypothesis].split(" = "), [ [ PATH_TYPE_START, hypothesis ] ], hypothesis_depth, false)
    }
    @visited = {}
  end

  def print_best_proofs
    @best_proof.each { |proved_eq, path|
      hypothesis_eq = path[0][1]
      puts <<-END
/- #{path.inspect} -/
theorem Equation#{hypothesis_eq}_implies_Equation#{proved_eq} (G: Type _) [Magma G] (h: Equation#{hypothesis_eq} G) : Equation#{proved_eq} G := by
END

      seen_eq = {}
      path.reverse.each { |path_type, eq_num|
        next if path_type != PATH_TYPE_SUBSTITUTION
        next if eq_num == hypothesis_eq || seen_eq[eq_num]
        seen_eq[eq_num] = true

        vars = expr_variables($equations_num_to_str[eq_num])
        puts "  have eq#{eq_num} (#{vars.join(" ")} : G) : #{$equations_num_to_str[eq_num]} := by sorry"
      }
      puts "  intro " + expr_variables($equations_num_to_str[proved_eq]).join(" ")

      path.reverse.each { |path_element|
        path_type = path_element[0]
        if path_type == PATH_TYPE_SYMM
          puts "  symm"
          next
        elsif path_type == PATH_TYPE_START || path_type == PATH_TYPE_END
          next
        end

        eq_num, expr_left, eq_left = *path_element[1,3]

        puts "  symm" if !eq_left

        direction_str = ""
        if expr_left
          direction_str = "← "
        end
        if eq_num != hypothesis_eq
          puts "  nth_rewrite 1 [#{direction_str}eq#{eq_num}]"
        else
          puts "  nth_rewrite 1 [#{direction_str}h]"
        end

        puts "  symm" if !eq_left
      }
      puts "  apply h"
      puts "  repeat assumption"
    }
  end

  private

  def reverse_goal_path(path)
    path.reverse.map { |path_elements|
      if path_elements[0] == PATH_TYPE_SUBSTITUTION
        # Flip expr_left
        [ path_elements[0], path_elements[1], path_elements[2] ^ 1, path_elements[3] ]
      else
        path_elements
      end
    }
  end

  def add_proof(eq_num, path)
    if !@best_proof[eq_num] || @best_proof[eq_num].length > path.length
      @best_proof[eq_num] = path
      return true
    end
  end

  def __search(lhs, rhs, path, depth, is_goal_search)
    return if lhs == rhs

    lhs_ops = expr_operations(lhs)
    rhs_ops = expr_operations(rhs)
    return if (lhs_ops + rhs_ops) > SEARCH_MAX_EQUATION_OPERATIONS_ALLOWED || lhs_ops > SEARCH_MAX_EXPR_OPERATIONS_ALLOWED || rhs_ops > SEARCH_MAX_EXPR_OPERATIONS_ALLOWED

    combined_eq = "#{lhs} = #{rhs}"
    reverse_eq = "#{rhs} = #{lhs}"

    if VERBOSE
      $stderr.puts "At #{combined_eq} path=#{path.inspect} lhs_num=#{(@implied_expressions[lhs] || []).length} rhs_num=#{(@implied_expressions[rhs] || []).length} (goal_search=#{is_goal_search})"
    end

    if STRICT_ERROR_CHECKING
      combined_eq_num = $equations_str_to_num[combined_eq]
      reverse_eq_num = $equations_str_to_num[reverse_eq]
      if !is_goal_search && (combined_eq_num && @refutes.include?(combined_eq_num)) ||
          (reverse_eq_num && @refutes.include?(reverse_eq_num))

        $stderr.puts "ERROR ! non-implied equation reached: #{path}: #{lhs} = #{rhs}"
        exit 1
      elsif is_goal_search && (combined_eq_num && @refutes.include?(combined_eq_num)) ||
          (reverse_eq_num && @refutes.include?(reverse_eq_num))
        $stderr.puts "WARNING! Found refutation? #{@hypothesis_scc.inspect}->#{combined_eq_num}/#{reverse_eq_num}: #{path.inspect}"
      end
    end

    if is_goal_search
      # TODO: We shouldn't overwrite here in case we can discover multiple goals at one node.
      @visited[combined_eq] = path if !@visited[combined_eq] || path.length < @visited[combined_eq].length
    else
      if @visited[combined_eq]
        if @visited[combined_eq].class == Integer
          # We've visited this node on this side of the search
          return if @visited[combined_eq] > depth
          @visited[combined_eq] = depth if depth > 1
        else
          combined_eq_num = $equations_str_to_num[combined_eq]
          goal_path = @visited[combined_eq]
          if add_proof(goal_path[0][1], path + reverse_goal_path(goal_path))
            $stderr.puts "Found proof for #{path[0][1]}->#{goal_path[0][1]} #{path.inspect} -> #{goal_path.inspect}"
          end

          return
        end
      else
        @visited[combined_eq] = depth
      end

      if @visited[reverse_eq]
        if @visited[reverse_eq].class == Array
          path << [PATH_TYPE_SYMM]
          reverse_eq_num = $equations_str_to_num[reverse_eq]
          goal_path = @visited[reverse_eq]
          if add_proof(goal_path[0][1], path + reverse_goal_path(goal_path))
            $stderr.puts "Found (reverse) proof for #{path[0][1]}->#{goal_path[0][1]} #{path.inspect} #{goal_path.inspect}"
          end

          return
        end
      end
    end

    return if depth <= 0

    handle_expr = lambda { |expr, left|
      if @implied_expressions[expr]
        @implied_expressions[expr].each { |expr_info|
          if VERBOSE
            $stderr.puts "  hit left=#{left} eq=#{expr_info[:num]} expr=#{expr_info[:expr]} [from #{$equations_num_to_str[expr_info[:num]]}]"
          end

          next_lhs = lhs
          next_rhs = rhs
          need_to_rebind = false
          if left
            next_lhs = expr_info[:expr]

            if expr_variables(lhs) != expr_variables(expr_info[:expr])
              added_vars = expr_variables(expr_info[:expr]) - expr_variables(lhs)
              removed_vars = expr_variables(lhs) - expr_variables(expr_info[:expr])

              # Requires rebinding
              if removed_vars != [] || (added_vars & expr_variables(rhs)) != []
                next_lhs, next_rhs = rebind(lhs, rhs, true, expr_info[:expr])
                return if !next_lhs
              end
            end
          else
            next_rhs = expr_info[:expr]
            if expr_variables(rhs) != expr_variables(expr_info[:expr])
              added_vars = expr_variables(expr_info[:expr]) - expr_variables(rhs)
              removed_vars = expr_variables(rhs) - expr_variables(expr_info[:expr])

              # Requires rebinding
              if (removed_vars & expr_variables(lhs)) != removed_vars || added_vars != []
                next_lhs, next_rhs = rebind(lhs, rhs, false, expr_info[:expr])
                return if !next_lhs
              end

            end
          end

          __search(next_lhs, next_rhs, path + [[ PATH_TYPE_SUBSTITUTION, expr_info[:num], expr_info[:left], left ]], depth-1, is_goal_search)
        }
      end

      if SUB_EXPR_MATCHING
        for_each_subexpr(expr) { |left_idx, right_idx|
          subexpr = expr[left_idx, right_idx - left_idx]

          @implied_expressions[subexpr].each { |expr_info|
            # No complex rebinding
            next if expr_variables(subexpr) != expr_variables(expr_info[:expr])

            if VERBOSE
              $stderr.puts "  sub-expr hit left=#{left} #{expr_info[:num]} #{expr_info[:expr]} [from #{$equations_num_to_str[expr_info[:num]]}] subexpr = #{subexpr}"
            end

            next_lhs, next_rhs = nil, nil
            if left
              if expr_info[:expr].length == 1
                # (x+x) -> x not (x)
                next_lhs = lhs[0,left_idx-1] + expr_info[:expr] + lhs[right_idx+1,lhs.length]
              else
                next_lhs = lhs[0,left_idx] + expr_info[:expr] + lhs[right_idx,lhs.length]
              end
              next_rhs = rhs.dup
            else
              if expr_info[:expr].length == 1
                next_rhs = rhs[0,left_idx-1] + expr_info[:expr] + rhs[right_idx+1,rhs.length]
              else
                next_rhs = rhs[0,left_idx] + expr_info[:expr] + rhs[right_idx,rhs.length]
              end
              next_lhs = lhs.dup
            end

            __search(next_lhs, next_rhs, path + [[ PATH_TYPE_SUBSTITUTION, expr_info[:num], expr_info[:left], left ]], depth-1, is_goal_search)
          } if @implied_expressions[subexpr]
        }
      end
    }

    handle_expr.call(lhs, true)
    handle_expr.call(rhs, false)
  end
end

puts <<-END
/- GENERATE_PERMUTATIONS = #{GENERATE_PERMUTATIONS} -/
/- SUB_EXPR_MATCHING = #{SUB_EXPR_MATCHING} -/
/- TOTAL_SEARCH_DEPTH = #{TOTAL_SEARCH_DEPTH} -/
/- BRANCHING_FACTOR = #{BRANCHING_FACTOR} -/
/- SEARCH_MAX_EQUATION_OPERATIONS_ALLOWED = #{SEARCH_MAX_EQUATION_OPERATIONS_ALLOWED} -/
/- SEARCH_MAX_EXPR_OPERATIONS_ALLOWED = #{SEARCH_MAX_EXPR_OPERATIONS_ALLOWED} -/
END

puts "import equational_theories.AllEquations"
puts "import Mathlib.Tactic"

$implies.scc.sort_by { |scc| scc.length }.reverse.each { |scc|
  search = Search.new(scc)

  next if search.already_proven

  search.search
  search.print_best_proofs
}

# Inspired by the following proof:
# theorem Equation387_implies_Equation43 (G: Type*) [Magma G] (h: Equation387 G) : Equation43 G := by
#   have idem (x : G) : (x ∘ x) ∘ (x ∘ x) = (x ∘ x) := by rw [← h, ← h]
#   have comm (x y : G) : (x ∘ x) ∘ y = y ∘ (x ∘ x) := by rw [← idem, ← h, idem]
#   have op_idem (x y : G) : (x ∘ x) ∘ (y ∘ y) = x ∘ y := by rw [← h, ← h]
#   exact fun _ _ ↦ by rw [← op_idem, comm, op_idem]
#
#  Equation 43: x ∘ y = y ∘ x
#  Equation 387: x ∘ y = (y ∘ y) ∘ x
#
#  Equation 3659: x ∘ x = (x ∘ x) ∘ (x ∘ x)
#  Equation 4482: (x ∘ x) ∘ y = y ∘ (x ∘ x)
#  Equation 3715: x ∘ y = (x ∘ x) ∘ (y ∘ y)

# Turning these on increases the number of finds but blows-up the search space.
GENERATE_PERMUTATIONS = true
SUB_EXPR_MATCHING = true
SEARCH_DEPTH = 3

# Go above what's in equational to allow equations with 4 operations on one side and 3 on the other.
SEARCH_MAX_EQUATION_OPERATIONS_ALLOWED = 7
SEARCH_MAX_EXPR_OPERATIONS_ALLOWED = 4



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
      yield(str[start_of_expr, i - start_of_expr])
    end
  }
end

def expr_variables(expr)
  vars = ""
  expr.split('').uniq & ALL_VARIABLES
end

def expr_operations(expr)
  expr.count("∘")
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
      if next_expr[i] == '(' || next_expr[i] == ')' || next_expr[i] == ' ' || next_expr[i] == '∘'
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
      if rhs[i] == '(' || rhs[i] == ')' || rhs[i] == ' ' || rhs[i] == '∘'
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
              return nil
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
      if next_expr[i] == '(' || next_expr[i] == ')' || next_expr[i] == ' ' || next_expr[i] == '∘'
        next
      else
        var_idx = VAR_NAME_TO_IDX[next_expr[i]]
        if !lhs_vars.include?(next_expr[i]) || !rhs_vars.include?(next_expr[i])
          if !free_map[var_idx]
            free_map[var_idx] = next_free_idx
            next_free_idx += 1
            if next_free_idx > 5
              return nil
            end
          end

          next_expr[i] = VAR_NAMES[free_map[var_idx]]
        end
      end
    }

    return [lhs, next_expr]
  end
end

raise "Error" unless rebind("x ∘ x", "(x ∘ y) ∘ z", true, "x ∘ y")[1] == "(x ∘ z) ∘ w"
raise "Error" unless rebind("x ∘ y", "(x ∘ z) ∘ w", true, "x ∘ x")[1] == "(x ∘ y) ∘ z"
raise "Error" unless rebind("x ∘ y", "(x ∘ y) ∘ z", true, "x ∘ x")[1] == "(x ∘ y) ∘ z"
raise "Error" unless rebind("x ∘ y", "y ∘ (x ∘ z)", true, "(x ∘ x) ∘ (y ∘ z)")[1] == "y ∘ (x ∘ w)"
raise "Error" unless rebind("x ∘ y", "(z ∘ y) ∘ x", true, "((x ∘ y) ∘ x) ∘ x")[1] == "(z ∘ y) ∘ x"
raise "Error" unless rebind("x ∘ y", "y ∘ (x ∘ z)", true, "y ∘ y") == ['x ∘ x', 'x ∘ (y ∘ z)']
raise "Error" unless rebind("x ∘ (y ∘ z)", "(z ∘ w) ∘ x", true, "(x ∘ z) ∘ x") == ["(x ∘ y) ∘ x", "(y ∘ z) ∘ x"]
raise "Error" unless rebind("x ∘ (y ∘ x)", "(x ∘ z) ∘ x", true, "y ∘ (z ∘ y)") == ["x ∘ (y ∘ x)", "(z ∘ w) ∘ z"]
raise "Error" unless rebind("x ∘ (y ∘ z)", "(y ∘ w) ∘ y", true, "x ∘ (y ∘ x)") == ["x ∘ (y ∘ x)", "(y ∘ z) ∘ y"]
raise "Error" unless rebind("x ∘ (y ∘ x)", "(y ∘ z) ∘ y", true, "y ∘ (z ∘ y)") == ["x ∘ (y ∘ x)", "(x ∘ z) ∘ x"]

raise "Error" unless rebind("x ∘ y", "(x ∘ y) ∘ z", false, "x ∘ y") == ["x ∘ y", "x ∘ y"]
raise "Error" unless rebind("x ∘ y", "(x ∘ y) ∘ z", false, "y") == ["x ∘ y", "y"]
raise "Error" unless rebind("x ∘ y", "x", false, "x ∘ y") == ["x ∘ y", "x ∘ z"]
raise "Error" unless rebind("x ∘ y", "(x ∘ y) ∘ z", false, "x ∘ w") == ["x ∘ y", "x ∘ z"]
raise "Error" unless rebind("x", "(x ∘ x) ∘ y", false, "(x ∘ z) ∘ y") == ["x", "(x ∘ y) ∘ z"]

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

    permutations_recurse(lhs, rhs, decl_vars[1, decl_vars.length - 1], unbound_vars - [new_var], binding, &block)

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

$implies = read_csv(ARGV[0])
$not_implies = read_csv(ARGV[1])

2.upto(4694) { |n|
  $implies[n] ||= {}
  $implies[n][n] = true
  $not_implies[n] ||= {}
}

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
    }
  end
}

class Search
  def initialize(target_equation)
    @target_equation = target_equation

    if !$equations_num_to_str[@target_equation]
      $stderr.puts "Bad target equation #{@target_equation}"
      exit 1
    end

    unproven_arr = 2.upto(4694).to_a - ($implies[@target_equation].keys + $not_implies[@target_equation].keys)
    unproven_arr -= [@target_equation]
    @unproven_hash = {}
    unproven_arr.each { |n| @unproven_hash[n] = true }

    @best_proof = {}
    @visited = {}
  end

  def already_proven
    return @unproven_hash.length == 0
  end

  def search(max_depth)
    __search(*$equations_num_to_str[@target_equation].split(" = "), [], max_depth)
  end

  def print_best_proofs
    @best_proof.each { |proved_eq, path|
      puts <<-END
/- #{path.inspect} -/
theorem Equation#{@target_equation}_implies_Equation#{proved_eq} (G: Type _) [Magma G] (h: Equation#{@target_equation} G) : Equation#{proved_eq} G := by
END
      path.reverse.map { |eq_num, left| eq_num }.uniq.each { |eq_num|
        next if eq_num == @target_equation
        vars = expr_variables($equations_num_to_str[eq_num])
				puts "  have eq#{eq_num} (#{vars.join(" ")} : G) : #{$equations_num_to_str[eq_num]} := by sorry"
			}
      puts "  intro " + expr_variables($equations_num_to_str[proved_eq]).join(" ")

      path.reverse.each { |eq_num, expr_left, eq_left|
        puts "  symm" if !eq_left

        direction_str = ""
        if expr_left
          direction_str = "← "
        end
        if eq_num != @target_equation
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

  def __search(lhs, rhs, path, max_depth)
    lhs_ops = expr_operations(lhs)
    rhs_ops = expr_operations(rhs)
    return if (lhs_ops + rhs_ops) > SEARCH_MAX_EQUATION_OPERATIONS_ALLOWED || lhs_ops > SEARCH_MAX_EXPR_OPERATIONS_ALLOWED || rhs_ops > SEARCH_MAX_EXPR_OPERATIONS_ALLOWED

    # TODO: This is very naive, optimize
    visited_idx = [lhs, rhs]
    if lhs.length > rhs.length
      visited_idx = [rhs, lhs]
    end
    return if @visited[visited_idx] && @visited[visited_idx] > max_depth
    @visited[visited_idx] = max_depth

    combined_eq = "#{lhs} = #{rhs}"
    combined_eq_num = $equations_str_to_num[combined_eq]
    reverse_eq = "#{rhs} = #{lhs}"
    reverse_eq_num = $equations_str_to_num[reverse_eq]

    if VERBOSE
      $stderr.puts "At #{combined_eq} (eq #{combined_eq_num}) path=#{path.inspect} lhs_num=#{($expressions[lhs] || []).length} rhs_num=#{($expressions[rhs] || []).length} by hypothesis #{@target_equation}"
    end

    if combined_eq_num && @unproven_hash[combined_eq_num]
      if !@best_proof[combined_eq_num] || @best_proof[combined_eq_num].length > path.length
        $stderr.puts "Found proof for #{@target_equation}->#{combined_eq_num} [#{$equations_num_to_str[@target_equation]} -> #{combined_eq}]: #{path.inspect}"
        @best_proof[combined_eq_num] = path
      end

      if $not_implies[@target_equation][combined_eq_num]
        $stderr.puts "ERROR ! non-implied equation reached"
        exit 1
      end

      # No need to search further here.
      # TODO is that true?
      return
    elsif reverse_eq_num && @unproven_hash[reverse_eq_num]
      $stderr.puts "WARNING: Found a reverse proof! Not being added in reverse form. #{@target_equation}->#{reverse_eq_num}: #{path.inspect}"
      # TODO: Support this case by outputting an extra symm at the end
    end

    return if lhs == rhs
    return if max_depth <= 0

    handle_expr = lambda { |expr, left|
			if $expressions[expr]
				$expressions[expr].each { |expr_info|
					next if !$implies[@target_equation][expr_info[:num]]

          if VERBOSE
            $stderr.puts "  hit left=#{left} #{expr_info[:num]} #{expr_info[:expr]} [from #{$equations_num_to_str[expr_info[:num]]}]"
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

          __search(next_lhs, next_rhs, path + [[ expr_info[:num], expr_info[:left], left ]], max_depth-1)
				}
			end

      if SUB_EXPR_MATCHING
        for_each_subexpr(expr) { |subexpr|
          # TODO: Doesn't properly handle redundant expressions e.g. (x+x)+(x+x), replaces the first subexpr twice
          return if !$expressions[subexpr]

          $expressions[subexpr].each { |expr_info|
            next if !$implies[@target_equation][expr_info[:num]]

            # Avoid complex rebinding
            next if expr_variables(subexpr) != expr_variables(expr_info[:expr])

            if VERBOSE
              $stderr.puts "  sub-expr hit left=#{left} #{expr_info[:num]} #{expr_info[:expr]} [from #{$equations_num_to_str[expr_info[:num]]}] subexpr = #{subexpr}"
            end

            next_lhs, next_rhs = lhs.dup, rhs.dup
            if left
              if expr_info[:expr].length == 1
                next_lhs.sub!("(" + subexpr + ")", expr_info[:expr])
              else
                next_lhs.sub!(subexpr, expr_info[:expr])
              end
            else
              if expr_info[:expr].length == 1
                next_rhs.sub!("(" + subexpr + ")", expr_info[:expr])
              else
                next_rhs.sub!(subexpr, expr_info[:expr])
              end
            end

            __search(next_lhs, next_rhs, path + [[ expr_info[:num], expr_info[:left], left ]], max_depth-1)
          }
        }
      end
		}

    handle_expr.call(lhs, true)
    handle_expr.call(rhs, false)
  end
end

puts "import equational_theories.AllEquations"
puts "import Mathlib.Tactic"

2.upto(4694).each { |eq_num|
  search = Search.new(eq_num)
  next if search.already_proven

  search.search(SEARCH_DEPTH)
  search.print_best_proofs
}

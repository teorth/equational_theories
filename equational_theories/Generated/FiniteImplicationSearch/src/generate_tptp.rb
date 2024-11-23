require 'optparse'
require 'open3'
require 'json'
require 'set'

FIND_EQUATION_ID = File.join(__dir__, '..', '..', '..', '..', 'scripts', 'find_equation_id.py')

# A fairly minimal set that I computed that were required to solve different finite implications
# up to order 4.
SIMPLE_BIJECTIONS = [
  ["eq3_surj_inj", "![X] : ?[T] : ( X = mul(T, T) ) => ![T1,T2] : ( (mul(T1, T1) = mul(T2, T2) ) => T1 = T2 )"],
  ["eq3_inj_surj", "![T1,T2] : ( (mul(T1, T1) = mul(T2, T2) ) => T1 = T2 ) => ![X] : ?[T] : ( X = mul(T, T) )"],
  ["eq4_surj_inj", "![X,Y] : ?[T] : ( X = mul(T, Y) ) => ![Y,T1,T2] : ( (mul(T1, Y) = mul(T2, Y) ) => T1 = T2 )"],
  ["eq4_inj_surj", "![Y,T1,T2] : ( (mul(T1, Y) = mul(T2, Y) ) => T1 = T2 ) => ![X,Y] : ?[T] : ( X = mul(T, Y) )"],
  ["eq5_surj_inj", "![X,Y] : ?[T] : ( X = mul(Y, T) ) => ![Y,T1,T2] : ( (mul(Y, T1) = mul(Y, T2) ) => T1 = T2 )"],
  ["eq5_inj_surj", "![Y,T1,T2] : ( (mul(Y, T1) = mul(Y, T2) ) => T1 = T2 ) => ![X,Y] : ?[T] : ( X = mul(Y, T) )"],
  ["eq8_surj_inj", "![X] : ?[T] : ( X = mul(T, mul(T, T)) ) => ![T1,T2] : ( (mul(T1, mul(T1, T1)) = mul(T2, mul(T2, T2)) ) => T1 = T2 )"],
  ["eq8_inj_surj", "![T1,T2] : ( (mul(T1, mul(T1, T1)) = mul(T2, mul(T2, T2)) ) => T1 = T2 ) => ![X] : ?[T] : ( X = mul(T, mul(T, T)) )"],
  ["eq11_surj_inj", "![X,Y] : ?[T] : ( X = mul(T, mul(Y, Y)) ) => ![Y,T1,T2] : ( (mul(T1, mul(Y, Y)) = mul(T2, mul(Y, Y)) ) => T1 = T2 )"],
  ["eq11_inj_surj", "![Y,T1,T2] : ( (mul(T1, mul(Y, Y)) = mul(T2, mul(Y, Y)) ) => T1 = T2 ) => ![X,Y] : ?[T] : ( X = mul(T, mul(Y, Y)) )"],
  ["eq23_surj_inj", "![X] : ?[T] : ( X = mul(mul(T, T), T) ) => ![T1,T2] : ( (mul(mul(T1, T1), T1) = mul(mul(T2, T2), T2) ) => T1 = T2 )"],
  ["eq23_inj_surj", "![T1,T2] : ( (mul(mul(T1, T1), T1) = mul(mul(T2, T2), T2) ) => T1 = T2 ) => ![X] : ?[T] : ( X = mul(mul(T, T), T) )"],
  ["eq31_surj_inj", "![X,Y] : ?[T] : ( X = mul(mul(Y, Y), T) ) => ![Y,T1,T2] : ( (mul(mul(Y, Y), T1) = mul(mul(Y, Y), T2) ) => T1 = T2 )"],
  ["eq31_inj_surj", "![Y,T1,T2] : ( (mul(mul(Y, Y), T1) = mul(mul(Y, Y), T2) ) => T1 = T2 ) => ![X,Y] : ?[T] : ( X = mul(mul(Y, Y), T) )"],
]

VARS = "XYZWUVRSTABCDEFGHIJKLMNOPQ"

def expr_repr(e)
  return VARS[e] if e.class == Integer
  return e if e.class == String    # Allow specifying custom expressions

  return "(#{expr_repr(e[0])} ◇ #{expr_repr(e[1])})"
end

def eq_repr(eq)
  "#{expr_repr(eq[0])} = #{expr_repr(eq[1])}"
end

# Map vars to bits
def expr_var_bitfield(e)
  [e].flatten.map { |i| 1 << i.to_i }.inject(0, &:|)
end

def subtree_replace(tree, subtree, newsubtree)
  return newsubtree if tree == subtree
  return tree if tree.class != Array
  
  [ subtree_replace(tree[0], subtree, newsubtree), subtree_replace(tree[1], subtree, newsubtree) ]
end

# Return one node up from the given subtree matches.
def subtree_search(tree, subtree)
  matches = []

  return [] if tree.class != Array

  if tree[0] == subtree
    matches << tree
  else
    matches = matches.concat(subtree_search(tree[0], subtree))
  end

  if tree[1] == subtree
    matches << tree
  else
    matches = matches.concat(subtree_search(tree[1], subtree))
  end

  matches
end

def leanify_eq(eq)
  "∀ " + eq.flatten.uniq.map { |x| VARS[x] }.join(" ") + " : G, " + eq_repr(eq)
end

def leanify_inverse(operation, inv_operation, inverted)
  src_lhs = inverted[0]
  str_operation = expr_repr operation
  str_inv_operation = expr_repr inv_operation

  proof = []
  proof << "  have REPLACE (" + inverted.flatten.uniq.map { |x| VARS[x] }.join(" ") + " : G) : " + expr_repr(inverted[1]) + " = " + expr_repr(inverted[0]) + " := by"
  if [src_lhs].flatten.length > 1
    proof << "    let S := {a | ∃ " + [inverted[0]].flatten.uniq.map { |x| VARS[x] }.join(" ") + " : G, " + expr_repr(inverted[0]) + " = a}"
  else
    proof << "    let S : Set G := Set.univ"
  end

  proof.push <<-END
    have m1 : S.MapsTo (fun s => #{str_operation}) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => #{str_inv_operation}) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => #{str_inv_operation}) (fun s => #{str_operation}) := by
      intro a ha
END
  if [src_lhs].flatten.length > 1
    proof << "      simp only [Set.mem_setOf_eq, S] at ha"
    proof << "      obtain ⟨" + [inverted[0]].flatten.uniq.map { |x| "abcdefghijkl"[x] }.join(", ") + ", rfl⟩ := ha"
  end
  proof.push <<-END
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
END

  proof.join("\n").gsub(/\n+/, "\n")
end

def expr2tptp(e, var_names)
  return var_names[e] if e.class == Integer
  return e if e.class == String
  raise "Unexpected! #{e}" if e.class != Array
  return "mul(#{expr2tptp(e[0], var_names)}, #{expr2tptp(e[1], var_names)})"
end
def eq2tptp(lhs, rhs, var_names)
  expr2tptp(lhs, var_names) + " = " + expr2tptp(rhs, var_names)
end
def tptp(eq, var_names=VARS)
  vars = eq.flatten.uniq
  "![" + vars.map { |v| var_names[v] }.join(",") + "] : " + eq2tptp(eq[0], eq[1], var_names)
end

def gen_sequences(num_vars, min_var=-1, prev=[], &block)
  return if num_vars == 0
  0.upto(min_var+1) { |l|
    cur = prev + [l]
    if num_vars == 1
      yield(cur)
    else
      gen_sequences(num_vars - 1, [min_var,l].max, cur, &block)
    end
  }
end

def gen_shapes(array)
  if array.length == 1
    yield array[0]
    return
  elsif array.length == 2
    yield array
    return
  end

  0.upto(array.length - 1) { |i|
    gen_shapes(array[0, i]) { |left|
      gen_shapes(array[i, array.length]) { |right|
        yield([left, right])
      }
    }
  }
end

def gen_exprs_upto(num_vars, min_var=-1, &block)
  1.upto(num_vars) { |i|
    gen_sequences(i, min_var) { |seq|
      gen_shapes(seq, &block)
    }
  }
end

def gen_equations(lhs_size, rhs_size, &block)
  counter = 0
  seen = {}

  gen_exprs_upto(lhs_size) { |lhs|
    gen_exprs_upto(rhs_size, 0) { |rhs|
      next if ![rhs].flatten.include?(0) # We want the LHS to be included
      next if [rhs].flatten.length == 1

      next if seen[[lhs, rhs]]
      seen[[lhs,rhs]]=true

      lhs_max_var = [lhs].flatten.max
      rhs_max_var = [rhs].flatten.max

      # Order matters here!
      rhs_max_var.downto(1) { |i|
        rhs = subtree_replace(rhs, i, lhs_max_var+i)
      }
      rhs = subtree_replace(rhs, 0, lhs)

      yield(counter, lhs, rhs)
      counter += 1
    }
  }
end

def gen_bij_tptp(lhs, rhs)
  return if lhs == rhs
  return if [lhs].flatten.length == 1 && [rhs].flatten.length == 1

  # TODO: Support LHS.length > 1
  raise "LHS length must be 1" if [lhs].flatten.length != 1

  surj_lhs = lhs
  surj_rhs = rhs

  inj1, inj2 = surj_rhs, surj_rhs
  inj_final_eq1, inj_final_eq2 = lhs, lhs

  [lhs].flatten.uniq.each { |chosen_lhs_var|
    surj_rhs = subtree_replace(surj_rhs, chosen_lhs_var, VARS[chosen_lhs_var] + "T")
    inj1 = subtree_replace(inj1, chosen_lhs_var, VARS[chosen_lhs_var] + "T1")
    inj2 = subtree_replace(inj2, chosen_lhs_var, VARS[chosen_lhs_var] + "T2")
    inj_final_eq1 = subtree_replace(inj_final_eq1, chosen_lhs_var, VARS[chosen_lhs_var] + "T1")
    inj_final_eq2 = subtree_replace(inj_final_eq2, chosen_lhs_var, VARS[chosen_lhs_var] + "T2")
  }

  vars_str1 = [surj_lhs, surj_rhs].flatten.uniq.keep_if { |i| i.class != String }.sort.map { |i| VARS[i] }.join(",")
  vars_str11 = [surj_lhs, surj_rhs].flatten.uniq.keep_if { |i| i.class == String }.sort.join(",")
  vars_str2 = [inj1, inj2].flatten.uniq.map { |i|
    if i.class == String
      i
    else
      VARS[i]
    end
  }.sort.join(",")

  return "![#{vars_str1}] : ?[#{vars_str11}] : ( " + eq2tptp(surj_lhs, surj_rhs, VARS) + " ) <=> ![#{vars_str2}] : ( (" + eq2tptp(inj1, inj2, VARS) + " ) => " + eq2tptp(inj_final_eq1, inj_final_eq2, VARS) + " )"
end

# Turn "x = x ◇ y" into ["x", ["x, "y"]]
def parse_expression(expr)
  tokens = expr.scan(/◇|\w+|[(),=]/)
  __parse_eq(tokens)
end

def __parse_eq(tokens)
  left = __parse_term(tokens)
  throw "Bad token!" unless tokens.shift == '='
  right = __parse_term(tokens)
  return [left, right]
end

def __parse_term(tokens)
  token = tokens.shift
  if token == '('
    args = []
    args << __parse_term(tokens)
    throw "Bad token!" unless tokens.shift == ')'
    if tokens.length > 1 && tokens[0] == '◇'
      throw "Bad token!" unless tokens.shift == '◇'
      args << __parse_term(tokens)
      return args
    else
      return args[0]
    end
  elsif tokens.length > 1 && tokens[0] == '◇'
    args = []
    args << token
    throw "Bad token!" unless tokens.shift == '◇'
    args << __parse_term(tokens)
    return args
  else
    return token
  end
end

# TODO: port
def find_equation_ids(equations)
  stdout, stderr, status = Open3.capture3('python', FIND_EQUATION_ID, *equations.map(&:to_s))
  if status != 0
    $stderr.puts "Bad result: #{status} #{stdout} #{stderr}"
    exit 1
  end

  equations = {}
  stdout.split("\n").each { |s|
    if s =~ /Equation (\d+): (.+)/
      eq_num = $1.to_i
      eq = parse_expression($2)

      # ["x", "y"] -> [0, 1]
      vars = eq.flatten.uniq
      vars.each_with_index { |v, i|
        eq = subtree_replace(eq, v, i)
      }

      equations[eq_num] = eq
    end
  }

  equations
end

def find_equation_id(equation)
  result = find_equation_ids([equation])
  raise "Unexpected" unless result.keys.length == 1
  return result.keys[0]
end

class TreeDoesntMatch < Exception
end

def __tree_matches_structure(tree, match_tree, assignments={})
  if match_tree.class != Array
    if assignments[match_tree] && assignments[match_tree] != tree
      raise TreeDoesntMatch.new
    end
    assignments[match_tree] = tree
    return
  end

  if tree.class != Array
    raise TreeDoesntMatch.new
  end

  __tree_matches_structure(tree[0], match_tree[0], assignments)
  __tree_matches_structure(tree[1], match_tree[1], assignments)
end

# (xy)(xy) matches (xx), but (xy) does not
def tree_matches_structure(tree, match_tree)
  begin
    __tree_matches_structure(tree, match_tree)
    return true
  rescue TreeDoesntMatch
    return false
  end
end

def renumber_rhs(lhs, rhs)
  remap = {}
  bound = [lhs].flatten.uniq
  bound.each { |v| remap[v] = v }

  high = bound.max
  rhs.flatten.each { |v|
    if !remap[v]
      high += 1
      remap[v] = high
    end
  }

  remap.each { |k, v|
    next if k == v
    rhs = subtree_replace(rhs, k, -v)
  }
  remap.each { |k, v|
    next if k == v
    rhs = subtree_replace(rhs, -v, v)
  }

  return rhs
end

# Some test cases to remember for the future: 35086954397121969570, 48337705565069
def find_inverses(eq)
  lhs, rhs = eq

  seen_rhs = Set.new([rhs])
  inverses = []
  match_expr = lhs
  loop {
    results = subtree_search(rhs, match_expr)
    break if results.length == 0
    if results.uniq.length > 1
      # This may be nested, e.g. x=y((x(xy))y) so continue trying, but start at the smallest element (e.g. for eq 124)
      match_expr = results.sort_by { |r| r.flatten.length }[0]
      next
    end

    sub_expr = results[0]
    match_expr = sub_expr

    break if sub_expr == rhs
    next if sub_expr.flatten.length == 1

    operation = subtree_replace(sub_expr, lhs, "s")
    inv_operation = subtree_replace(rhs, sub_expr, "s")
    next if [inv_operation, operation].flatten & [lhs].flatten != []

    # For example, if the LHS is x ◇ x then the operations must also match, e.g. as in equation 48337705565069
    next if !tree_matches_structure(operation, lhs) || !tree_matches_structure(inv_operation, lhs)

    inverted_rhs = subtree_replace(operation, "s", subtree_replace(inv_operation, "s", lhs))
    next if inverted_rhs == rhs

    # Equation 19, X = (Y ◇ (Z ◇ X))), is transformed into X = (Z ◇ (Y ◇ X)) which is equivalent,
    # except for numbering. This checks for this case, but we don't want to use it further
    # as it conflicts with the variable declarations in operation/inv_operation
    renumbered = renumber_rhs(lhs, inverted_rhs)
    next if seen_rhs.include? renumbered
    seen_rhs.add(renumbered)

    inverses.push({
      operation: operation,
      inv_operation: inv_operation,
      inverted: [lhs, inverted_rhs]
    })
  }

  return inverses
end

options = {}
opt_parser= OptionParser.new do |opt|
  opt.banner = "Usage: generate_tptp [options] <output directory>"

  opt.on('--inverses', 'Include axioms for inverses')
  opt.on('--generate-test-inverses LOW-HIGH', 'Generate proofs of inverses for all equations in the given range, intended for testing the correctness of the inverses code')

  opt.on('--simple-bijections', 'Include simple bijective axioms')
  opt.on('--bruteforce-bijections1 LHS,RHS', 'Bruteforce bijections by number of terms on LHS/RHS')

  opt.on('--bruteforce-periodicity-heuristic', 'Generates axioms to test if this implication may be subject to proof using a periodicity heuristic as mentioned here: https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/Austin.20pairs/near/483445305')
end

opt_parser.parse!(into: options)

if options[:"generate-test-inverses"]
  low, high = options[:"generate-test-inverses"].split("-").map(&:to_i)
  equations = find_equation_ids(low.upto(high).to_a)

  puts <<-END
import equational_theories.MagmaOp
import Mathlib.Data.Set.Finite.Basic

set_option linter.unusedVariables false

END

  inverses = {}
  equations.each { |eqnum, eqtree|
    r = find_inverses(eqtree)
    next if r.length == 0

    inverses[[eqnum, eqtree]] = r
  }

  inverse_eqs = find_equation_ids(inverses.values.flatten.map { |i| eq_repr i[:inverted] })
  reverse_inverse_eqs = {}
  inverse_eqs.each { |k, v| reverse_inverse_eqs[v] = k }

  inverses.each { |d, invs|
    eqnum, eqtree = d
    invs.each { |inv|
      renumbered = [inv[:inverted][0], renumber_rhs(*inv[:inverted])]
      inverted_eqnum = reverse_inverse_eqs[renumbered]
      raise "Unexpected" if !inverted_eqnum

      puts "theorem Finite.Equation#{eqnum}_implies_inverse_Equation#{inverted_eqnum} (G: Type _) [Magma G] [Finite G] (h : #{leanify_eq(eqtree)}) : #{leanify_eq(inv[:inverted])} := by"
      #puts "theorem Finite.Equation#{eqnum}_implies_inverse_Equation#{inverted_eqnum} (G: Type _) [Magma G] [Finite G] (h : Equation#{eqnum} G) : Equation#{inverted_eqnum} G := by"
      puts leanify_inverse(inv[:operation], inv[:inv_operation], inv[:inverted]).gsub("REPLACE", "result")
      puts "  simp [result]"
      puts
    }
  }

  exit 0
end

if ARGV.length != 1
  $stderr.puts "Missing arguments"
  $stderr.puts opt_parser
  exit 1
end

begin
  Dir.mkdir(ARGV[0])
rescue Errno::EEXIST
  $stderr.puts "Output directory already exists, move it aside or delete it"
  exit 1
end

seen_eqs = Set.new
unknowns = {}
while $stdin.gets
  src, dst = $_.split(",").map(&:to_i)
  unknowns[src] ||= []
  unknowns[src] << dst
  seen_eqs.add(src)
  seen_eqs.add(dst)
end

equations = find_equation_ids(seen_eqs.to_a)
equations.each { |src_eq, e|
  next if !unknowns[src_eq]

  export = {
    "hypothesis_num" => src_eq,
    "finite" => options != {},
    "axioms" => {}
  }

  axioms_tptp = {}

  if options[:inverses]
    inverses = {}
    find_inverses(equations[src_eq]).each { |inv|
      # Slow
      #eqnum = find_equation_id(eq_repr(inv[:inverted]))
      #name = "inverse_#{eqnum}"
      name = "inverse_rnd#{inv[:inverted].hash.abs}"
      export["axioms"][name] = { "proof" => leanify_inverse(inv[:operation], inv[:inv_operation], inv[:inverted]) }
      axioms_tptp[name] = tptp(inv[:inverted])
    }
  end

  if options[:"simple-bijections"]
    SIMPLE_BIJECTIONS.each { |name, tptp|
      export["axioms"][name] = { "proof" => "Not implemented" }
      axioms_tptp[name] = tptp
    }
  end

  unknowns[src_eq].each { |dst_eq|
    export["goal_num"] = dst_eq
    export["goal_eq"] = equations[dst_eq]
    base_tptp = <<-END
% JSON: #{JSON.generate(export)}
%---- #{src_eq} => #{dst_eq}
fof(hypothesis, axiom, #{tptp(equations[src_eq])} ).
fof(goal, conjecture, #{tptp(equations[dst_eq])} ).
END

    if options[:"bruteforce-bijections1"]
      l, r = options[:"bruteforce-bijections1"].split(",").map(&:to_i)
      gen_equations(l, r) { |axiom_num, lhs, rhs|
        bf_fof = gen_bij_tptp(lhs, rhs)
        if bf_fof
          File.open(File.join(ARGV[0], "#{src_eq}_#{dst_eq}_axiom#{axiom_num}.p"), "w") { |f|
            f.puts base_tptp
            axioms_tptp.each { |name, tptp|
              f.puts "fof(#{name}, axiom, " + tptp + ")."
            }
            f.puts "fof(try, axiom, #{bf_fof} )."
          }
        end
      }
    elsif options[:"bruteforce-periodicity-heuristic"]
      expr_idx = 1
      #call_on_every_subtree(equations[dst_eq][1]) { |rhs|
      gen_equations(1, 4) { |axiom_num, lhs, rhs|
        next if rhs.class != Array
        next if [rhs].flatten.uniq.length != 1

        # f^[i] = f^[i*j]
        [
          [1, 2], [1, 3], [1, 4], [1, 8],
          [2, 2], [2, 3]
        ].each { |i, j|
          File.open(File.join(ARGV[0], "#{src_eq}_#{dst_eq}_expr#{expr_idx}_#{i}_#{j}.p"), "w") { |f|
            f.puts base_tptp

            f_i = 0
            i.times { f_i = subtree_replace(f_i, 0, rhs) }
            f_ij = 0
            j.times { f_ij = subtree_replace(f_ij, 0, f_i) }
            f.puts "fof(expr#{expr_idx}_#{i}_#{j}, axiom, #{tptp([f_i, f_ij])} )."
          }
        }

        expr_idx += 1
      }
    else
      File.open(File.join(ARGV[0], "#{src_eq}_#{dst_eq}.p"), "w") { |f|
        f.puts base_tptp
        axioms_tptp.each { |name, tptp|
          f.puts "fof(#{name}, axiom, " + tptp + ")."
        }
      }
    end
  }
}

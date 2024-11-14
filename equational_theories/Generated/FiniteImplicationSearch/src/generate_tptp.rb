require 'json'

VARS = "XYZWUV"

def expr_repr(e)
  return VARS[e] if e.class == Integer
  return e if e.class == String    # Allow specifying custom expressions

  return "(#{expr_repr(e[0])} ◇ #{expr_repr(e[1])})"
end

def simplify_expr(t)
  if t["leaf"]
    return t["leaf"]
  end

  return [ simplify_expr(t["left"]), simplify_expr(t["right"]) ]
end

def simplify_eq(t)
  [ simplify_expr(t["lhs"]), simplify_expr(t["rhs"]) ]
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

def leanify_inverse(src_lhs, operation, inv_operation, inverted)
  str_operation = expr_repr operation
  str_inv_operation = expr_repr inv_operation

  proof = []
  proof << "  have REPLACE (" + inverted.flatten.uniq.map { |x| VARS[x] }.join(" ") + " : G) : " + expr_repr(inverted[1]) + " = " + expr_repr(inverted[0]) + " := by"
  if [src_lhs].flatten.length > 1
    proof << "    let S := {x | ∃ a b : G, a ◇ b = x}"
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
    proof << "      obtain ⟨a, b, rfl⟩ := ha"
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

if ARGV.length != 2
  $stderr.puts "Arguments: <equations.json> <output directory>"
  exit 1
end

$equations = {}
JSON.parse(File.read(ARGV[0])).each { |a|
  eq_num = a['equation'][8,16].to_i
  $equations[eq_num] = a
}

begin
  Dir.mkdir(ARGV[1])
rescue Errno::EEXIST
  puts "output directory already exists, move it aside or delete it"
  exit 1
end

$unknowns = {}
while $stdin.gets
  src, dst = $_.split(",").map(&:to_i)
  $unknowns[src] ||= []
  $unknowns[src] << dst
end

$equations.each { |src_eq, e|
  #next if src_eq > 4694

  next if !$unknowns[src_eq]
  $unknowns[src_eq].each { |dst_eq|
    src_lhs, src_rhs = simplify_eq($equations[src_eq]["law"])
    dst_lhs, dst_rhs = simplify_eq($equations[dst_eq]["law"])

    src_vars = [src_lhs, src_rhs].flatten.uniq
    dst_vars = [dst_lhs, dst_rhs].flatten.uniq

    i = 1
    export = {
      "hypothesis_num" => src_eq,
      "hypothesis_eq" => [src_lhs, src_rhs],
      "goal_num" => dst_eq,
      "goal_eq" => [dst_lhs, dst_rhs],
      "finite" => true,
      "axioms" => {}
    }
    match_expr = src_lhs
    loop {
      results = subtree_search(src_rhs, match_expr)
      break if results.length == 0
      if results.uniq.length > 1
        # This may be nested, e.g. x=y((x(xy))y) so continue trying, but start at the smallest element (e.g. for eq 124)
        match_expr = results.sort_by { |r| r.flatten.length }[0]
        next
      end

      sub_expr = results[0]
      match_expr = sub_expr

      break if sub_expr == src_rhs

      operation = subtree_replace(sub_expr, src_lhs, "s")
      inv_operation = subtree_replace(src_rhs, sub_expr, "s")

      next if [inv_operation, operation].flatten & [src_lhs].flatten != []

      inverted = subtree_replace(operation, "s", subtree_replace(inv_operation, "s", src_lhs))
      
      name = "inverse#{i}"
      i += 1
      export["axioms"][name] = {
        "eq" => [src_lhs, inverted],
        "proof" => leanify_inverse(src_lhs, operation, inv_operation, [src_lhs, inverted]),
      }
    }

    File.open(File.join(ARGV[1], "#{src_eq}_#{dst_eq}.p"), "w") { |f|
      f.puts "% JSON: #{JSON.generate(export)}"
      f.puts "%---- #{src_eq} => #{dst_eq}"
      f.puts "fof(hypothesis, axiom, " + tptp([src_lhs, src_rhs]) + ")."
      f.puts "fof(goal, conjecture, " + tptp([dst_lhs, dst_rhs]) + ")."
      export["axioms"].each { |k, v|
        f.puts "fof(#{k}, axiom, " + tptp(v["eq"]) + ")."
      }
    }
  }
}

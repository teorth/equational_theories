import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.Finsupp.Notation
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.Data.Rat.Encodable
import Mathlib.Data.Rat.Star
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.SimpleModule
import equational_theories.Equations.All
import equational_theories.FactsSyntax

-- Implements the magma (an infinite-dimentional vector space) from the proof:
-- https://leanprover.zulipchat.com/user_uploads/3121/ASjTo5huToAvNGcg7pOGOOSy/Equation1692.pdf

-- Our vector space G is a countably-infinite vector space over ℚ
abbrev G := (ℕ →₀ ℚ)

noncomputable abbrev n_q_basis := Finsupp.basisSingleOne (R := ℚ) (ι := ℕ)
noncomputable abbrev basis_n := DFunLike.coe n_q_basis

lemma basis_n_injective: Function.Injective basis_n := Basis.injective Finsupp.basisSingleOne

-- Holds the left and right values of a particular node in a tree: this is the (-b, c) and (c, a-b) from the paper
structure TreeData where
  a: G
  b: G

-- This represents the set 'S_i' from the paper, used to construct all of the nodes in a particular
-- binary tree.
structure XVals where
  -- Represents the 'i' in the set 'S_i' from the paper. We use this to take elements from
  -- our basis that do not occur in any other `XVals`
  i: ℕ
  -- Our root element, determined when we recursively build up the partial function
  root_elem: G
  -- The paper requires that all of the 'x_i' elements (as well as the root 'a') are linearly independent.
  -- For convenience, we use a stronger condition: there is no overlap between root element coordinates
  -- (in the single element basis) and the coordinates of any of the 'x_i' elements.
  supp_gt: ∀ n, root_elem.support.max < (basis_n (2^(i) + n*2^(i+1))).support.min
  root_nonzero: i ≠ 0 → root_elem ≠ 0

-- We map 'n=0' to the root element, and all other values to a value from the basis.
-- This is chosen such that distinct `XVals` have disjoint `G` values
noncomputable def XVals.x_vals (vals: XVals) (n: ℕ): G := if n = 0 then vals.root_elem else basis_n (2^(vals.i) + (n-1)*2^(vals.i+1))

-- The index passed to `basis_n` in `x_vals`. This is offset by one compared to `x_vals`
-- (e.g. `x_vals 0` maps to the root element from `XVals`, but `x_to_index 0` is the index of `x_vals 1`)
noncomputable def XVals.x_to_index (vals: XVals) (n: ℕ): ℕ := (2^(vals.i) + n*2^(vals.i+1))

lemma XVals.x_to_index_inj (vals: XVals): Function.Injective (XVals.x_to_index vals) := by
  simp [XVals.x_to_index, Function.Injective]

lemma XVals.x_to_index_eq (vals: XVals): ∀ n, vals.x_vals (n + 1) = basis_n (vals.x_to_index (n)) := by
  simp [XVals.x_vals, XVals.x_to_index]

lemma XVals.root_neq (vals: XVals) : vals.root_elem ∉ Set.range (fun n => basis_n (2^(vals.i) + n*2^(vals.i+1))) := by
  simp only [Finsupp.coe_basisSingleOne, Set.mem_range, not_exists]
  intro x
  by_contra!
  have app_eq := DFunLike.congr (x := 2 ^ vals.i + x * 2 ^ (vals.i + 1)) this rfl
  simp only [Finsupp.single_eq_same] at app_eq
  have not_in_supp: (2 ^ vals.i + x * 2 ^ (vals.i + 1)) ∉ vals.root_elem.support := by
    apply Finset.not_mem_of_max_lt_coe
    have supp_gt := vals.supp_gt x
    simp [basis_n, Finsupp.support_single_ne_zero] at supp_gt
    exact supp_gt
  rw [Finsupp.not_mem_support_iff] at not_in_supp
  simp [not_in_supp] at app_eq

lemma XVals.x_inj (vals: XVals): Function.Injective vals.x_vals := by
  rw [Function.Injective]
  intro a1 a2 funs_eq
  simp only [x_vals, Finsupp.coe_basisSingleOne] at funs_eq
  match ha1: a1 with
  | 0 =>
    simp only at funs_eq
    match a2 with
    | 0 => rfl
    | new_a2 + 1 =>
      simp only [↓reduceIte, AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false,
        add_tsub_cancel_right] at funs_eq
      have not_eq := vals.root_neq
      simp only [Finsupp.coe_basisSingleOne, Set.mem_range, not_exists] at not_eq
      specialize not_eq new_a2
      rw [eq_comm] at not_eq
      contradiction
  | new_a1 + 1 =>
    match a2 with
    | 0 =>
      simp only [AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, ↓reduceIte,
        add_tsub_cancel_right] at funs_eq
      have not_eq := vals.root_neq
      simp only [Finsupp.coe_basisSingleOne, Set.mem_range, not_exists] at not_eq
      specialize not_eq new_a1
      contradiction
    | new_a2 + 1 =>
      simp only [AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, ↓reduceIte,
        add_tsub_cancel_right] at funs_eq
      have apply_eq: (fun₀ | 2 ^ vals.i + new_a1 * 2 ^ (vals.i + 1) => (1 : ℚ)) (2 ^ (vals.i) + new_a1 * 2 ^ ((vals.i) + 1)) = (fun₀ | 2 ^ vals.i + new_a2 * 2 ^ (vals.i + 1) => 1) ((2 ^ (vals.i) + new_a1 * 2 ^ ((vals.i) + 1))) := by
        rw [funs_eq]
      simp only [Finsupp.single_eq_same] at apply_eq
      simp only [Finsupp.single_apply, add_right_inj, mul_eq_mul_right_iff, ne_eq,
        AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, not_false_eq_true, pow_eq_zero_iff,
        OfNat.ofNat_ne_zero, or_false] at apply_eq
      rw [eq_comm] at apply_eq
      simp only [add_left_inj]
      have new_a1_neq: new_a1 ≠ a1 := by linarith
      simp only [ite_eq_left_iff, zero_ne_one, imp_false, Decidable.not_not] at apply_eq
      exact apply_eq.symm

-- A node within a tree. The `XVals` parameter determines the value of the root element,
-- as well as the `x_i` elements used to build up other node values.
inductive TreeNode {vals: XVals} where
| root: TreeNode
| left: TreeNode → TreeNode
| right: TreeNode → TreeNode

-- Used to compute the index of the 'x_i' element we take from XVals at
-- a particular tree node (either the 'b' value of a left tree, or the 'a' value of a right tree)
def treeNum {vals: XVals}: @TreeNode vals → ℕ
  | TreeNode.root => 2
  | TreeNode.left prev => 2 * (treeNum prev) - 1
  | TreeNode.right prev => 2 * (treeNum prev)

-- Obtains the 'a' and 'b' values of a tree node, based on its position in the tree
noncomputable def TreeNode.getData {vals: XVals}: @TreeNode vals → TreeData
| TreeNode.root => {a := vals.root_elem, b := vals.x_vals 1}
| TreeNode.left base => {a := -base.getData.b, b := vals.x_vals (treeNum base)}
| TreeNode.right base => {a := vals.x_vals (treeNum base), b := base.getData.a - base.getData.b}

lemma treeNum_gt_one {vals: XVals} (t: @TreeNode vals): 1 < treeNum t := by
  induction t with
  | root => exact Nat.one_lt_succ_succ 0
  | left prev h_prev => rw [treeNum]; omega
  | right prev h_prev => rw [treeNum]; linarith

lemma treeNum_neq_zero {vals: XVals} (t: @TreeNode vals): treeNum t ≠ 0 := by
  linarith [treeNum_gt_one t]

lemma treeNum_increasing {vals: XVals} (t: @TreeNode vals): treeNum t < treeNum (TreeNode.left t) ∧ treeNum t < treeNum (TreeNode.right t) := by
  match t with
  | .root => simp [treeNum]
  | .left prev =>
    simp only [treeNum]
    have gt_zero: 1 < treeNum prev := treeNum_gt_one prev
    exact ⟨by omega, by omega⟩
  | .right prev =>
    simp only [treeNum]
    have gt_zero: 1 < treeNum prev := treeNum_gt_one prev
    exact ⟨by omega, by omega⟩

lemma treeNum_injective {vals: XVals} (t1: @TreeNode vals) (t2: TreeNode) (h_eq: treeNum t1 = treeNum t2): t1 = t2 := by
  induction t1 generalizing t2 with
  | root =>
    have t2_root: t2 = TreeNode.root := by
      by_contra!
      match t2 with
      | TreeNode.root => exact this rfl
      | TreeNode.left prev =>
        simp only [treeNum] at h_eq
        omega
      | TreeNode.right prev =>
        simp only [treeNum, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, left_eq_mul₀] at h_eq
        exact (Ne.symm (Nat.ne_of_lt (treeNum_gt_one prev))) h_eq
    rw [t2_root]
  | left prev h_prev =>
    have t2_left: ∃ d, t2 = TreeNode.left d := by
      by_contra!
      match t2 with
      | TreeNode.root =>
        simp only [treeNum] at h_eq
        omega
      | TreeNode.left prev2 =>
        specialize this prev2
        contradiction
      | TreeNode.right prev2 =>
        simp only [treeNum] at h_eq
        have gt_one: 1 < treeNum prev := treeNum_gt_one prev
        omega
    obtain ⟨d, hd⟩ := t2_left
    have d_num_eq: treeNum prev = treeNum d := by
      simp only [treeNum, hd] at h_eq
      omega
    have d_eq_prev: d = prev := by
      specialize h_prev d d_num_eq
      exact id (Eq.symm h_prev)
    rw [d_eq_prev, Eq.comm] at hd
    exact hd
  | right prev h_prev =>
    have t2_right: ∃ d, t2 = TreeNode.right d := by
      by_contra!
      match t2 with
      | TreeNode.root =>
        simp only [treeNum, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_eq_left₀] at h_eq
        have gt_one: 1 < treeNum prev := treeNum_gt_one prev
        omega
      | TreeNode.left prev2 =>
        simp only [treeNum] at h_eq
        have gt_one: 1 < treeNum prev := treeNum_gt_one prev
        omega
      | TreeNode.right prev2 =>
        specialize this prev2
        contradiction
    obtain ⟨d, hd⟩ := t2_right
    have d_num_eq: treeNum prev = treeNum d := by
      rw [hd] at h_eq
      simp only [treeNum] at h_eq
      omega
    have d_eq_prev: d = prev := by
      specialize h_prev d d_num_eq
      rw [Eq.comm] at h_prev
      exact h_prev
    rw [d_eq_prev, Eq.comm] at hd
    exact hd

-- Holds proofs that the 'a' and 'b' values of a particular node in a tree are linear combinations of the 'x_i' elements
structure TreeLinearCombData {vals: XVals} (t: @TreeNode vals) where
  a_coords: ℕ →₀ ℚ
  b_coords: ℕ →₀ ℚ
  a_coords_supp: a_coords.support.max < treeNum t
  b_coords_supp: b_coords.support.max < treeNum t
  a_eq: t.getData.a = ∑ i ∈ Finset.range (treeNum t), a_coords i • vals.x_vals i
  b_eq: t.getData.b = ∑ i ∈ Finset.range (treeNum t), b_coords i • vals.x_vals i

noncomputable def tree_linear_comb {vals: XVals} (t: @TreeNode vals): TreeLinearCombData t := by
  induction t with
  | root =>
    exact {
      a_coords := Finsupp.single 0 1,
      b_coords := Finsupp.single 1 1,
      a_coords_supp := by simp [treeNum, Finsupp.support_single_ne_zero]
      b_coords_supp := by simp [treeNum, Finsupp.support_single_ne_zero]
      a_eq := by
        rw [TreeNode.getData, treeNum, Finset.sum_eq_single 0]
        · simp [XVals.x_vals]
        · intro b hb b_neq_zero
          simp [Finsupp.single_apply, b_neq_zero.symm]
        · simp
      b_eq := by
        rw [TreeNode.getData, treeNum, Finset.sum_eq_single 1]
        · simp [XVals.x_vals]
        · intro b hb b_neq_zero
          simp [Finsupp.single_apply, b_neq_zero.symm]
        · simp
    }
  | left prev h_prev =>
    have treeNum_gt_one: 1 < treeNum prev := treeNum_gt_one prev
    have prev_lt_mul: treeNum prev < 2 * treeNum prev - 1 := by omega
    let neg_val := λ i => (-1: ℚ) * i
    let f_a := Finsupp.mapRange neg_val (Rat.mul_zero ..) h_prev.b_coords
    let f_b := Finsupp.single (treeNum prev) (1 : ℚ)
    exact {
      a_coords := f_a,
      b_coords := f_b,
      a_coords_supp := by
        simp only [f_a]
        have neg_val_injective: Function.Injective neg_val := by
          simp only [neg_mul, one_mul, neg_val]
          exact neg_injective
        rw [Finsupp.support_mapRange_of_injective (he0 := Rat.mul_zero ..) h_prev.b_coords neg_val_injective]
        rw [← WithBot.coe_lt_coe] at prev_lt_mul
        exact gt_trans prev_lt_mul h_prev.b_coords_supp
      b_coords_supp := by
        rw [Finsupp.support_single_ne_zero]
        · rw [Finset.max_singleton, treeNum, ← WithBot.coe_natCast]
          exact WithBot.coe_lt_coe.mpr prev_lt_mul
        · exact Ne.symm Rat.zero_ne_one
      a_eq := by
        simp only [TreeNode.getData, treeNum, neg_mul, one_mul, Finsupp.mapRange_apply, neg_smul,
          Finset.sum_neg_distrib, neg_inj, f_a, neg_val]
        rw [← Finset.sum_subset (s₁ := Finset.range (treeNum prev))]
        · exact h_prev.b_eq
        · rw [Finset.range_subset]
          exact Nat.le_of_succ_le prev_lt_mul
        · intro x _ x_not_in
          rw [smul_eq_zero]
          have x_not_g_supp: x ∉ h_prev.b_coords.support := by
            apply Finset.not_mem_of_max_lt_coe
            simp only [Finset.mem_range, not_lt] at x_not_in
            rw [← WithBot.coe_le_coe] at x_not_in
            exact gt_of_ge_of_gt x_not_in h_prev.b_coords_supp
          exact Or.inl (Finsupp.not_mem_support_iff.mp x_not_g_supp)
      b_eq := by
        simp only [f_b, TreeNode.getData, treeNum, Finsupp.single_apply, ite_smul, one_smul, zero_smul,
          Finset.sum_ite_eq, Finset.mem_range]
        exact Eq.symm (if_pos prev_lt_mul)
    }
  | right prev h_prev =>
    have prev_not_zero: treeNum prev ≠ 0 := treeNum_neq_zero prev
    have real_lt: treeNum prev < 2 * treeNum prev := by omega
    exact {
      a_coords := Finsupp.single (treeNum prev) 1,
      b_coords := h_prev.a_coords - h_prev.b_coords,
      a_coords_supp := by
        rw [Finsupp.support_single_ne_zero]
        · rw [Finset.max_singleton, treeNum, Nat.cast_mul, Nat.cast_ofNat, ← WithBot.coe_ofNat,
            ← WithBot.coe_natCast]
          norm_cast
        · exact Ne.symm Rat.zero_ne_one
      a_eq := by simp [Finsupp.single_apply, treeNum, real_lt, TreeNode.getData]
      b_coords_supp := by
        apply LE.le.trans_lt (hab := Finset.max_mono (Finsupp.support_sub (f := h_prev.a_coords) (g := h_prev.b_coords)))
        rw [Finset.max_union]
        rw [← WithBot.coe_lt_coe] at real_lt
        rw [sup_lt_iff]
        exact ⟨lt_trans h_prev.a_coords_supp real_lt, lt_trans h_prev.b_coords_supp real_lt⟩
      b_eq := by
        simp only [TreeNode.getData, treeNum, Finsupp.coe_sub, Pi.sub_apply]
        rw [h_prev.a_eq, h_prev.b_eq, ← Finset.sum_sub_distrib]
        have prev_subset_mul_two: Finset.range (treeNum prev) ⊆ Finset.range (2 * treeNum prev) := by
          rw [Finset.range_subset]
          exact Nat.le_of_succ_le real_lt
        rw [← Finset.sum_extend_by_zero, Finset.sum_subset prev_subset_mul_two]
        apply Finset.sum_congr rfl
        · intro x hx
          by_cases x_lt_treeNum: x < treeNum prev
          · simp only [Finset.mem_range, x_lt_treeNum]
            exact Eq.symm (sub_smul (h_prev.a_coords x) (h_prev.b_coords x) (vals.x_vals x))
          · simp only [Finset.mem_range, x_lt_treeNum, ↓reduceIte]
            simp only [not_lt] at x_lt_treeNum
            have x_not_g_supp: x ∉ h_prev.b_coords.support := by
              apply Finset.not_mem_of_max_lt_coe
              rw [← WithBot.coe_le_coe] at x_lt_treeNum
              exact gt_of_ge_of_gt x_lt_treeNum h_prev.b_coords_supp
            have x_not_g_l_supp: x ∉ h_prev.a_coords.support := by
              apply Finset.not_mem_of_max_lt_coe
              rw [← WithBot.coe_le_coe] at x_lt_treeNum
              exact gt_of_ge_of_gt x_lt_treeNum h_prev.a_coords_supp
            rw [Finsupp.not_mem_support_iff] at x_not_g_supp
            rw [Finsupp.not_mem_support_iff] at x_not_g_l_supp
            simp [x_not_g_supp, x_not_g_l_supp]
        · simp only [Finset.mem_range, not_lt, ite_eq_right_iff]
          omega
    }

lemma n_not_supp {vals: XVals} (t: @TreeNode vals) (n: ℕ) (hn: treeNum t - 1 ≤ n) (i: ℕ) (hi: i < (treeNum t)): vals.x_to_index n ∉ (vals.x_vals i).support := by
  by_cases i_eq_zero: i = 0
  · simp only [XVals.x_vals, i_eq_zero, ↓reduceIte, Finsupp.mem_support_iff, ne_eq,
      Decidable.not_not]
    have root_supp := vals.supp_gt (n)
    have index_supp := Finsupp.support_single_ne_zero (b := (1 : ℚ)) (vals.x_to_index n) (by simp)
    rw [XVals.x_to_index] at index_supp
    rw [basis_n, Finsupp.coe_basisSingleOne, index_supp] at root_supp
    exact Finsupp.not_mem_support_iff.mp (Finset.not_mem_of_max_lt_coe root_supp)
  · rw [XVals.x_vals, XVals.x_to_index]
    simp only [i_eq_zero, ↓reduceIte, Finsupp.coe_basisSingleOne, Finsupp.mem_support_iff]
    rw [Finsupp.single_apply]
    simp
    omega

lemma eval_larger_a_eq_zero {vals: XVals} (t: @TreeNode vals) (n: ℕ) (hn: treeNum t - 1 ≤ n) : t.getData.a (vals.x_to_index n) = 0 := by
  let tree_comb := tree_linear_comb t
  have sum_eval_eq_zero: ∑ i ∈ Finset.range (treeNum t), (tree_comb.a_coords i • vals.x_vals i) (vals.x_to_index n) = ∑ i ∈ Finset.range (treeNum t), 0 := by
    refine Finset.sum_congr rfl fun x hx ↦ ?_
    rw [Finset.mem_range] at hx
    have supp_subset := Finsupp.support_smul (g := vals.x_vals x) (b := tree_comb.a_coords x)
    exact Finsupp.not_mem_support_iff.mp fun a ↦ n_not_supp t n hn x hx (supp_subset a)
  have fun_congr := DFunLike.congr tree_comb.a_eq (x := vals.x_to_index n) rfl
  rw [Finsupp.finset_sum_apply, sum_eval_eq_zero, Finset.sum_const_zero] at fun_congr
  exact fun_congr

lemma eval_larger_b_eq_zero {vals: XVals} (t: @TreeNode vals) (n: ℕ) (hn: treeNum t - 1 ≤ n) : t.getData.b (vals.x_to_index n) = 0 := by
  let tree_comb := tree_linear_comb t
  have sum_eval_eq_zero: ∑ i ∈ Finset.range (treeNum t), (tree_comb.b_coords i • vals.x_vals i) (vals.x_to_index n) = ∑ i ∈ Finset.range (treeNum t), 0 := by
    refine Finset.sum_congr rfl fun x hx ↦ ?_
    simp only [Finset.mem_range] at hx
    have supp_subset := Finsupp.support_smul (g := vals.x_vals x) (b := tree_comb.b_coords x)
    exact Finsupp.not_mem_support_iff.mp fun a ↦ n_not_supp t n hn x hx (supp_subset a)
  have fun_congr := DFunLike.congr tree_comb.b_eq (x := vals.x_to_index n) rfl
  rw [Finsupp.finset_sum_apply, sum_eval_eq_zero, Finset.sum_const_zero] at fun_congr
  exact fun_congr

lemma xvals_root_not_supp (vals: XVals) (n: ℕ): vals.root_elem (vals.x_to_index (n)) = 0 := by
  have not_supp := vals.supp_gt n
  rw [← Finsupp.not_mem_support_iff]
  apply Finset.not_mem_of_max_lt_coe
  have supp_single := Finsupp.support_single_ne_zero (2 ^ vals.i + n * 2 ^ (vals.i + 1)) (b := (1 : ℚ)) (by simp)
  simp only [Finsupp.coe_basisSingleOne, supp_single] at not_supp
  exact not_supp

lemma tree_supp_disjoint {vals: XVals} (t: @TreeNode vals): t.getData.b.support ∩ t.getData.a.support = ∅ := by
  match t with
    | .root =>
      simp only [TreeNode.getData, vals.x_to_index_eq, Finsupp.coe_basisSingleOne, XVals.x_to_index,
        zero_mul, ne_eq, one_ne_zero, not_false_eq_true, Finsupp.support_single_ne_zero]
      have root_supp_lt := vals.supp_gt 0
      simp only [Finsupp.coe_basisSingleOne, zero_mul, add_zero, ne_eq, one_ne_zero, not_false_eq_true,
        Finsupp.support_single_ne_zero] at root_supp_lt
      exact Finset.singleton_inter_of_not_mem (Finset.not_mem_of_max_lt_coe root_supp_lt)
    | .left parent =>
        rw [TreeNode.getData, Finsupp.support_neg]
        let tree_comb := tree_linear_comb parent
        rw [tree_comb.b_eq]
        by_contra!
        obtain ⟨x, hx⟩ := Finset.Nonempty.exists_mem (Finset.nonempty_of_ne_empty this)
        have x_in_cur: x ∈ (vals.x_vals (treeNum parent)).support := Finset.mem_of_mem_inter_left hx
        simp only [XVals.x_vals, treeNum_neq_zero, ↓reduceIte, Finsupp.coe_basisSingleOne,
          Finsupp.mem_support_iff, ne_eq] at x_in_cur
        have supp_single: ∀ x ∈ Finset.range (treeNum parent), ((tree_comb.b_coords x) • vals.x_vals x).support ⊆ Finset.range (vals.x_to_index ((treeNum parent) - 1)) := by
          intro x hx
          simp only [XVals.x_vals, Finsupp.coe_basisSingleOne]
          by_cases x_eq_zero: x = 0
          · simp only [x_eq_zero, XVals.x_to_index]
            have root_supp_gt := vals.supp_gt 0
            intro a ha
            by_cases g_0_eq_zero: tree_comb.b_coords 0 = 0
            · simp [g_0_eq_zero] at ha
            · simp only [Finset.mem_range, gt_iff_lt]
              simp only [basis_n, zero_mul, add_zero, Finsupp.coe_basisSingleOne, ne_eq,
                one_ne_zero, not_false_eq_true, Finsupp.support_single_ne_zero,
                Finset.min_singleton, WithTop.coe_pow, WithTop.coe_ofNat] at root_supp_gt
              have supp_nonempty : (tree_comb.b_coords 0 • vals.root_elem).support.Nonempty := by
                rw [Finset.nonempty_iff_ne_empty]
                exact Finset.ne_empty_of_mem ha
              rw [← Finsupp.support_smul_eq g_0_eq_zero, ← Finset.coe_max' supp_nonempty] at root_supp_gt
              norm_cast at root_supp_gt
              rw [Nat.cast_withBot] at root_supp_gt
              norm_cast at root_supp_gt
              exact Nat.lt_add_right ((treeNum parent - 1) * 2 ^ (vals.i + 1))
                (LE.le.trans_lt (Finset.le_max' _ a ha) root_supp_gt)
          · simp only [x_eq_zero, ↓reduceIte, Finsupp.smul_single, smul_eq_mul, mul_one]
            by_cases g_x_eq_zero: tree_comb.b_coords x = 0
            · simp [g_x_eq_zero]
            · rw [Finsupp.support_single_ne_zero]
              simp only [XVals.x_to_index, Finset.singleton_subset_iff, Finset.mem_range,
                add_lt_add_iff_left, Nat.ofNat_pos, pow_pos, mul_lt_mul_right]
              rw [Finset.mem_range] at hx
              omega
              exact g_x_eq_zero
        have mul_supp_subset: ∀ i ∈ Finset.range (treeNum parent), (tree_comb.b_coords i • basis_n i).support ⊆ (basis_n i).support :=
          fun _ _ ↦ Finsupp.support_smul
        simp only [basis_n, Finsupp.coe_basisSingleOne, Finsupp.smul_single,
          smul_eq_mul, mul_one] at mul_supp_subset
        have coords_subset_max := (Finset.biUnion_subset (s := Finset.range (treeNum parent)) (t := fun x => (tree_comb.b_coords x • vals.x_vals x).support)).mpr supp_single
        have x_in_biunion: x ∈ ((Finset.range (treeNum parent)).biUnion fun x ↦ (tree_comb.b_coords x • vals.x_vals x).support) :=
          Finset.mem_of_subset (Finsupp.support_finset_sum (s := Finset.range (treeNum parent))
            (f := fun i => tree_comb.b_coords i • vals.x_vals i)) (Finset.mem_of_mem_inter_right hx)
        simp only [basis_n, Finsupp.coe_basisSingleOne] at x_in_biunion
        have x_in_range: x ∈ Finset.range (vals.x_to_index ((treeNum parent) - 1)) :=
          Finset.mem_of_subset coords_subset_max x_in_biunion
        have x_lt_m: x < vals.x_to_index ((treeNum parent) - 1) := by
          rw [Finset.mem_range] at x_in_range
          exact x_in_range
        rw [← ne_eq, ← Finsupp.mem_support_iff, Finsupp.support_single_ne_zero,
          Finset.mem_singleton] at x_in_cur
        rw [XVals.x_to_index] at x_lt_m
        rw [XVals.x_to_index] at x_in_range
        omega
        simp
    | .right parent =>
      simp only [TreeNode.getData]
      let tree_comb := tree_linear_comb parent
      rw [tree_comb.a_eq, tree_comb.b_eq]
      by_contra!
      obtain ⟨x, hx⟩ := Finset.Nonempty.exists_mem (Finset.nonempty_of_ne_empty this)
      have x_in_cur: x ∈ (vals.x_vals (treeNum parent)).support := Finset.mem_of_mem_inter_right hx
      have x_in_sum := Finset.mem_of_mem_inter_left hx
      simp only [XVals.x_vals, treeNum_neq_zero, ↓reduceIte, Finsupp.coe_basisSingleOne,
        Finsupp.mem_support_iff, ne_eq] at x_in_cur
      rw [← ne_eq, ← Finsupp.mem_support_iff, Finsupp.support_single_ne_zero] at x_in_cur
      simp only [Finset.mem_singleton] at x_in_cur
      rw [← Finset.sum_sub_distrib] at hx
      rw [← Finset.sum_sub_distrib] at x_in_sum
      have supp_single: ∀ g: ℕ →₀ ℚ, ∀ x ∈ Finset.range (treeNum parent), ((g x) • vals.x_vals x).support ⊆ Finset.range (vals.x_to_index (treeNum parent - 1)) := by
        intro g x hx
        by_cases x_eq_zero: x = 0
        · rw [x_eq_zero, XVals.x_to_index]
          have root_supp_gt := vals.supp_gt 0
          intro a ha
          by_cases g_0_eq_zero: g 0 = 0
          · simp [g_0_eq_zero] at ha
          · simp only [Finset.mem_range, gt_iff_lt]
            simp only [basis_n, zero_mul, add_zero, Finsupp.coe_basisSingleOne, ne_eq, one_ne_zero,
              not_false_eq_true, Finsupp.support_single_ne_zero, Finset.min_singleton,
              WithTop.coe_pow, WithTop.coe_ofNat] at root_supp_gt
            have supp_nonempty : (g 0 • vals.root_elem).support.Nonempty := by
              rw [Finset.nonempty_iff_ne_empty]
              exact Finset.ne_empty_of_mem ha
            have supp_eq: (g 0 • vals.root_elem).support = vals.root_elem.support :=
              Finsupp.support_smul_eq g_0_eq_zero
            rw [← supp_eq, ← Finset.coe_max' supp_nonempty] at root_supp_gt
            norm_cast at root_supp_gt
            rw [Nat.cast_withBot] at root_supp_gt
            norm_cast at root_supp_gt
            have a_lt := LE.le.trans_lt (Finset.le_max' _ a ha) root_supp_gt
            omega
        · simp only [XVals.x_vals, x_eq_zero, ↓reduceIte, Finsupp.coe_basisSingleOne,
          Finsupp.smul_single, smul_eq_mul, mul_one, XVals.x_to_index]
          by_cases g_x_eq_zero: g x = 0
          · simp [g_x_eq_zero]
          · rw [Finsupp.support_single_ne_zero]
            simp only [Finset.singleton_subset_iff, Finset.mem_range, add_lt_add_iff_left,
              Nat.ofNat_pos, pow_pos, mul_lt_mul_right]
            simp only [Finset.mem_range] at hx
            omega
            exact g_x_eq_zero
      have mul_supp_subset: ∀ g: ℕ →₀ ℚ, ∀ i ∈ Finset.range (treeNum parent), (g i • vals.x_vals i).support ⊆ (vals.x_vals i).support :=
        fun _ _ _ ↦ Finsupp.support_smul
      have combined_supp_subset: ∀ x ∈ Finset.range (treeNum parent), ((tree_comb.a_coords x • vals.x_vals x) - tree_comb.b_coords x • vals.x_vals x).support ⊆ Finset.range (vals.x_to_index ((treeNum parent) - 1)) := by
        intro x hx
        have support_sub_subset := Finsupp.support_sub (f := tree_comb.a_coords x • vals.x_vals x) (g := tree_comb.b_coords x • vals.x_vals x)
        have support_union_subset := Finset.union_subset_iff.mpr ⟨supp_single tree_comb.a_coords x hx, supp_single tree_comb.b_coords x hx⟩
        simp only at support_union_subset
        exact Finset.Subset.trans support_sub_subset support_union_subset
      simp only [basis_n, Finsupp.coe_basisSingleOne, Finsupp.smul_single,
          smul_eq_mul, mul_one] at mul_supp_subset
      have biunion_subset := (Finset.biUnion_subset (s := Finset.range (treeNum parent))).mpr combined_supp_subset
      have support_subset := Finsupp.support_finset_sum (s := Finset.range (treeNum parent)) (f := fun x => ((tree_comb.a_coords x • vals.x_vals x - tree_comb.b_coords x • vals.x_vals x)))
      have x_in_biunion := Finset.mem_of_subset support_subset x_in_sum
      simp only [basis_n, Finsupp.coe_basisSingleOne] at x_in_biunion
      have x_in_range: x ∈ Finset.range (vals.x_to_index ((treeNum parent) - 1)) :=
        Finset.mem_of_subset biunion_subset x_in_biunion
      have x_lt_m: x < (vals.x_to_index ((treeNum parent) - 1)) := by
        rw [Finset.mem_range] at x_in_range
        exact x_in_range
      have treeNum_val_gt: vals.x_to_index ((treeNum parent) - 1) ≤ 2 ^ vals.i + (treeNum parent - 1) * 2 ^ (vals.i + 1) :=
        Nat.le_refl (vals.x_to_index (treeNum parent - 1))
      omega
      simp

lemma tree_linear_independent {vals: XVals} (t: @TreeNode vals) (ht: t.getData.a ≠ 0): LinearIndependent ℚ ![t.getData.a, t.getData.b] := by
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, LinearIndependent.pair_iff]
  have supp_disjoint := tree_supp_disjoint t
  intro a b h_sum_zero
  have supp_nonempty: t.getData.a.support.Nonempty := by
    rw [Finsupp.support_nonempty_iff]
    exact ht
  obtain ⟨x, hx⟩ := supp_nonempty
  have new_supp_disjoint: Disjoint t.getData.b.support t.getData.a.support := Finset.disjoint_iff_inter_eq_empty.mpr supp_disjoint
  have x_not_b_supp: x ∉ t.getData.b.support := Finset.disjoint_right.mp new_supp_disjoint hx
  rw [Finsupp.not_mem_support_iff] at x_not_b_supp
  rw [Finsupp.mem_support_iff] at hx
  have eval_at := DFunLike.congr h_sum_zero (x := x) rfl
  simp only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    x_not_b_supp, mul_zero, add_zero, Finsupp.coe_zero, Pi.zero_apply, mul_eq_zero, hx, or_false] at eval_at
  have a_eq_zero := eval_at
  simp only [a_eq_zero, zero_smul, zero_add, smul_eq_zero] at h_sum_zero
  match t with
  | .root =>
    simp only [TreeNode.getData, XVals.x_vals, one_ne_zero, ↓reduceIte, Finsupp.coe_basisSingleOne,
      tsub_self, zero_mul, add_zero, Finsupp.single_eq_zero, or_false] at h_sum_zero
    exact ⟨a_eq_zero, h_sum_zero⟩
  | .left prev =>
    simp only [TreeNode.getData, XVals.x_vals, treeNum_neq_zero, ↓reduceIte,
      Finsupp.coe_basisSingleOne, Finsupp.single_eq_zero, one_ne_zero, or_false] at h_sum_zero
    exact ⟨a_eq_zero, h_sum_zero⟩
  | .right prev =>
    simp only [TreeNode.getData, XVals.x_vals, Finsupp.coe_basisSingleOne] at h_sum_zero
    have not_eq: prev.getData.a - prev.getData.b ≠ 0 := by
      by_contra!
      apply eq_of_sub_eq_zero at this
      have prev_disjoint := tree_supp_disjoint prev
      rw [this] at prev_disjoint
      simp only [Finset.inter_self, Finsupp.support_eq_empty] at prev_disjoint
      rw [prev_disjoint] at this
      match prev with
      | .root => simp [TreeNode.getData, XVals.x_vals] at prev_disjoint
      | .left grandparent => simp [TreeNode.getData, XVals.x_vals, treeNum_neq_zero] at prev_disjoint
      | .right grandparent => simp [TreeNode.getData, XVals.x_vals, treeNum_neq_zero] at this
    simp only [not_eq, or_false] at h_sum_zero
    exact ⟨a_eq_zero, h_sum_zero⟩

lemma tree_vals_nonzero {vals: XVals} (t: @TreeNode vals) : t.getData.b ≠ 0 := by
  by_cases tree_a_zero: t.getData.a = 0
  · match t with
    | .root => simp [TreeNode.getData, XVals.x_vals]
    | .left parent => simp [TreeNode.getData, XVals.x_vals, treeNum_neq_zero]
    | .right parent => simp [TreeNode.getData, XVals.x_vals, treeNum_neq_zero] at tree_a_zero
  · exact LinearIndependent.ne_zero 1 (tree_linear_independent t tree_a_zero)

lemma tree_b_supp_nonempty {vals: XVals} (t: @TreeNode vals) : t.getData.b.support.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty, ne_eq, Finsupp.support_eq_empty]
  exact tree_vals_nonzero t

-- A single `Finsupp` element is not equal to a linear combination of the `tree.getData.a` and `tree.getData.b`
-- (provded that several values are non-zero)
lemma basis_neq_elem_diff {vals: XVals} (t: @TreeNode vals) (a: ℕ) (b c r: ℚ) (hb: b ≠ 0) (hc: c ≠ 0) (hr: r ≠ 0) (h_tree_a: t.getData.a ≠ 0): (fun₀ | a => r) ≠ b • t.getData.b + c • t.getData.a := by
  by_contra!
  have mul_support_disjoint: Disjoint (b • t.getData.b).support (c • t.getData.a).support :=
    .mono Finsupp.support_smul Finsupp.support_smul (Finset.disjoint_iff_inter_eq_empty.mpr (tree_supp_disjoint t))
  have single_card_one: (fun₀ | a => r).support.card = 1 := by simp [Finsupp.support_single_ne_zero a hr]
  let s: Finset (Fin 2) := {0, 1}
  let g := fun (i: Fin 2) => if i = 0 then b • t.getData.b else c • t.getData.a
  have g_supp_disjoint: ∀ (i_1 i_2: Fin 2), i_1 ≠ i_2 → Disjoint (g i_1).support (g i_2).support := by
    intro i_1 i_2 i_neq
    simp only [Fin.isValue, g]
    by_cases i_1_eq: i_1 = 0
    · have i_2_eq: i_2 = 1 := by omega
      simp only [i_1_eq, Fin.isValue, ↓reduceIte, i_2_eq, one_ne_zero]
      exact mul_support_disjoint
    · have i_1_eq: i_1 = 1 := by omega
      have i_2_eq: i_2 = 0 := by omega
      simp only [i_1_eq, Fin.isValue, one_ne_zero, ↓reduceIte, i_2_eq]
      exact mul_support_disjoint.symm
  have support_sum := Finsupp.support_sum_eq_biUnion s g_supp_disjoint
  simp only [Fin.isValue, Finset.mem_singleton, zero_ne_one, not_false_eq_true, Finset.sum_insert,
    ↓reduceIte, Finset.sum_singleton, one_ne_zero, Finset.biUnion_insert, Finset.singleton_biUnion,
    s, g] at support_sum
  have b_mul_card: 1 ≤ (b • t.getData.b).support.card := by
    rw [Finsupp.support_smul_eq hb]
    exact Nat.one_le_iff_ne_zero.mpr (Finsupp.card_support_eq_zero.not.mpr
      (LinearIndependent.ne_zero 1 (tree_linear_independent t h_tree_a)))
  have c_mul_card: 1 ≤ (c • t.getData.a).support.card := by
    rw [Finsupp.support_smul_eq hc]
    exact Nat.one_le_iff_ne_zero.mpr (Finsupp.card_support_eq_zero.not.mpr h_tree_a)
  -- have card_union_sum := Finset.card_union_eq_card_add_card.mpr mul_support_disjoint
  have card_sum_le : 2 ≤ ((b • t.getData.b).support ∪ (c • t.getData.a).support).card := by
    linarith [Finset.card_union_eq_card_add_card.mpr mul_support_disjoint]
  rw [Finsupp.ext_iff'] at this
  obtain ⟨support_eq, _⟩ := this
  have card_eq : (fun₀ | a => r).support.card = (b • t.getData.b + c • t.getData.a).support.card := by rw [support_eq]
  rw [single_card_one, support_sum, Finset.card_union_eq_card_add_card.mpr mul_support_disjoint] at card_eq
  linarith

lemma finsupp_new_zero_treeNum {vals: XVals} (t: @TreeNode vals) (a b: ℚ) (hb: b ≠ 0): (fun₀ | vals.x_to_index 0 => (a: ℚ)) ≠ (fun₀ | (vals.x_to_index (treeNum t - 1)) => (b: ℚ)) := by
  by_contra!
  have eval_at := DFunLike.congr (x := (vals.x_to_index (treeNum t - 1))) (y := vals.x_to_index (treeNum t - 1)) this rfl
  simp only [Finsupp.single_eq_same] at eval_at
  have t2_gt_one := treeNum_gt_one t
  have vals_neq: vals.x_to_index 0 ≠ vals.x_to_index (treeNum t - 1) := by
    simp [XVals.x_to_index]
    omega
  simp only [ne_eq, vals_neq, not_false_eq_true, Finsupp.single_eq_of_ne, eq_comm] at eval_at
  contradiction

lemma xseq_zero_neq_b {vals: XVals} (t: @TreeNode vals) (s: ℚ) (hs: s ≠ 0): vals.root_elem ≠ s • t.getData.b := by
  by_contra!
  match t with
  | .root =>
      simp only [TreeNode.getData] at this
      have eval_at := DFunLike.congr (x := (vals.x_to_index 0)) (y := (vals.x_to_index 0)) this rfl
      rw [vals.x_to_index_eq, XVals.x_to_index, zero_mul, add_zero, basis_n, Finsupp.coe_basisSingleOne,
        Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.single_eq_same] at eval_at
      have root_supp := vals.supp_gt 0
      simp at root_supp
      simp [Finsupp.support_single_ne_zero] at root_supp
      have two_i_not_supp: 2^vals.i ∉ vals.root_elem.support := by
        apply Finset.not_mem_of_max_lt_coe
        simp only [WithBot.coe_pow, WithBot.coe_ofNat]
        exact root_supp
      rw [Finsupp.not_mem_support_iff, eval_at] at two_i_not_supp
      contradiction
  | .left t2_parent_parent =>
      simp only [TreeNode.getData, XVals.x_vals, treeNum_neq_zero, ↓reduceIte, Finsupp.coe_basisSingleOne,
        Finsupp.smul_single, smul_eq_mul, mul_one] at this
      have eval_at := DFunLike.congr (x := (vals.x_to_index (treeNum t2_parent_parent - 1))) this rfl
      simp only [XVals.x_to_index, Finsupp.single_eq_same] at eval_at
      have root_not_supp := xvals_root_not_supp vals (treeNum t2_parent_parent - 1)
      simp only [XVals.x_to_index] at root_not_supp
      simp [root_not_supp] at eval_at
      rw [← eval_at] at hs
      contradiction

    | .right t2_parent_parent =>
      simp only [TreeNode.getData] at this
      have neg_s_neq_zero: (-s) ≠ 0 := by
        simp only [ne_eq, neg_eq_zero]
        exact hs
      have vals_neq := basis_neq_elem_diff t2_parent_parent (vals.x_to_index 0) (-s) s 1 neg_s_neq_zero hs (by simp)
      simp only [one_smul, neg_one_smul, add_comm] at vals_neq
      rw [neg_smul, ← sub_eq_add_neg] at vals_neq
      rw [smul_sub] at this
      match t2_parent_parent with
      | .root =>
        simp only [TreeNode.getData, XVals.x_vals, one_ne_zero, ↓reduceIte,
          Finsupp.coe_basisSingleOne, tsub_self, zero_mul, add_zero, Finsupp.smul_single,
          smul_eq_mul, mul_one] at this
        have eval_at := DFunLike.congr (x := (vals.x_to_index (0))) this rfl
        have root_not_supp := xvals_root_not_supp vals (0)
        simp only [XVals.x_to_index, zero_mul, add_zero] at root_not_supp
        simp only [XVals.x_to_index, zero_mul, add_zero, root_not_supp, Finsupp.coe_sub,
          Finsupp.coe_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_zero,
          Finsupp.single_eq_same, zero_sub, zero_eq_neg] at eval_at
        contradiction
      | .left ancestor =>
        simp only [TreeNode.getData, XVals.x_vals, treeNum_neq_zero, ↓reduceIte,
          Finsupp.coe_basisSingleOne, smul_neg, Finsupp.smul_single, smul_eq_mul, mul_one] at this
        have eval_at := DFunLike.congr (x := (vals.x_to_index (treeNum ancestor - 1))) this rfl
        have root_not_supp := xvals_root_not_supp vals (treeNum ancestor - 1)
        simp only [XVals.x_to_index] at root_not_supp
        simp only [XVals.x_to_index, root_not_supp, Finsupp.coe_sub, Finsupp.coe_neg,
          Finsupp.coe_smul, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul,
          Finsupp.single_eq_same] at eval_at
        have ancestor_b_zero := eval_larger_b_eq_zero ancestor (treeNum ancestor - 1) (by simp)
        simp only [XVals.x_to_index] at ancestor_b_zero
        simp only [ancestor_b_zero, mul_zero, neg_zero, zero_sub, zero_eq_neg] at eval_at
        contradiction
      | .right ancestor =>
        simp only [TreeNode.getData, XVals.x_vals, treeNum_neq_zero, ↓reduceIte,
          Finsupp.coe_basisSingleOne, Finsupp.smul_single, smul_eq_mul, mul_one] at this
        have ancestor_a_zero := eval_larger_a_eq_zero ancestor (treeNum ancestor - 1) (by simp)
        have ancestor_b_zero := eval_larger_b_eq_zero ancestor (treeNum ancestor - 1) (by simp)
        rw [XVals.x_to_index] at ancestor_a_zero
        rw [XVals.x_to_index] at ancestor_b_zero
        have root_not_supp := xvals_root_not_supp vals (treeNum ancestor - 1)
        rw [XVals.x_to_index] at root_not_supp
        have eval_at := DFunLike.congr (x := (vals.x_to_index (treeNum ancestor - 1))) this rfl
        simp only [XVals.x_to_index, root_not_supp, Finsupp.coe_sub, Finsupp.coe_smul, Pi.sub_apply,
          Finsupp.single_eq_same, Pi.smul_apply, ancestor_a_zero, ancestor_b_zero, sub_self,
          smul_eq_mul, mul_zero, sub_zero, eq_comm] at eval_at
        contradiction

-- Proof that the following situation cannot occur:
--
--          --> t1
-- ancestor
--          --> t2
--
-- where t1.getData.b - t1.getData.a = t2.getData.b - t2.getData.a
-- Used as part of proving that 'f' is a partial function
lemma common_ancestor_helper {vals: XVals} (ancestor t1 t2: @TreeNode vals) (left_right: t1 = ancestor.left ∧ t2 = ancestor.right)
  (h_a_eq: t1.getData.b - t1.getData.a = t2.getData.b - t2.getData.a): False := by
  simp only [left_right.1, TreeNode.getData, sub_neg_eq_add, left_right.2] at h_a_eq
  have x_seq_add: vals.x_vals (treeNum ancestor) + ancestor.getData.b  + vals.x_vals (treeNum ancestor) = ancestor.getData.a - ancestor.getData.b :=
    add_eq_of_eq_sub h_a_eq
  have x_swap: vals.x_vals (treeNum ancestor) + ancestor.getData.b  + vals.x_vals (treeNum ancestor) = vals.x_vals (treeNum ancestor) + vals.x_vals (treeNum ancestor) + ancestor.getData.b :=
    Eq.symm (add_rotate (vals.x_vals (treeNum ancestor)) (vals.x_vals (treeNum ancestor))
      ancestor.getData.b)
  rw [x_swap] at x_seq_add
  have sub_b: vals.x_vals (treeNum ancestor) + vals.x_vals (treeNum ancestor) = ancestor.getData.a - ancestor.getData.b - ancestor.getData.b := by
    apply_fun (fun x => x - ancestor.getData.b) at x_seq_add
    simp only [add_sub_cancel_right] at x_seq_add
    exact x_seq_add
  rw [← two_nsmul, sub_sub, ← two_nsmul] at sub_b
  let tree_comb := tree_linear_comb ancestor
  rw [tree_comb.a_eq, tree_comb.b_eq, ← Finset.sum_nsmul, ← Finset.sum_sub_distrib] at sub_b
  apply n_q_basis.ext_elem_iff.mp at sub_b
  specialize sub_b (vals.x_to_index (treeNum ancestor - 1))
  simp only [n_q_basis, Finsupp.basisSingleOne_repr, Finsupp.coe_basisSingleOne, Finsupp.smul_single, nsmul_eq_mul, Nat.cast_ofNat, mul_one, LinearEquiv.refl_apply, Finsupp.single_eq_same, Finset.mem_range, smul_eq_mul, smul_ite, Finsupp.single_mul, smul_zero, Finsupp.coe_sub, Finsupp.coe_finset_sum, Pi.sub_apply, Finset.sum_apply] at sub_b
  have sum_eq_zero: ∑ x ∈ Finset.range (treeNum ancestor), (((tree_comb.a_coords x • vals.x_vals x) (vals.x_to_index (treeNum ancestor - 1)) - (2 • tree_comb.b_coords x • vals.x_vals x) ((vals.x_to_index (treeNum ancestor - 1))))) = ∑ x ∈ Finset.range (treeNum ancestor), 0 := by
    refine Finset.sum_congr rfl fun x hx ↦ ?_
    simp only [Finset.mem_range] at hx
    have treeNum_ancestor_gt: 1 < treeNum ancestor := treeNum_gt_one ancestor
    have x_neq_treeNum: x - 1 < treeNum ancestor - 1 := by omega
    have index_x_neq_treeNum: vals.x_to_index (x - 1) ≠ vals.x_to_index (treeNum ancestor - 1) := by
      simp [XVals.x_to_index]
      omega
    have root_not_supp := xvals_root_not_supp vals (treeNum ancestor - 1)
    rw [XVals.x_to_index] at root_not_supp
    by_cases x_eq_zero: x = 0
    · simp [vals.x_to_index_eq, index_x_neq_treeNum, x_eq_zero, XVals.x_vals, XVals.x_to_index,
        root_not_supp]
    · simp only [XVals.x_to_index] at index_x_neq_treeNum
      simp [vals.x_to_index_eq, index_x_neq_treeNum, x_eq_zero, XVals.x_vals, XVals.x_to_index,
        index_x_neq_treeNum]
  rw [sum_eq_zero] at sub_b
  simp [XVals.x_vals, XVals.x_to_index, treeNum_neq_zero] at sub_b

-- Another helper lemma for proving `partial_function`:
-- If the following two equations hold:
-- `t1.getData.a = t2.getData.a`
-- (`t1.getData.a - t1.getData.b = t2.getData.a - t2.getData.b`,
-- then `t1` and `t2` have a common parent
lemma cross_eq_same_parent {vals: XVals} {t1 t2: @TreeNode vals} (h_a_neq: t1.getData.a ≠ t2.getData.a) (h_eq: t1.getData.a - t1.getData.b = t2.getData.a - t2.getData.b) : ∃ ancestor: TreeNode, (t1 = ancestor.left ∧ t2 = ancestor.right) ∨ (t1 = ancestor.right ∧ t2 = ancestor.left) := by
    have parents_b_neq: t1.getData.b ≠ t2.getData.b := by?
      by_contra!
      rw [this] at h_eq
      simp only [sub_left_inj] at h_eq
      contradiction
    have treeNum_neq: treeNum t1 ≠ treeNum t2 := by
      by_contra!
      have t1_eq_t2: t1 = t2 := treeNum_injective t1 t2 this
      rw [t1_eq_t2] at h_a_neq
      contradiction
    match h_t1: t1 with
    | .root =>
      match h_t2: t2 with
      | .root =>
        have t1_eq_t2: t1 = t2 := by rwa [← h_t2] at h_t1
        rw [← h_t1, t1_eq_t2] at h_a_neq
        contradiction
      | .left t2_parent =>
          simp only [TreeNode.getData] at h_eq
          have fun_congr := DFunLike.congr h_eq (x := vals.x_to_index (treeNum t2_parent - 1)) rfl
          simp only [XVals.x_vals, one_ne_zero, ↓reduceIte, Finsupp.coe_basisSingleOne, tsub_self,
            zero_mul, add_zero, XVals.x_to_index, Finsupp.coe_sub, Pi.sub_apply, treeNum_neq_zero,
            Finsupp.coe_neg, Pi.neg_apply, Finsupp.single_eq_same] at fun_congr
          have t2_a_zero := eval_larger_a_eq_zero t2_parent (treeNum t2_parent - 1) (by simp)
          have t2_b_zero := eval_larger_b_eq_zero t2_parent (treeNum t2_parent - 1) (by simp)
          simp only [XVals.x_to_index] at t2_a_zero
          simp only [XVals.x_to_index] at t2_b_zero
          simp only [t2_b_zero, neg_zero, zero_sub] at fun_congr
          have t2_gt_one: 1 < treeNum t2_parent := treeNum_gt_one t2_parent
          have mul_ge_one: 1 ≤ (treeNum t2_parent - 1) * 2 ^ (vals.i + 1) :=
            one_le_mul_of_one_le_of_one_le (by omega) Nat.one_le_two_pow
          have vals_neq: 2 ^ vals.i ≠ (2 ^ vals.i + (treeNum t2_parent - 1) * 2 ^ (vals.i + 1)) := by
            linarith
          simp only [ne_eq, vals_neq, not_false_eq_true, Finsupp.single_eq_of_ne, sub_zero] at fun_congr
          have root_not_supp := xvals_root_not_supp vals (treeNum t2_parent - 1)
          simp only [XVals.x_to_index] at root_not_supp
            -- Implicit contradiction
          simp only [root_not_supp, zero_eq_neg, one_ne_zero] at fun_congr
      | .right t2_parent =>
          simp only [TreeNode.getData] at h_eq
          have fun_congr := DFunLike.congr h_eq (x := vals.x_to_index (treeNum t2_parent - 1)) rfl
          have t2_a_zero := eval_larger_a_eq_zero t2_parent (treeNum t2_parent - 1) (by simp)
          simp only [XVals.x_vals, one_ne_zero, ↓reduceIte, Finsupp.coe_basisSingleOne, tsub_self,
            zero_mul, add_zero, XVals.x_to_index, Finsupp.coe_sub, Pi.sub_apply, treeNum_neq_zero,
            Finsupp.single_eq_same] at fun_congr
          have t2_b_zero := eval_larger_b_eq_zero t2_parent (treeNum t2_parent - 1) (by simp)
          simp only [XVals.x_to_index] at t2_a_zero
          simp only [XVals.x_to_index] at t2_b_zero
          simp only [t2_a_zero, t2_b_zero, sub_self, sub_zero] at fun_congr
          have t2_gt_one: 1 < treeNum t2_parent := treeNum_gt_one t2_parent
          have mul_ge_one: 1 ≤ (treeNum t2_parent - 1) * 2 ^ (vals.i + 1) :=
            one_le_mul_of_one_le_of_one_le (by omega) Nat.one_le_two_pow
          have vals_neq: 2 ^ vals.i ≠ (2 ^ vals.i + (treeNum t2_parent - 1) * 2 ^ (vals.i + 1)) := by linarith
          simp only [ne_eq, vals_neq, not_false_eq_true, Finsupp.single_eq_of_ne, sub_zero] at fun_congr
          have root_not_supp := xvals_root_not_supp vals (treeNum t2_parent - 1)
          simp only [XVals.x_to_index] at root_not_supp
            -- Implicit contradiction
          simp only [root_not_supp, zero_ne_one] at fun_congr
    | .left t1_parent =>
        match h_t2: t2 with
          | .root =>
            simp [TreeNode.getData] at h_eq
            have fun_congr := DFunLike.congr h_eq (x := vals.x_to_index (treeNum t1_parent - 1)) rfl
            have t1_a_zero := eval_larger_a_eq_zero t1_parent (treeNum t1_parent - 1) (by simp)
            have t1_b_zero := eval_larger_b_eq_zero t1_parent (treeNum t1_parent - 1) (by simp)
            simp only [XVals.x_to_index] at t1_a_zero
            simp only [XVals.x_to_index] at t1_b_zero
            have t1_gt_one: 1 < treeNum t1_parent := treeNum_gt_one t1_parent
            have t1_neq_zero: 0 ≠ treeNum t1_parent := by linarith
            have index_zero_neq: vals.x_to_index 0 ≠ vals.x_to_index (treeNum t1_parent) :=
              Function.Injective.ne vals.x_to_index_inj t1_neq_zero
            have t1_neq_one: 1 ≠ treeNum t1_parent := by linarith
            repeat rw [vals.x_to_index_eq] at fun_congr
            simp only [Finsupp.coe_sub, Finsupp.coe_neg, Pi.sub_apply, Pi.neg_apply,
              Finsupp.coe_basisSingleOne] at fun_congr
            simp only [XVals.x_to_index, XVals.x_vals, treeNum_neq_zero, ↓reduceIte,
              Finsupp.coe_basisSingleOne, Finsupp.single_eq_same, zero_mul, add_zero] at fun_congr
            have mul_ge_one: 1 ≤ (treeNum t1_parent - 1) * 2 ^ (vals.i + 1) :=
              one_le_mul_of_one_le_of_one_le (by omega) Nat.one_le_two_pow
            have vals_neq: 2 ^ vals.i ≠ (2 ^ vals.i + (treeNum t1_parent - 1) * 2 ^ (vals.i + 1)) := by
              linarith
            simp only [t1_b_zero, neg_zero, zero_sub] at fun_congr
            have root_not_supp := xvals_root_not_supp vals (treeNum t1_parent - 1)
            simp only [XVals.x_to_index] at root_not_supp
              -- Implicit contradiction
            simp only [root_not_supp, ne_eq, vals_neq, not_false_eq_true, Finsupp.single_eq_of_ne,
              sub_self, neg_eq_zero, one_ne_zero] at fun_congr
          | .left t2_parent =>
              by_cases is_t1_lt: treeNum t1_parent - 1 < treeNum t2_parent - 1
              · have is_t1_le: treeNum t1_parent - 1 ≤ treeNum t2_parent - 1 := by omega
                simp only [TreeNode.getData] at h_eq
                have fun_congr := DFunLike.congr h_eq (x := vals.x_to_index (treeNum t2_parent - 1)) rfl
                have t1_b_zero := eval_larger_b_eq_zero t1_parent (treeNum t2_parent - 1) is_t1_le
                have t2_a_zero := eval_larger_a_eq_zero t2_parent (treeNum t2_parent - 1) (by simp)
                have t2_b_zero := eval_larger_b_eq_zero t2_parent (treeNum t2_parent - 1) (by simp)
                simp only [XVals.x_to_index] at t1_b_zero
                simp only [XVals.x_to_index] at t2_a_zero
                simp only [XVals.x_to_index] at t2_b_zero
                have treeNums_neq: treeNum t1_parent - 1 ≠ treeNum t2_parent - 1 := by linarith
                simp only [XVals.x_vals, XVals.x_to_index, treeNum_neq_zero] at fun_congr
                simp [t1_b_zero, t2_a_zero, t2_b_zero, treeNums_neq] at fun_congr
              · simp only [TreeNode.getData] at h_eq
                have fun_congr := DFunLike.congr h_eq (x := vals.x_to_index (treeNum t1_parent - 1)) rfl
                simp only at fun_congr
                have t2_a_zero := eval_larger_a_eq_zero t2_parent (treeNum t1_parent - 1) (by linarith)
                have t2_b_zero := eval_larger_b_eq_zero t2_parent (treeNum t1_parent - 1) (by linarith)
                have t1_b_zero := eval_larger_b_eq_zero t1_parent (treeNum t1_parent - 1) (by simp)
                rw [XVals.x_to_index] at t1_b_zero
                rw [XVals.x_to_index] at t2_a_zero
                rw [XVals.x_to_index] at t2_b_zero
                by_cases treeNums_eq: treeNum t1_parent = treeNum t2_parent
                · have t1_eq_t2: t1 = t2 := by
                    rw [treeNum_injective t1_parent t2_parent treeNums_eq] at h_t1
                    rwa [← h_t2] at h_t1
                  rw [← h_t1, ← h_t2, t1_eq_t2] at h_a_neq
                  contradiction
                · have treeNum_t2_gt: 1 < treeNum t2_parent := treeNum_gt_one t2_parent
                  have treeNums_neq: treeNum t1_parent - 1 ≠ treeNum t2_parent - 1 := by omega
                  have vals_neq: 2 ^ vals.i + (treeNum t1_parent - 1) * 2 ^ (vals.i + 1) ≠ 2 ^ vals.i + (treeNum t2_parent - 1) * 2 ^ (vals.i + 1) := by
                    by_contra!
                    simp at this
                    contradiction
                  simp [XVals.x_vals, XVals.x_to_index, treeNum_neq_zero, t1_b_zero, t2_a_zero,
                    t2_b_zero, treeNums_neq.symm, vals_neq.symm] at fun_congr
          | .right t2_parent =>
              have treeNums_eq: treeNum t1_parent = treeNum t2_parent := by
                by_contra!
                by_cases is_t1_lt: treeNum t1_parent - 1 < treeNum t2_parent - 1
                · have is_t1_le: treeNum t1_parent - 1 ≤ treeNum t2_parent - 1 := by linarith
                  simp only [TreeNode.getData] at h_eq
                  have fun_congr := DFunLike.congr h_eq (x := vals.x_to_index (treeNum t2_parent - 1)) rfl
                  simp at fun_congr
                  have t1_b_zero := eval_larger_b_eq_zero t1_parent (treeNum t2_parent - 1) is_t1_le
                  have t2_a_zero := eval_larger_a_eq_zero t2_parent (treeNum t2_parent - 1) (by simp)
                  have t2_b_zero := eval_larger_b_eq_zero t2_parent (treeNum t2_parent - 1) (by simp)
                  simp [XVals.x_to_index] at t1_b_zero
                  simp [XVals.x_to_index] at t2_a_zero
                  simp [XVals.x_to_index] at t2_b_zero
                  simp [XVals.x_vals, treeNum_neq_zero, XVals.x_to_index, t1_b_zero, t2_a_zero, t2_b_zero] at fun_congr
                  have vals_neq: 2 ^ vals.i + (treeNum t1_parent - 1) * 2 ^ (vals.i + 1) ≠ 2 ^ vals.i + (treeNum t2_parent - 1) * 2 ^ (vals.i + 1) := by
                    by_contra!
                    simp at this
                    omega
                  simp [vals_neq] at fun_congr
                · have is_t2_le: treeNum t2_parent - 1 ≤ treeNum t1_parent - 1 := by
                    linarith
                  simp [TreeNode.getData] at h_eq
                  have fun_congr := DFunLike.congr h_eq (x := vals.x_to_index (treeNum t1_parent - 1)) rfl
                  simp at fun_congr
                  have t2_a_zero := eval_larger_a_eq_zero t2_parent (treeNum t1_parent - 1) is_t2_le
                  have t2_b_zero := eval_larger_b_eq_zero t2_parent (treeNum t1_parent - 1) is_t2_le
                  have t1_b_zero := eval_larger_b_eq_zero t1_parent (treeNum t1_parent - 1) (by simp)
                  simp [XVals.x_to_index] at t1_b_zero
                  simp [XVals.x_to_index] at t2_a_zero
                  simp [XVals.x_to_index] at t2_b_zero
                  simp [XVals.x_to_index, XVals.x_vals, treeNum_neq_zero] at fun_congr
                  simp [t1_b_zero, t2_a_zero, t2_b_zero] at fun_congr
                  have treeNum_t2_gt: 1 < treeNum t2_parent := treeNum_gt_one t2_parent
                  have vals_neq: 2 ^ vals.i + (treeNum t1_parent - 1) * 2 ^ (vals.i + 1) ≠ 2 ^ vals.i + (treeNum t2_parent - 1) * 2 ^ (vals.i + 1) := by
                    by_contra!
                    simp at this
                    omega
                  simp [vals_neq.symm] at fun_congr
              exact ⟨t1_parent, Or.inl ((treeNum_injective t1_parent t2_parent treeNums_eq) ▸ ⟨rfl, rfl⟩)⟩
    | .right t1_parent =>
      match h_t2: t2 with
        | .root =>
          simp only [TreeNode.getData] at h_eq
          have fun_congr := DFunLike.congr h_eq (x := vals.x_to_index (treeNum t1_parent - 1)) rfl
          simp [XVals.x_vals, XVals.x_to_index, treeNum_neq_zero] at fun_congr
          have t1_a_zero := eval_larger_a_eq_zero t1_parent (treeNum t1_parent - 1) (by simp)
          have t1_b_zero := eval_larger_b_eq_zero t1_parent (treeNum t1_parent - 1) (by simp)
          simp [XVals.x_to_index] at t1_a_zero
          simp [XVals.x_to_index] at t1_b_zero
          simp [t1_a_zero, t1_b_zero] at fun_congr
          have t1_gt_one: 1 < treeNum t1_parent := treeNum_gt_one t1_parent
          have pow_pow_ge_one: 1 ≤ 2 ^ (vals.i + 1) := Nat.one_le_two_pow
          have t1_sub_gt: 1 ≤ treeNum t1_parent - 1 := by omega
          have mul_ge_one: 1 ≤ (treeNum t1_parent - 1) * 2 ^ (vals.i + 1) := one_le_mul_of_one_le_of_one_le t1_sub_gt pow_pow_ge_one
          have vals_neq: 2 ^ vals.i ≠ (2 ^ vals.i + (treeNum t1_parent - 1) * 2 ^ (vals.i + 1)) := by linarith
          simp [vals_neq] at fun_congr
          have root_not_supp := xvals_root_not_supp vals (treeNum t1_parent - 1)
          simp [XVals.x_to_index] at root_not_supp
          -- Implicit contradiction
          simp [root_not_supp] at fun_congr
        | .left t2_parent =>
            have treeNums_eq: treeNum t1_parent = treeNum t2_parent := by
              by_contra!
              by_cases is_t1_lt: treeNum t1_parent - 1 < treeNum t2_parent - 1
              · have is_t1_le: treeNum t1_parent - 1 ≤ treeNum t2_parent - 1 := by
                  linarith
                simp [TreeNode.getData] at h_eq
                have fun_congr := DFunLike.congr h_eq (x := vals.x_to_index (treeNum t2_parent - 1)) rfl
                simp at fun_congr
                have t1_a_zero := eval_larger_a_eq_zero t1_parent (treeNum t2_parent - 1) is_t1_le
                have t1_b_zero := eval_larger_b_eq_zero t1_parent (treeNum t2_parent - 1) is_t1_le
                have t2_a_zero := eval_larger_a_eq_zero t2_parent (treeNum t2_parent - 1) (by simp)
                have t2_b_zero := eval_larger_b_eq_zero t2_parent (treeNum t2_parent - 1) (by simp)
                simp [XVals.x_to_index] at t1_a_zero
                simp [XVals.x_to_index] at t1_b_zero
                simp [XVals.x_to_index] at t2_a_zero
                simp [XVals.x_to_index] at t2_b_zero
                simp [XVals.x_vals, XVals.x_to_index] at fun_congr
                simp [treeNum_neq_zero] at fun_congr
                simp [t1_b_zero, t2_a_zero, t2_b_zero, t1_a_zero] at fun_congr
                have vals_neq: 2 ^ vals.i + (treeNum t1_parent - 1) * 2 ^ (vals.i + 1) ≠ 2 ^ vals.i + (treeNum t2_parent - 1) * 2 ^ (vals.i + 1) := by
                  by_contra!
                  simp at this
                  omega
                simp [vals_neq] at fun_congr
              · have is_t2_le: treeNum t2_parent - 1 ≤ treeNum t1_parent - 1 := by linarith
                simp [TreeNode.getData] at h_eq
                have fun_congr := DFunLike.congr h_eq (x := vals.x_to_index (treeNum t1_parent - 1)) rfl
                simp at fun_congr
                have t2_a_zero := eval_larger_a_eq_zero t2_parent (treeNum t1_parent - 1) is_t2_le
                have t2_b_zero := eval_larger_b_eq_zero t2_parent (treeNum t1_parent - 1) is_t2_le
                have t1_a_zero := eval_larger_a_eq_zero t1_parent (treeNum t1_parent - 1) (by simp)
                have t1_b_zero := eval_larger_b_eq_zero t1_parent (treeNum t1_parent - 1) (by simp)
                simp [XVals.x_to_index] at t1_a_zero
                simp [XVals.x_to_index] at t1_b_zero
                simp [XVals.x_to_index] at t2_a_zero
                simp [XVals.x_to_index] at t2_b_zero
                simp [XVals.x_to_index, XVals.x_vals, treeNum_neq_zero] at fun_congr
                simp [t1_b_zero, t2_a_zero, t2_b_zero, t1_a_zero] at fun_congr
                have treeNum_t1_gt: 1 < treeNum t1_parent := treeNum_gt_one t1_parent
                have treeNum_t2_gt: 1 < treeNum t2_parent := treeNum_gt_one t2_parent
                have vals_neq: 2 ^ vals.i + (treeNum t1_parent - 1) * 2 ^ (vals.i + 1) ≠ 2 ^ vals.i + (treeNum t2_parent - 1) * 2 ^ (vals.i + 1) := by
                  by_contra!
                  simp at this
                  omega
                simp [vals_neq.symm] at fun_congr
            exact ⟨t1_parent, Or.inr (treeNum_injective t1_parent t2_parent treeNums_eq ▸ ⟨rfl, rfl⟩)⟩
        | .right t2_parent =>
            by_cases is_t2_lt: treeNum t2_parent - 1 < treeNum t1_parent - 1
            · have is_t2_le: treeNum t2_parent - 1 ≤ treeNum t1_parent - 1 := by linarith
              simp [TreeNode.getData, XVals.x_vals, treeNum_neq_zero] at h_eq
              have fun_congr := DFunLike.congr h_eq (x := vals.x_to_index (treeNum t1_parent - 1)) rfl
              have t2_a_zero := eval_larger_a_eq_zero t2_parent (treeNum t1_parent - 1) is_t2_le
              have t2_b_zero := eval_larger_b_eq_zero t2_parent (treeNum t1_parent - 1) is_t2_le
              have t1_a_zero := eval_larger_a_eq_zero t1_parent (treeNum t1_parent - 1) (by simp)
              have t1_b_zero := eval_larger_b_eq_zero t1_parent (treeNum t1_parent - 1) (by simp)
              simp [XVals.x_to_index] at t1_a_zero
              simp [XVals.x_to_index] at t1_b_zero
              simp [XVals.x_to_index] at t2_a_zero
              simp [XVals.x_to_index] at t2_b_zero
              simp [XVals.x_to_index, XVals.x_vals, treeNum_neq_zero] at fun_congr
              simp [t2_a_zero, t2_b_zero, t1_a_zero, t1_b_zero] at fun_congr
              have vals_neq: 2 ^ vals.i + (treeNum t1_parent - 1) * 2 ^ (vals.i + 1) ≠ 2 ^ vals.i + (treeNum t2_parent - 1) * 2 ^ (vals.i + 1) := by
                by_contra!
                simp at this
                omega
              simp [vals_neq.symm] at fun_congr
            · by_cases treeNums_eq: treeNum t1_parent = treeNum t2_parent
              · have parents_eq: t1_parent = t2_parent := treeNum_injective t1_parent t2_parent treeNums_eq
                have t1_eq_t2: t1 = t2 := by
                  rwa [parents_eq, ← h_t2] at h_t1
                rw [← h_t1, ← h_t2, t1_eq_t2] at h_a_neq
                contradiction
              · have treeNum_t1_gt: 1 < treeNum t1_parent := treeNum_gt_one t1_parent
                have treeNum_t2_gt: 1 < treeNum t2_parent := treeNum_gt_one t2_parent
                have treeNums_neq: treeNum t1_parent - 1 ≠ treeNum t2_parent - 1 := by omega
                have is_t1_minus_le: treeNum t1_parent - 1 ≤ treeNum t2_parent - 1 := by omega
                simp [TreeNode.getData] at h_eq
                have fun_congr := DFunLike.congr h_eq (x := vals.x_to_index (treeNum t2_parent - 1)) rfl
                simp [XVals.x_to_index, XVals.x_vals, treeNum_neq_zero] at fun_congr
                have t1_a_zero := eval_larger_a_eq_zero t1_parent (treeNum t2_parent - 1) is_t1_minus_le
                have t1_b_zero := eval_larger_b_eq_zero t1_parent (treeNum t2_parent - 1) is_t1_minus_le
                have t2_a_zero := eval_larger_a_eq_zero t2_parent (treeNum t2_parent - 1) (by simp)
                have t2_b_zero := eval_larger_b_eq_zero t2_parent (treeNum t2_parent - 1) (by simp)
                simp [XVals.x_to_index] at t1_a_zero
                simp [XVals.x_to_index] at t1_b_zero
                simp [XVals.x_to_index] at t2_a_zero
                simp [XVals.x_to_index] at t2_b_zero
                simp [t1_a_zero, t1_b_zero, t2_a_zero, t2_b_zero] at fun_congr
                have vals_neq: 2 ^ vals.i + (treeNum t1_parent - 1) * 2 ^ (vals.i + 1) ≠ 2 ^ vals.i + (treeNum t2_parent - 1) * 2 ^ (vals.i + 1) := by
                  by_contra!
                  simp at this
                  omega
                simp [vals_neq] at fun_congr

-- The main part of proving that 'f' is a partial function:
-- We cannot have two distinct nodes (in the same `XVals` tree) with the same 'a' value.
-- This lemma takes in an additional 'minimality' hypothesis (`t1` and `t2` are the nodes with the smallest `treeNum`)
-- We prove this by repeatedly considering the ancestors of these nodes, ruling out cases as we go along.
-- This eventually leads to a contradiction for all cases.
--
-- This lemma is used by the main `partial_function` lemma, which obtains a minimal counterexample (distinct nodes with the same 'a' value) and applies this lemma to it.
lemma partial_function_inner {vals: XVals} {t1 t2: @TreeNode vals} (h_a_eq: t1.getData.a = t2.getData.a) (h_min: ∀ (tree1 tree2: @TreeNode vals), tree1.getData.a = tree2.getData.a ∧ tree1 ≠ tree2 → treeNum t1 ≤ treeNum tree1) (this: t1 ≠ t2): False := by
  match t1 with
  | .root =>
    match t2 with
    | .root => contradiction
    | .left t2_parent =>
        simp [TreeNode.getData] at h_a_eq
        have b_neq := xseq_zero_neq_b t2_parent (-1) (by simp)
        simp at b_neq
        contradiction
    | .right t2_parent =>
        simp [TreeNode.getData, vals.x_to_index_eq, basis_n] at h_a_eq
        simp [XVals.x_vals, treeNum_neq_zero] at h_a_eq
        have root_not_range := vals.root_neq
        simp at root_not_range
        specialize root_not_range (treeNum t2_parent - 1)
        rw [eq_comm] at h_a_eq
        contradiction
  | .left t1_parent =>
    match t2 with
    | .root =>
        simp [TreeNode.getData, vals.x_to_index_eq, basis_n] at h_a_eq
        have b_neq := xseq_zero_neq_b t1_parent (-1) (by simp)
        simp at b_neq
        rw [eq_comm] at b_neq
        contradiction
    | .left t2_parent =>
      -- Both parents must be left trees
        match t1_parent with
        | .root =>
            simp [TreeNode.getData] at h_a_eq
            match t2_parent with
            | .root => contradiction
            | .left t2_parent_parent =>
                simp [TreeNode.getData] at h_a_eq
                simp only [vals.x_to_index_eq] at h_a_eq
                simp [basis_n, XVals.x_vals, treeNum_neq_zero] at h_a_eq
                apply basis_n_injective at h_a_eq
                apply vals.x_to_index_inj at h_a_eq
                have val_gt_one := treeNum_gt_one t2_parent_parent
                omega
            | .right t2_parent_parent =>
                simp [TreeNode.getData, vals.x_to_index_eq, basis_n] at h_a_eq
                by_cases t_a_zero: t2_parent_parent.getData.a = 0
                · simp [t_a_zero] at h_a_eq
                  match t2_parent_parent with
                  | .root =>
                    simp [TreeNode.getData, XVals.x_vals, XVals.x_to_index] at h_a_eq
                    rw [← Finsupp.single_neg, Finsupp.single_eq_single_iff] at h_a_eq
                    simp at h_a_eq
                    contradiction
                  | .left grandparent =>
                    simp [TreeNode.getData, XVals.x_vals, XVals.x_to_index, treeNum_neq_zero] at h_a_eq
                    rw [← Finsupp.single_neg] at h_a_eq
                    rw [Finsupp.single_eq_single_iff] at h_a_eq
                    simp at h_a_eq
                    have bad := h_a_eq.2
                    contradiction
                  | .right grandparent =>
                    simp [TreeNode.getData, XVals.x_vals, treeNum_neq_zero] at t_a_zero
                · have vals_neq := basis_neq_elem_diff t2_parent_parent (vals.x_to_index 0) (-1) 1 1 (by simp) (by simp) (by simp) t_a_zero
                  simp only [one_smul, neg_one_smul] at vals_neq
                  rw [add_comm, ← sub_eq_add_neg] at vals_neq
                  simp [XVals.x_to_index] at h_a_eq
                  simp [XVals.x_to_index] at vals_neq
                  contradiction
        | .left t1_parent_parent =>
            match t2_parent with
            | .root =>
              simp [TreeNode.getData] at h_a_eq
              apply vals.x_inj at h_a_eq
              have val_gt_one := treeNum_gt_one t1_parent_parent
              omega
            | .left t2_parent_parent =>
              -- If both parents are left trees - we know that left trees have unique 'b' values so their parents must be the same node. But then our original nodes are left children of the same node, so they're again the same node - contradiction
              simp [TreeNode.getData] at h_a_eq
              apply vals.x_inj at h_a_eq
              apply treeNum_injective at h_a_eq
              rw [h_a_eq] at this
              contradiction
            | .right t2_parent_parent =>
                simp [TreeNode.getData, vals.x_to_index_eq, basis_n, XVals.x_vals, treeNum_neq_zero, XVals.x_to_index] at h_a_eq
                rw [← Finsupp.single_neg] at h_a_eq
                by_cases t_a_zero: t2_parent_parent.getData.a = 0
                · simp [t_a_zero] at h_a_eq
                  match t2_parent_parent with
                  | .root =>
                    simp [TreeNode.getData, XVals.x_vals, XVals.x_to_index] at h_a_eq
                    rw [← Finsupp.single_neg] at h_a_eq
                    rw [Finsupp.single_eq_single_iff] at h_a_eq
                    simp at h_a_eq
                    have bad := h_a_eq.2
                    contradiction
                  | .left grandparent =>
                    simp [TreeNode.getData, XVals.x_vals, XVals.x_to_index, treeNum_neq_zero] at h_a_eq
                    rw [← Finsupp.single_neg] at h_a_eq
                    rw [Finsupp.single_eq_single_iff] at h_a_eq
                    simp at h_a_eq
                    have bad := h_a_eq.2
                    contradiction
                  | .right grandparent =>
                    simp [TreeNode.getData, XVals.x_vals, treeNum_neq_zero] at t_a_zero
                · have vals_neq := basis_neq_elem_diff t2_parent_parent (vals.x_to_index (treeNum t1_parent_parent - 1)) (1) (-1) (-1) (by simp) (by simp) (by simp) t_a_zero
                  simp [XVals.x_to_index] at vals_neq
                  rw [← sub_eq_add_neg, ← Finsupp.single_neg] at vals_neq
                  contradiction
        | .right t1_parent_parent =>
          match t2_parent with
          | .root =>
            simp [TreeNode.getData, vals.x_to_index_eq, basis_n, XVals.x_to_index] at h_a_eq
            rw [← Finsupp.single_neg] at h_a_eq
            by_cases t_a_zero: t1_parent_parent.getData.a = 0
            · simp [t_a_zero] at h_a_eq
              match t1_parent_parent with
              | .root =>
                simp [TreeNode.getData, XVals.x_vals, XVals.x_to_index] at h_a_eq
                rw [← Finsupp.single_neg] at h_a_eq
                rw [Finsupp.single_eq_single_iff] at h_a_eq
                simp at h_a_eq
                contradiction
              | .left grandparent =>
                simp [TreeNode.getData, XVals.x_vals, XVals.x_to_index, treeNum_neq_zero] at h_a_eq
                rw [← Finsupp.single_neg] at h_a_eq
                rw [Finsupp.single_eq_single_iff] at h_a_eq
                simp at h_a_eq
                have bad := h_a_eq.2
                contradiction
              | .right grandparent =>
                simp [TreeNode.getData, XVals.x_vals, treeNum_neq_zero] at t_a_zero
            · have vals_neq := basis_neq_elem_diff t1_parent_parent (vals.x_to_index 0) (1) (-1) (-1) (by simp) (by simp) (by simp) t_a_zero
              simp only [one_smul, neg_one_smul] at vals_neq
              simp [XVals.x_to_index] at vals_neq
              rw [← sub_eq_add_neg] at vals_neq
              simp at h_a_eq
              rw [eq_comm] at h_a_eq
              contradiction
          | .left t2_parent_parent =>
            simp [TreeNode.getData, vals.x_to_index_eq, basis_n, XVals.x_vals, treeNum_neq_zero] at h_a_eq
            rw [← Finsupp.single_neg] at h_a_eq
            by_cases t_a_zero: t1_parent_parent.getData.a = 0
            · simp [t_a_zero] at h_a_eq
              match t1_parent_parent with
              | .root =>
                simp [TreeNode.getData, XVals.x_vals, XVals.x_to_index] at h_a_eq
                rw [← Finsupp.single_neg, Finsupp.single_eq_single_iff] at h_a_eq
                simp at h_a_eq
                have bad := h_a_eq.2
                contradiction
              | .left grandparent =>
                simp [TreeNode.getData, XVals.x_vals, XVals.x_to_index, treeNum_neq_zero] at h_a_eq
                rw [← Finsupp.single_neg, Finsupp.single_eq_single_iff] at h_a_eq
                simp at h_a_eq
                have bad := h_a_eq.2
                contradiction
              | .right grandparent =>
                simp [TreeNode.getData, XVals.x_vals, treeNum_neq_zero] at t_a_zero
            · have vals_neq := basis_neq_elem_diff t1_parent_parent (vals.x_to_index (treeNum t2_parent_parent - 1)) 1 (-1) (-1) (by simp) (by simp) (by simp) t_a_zero
              simp only [one_smul, neg_one_smul] at vals_neq
              simp [XVals.x_to_index] at vals_neq
              rw [← sub_eq_add_neg] at vals_neq
              simp at h_a_eq
              rw [eq_comm] at h_a_eq
              contradiction
          | .right t2_parent_parent =>
            -- Both parents must be right trees.
            simp [TreeNode.getData] at h_a_eq
            have grandparents_neq: t1_parent_parent ≠ t2_parent_parent := by
              by_contra! grandparents_eq
              rw [grandparents_eq] at this
              simp at this
            -- This is where we use the minimality assumption
            have parents_a_neq: t1_parent_parent.getData.a ≠ t2_parent_parent.getData.a := by
              by_contra! grandparent_a_eq
              specialize h_min t1_parent_parent t2_parent_parent ⟨grandparent_a_eq, grandparents_neq⟩
              have treeNum_gt_right := (treeNum_increasing t1_parent_parent).2
              have treeNum_gt_left := (treeNum_increasing t1_parent_parent.right).1
              omega
            -- The parents look like (c, d) and (x, y) with c ≠ x, We must also have d ≠ y to satisfy 'c - d = x - y'
            apply_fun (fun x => -1 • x) at h_a_eq
            simp at h_a_eq
            have common_ancestor := cross_eq_same_parent parents_a_neq h_a_eq
            apply_fun (fun x => -1 • x) at h_a_eq
            simp at h_a_eq
            obtain ⟨ancestor, h_ancestor⟩ := common_ancestor
--     Let this common ancestor be (f, g).
--     Then, the parents are (-g, x_i) and (x_i, f - g),
--     We have -g - x_i = x_i - (f - g)
--              -g -x_i = x_i - f + g
--              0 = 2x_i + 2g - f
--     This is impossible, because x_i is fresh: g and/or f would need to contain x_i, which is impossible.
            cases h_ancestor with
            | inl left_right =>
              exact common_ancestor_helper ancestor t1_parent_parent t2_parent_parent left_right h_a_eq
            | inr right_left =>
              exact common_ancestor_helper ancestor t2_parent_parent t1_parent_parent right_left.symm h_a_eq.symm
    | .right t2_parent =>
      simp [TreeNode.getData] at h_a_eq
      match t1_parent with
      | .root =>
        simp [TreeNode.getData, XVals.x_vals, treeNum_neq_zero] at h_a_eq
        have fun_neq := finsupp_new_zero_treeNum t2_parent (-1) 1 (by simp)
        simp [XVals.x_to_index] at fun_neq
        contradiction
      | .left t1_parent_parent =>
        simp [TreeNode.getData, vals.x_to_index_eq, basis_n, XVals.x_vals, treeNum_neq_zero] at h_a_eq
        rw [← Finsupp.single_neg] at h_a_eq
        rw [Finsupp.single_eq_single_iff] at h_a_eq
        simp at h_a_eq
        have bad := h_a_eq.2
        contradiction
      | .right t1_parent_parent =>
        simp [TreeNode.getData, vals.x_to_index_eq, basis_n] at h_a_eq

        by_cases t_a_zero: t1_parent_parent.getData.a = 0
        ·
          simp [t_a_zero] at h_a_eq
          match t1_parent_parent with
          | .root =>
            simp [TreeNode.getData, XVals.x_vals, XVals.x_to_index, treeNum_neq_zero] at h_a_eq
            rw [Finsupp.single_eq_single_iff] at h_a_eq
            simp at h_a_eq
            have treeNum_parent_ge: 1 < treeNum t2_parent := by
              exact treeNum_gt_one t2_parent
            omega
          | .left grandparent =>
            simp [TreeNode.getData, XVals.x_vals, XVals.x_to_index, treeNum_neq_zero] at h_a_eq
            rw [Finsupp.single_eq_single_iff] at h_a_eq
            simp at h_a_eq
            simp [TreeNode.getData] at t_a_zero
            have grandparent_b_not_zero := tree_vals_nonzero grandparent
            contradiction
          | .right grandparent =>
            simp [TreeNode.getData, XVals.x_vals, treeNum_neq_zero] at t_a_zero
        ·
          have vals_neq := basis_neq_elem_diff t1_parent_parent (vals.x_to_index (treeNum t2_parent - 1)) 1 (-1) 1 (by simp) (by simp) (by simp) t_a_zero
          simp only [one_smul, neg_one_smul, ← sub_eq_add_neg] at vals_neq
          rw [eq_comm] at h_a_eq
          simp [XVals.x_vals, treeNum_neq_zero] at h_a_eq
          simp [XVals.x_to_index] at vals_neq
          contradiction
  | .right t1_parent =>
    match t2 with
    | .root =>
        simp [TreeNode.getData] at h_a_eq
        simp [XVals.x_vals, treeNum_neq_zero] at h_a_eq
        have root_not_range := vals.root_neq
        simp at root_not_range
        specialize root_not_range (treeNum t1_parent - 1)
        contradiction
    | .left t2_parent =>
      simp [TreeNode.getData] at h_a_eq
      match t2_parent with
      | .root =>
        simp [TreeNode.getData, vals.x_to_index_eq, basis_n] at h_a_eq
        simp [XVals.x_vals, XVals.x_to_index, treeNum_neq_zero] at h_a_eq
        rw [← Finsupp.single_neg] at h_a_eq
        rw [Finsupp.single_eq_single_iff] at h_a_eq
        simp at h_a_eq
        have bad := h_a_eq.2
        contradiction
      | .left t2_parent_parent =>
          -- b is fresh - it must therefore come from a different node, which will therefore have a different basis element - contradiction.
          simp [TreeNode.getData] at h_a_eq
          apply eq_neg_iff_add_eq_zero.mp at h_a_eq
          have basis_indep: LinearIndependent ℚ n_q_basis := Basis.linearIndependent n_q_basis
          simp [n_q_basis] at basis_indep
          have linear_indep: LinearIndependent ℚ ![fun₀ | (vals.x_to_index (treeNum t1_parent - 1)) => (1 : ℚ), fun₀ | (vals.x_to_index (treeNum t2_parent_parent - 1)) => 1] := by
            apply LinearIndependent.pair_iff.mpr
            intro s t h_sum_zero
            simp only [linearIndependent_iff', Finsupp.smul_single, smul_eq_mul, mul_one] at basis_indep
            specialize basis_indep {vals.x_to_index (treeNum t1_parent - 1), vals.x_to_index (treeNum t2_parent_parent - 1)}
            have parents_neq: t1_parent ≠ t2_parent_parent := by
              by_contra! other_parents_eq
              rw [other_parents_eq, add_eq_zero_iff_eq_neg] at h_a_eq
              have eq_zero: (fun₀ | (vals.x_to_index (treeNum t2_parent_parent - 1)) => 1) = 0 := by
                simp [XVals.x_vals, treeNum_neq_zero] at h_a_eq
                rw [← Finsupp.single_neg, Finsupp.single_eq_single_iff] at h_a_eq
                simp only [true_and, one_ne_zero, neg_eq_zero, and_self, or_false] at h_a_eq
                contradiction
              simp at eq_zero
            have base_nums_not_eq: treeNum t1_parent ≠  treeNum t2_parent_parent :=
              Function.Injective.ne treeNum_injective parents_neq
            have treeNum_t1_neq_zero := treeNum_neq_zero t1_parent
            have treeNum_t2_neq_zero := treeNum_neq_zero t2_parent_parent
            have nums_not_eq: treeNum t1_parent - 1 ≠ treeNum t2_parent_parent - 1 := by
              by_contra!
              apply_fun (fun y => y + 1) at this
              have minus_plus_t1: treeNum t1_parent - 1 + 1 = treeNum t1_parent := by omega
              have minus_plus_t2: treeNum t2_parent_parent - 1 + 1 = treeNum t2_parent_parent := by omega
              rw [minus_plus_t1, minus_plus_t2] at this
              contradiction
            have num_reverse: treeNum t2_parent_parent - 1 ≠ treeNum t1_parent - 1 :=
              id (Ne.symm nums_not_eq)
            have val_treeNums_neq: vals.x_to_index (treeNum t2_parent_parent - 1) ≠ vals.x_to_index (treeNum t1_parent - 1) := by
              apply Function.Injective.ne vals.x_to_index_inj num_reverse
            let g : ℕ → ℚ := fun n => if n = vals.x_to_index (treeNum t1_parent - 1) then s else if n = (vals.x_to_index (treeNum t2_parent_parent - 1)) then t else 0
            have finsum_to_pair := Finset.sum_pair (f := fun x => fun₀ | x => g x) val_treeNums_neq.symm
            specialize basis_indep g
            simp only [g] at basis_indep
            simp [g] at finsum_to_pair
            simp only [finsum_to_pair] at basis_indep
            simp only [val_treeNums_neq] at basis_indep
            simp at h_sum_zero
            specialize basis_indep h_sum_zero
            have s_eq_zero := basis_indep (vals.x_to_index (treeNum t1_parent - 1))
            simp at s_eq_zero
            have t_eq_zero := basis_indep (vals.x_to_index (treeNum t2_parent_parent - 1))
            simp [val_treeNums_neq] at t_eq_zero
            exact ⟨s_eq_zero, t_eq_zero⟩
          simp [LinearIndependent.pair_iff] at linear_indep
          simp [XVals.x_vals, treeNum_neq_zero, basis_n] at h_a_eq
          simp [XVals.x_to_index] at linear_indep
          specialize linear_indep 1 1 h_a_eq
          contradiction
      | .right t2_parent_parent =>
        --  b = p - q for some p and q. We know that p and q have disjoint coordinates, and q is not zero, so we have two different representations for 'a' - impossible.
        simp [TreeNode.getData, vals.x_to_index_eq, basis_n] at h_a_eq
        by_cases tree_a_zero: t2_parent_parent.getData.a = 0
        · simp [tree_a_zero] at h_a_eq
          match t2_parent_parent with
          | .root =>
            simp [TreeNode.getData] at tree_a_zero
            simp [TreeNode.getData, XVals.x_vals, treeNum_neq_zero] at h_a_eq
            simp [Finsupp.single_eq_single_iff] at h_a_eq
            have treeNum_t1_gt: 1 < treeNum t1_parent := by
              exact treeNum_gt_one t1_parent
            omega
          | .left ancestor =>
            simp [TreeNode.getData] at tree_a_zero
            have b_nonzero := tree_vals_nonzero ancestor
            contradiction
          | .right ancestor =>
            simp [TreeNode.getData, XVals.x_vals, treeNum_neq_zero] at tree_a_zero
        · have vals_neq := basis_neq_elem_diff t2_parent_parent (vals.x_to_index (treeNum t1_parent - 1)) 1 (-1) 1 (by simp) (by simp) (by simp) tree_a_zero
          simp only [one_smul, neg_one_smul, ← sub_eq_add_neg] at vals_neq
          simp [XVals.x_vals, treeNum_neq_zero] at h_a_eq
          simp [XVals.x_to_index] at vals_neq
          contradiction
    | .right t2_parent =>
      -- If they're both right trees, contradiction - all right trees have unique 'a' values
      simp [TreeNode.getData] at h_a_eq
      apply vals.x_inj at h_a_eq
      apply treeNum_injective at h_a_eq
      simp [h_a_eq] at this

-- The main lemma - if two tree nodes have the same `a` values, then they're the same node.
-- This implies that `f(g)` (defined as mapping `g = tree.getData.a` to `tree.getData.b`) is a partial function
-- (as we only have oen node with `g = tree.getData.a` to pick from)
lemma partial_function {vals: XVals}: ∀ {t1 t2: @TreeNode vals}, (t1.getData.a = t2.getData.a) → t1 = t2 := by
  intro t1 t2
  by_contra!
  -- Obtaain the smallest (by `treeNum`) counterexample from the set of all counterexamples, and use it
  -- with `partial_function_inner`
  let counterexamples := {(t1, t2) : (@TreeNode vals × TreeNode) | t1.getData.a = t2.getData.a ∧ t1 ≠ t2}
  have counter_nonempty: counterexamples.Nonempty := by
    simp only [Set.Nonempty, ne_eq, Set.mem_setOf_eq, Prod.exists, counterexamples]
    use t1, t2
  let counter_nums := ((fun (t1, _) => treeNum t1) '' counterexamples)
  let counter_nums_nonempty : counter_nums.Nonempty := by
    simp only [Set.image_nonempty, counter_nums]
    exact counter_nonempty
  have min_mem := Nat.sInf_mem counter_nums_nonempty
  simp only [Set.mem_image, Prod.exists, exists_and_right, counter_nums] at min_mem
  obtain ⟨a, ⟨x, a_x_in⟩, treenum_eq_inf⟩ := min_mem
  have new_min_treeNum_le: ∀ (tree1 tree2: @TreeNode vals), tree1.getData.a = tree2.getData.a ∧ tree1 ≠ tree2 → treeNum a ≤ treeNum tree1 := by
    intro tree1 tree2 h_neq
    have trees_in: (tree1, tree2) ∈ counterexamples := by
      simp only [ne_eq, Set.mem_setOf_eq, counterexamples]
      exact h_neq
    have tree1_num_in: treeNum tree1 ∈ counter_nums := by
      simp only [counter_nums, Set.mem_image, Set.mem_setOf_eq]
      use (tree1, tree2)
    rw [treenum_eq_inf]
    exact Nat.sInf_le tree1_num_in
  exact partial_function_inner a_x_in.1 new_min_treeNum_le a_x_in.2

def g_exclude := {g: G // g ≠ 0 }

-- A bijection between G and ℕ, with (0 : ℕ) mapped to (0 : G)
noncomputable def biject_with_zero: Equiv G ℕ := by
  haveI g_exclude_countable: Countable g_exclude := Subtype.countable
  haveI g_exclude_infinite: Infinite g_exclude := by
    by_contra!
    simp at this
    have g_eq_union : @Set.univ G = Set.range (fun g: g_exclude => g.val) ∪ {0} := by
      apply Set.Subset.antisymm_iff.mpr
      refine ⟨?_, ?_⟩
      · intro g _
        by_cases g_zero: g = 0
        · simp [g_zero]
        · apply Set.mem_union_left
          simp only [ne_eq, Set.mem_range]
          use ⟨g, g_zero⟩
      · intro g
        simp
    have range_finite: Set.Finite (Set.range fun g: g_exclude ↦ g.val) :=
      @Set.finite_range _ _ _ this
    have finite_union := Set.Finite.union range_finite (Set.finite_singleton 0)
    rw [← g_eq_union] at finite_union
    have g_infinite: Set.Infinite (@Set.univ G) := Set.infinite_univ
    contradiction
  let default_equiv := Classical.choice (nonempty_equiv_of_countable (α := g_exclude) (β := ℕ))
  exact {
    toFun := fun g ↦ by
      by_cases g_eq_zero: g = 0
      · exact 0
      · exact 1 + default_equiv.toFun ⟨g, g_eq_zero⟩
    invFun := fun n => by
      by_cases n = 0
      · exact 0
      · exact (default_equiv.invFun (n - 1)).val
    left_inv := by
      rw [Function.LeftInverse]
      intro x
      by_cases x_zero: x = 0
      <;> simp [x_zero]
    right_inv := by
      rw [Function.RightInverse]
      intro x
      by_cases x_zero: x = 0
      · simp [x_zero]
      · simp [x_zero]
        have val_neq_zero: (default_equiv.symm (x - 1)).val ≠ 0 :=
          (default_equiv.symm (x - 1)).property
        simp only [val_neq_zero, ↓reduceIte]
        omega
  }

@[irreducible] noncomputable def g_enumerate: ℕ → G := biject_with_zero.symm

lemma g_enum_zero_eq_zero: g_enumerate 0 = 0 := by simp [g_enumerate, biject_with_zero]

lemma g_enum_nonzero_eq_nonzero (n: ℕ) (hn: n > 0): g_enumerate n ≠ 0 := by
  simp only [g_enumerate, biject_with_zero, ne_eq, Equiv.toFun_as_coe, Equiv.invFun_as_coe,
    dite_eq_ite, Equiv.coe_fn_symm_mk, ite_eq_left_iff, Classical.not_imp]
  refine ⟨by omega, ?_⟩
  have exclude_not_zero: ∀ g: g_exclude, g.val ≠ 0 := fun g ↦ g.property
  simp [exclude_not_zero]

@[irreducible] noncomputable def g_to_num (g: G): ℕ := biject_with_zero g

def g_enum_inverse (g: G): g_enumerate (g_to_num g) = g := by simp [g_enumerate, g_to_num]

lemma g_num_zero_eq_zero: g_to_num 0 = 0 := by simp [g_to_num, biject_with_zero]

-- Linear independence alone is insufficient to prove this - we could have an alterate definition of TreeNode
-- with linearly independent elements, but with the root re-appearing somewhere later on
lemma tree_b_neq_root_mul {vals: XVals} (t: @TreeNode vals) (a: ℚ): t.getData.b ≠ a • vals.root_elem := by
  induction t with
  | root =>
    rw [TreeNode.getData, ne_eq]
    have tree_sup := vals.supp_gt 0
    simp only [Finsupp.coe_basisSingleOne, zero_mul, add_zero] at tree_sup
    have supp_ne_zero := Finsupp.support_single_ne_zero (2 ^ vals.i) (b := (1 : ℚ)) (by simp)
    rw [supp_ne_zero] at tree_sup
    simp only [Finset.min_singleton, WithTop.coe_pow, WithTop.coe_ofNat] at tree_sup
    by_contra!
    have app_eq := DFunLike.congr (x := vals.x_to_index 0) this rfl
    simp only [XVals.x_vals, one_ne_zero, ↓reduceIte, Finsupp.coe_basisSingleOne, tsub_self,
      zero_mul, add_zero, XVals.x_to_index, Finsupp.single_eq_same, Finsupp.coe_smul, Pi.smul_apply,
      smul_eq_mul] at app_eq
    have eval_zero: vals.root_elem (2 ^ vals.i) = 0 := by
      rw [← Finsupp.not_mem_support_iff]
      exact Finset.not_mem_of_max_lt_coe tree_sup
    rw [eval_zero] at app_eq
    simp only [mul_zero, one_ne_zero] at app_eq
  | left t1_parent _ =>
    rw [TreeNode.getData, ne_eq]
    have tree_sup := vals.supp_gt (treeNum t1_parent - 1)
    simp only [Finsupp.coe_basisSingleOne] at tree_sup
    have supp_ne_zero := Finsupp.support_single_ne_zero (2 ^ vals.i + (treeNum t1_parent - 1) * 2 ^ (vals.i + 1)) (b := (1 : ℚ)) (by simp)
    rw [supp_ne_zero] at tree_sup
    simp only [Finset.min_singleton, WithTop.coe_add, WithTop.coe_pow, WithTop.coe_ofNat,
      WithTop.coe_mul, WithTop.coe_sub, ENat.some_eq_coe, WithTop.coe_one] at tree_sup
    by_contra!
    have app_eq := DFunLike.congr (x := vals.x_to_index ((treeNum t1_parent - 1))) this rfl
    simp only [XVals.x_vals, Finsupp.coe_basisSingleOne, XVals.x_to_index, Finsupp.coe_smul,
      Pi.smul_apply, smul_eq_mul] at app_eq
    have eval_zero: vals.root_elem (2 ^ vals.i + (treeNum t1_parent - 1) * 2 ^ (vals.i + 1)) = 0 := by
      rw [← Finsupp.not_mem_support_iff]
      exact Finset.not_mem_of_max_lt_coe tree_sup
    rw [eval_zero] at app_eq
    simp [treeNum_neq_zero] at app_eq
  | right t2_parent h_parent =>
    simp only [TreeNode.getData, ne_eq]
    by_contra!
    match t2_parent with
    | .root =>
      simp [TreeNode.getData] at this
      simp [XVals.x_vals] at this
      have app_eq := DFunLike.congr (x := 2^(vals.i)) this rfl
      simp at app_eq
      have not_supp := xvals_root_not_supp vals 0
      simp [XVals.x_to_index] at not_supp
      simp [not_supp] at app_eq
    | .left t2_parent_parent =>
      simp [TreeNode.getData, XVals.x_vals, treeNum_neq_zero] at this
      let tree_comb := tree_linear_comb t2_parent_parent
      have app_eq := DFunLike.congr (x := 2 ^ vals.i + (treeNum t2_parent_parent - 1) * 2 ^ (vals.i + 1)) this rfl
      have not_supp := xvals_root_not_supp vals (treeNum t2_parent_parent - 1)
      simp [XVals.x_to_index] at not_supp
      simp [not_supp] at app_eq
      have outside_support: ∀ x ∈ Finset.range (treeNum t2_parent_parent), (vals.x_vals x) (vals.x_to_index (treeNum t2_parent_parent - 1)) = 0 := by
        intro x hx
        simp [XVals.x_to_index]
        by_cases x_eq_zero: x = 0
        · simp [XVals.x_vals, x_eq_zero]
          have not_supp := xvals_root_not_supp vals (treeNum t2_parent_parent - 1)
          simp [XVals.x_to_index] at not_supp
          simp [not_supp]
        · simp [XVals.x_vals, x_eq_zero]
          have x_minus_lt: x - 1 < (treeNum t2_parent_parent - 1) := by
            simp at hx
            omega
          simp [Finsupp.single_apply]
          omega
      rw [tree_comb.b_eq] at app_eq
      simp at app_eq
      rw [Finset.sum_eq_zero] at app_eq
      rotate_left 1
      · intro x hx
        have outside := outside_support x hx
        simp [XVals.x_to_index] at outside
        simp [outside]
      · simp at app_eq
    | .right t2_parent_parent =>
      simp [TreeNode.getData] at this
      simp [TreeNode.getData, XVals.x_vals, treeNum_neq_zero] at this
      let tree_comb := tree_linear_comb t2_parent_parent
      have app_eq := DFunLike.congr (x := 2 ^ vals.i + (treeNum t2_parent_parent - 1) * 2 ^ (vals.i + 1)) this rfl
      have not_supp := xvals_root_not_supp vals (treeNum t2_parent_parent - 1)
      simp [XVals.x_to_index] at not_supp
      simp [not_supp] at app_eq
      have outside_support: ∀ x, x < treeNum t2_parent_parent → (vals.x_vals x) (vals.x_to_index (treeNum t2_parent_parent - 1)) = 0 := by
        intro x hx
        simp [XVals.x_to_index]
        by_cases x_eq_zero: x = 0
        · simp [XVals.x_vals, x_eq_zero]
          have not_supp := xvals_root_not_supp vals (treeNum t2_parent_parent - 1)
          simp [XVals.x_to_index] at not_supp
          simp [not_supp]
        · simp [XVals.x_vals, x_eq_zero]
          have x_minus_lt: x - 1 < (treeNum t2_parent_parent - 1) := by
            simp at hx
            omega
          simp [Finsupp.single_apply]
          omega
      rw [tree_comb.b_eq] at app_eq
      simp at app_eq
      rw [Finset.sum_eq_zero] at app_eq
      rotate_left 1
      · intro x hx
        simp at hx
        have outside := outside_support x (by omega)
        simp [XVals.x_to_index] at outside
        simp [outside]
      rw [tree_comb.a_eq] at app_eq
      simp at app_eq
      rw [Finset.sum_eq_zero] at app_eq
      rotate_left 1
      · intro x hx
        simp at hx
        have outside := outside_support x (by omega)
        simp [XVals.x_to_index] at outside
        simp [outside]
      simp at app_eq

attribute [local instance] Classical.propDecidable

-- The element `g` has a negative value in its range (e.g. `basis_n 0 - basis_n 2`)
-- Certain elements in the tree (e.g. 'fresh' elements consisting of a single basis value)
-- never have negative values in their range, so we can use this condition to rule out
-- certain trees as candidates for `tree.getData.a = g`
def finsuppHasNeg (g: G) := ∃ x ∈ (Set.range g), x < 0

lemma left_tree_supp_increasing {vals: XVals} (t: @TreeNode vals): t.left.getData.a.support.max < t.left.getData.b.support.max := by
  simp [TreeNode.getData]
  let tree_comb := tree_linear_comb t
  have eq_union := Finsupp.support_sum_eq_biUnion (Finset.range (treeNum t)) ?_ (g := fun i => tree_comb.b_coords i • vals.x_vals i)
  rotate_left
  · intro a b a_neq_b
    by_cases a_eq_zero: a = 0
    · simp [a_eq_zero, XVals.x_vals]
      have b_neq_zero: b ≠ 0 := by omega
      simp [b_neq_zero]
      by_cases g_zero_eq_zero: tree_comb.b_coords 0 = 0
      · simp [g_zero_eq_zero]
      · simp [g_zero_eq_zero]
        by_cases g_b_eq_zero: tree_comb.b_coords b = 0
        · simp [g_b_eq_zero]
        · rw [Finsupp.support_single_ne_zero]
          simp
          apply xvals_root_not_supp
          exact g_b_eq_zero
    ·
      simp [XVals.x_vals, a_eq_zero]
      by_cases g_a_zero: tree_comb.b_coords a = 0
      ·
        simp [g_a_zero]
      ·
        rw [Finsupp.support_single_ne_zero]
        simp
        by_cases b_eq_zero: b = 0
        · simp [b_eq_zero]
          right
          apply xvals_root_not_supp
        · simp [b_eq_zero]
          rw [← Finsupp.not_mem_support_iff]
          by_cases g_b_zero: tree_comb.b_coords b = 0
          · simp [g_b_zero]
          ·
            rw [Finsupp.support_single_ne_zero]
            simp
            omega
            simp [g_b_zero]
        simp [g_a_zero]

  have treeNum_t_gt: 1 < treeNum t := by
    exact treeNum_gt_one t
  have minus_one_not_zero: treeNum t - 1 ≠ 0 := by omega

  have supp_max_sum: (∑ i ∈ Finset.range (treeNum t), tree_comb.b_coords i • vals.x_vals i).support.max ≤ (vals.x_vals ((treeNum t) - 1)).support.max := by
    rw [eq_union]
    simp [XVals.x_vals]
    simp [minus_one_not_zero]
    rw [Finsupp.support_single_ne_zero]
    simp
    norm_cast
    intro a x hx not_zero
    by_cases x_eq_zero: x = 0
    · simp [x_eq_zero] at not_zero
      have in_supp := not_zero.2
      rw [← ne_eq] at in_supp
      rw [← Finsupp.mem_support_iff] at in_supp
      have supp_lt := vals.supp_gt (treeNum t - 1 - 1)
      simp [basis_n] at supp_lt
      simp [Finsupp.support_single_ne_zero] at supp_lt
      have a_le_max := Finset.le_max in_supp
      norm_cast at supp_lt
      exact le_trans a_le_max (le_of_lt supp_lt)


    · simp [x_eq_zero] at not_zero
      rw [← ne_eq] at not_zero
      by_cases g_x_zero: tree_comb.b_coords x = 0
      ·
        simp [g_x_zero]
        rw [g_x_zero] at not_zero
        simp at not_zero
      ·
        rw [← Finsupp.mem_support_iff] at not_zero
        rw [Finsupp.support_single_ne_zero] at not_zero
        simp at not_zero
        rw [not_zero]
        rw [Nat.cast_withBot]
        rw [Nat.cast_withBot]
        norm_cast
        field_simp
        omega
        exact g_x_zero
    simp


  have m_supp_max_lt: (vals.x_vals (treeNum t - 1)).support.max < (vals.x_vals (treeNum t)).support.max := by
    simp [XVals.x_vals, treeNum_neq_zero]
    simp [minus_one_not_zero]
    simp [Finsupp.support_single_ne_zero]
    norm_cast
    rw [Nat.cast_withBot]
    rw [Nat.cast_withBot]
    norm_cast
    field_simp
    omega

  rw [tree_comb.b_eq]
  exact lt_of_le_of_lt supp_max_sum m_supp_max_lt

-- The initial `XVals`, corresponding to `n = 0` (which our enumeration of `G` maps to the zero vector)
def x_vals_zero: XVals := {
  i := 0
  root_elem := 0
  supp_gt := by
    intro n
    simp
    rw [Finsupp.support_single_ne_zero]
    · simp
      norm_cast
      apply WithBot.bot_lt_coe
    · simp
  root_nonzero := by simp
}

-- Holds data used for evaluating our function 'f' at a given element 'g' of the vector space
structure FData (g: G) where
  -- The previous `XVals` from the recursive construction of the function `f`.
  -- This includes whichever `XVals` contains a tree with an `a` value equal to `g`
  vals: Finset XVals

  -- Our chosen `XVals` and `TreeNode`, along with proofs about how they relate to the function argument `g`
  cur: XVals
  cur_in_vals: cur ∈ vals
  tree: @TreeNode cur
  a_val: tree.getData.a = g

  distinct_i: ∀ a ∈ vals, ∀ b ∈ vals, a.i = b.i → a = b
  distinct_trees: ∀ a ∈ vals, ∀ b ∈ vals, (∃ ta: @TreeNode a, ∃ tb: @TreeNode b, ta.getData.a = tb.getData.a) → a = b
  vals_has_zero : x_vals_zero ∈ vals

  -- Helper lemmas used for proving some non-implications - when we evaluate at concrete elements (e.g. `x_1 - x_3`),
  -- we can use this to bound the support of the resulting value, which will help us prove that the overall
  -- expression is not zero.
  supp_increasing: finsuppHasNeg tree.getData.a → tree.getData.a.support.max < tree.getData.b.support.max' (tree_b_supp_nonempty tree)
  supp_max_pos: finsuppHasNeg tree.getData.a → tree.getData.b (tree.getData.b.support.max' (tree_b_supp_nonempty tree)) > 0


lemma nonpos_not_tree_right {vals: XVals} (t: @TreeNode vals) (ht: finsuppHasNeg t.getData.a): ¬(∃ parent: TreeNode, parent.right = t) := by
  by_contra!
  obtain ⟨parent, hparent⟩ := this
  simp only [finsuppHasNeg] at ht
  obtain ⟨x, hx⟩ := ht
  rw [← hparent] at hx
  rw [TreeNode.getData] at hx
  simp only [XVals.x_vals, treeNum_neq_zero] at hx
  simp at hx
  obtain ⟨y, hy⟩ := hx.1
  rw [Finsupp.single_apply] at hy
  by_cases eq_val: 2 ^ vals.i + (treeNum parent - 1) * 2 ^ (vals.i + 1) = y
  · simp [eq_val] at hy
    linarith
  · simp [eq_val] at hy
    linarith

-- All of the data associated with evaluating `f` at a given element `g`
-- The actual function `f` is defined in terms of this - we use the proofs
-- contained in `FData` to prove non-implications
noncomputable def f_data (n: ℕ): FData (g_enumerate n) := by
  match hn: n with
  | 0 =>
    let x_vals := x_vals_zero
    exact {
      vals := {x_vals},
      cur := x_vals,
      cur_in_vals := by simp,
      tree := TreeNode.root,
      a_val := by
        simp only [TreeNode.getData, x_vals, XVals.root_elem, hn]
        rw [g_enum_zero_eq_zero]
        simp only [x_vals_zero]
      distinct_i := by simp
      distinct_trees := by simp
      vals_has_zero := by simp
      supp_increasing := by
        simp [TreeNode.getData, finsuppHasNeg, x_vals, x_vals_zero]
      supp_max_pos := by
        simp [TreeNode.getData, finsuppHasNeg, x_vals, x_vals_zero]
  }
  | a + 1 =>
    let prev_x_vals := f_data a
    by_cases has_tree: ∃ x_vals: XVals, ∃ t: @TreeNode x_vals, x_vals ∈ prev_x_vals.vals ∧ t.getData.a = g_enumerate n
    · exact {
      vals := prev_x_vals.vals,
      cur := Classical.choose has_tree,
      vals_has_zero := prev_x_vals.vals_has_zero
      cur_in_vals := (Classical.choose_spec (Classical.choose_spec has_tree)).1,
      tree := Classical.choose (Classical.choose_spec has_tree)
      a_val := by
        have tree_eq := (Classical.choose_spec (Classical.choose_spec has_tree)).2
        have n_eq: n = a  +1 := by
          simp [hn]
        rw [← n_eq]
        exact tree_eq
      distinct_i := prev_x_vals.distinct_i
      distinct_trees := prev_x_vals.distinct_trees
      supp_max_pos := by
        match Classical.choose (Classical.choose_spec has_tree) with
        | .root =>
          intro _
          simp [TreeNode.getData, XVals.x_vals, Finsupp.support_single_ne_zero]
        | .left parent =>
          intro _
          simp [TreeNode.getData, XVals.x_vals, treeNum_neq_zero, Finsupp.support_single_ne_zero]
        | .right parent =>
          intro has_neg
          have not_right := nonpos_not_tree_right _ has_neg
          simp at not_right
      supp_increasing := by
        match Classical.choose (Classical.choose_spec has_tree) with
        | .root =>
          simp [TreeNode.getData]
          have supp_gt := (Classical.choose has_tree).supp_gt 0
          simp [basis_n] at supp_gt
          simp [Finsupp.support_single_ne_zero _ ?_] at supp_gt
          simp [XVals.x_vals]
          simp [Finsupp.support_single_ne_zero _ ?_]
          exact fun _ ↦ supp_gt
        | .left parent =>
          simp [TreeNode.getData]
          intro _
          have increasing := left_tree_supp_increasing parent
          simp [TreeNode.getData] at increasing
          rw [← WithBot.coe_natCast]
          simp
          rw [Finset.coe_max']
          exact increasing
        | .right parent =>
          intro has_neg
          have not_right := nonpos_not_tree_right _ has_neg
          simp at not_right
    }
    ·
      have img_nonempty : (prev_x_vals.vals.image XVals.i).Nonempty := by
        simp [Finset.Nonempty]
        use prev_x_vals.cur.i
        use prev_x_vals.cur
        refine ⟨prev_x_vals.cur_in_vals, rfl⟩
      let max_i := (prev_x_vals.vals.image XVals.i).max' img_nonempty
      let max_root_supp := ({(g_enumerate n).support.max.getD 0} ∪ (prev_x_vals.vals.image fun v => v.root_elem.support.max.getD 0)).max' (
        by
          refine ⟨Option.getD (g_enumerate n).support.max 0, ?_⟩
          simp
      )

      have g_supp_le: (g_enumerate n).support.max.getD 0 ≤ max max_i max_root_supp := by
        simp [le_max_iff]
        right
        simp [max_root_supp]
        apply Finset.le_max'
        simp


      have g_supp_lt: (g_enumerate n).support.max.getD 0 < max max_i max_root_supp + 1 := by
        omega

      have new_vals_not_supp: ∀ i, (2^(((max max_i max_root_supp) + 1)) + i*2^(((max max_i max_root_supp) + 1))) ∉ (g_enumerate n).support := by
        intro i
        have supp_max_lt: (g_enumerate n).support.max.getD 0 < (2 ^ (max max_i max_root_supp + 1)) := by
          have lt_self_pow := Nat.lt_pow_self Nat.one_lt_two (n := (max max_i max_root_supp + 1))
          omega
        apply Finset.not_mem_of_max_lt_coe
        match h_supp_max: (g_enumerate n).support.max with
        | WithBot.some max_val =>
          norm_cast
          simp [h_supp_max] at supp_max_lt
          omega
        | ⊥ =>
          apply WithBot.bot_lt_coe

      have new_vals_not_supp_double_plus: ∀ i, (2^(((max max_i max_root_supp) + 1)) + i*2^(((max max_i max_root_supp) + 1 + 1))) ∉ (g_enumerate n).support := by
        intro i
        have supp_max_lt: (g_enumerate n).support.max.getD 0 < (2 ^ (max max_i max_root_supp + 1)) := by
          have lt_self_pow := Nat.lt_pow_self Nat.one_lt_two (n := (max max_i max_root_supp + 1))
          omega
        apply Finset.not_mem_of_max_lt_coe
        match h_supp_max: (g_enumerate n).support.max with
        | WithBot.some max_val =>
          norm_cast
          simp [h_supp_max] at supp_max_lt
          omega
        | ⊥ =>
          apply WithBot.bot_lt_coe

      have lt_self_pow := Nat.lt_pow_self Nat.one_lt_two (n := (max max_i max_root_supp + 1))

      let new_x_vals: XVals := {
        i := ((max max_i max_root_supp) + 1)
        root_elem := g_enumerate n
        supp_gt := by
          intro x
          simp [basis_n]
          rw [Finsupp.support_single_ne_zero]
          · simp
            norm_cast
            have supp_max_lt: (g_enumerate n).support.max.getD 0 < (2 ^ (max max_i max_root_supp + 1)) := by
              omega
            match h_supp_max: (g_enumerate n).support.max with
            | WithBot.some max_val =>
              norm_cast
              simp [h_supp_max] at supp_max_lt
              rw [Nat.cast_withBot]
              rw [WithBot.coe_lt_coe]
              omega
            | ⊥ =>
              apply WithBot.bot_lt_coe
          · simp
        root_nonzero := by
          simp
          apply g_enum_nonzero_eq_nonzero
          omega
      }


      have prev_vals_root_not_supp: ∀ vals ∈ prev_x_vals.vals, ∀ i, (new_x_vals.x_to_index i) ∉ vals.root_elem.support := by
        intro vals h_vals i
        simp only [XVals.x_to_index, new_x_vals]
        have supp_max_lt: vals.root_elem.support.max.getD 0 < (2 ^ (max max_i max_root_supp + 1)) := by
          have le_max_plus: vals.root_elem.support.max.getD 0 ≤ max max_i max_root_supp := by
            simp
            right
            apply Finset.le_max'
            simp
            right
            use vals
          omega

        apply Finset.not_mem_of_max_lt_coe
        match h_supp_max: vals.root_elem.support.max with
        | WithBot.some max_val =>
          simp [h_supp_max] at supp_max_lt
          rw [WithBot.coe_lt_coe]
          omega
        | ⊥ =>
          apply WithBot.bot_lt_coe


      exact {
        vals := prev_x_vals.vals ∪ {new_x_vals},
        cur := new_x_vals,
        cur_in_vals := by simp,
        tree := TreeNode.root,
        supp_max_pos := by
          simp [TreeNode.getData, XVals.x_vals, Finsupp.support_single_ne_zero]
        supp_increasing := by
          simp [TreeNode.getData, XVals.x_vals]
          simp [Finsupp.support_single_ne_zero]
          intro has_neg
          have le_getd : (g_enumerate n).support.max ≤ Option.getD (g_enumerate n).support.max 0 := by
            match h_max: (g_enumerate n).support.max with
            | .some max_val =>
              rw [← WithBot.some_eq_coe]
              simp [h_max]
              rw [WithBot.some_eq_coe]
              rfl
            | ⊥ =>
              simp [h_max]
          rw [← WithBot.coe_lt_coe] at g_supp_lt
          rw [← WithBot.coe_lt_coe] at lt_self_pow
          have first_trans := LE.le.trans_lt le_getd g_supp_lt
          have second_trans := lt_trans first_trans lt_self_pow
          simp at second_trans
          exact second_trans

        a_val := by
          simp only [TreeNode.getData, new_x_vals, XVals.root_elem, hn]


        vals_has_zero := Finset.mem_union_left {new_x_vals} prev_x_vals.vals_has_zero

        distinct_trees := by
          have helper_distinct: ∀ a ∈ prev_x_vals.vals, ∀ b, b = new_x_vals → (∃ ta: @TreeNode a, ∃ tb: @TreeNode b, ta.getData.a = tb.getData.a) → a = b := by
            intro a a_prev b b_new exists_trees
            obtain ⟨ta, tb, h_tree_eq⟩ := exists_trees
            let ta_comb := tree_linear_comb ta
            let tb_comb := tree_linear_comb tb
            have ta_sum := ta_comb.a_eq
            have tb_sum := tb_comb.a_eq

            have b_i_nonzero: b.i ≠ 0 := by
              simp [b_new, new_x_vals]

            have tb_g_supp_nonempty: tb_comb.a_coords.support.Nonempty := by
              by_contra!
              have tb_eq_zero: tb_comb.a_coords = 0 := by
                simp at this
                exact this
              simp [tb_eq_zero] at tb_sum
              match h_tb: tb with
              | .root =>
                have tb_a_nonzero := b.root_nonzero b_i_nonzero
                simp [h_tb, TreeNode.getData] at tb_sum
                contradiction
              | .left tb_parent =>
                simp [h_tb, TreeNode.getData] at tb_sum
                have b_nonzero := (tree_vals_nonzero tb_parent)
                contradiction
              | .right tb_parent =>
                simp [h_tb, TreeNode.getData] at tb_sum
                simp [XVals.x_vals] at tb_sum
                simp [treeNum_neq_zero] at tb_sum

            by_cases tb_root: tb = TreeNode.root
            ·
              simp [tb_root, TreeNode.getData] at h_tree_eq
              have simple_have_tree: ∃ x_vals: XVals, ∃ t: @TreeNode x_vals, x_vals ∈ prev_x_vals.vals ∧ t.getData.a = g_enumerate n := by
                use a
                use ta
                refine ⟨a_prev, ?_⟩
                rw [h_tree_eq]
                simp [b_new, new_x_vals]
              contradiction


            have nonzero_b_coord: ∃ y, y + 1 ∈ Finset.range (treeNum tb) ∧ tb_comb.a_coords (y + 1) ≠ 0 := by
              by_contra!
              have tb_coords_zero: ∀ z ∈ Finset.range (treeNum tb), z > 0 → tb_comb.a_coords z = 0 := by
                intro z hz z_gt_zero
                have z_minus_plus: z - 1 + 1 = z := by
                  apply Nat.sub_add_cancel
                  omega

                specialize this (z - 1)
                simp [z_minus_plus] at this
                simp at hz
                exact this hz
              rw [Finset.sum_eq_single_of_mem 0 ?_ ?_] at tb_sum
              rotate_left 1
              · simp
                have treeNum_tb_one: 1 < treeNum tb := by
                  simp [treeNum_gt_one tb]
                omega
              · intro x hx x_neq_zero
                specialize tb_coords_zero x hx (by omega)
                simp [tb_coords_zero]


              match h_tb: tb with
              | .root =>
                simp [h_tb] at tb_sum
                contradiction
              | .left tb_parent =>
                simp [h_tb, TreeNode.getData] at tb_sum
                apply_fun (fun y => -y) at tb_sum
                simp at tb_sum
                have neq_mul := tree_b_neq_root_mul tb_parent (-(tb_comb.a_coords 0))
                simp at neq_mul
                simp [XVals.x_vals] at tb_sum
                contradiction
              | .right tb_parent =>
                simp [h_tb, TreeNode.getData] at tb_sum
                simp [XVals.x_vals, b_new, new_x_vals, treeNum_neq_zero] at tb_sum
                have app_eq := DFunLike.congr (x := new_x_vals.x_to_index (treeNum tb_parent - 1)) tb_sum rfl
                simp [XVals.x_to_index, new_x_vals, Finsupp.single_apply] at app_eq
                have eval_to_zero := (new_vals_not_supp_double_plus (treeNum tb_parent - 1))
                simp [new_x_vals, XVals.x_to_index] at eval_to_zero
                -- This gives us a contradiction
                simp [eval_to_zero] at app_eq

            obtain ⟨y, y_plus_in_range, h_y⟩ := nonzero_b_coord

            have outside_support: ∀ i ∈ Finset.range (treeNum ta), (a.x_vals i) (b.x_to_index y) = 0 := by
              intro i _
              simp [XVals.x_vals, XVals.x_to_index]
              by_cases i_eq_zero: i = 0
              · simp [i_eq_zero]
                have y_outside := prev_vals_root_not_supp a a_prev y
                simp [new_x_vals, XVals.x_to_index] at y_outside
                simp [b_new, new_x_vals]
                exact y_outside
              · simp [i_eq_zero]
                simp [b_new, new_x_vals]
                rw [Finsupp.single_apply]
                simp
                have ai_le_max: a.i ≤ max_i := by
                  dsimp [max_i]
                  apply Finset.le_max'
                  simp
                  use a
                by_contra!

                conv at this =>
                  lhs
                  equals (2 ^ a.i) * (1 + (i - 1) * 2) =>
                    rw [Nat.pow_succ]
                    ring

                conv at this =>
                  rhs
                  equals (2 ^ (max max_i max_root_supp + 1)) * (1 + y * 2) =>
                    rw [Nat.pow_succ]
                    ring


                have two_factor_i: (2^a.i * (1 + ( i - 1)*2)).factorization 2 = a.i := by
                  rw [Nat.factorization_mul]
                  rw [Nat.Prime.factorization_pow (Nat.prime_two)]
                  simp [Nat.factorization_eq_zero_of_not_dvd]
                  simp
                  simp

                have two_factor_max: (2 ^ (max max_i max_root_supp + 1) * (1 + y * 2)).factorization 2 = max max_i max_root_supp + 1 := by
                  rw [Nat.factorization_mul]
                  rw [Nat.Prime.factorization_pow (Nat.prime_two)]
                  simp [Nat.factorization_eq_zero_of_not_dvd]
                  simp
                  simp

                rw [this] at two_factor_i
                rw [two_factor_max] at two_factor_i
                omega

            have rhs_sum: ∀ i ∈ Finset.range (treeNum tb), i ≠ y → ((b.x_vals (i + 1)) (b.x_to_index y) = 0) := by
              intro i _ i_neq_y
              simp [XVals.x_vals, XVals.x_to_index]
              simp [Finsupp.single_apply, i_neq_y]


            by_contra!
            rw [ta_sum] at h_tree_eq
            have eval_both_trees := DFunLike.congr (x := b.x_to_index y) h_tree_eq rfl
            simp at eval_both_trees
            conv at eval_both_trees =>
              lhs
              rw [Finset.sum_eq_zero]
              rfl
              tactic =>
                intro x hx
                simp [outside_support x hx]

            rw [tb_sum] at eval_both_trees
            simp at eval_both_trees
            conv at eval_both_trees =>
              rhs
              rw [Finset.sum_eq_single_of_mem (y + 1) y_plus_in_range]
              rfl
              tactic =>
                intro x _ x_neq_y
                by_cases x_eq_zero: x = 0
                · simp [x_eq_zero, XVals.x_vals, XVals.x_to_index]
                  right
                  have not_i := new_vals_not_supp_double_plus y
                  simp [XVals.x_to_index, new_x_vals] at not_i
                  simp [b_new, new_x_vals]
                  exact not_i
                · simp [XVals.x_vals, XVals.x_to_index, x_eq_zero]
                  right
                  simp [Finsupp.single_apply]
                  omega

            simp [XVals.x_vals, XVals.x_to_index] at eval_both_trees
            rw [eq_comm] at eval_both_trees
            contradiction



          intro a ha b hb exists_trees
          simp at ha
          simp at hb
          match ha with
          | .inl a_prev =>
            match hb with
            | .inl b_prev => apply prev_x_vals.distinct_trees a a_prev b b_prev exists_trees
            | .inr b_new => apply helper_distinct a a_prev b b_new exists_trees
          | .inr a_new =>
            match hb with
            | .inl b_prev =>
              have new_exists: ∃ t_1: @TreeNode b, ∃ t_2: @TreeNode a, t_1.getData.a = t_2.getData.a := by
                obtain ⟨t1, t2, h_eq⟩ := exists_trees
                exact ⟨t2, t1, h_eq.symm⟩
              apply (helper_distinct b b_prev a a_new new_exists).symm
            | .inr b_new => rw [a_new, b_new]

        distinct_i := by
          intro a ha b hb i_eq
          simp at ha
          simp at hb
          match ha with
          | .inl a_prev =>
            match hb with
            | .inl b_prev => apply prev_x_vals.distinct_i a a_prev b b_prev i_eq
            | .inr b_new =>
              have a_le_max: a.i ≤ max_i := by
                dsimp [max_i]
                apply Finset.le_max'
                simp
                use a
              have a_lt_b: a.i < b.i := by
                rw [b_new]
                dsimp [new_x_vals]
                omega
              rw [i_eq] at a_lt_b
              -- obtains a contradiction
              simp at a_lt_b
          | .inr a_new =>
            match hb with
            | .inl b_prev =>
                have b_le_max: b.i ≤ max_i := by
                  dsimp [max_i]
                  apply Finset.le_max'
                  simp
                  use b
                have b_lt_a: b.i < a.i := by
                  rw [a_new]
                  dsimp [new_x_vals]
                  omega
                rw [i_eq] at b_lt_a
                -- obtains a contradiction
                simp at b_lt_a
            | .inr b_new => rw [a_new, b_new]
      }


lemma f_data_subset (a b: ℕ) (hab: a ≤ b): (f_data a).vals ⊆ (f_data b).vals := by
  induction b with
  | zero =>
    have a_eq_zero: a = 0 := by
      omega
    rw [a_eq_zero]
  | succ new_b h_prev =>
    by_cases a_le_new_b: a ≤ new_b
    ·
      have new_b_in: (f_data new_b).vals ⊆ (f_data (new_b + 1)).vals := by
        conv =>
          rhs
          simp [f_data]
        by_cases has_tree: ∃ x_vals ∈ (f_data new_b).vals, ∃ x: @TreeNode x_vals, x.getData.a = g_enumerate (new_b + 1)
        · rw [dite_cond_eq_true]
          simp [has_tree]
        · rw [dite_cond_eq_false]
          · simp
          · simp [has_tree]

      exact Finset.Subset.trans (h_prev a_le_new_b) new_b_in
    ·
      have a_eq_new_b_succ: a = new_b + 1 := by omega
      rw [a_eq_new_b_succ]



noncomputable def f (g: G): G := (f_data (g_to_num g)).tree.getData.b

lemma vals_eq_to_types {vals1 vals2: XVals} (h_vals: vals1 = vals2): @TreeNode vals1 = @TreeNode vals2 := by
  rw [h_vals]

lemma cast_data_eq {vals1 vals2: XVals} (t: @TreeNode vals1) (h_vals: vals1 = vals2): t.getData = (cast (vals_eq_to_types h_vals) t).getData := by
  congr
  rw [heq_comm]
  simp

-- Our main 'evaluation lemma' - given a tree `t`, `f(t.getData.a) = t.getData.b`
lemma f_eval_at {other_vals: XVals} (t: @TreeNode other_vals) {n: ℕ} (hvals: (f_data n).cur = other_vals): f t.getData.a = t.getData.b := by
  simp [f]
  have a_eq := (f_data (g_to_num t.getData.a)).a_val
  have trees_eq := cast_data_eq t hvals.symm

  have t_num_self := (f_data (g_to_num t.getData.a)).cur_in_vals
  have n_self := (f_data n).cur_in_vals

  have x_vals_eq: (f_data (g_to_num t.getData.a)).cur = other_vals := by
    by_cases n_le_num: n ≤ g_to_num t.getData.a
    · have vals_subset := f_data_subset n (g_to_num t.getData.a) n_le_num
      specialize vals_subset n_self
      have a_eq := (f_data (g_to_num t.getData.a)).a_val

      have same_tree: ∃ ta: @TreeNode (f_data n).cur, ∃ tb: @TreeNode (f_data (g_to_num t.getData.a)).cur, ta.getData.a = tb.getData.a := by
        use (cast (vals_eq_to_types hvals.symm) t)
        use (f_data (g_to_num t.getData.a)).tree
        rw [a_eq]
        rw [g_enum_inverse]
        rw [trees_eq]

      have x_vals_eq := (f_data (g_to_num t.getData.a)).distinct_trees (f_data n).cur vals_subset (f_data (g_to_num t.getData.a)).cur t_num_self same_tree
      rw [hvals] at x_vals_eq
      exact x_vals_eq.symm
    · have vals_subset := f_data_subset (g_to_num t.getData.a) n (by linarith)
      specialize vals_subset t_num_self
      have a_eq := (f_data (g_to_num t.getData.a)).a_val

      have same_tree: ∃ tb: @TreeNode (f_data (g_to_num t.getData.a)).cur, ∃ ta: @TreeNode (f_data n).cur, tb.getData.a = ta.getData.a := by
        use (f_data (g_to_num t.getData.a)).tree
        use (cast (vals_eq_to_types hvals.symm) t)
        rw [a_eq]
        rw [g_enum_inverse]
        rw [trees_eq]

      have x_vals_eq := (f_data n).distinct_trees (f_data (g_to_num t.getData.a)).cur vals_subset (f_data n).cur n_self same_tree
      rw [hvals] at x_vals_eq
      exact x_vals_eq


  simp [g_enum_inverse] at a_eq
  have trees_eq := cast_data_eq t x_vals_eq.symm
  have orig_trees_eq := trees_eq
  apply_fun (fun x => TreeData.a x) at trees_eq
  simp [← a_eq] at trees_eq
  rw [partial_function trees_eq, ← orig_trees_eq]


-- The definition of the diamond operator from the paper
noncomputable abbrev diamond (x y: G) := x + (f (y - x))

-- f satisfies the functional equation derived in the paper (based on substituing our diamond definition
-- into Equation 1692)
lemma f_functional_eq (g: G): f (f (- f g)) = g - (f g) := by
  let g_data := f_data (g_to_num g)
  have neg_eq_left: - f g = (f_data (g_to_num g)).tree.left.getData.a := by
    simp [f]
    simp [TreeNode.getData]
  have eval_neg := f_eval_at (f_data (g_to_num g)).tree.left (other_vals := (f_data (g_to_num g)).cur) (n := g_to_num g) rfl
  rw [neg_eq_left]
  rw [eval_neg]

  have left_eq_right_a: (f_data (g_to_num g)).tree.left.getData.b = (f_data (g_to_num g)).tree.right.getData.a := by
    simp [TreeNode.getData]

  have eval_right := f_eval_at (f_data (g_to_num g)).tree.right (other_vals := (f_data (g_to_num g)).cur) (n := g_to_num g) rfl
  rw [left_eq_right_a]
  rw [eval_right]
  simp [TreeNode.getData, f]
  have g_eq := g_data.a_val
  simp only [g_data] at g_eq
  rw [g_eq]
  rw [g_enum_inverse]


lemma diamond_law (x y: G): x = (diamond (x + (y - x) + (f (-(y - x)))) (diamond (x + (y - x) + (f (-(y - x)))) (x + y - x))) := by
  field_simp [diamond, f_functional_eq (x - y)]

lemma neg_f_zero: - f (0) = (f_data 0).tree.left.getData.a := by
  simp [f]
  simp [TreeNode.getData]
  simp only [f_data]
  rw [g_num_zero_eq_zero]
  simp only [XVals.x_vals]
  simp
  simp [f_data]
  simp only [TreeNode.getData, XVals.x_vals]
  simp

lemma f_neg_b {other_vals: XVals} (t: @TreeNode other_vals) {n: ℕ} (hvals: (f_data n).cur = other_vals): f (-t.getData.b) = t.left.getData.b := by
  have eq_tree: -t.getData.b = t.left.getData.a := by
    simp [TreeNode.getData]
  rw [eq_tree]
  rw [f_eval_at (n := n) _ hvals]

-- Proof of our non-implications. The general strategy is to obtain a particular support element
-- (usually the largest one, resulting from repeated applications of `f`), and evaluate both sides
-- of the equation at that element. Most of the terms are shown to drop out (since our element
-- is constructed to be outside the support of most of them), leaving us with a contradiction (0 = 1)
theorem not_equation_23: 0 ≠ (f (0)) + (f (- (f (0)))) := by
  have eval_neg := f_eval_at (f_data 0).tree.left (n := 0) rfl
  rw [neg_f_zero, eval_neg]
  simp [f]
  simp [f_data]
  simp only [TreeNode.getData, XVals.x_vals]
  simp
  have mynum_gt_1 := treeNum_gt_one (@TreeNode.root x_vals_zero)
  have root_neq_zero: treeNum (@TreeNode.root x_vals_zero) ≠ 0 := by
    linarith
  simp [root_neq_zero]
  by_contra!
  have app_eq := DFunLike.congr (x := 1) this rfl
  simp [x_vals_zero] at app_eq
  have val_neq_1: 1 + (treeNum (@TreeNode.root x_vals_zero) - 1) * 2 ≠ 1 := by
    omega
  simp [val_neq_1] at app_eq
  rw [g_num_zero_eq_zero] at app_eq
  simp [f_data] at app_eq
  simp [TreeNode.getData, x_vals_zero, XVals.x_vals] at app_eq


theorem not_equation_47: f (f (f 0)) ≠ 0 := by
  rw [f]
  have vals_nonzero := (tree_vals_nonzero (f_data (g_to_num (f (f 0)))).tree)
  exact vals_nonzero


lemma f_zero_eq: f (0) = (fun₀ | 1 => 1) := by
  have tree_eq: 0 = (@TreeNode.root (x_vals_zero)).getData.a := by
    simp [TreeNode.getData, x_vals_zero]
  rw [tree_eq, f_eval_at (n := 0)]
  simp [TreeNode.getData, x_vals_zero, XVals.x_vals]
  simp [x_vals_zero, f_data]

theorem not_equation_1832: 0 ≠ f (f (0)) + f ((f (0)) - f (f (0))) := by
  simp [f_zero_eq]

  let root_tree: @TreeNode x_vals_zero := TreeNode.root



  have my_one_tree: root_tree.right.left.getData.a  = fun₀ | 1 => 1 := by
    simp [TreeNode.getData, x_vals_zero, XVals.x_vals]

  rw [← my_one_tree, f_eval_at (n := 0)]
  simp [TreeNode.getData, x_vals_zero, XVals.x_vals, treeNum_neq_zero, treeNum]

  have x_diff_has_neg: finsuppHasNeg ((fun₀ | 1 => (1 : ℚ)) - fun₀ | 7 => 1) := by
    simp [finsuppHasNeg]
    use 7
    simp

  have x_diff_supp: ((fun₀ | 1 => (1 : ℚ)) - fun₀ | 7 => 1).support = {1, 7} := by
    rw [ sub_eq_add_neg, ← Finsupp.single_neg]
    have disjoint_supp: Disjoint (fun₀ | 1 => (1 : ℚ)).support (fun₀ | 7 => (-1 : ℚ)).support := by
      simp [Finsupp.support_single_ne_zero]
    rw [Finsupp.support_add_eq disjoint_supp]
    simp
    rw [Finsupp.support_single_ne_zero _ (by simp), Finsupp.support_single_ne_zero _ (by simp)]
    exact rfl

  have supp_increasing := (f_data (g_to_num ((fun₀ | 1 => (1 : ℚ)) - fun₀ | 7 => 1))).supp_increasing
  have a_eq := (f_data (g_to_num ((fun₀ | 1 => (1 : ℚ)) - fun₀ | 7 => 1))).a_val
  simp [a_eq, g_enum_inverse] at supp_increasing
  specialize supp_increasing x_diff_has_neg
  simp [x_diff_supp] at supp_increasing
  let max_supp := (f_data (g_to_num ((fun₀ | 1 => 1) - fun₀ | 7 => 1))).tree.getData.b.support.max' (tree_b_supp_nonempty _)
  have seven_neq_max: 7 ≠ max_supp := by omega
  by_contra!
  have eval_at := DFunLike.congr (x := max_supp) this rfl
  simp [seven_neq_max] at eval_at
  have eval_max_nonzero: (f ((fun₀ | 1 => 1) - fun₀ | 7 => 1)) max_supp ≠ 0 := by
    rw [← Finsupp.mem_support_iff]
    apply Finset.max'_mem
  rw [eq_comm] at eval_at
  contradiction
  simp [f_data]

lemma sum_1_3_eq_tree: (fun₀ | 1 => (1: ℚ)) + (fun₀ | 3 => 1) = (@TreeNode.root x_vals_zero).left.right.left.getData.a := by
  simp [TreeNode.getData, x_vals_zero, XVals.x_vals, treeNum_neq_zero, treeNum, add_comm]

theorem not_equation_2441: 0 ≠ (f ((f 0) + (f (- f 0)))) + (f ( -(f ((f 0) + f (- f (0))))) ) := by
  simp only [neg_f_zero, f_eval_at (n := 0), ne_eq]
  simp [f_data, TreeNode.getData, x_vals_zero, XVals.x_vals, treeNum_neq_zero, f_zero_eq, treeNum]
  rw [sum_1_3_eq_tree, f_eval_at (n := 0) _ rfl, f_neg_b (n := 0) _ rfl]
  simp only [TreeNode.getData]
  simp [x_vals_zero, XVals.x_vals, treeNum_neq_zero, treeNum]
  by_contra!
  simp [f_data, x_vals_zero] at this
  have app_eq := DFunLike.congr (x := 11) this rfl
  simp at app_eq

lemma x_vals_zero_left_b: (f_data 0).tree.left.getData.b = fun₀ | 3 => 1 := by
  simp [TreeNode.getData, XVals.x_vals, treeNum_neq_zero, treeNum, f_data, x_vals_zero]

theorem not_equation_3050: 0 ≠ (f 0) + (f (- (f 0))) + (f (- (f 0) - f (- f 0))) + (f (- (f 0) - f (- f 0) - f (- (f 0) - f (- f 0)))) := by
  let x_sum: G := (-fun₀ | 1 => 1) - fun₀ | 3 => 1
  have x_sum_nonpos: finsuppHasNeg x_sum := by
    simp [x_sum, finsuppHasNeg]
    use 1
    simp
  have f_supp_increasing := (f_data (g_to_num x_sum)).supp_increasing
  rw [(f_data (g_to_num x_sum)).a_val] at f_supp_increasing
  simp [g_enum_inverse] at f_supp_increasing
  specialize f_supp_increasing x_sum_nonpos
  simp [x_sum] at f_supp_increasing
  simp [neg_f_zero]
  simp [f_eval_at (n := 0)]
  simp [f_data, TreeNode.getData, x_vals_zero, XVals.x_vals, treeNum_neq_zero]
  simp [f_zero_eq]
  simp [treeNum]
  have x_sum_supp: x_sum.support = {1, 3} := by
    unfold x_sum
    rw [← Finsupp.single_neg, sub_eq_add_neg, ← Finsupp.single_neg]
    have disjoint_supp: Disjoint (fun₀ | 1 => (-1 : ℚ)).support (fun₀ | 3 => (-1 : ℚ)).support := by
      simp [Finsupp.support_single_ne_zero]
    rw [Finsupp.support_add_eq disjoint_supp]
    simp
    rw [Finsupp.support_single_ne_zero _ (by simp), Finsupp.support_single_ne_zero _ (by simp)]
    exact rfl


  by_cases same_vals: (f_data (g_to_num (x_sum))).cur = x_vals_zero
  · simp [f]
    match h_tree: (f_data (g_to_num (x_sum))).tree with
    | .root =>
      rw [h_tree] at f_supp_increasing
      simp [XVals.x_vals, TreeNode.getData] at f_supp_increasing
      simp [same_vals, x_vals_zero] at f_supp_increasing
      rw [x_sum_supp] at f_supp_increasing
      simp at f_supp_increasing
      -- Obtain contradiction
      simp [Finsupp.support_single_ne_zero _] at f_supp_increasing

    | .left parent =>
      by_contra!
      unfold x_sum at same_vals
      have i_same := same_vals
      apply_fun (fun v => v.i) at i_same
      simp [TreeNode.getData] at this
      simp [same_vals, x_vals_zero, XVals.x_vals, treeNum_neq_zero] at this
      have not_zero := treeNum_neq_zero parent
      rw [ite_cond_eq_false] at this
      simp [basis_n, n_q_basis] at this
      simp [Finsupp.basisSingleOne] at this
      rw [i_same, x_vals_zero] at this
      simp [XVals.i] at this

      have second_sum_has_neg : finsuppHasNeg ((-fun₀ | 1 => (1 : ℚ)) - (fun₀ | 3 => (1 : ℚ)) - (fun₀ | 1 + (treeNum parent - 1) * 2 => (1 : ℚ))) := by
        simp [finsuppHasNeg]
        use 1
        simp
        by_cases val_eq_one: 1 + (treeNum parent - 1) * 2 = 1
        · simp [val_eq_one]
        · simp [val_eq_one]


      have second_supp_increase := (f_data (g_to_num ((((-fun₀ | 1 => 1) - fun₀ | 3 => 1) - fun₀ | 1 + (treeNum parent - 1) * 2 => 1)))).supp_increasing
      rw [(f_data _).a_val] at second_supp_increase
      simp [g_enum_inverse] at second_supp_increase
      specialize second_supp_increase second_sum_has_neg

      let largest_support := (f_data
              (g_to_num
                (((-fun₀ | 1 => 1) - fun₀ | 3 => 1) -
                  fun₀ | 1 + (treeNum parent - 1) * 2 => 1))).tree.getData.b.support.max

      match h_bot: largest_support with
      | WithBot.some largest_supp_n =>
        have app_eq := DFunLike.congr (x := largest_supp_n) this rfl
        simp at app_eq

        have largest_gt_three: 3 < largest_supp_n ∧ 1 + (treeNum parent - 1) * 2 < largest_supp_n := by
          rw [h_tree] at f_supp_increasing
          simp [TreeNode.getData] at f_supp_increasing
          simp [same_vals, x_vals_zero, XVals.x_vals, treeNum_neq_zero] at f_supp_increasing
          unfold x_sum at x_sum_supp
          simp [x_sum_supp] at f_supp_increasing
          simp [Finsupp.support_single_ne_zero _] at f_supp_increasing
          rw [← Finsupp.single_neg, sub_eq_add_neg, ← Finsupp.single_neg] at second_supp_increase
          rw [Finsupp.support_add_eq _] at second_supp_increase
          rw [sub_eq_add_neg, ← Finsupp.single_neg] at second_supp_increase
          rw [Finsupp.support_add_eq _] at second_supp_increase
          simp [Finsupp.support_single_ne_zero _] at second_supp_increase
          rw [← Finset.insert_eq] at second_supp_increase
          rw [← Finset.insert_eq] at second_supp_increase
          unfold largest_support at h_bot
          rw [sub_eq_add_neg] at h_bot
          rw [← Finsupp.single_neg] at h_bot
          rw [← Finsupp.single_neg] at h_bot
          rw [sub_eq_add_neg] at h_bot
          rw [← Finsupp.single_neg] at h_bot
          nth_rw 1 [← WithBot.coe_lt_coe]
          nth_rw 2 [← WithBot.coe_lt_coe]
          rw [WithBot.some_eq_coe] at h_bot
          rw [← h_bot]
          rw [← Finset.coe_max' (tree_b_supp_nonempty _)]
          norm_cast
          simp only [Finset.max_insert, Finset.max_singleton, true_or, sup_of_le_right, sup_lt_iff] at second_supp_increase
          rw [Nat.cast_withBot] at second_supp_increase
          obtain ⟨_, three_lt, three_plus_lt⟩ := second_supp_increase
          norm_cast at three_lt
          norm_cast at three_plus_lt
          · simp [x_sum_supp, Finsupp.support_single_ne_zero _]
          · simp only [Finsupp.single_neg, x_sum_supp, Finsupp.support_neg,
            Finset.disjoint_insert_left, Finsupp.mem_support_iff, ne_eq, Decidable.not_not,
            Finset.disjoint_singleton_left]
            rw [Finsupp.single_apply]
            simp only [add_right_eq_self, mul_eq_zero, OfNat.ofNat_ne_zero, or_false,
              ite_eq_right_iff, one_ne_zero, imp_false]
            refine ⟨?_, ?_⟩
            · omega
            · rw [Finsupp.single_apply]
              simp only [ite_eq_right_iff, one_ne_zero, imp_false]
              omega
        have largest_ne_one: 1 ≠ largest_supp_n := by omega
        have largest_ne_three: 3 ≠ largest_supp_n := by omega
        have largest_ne_treeNum: 1 + (treeNum parent - 1) * 2 ≠ largest_supp_n := by omega
        simp [Finsupp.single_apply, largest_ne_one, largest_ne_three, largest_ne_treeNum] at app_eq
        have eval_nonzero : (f_data (g_to_num (((-fun₀ | 1 => 1) - fun₀ | 3 => 1) - fun₀ | 1 + (treeNum parent - 1) * 2 => 1))).tree.getData.b largest_supp_n ≠ 0 := by
          rw [← Finsupp.mem_support_iff]
          apply Finset.mem_of_max
          rw [← WithBot.some_eq_coe, ← h_bot]
        simp at eval_nonzero
        rw [eq_comm] at app_eq
        contradiction
      | ⊥ =>
        unfold largest_support at h_bot
        rw [WithBot.none_eq_bot, Finset.max_eq_bot] at h_bot
        have supp_nonempty := tree_b_supp_nonempty (f_data (g_to_num
          (((-fun₀ | 1 => 1) - fun₀ | 3 => 1) - fun₀ | 1 + (treeNum parent - 1) * 2 => 1))).tree
        rw [Finset.nonempty_iff_ne_empty] at supp_nonempty
        contradiction
      simp only [eq_iff_iff, iff_false]
      exact not_zero
    | .right parent =>
      have a_eq := (f_data (g_to_num (x_sum))).a_val
      have nonpos := nonpos_not_tree_right (f_data (g_to_num (x_sum))).tree
      simp [a_eq, g_enum_inverse] at nonpos
      specialize nonpos x_sum_nonpos parent
      rw [eq_comm] at nonpos
      contradiction
  · have cur_i_not_zero := (f_data (g_to_num x_sum)).distinct_i x_vals_zero  (f_data (g_to_num x_sum)).vals_has_zero (f_data (g_to_num x_sum)).cur (f_data (g_to_num x_sum)).cur_in_vals
    rw [← not_imp_not] at cur_i_not_zero
    rw [eq_comm] at same_vals
    specialize cur_i_not_zero same_vals
    simp [x_vals_zero] at cur_i_not_zero
    unfold x_sum at cur_i_not_zero

    have first_app_supp_pos := (f_data (g_to_num x_sum)).supp_max_pos
    simp_rw [(f_data (g_to_num x_sum)).a_val, g_enum_inverse] at first_app_supp_pos
    specialize first_app_supp_pos x_sum_nonpos

    have three_lt_max: 3 < ((f_data (g_to_num x_sum)).tree.getData.b.support.max' (tree_b_supp_nonempty _)) := by
      rw [x_sum_supp] at f_supp_increasing
      simp at f_supp_increasing
      exact f_supp_increasing

    have three_lt_max_withbot: 3 < ((f_data (g_to_num x_sum)).tree.getData.b.support.max) := by
      rw [← WithBot.coe_lt_coe] at three_lt_max
      rw [Finset.coe_max'] at three_lt_max
      simp at three_lt_max
      exact three_lt_max


    have three_neq_max: 3 ≠ ((f_data (g_to_num x_sum)).tree.getData.b.support.max' (tree_b_supp_nonempty _)) := by omega
    have one_neq_max: 1 ≠ ((f_data (g_to_num x_sum)).tree.getData.b.support.max' (tree_b_supp_nonempty _)) := by
      omega

    have three_lt_second_term_max: 3 < (((-fun₀ | 1 => 1) - fun₀ | 3 => 1) - f ((-fun₀ | 1 => 1) - fun₀ | 3 => 1)).support.max := by
      have max_in_supp: (f_data (g_to_num ((-fun₀ | 1 => 1) - fun₀ | 3 => 1))).tree.getData.b.support.max' (tree_b_supp_nonempty _) ∈ (((-fun₀ | 1 => 1) - fun₀ | 3 => 1) - f ((-fun₀ | 1 => 1) - fun₀ | 3 => 1)).support := by
        simp
        unfold x_sum at x_sum_supp
        rw [x_sum_supp] at f_supp_increasing
        simp at f_supp_increasing
        have max_neq_one: 1 ≠ (f_data (g_to_num ((-fun₀ | 1 => 1) - fun₀ | 3 => 1))).tree.getData.b.support.max' (tree_b_supp_nonempty _) := by omega
        have max_neq_3: 3 ≠ (f_data (g_to_num ((-fun₀ | 1 => 1) - fun₀ | 3 => 1))).tree.getData.b.support.max' (tree_b_supp_nonempty _) := by omega
        simp [max_neq_one, max_neq_3]
        exact ne_of_gt first_app_supp_pos

      have max_le_mem := Finset.le_max' _ _ max_in_supp
      have my_trans := LT.lt.trans_le three_lt_max max_le_mem
      rw [← WithBot.coe_lt_coe] at my_trans
      rw [Finset.coe_max'] at my_trans
      simp at my_trans
      exact my_trans

    have second_app_has_neg: finsuppHasNeg (((-fun₀ | 1 => 1) - fun₀ | 3 => 1) - f ((-fun₀ | 1 => 1) - fun₀ | 3 => 1)) := by
      simp [finsuppHasNeg]
      use (f_data (g_to_num x_sum)).tree.getData.b.support.max' (tree_b_supp_nonempty _)
      simp only [ne_eq, one_neq_max, not_false_eq_true, Finsupp.single_eq_of_ne, neg_zero,
        three_neq_max, sub_self]
      exact first_app_supp_pos

    have second_app_supp_increase := (f_data (g_to_num (((-fun₀ | 1 => 1) - fun₀ | 3 => 1) - f ((-fun₀ | 1 => 1) - fun₀ | 3 => 1)))).supp_increasing
    have a_val := (f_data ((g_to_num (((-fun₀ | 1 => 1) - fun₀ | 3 => 1) - f ((-fun₀ | 1 => 1) - fun₀ | 3 => 1))))).a_val
    simp_rw [a_val, g_enum_inverse] at second_app_supp_increase
    specialize second_app_supp_increase second_app_has_neg

    let max_supp := (f_data
                  (g_to_num
                    (((-fun₀ | 1 => 1) - fun₀ | 3 => 1) -
                      f ((-fun₀ | 1 => 1) - fun₀ | 3 => 1)))).tree.getData.b.support.max' (tree_b_supp_nonempty _)

    by_contra!
    have app_eq:= DFunLike.congr (x := max_supp) this rfl
    have max_supp_gt_three: 3 < max_supp := by
      rw [← WithBot.coe_lt_coe, WithBot.coe_ofNat]
      exact lt_trans three_lt_second_term_max second_app_supp_increase
    have max_supp_not_first: max_supp ∉ (f ((-fun₀ | 1 => 1) - fun₀ | 3 => 1)).support := by
      have max_supp_not_in_superset: max_supp ∉ (((-fun₀ | 1 => 1) - fun₀ | 3 => 1) - f ((-fun₀ | 1 => 1) - fun₀ | 3 => 1)).support :=
        Finset.not_mem_of_max_lt_coe second_app_supp_increase
      have first_subset := Finsupp.support_sub (f := (-fun₀ | 1 => 1) - fun₀ | 3 => 1) (g := f ((-fun₀ | 1 => 1) - fun₀ | 3 => 1))
      have correct_subset : (f ((-fun₀ | 1 => 1) - fun₀ | 3 => 1)).support ⊆ (((-fun₀ | 1 => 1) - fun₀ | 3 => 1) - f ((-fun₀ | 1 => 1) - fun₀ | 3 => 1)).support := by
        have eq_add := Finsupp.support_add_eq (g₁ := (-fun₀ | 1 => (1 : ℚ)) - fun₀ | 3 => 1)  (g₂ := -f ((-fun₀ | 1 => 1) - fun₀ | 3 => 1)) ?_
        · nth_rw 1 [← sub_eq_add_neg] at eq_add
          rw [eq_add]
          simp
        · simp only [f, Finsupp.support_neg]
          have three_neq_two_n: ∀ n, 3 ≠ 2^n := by
            intro n
            by_cases n_eq_zero: n = 0
            · simp [n_eq_zero]
            · by_cases n_eq_one: n = 1
              · simp [n_eq_one]
              · have n_gt_two: 2 ≤ n := by
                  omega
                have two_n_ge_4: 2^2 ≤ 2^n := by
                  exact Nat.pow_le_pow_of_le_right (by simp) n_gt_two
                omega

          match h_tree: (f_data (g_to_num (((-fun₀ | 1 => 1) - fun₀ | 3 => 1) : Finsupp _ _))).tree with
          | .root =>
            simp [h_tree, TreeNode.getData, XVals.x_vals]
            rw [Finset.disjoint_iff_ne]
            intro a ha b hb
            rw [x_sum_supp] at ha
            simp [Finsupp.support_single_ne_zero] at hb
            have cur_i_gt:  0 < (f_data (g_to_num ((-fun₀ | 1 => 1) - fun₀ | 3 => 1))).cur.i := by omega
            by_cases cur_i_one: (f_data (g_to_num ((-fun₀ | 1 => 1) - fun₀ | 3 => 1))).cur.i = 1
            · simp [cur_i_one] at hb
              rw [hb]
              have two_not_mem: 2 ∉ ({1, 3}: Finset ℕ) := by simp
              exact ne_of_mem_of_not_mem ha two_not_mem
            · have cur_i_ge_two: 2 ≤ (f_data (g_to_num ((-fun₀ | 1 => 1) - fun₀ | 3 => 1))).cur.i := by omega
              have pow_ge_4: 2^2 ≤ 2^((f_data (g_to_num ((-fun₀ | 1 => 1) - fun₀ | 3 => 1))).cur.i) :=
                Nat.pow_le_pow_of_le_right (by simp) cur_i_ge_two
              have a_le_3: a ≤ 3 := Nat.divisor_le ha
              omega
          | .left parent =>
            simp [h_tree, TreeNode.getData, XVals.x_vals, treeNum_neq_zero]
            rw [Finset.disjoint_iff_ne]
            intro a ha b hb
            rw [x_sum_supp] at ha
            simp [Finsupp.support_single_ne_zero] at hb
            have term_ge_4: 2^2 ≤ 2^((f_data (g_to_num ((-fun₀ | 1 => 1) - fun₀ | 3 => 1))).cur.i + 1) := by
              rw [StrictMono.le_iff_le]
              omega
              exact pow_right_strictMono₀ (a := 2) Nat.one_lt_two
            have treeNum_ge: 1 ≤ (treeNum parent - 1) := Nat.le_sub_one_of_lt (treeNum_gt_one parent)
            simp at term_ge_4
            have full_term_ge: 4 ≤ (treeNum parent - 1) * 2 ^ ((f_data (g_to_num ((-fun₀ | 1 => 1) - fun₀ | 3 => 1))).cur.i + 1) :=
              le_mul_of_one_le_of_le treeNum_ge term_ge_4
            by_cases a_eq_one: a = 1
            · omega
            · simp only [Finset.mem_insert, a_eq_one, Finset.mem_singleton, false_or] at ha
              rw [ha, hb]
              omega
          | .right parent =>
            have a_eq := (f_data (g_to_num ((-fun₀ | 1 => 1) - fun₀ | 3 => 1))).a_val
            simp [g_enum_inverse] at a_eq
            unfold x_sum at x_sum_nonpos
            rw [← a_eq] at x_sum_nonpos
            have not_right := nonpos_not_tree_right _ x_sum_nonpos
            simp at not_right
            specialize not_right parent
            rw [eq_comm] at not_right
            contradiction
      exact fun a ↦ max_supp_not_in_superset (correct_subset a)
    have max_supp_neg_1: 1 ≠ max_supp := by omega
    have max_supp_in: max_supp ∈ (f (((-fun₀ | 1 => 1) - fun₀ | 3 => 1) - f ((-fun₀ | 1 => 1) - fun₀ | 3 => 1))).support :=
      Finset.max'_mem ..
    simp [max_supp_neg_1, Nat.ne_of_lt max_supp_gt_three] at app_eq
    rw [Finsupp.not_mem_support_iff] at max_supp_not_first
    rw [max_supp_not_first, zero_add] at app_eq
    simp only [Finsupp.mem_support_iff, ne_eq] at max_supp_in
    rw [eq_comm] at max_supp_in
    contradiction

theorem not_equation_3456: f 0 ≠ f ((f 0) + f (- (f 0))) := by
  rw [neg_f_zero, f_eval_at (n := 0)]
  simp only [f_zero_eq, TreeNode.getData, f_data, x_vals_zero, XVals.x_vals, one_ne_zero,
    ↓reduceIte, Finsupp.coe_basisSingleOne, pow_zero, tsub_self, zero_add, pow_one, zero_mul,
    add_zero, treeNum, OfNat.ofNat_ne_zero]
  rw [sum_1_3_eq_tree, f_eval_at (n := 0)]
  simp only [TreeNode.getData, XVals.x_vals, treeNum, Nat.reduceMul, Nat.add_one_sub_one,
    OfNat.ofNat_ne_zero, ↓reduceIte, Finsupp.coe_basisSingleOne, x_vals_zero, pow_zero, zero_add,
    pow_one, Nat.reduceAdd, one_ne_zero, tsub_self, zero_mul, add_zero, one_mul, neg_sub,
    sub_neg_eq_add, ne_eq]
  by_contra!
  rw [Finsupp.single_left_inj] at this
  linarith
  simp only [ne_eq, one_ne_zero, not_false_eq_true]
  rw [f_data]
  rfl

theorem not_equation_4065: f 0 ≠ (f 0) + (f (- f 0)) + f (- f (- (f 0)) + - (f 0) ) := by
  rw [← sub_eq_add_neg, neg_f_zero, f_eval_at (n := 0)]
  nth_rw 1 [f_zero_eq]
  simp [x_vals_zero_left_b]
  rw [f_zero_eq]
  by_contra!
  apply_fun (λ y => -(fun₀ | 1 => 1) + y) at this
  simp only [neg_add_cancel] at this
  rw [← add_assoc, ← add_assoc] at this
  simp at this
  let x_sum: G := (-fun₀ | 3 => 1) - fun₀ | 1 => 1
  have x_sum_nonpos: finsuppHasNeg x_sum := by
    simp only [finsuppHasNeg, Finsupp.coe_sub, Finsupp.coe_neg, Set.mem_range, Pi.sub_apply,
      Pi.neg_apply, exists_exists_eq_and, sub_neg, x_sum]
    use 1
    simp
  have f_supp_increasing := (f_data (g_to_num x_sum)).supp_increasing
  rw [(f_data (g_to_num x_sum)).a_val] at f_supp_increasing
  simp only [g_enum_inverse] at f_supp_increasing
  specialize f_supp_increasing x_sum_nonpos
  simp only [x_sum] at f_supp_increasing
  have x_sum_supp: x_sum.support = {3, 1} := by
    unfold x_sum
    rw [← Finsupp.single_neg, sub_eq_add_neg, ← Finsupp.single_neg]
    have disjoint_supp: Disjoint (fun₀ | 3 => (-1 : ℚ)).support (fun₀ | 1 => (-1 : ℚ)).support := by
      simp [Finsupp.support_single_ne_zero]
    rw [Finsupp.support_add_eq disjoint_supp]
    simp only [Finsupp.single_neg, Finsupp.support_neg]
    rw [Finsupp.support_single_ne_zero _ (by simp), Finsupp.support_single_ne_zero _ (by simp)]
    exact rfl
  dsimp [x_sum] at x_sum_supp
  simp only [x_sum_supp, Finset.max_insert, WithBot.coe_ofNat, Finset.max_singleton,
    WithBot.coe_one, Nat.one_le_ofNat, sup_of_le_left, Nat.ofNat_lt_cast] at f_supp_increasing
  have three_lt_max: 3 < ((f_data (g_to_num x_sum)).tree.getData.b.support.max' (tree_b_supp_nonempty _)) :=
    f_supp_increasing
  have first_app_supp_pos := (f_data (g_to_num x_sum)).supp_max_pos
  simp_rw [(f_data (g_to_num x_sum)).a_val, g_enum_inverse] at first_app_supp_pos
  specialize first_app_supp_pos x_sum_nonpos
  have three_neq_max: 3 ≠ ((f_data (g_to_num x_sum)).tree.getData.b.support.max' (tree_b_supp_nonempty _)) := by omega
  have one_neq_max: 1 ≠ ((f_data (g_to_num x_sum)).tree.getData.b.support.max' (tree_b_supp_nonempty _)) := by
    omega
  have second_app_has_neg: finsuppHasNeg (((-fun₀ | 1 => 1)) - f ((-fun₀ | 3 => 1) - fun₀ | 1 => 1)) := by
    simp only [finsuppHasNeg, Finsupp.coe_sub, Finsupp.coe_neg, Set.mem_range, Pi.sub_apply,
      Pi.neg_apply, exists_exists_eq_and, sub_neg]
    use (f_data (g_to_num x_sum)).tree.getData.b.support.max' (tree_b_supp_nonempty _)
    simp only [ne_eq, one_neq_max, not_false_eq_true, Finsupp.single_eq_of_ne, neg_zero, f, x_sum]
    exact first_app_supp_pos
  have second_app_supp_increase := (f_data (g_to_num (((-fun₀ | 1 => 1)) - f ((-fun₀ | 3 => 1) - fun₀ | 1 => 1)))).supp_increasing
  have a_val := (f_data ((g_to_num (((-fun₀ | 1 => 1)) - f ((-fun₀ | 3 => 1) - fun₀ | 1 => 1))))).a_val
  simp only [a_val, g_enum_inverse] at second_app_supp_increase
  specialize second_app_supp_increase second_app_has_neg
  have app_eq := DFunLike.congr (x :=  ((f_data (g_to_num x_sum)).tree.getData.b.support.max' (tree_b_supp_nonempty _))) this rfl
  rw [Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_add, Pi.add_apply] at app_eq
  have three_neq_supp: 3 ≠  ((f_data (g_to_num x_sum)).tree.getData.b.support.max' (tree_b_supp_nonempty _)) := by omega
  simp only [ne_eq, three_neq_supp, not_false_eq_true, Finsupp.single_eq_of_ne, f, zero_add] at app_eq
  have max_in: ((f_data (g_to_num x_sum)).tree.getData.b.support.max' (tree_b_supp_nonempty _)) ∈ ((f_data (g_to_num x_sum)).tree.getData.b.support) :=
    Finset.max'_mem ..
  rw [Finsupp.mem_support_iff] at max_in
  rw [eq_comm] at app_eq
  · exact max_in app_eq
  · rfl

-- Wire up the above non-implication proofs to `equational_result`

noncomputable def magG: Magma G := ⟨fun x y ↦ x + (f (y - x))⟩

theorem f_equation_1692: @Equation1692 G magG := by
  simp only [Equation1692, magG, sub_add_cancel_left, add_sub_cancel_left]
  have law := diamond_law
  simp only [diamond, add_sub_cancel, neg_sub, add_sub_cancel_left, sub_add_cancel_left] at law
  exact law

@[equational_result]
theorem Equation1692_not_implies_Equation23 :
  ∃ (T : Type) (_ : Magma T), Equation1692 T ∧ ¬ Equation23 T := by
  refine ⟨G, magG, f_equation_1692, ?_⟩
  simp only [Equation23, magG, sub_self, sub_add_cancel_left, not_forall]
  use 0
  rw [zero_add]
  exact not_equation_23

@[equational_result]
theorem Equation1692_not_implies_Equation47 :
  ∃ (T : Type) (_ : Magma T), Equation1692 T ∧ ¬ Equation47 T := by
  refine ⟨G, magG, f_equation_1692, ?_⟩
  simp only [Equation47, magG, sub_self, add_sub_cancel_left, self_eq_add_right, forall_const]
  exact not_equation_47

@[equational_result]
theorem Equation1692_not_implies_Equation1832 :
  ∃ (T : Type) (_ : Magma T), Equation1692 T ∧ ¬ Equation1832 T := by
  refine ⟨G, magG, f_equation_1692, ?_⟩
  simp only [magG, not_forall, sub_self, add_sub_cancel_left, add_sub_add_left_eq_sub]
  use 0
  rw [zero_add]
  exact not_equation_1832

@[equational_result]
theorem Equation1692_not_implies_Equation2441 :
  ∃ (T : Type) (_ : Magma T), Equation1692 T ∧ ¬ Equation2441 T := by
  refine ⟨G, magG, f_equation_1692, ?_⟩
  simp only [magG, not_forall, sub_self, sub_add_cancel_left]
  use 0
  simp only [zero_add, sub_zero]
  exact not_equation_2441

@[equational_result]
theorem Equation1692_not_implies_Equation3050 :
  ∃ (T : Type) (_ : Magma T), Equation1692 T ∧ ¬ Equation3050 T := by
  refine ⟨G, magG, f_equation_1692, ?_⟩
  rw [magG, not_forall]
  use 0
  simp only [sub_self, zero_add, zero_sub, neg_add_rev]
  conv =>
    pattern f (-f (-f 0) + -f 0)
    rw [add_comm, ← sub_eq_add_neg]
  conv =>
    pattern f (-f (-f (-f 0) + -f 0) + (-f (-f 0) + -f 0))
    rw [add_comm]
    arg 1
    arg 1
    rw [add_comm]
  conv => rw [← sub_eq_add_neg, ← sub_eq_add_neg]
  conv =>
    pattern f (-f (-f 0) + -f 0)
    rw [add_comm, ← sub_eq_add_neg]
  exact not_equation_3050

@[equational_result]
theorem Equation1692_not_implies_Equation3456 :
  ∃ (T : Type) (_ : Magma T), Equation1692 T ∧ ¬ Equation3456 T := by
  refine ⟨G, magG, f_equation_1692, ?_⟩
  simp only [magG, not_forall, sub_self, sub_add_cancel_left, add_right_inj]
  use 0
  rw [zero_add, sub_zero]
  exact not_equation_3456

@[equational_result]
theorem Equation1692_not_implies_Equation4065 :
  ∃ (T : Type) (_ : Magma T), Equation1692 T ∧ ¬ Equation4065 T := by
  refine ⟨G, magG, f_equation_1692, ?_⟩
  simp only [magG, not_forall, sub_self, sub_add_cancel_left]
  use 0
  rw [zero_add, zero_sub, neg_add_rev]
  exact not_equation_4065

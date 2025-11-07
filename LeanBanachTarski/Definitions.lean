import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.RCLike.Basic
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
noncomputable section
def matrix_a   : Matrix (Fin 3) (Fin 3) Real := !![1, 0, 0; 0, 1/3, -2/3*Real.sqrt 2; 0, 2/3*Real.sqrt 2, 1/3]
def matrix_b   : Matrix (Fin 3) (Fin 3) Real := !![1/3, -2/3*Real.sqrt 2, 0; (2/3*Real.sqrt 2), 1/3, 0; 0, 0, 1]
end noncomputable section


theorem matrix_a_det_eq_one : Matrix.det matrix_a = 1 := by
  rw [matrix_a, Matrix.det_fin_three]
  norm_num
  simp only [one_div, Fin.isValue, Matrix.cons_val, Matrix.cons_val_one, neg_mul, sub_neg_eq_add,
    zero_mul, mul_zero, sub_zero]
  ring_nf
  norm_num

theorem matrix_b_det_eq_one : Matrix.det matrix_b = 1 := by
  rw [matrix_b, Matrix.det_fin_three]
  norm_num
  simp only [one_div, Fin.isValue, Matrix.cons_val, Matrix.cons_val_one, mul_one, mul_zero,
    sub_zero, neg_zero, add_zero, zero_mul]
  ring_nf
  norm_num

open MatrixGroups

noncomputable section
def sl_a : SL(3, ℝ) := ⟨matrix_a, matrix_a_det_eq_one⟩
def sl_b : SL(3, ℝ) := ⟨matrix_b, matrix_b_det_eq_one⟩
end noncomputable section

lemma sl_a_neq_one : sl_a ≠ 1 := by
  simp [sl_a, matrix_a]
  rw [Subtype.ext_iff]
  simp [← Matrix.ext_iff]
  use 1
  use 1
  simp

lemma sl_b_neq_one : sl_b ≠ 1 := by
  simp [sl_b, matrix_b]
  rw [Subtype.ext_iff]
  simp [← Matrix.ext_iff]
  use 1
  use 1
  simp

-- TOOD mathlib?? closure von ... ist free Group.

open scoped Classical

abbrev Free_Rots : Subgroup SL(3, ℝ) := Subgroup.closure {sl_a, sl_b}

open Matrix FreeGroup

def fin_2_to_rots (w : Fin 2) : Free_Rots :=
  match w with
  | 1 => ⟨sl_a, by apply Subgroup.mem_closure_of_mem; simp⟩
  | 2 => ⟨sl_b, by apply Subgroup.mem_closure_of_mem; simp⟩

def F_2_to_Rots := FreeGroup.lift fin_2_to_rots

-- lemma 3.1
lemma Free_Rots_mul_vec (w : FreeGroup (Fin 2)):
    ∃a b c : ℤ , ((lift fin_2_to_rots) w) *ᵥ (![0,1,0]) = (1/3^ w.toWord.length : ℝ) • ![a * Real.sqrt 2, b,c *  Real.sqrt 2] := by
  rw [← @mk_toWord _ _ w]
  induction h : w.toWord.length generalizing w with
  | zero =>
    have h : w.toWord = [] := by exact List.eq_nil_iff_length_eq_zero.mpr h
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, h, lift_mk, List.map_nil, List.prod_nil,
      OneMemClass.coe_one, SpecialLinearGroup.coe_one, one_mulVec, toWord_mk, reduce_nil,
      List.length_nil, pow_zero, ne_eq, one_ne_zero, not_false_eq_true, div_self, one_smul,
      vecCons_inj, zero_eq_mul, Int.cast_eq_zero, Nat.ofNat_nonneg, Real.sqrt_eq_zero,
      OfNat.ofNat_ne_zero, or_false, and_true, exists_and_left, ↓existsAndEq, exists_eq_left]
    use 1
    simp only [Int.cast_one]
  | succ i hi =>
    match hw: w.toWord with
    | [] =>
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, lift_mk, List.map_nil, List.prod_nil,
        OneMemClass.coe_one, SpecialLinearGroup.coe_one, one_mulVec, toWord_mk, reduce_nil,
        List.length_nil, pow_zero, ne_eq, one_ne_zero, not_false_eq_true, div_self, one_smul,
        vecCons_inj, zero_eq_mul, Int.cast_eq_zero, Nat.ofNat_nonneg, Real.sqrt_eq_zero,
        OfNat.ofNat_ne_zero, or_false, and_true, exists_and_left, ↓existsAndEq, exists_eq_left]
      grind
    | head :: tail =>
      rw [show ((mk (head :: tail)).toWord.length) = i + 1 by rw [← hw, mk_toWord, h]]
      rw [lift_mk, List.map_cons, List.prod_cons]
      have he : ∃ w' : FreeGroup (Fin 2), w'.toWord = tail ∧ w'.toWord.length = i:= by
        use mk tail
        have h : FreeGroup.IsReduced tail := by
          apply IsReduced.infix w.isReduced_toWord
          rw [hw]
          apply List.infix_cons
          rfl
        simp [IsReduced.reduce_eq h]
        grind

      rcases he with ⟨w', he1, he2⟩
      specialize hi w' he2
      rcases hi with ⟨a, b, c, hi⟩
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, lift_mk, Subgroup.val_list_prod, List.map_map,
        toWord_mk, reduce_toWord, one_div, smul_cons, smul_eq_mul, smul_empty] at hi
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Subgroup.coe_mul, Subgroup.val_list_prod,
        List.map_map, SpecialLinearGroup.coe_mul, one_div, smul_cons, smul_eq_mul, smul_empty]
      rw [← mulVec_mulVec]
      rw [he1] at hi
      rw [hi]
      fin_cases head
      . simp only [fin_2_to_rots, cond_true]
        use a - 2 * b
        use 4 * a + b
        use 3 * c
        ext j
        simp only [sl_b, matrix_b, one_div, mulVec_cons, Nat.succ_eq_add_one, Nat.reduceAdd,
          mulVec_empty, add_zero, Pi.add_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul,
          Int.cast_sub, Int.cast_mul, Int.cast_ofNat, ← he1, he2]
        fin_cases j <;> simp <;> grind
      . simp only [fin_2_to_rots, cond_false, InvMemClass.coe_inv, SpecialLinearGroup.coe_inv]
        use a + 2 * b
        use -4 * a + b
        use 3 * c
        ext j
        simp only [sl_b, matrix_b, one_div, adjugate_fin_three, Fin.isValue, of_apply, cons_val',
          cons_val_one, cons_val_zero, cons_val_fin_one, cons_val, mul_one, mul_zero, sub_zero,
          add_zero, zero_mul, sub_self, neg_zero, ← he1, he2, mulVec_cons, Nat.succ_eq_add_one,
          Nat.reduceAdd, mulVec_empty, Pi.add_apply, Pi.smul_apply, Function.comp_apply,
          smul_eq_mul, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.reduceNeg, neg_mul,
          Int.cast_neg]
        fin_cases j <;> simp <;> grind
      . simp only [fin_2_to_rots, cond_true]
        use 3 * a
        use b - 4 * c
        use 2 * b + c
        ext j
        simp only [sl_a, matrix_a, one_div, ← he1, he2, mulVec_cons, Nat.succ_eq_add_one,
          Nat.reduceAdd, mulVec_empty, add_zero, Pi.add_apply, Pi.smul_apply, Function.comp_apply,
          smul_eq_mul, Int.cast_mul, Int.cast_ofNat, Int.cast_sub, Int.cast_add]
        fin_cases j <;> simp <;> grind
      . simp only [fin_2_to_rots, cond_false, InvMemClass.coe_inv, SpecialLinearGroup.coe_inv]
        use 3 * a
        use b + 4 * c
        use - 2 * b + c
        ext j
        simp only [sl_a, matrix_a, one_div, adjugate_fin_three, Fin.isValue, of_apply, cons_val',
          cons_val_one, cons_val_zero, cons_val_fin_one, cons_val, zero_mul, neg_zero, add_zero,
          sub_self, mul_zero, one_mul, sub_zero, ← he1, he2, mulVec_cons, Nat.succ_eq_add_one,
          Nat.reduceAdd, mulVec_empty, Pi.add_apply, Pi.smul_apply, Function.comp_apply,
          smul_eq_mul, Int.cast_mul, Int.cast_ofNat, Int.reduceNeg, neg_mul, Int.cast_add,
          Int.cast_neg]
        fin_cases j <;> simp <;> grind

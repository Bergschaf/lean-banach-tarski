import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.GroupTheory.FreeGroup.IsFreeGroup
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Algebra.Group.Subgroup.Lattice

noncomputable section
def matrix_a   : Matrix (Fin 3) (Fin 3) Real := !![1, 0, 0; 0, 1/3, -2/3*Real.sqrt 2; 0, 2/3*Real.sqrt 2, 1/3]
def matrix_a'  : Matrix (Fin 3) (Fin 3) Real := !![1, 0, 0; 0, 1/3, 2/3*Real.sqrt 2; 0, -2/3*Real.sqrt 2, 1/3]
def matrix_b   : Matrix (Fin 3) (Fin 3) Real := !![1/3, -2/3*Real.sqrt 2, 0; (2/3*Real.sqrt 2), 1/3, 0; 0, 0, 1]
def matrix_b'  : Matrix (Fin 3) (Fin 3) Real := !![1/3, 2/3*Real.sqrt 2, 0; (-2/3*Real.sqrt 2), 1/3, 0; 0, 0, 1]
def matrix_one : Matrix (Fin 3) (Fin 3) Real := 1
end noncomputable section


theorem matrix_a_det_eq_one : Matrix.det matrix_a = 1 := by
  rw [matrix_a, Matrix.det_fin_three]
  norm_num
  simp only [one_div, Fin.isValue, Matrix.cons_val, Matrix.cons_val_one, neg_mul, sub_neg_eq_add,
    zero_mul, mul_zero, sub_zero]
  ring_nf
  norm_num

theorem matrix_a'_det_eq_one : Matrix.det matrix_a' = 1 := by
  rw [matrix_a', Matrix.det_fin_three]
  norm_num
  simp only [one_div, Fin.isValue, Matrix.cons_val, Matrix.cons_val_one, mul_neg, sub_neg_eq_add,
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

theorem matrix_b'_det_eq_one : Matrix.det matrix_b' = 1 := by
  rw [matrix_b', Matrix.det_fin_three]
  norm_num
  simp only [one_div, Fin.isValue, Matrix.cons_val, Matrix.cons_val_one, mul_one, mul_zero,
    sub_zero, add_zero, zero_mul, neg_zero]
  ring_nf
  norm_num

theorem matrix_one_det_eq_one : Matrix.det matrix_one = 1 := by
  rw [matrix_one, Matrix.det_fin_three]
  simp

open MatrixGroups


noncomputable section
def sl_a : SL(3, ℝ) := ⟨matrix_a, matrix_a_det_eq_one⟩
def sl_a' : SL(3, ℝ) := sl_a⁻¹  -- ⟨matrix_a', matrix_a'_det_eq_one⟩
def sl_b : SL(3, ℝ) := ⟨matrix_b, matrix_b_det_eq_one⟩
def sl_b' : SL(3, ℝ) := sl_b⁻¹ -- ⟨matrix_b', matrix_b'_det_eq_one⟩
end noncomputable section

@[simp]
lemma sl_b_inv_neq : ¬ sl_b = sl_b⁻¹ := by
  sorry

@[simp]
lemma sl_a_inv_neq : ¬ sl_a = sl_a⁻¹ := by
  sorry

@[simp]
lemma sl_a_neq_sl_b : ¬ sl_a = sl_b := by
  sorry


-- TOOD mathlib?? closure von ... ist free Group.

-- benutze closure_induction
open scoped Classical
--@[simp, grind = ]
--def fin_generators : Finset SL(3, ℝ) := {sl_a, sl_b, sl_a⁻¹, sl_b⁻¹}

def Free_Rots : Subgroup SL(3, ℝ) := Subgroup.closure {sl_a, sl_b}

def fin_2_to_rots (w : Fin 2) : Free_Rots :=
  match w with
  | 1 => ⟨sl_a, by apply Subgroup.mem_closure_of_mem; simp⟩
  | 2 => ⟨sl_b, by apply Subgroup.mem_closure_of_mem; simp⟩

def test := FreeGroup.lift fin_2_to_rots


#check test


--- v schlecht ^ gut

@[simp]
def fin_2_to_Rots (w : Fin 2 × Bool) : SL(3, ℝ) :=
  match w with
  | (1, true) => sl_a
  | (1, false) => sl_a⁻¹
  | (2, true) => sl_b
  | (2, false) => sl_b⁻¹


def Rots_to_fin_2 (g : SL(3, ℝ)) : Fin 2 × Bool :=
  if g = sl_a then (1, true)
  else if g = sl_a⁻¹ then (1, false)
  else if g = sl_b then (2, true)
  else (2, false)  -- g = sl_b⁻¹

theorem reduce_append_prod (l1 l2 : List (Fin 2 × Bool)) :
    ((FreeGroup.reduce (l1 ++ l2)).map fin_2_to_Rots).prod = ((FreeGroup.reduce l1).map fin_2_to_Rots).prod * ((FreeGroup.reduce l2).map fin_2_to_Rots).prod := by
  rw [← List.prod_append, ← List.map_append]
  induction l2 with
  | nil => simp
  | cons head tail ih =>
     5



theorem reduce_prod (l : List (Fin 2 × Bool)) :
    ((FreeGroup.reduce l).map fin_2_to_Rots).prod = (l.map fin_2_to_Rots).prod := by
  induction l using List.twoStepInduction with
  | nil => simp
  | singleton x => simp
  | cons_cons x y tail h1 h2 =>











#exit

lemma f_2_representable : ∀ g ∈ F_2,
    ∃ l : List fin_generators, (l : List SL(3, ℝ)).prod = g ∧ FreeGroup.IsReduced (l.map F_2_to_fin_2) := by
  apply Subgroup.closure_induction
  . simp only [Set.mem_insert_iff, Set.mem_singleton_iff, List.pure_def, List.bind_eq_flatMap,
    forall_eq_or_imp, forall_eq]
    apply And.intro
    . use [⟨sl_a, by simp⟩]
      simp
    . use [⟨sl_b, by simp⟩]
      simp
  . use []
    simp
  . simp only [fin_generators, List.pure_def, List.bind_eq_flatMap, forall_exists_index, and_imp]
    intro x y hx hy l1 hl1 hrl1 l2 hl2 hrl2
    use (FreeGroup.reduce ((l1 ++ l2).map F_2_to_fin_2)).map fin_2_to_F_2
    apply And.intro
    .
      rw [← hl1, ← hl2, ← List.prod_append, ←  List.flatMap_append]
      rw [← reduce_prod]




    . sorry
  . simp only [fin_generators, List.pure_def, List.bind_eq_flatMap, List.map_id_fun', id_eq,
    forall_exists_index]
    intro g hg l h1
    rw [← h1]
    rw [@List.prod_inv_reverse]
    have h (x : fin_generators) :  (x.val)⁻¹ ∈ fin_generators:= by
      have prop := x.prop
      simp only [fin_generators, Finset.mem_insert, inv_eq_iff_eq_inv, inv_inv,
        Finset.mem_singleton]
      simp only [fin_generators] at prop
      grind
    let simple_inv (x : fin_generators) : fin_generators := ⟨x.val⁻¹,h x⟩
    use (l.map (fun a ↦ simple_inv a)).reverse
    simp [simple_inv, List.flatMap_reverse, List.flatMap_map, List.map_flatMap]


open FreeGroup
def equiv : ↥F_2 ≃* FreeGroup (Fin 2) where
  toFun g :=  mk <|(f_2_representable g.val g.prop).choose.map F_2_to_fin_2
  invFun x := ⟨(((x.toWord.map fin_2_to_F_2)).map (fun x ↦ x.val)).prod, by
      simp [F_2]
      apply Subgroup.list_prod_mem
      simp [fin_2_to_F_2]
      intro g h1
      cases h1 with
      | inl h =>
        cases h with
        | inr h => exact Subgroup.mem_closure_of_mem (by grind)
        | inl h =>
          rw [← h.right]
          apply Subgroup.inv_mem
          exact Subgroup.mem_closure_of_mem (by grind)
      | inr h => sorry -- gschenkt

  ⟩
  left_inv := by
    simp only [Function.LeftInverse, fin_generators, List.pure_def, List.bind_eq_flatMap,
      List.map_id_fun', id_eq, toWord_mk, List.map_map, Subtype.forall, Subtype.mk.injEq]
    intro a b
    simp [Function.comp_def]


  right_inv := by sorry
  map_mul' x y := by
    simp only [fin_generators, List.pure_def, List.bind_eq_flatMap, List.map_id_fun', id_eq,
      Subgroup.coe_mul, mul_mk]
    sorry



def basis : FreeGroupBasis (Fin 2) ↥F_2 where
  repr := equiv

instance : IsFreeGroup F_2 where
  nonempty_basis := by
    use (Fin 2)
    refine Nonempty.intro basis


abbrev ℝ_3 := Fin 3 -> ℝ

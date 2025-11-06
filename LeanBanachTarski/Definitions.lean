import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.GroupTheory.FreeGroup.IsFreeGroup
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Algebra.Group.Subgroup.Lattice

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

-- TOOD mathlib?? closure von ... ist free Group.

-- benutze closure_induction
open scoped Classical
--@[simp, grind = ]

abbrev Free_Rots : Subgroup SL(3, ℝ) := Subgroup.closure {sl_a, sl_b}

def fin_2_to_rots (w : Fin 2) : Free_Rots :=
  match w with
  | 1 => ⟨sl_a, by apply Subgroup.mem_closure_of_mem; simp⟩
  | 2 => ⟨sl_b, by apply Subgroup.mem_closure_of_mem; simp⟩

def F_2_to_Rots := FreeGroup.lift fin_2_to_rots
open FreeGroup

theorem inj : Function.Injective F_2_to_Rots := by
  simp [Function.Injective, F_2_to_Rots]
  intro a1 a2 h
  -- richtig, wichtiges resultat, wo beweis?
  --refine FreeGroup.toWord_inj.mp ?_
  rw [← @mk_toWord _ _ a1, ← @mk_toWord _ _ a2] at h
  simp at h
  sorry


#check F_2_to_Rots


theorem exists_inv_fun : ∀ g ∈ Free_Rots, ∃ w : FreeGroup (Fin 2), F_2_to_Rots w = g := by
  apply Subgroup.closure_induction
  . simp [F_2_to_Rots]
    apply And.intro
    .
      use mk [(1, true)]
      simp [fin_2_to_rots]
    . use mk [(2, true)]
      simp [fin_2_to_rots]
  . use 1
    simp [F_2_to_Rots]
  . rintro g1 g2 hg1 hg2 ⟨w1,h1⟩ ⟨w2,h2⟩
    subst h1
    subst h2
    use w1 * w2
    simp
  . rintro g1 gh1 ⟨w, h1⟩
    subst h1
    use w⁻¹
    simp

#check F_2_to_Rots

open FreeGroup
def equiv :   FreeGroup (Fin 2) ≃* ↥Free_Rots where
  toFun := F_2_to_Rots
  invFun g := (exists_inv_fun g.val g.prop).choose
  map_mul' := by simp
  left_inv := by
    simp [Function.LeftInverse]
    intro w
    have spec := (exists_inv_fun (F_2_to_Rots w).val (F_2_to_Rots w).prop).choose_spec
    apply inj
    grind
  right_inv := by
    simp [Function.RightInverse]
    simp [Function.LeftInverse]
    intro g h
    have spec := (exists_inv_fun g h).choose_spec
    grind


def basis : FreeGroupBasis (Fin 2) ↥Free_Rots where
  repr := equiv.symm

instance : IsFreeGroup ↥Free_Rots where
  nonempty_basis := by
    use (Fin 2)
    refine Nonempty.intro basis


abbrev ℝ_3 := Fin 3 -> ℝ

import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.GroupTheory.FreeGroup.IsFreeGroup
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Data.Matrix.Mul
import Mathlib
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

-- benutze closure_induction
open scoped Classical
--@[simp, grind = ]

abbrev Free_Rots : Subgroup SL(3, ℝ) := Subgroup.closure {sl_a, sl_b}
open Matrix



def fin_2_to_rots (w : Fin 2) : Free_Rots :=
  match w with
  | 1 => ⟨sl_a, by apply Subgroup.mem_closure_of_mem; simp⟩
  | 2 => ⟨sl_b, by apply Subgroup.mem_closure_of_mem; simp⟩

def F_2_to_Rots := FreeGroup.lift fin_2_to_rots
#check F_2_to_Rots
open FreeGroup

theorem linear (w1 w2 : FreeGroup (Fin 2)) : F_2_to_Rots (w1 * w2) = F_2_to_Rots w1 * F_2_to_Rots w2 := by
  simp [F_2_to_Rots]

theorem matrix_independent (i : FreeGroup (Fin 2)) :
  (List.map (fun x => bif x.2 then fin_2_to_rots x.1 else (fin_2_to_rots x.1)⁻¹) i.toWord).prod = 1 ↔ ∀ x ∈ (List.map (fun x => bif x.2 then fin_2_to_rots x.1 else (fin_2_to_rots x.1)⁻¹) i.toWord), x = 1 := by
  apply Iff.intro
  intro h w h1

  induction hl: (List.map (fun x => bif x.2 then fin_2_to_rots x.1 else (fin_2_to_rots x.1)⁻¹) i.toWord) with
  | nil => grind
  | cons head tail ih =>
    simp_all
    rw [← List.prod_cons, ← hl] at h
    contrapose h
    cases h1 with
    | inl hC =>
      simp_all
      subst hC
      rw [← List.prod_cons]
      rw [← hl]
      contrapose h
      simp_all

    | inr h => admit
-- lemma 3.1
lemma Free_Rots_mul_vec (w : FreeGroup (Fin 2)):
    ∃a b c : ℤ , ((lift fin_2_to_rots) w) *ᵥ (![0,1,0]) = (1/3^ w.toWord.length : ℝ) • ![a * Real.sqrt 2, b,c *  Real.sqrt 2] := by
  rw [← @mk_toWord _ _ w]

  induction h : w.toWord.length generalizing w with
  | zero =>

    have h : w.toWord = [] := by exact List.eq_nil_iff_length_eq_zero.mpr h
    simp [h]
    use 1
    simp
  | succ i hi =>
    match hw: w.toWord with
    | [] =>
      simp[hw]
      use 1
      simp

    | head :: tail =>








#exit
  have h : IsReduced w.toWord := by exact isReduced_toWord
  induction' w.toWord with head tail ih
  . simp
    use 1
    simp
  .

    have h2 :(mk (head :: tail)).toWord.length = (mk (tail)).toWord.length + 1 := by
      sorry -- todo
    rw [h2]
    rcases ih with ⟨a, b, c, ih⟩
    simp at ih
    simp [← @mulVec_mulVec]
    rw [ih]
    fin_cases head <;> simp [fin_2_to_rots]
    . use a - 2 * b
      use 4 * a + b
      use 3 * c
      ext i
      fin_cases i <;> simp [sl_b, matrix_b] <;> ring_nf <;> grind
    . sorry
    . sorry
    . sorry


theorem inj : Function.Injective F_2_to_Rots := by
  rw [← MonoidHom.ker_eq_bot_iff]
  ext i
  simp [MonoidHom.ker, F_2_to_Rots]
  apply Iff.intro
  . intro h
    -- test
    apply_fun (fun (x : SL(3, ℝ)) ↦ (x : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ (![0,1,0])) at h
    obtain ⟨a, b, c, n, h1⟩ := Free_Rots_mul_vec i
    rw [h1] at h


    contrapose h

  #exit
    rw [← @mk_toWord _ _ i] at h
    simp only [lift_mk] at h
    rw [matrix_independent] at h
    contrapose h
    rw [← toWord_eq_nil_iff] at h
    rw [List.eq_nil_iff_forall_not_mem] at h
    have h1 :
        (1, true) ∈ i.toWord ∨ (1, false) ∈ i.toWord ∨ (2, true) ∈ i.toWord ∨ (2,false) ∈ i.toWord := by
      simp at h
      grind
    simp only [List.mem_map, Prod.exists, Bool.exists_bool, cond_false, cond_true,
      Fin.exists_fin_two, Fin.isValue, Subtype.forall, Subgroup.mk_eq_one, not_forall,
      Classical.not_imp, exists_and_right]
    have h3 : (2 : Fin 2) = 0 := by rfl
    rcases h1 with h1 | h1 | h1 | h1
    . use sl_a
      simp [Free_Rots, h1, fin_2_to_rots, Subgroup.mem_closure_of_mem]
      exact sl_a_neq_one
    . use sl_a⁻¹
      simp [Subtype.ext_iff, Free_Rots, h1, fin_2_to_rots, Subgroup.mem_closure_of_mem]
      exact sl_a_neq_one
    . use sl_b
      rw [h3] at h1
      simp [Subtype.ext_iff, Free_Rots, h1, fin_2_to_rots, Subgroup.mem_closure_of_mem]
      exact sl_b_neq_one
    . use sl_b⁻¹
      rw [h3] at h1
      simp [Subtype.ext_iff, Free_Rots, h1, fin_2_to_rots, Subgroup.mem_closure_of_mem]
      exact sl_b_neq_one
  . intro h
    simp [h]


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

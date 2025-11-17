import LeanBanachTarski.Definitions
import Mathlib.Tactic.Rify
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib
open Matrix FreeGroup MatrixGroups


theorem SL3_inv_expl_det (A : SL(3, ℝ)) :
    det !![A.1 1 1 * A.1 2 2 - A.1 1 2 * A.1 2 1, -(A.1 0 1 * A.1 2 2) + A.1 0 2 * A.1 2 1, A.1 0 1 * A.1 1 2 - A.1 0 2 * A.1 1 1;
    -(A.1 1 0 * A.1 2 2) + A.1 1 2 * A.1 2 0, A.1 0 0 * A.1 2 2 - A.1 0 2 * A.1 2 0, -(A.1 0 0 * A.1 1 2) + A.1 0 2 * A.1 1 0;
    A.1 1 0 * A.1 2 1 - A.1 1 1 * A.1 2 0, -(A.1 0 0 * A.1 2 1) + A.1 0 1 * A.1 2 0, A.1 0 0 * A.1 1 1 - A.1 0 1 * A.1 1 0] = 1 := by
  simp [Matrix.det_fin_three]
  have test := A.prop
  rw [Matrix.det_fin_three] at test
  grind only

theorem SL3_inv_expl (A : SL(3, ℝ)) :
    A⁻¹ = ⟨!![A.1 1 1 * A.1 2 2 - A.1 1 2 * A.1 2 1, -(A.1 0 1 * A.1 2 2) + A.1 0 2 * A.1 2 1, A.1 0 1 * A.1 1 2 - A.1 0 2 * A.1 1 1;
    -(A.1 1 0 * A.1 2 2) + A.1 1 2 * A.1 2 0, A.1 0 0 * A.1 2 2 - A.1 0 2 * A.1 2 0, -(A.1 0 0 * A.1 1 2) + A.1 0 2 * A.1 1 0;
    A.1 1 0 * A.1 2 1 - A.1 1 1 * A.1 2 0, -(A.1 0 0 * A.1 2 1) + A.1 0 1 * A.1 2 0, A.1 0 0 * A.1 1 1 - A.1 0 1 * A.1 1 0], SL3_inv_expl_det A⟩ := by
  ext
  have := Matrix.adjugate_fin_three A.1
  simp_all only [Fin.isValue, SpecialLinearGroup.coe_inv, of_apply, cons_val', cons_val_fin_one]

theorem inj : Function.Injective F_2_to_Rots := by
  rw [← MonoidHom.ker_eq_bot_iff]

  ext w

  simp [MonoidHom.ker, F_2_to_Rots]
  sorry
/-  apply Iff.intro
  .
    induction hn: FreeGroup.norm w generalizing w with
    | zero =>
      sorry
    | succ   n ih =>
      intro h


      have split_w : w = mk [w.toWord.head sorry] * mk w.toWord.tail := by sorry
      have h2 : (mk w.toWord.tail).norm = n := by sorry
      specialize ih (mk w.toWord.tail) h2

      obtain ⟨a,b,c,h1⟩ := Free_Rots_mul_vec (mk w.toWord.tail)
      have h_tail : (lift fin_2_to_rots) (mk w.toWord.tail) = 1 -> false := by
        rw [split_w, _root_.map_mul] at h
        rw [← h]
        intro hC
        apply_fun (. * ((lift fin_2_to_rots) (mk w.toWord.tail))⁻¹) at hC
        rw [mul_inv_cancel, mul_assoc, mul_inv_cancel] at hC
        simp [fin_2_to_rots] at hC
        sorry -- stimmt
      obtain ⟨a',b',c',hrot⟩ := Free_Rots_mul_vec w
      have hrot1 := hrot
      have hrot2 := hrot
      rw[h] at hrot2
      simp at hrot2
      obtain ⟨ha, hb, hc⟩ := hrot2
      apply_fun ((3 ^ w.toWord.length) * ·) at hb
      simp at hb
      simp [ha, ← hb, hc] at hrot
      rw [split_w, _root_.map_mul] at hrot
      simp [-lift_mk,Subgroup.coe_mul, SpecialLinearGroup.coe_mul, ← mulVec_mulVec, h1] at hrot
      cases h_case : (w.toWord.head sorry).2
      . simp [fin_2_to_rots, h_case] at hrot
        -- cases mit head.2
        -- dann irgendwie zeigen, dass es nd geht??

      -- irgendwas mit a = c = 0 oder b = 1 genau dann wenn w = 0 (weil length dann 0)
      have h_len : w.toWord.length > 0 := by sorry
      have h1' := h1
      have h1'' := h1
      have h' : (lift fin_2_to_rots) (mk w.toWord.tail) = 1 := by sorry
      rw [h'] at h1
      simp at h1
      simp [h1, h'] at h1'

      cases h1' with
      | inl h =>
        have hb : b = 3^ w.toWord.tail.length := by sorry
        /-
          apply_fun ((3 ^ w.toWord.length) * .) at h
          simp at h
          simp_all only [gt_iff_lt, Nat.succ_eq_add_one, Nat.reduceAdd, OneMemClass.coe_one,
            SpecialLinearGroup.coe_one, one_mulVec, Int.cast_zero, zero_mul, smul_cons, smul_eq_mul,
            mul_zero, smul_empty, vecCons_inj, mul_eq_mul_right_iff, Int.cast_eq_zero, and_true,
            true_and]
          apply_fun ((3 ^ w.toWord.length) * .) at h
          simp at h
          rify
          exact h.symm-/
        obtain ⟨ha, -,hc⟩ := h1
        subst ha hb hc
        clear h
        simp at h1''

      | inr h =>
        sorry


        -- induktion über die länge von w.toWord => FreeGroup.norm

#exit
      --- blöd, wie schließt man aus, dass tail = [head.inv]
      --- todo rausfinden, wie a, b, c aussieht, wenn man w invertiert (TODO konkrete Formel für invertierung von SL(3,R) Matrizen)
      induction hw: w using FreeGroup.induction_on with

      | C1 => grind
      | of x => sorry
      | inv_of x _ => sorry
      | mul x y h1 h2 =>
        rw [hw] at h1''
        simp at h1''
        --- todo sagen, dass x != y.inv
        sorry









    | inr h => simp_all


  simp_all

#exit-/
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
noncomputable def equiv :  FreeGroup (Fin 2) ≃* ↥Free_Rots where
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

#check equiv
noncomputable def basis : FreeGroupBasis (Fin 2) ↥Free_Rots where
  repr := equiv.symm

instance : IsFreeGroup ↥Free_Rots where
  nonempty_basis := by
    use (Fin 2)
    refine Nonempty.intro basis


noncomputable def Free_Free_Rots := (IsFreeGroup.toFreeGroup Free_Rots)

#check Free_Free_Rots

abbrev ℝ_3 := Fin 3 -> ℝ

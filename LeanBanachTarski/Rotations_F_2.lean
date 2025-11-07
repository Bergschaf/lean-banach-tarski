import LeanBanachTarski.Definitions
import Mathlib.Tactic.Rify

open Matrix FreeGroup

theorem inj : Function.Injective F_2_to_Rots := by
  rw [← MonoidHom.ker_eq_bot_iff]
  ext w
  simp [MonoidHom.ker, F_2_to_Rots]
  apply Iff.intro
  . intro h
    obtain ⟨a,b,c,h1⟩ := Free_Rots_mul_vec w
    by_contra hc
    -- irgendwas mit a = c = 0 oder b = 1 genau dann wenn w = 0 (weil length dann 0)
    have h_len : w.toWord.length > 0 := by
      contrapose h
      simp_all only [Nat.succ_eq_add_one, Nat.reduceAdd, one_div, smul_cons, smul_eq_mul,
        smul_empty, gt_iff_lt, not_lt, nonpos_iff_eq_zero, List.length_eq_zero_iff,
        toWord_eq_nil_iff, not_true_eq_false, not_false_eq_true]
    have h1' := h1
    have h1'' := h1
    rw [h] at h1
    simp at h1
    simp [h1, h] at h1'
    cases h1' with
    | inl h =>
      have hb : b = 3^ w.toWord.length := by
        apply_fun ((3 ^ w.toWord.length) * .) at h
        simp at h
        simp_all only [gt_iff_lt, Nat.succ_eq_add_one, Nat.reduceAdd, OneMemClass.coe_one,
          SpecialLinearGroup.coe_one, one_mulVec, Int.cast_zero, zero_mul, smul_cons, smul_eq_mul,
          mul_zero, smul_empty, vecCons_inj, mul_eq_mul_right_iff, Int.cast_eq_zero, and_true,
          true_and]
        apply_fun ((3 ^ w.toWord.length) * .) at h
        simp at h
        rify
        exact h.symm
      clear h1 h
      subst hb
      sorry
    | inr h => simp_all
  simp_all

#exit
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

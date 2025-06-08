import Mathlib.Algebra.Group.Action.Equidecomp
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Pi.Irrational
import Mathlib.Data.Real.Irrational
import Mathlib.Tactic.SplitIfs
import Mathlib.Topology.Instances.AddCircle.Defs

/-!
# The deleted `AddCircle` is equidecomposable to the `AddCircle`

This file shows an application of equidecomposition,
to the elementary example of a circle being equidecomposable with
a circle with a missing point.

Instead of using the `Circle` structure, we use `AddCircle` to simplify our proof.
-/

/--
The two potential actions that we can make in our additive circle equidecomposition:
stay or move.
-/
inductive AddCircleRotation where
  | stay
  | move
deriving DecidableEq, Repr

instance : Top (Finset AddCircleRotation) := ⟨{.stay, .move}⟩

open Real AddCircle

variable (r : ℝ) (hr : Irrational r)

/-- TODO(mathlib4): PR -/
@[simp]
theorem AddCircle_coe_zero : ↑(0 : ℝ) = (0 : AddCircle r) :=
  rfl


noncomputable instance : SMul AddCircleRotation (AddCircle r) :=
  ⟨fun x θ ↦ if x = .move then θ + (-1 : ℝ) else θ⟩

open Classical in
/--
We say that the deleted circle (a circle with one point missing) is equidecomposable
with the circle by moving every point that is ℕ+ radians forward from in the deleted circle
back by one radian.
-/
noncomputable def add_circle_equidecomp (m : AddCircle r) : Equidecomp (AddCircle r) AddCircleRotation where
  toFun θ := if ∃ (n : ℕ+), θ = m + (n : ℝ) then θ - (1 : ℝ) else θ
  invFun θ := if ∃ (n : ℕ), θ = m + (n : ℝ) then θ + (1 : ℝ) else θ
  source := ⊤ \ {m}
  target := ⊤
  map_source' := by simp
  map_target' x h := by
    simp_rw [Set.top_eq_univ, Set.mem_diff, Set.mem_singleton_iff, Set.mem_univ, true_and]
    split_ifs with h₁
    · rw [h₁.choose_spec, add_assoc, add_eq_left,
          ← AddCircle.coe_add, AddCircle.coe_eq_zero_iff, ← Nat.cast_add_one]
      push_neg
      intro n
      by_cases h₃ : n = 0
      · rw [h₃, zero_zsmul]
        -- The ℕ cast is necessary: ((h₁.choose + 1) : ℝ) turns to ((h₁.choose : ℝ) + 1)
        exact NeZero.ne' (((h₁.choose + 1) : ℕ) : ℝ)
      · refine Irrational.ne_nat ?_ (h₁.choose + 1)
        rw [zsmul_eq_mul]
        refine (.intCast_mul hr h₃)
    · push_neg at h₁
      have h₂ := h₁ 0
      simp_rw [CharP.cast_eq_zero, AddCircle_coe_zero, add_zero, ne_eq] at h₂
      exact h₂
  left_inv' x h := by
    simp_all only
      [Set.top_eq_univ, Set.mem_diff, Set.mem_univ, Set.mem_singleton_iff, true_and, ne_eq]
    split
    next h₁ =>
      rw [sub_add_cancel, ite_eq_left_iff, not_exists, h₁.choose_spec, add_sub_assoc]
      intro p
      have h₂ := p (h₁.choose - 1)
      simp only [add_right_inj, Angle.coe_sub, PNat.pos, Nat.cast_pred] at h₁ h₂
      contradiction
    next h₁ =>
      simp_all only [not_exists, ite_eq_right_iff, forall_exists_index]
      intro x₁ _
      have := h₁ ⟨x₁, Nat.zero_lt_of_ne_zero (fun _ ↦ by
        simp_all only [CharP.cast_eq_zero, AddCircle_coe_zero, add_zero, not_true_eq_false] )⟩
      rw [PNat.mk_coe] at this
      contradiction
  right_inv' x h := by
    simp_all only [Set.top_eq_univ, Set.mem_univ]
    split_ifs with h₁ h₂ <;> try simp_all only [add_sub_cancel_right, not_exists, exists_const]
    have q := h₂ (⟨h₁.choose + 1, by simp_rw [add_pos_iff, Nat.lt_one_iff, or_true]⟩)
    rw [PNat.mk_coe, Nat.cast_add, Nat.cast_one,
      AddCircle.coe_add, ← add_assoc, ← h₁.choose_spec] at q
    contradiction
  isDecompOn' := by
    simp_rw [Set.top_eq_univ]
    refine ⟨⊤, fun θ h ↦ ?_⟩
    by_cases h₁ : ∃ (n : ℕ+), θ = m + (n : ℝ)
    · exact ⟨.move, ⟨by decide, if_pos h₁⟩⟩
    · exact ⟨.stay, ⟨by decide, if_neg h₁⟩⟩

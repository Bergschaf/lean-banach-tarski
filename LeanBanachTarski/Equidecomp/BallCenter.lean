import Mathlib.Algebra.Group.Action.Equidecomp
import Mathlib.Analysis.Normed.Field.UnitBall
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Pi.Irrational
import Mathlib.Data.Real.Irrational
import Mathlib.Tactic.SplitIfs
import Mathlib.Topology.Instances.AddCircle

-- Note: we don't use an arbitrary point, as the proof mechanism we use to proof this
-- has a special case for the center point: since this builds up to the
-- strong Banach-Tarski theorem anyways

/-!
# The equidecomposable of the centerless n-sphere to the full n-sphere (for 2 ≤ n).
-/

inductive BallRotation where
  | stay
  | move
deriving DecidableEq, Repr

instance : Top (Finset BallRotation) := ⟨{.stay, .move}⟩

variable (r : ℝ) (hr : Irrational r) (n : ℕ) (hd : 2 ≤ n)

abbrev Point := (Fin n -> ℝ)
abbrev origin : Point n := fun _ => (0 : ℝ)
abbrev Ball : Set (Point n) := Euclidean.closedBall (origin n) r

-- TODO: we want to define this as the rotation of points on a specific circle.
noncomputable instance : SMul BallRotation (Point n) :=
  ⟨fun x p ↦ if x = .move then sorry else p⟩

open Classical in
noncomputable def circle_equidecomp : Equidecomp (Point n) BallRotation where
  toFun := sorry
  invFun := sorry
  source := (Ball r n) \ {origin n}
  target := (Ball r n)
  map_source' := sorry
  map_target' := sorry
  left_inv' := sorry
  right_inv' := sorry
  isDecompOn' := sorry

import Mathlib.Algebra.Group.Action.Equidecomp
import Mathlib.Analysis.Normed.Field.UnitBall
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Pi.Irrational
import Mathlib.Data.Real.Irrational
import Mathlib.Tactic.SplitIfs
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The equidecomposable of the deleted geometric unit circle to the unit circle.
-/

inductive CircleRotation where
  | stay
  | move
deriving DecidableEq, Repr

instance : Top (Finset CircleRotation) := ⟨{.stay, .move}⟩

noncomputable instance : SMul CircleRotation Circle :=
  ⟨fun x p ↦ if x = .move then p * ((1 : ℝ) : Real.Angle).toCircle else p⟩

-- TODO: we should derive this from the AddCircle equidecomposition with equivariant bijections

open Classical in
noncomputable def circle_equidecomp (m : Circle) : Equidecomp Circle CircleRotation := sorry

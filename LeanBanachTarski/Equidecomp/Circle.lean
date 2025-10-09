import Mathlib.Algebra.Group.Action.Equidecomp
import Mathlib.Analysis.Normed.Field.UnitBall
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Real.Pi.Irrational
import Mathlib.Data.Real.Irrational
import Mathlib.Tactic.SplitIfs
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import LeanBanachTarski.Definitions
import LeanBanachTarski.Equidecomp.Equidecomp
import Mathlib.Data.Matrix.Mul

def TestCircle : Set ℝ_3 := {x | |x| = 1 ∧ x 3 = 0}
def TestCircle' := TestCircle \ {![1,0,0]}

instance : SMul SO_3 ℝ_3 where
    smul A r := A.val.mulVec r


def decomp : Equidecomp.Equipartition ℝ_3 SO_3 where
    parts := {}

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

def TestCircle : Set ℝ_3 := {x | dist x (0 : ℝ_3) = 1 ∧ x 2 = 0}
def TestCircle' := TestCircle \ {![1,0,0]}

instance : SMul SO_3 ℝ_3 where
    smul A r := A.val.mulVec r

lemma det_eq_1 (n : ℕ) : Matrix.det !![Real.cos n, Real.sin n, 0 ; -Real.sin n, Real.cos n, 0; 0, 0, 1] = 1 := by
    simp [Matrix.det_fin_three, ← Real.cos_sub]


noncomputable def rotate (n : ℕ) : SO_3 where
    val := !![Real.cos n, Real.sin n, 0 ; -Real.sin n, Real.cos n, 0; 0, 0, 1]
    property := by
        simp [SO_3, @Matrix.mem_specialOrthogonalGroup_iff, det_eq_1]
        rw [Matrix.mem_orthogonalGroup_iff] -- TODO mem orthogonal group if det=1??
        simp
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.vecHead, Matrix.vecTail, ← Real.cos_sub] <;> ring_nf
        exact Real.sin_sq_add_cos_sq ↑n

lemma rotate_0_eq_one : rotate 0 = 1 := by
  simp [rotate]
  exact Eq.symm Matrix.one_fin_three

def start : ℝ_3 := ![1, 0, 0]
def part_1 := {x ∈ TestCircle | ∃ n : ℕ, (rotate n).val.mulVec start = x}


noncomputable def decomp : Equidecomp.Equipartition ℝ_3 SO_3 where
  parts :=  {val := {(part_1, rotate 1, part_1 ∪ {start}),
        (TestCircle \ (part_1 ∪ {start}), 1, TestCircle \ (part_1 ∪ {start}))},
               nodup := by
                simp
                sorry
                }
  supIndepSource := by
    sorry
  supIndepTarget := by
    sorry
  bot_notMem := by
    simp [part_1]
    constructor
    . use start
      simp [TestCircle, start]
      constructor
      . rw [norm_eq_sqrt_real_inner]
        . simp
          sorry
        . rw [InnerProductSpace]





      . use 0
        rw [rotate_0_eq_one]
        simp
    . simp [TestCircle, start]

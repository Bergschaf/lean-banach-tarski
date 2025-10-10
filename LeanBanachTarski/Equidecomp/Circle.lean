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
import Mathlib

def TestCircle : Set ℝ_3 := {x | dist x (0 : ℝ_3) = 1 ∧ x 2 = 0}
def TestCircle' := TestCircle \ {![1,0,0]}

instance : SMul SO_3 ℝ_3 where
    smul A r := A.val.mulVec r

lemma det_eq_1 (n : ℕ) : Matrix.det !![Real.cos n, Real.sin n, 0 ; -Real.sin n, Real.cos n, 0; 0, 0, 1] = 1 := by
    simp [Matrix.det_fin_three, ← Real.cos_sub]

noncomputable def rotate (n : ℤ) : SO_3 where
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
                simp only [Set.union_singleton, Multiset.insert_eq_cons, Multiset.nodup_cons,
                  Multiset.mem_singleton, Prod.mk.injEq, not_and, Multiset.nodup_singleton,
                  and_true]
                sorry
                }
  supIndepSource := by
    sorry
  supIndepTarget := by
    sorry
  bot_notMem := by
    simp only [part_1, Set.union_singleton, Multiset.insert_eq_cons, Finset.mk_cons,
      Finset.mem_cons, Finset.mem_mk, Multiset.mem_singleton, ne_eq, forall_eq_or_imp,
      Set.sep_eq_empty_iff_mem_false, not_exists, not_forall, Classical.not_imp, Decidable.not_not,
      forall_eq]
    constructor
    . use start
      simp only [start, TestCircle, dist_zero_right, Fin.isValue, Set.mem_setOf_eq, Matrix.cons_val,
        and_true, exists_prop]
      constructor
      . simp [@Pi.norm_def]
        apply le_antisymm
        · simp only [Finset.sup_le_iff, Finset.mem_univ, forall_const]
          intro b
          fin_cases b <;> simp
        . simp
          use 0
          simp
      . use 0
        rw [rotate_0_eq_one]
        simp
    . simp only [TestCircle, dist_zero_right, Fin.isValue, start, Set.mem_setOf_eq]
      sorry
  decomp := by
    simp only [part_1, start, Set.union_singleton, Multiset.insert_eq_cons, Finset.mk_cons,
      Finset.mem_cons, Finset.mem_mk, Multiset.mem_singleton, forall_eq_or_imp, forall_eq, one_smul,
      Set.image_id', and_true]
    ext i
    simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_insert_iff]
    constructor
    . simp only [forall_exists_index, and_imp]
      intro x hx n h1 h2

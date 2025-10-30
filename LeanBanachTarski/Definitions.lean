import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.GroupTheory.FreeGroup.IsFreeGroup

noncomputable section
def matrix_a   : Matrix (Fin 3) (Fin 3) Real := !![1, 0, 0; 0, 1/3, -2/3*Real.sqrt 2; 0, 2/3*Real.sqrt 2, 1/3]
def matrix_a'  : Matrix (Fin 3) (Fin 3) Real := !![1, 0, 0; 0, 1/3, 2/3*Real.sqrt 2; 0, -2/3*Real.sqrt 2, 1/3]
def matrix_b   : Matrix (Fin 3) (Fin 3) Real := !![1/3, -2/3*Real.sqrt 2, 0; (2/3*Real.sqrt 2), 1/3, 0; 0, 0, 1]
def matrix_b'  : Matrix (Fin 3) (Fin 3) Real := !![1/3, 2/3*Real.sqrt 2, 0; (-2/3*Real.sqrt 2), 1/3, 0; 0, 0, 1]
def matrix_one : Matrix (Fin 3) (Fin 3) Real := 1
end noncomputable section


theorem matrix_a_det_eq_one : Matrix.det matrix_a = 1 := by
  rw [matrix_a, Matrix.det_fin_three]
  norm_num
  simp only [one_div, Fin.isValue, Matrix.cons_val, Matrix.cons_val_one, neg_mul, sub_neg_eq_add,
    zero_mul, mul_zero, sub_zero]
  ring_nf
  norm_num

theorem matrix_a'_det_eq_one : Matrix.det matrix_a' = 1 := by
  rw [matrix_a', Matrix.det_fin_three]
  norm_num
  simp only [one_div, Fin.isValue, Matrix.cons_val, Matrix.cons_val_one, mul_neg, sub_neg_eq_add,
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

theorem matrix_b'_det_eq_one : Matrix.det matrix_b' = 1 := by
  rw [matrix_b', Matrix.det_fin_three]
  norm_num
  simp only [one_div, Fin.isValue, Matrix.cons_val, Matrix.cons_val_one, mul_one, mul_zero,
    sub_zero, add_zero, zero_mul, neg_zero]
  ring_nf
  norm_num

theorem matrix_one_det_eq_one : Matrix.det matrix_one = 1 := by
  rw [matrix_one, Matrix.det_fin_three]
  simp

open MatrixGroups


noncomputable section
def sl_a : SL(3, ℝ) := ⟨matrix_a, matrix_a_det_eq_one⟩
def sl_a' : SL(3, ℝ) := ⟨matrix_a', matrix_a'_det_eq_one⟩
def sl_b : SL(3, ℝ) := ⟨matrix_b, matrix_b_det_eq_one⟩
def sl_b' : SL(3, ℝ) := ⟨matrix_b', matrix_b'_det_eq_one⟩
def sl_one : SL(3, ℝ) := ⟨matrix_one, matrix_one_det_eq_one⟩
end noncomputable section


-- TOOD mathlib?? closure von ... ist free Group.
def F_2 : Subgroup SL(3, ℝ) := Subgroup.closure {sl_a, sl_b, sl_a', sl_b'}

instance : IsFreeGroup F_2 where
  nonempty_basis := by
    sorry

abbrev ℝ_3 := Fin 3 -> ℝ

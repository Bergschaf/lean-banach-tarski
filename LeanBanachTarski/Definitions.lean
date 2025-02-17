import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

noncomputable section
def matrix_a   : Matrix (Fin 3) (Fin 3) Real := !![1, 0, 0; 0, 1/3, -2/3*Real.sqrt 2; 0, 2/3*Real.sqrt 2, 1/3]
def matrix_a'  : Matrix (Fin 3) (Fin 3) Real := !![1, 0, 0; 0, 1/3, 2/3*Real.sqrt 2; 0, -2/3*Real.sqrt 2, 1/3]
def matrix_b   : Matrix (Fin 3) (Fin 3) Real := !![1/3, -2/3*Real.sqrt 2, 0; (2/3*Real.sqrt 2), 1/3, 0; 0, 0, 1]
def matrix_b'  : Matrix (Fin 3) (Fin 3) Real := !![1/3, 2/3*Real.sqrt 2, 0; (-2/3*Real.sqrt 2), 1/3, 0; 0, 0, 1]
def matrix_one : Matrix (Fin 3) (Fin 3) Real := 1
end noncomputable section


theorem matrix_a_det_neq_zero : Matrix.det matrix_a ≠ 0 := by
  rw [matrix_a]
  rw [Matrix.det_fin_three]
  simp
  norm_num
  ring_nf
  simp
  norm_num

theorem matrix_a'_det_neq_zero : Matrix.det matrix_a' ≠ 0 := by
  rw [matrix_a']
  rw [Matrix.det_fin_three]
  simp
  norm_num
  ring_nf
  simp
  norm_num

theorem matrix_b_det_neq_zero : Matrix.det matrix_b ≠ 0 := by
  rw [matrix_b]
  rw [Matrix.det_fin_three]
  simp
  norm_num
  ring_nf
  simp
  norm_num

theorem matrix_b'_det_neq_zero : Matrix.det matrix_b' ≠ 0 := by
  rw [matrix_b']
  rw [Matrix.det_fin_three]
  simp
  norm_num
  ring_nf
  simp
  norm_num

theorem matrix_one_det_neq_zero : Matrix.det matrix_one ≠ 0 := by
  rw [matrix_one]
  rw [Matrix.det_fin_three]
  simp


noncomputable section
def gl_a   : GL (Fin 3) Real := Matrix.GeneralLinearGroup.mkOfDetNeZero matrix_a matrix_a_det_neq_zero
def gl_a'  : GL (Fin 3) Real := Matrix.GeneralLinearGroup.mkOfDetNeZero matrix_a' matrix_a'_det_neq_zero
def gl_b   : GL (Fin 3) Real := Matrix.GeneralLinearGroup.mkOfDetNeZero matrix_b matrix_b_det_neq_zero
def gl_b'  : GL (Fin 3) Real := Matrix.GeneralLinearGroup.mkOfDetNeZero matrix_b' matrix_b'_det_neq_zero
def gl_one : GL (Fin 3) Real := Matrix.GeneralLinearGroup.mkOfDetNeZero matrix_one matrix_one_det_neq_zero
end noncomputable section


def generator : Set (GL (Fin 3) Real) := {gl_a, gl_b}

def G := Subgroup.closure generator


abbrev r_3 := Fin 3 -> ℝ
abbrev r_2 := Fin 2 -> ℝ
def zero_one_zero : r_3 := ![0,1,0]

def rotate (p : GL (Fin 3) Real) (vec : r_3) : r_3 :=
  (p : Matrix (Fin 3) (Fin 3) Real).vecMul vec

def rotate_set (x : Set r_3) (p : GL (Fin 3) Real) : Set r_3 :=
  {w : r_3  | ∃ v, v ∈ x ∧ rotate p v = w}

def rotate_n_times (n : ℕ) (p : GL (Fin 3) Real) (vec : r_3) : r_3 :=
  match n with
  | 0 => vec
  | Nat.succ m => rotate_n_times m p (rotate p vec)

def translate (p : r_3) (vec : r_3) : r_3 := p + vec

def unitBall : Set (Fin 3 -> ℝ) := Euclidean.closedBall ![(0 : ℝ), (0 : ℝ), (0 : ℝ)] 1
def origin : r_3 := ![0,0,0]
def unitBall_without_origin := unitBall \ {origin}

def fixpoint (y: r_3) (p: GL (Fin 3) Real) := rotate p y = y

def D := {w :unitBall_without_origin | ∀ p : G, fixpoint w p}

def RotationAxis (p : GL (Fin 3) Real) : Set r_3 :=
  {w : r_3 | fixpoint w p}


inductive Generator
  | gl_a : Generator
  | gl_b : Generator
  deriving DecidableEq

abbrev G_list := {w : List (Generator × Bool) // w = FreeGroup.reduce w}

def S_A := {w : G_list | w.val.head? = some (Generator.gl_a, true)}
def S_A' := {w : G_list | w.val.head? = some (Generator.gl_a, false)}
def S_B := {w : G_list | w.val.head? = some (Generator.gl_b, true)}
def S_B' := {w : G_list | w.val.head? = some (Generator.gl_b, false)}


def item_to_matrix (i : Generator × Bool) : GL (Fin 3) Real :=
  match i with
  | (Generator.gl_a, true) => gl_a
  | (Generator.gl_a, false) => gl_a'
  | (Generator.gl_b, true) => gl_b
  | (Generator.gl_b, false) => gl_b'


def list_to_matrix (w : List (Generator × Bool)) : GL (Fin 3) Real :=
  match w with
  | [] => gl_one
  | (head::rest) =>  list_to_matrix rest * item_to_matrix head

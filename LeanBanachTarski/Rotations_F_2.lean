/-
This file was edited by Aristotle.

Lean Toolchain version: leanprover/lean4:v4.20.0-rc5
Mathlib version: d62eab0cc36ea522904895389c301cf8d844fd69 (May 9, 2025)

The following was proved by Aristotle:

- theorem inj : Function.Injective F_2_to_Rots
-/

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

section AristotleLemmas

def GoodTriple (head : Option (Fin 2 × Bool)) (a b c : ℤ) : Prop :=
  b % 3 ≠ 0 ∧
  match head with
  | none => a = 0 ∧ c = 0
  | some (1, true) => a % 3 = 0 ∧ (b - c) % 3 ≠ 0
  | some (1, false) => a % 3 = 0 ∧ (b + c) % 3 ≠ 0
  | some (0, true) => c % 3 = 0 ∧ (a + b) % 3 ≠ 0
  | some (0, false) => c % 3 = 0 ∧ (b - a) % 3 ≠ 0

lemma reduce_cons_of_reduce_cons {α} [DecidableEq α] {x : α × Bool} {L : List (α × Bool)}
    (h : FreeGroup.reduce (x :: L) = x :: L) : FreeGroup.reduce L = L := by
  cases h' : FreeGroup.reduce L <;> aesop;
  replace h' := congr_arg List.length h'; simp_all +arith +decide;
  -- By definition of reduce, the length of the reduced list is less than or equal to the original length.
  have h_length : ∀ (L : List (α × Bool)), (FreeGroup.reduce L).length ≤ L.length := by
    intro L
    induction' L with x L ih;
    · rfl;
    · cases h : FreeGroup.reduce L <;> aesop;
      linarith;
  linarith [ h_length L ]


def next_coeffs (g : Fin 2 × Bool) (a b c : ℤ) : ℤ × ℤ × ℤ :=
  match g with
  | (1, true)  => (3 * a, b - 4 * c, 2 * b + c)
  | (1, false) => (3 * a, b + 4 * c, -2 * b + c)
  | (0, true)  => (a - 2 * b, 4 * a + b, 3 * c)
  | (0, false) => (a + 2 * b, -4 * a + b, 3 * c)

lemma GoodTriple_step {g : Fin 2 × Bool} {head : Option (Fin 2 × Bool)} {a b c : ℤ}
    (h_good : GoodTriple head a b c)
    (h_red : match head with | none => true | some h => g ≠ (h.1, !h.2)) :
    let (a', b', c') := next_coeffs g a b c
    GoodTriple (some g) a' b' c' := by
      rcases head with - | head;
      · cases g ; ( unfold GoodTriple at * ; aesop; );
        all_goals unfold next_coeffs at *; simp_all +decide [ dvd_sub_comm, dvd_add, dvd_mul_of_dvd_right ] ;
        · exact left ( by rw [ Int.dvd_iff_emod_eq_zero ] at *; omega );
        · -- Simplify the expression $b + -(2 * b)$ to $-b$.
          ring_nf at *;
          -- Since 3 divides -b, it must also divide b, which contradicts the assumption that 3 does not divide b.
          exact left (by simpa using a);
        · exact left ( by rw [ Int.dvd_iff_emod_eq_zero ] at *; omega );
        · exact left ( by rw [ Int.dvd_iff_emod_eq_zero ] at *; omega );
      · unfold GoodTriple at *;
        fin_cases head <;> fin_cases g <;> simp +decide [ next_coeffs ] at * <;> omega


lemma fin_2_to_rots_val_0 : (fin_2_to_rots 0 : Matrix (Fin 3) (Fin 3) ℝ) = matrix_b := by
  have : (0 : Fin 2) = 2 := rfl
  rw [this]
  unfold fin_2_to_rots
  simp [sl_b]

lemma fin_2_to_rots_val_1 : (fin_2_to_rots 1 : Matrix (Fin 3) (Fin 3) ℝ) = matrix_a := by
  unfold fin_2_to_rots
  simp [sl_a]

lemma fin_2_to_rots_sl_0 : fin_2_to_rots 0 = sl_b := by
  have : (0 : Fin 2) = 2 := rfl
  rw [this]
  unfold fin_2_to_rots
  simp

lemma fin_2_to_rots_sl_1 : fin_2_to_rots 1 = sl_a := by
  unfold fin_2_to_rots
  simp

def compute_coeffs : List (Fin 2 × Bool) → ℤ × ℤ × ℤ
  | [] => (0, 1, 0)
  | head :: tail => next_coeffs head (compute_coeffs tail).1 (compute_coeffs tail).2.1 (compute_coeffs tail).2.2

lemma head_not_inv_of_reduced {α} [DecidableEq α] {head : α × Bool} {tail : List (α × Bool)}
    (h : FreeGroup.reduce (head :: tail) = head :: tail) :
    match tail.head? with
    | none => true
    | some h' => head ≠ (h'.1, !h'.2) := by
      induction tail <;> aesop;
      -- If snd were not equal to snd_1, then the first two elements would be inverses, and the reduce function would remove them, resulting in a shorter list. But h says that the reduce of the list is the same as the original list, which means that the first two elements can't be inverses. Therefore, snd must equal snd_1.
      by_contra h_contra;
      replace h := congr_arg List.length h ; simp_all +decide;
      -- Since the length of the reduced tail is the same as the original tail's length, we can substitute this into `h`.
      have h_reduced_tail_length : (FreeGroup.reduce tail).length ≤ tail.length := by
        have h_reduced_tail_length : ∀ (L : List (α × Bool)), (FreeGroup.reduce L).length ≤ L.length := by
          intro L;
          induction L <;> aesop;
          induction tail_1 using List.reverseRecOn <;> aesop;
          refine' le_trans _ ( add_le_add_right tail_ih_1 1 );
          induction ( FreeGroup.reduce ( l ++ [ ( fst_3, snd_4 ) ] ) ) <;> aesop;
          linarith;
        exact h_reduced_tail_length tail;
      cases hc : FreeGroup.reduce tail <;> simp_all +arith +decide;
      · by_cases hC: snd = !snd_1
        . grind
        . simp [hC] at h
          grind

      · split_ifs at * <;> simp_all +arith +decide;
        · contrapose! h;
          refine' ne_of_lt ( lt_of_le_of_lt ( _ : _ ≤ _ ) ( Nat.lt_succ_of_le ( Nat.le_succ_of_le h_reduced_tail_length ) ) );
          induction ‹List ( α × Bool ) › <;> aesop;
          linarith;
        · split_ifs at h <;> simp_all +arith +decide


#check head_not_inv_of_reduced

lemma Matrix_step (g : Fin 2 × Bool) (a b c : ℤ) :
    (if g.2 then (fin_2_to_rots g.1 : Matrix (Fin 3) (Fin 3) ℝ) else ((fin_2_to_rots g.1)⁻¹ : Matrix (Fin 3) (Fin 3) ℝ)) *ᵥ ![a * Real.sqrt 2, b, c * Real.sqrt 2] =
    (1/3 : ℝ) • ![(next_coeffs g a b c).1 * Real.sqrt 2, (next_coeffs g a b c).2.1, (next_coeffs g a b c).2.2 * Real.sqrt 2] := by
  bound;
  · fin_cases fst <;> norm_num [ fin_2_to_rots_val_0, fin_2_to_rots_val_1, next_coeffs ] <;> ring;
    · ext i ; fin_cases i <;> norm_num [ matrix_b ] <;> ring;
      norm_num ; ring;
    · unfold matrix_a; ext i; fin_cases i <;> norm_num [ Matrix.mulVec ] <;> ring;
      norm_num ; ring;
  · -- By definition of matrix multiplication and the properties of the adjugate matrix, we can compute the inverse of matrix_a and matrix_b.
    have h_inv_a : (fin_2_to_rots 1 : Matrix (Fin 3) (Fin 3) ℝ)⁻¹ = !![1, 0, 0; 0, 1/3, 2/3*Real.sqrt 2; 0, -2/3*Real.sqrt 2, 1/3] := by
      unfold fin_2_to_rots;
      rw [ Matrix.inv_eq_left_inv ];
      unfold sl_a; norm_num [ ← List.ofFn_inj, Matrix.mul_fin_three ]
      unfold matrix_a; ext i j; fin_cases i <;> fin_cases j <;> norm_num [ Matrix.mul_apply, Fin.sum_univ_succ ] <;> ring;
      · norm_num;
      · norm_num
    have h_inv_b : (fin_2_to_rots 0 : Matrix (Fin 3) (Fin 3) ℝ)⁻¹ = !![1/3, 2/3*Real.sqrt 2, 0; -2/3*Real.sqrt 2, 1/3, 0; 0, 0, 1] := by
      unfold fin_2_to_rots; norm_num [ Matrix.inv_def ] ;
      unfold sl_b; norm_num [ Matrix.adjugate_fin_three ] ;
      unfold matrix_b; norm_num [ Fin.ext_iff ] ; ring; norm_num;
      --simp +zetaDelta at *;
    -- By definition of matrix multiplication and the properties of the adjugate matrix, we can compute the inverse of matrix_a and matrix_b. We'll handle each case separately.
    cases fst <;> simp_all +decide [ Matrix.mulVec ];
    interval_cases ( ‹_› : ℕ ) <;> simp_all +decide [ ← List.ofFn_inj ];
    · unfold next_coeffs; norm_num; ring_nf; norm_num;
      ring;
    · unfold next_coeffs; norm_num ; ring ; norm_num;
      ring


end AristotleLemmas

theorem inj : Function.Injective F_2_to_Rots := by
  rw [← MonoidHom.ker_eq_bot_iff]

  ext w

  simp [MonoidHom.ker, F_2_to_Rots]
  -- If $w$ is non-trivial, then $F_2_to_Rots w$ will be a product of the matrices $sl_a$ and $sl_b$, which can't be the identity.
  have h_nontrivial : ∀ w : FreeGroup (Fin 2), w ≠ 1 → (F_2_to_Rots w : Matrix (Fin 3) (Fin 3) ℝ) ≠ 1 := by
    have h_nontrivial : ∀ w : List (Fin 2 × Bool), w ≠ [] → FreeGroup.reduce w = w → (F_2_to_Rots (FreeGroup.mk w) : Matrix (Fin 3) (Fin 3) ℝ) ≠ 1 := by
      intros w hw_ne_empty hw_reduced
      have h_coeffs : ∃ a b c : ℤ, ((F_2_to_Rots (FreeGroup.mk w)) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ ![0, 1, 0] = (1/3^w.length : ℝ) • ![a * Real.sqrt 2, b, c * Real.sqrt 2] ∧ GoodTriple w.head? a b c := by
        induction' w with g w ih;
        · contradiction;
        · by_cases hw_empty : w = [] <;> simp_all +decide [ FreeGroup.lift ];
          · use (compute_coeffs [g]).1, (compute_coeffs [g]).2.1, (compute_coeffs [g]).2.2;
            bound;
            · have h_step : ∀ g : Fin 2 × Bool, (if g.2 then (fin_2_to_rots g.1 : Matrix (Fin 3) (Fin 3) ℝ) else ((fin_2_to_rots g.1)⁻¹ : Matrix (Fin 3) (Fin 3) ℝ)) *ᵥ ![0, 1, 0] = (1/3 : ℝ) • ![(next_coeffs g 0 1 0).1 * Real.sqrt 2, (next_coeffs g 0 1 0).2.1, (next_coeffs g 0 1 0).2.2 * Real.sqrt 2] := by
                intro g; exact (by
                convert Matrix_step g 0 1 0 using 1 ; norm_num [ fin_2_to_rots ]);
              convert h_step ( fst, snd ) using 1 ; norm_num [ compute_coeffs ];
              · simp +zetaDelta at *;
                split_ifs <;> simp_all ( config := { decide := Bool.true } ) [ F_2_to_Rots ];
                convert h_step fst |>.1 using 1;
                rw [ Matrix.inv_def ] ; aesop;
              · norm_num [ compute_coeffs ];
            · fin_cases fst <;> fin_cases snd <;> simp +decide [ GoodTriple ];
          · rcases ih ( by
              have h_reduced : FreeGroup.reduce (g :: w) = g :: w := by
                convert hw_reduced using 1;
              exact? ) with ⟨ a, b, c, h₁, h₂ ⟩;
            have h_step : ((F_2_to_Rots (FreeGroup.mk (g :: w)) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ ![0, 1, 0]) = ((if g.2 then (fin_2_to_rots g.1 : Matrix (Fin 3) (Fin 3) ℝ) else ((fin_2_to_rots g.1)⁻¹ : Matrix (Fin 3) (Fin 3) ℝ)) *ᵥ ![a * Real.sqrt 2, b, c * Real.sqrt 2]) / 3^w.length := by
              convert congr_arg ( fun x : Fin 3 → ℝ => ( if g.2 = Bool.true then ( fin_2_to_rots g.1 : Matrix ( Fin 3 ) ( Fin 3 ) ℝ ) else ( fin_2_to_rots g.1 : Matrix ( Fin 3 ) ( Fin 3 ) ℝ ) ⁻¹ ) *ᵥ x ) h₁ using 1;
              · field_simp;
                -- By definition of F_2_to_Rots, we have F_2_to_Rots (FreeGroup.mk (g :: w)) = (if g.2 then (fin_2_to_rots g.1) else (fin_2_to_rots g.1)⁻¹) * F_2_to_Rots (FreeGroup.mk w).
                have h_def : F_2_to_Rots (FreeGroup.mk (g :: w)) = (if g.2 then (fin_2_to_rots g.1) else (fin_2_to_rots g.1)⁻¹) * F_2_to_Rots (FreeGroup.mk w) := by
                  norm_num +zetaDelta at *;
                  split_ifs <;> simp_all +decide [ F_2_to_Rots ];
                split_ifs at * <;> simp_all +decide [ div_eq_mul_inv ];
                rw [ Matrix.inv_def ];
                simp +decide [ Ring.inverse ];
              · ext i; fin_cases i <;> norm_num [ Matrix.mulVec ] <;> ring;
            have h_step : ((if g.2 then (fin_2_to_rots g.1 : Matrix (Fin 3) (Fin 3) ℝ) else ((fin_2_to_rots g.1)⁻¹ : Matrix (Fin 3) (Fin 3) ℝ)) *ᵥ ![a * Real.sqrt 2, b, c * Real.sqrt 2]) = (1/3 : ℝ) • ![(next_coeffs g a b c).1 * Real.sqrt 2, (next_coeffs g a b c).2.1, (next_coeffs g a b c).2.2 * Real.sqrt 2] := by
              exact?;
            use (next_coeffs g a b c).1, (next_coeffs g a b c).2.1, (next_coeffs g a b c).2.2;
            bound;
            all_goals have := head_not_inv_of_reduced hw_reduced; simp_all +decide [ Fin.forall_fin_two ];
            · ext i; fin_cases i <;> norm_num [ pow_succ' ] <;> ring;
            · ext i; fin_cases i <;> norm_num [ pow_succ' ] <;> ring;
            · exact GoodTriple_step h₂ ( by aesop );
            · exact GoodTriple_step h₂ ( by aesop );
      contrapose! h_coeffs; aesop;
      rw [ ← List.ofFn_inj ] at * ; aesop;
      rw [ inv_mul_eq_div, eq_div_iff ] at * <;> norm_cast at * <;> aesop;
      cases w <;> simp_all +decide [ GoodTriple ];
      exact a_1.1 ( dvd_pow_self _ ( Nat.succ_ne_zero _ ) );
    intro w hw;
    convert h_nontrivial ( FreeGroup.toWord w ) _ _;
    · exact?;
    · contrapose! hw; aesop;
    · exact?;
  bound;
  simp +zetaDelta at *;
  exact Classical.not_not.1 fun h => h_nontrivial w h <| by simpa [ ← Matrix.one_fin_three ] using congr_arg ( fun x : Free_Rots => ( x : Matrix ( Fin 3 ) ( Fin 3 ) ℝ ) ) a;

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

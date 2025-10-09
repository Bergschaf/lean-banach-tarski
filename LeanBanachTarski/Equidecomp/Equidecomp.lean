import Mathlib.Algebra.Group.Action.Equidecomp
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Logic.Equiv.PartialEquiv
import Mathlib.Order.Partition.Finpartition

open Function Set Pointwise PartialEquiv

namespace Equidecomp

variable {X : Type*} {G : Type*} [Group G] [MulAction G X]

/--
An Equipartition contains a Finset of parts.
Each part has a source, a group element and a target.
The sources and targets of every part are supremum independent (and not empty), which ensures that
they form a `Finpartition` of the source and target of the whole Equipartition.
`decomp` ensures that applying the group element of a part to its source gives the target.
This definition is equivalent to the one given at `Equidecomp`, but it is more useful for
constructing concrete Equidecompositions.
-/
structure Equipartition (X : Type*) (G : Type*) [SMul G X] where
  /-- The parts of the Equipartition, consisting of source, group element, and target. -/
  parts : Finset (Set X × G × Set X)
  /-- The supremum independent property of the sources of the parts. -/
  supIndepSource : Finset.SupIndep parts (fun p ↦ p.1)
  /-- The supremum independent property of the targets of the parts. -/
  supIndepTarget : Finset.SupIndep parts (fun p ↦ p.2.2)
  /-- The sources of the parts are not empty. -/
  bot_notMem : ∀ p ∈ parts, p.1 ≠ ∅
  /-- Applying the group element of a part to its source gives the target. -/
  decomp : ∀ p ∈ parts, (fun x ↦ p.2.1 • x) '' p.1 = p.2.2

namespace Equipartition

variable (P : Equipartition X G)

/--
The source of the Equipartition, defined as the union of the source of all parts.
-/
def source := P.parts.sup (fun p ↦ p.1)

/--
The target of the Equipartition, defined as the union of the target of all parts.
-/
def target := P.parts.sup (fun p ↦ p.2.2)

theorem subset_source (p : Set X × G × Set X) (h : p ∈ P.parts) : p.1 ⊆ P.source := by
  simpa [source] using subset_biUnion_of_mem h

theorem subset_target (p : Set X × G × Set X) (h : p ∈ P.parts) : p.2.2 ⊆ P.target := by
  simp only [target, Finset.sup_set_eq_biUnion]
  exact subset_iUnion₂_of_subset p h fun ⦃a⦄ a ↦ a

/--
The sources of each part form a `Finpartition` of `source`.
-/
def source.to_finpartition [DecidableEq (Set X)] (P : Equipartition X G) : Finpartition P.source :=
  { parts := Finset.image (fun p ↦ p.1) P.parts
    sup_parts := by simp [source]
    supIndep := by exact Finset.SupIndep.image P.supIndepSource
    bot_notMem := by
      simp only [bot_eq_empty, Finset.mem_image, Prod.exists, exists_and_right, exists_eq_right,
        not_exists]
      refine fun x y ↦ Finset.forall_mem_not_eq'.mp (fun b h ↦ ?_)
      simp [@Prod.eq_iff_fst_eq_snd_eq, P.bot_notMem b h]}

/--
The targets of each part form a `Finpartition` of `target`.
-/
def target.to_finpartition [DecidableEq (Set X)] (P : Equipartition X G) :
    Finpartition P.target :=
  { parts := Finset.image (fun p ↦ p.2.2) P.parts
    sup_parts := by simp [target]
    supIndep := by exact Finset.SupIndep.image P.supIndepTarget
    bot_notMem := by
      simp only [bot_eq_empty, Finset.mem_image, Prod.exists, exists_eq_right, not_exists]
      refine fun x y ↦ Finset.forall_mem_not_eq'.mp (fun b h ↦ ?_)
      exact ne_of_apply_ne (fun b ↦ b.2.2) (by simp [← P.decomp b h, P.bot_notMem b h])}

theorem parts_eq_iff_1 {p1 p2 : Set X × G × Set X} (h1 : p1 ∈ P.parts) (h2 : p2 ∈ P.parts) :
    p1 = p2 ↔ p1.1 = p2.1 := by
  refine Iff.intro (by simp +contextual) (fun h3 ↦ ?_)
  have h4 := Finset.SupIndep.pairwiseDisjoint P.supIndepSource
  by_contra hC
  simp only [PairwiseDisjoint, Set.Pairwise, Finset.mem_coe, ne_eq, Prod.forall, Prod.mk.injEq,
    not_and] at h4
  have h5 := @h4 p1.1 p1.2.1 p1.2.2 h1 p2.1 p2.2.1 p2.2.2 h2 (by grind)
  simp only [h3, Prod.mk.eta, disjoint_self, bot_eq_empty, P.bot_notMem p2 h2] at h5

theorem parts_eq_iff_2 {p1 p2 : Set X × G × Set X} (h1 : p1 ∈ P.parts) (h2 : p2 ∈ P.parts) :
    p1 = p2 ↔ p1.2.2 = p2.2.2 := by
  refine Iff.intro (by simp +contextual) (fun h3 ↦ ?_)
  have h4 := Finset.SupIndep.pairwiseDisjoint P.supIndepTarget
  by_contra hC
  simp only [PairwiseDisjoint, Set.Pairwise, Finset.mem_coe, ne_eq, Prod.forall, Prod.mk.injEq,
    not_and] at h4
  have h5 := @h4 p1.1 p1.2.1 p1.2.2 h1 p2.1 p2.2.1 p2.2.2 h2 (by grind)
  simp only [h3, ← P.decomp _ h2, image_smul, disjoint_self, bot_eq_empty, smul_set_eq_empty,
    P.bot_notMem p2 h2] at h5

/--
The piece of the partition containing `x`, the group element associated to that piece,
and the image of that piece under the group element.
-/
noncomputable def source_part (x : X) (h : x ∈ P.source) : Set X × G × Set X := by
  have h1 : ∃ p ∈ P.parts, x ∈ p.1 := by simp [source, mem_iUnion] at h ⊢; assumption
  exact Classical.choose h1

theorem source_part_spec (x : X) (h : x ∈ P.source) : x ∈ (P.source_part x h).1 := by
  rw [Equipartition.source_part]
  have h1 : ∃ p ∈ P.parts, x ∈ p.1 := by simp [source, mem_iUnion] at h ⊢; assumption
  exact (Classical.choose_spec h1).2


theorem source_part_mem_parts (x : X) (h : x ∈ P.source) : (P.source_part x h) ∈ P.parts := by
  rw [Equipartition.source_part]
  have h1 : ∃ p ∈ P.parts, x ∈ p.1 := by simp [source, mem_iUnion] at h ⊢; assumption
  exact (Classical.choose_spec h1).1

theorem source_part_decomp (x : X) (h : x ∈ P.source) :
      (P.source_part x h).2.1 • x ∈ (P.source_part x h).2.2 := by
  simp only [← P.decomp (P.source_part x h) (P.source_part_mem_parts x h), image_smul,
    mem_smul_set]
  use x
  simpa using source_part_spec P x h

/--
The piece of the partition whose image contains `x`, the group element associated to that piece,
and the image of that piece under the group element.
-/
noncomputable def target_part (x : X) (h : x ∈ P.target) : Set X × G × Set X := by
  have h1 : ∃ p ∈ P.parts, x ∈ p.2.2 := by
    simp [Equipartition.target, mem_iUnion] at h ⊢; assumption
  exact Classical.choose h1

theorem target_part_spec (x : X) (h : x ∈ P.target) : x ∈ (P.target_part x h).2.2 := by
  rw [Equipartition.target_part]
  have h1 : ∃ p ∈ P.parts, x ∈ p.2.2 := by
    simp [Equipartition.target, mem_iUnion] at h ⊢; assumption
  exact (Classical.choose_spec h1).2

theorem target_part_mem_parts (x : X) (h : x ∈ P.target) : (P.target_part x h) ∈ P.parts := by
  rw [Equipartition.target_part]
  have h1 : ∃ p ∈ P.parts, x ∈ p.2.2 := by
      simp [Equipartition.target, mem_iUnion] at h ⊢; assumption
  exact (Classical.choose_spec h1).1

theorem decomp_inv (x : X) (h : x ∈ P.target) :
    ∃ y ∈ (P.target_part x h).1, (P.target_part x h).2.1 • y = x := by
  let h1 := P.decomp (P.target_part x h) <| Equipartition.target_part_mem_parts P x h
  simp [Set.ext_iff] at h1
  rw [← @mem_smul_set]
  exact (h1 x).mpr <| Equipartition.target_part_spec P x h

theorem target_part_decomp (x : X) (h : x ∈ P.target) :
    (P.target_part x h).2.1⁻¹ • x ∈ (P.target_part x h).1 := by
  rcases P.decomp_inv x h with ⟨y,⟨h1, h2⟩⟩
  have h3 :  (P.target_part x h).2.1⁻¹ • x =
    (P.target_part x h).2.1⁻¹ • (P.target_part x h).2.1 • y := by
    rw [h2]

  simpa [h3] using h1

theorem part_eq_target_part_iff_mem (x : X) (hx : x ∈ P.target) (part : Set X × G × Set X)
    (hp : part ∈ P.parts) : x ∈ part.2.2 ↔ P.target_part x hx = part := by
  constructor
  · intro h
    rw [P.parts_eq_iff_2 (target_part_mem_parts P x hx) hp]
    by_contra h1
    have h2 := Finset.SupIndep.pairwiseDisjoint P.supIndepTarget
    simp [PairwiseDisjoint, Set.Pairwise] at h2
    have h2 := h2 part.1 part.2.1 part.2.2 hp (P.target_part x hx).1 (P.target_part x hx).2.1
            (P.target_part x hx).2.2 (by simpa using target_part_mem_parts P x hx) (by grind)
    simp only [Prod.mk.eta, Disjoint, le_eq_subset, bot_eq_empty, subset_empty_iff] at h2
    have h2 := @h2 {x} (by simp [h]) (by simpa using target_part_spec P x hx)
    simp at h2
  · intro h
    rw [← h]
    exact target_part_spec P x hx

theorem part_eq_source_part_iff_mem (x : X) (hx : x ∈ P.source) (part : Set X × G × Set X)
    (hp : part ∈ P.parts) : x ∈ part.1 ↔ P.source_part x hx = part := by
  constructor
  · intro h
    rw [P.parts_eq_iff_2 (source_part_mem_parts P x hx) hp]
    by_contra h1
    have h2 := Finset.SupIndep.pairwiseDisjoint P.supIndepSource
    simp only [PairwiseDisjoint, Set.Pairwise, Finset.mem_coe, ne_eq, Prod.forall, Prod.mk.injEq,
      not_and] at h2
    have h2 := h2 part.1 part.2.1 part.2.2 hp (P.source_part x hx).1 (P.source_part x hx).2.1
            (P.source_part x hx).2.2 (by simpa using source_part_mem_parts P x hx) (by grind)
    have h2 := @h2 {x} (by simp [h]) (by simpa using source_part_spec P x hx)
    simp at h2
  · intro h
    rw [← h]
    exact source_part_spec P x hx

theorem source_part_eq_target_part (x : X) (h : x ∈ P.source) :
    P.source_part x h = P.target_part ((P.source_part x h).2.1 • x) (mem_of_subset_of_mem
      (P.subset_target (P.source_part x h) (source_part_mem_parts P x h))
          (source_part_decomp P x h)) := by
  let s := P.source_part x h
  have h_target : s.2.1 • x ∈ P.target := by
    apply mem_of_subset_of_mem (P.subset_target s (source_part_mem_parts P x h))
        (source_part_decomp P x h)
  have eq_iff := P.part_eq_target_part_iff_mem _ h_target s (source_part_mem_parts P x h)
  exact (eq_iff.mp (source_part_decomp P x h)).symm

theorem target_part_eq_source_part (x : X) (h : x ∈ P.target) :
    P.target_part x h = P.source_part ((P.target_part x h).2.1⁻¹ • x) (mem_of_subset_of_mem
      (P.subset_source (P.target_part x h) (target_part_mem_parts P x h))
          (target_part_decomp P x h)) := by
  let t := P.target_part x h
  have h_source : t.2.1⁻¹ • x ∈ P.source := by
    apply mem_of_subset_of_mem (P.subset_source t (target_part_mem_parts P x h))
        (target_part_decomp P x h)
  have eq_iff := P.part_eq_source_part_iff_mem _ h_source t (target_part_mem_parts P x h)
  exact (eq_iff.mp (target_part_decomp P x h)).symm

/--
The Equidecomposition associated with an Equipartition.
-/
noncomputable def to_equidecomp : Equidecomp X G where
  toFun x := by classical exact
    if h : x ∉ P.source then x else (P.source_part x (not_notMem.mp h)).2.1 • x
  invFun x := by classical exact
    if h : x ∉ P.target then x else (P.target_part x (not_notMem.mp h)).2.1⁻¹ • x
  source := P.source
  target := P.target
  map_source' x hx := by simpa [hx] using (mem_of_subset_of_mem (P.subset_target
    (P.source_part x hx) (source_part_mem_parts P x hx)) (source_part_decomp P x hx))
  map_target' x hx := by
    simpa [hx] using (mem_of_subset_of_mem  (P.subset_source (P.target_part x hx)
       (target_part_mem_parts P x hx)) (target_part_decomp P x hx))
  left_inv' x hx := by
    have h1 : (P.source_part x (not_notMem.mp (of_eq_false (Eq.trans (congrArg Not (eq_true hx))
        not_true_eq_false)) )).2.1 • x ∈ P.target := by
      refine mem_of_subset_of_mem ?_ (P.source_part_decomp x hx)
      exact P.subset_target _ (source_part_mem_parts P x hx)
    simp [hx, h1, ↓reduceDIte, ← P.source_part_eq_target_part x hx, inv_smul_smul]
  right_inv' x hx := by
    have h1 : (P.target_part x (not_notMem.mp (of_eq_false (Eq.trans (congrArg Not (eq_true hx))
        not_true_eq_false)))).2.1⁻¹ • x ∈ P.source := by
      refine mem_of_subset_of_mem ?_ (P.target_part_decomp x hx)
      exact P.subset_source _ (target_part_mem_parts P x hx)
    simp [← P.target_part_eq_source_part x hx, smul_inv_smul, h1, hx]
  isDecompOn' := by
    classical use Finset.image (fun p ↦ p.2.1) P.parts
    intro x hx
    use (P.source_part x hx).2.1
    constructor
    · simp only [Finset.mem_image, Prod.exists, exists_and_right, exists_eq_right]
      use (P.source_part x hx).1
      use (P.source_part x hx).2.2
      exact source_part_mem_parts P x hx
    · simp [hx]

theorem to_equidecomp_source (P : Equipartition X G) :
    (P.to_equidecomp).source = P.source := rfl

theorem to_equidecomp_target (P : Equipartition X G) :
    (P.to_equidecomp).target = P.target := rfl

end Equipartition

/--
Chooses the group element that is applied to a certain `x` in the source of f.
-/
noncomputable def source_witness (f : Equidecomp X G) {x : X} (h : x ∈ f.source) : G :=
  (f.isDecompOn x h).choose

theorem source_witness_spec (f : Equidecomp X G) {x : X} (h : x ∈ f.source) :
  f.source_witness h ∈ f.witness ∧ f x = f.source_witness h • x := (f.isDecompOn x h).choose_spec

/--
Chooses the group element which was used to send an element of the source to `y`.
-/
noncomputable def target_witness (f : Equidecomp X G) {y : X} (h : y ∈ f.target) : G :=
  f.source_witness (f.map_target' h)

theorem target_witness_spec (f : Equidecomp X G) {y : X} (h : y ∈ f.target) :
  f.target_witness h ∈ f.witness ∧ y = f.target_witness h • (f.invFun y):= by
  rw [target_witness, source_witness]
  have h1 := (f.isDecompOn (f.invFun y) (f.map_target' h)).choose_spec
  have h2 : f (f.invFun y) = y := by
    rw [f.right_inv' h]
  grind


open scoped Classical in
/--
All witnesses that are actually used to send some element of the source to the target.
-/
noncomputable def minimal_witness (f : Equidecomp X G) : Finset G :=
  {w ∈ f.witness | ∃ a, ∃ h, @f.source_witness _ _ _ _ a h = w}

/--
Constructs an `Equipartition` from an `Equidecomp`.
-/
noncomputable def to_equipartition (f : Equidecomp X G) : Equipartition X G where
  parts := by classical exact Finset.image (fun g ↦
    ({x : X | if h : x ∈ f.source then f.source_witness h = g else false},g,
     {y : X | if h : y ∈ f.target then f.target_witness h = g else false})) f.minimal_witness
  bot_notMem p h := by
    simp only [Bool.false_eq_true, dite_else_false, Finset.mem_image] at h
    rcases h with ⟨g, ⟨hg, h⟩⟩
    subst h
    simp only [minimal_witness, Finset.mem_filter, ne_eq, eq_empty_iff_forall_notMem, mem_setOf_eq,
      not_exists, not_forall, not_not] at hg ⊢
    grind
  decomp p hp := by
    simp only [Bool.false_eq_true, dite_else_false, Finset.mem_image] at hp
    rcases hp with ⟨g, ⟨hg, hp⟩⟩
    subst hp
    apply le_antisymm
    · simp only [image_smul, target_witness, invFun_as_coe, le_eq_subset, subset_setOf,
      mem_smul_set, mem_setOf_eq, forall_exists_index, and_imp]
      intro x1 x2 h1 h2 h3
      subst h2
      rw [← (f.source_witness_spec h1).2] at h3
      have h5 : x1 ∈ f.target := by
        rw [← h3]
        exact f.map_source' h1
      apply_fun f.invFun at h3
      rw [f.left_inv' h1] at h3
      simp [h3, h5]
    · simp only [target_witness, invFun_as_coe, image_smul, le_eq_subset, setOf_subset,
      mem_smul_set, mem_setOf_eq, forall_exists_index]
      intro x1 hx1 h1
      use f.invFun x1
      subst h1
      simp only [invFun_as_coe, exists_prop, and_true]
      refine And.intro (PartialEquiv.map_target f.toPartialEquiv hx1) ?_
      have h4 := (f.source_witness_spec (id (Eq.refl (f.symm x1)) ▸ target_witness._proof_1 f
        (Eq.mpr_prop (Eq.refl (x1 ∈ f.target)) ((Iff.of_eq (Eq.refl (x1 ∈ f.target))).mpr hx1))
        : f.symm x1 ∈ f.source)).2
      simp_rw [symm_toPartialEquiv] at h4
      rw [← h4, right_inv hx1]
  supIndepSource s h1 p h2 := by
    simp_all only [Bool.false_eq_true, dite_else_false, Finset.mem_image, Finset.sup_set_eq_biUnion,
      disjoint_iUnion_right, Prod.forall]
    intro h3 p_1 p_2 p_3 h4
    classical rw [Finset.subset_image_iff] at h1
    rcases h1 with ⟨s', ⟨h1, h5⟩⟩
    rcases h2 with ⟨g', ⟨hg, h2⟩⟩
    rw [← h5] at h4
    simp only [Finset.mem_image, Prod.mk.injEq, existsAndEq, true_and] at h4
    rcases h4 with ⟨h4_1, ⟨h4_2, h4_3⟩⟩
    simp only [← h2, ← h4_2, Set.disjoint_iff, inter_setOf_eq_sep, mem_setOf_eq, subset_empty_iff,
      eq_empty_iff_forall_notMem, not_and, not_exists, forall_exists_index]
    have h : g' ∉ s' := by grind
    grind
  supIndepTarget s h1 p h2 hp := by
    simp_all only [Bool.false_eq_true, dite_else_false, Finset.mem_image, Finset.sup_set_eq_biUnion,
      disjoint_iUnion_right, Prod.forall]
    intro s' g' b' hA'
    rcases h2 with ⟨g,⟨hg, hpg⟩⟩
    simp only [← hpg, Finset.subset_image_iff] at h1 ⊢
    rcases h1 with ⟨s_g, ⟨h_s_g, h_s_g_s⟩⟩
    rw [← h_s_g_s] at hA'
    simp only [Finset.mem_image, Prod.mk.injEq, existsAndEq, true_and] at hA'
    rcases hA' with ⟨hg', ⟨hs', hb'⟩⟩
    simp only [← hb', Set.disjoint_iff, subset_empty_iff, eq_empty_iff_forall_notMem, mem_inter_iff,
      mem_setOf_eq, not_and, not_exists, forall_exists_index]
    intro x hx hg_ _
    rw [hg_]
    have h : g ∉ s_g := by grind
    grind

theorem to_equipartition_source (f : Equidecomp X G) :
    (f.to_equipartition).source = f.source := by
  ext i
  simp only [Equipartition.source, to_equipartition, Bool.false_eq_true, dite_else_false,
    minimal_witness, Finset.sup_image, Finset.sup_set_eq_biUnion, Finset.mem_filter, comp_apply,
    mem_iUnion, mem_setOf_eq, exists_prop]
  refine Iff.intro (by grind) (fun h ↦ ?_)
  use f.source_witness h
  simpa [h] using And.intro (f.source_witness_spec h).1 (by grind)

end Equidecomp

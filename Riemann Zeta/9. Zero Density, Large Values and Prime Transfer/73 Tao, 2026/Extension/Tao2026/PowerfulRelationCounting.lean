import Tao2026.QuadraticSolutionCount

/-!
# Sharp counting of powerful linear relations

This module implements Tao's Corollary 2.11 after the exact representation
and Lemma 2.10 modules.  The first layer is the literal four-parameter
dyadic decomposition of the unique square-times-squarefree-cube
representations.
-/

namespace Tao2026

open Filter Asymptotics

/-- The four base-two scale indices `(n₁,n₂,m₁,m₂)` of a pair of canonical
powerful-number representations. -/
def powerfulRelationDyadicIndex
    (rs : (Σ _cubeBase : ℕ, ℕ) × (Σ _cubeBase : ℕ, ℕ)) :
    (ℕ × ℕ) × (ℕ × ℕ) :=
  ((Nat.log 2 rs.1.2, Nat.log 2 rs.1.1),
    (Nat.log 2 rs.2.2, Nat.log 2 rs.2.1))

/-- One exact four-variable dyadic fiber of the powerful relation
representation set. -/
noncomputable def powerfulRelationDyadicBlock
    (a b h x : ℕ) (q : (ℕ × ℕ) × (ℕ × ℕ)) :
    Finset ((Σ _cubeBase : ℕ, ℕ) × (Σ _cubeBase : ℕ, ℕ)) := by
  classical
  exact (powerfulRelationRepresentationsUpTo a b h x).filter fun rs =>
    powerfulRelationDyadicIndex rs = q

theorem mem_powerfulRelationDyadicBlock
    {a b h x : ℕ} {q : (ℕ × ℕ) × (ℕ × ℕ)}
    {rs : (Σ _cubeBase : ℕ, ℕ) × (Σ _cubeBase : ℕ, ℕ)} :
    rs ∈ powerfulRelationDyadicBlock a b h x q ↔
      rs ∈ powerfulRelationRepresentationsUpTo a b h x ∧
        powerfulRelationDyadicIndex rs = q := by
  classical
  simp [powerfulRelationDyadicBlock]

/-- The finite set of realized dyadic scale quadruples. -/
noncomputable def powerfulRelationDyadicIndices
    (a b h x : ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (powerfulRelationRepresentationsUpTo a b h x).image
    powerfulRelationDyadicIndex

/-- Exact fiberwise partition of the representation count. -/
theorem card_powerfulRelationRepresentationsUpTo_eq_sum_dyadicBlocks
    (a b h x : ℕ) :
    (powerfulRelationRepresentationsUpTo a b h x).card =
      ∑ q ∈ powerfulRelationDyadicIndices a b h x,
        (powerfulRelationDyadicBlock a b h x q).card := by
  classical
  rw [powerfulRelationDyadicIndices,
    Finset.card_eq_sum_card_image powerfulRelationDyadicIndex
      (powerfulRelationRepresentationsUpTo a b h x)]
  apply Finset.sum_congr rfl
  intro q _hq
  congr 1

/-- Every positive integer lies between its lower base-two scale and the
next power of two. -/
theorem two_pow_log_bounds {n : ℕ} (hn : 0 < n) :
    2 ^ Nat.log 2 n ≤ n ∧ n < 2 ^ (Nat.log 2 n + 1) := by
  exact ⟨Nat.pow_log_le_self 2 hn.ne', by
    simpa only [Nat.succ_eq_add_one] using
      Nat.lt_pow_succ_log_self (by omega : 1 < 2) n⟩

/-- Coordinate bounds furnished by membership in one realized dyadic
block. -/
theorem powerfulRelationDyadicBlock_coordinate_bounds
    {a b h x : ℕ} {q : (ℕ × ℕ) × (ℕ × ℕ)}
    {rs : (Σ _cubeBase : ℕ, ℕ) × (Σ _cubeBase : ℕ, ℕ)}
    (hrs : rs ∈ powerfulRelationDyadicBlock a b h x q) :
    (2 ^ q.1.1 ≤ rs.1.2 ∧ rs.1.2 < 2 ^ (q.1.1 + 1)) ∧
      (2 ^ q.1.2 ≤ rs.1.1 ∧ rs.1.1 < 2 ^ (q.1.2 + 1)) ∧
      (2 ^ q.2.1 ≤ rs.2.2 ∧ rs.2.2 < 2 ^ (q.2.1 + 1)) ∧
      (2 ^ q.2.2 ≤ rs.2.1 ∧ rs.2.1 < 2 ^ (q.2.2 + 1)) := by
  have hrs' := mem_powerfulRelationDyadicBlock.mp hrs
  have hrep := mem_powerfulRelationRepresentationsUpTo_iff.mp hrs'.1
  have hn := mem_powerfulOneTermRepresentations_iff.mp hrep.1
  have hm := mem_powerfulOneTermRepresentations_iff.mp hrep.2.1
  have hidx := hrs'.2
  simp only [powerfulRelationDyadicIndex] at hidx
  rcases Prod.ext_iff.mp hidx with ⟨hnidx, hmidx⟩
  rcases Prod.ext_iff.mp hnidx with ⟨hn1idx, hn2idx⟩
  rcases Prod.ext_iff.mp hmidx with ⟨hm1idx, hm2idx⟩
  simp only at hn1idx hn2idx hm1idx hm2idx
  subst q
  exact ⟨two_pow_log_bounds hn.2.2.2.1,
    two_pow_log_bounds hn.1,
    two_pow_log_bounds hm.2.2.2.1,
    two_pow_log_bounds hm.1⟩

/-- A rectangular finite family containing every possible dyadic index. -/
def powerfulRelationDyadicIndexBox (z : ℕ) :
    Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  ((Finset.range (Nat.log 2 z + 1)).product
      (Finset.range (Nat.log 2 z + 1))).product
    ((Finset.range (Nat.log 2 z + 1)).product
      (Finset.range (Nat.log 2 z + 1)))

theorem powerfulRelationDyadicIndices_subset_indexBox
    (a b h x : ℕ) :
    powerfulRelationDyadicIndices a b h x ⊆
      powerfulRelationDyadicIndexBox (x + h) := by
  classical
  intro q hq
  rw [powerfulRelationDyadicIndices, Finset.mem_image] at hq
  rcases hq with ⟨rs, hrs, rfl⟩
  have hrep := mem_powerfulRelationRepresentationsUpTo_iff.mp hrs
  have hn := mem_powerfulOneTermRepresentations_iff.mp hrep.1
  have hm := mem_powerfulOneTermRepresentations_iff.mp hrep.2.1
  have hn1le : rs.1.2 ≤ x + h := by
    exact (hn.2.2.2.2.trans (Nat.sqrt_le_self _)).trans
      ((Nat.div_le_self _ _).trans (Nat.le_add_right _ _))
  have hn2le : rs.1.1 ≤ x + h := hn.2.1.trans (Nat.le_add_right _ _)
  have hm1le : rs.2.2 ≤ x + h :=
    hm.2.2.2.2.trans (Nat.sqrt_le_self _ |>.trans (Nat.div_le_self _ _))
  have hm2le : rs.2.1 ≤ x + h := hm.2.1
  unfold powerfulRelationDyadicIndexBox powerfulRelationDyadicIndex
  exact Finset.mk_mem_product
    (Finset.mk_mem_product
      (Finset.mem_range.mpr
        (Nat.lt_succ_of_le (Nat.log_mono_right hn1le)))
      (Finset.mem_range.mpr
        (Nat.lt_succ_of_le (Nat.log_mono_right hn2le))))
    (Finset.mk_mem_product
      (Finset.mem_range.mpr
        (Nat.lt_succ_of_le (Nat.log_mono_right hm1le)))
      (Finset.mem_range.mpr
        (Nat.lt_succ_of_le (Nat.log_mono_right hm2le))))

theorem card_powerfulRelationDyadicIndices_le
    (a b h x : ℕ) :
    (powerfulRelationDyadicIndices a b h x).card ≤
      (Nat.log 2 (x + h) + 1) ^ 4 := by
  calc
    (powerfulRelationDyadicIndices a b h x).card ≤
        (powerfulRelationDyadicIndexBox (x + h)).card :=
      Finset.card_le_card
        (powerfulRelationDyadicIndices_subset_indexBox a b h x)
    _ = (Nat.log 2 (x + h) + 1) ^ 4 := by
      simp [powerfulRelationDyadicIndexBox]
      ring

/-! ## The two coordinate bounds on a dyadic block -/

private theorem injOn_powerfulRelationDyadicBlock_leftCoordinates
    {a b h x : ℕ} {q : (ℕ × ℕ) × (ℕ × ℕ)} (hb : 0 < b) :
    Set.InjOn
      (fun rs : (Σ _cubeBase : ℕ, ℕ) × (Σ _cubeBase : ℕ, ℕ) =>
        (rs.1.2, rs.1.1))
      (powerfulRelationDyadicBlock a b h x q) := by
  rintro ⟨r₁, s₁⟩ hrs₁ ⟨r₂, s₂⟩ hrs₂ heq
  have hrCube : r₁.1 = r₂.1 := congrArg Prod.snd heq
  have hrSquare : r₁.2 = r₂.2 := congrArg Prod.fst heq
  have hr : r₁ = r₂ := Sigma.ext hrCube (heq_of_eq hrSquare)
  subst r₂
  have hrs₁' := mem_powerfulRelationDyadicBlock.mp hrs₁
  have hrs₂' := mem_powerfulRelationDyadicBlock.mp hrs₂
  have hrep₁ := mem_powerfulRelationRepresentationsUpTo_iff.mp hrs₁'.1
  have hrep₂ := mem_powerfulRelationRepresentationsUpTo_iff.mp hrs₂'.1
  have hsValue : powerfulOneTermRepresentationValue s₁ =
      powerfulOneTermRepresentationValue s₂ := by
    apply Nat.mul_left_cancel hb
    calc
      b * powerfulOneTermRepresentationValue s₁ =
          a * powerfulOneTermRepresentationValue r₁ + h :=
        hrep₁.2.2.1.symm
      _ = b * powerfulOneTermRepresentationValue s₂ :=
        hrep₂.2.2.1
  have hs : s₁ = s₂ :=
    injOn_powerfulOneTermRepresentationValue (x + h)
      hrep₁.2.1 hrep₂.2.1 hsValue
  subst s₂
  rfl

private theorem injOn_powerfulRelationDyadicBlock_rightCoordinates
    {a b h x : ℕ} {q : (ℕ × ℕ) × (ℕ × ℕ)} (ha : 0 < a) :
    Set.InjOn
      (fun rs : (Σ _cubeBase : ℕ, ℕ) × (Σ _cubeBase : ℕ, ℕ) =>
        (rs.2.2, rs.2.1))
      (powerfulRelationDyadicBlock a b h x q) := by
  rintro ⟨r₁, s₁⟩ hrs₁ ⟨r₂, s₂⟩ hrs₂ heq
  have hsCube : s₁.1 = s₂.1 := congrArg Prod.snd heq
  have hsSquare : s₁.2 = s₂.2 := congrArg Prod.fst heq
  have hs : s₁ = s₂ := Sigma.ext hsCube (heq_of_eq hsSquare)
  subst s₂
  have hrs₁' := mem_powerfulRelationDyadicBlock.mp hrs₁
  have hrs₂' := mem_powerfulRelationDyadicBlock.mp hrs₂
  have hrep₁ := mem_powerfulRelationRepresentationsUpTo_iff.mp hrs₁'.1
  have hrep₂ := mem_powerfulRelationRepresentationsUpTo_iff.mp hrs₂'.1
  have hrValue : powerfulOneTermRepresentationValue r₁ =
      powerfulOneTermRepresentationValue r₂ := by
    apply Nat.mul_left_cancel ha
    exact Nat.add_right_cancel
      (hrep₁.2.2.1.trans hrep₂.2.2.1.symm)
  have hr : r₁ = r₂ :=
    injOn_powerfulOneTermRepresentationValue x
      hrep₁.1 hrep₂.1 hrValue
  subst r₂
  rfl

/-- Fixing the two left representation coordinates determines the right
representation.  This is the first of Tao's three dyadic-block estimates. -/
theorem card_powerfulRelationDyadicBlock_le_left
    {a b h x : ℕ} (q : (ℕ × ℕ) × (ℕ × ℕ)) (hb : 0 < b) :
    (powerfulRelationDyadicBlock a b h x q).card ≤
      2 ^ (q.1.1 + 1) * 2 ^ (q.1.2 + 1) := by
  classical
  let f := fun rs : (Σ _cubeBase : ℕ, ℕ) × (Σ _cubeBase : ℕ, ℕ) =>
    (rs.1.2, rs.1.1)
  have hsubset : (powerfulRelationDyadicBlock a b h x q).image f ⊆
      (Finset.range (2 ^ (q.1.1 + 1))).product
        (Finset.range (2 ^ (q.1.2 + 1))) := by
    intro nm hnm
    rw [Finset.mem_image] at hnm
    rcases hnm with ⟨rs, hrs, rfl⟩
    have hc := powerfulRelationDyadicBlock_coordinate_bounds hrs
    exact Finset.mk_mem_product
      (Finset.mem_range.mpr hc.1.2)
      (Finset.mem_range.mpr hc.2.1.2)
  calc
    (powerfulRelationDyadicBlock a b h x q).card =
        ((powerfulRelationDyadicBlock a b h x q).image f).card :=
      (Finset.card_image_iff.mpr
        (injOn_powerfulRelationDyadicBlock_leftCoordinates hb)).symm
    _ ≤ ((Finset.range (2 ^ (q.1.1 + 1))).product
          (Finset.range (2 ^ (q.1.2 + 1)))).card :=
      Finset.card_le_card hsubset
    _ = 2 ^ (q.1.1 + 1) * 2 ^ (q.1.2 + 1) := by simp

/-- Fixing the two right representation coordinates determines the left
representation.  This is the second of Tao's three dyadic-block estimates. -/
theorem card_powerfulRelationDyadicBlock_le_right
    {a b h x : ℕ} (q : (ℕ × ℕ) × (ℕ × ℕ)) (ha : 0 < a) :
    (powerfulRelationDyadicBlock a b h x q).card ≤
      2 ^ (q.2.1 + 1) * 2 ^ (q.2.2 + 1) := by
  classical
  let f := fun rs : (Σ _cubeBase : ℕ, ℕ) × (Σ _cubeBase : ℕ, ℕ) =>
    (rs.2.2, rs.2.1)
  have hsubset : (powerfulRelationDyadicBlock a b h x q).image f ⊆
      (Finset.range (2 ^ (q.2.1 + 1))).product
        (Finset.range (2 ^ (q.2.2 + 1))) := by
    intro nm hnm
    rw [Finset.mem_image] at hnm
    rcases hnm with ⟨rs, hrs, rfl⟩
    have hc := powerfulRelationDyadicBlock_coordinate_bounds hrs
    exact Finset.mk_mem_product
      (Finset.mem_range.mpr hc.2.2.1.2)
      (Finset.mem_range.mpr hc.2.2.2.2)
  calc
    (powerfulRelationDyadicBlock a b h x q).card =
        ((powerfulRelationDyadicBlock a b h x q).image f).card :=
      (Finset.card_image_iff.mpr
        (injOn_powerfulRelationDyadicBlock_rightCoordinates ha)).symm
    _ ≤ ((Finset.range (2 ^ (q.2.1 + 1))).product
          (Finset.range (2 ^ (q.2.2 + 1)))).card :=
      Finset.card_le_card hsubset
    _ = 2 ^ (q.2.1 + 1) * 2 ^ (q.2.2 + 1) := by simp

/-! ## The square-equation fiber bound -/

/-- The pair of squarefree cube bases in a represented relation. -/
def powerfulRelationCubeIndex
    (rs : (Σ _cubeBase : ℕ, ℕ) × (Σ _cubeBase : ℕ, ℕ)) : ℕ × ℕ :=
  (rs.1.1, rs.2.1)

/-- A fiber of a dyadic block after fixing the two cube bases. -/
noncomputable def powerfulRelationCubeFiber
    (a b h x : ℕ) (q : (ℕ × ℕ) × (ℕ × ℕ)) (bc : ℕ × ℕ) :
    Finset ((Σ _cubeBase : ℕ, ℕ) × (Σ _cubeBase : ℕ, ℕ)) := by
  classical
  exact (powerfulRelationDyadicBlock a b h x q).filter fun rs =>
    powerfulRelationCubeIndex rs = bc

theorem mem_powerfulRelationCubeFiber
    {a b h x : ℕ} {q : (ℕ × ℕ) × (ℕ × ℕ)} {bc : ℕ × ℕ}
    {rs : (Σ _cubeBase : ℕ, ℕ) × (Σ _cubeBase : ℕ, ℕ)} :
    rs ∈ powerfulRelationCubeFiber a b h x q bc ↔
      rs ∈ powerfulRelationDyadicBlock a b h x q ∧
        powerfulRelationCubeIndex rs = bc := by
  classical
  simp [powerfulRelationCubeFiber]

/-- The cube-base pairs realized in one dyadic block. -/
noncomputable def powerfulRelationCubeIndices
    (a b h x : ℕ) (q : (ℕ × ℕ) × (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  (powerfulRelationDyadicBlock a b h x q).image powerfulRelationCubeIndex

theorem card_powerfulRelationDyadicBlock_eq_sum_cubeFibers
    (a b h x : ℕ) (q : (ℕ × ℕ) × (ℕ × ℕ)) :
    (powerfulRelationDyadicBlock a b h x q).card =
      ∑ bc ∈ powerfulRelationCubeIndices a b h x q,
        (powerfulRelationCubeFiber a b h x q bc).card := by
  classical
  rw [powerfulRelationCubeIndices,
    Finset.card_eq_sum_card_image powerfulRelationCubeIndex
      (powerfulRelationDyadicBlock a b h x q)]
  apply Finset.sum_congr rfl
  intro bc _hbc
  congr 1

theorem card_powerfulRelationCubeIndices_le
    (a b h x : ℕ) (q : (ℕ × ℕ) × (ℕ × ℕ)) :
    (powerfulRelationCubeIndices a b h x q).card ≤
      2 ^ (q.1.2 + 1) * 2 ^ (q.2.2 + 1) := by
  classical
  have hsubset : powerfulRelationCubeIndices a b h x q ⊆
      (Finset.range (2 ^ (q.1.2 + 1))).product
        (Finset.range (2 ^ (q.2.2 + 1))) := by
    intro bc hbc
    rw [powerfulRelationCubeIndices, Finset.mem_image] at hbc
    rcases hbc with ⟨rs, hrs, rfl⟩
    have hc := powerfulRelationDyadicBlock_coordinate_bounds hrs
    exact Finset.mk_mem_product
      (Finset.mem_range.mpr hc.2.1.2)
      (Finset.mem_range.mpr hc.2.2.2.2)
  calc
    (powerfulRelationCubeIndices a b h x q).card ≤
        ((Finset.range (2 ^ (q.1.2 + 1))).product
          (Finset.range (2 ^ (q.2.2 + 1)))).card :=
      Finset.card_le_card hsubset
    _ = 2 ^ (q.1.2 + 1) * 2 ^ (q.2.2 + 1) := by simp

private theorem injOn_powerfulRelationCubeFiber_squareCoordinates
    {a b h x : ℕ} {q : (ℕ × ℕ) × (ℕ × ℕ)} {bc : ℕ × ℕ} :
    Set.InjOn
      (fun rs : (Σ _cubeBase : ℕ, ℕ) × (Σ _cubeBase : ℕ, ℕ) =>
        (rs.1.2, rs.2.2))
      (powerfulRelationCubeFiber a b h x q bc) := by
  rintro ⟨r₁, s₁⟩ hrs₁ ⟨r₂, s₂⟩ hrs₂ heq
  have hcube₁ := (mem_powerfulRelationCubeFiber.mp hrs₁).2
  have hcube₂ := (mem_powerfulRelationCubeFiber.mp hrs₂).2
  have hcubes : (r₁.1, s₁.1) = (r₂.1, s₂.1) := hcube₁.trans hcube₂.symm
  have hrCube : r₁.1 = r₂.1 := congrArg Prod.fst hcubes
  have hsCube : s₁.1 = s₂.1 := congrArg Prod.snd hcubes
  have hrSquare : r₁.2 = r₂.2 := congrArg Prod.fst heq
  have hsSquare : s₁.2 = s₂.2 := congrArg Prod.snd heq
  have hr : r₁ = r₂ := Sigma.ext hrCube (heq_of_eq hrSquare)
  have hs : s₁ = s₂ := Sigma.ext hsCube (heq_of_eq hsSquare)
  exact Prod.ext hr hs

/-- Once the cube bases are fixed, the remaining square bases inject into
the literal solution set of Lemma 2.10. -/
theorem card_powerfulRelationCubeFiber_le_squareRelationSolutionsUpTo
    {a b h x : ℕ} {q : (ℕ × ℕ) × (ℕ × ℕ)} {bc : ℕ × ℕ}
    (hb : 0 < b) :
    (powerfulRelationCubeFiber a b h x q bc).card ≤
      (squareRelationSolutionsUpTo
        (a * bc.1 ^ 3) (b * bc.2 ^ 3) (h : ℤ) x).card := by
  classical
  let f := fun rs : (Σ _cubeBase : ℕ, ℕ) × (Σ _cubeBase : ℕ, ℕ) =>
    (rs.1.2, rs.2.2)
  have hsubset : (powerfulRelationCubeFiber a b h x q bc).image f ⊆
      squareRelationSolutionsUpTo
        (a * bc.1 ^ 3) (b * bc.2 ^ 3) (h : ℤ) x := by
    intro nm hnm
    rw [Finset.mem_image] at hnm
    rcases hnm with ⟨rs, hrs, rfl⟩
    have hfiber := mem_powerfulRelationCubeFiber.mp hrs
    have hrep := mem_powerfulRelationRepresentationsUpTo_iff.mp
      (mem_powerfulRelationDyadicBlock.mp hfiber.1).1
    have hn := mem_powerfulOneTermRepresentations_iff.mp hrep.1
    have hm := mem_powerfulOneTermRepresentations_iff.mp hrep.2.1
    have hbc : (rs.1.1, rs.2.1) = bc := hfiber.2
    have hnCube : rs.1.1 = bc.1 := congrArg Prod.fst hbc
    have hmCube : rs.2.1 = bc.2 := congrArg Prod.snd hbc
    have hbcPos : 0 < b * bc.2 ^ 3 := by
      rw [← hmCube]
      exact mul_pos hb (pow_pos hm.1 3)
    rw [mem_squareRelationSolutionsUpTo hbcPos]
    refine ⟨hn.2.2.2.1, ?_, hm.2.2.2.1, ?_⟩
    · exact hn.2.2.2.2.trans
        ((Nat.sqrt_le_self _).trans (Nat.div_le_self _ _))
    · norm_cast
      calc
        (a * bc.1 ^ 3) * rs.1.2 ^ 2 + h =
            a * (rs.1.2 ^ 2 * rs.1.1 ^ 3) + h := by
          rw [hnCube]
          ring
        _ = b * (rs.2.2 ^ 2 * rs.2.1 ^ 3) := by
          simpa only [powerfulOneTermRepresentationValue] using hrep.2.2.1
        _ = (b * bc.2 ^ 3) * rs.2.2 ^ 2 := by
          rw [hmCube]
          ring
  calc
    (powerfulRelationCubeFiber a b h x q bc).card =
        ((powerfulRelationCubeFiber a b h x q bc).image f).card :=
      (Finset.card_image_iff.mpr
        injOn_powerfulRelationCubeFiber_squareCoordinates).symm
    _ ≤ (squareRelationSolutionsUpTo
          (a * bc.1 ^ 3) (b * bc.2 ^ 3) (h : ℤ) x).card :=
      Finset.card_le_card hsubset

/-- Realized cube bases inherit the global size and positivity constraints
from their canonical powerful-number representations. -/
theorem powerfulRelationCubeIndex_bounds
    {a b h x : ℕ} {q : (ℕ × ℕ) × (ℕ × ℕ)} {bc : ℕ × ℕ}
    (hbc : bc ∈ powerfulRelationCubeIndices a b h x q) :
    0 < bc.1 ∧ bc.1 ≤ x ∧ 0 < bc.2 ∧ bc.2 ≤ x + h := by
  rw [powerfulRelationCubeIndices, Finset.mem_image] at hbc
  rcases hbc with ⟨rs, hrs, rfl⟩
  have hrep := mem_powerfulRelationRepresentationsUpTo_iff.mp
    (mem_powerfulRelationDyadicBlock.mp hrs).1
  have hn := mem_powerfulOneTermRepresentations_iff.mp hrep.1
  have hm := mem_powerfulOneTermRepresentations_iff.mp hrep.2.1
  exact ⟨hn.1, hn.2.1, hm.1, hm.2.1⟩

/-- Uniform Lemma 2.10 estimate on a fixed cube-base fiber.  The exponent
eight is only bookkeeping: under `a,b,h ≤ x`, both new square-equation
coefficients and the shift are bounded by `x⁸`. -/
theorem card_powerfulRelationCubeFiber_le_const_mul_rpow
    {a b h x : ℕ} {q : (ℕ × ℕ) × (ℕ × ℕ)} {bc : ℕ × ℕ}
    (ha : 0 < a) (hb : 0 < b) (hh : 0 < h) (hx : 2 ≤ x)
    (haX : a ≤ x) (hbX : b ≤ x) (hhX : h ≤ x)
    (hbc : bc ∈ powerfulRelationCubeIndices a b h x q)
    {ε : ℝ} (hε : 0 < ε) :
    ((powerfulRelationCubeFiber a b h x q bc).card : ℝ) ≤
      squareRelationPolynomialEpsilonConstant
          (ε / ((10 * 8 + 6 : ℕ) : ℝ)) *
        (x : ℝ) ^ ε := by
  have hbcBounds := powerfulRelationCubeIndex_bounds hbc
  have hxPos : 0 < x := by omega
  have hbcRight : bc.2 ≤ x ^ 2 := by
    calc
      bc.2 ≤ x + h := hbcBounds.2.2.2
      _ ≤ 2 * x := by omega
      _ ≤ x ^ 2 := by nlinarith
  have hleftCoeff : a * bc.1 ^ 3 ≤ x ^ 8 := by
    calc
      a * bc.1 ^ 3 ≤ x * x ^ 3 :=
        Nat.mul_le_mul haX (Nat.pow_le_pow_left hbcBounds.2.1 3)
      _ = x ^ 4 := by ring
      _ ≤ x ^ 8 := Nat.pow_le_pow_right hxPos (by omega)
  have hrightCoeff : b * bc.2 ^ 3 ≤ x ^ 8 := by
    calc
      b * bc.2 ^ 3 ≤ x * (x ^ 2) ^ 3 :=
        Nat.mul_le_mul hbX (Nat.pow_le_pow_left hbcRight 3)
      _ = x ^ 7 := by ring
      _ ≤ x ^ 8 := Nat.pow_le_pow_right hxPos (by omega)
  have hshift : ((h : ℤ)).natAbs ≤ x ^ 8 := by
    simpa only [Int.natAbs_natCast] using
      hhX.trans (show x ≤ x ^ 8 by
        simpa only [pow_one] using Nat.pow_le_pow_right hxPos (by omega : 1 ≤ 8))
  have hleftPos : 0 < a * bc.1 ^ 3 :=
    mul_pos ha (pow_pos hbcBounds.1 3)
  have hrightPos : 0 < b * bc.2 ^ 3 :=
    mul_pos hb (pow_pos hbcBounds.2.2.1 3)
  have hhInt : (h : ℤ) ≠ 0 := by exact_mod_cast hh.ne'
  calc
    ((powerfulRelationCubeFiber a b h x q bc).card : ℝ) ≤
        ((squareRelationSolutionsUpTo
          (a * bc.1 ^ 3) (b * bc.2 ^ 3) (h : ℤ) x).card : ℝ) := by
      exact_mod_cast
        card_powerfulRelationCubeFiber_le_squareRelationSolutionsUpTo hb
    _ ≤ squareRelationPolynomialEpsilonConstant
          (ε / ((10 * 8 + 6 : ℕ) : ℝ)) * (x : ℝ) ^ ε :=
      card_squareRelationSolutionsUpTo_le_const_mul_rpow
        hleftPos hrightPos hhInt hxPos hleftCoeff hrightCoeff hshift hε

/-- The third dyadic-block estimate: fix the two cube bases and apply the
uniform square-solution count. -/
theorem card_powerfulRelationDyadicBlock_le_cube_mul_const_mul_rpow
    {a b h x : ℕ} (q : (ℕ × ℕ) × (ℕ × ℕ))
    (ha : 0 < a) (hb : 0 < b) (hh : 0 < h) (hx : 2 ≤ x)
    (haX : a ≤ x) (hbX : b ≤ x) (hhX : h ≤ x)
    {ε : ℝ} (hε : 0 < ε) :
    ((powerfulRelationDyadicBlock a b h x q).card : ℝ) ≤
      (2 ^ (q.1.2 + 1) * 2 ^ (q.2.2 + 1) : ℕ) *
        (squareRelationPolynomialEpsilonConstant
            (ε / ((10 * 8 + 6 : ℕ) : ℝ)) *
          (x : ℝ) ^ ε) := by
  let C := squareRelationPolynomialEpsilonConstant
    (ε / ((10 * 8 + 6 : ℕ) : ℝ)) * (x : ℝ) ^ ε
  have hC : 0 ≤ C := mul_nonneg
    (squareRelationPolynomialEpsilonConstant_pos
      (div_pos hε (by positivity))).le
    (Real.rpow_nonneg (by positivity) _)
  calc
    ((powerfulRelationDyadicBlock a b h x q).card : ℝ) =
        ∑ bc ∈ powerfulRelationCubeIndices a b h x q,
          ((powerfulRelationCubeFiber a b h x q bc).card : ℝ) := by
      exact_mod_cast card_powerfulRelationDyadicBlock_eq_sum_cubeFibers a b h x q
    _ ≤ ∑ _bc ∈ powerfulRelationCubeIndices a b h x q, C := by
      apply Finset.sum_le_sum
      intro bc hbc
      exact card_powerfulRelationCubeFiber_le_const_mul_rpow
        ha hb hh hx haX hbX hhX hbc hε
    _ = ((powerfulRelationCubeIndices a b h x q).card : ℝ) * C := by
      simp
    _ ≤ (2 ^ (q.1.2 + 1) * 2 ^ (q.2.2 + 1) : ℕ) * C := by
      gcongr
      exact_mod_cast card_powerfulRelationCubeIndices_le a b h x q

/-! ## The `2/5,2/5,1/5` interpolation -/

/-- Elementary geometric interpolation behind Tao's weights
`2/5,2/5,1/5`. -/
theorem le_fifthRoot_of_le_three_bounds
    {z A B D : ℝ} (hz : 0 ≤ z) (hzA : z ≤ A) (hzB : z ≤ B)
    (hzD : z ≤ D) :
    z ≤ (A ^ 2 * B ^ 2 * D) ^ ((5 : ℝ)⁻¹) := by
  have hA : 0 ≤ A := hz.trans hzA
  have hB : 0 ≤ B := hz.trans hzB
  have hD : 0 ≤ D := hz.trans hzD
  have hpow : z ^ 5 ≤ A ^ 2 * B ^ 2 * D := by
    calc
      z ^ 5 = z * z * z * z * z := by ring
      _ ≤ A * A * B * B * D := by gcongr
      _ = A ^ 2 * B ^ 2 * D := by ring
  calc
    z = (z ^ 5) ^ ((5 : ℝ)⁻¹) :=
      (Real.pow_rpow_inv_natCast hz (by norm_num : (5 : ℕ) ≠ 0)).symm
    _ ≤ (A ^ 2 * B ^ 2 * D) ^ ((5 : ℝ)⁻¹) :=
      Real.rpow_le_rpow (by positivity) hpow (by positivity)

/-- The literal interpolation of the three proved block estimates. -/
theorem card_powerfulRelationDyadicBlock_le_interpolated
    {a b h x : ℕ} (q : (ℕ × ℕ) × (ℕ × ℕ))
    (ha : 0 < a) (hb : 0 < b) (hh : 0 < h) (hx : 2 ≤ x)
    (haX : a ≤ x) (hbX : b ≤ x) (hhX : h ≤ x)
    {ε : ℝ} (hε : 0 < ε) :
    ((powerfulRelationDyadicBlock a b h x q).card : ℝ) ≤
      (((2 ^ (q.1.1 + 1) * 2 ^ (q.1.2 + 1) : ℕ) : ℝ) ^ 2 *
        ((2 ^ (q.2.1 + 1) * 2 ^ (q.2.2 + 1) : ℕ) : ℝ) ^ 2 *
        (((2 ^ (q.1.2 + 1) * 2 ^ (q.2.2 + 1) : ℕ) : ℝ) *
          (squareRelationPolynomialEpsilonConstant
              (ε / ((10 * 8 + 6 : ℕ) : ℝ)) *
            (x : ℝ) ^ ε))) ^ ((5 : ℝ)⁻¹) := by
  apply le_fifthRoot_of_le_three_bounds (Nat.cast_nonneg _)
  · exact_mod_cast card_powerfulRelationDyadicBlock_le_left q hb
  · exact_mod_cast card_powerfulRelationDyadicBlock_le_right q ha
  · exact card_powerfulRelationDyadicBlock_le_cube_mul_const_mul_rpow
      q ha hb hh hx haX hbX hhX hε

/-- A realized dyadic block has both powerful-number scale products bounded
by the corresponding global cutoffs, with the exact factor `2⁵=32` caused
by passing from lower to upper dyadic endpoints. -/
theorem powerfulRelationDyadicBlock_scale_products
    {a b h x : ℕ} {q : (ℕ × ℕ) × (ℕ × ℕ)}
    {rs : (Σ _cubeBase : ℕ, ℕ) × (Σ _cubeBase : ℕ, ℕ)}
    (hrs : rs ∈ powerfulRelationDyadicBlock a b h x q) :
    (2 ^ (q.1.1 + 1)) ^ 2 * (2 ^ (q.1.2 + 1)) ^ 3 ≤ 32 * x ∧
      (2 ^ (q.2.1 + 1)) ^ 2 * (2 ^ (q.2.2 + 1)) ^ 3 ≤
        32 * (x + h) := by
  have hc := powerfulRelationDyadicBlock_coordinate_bounds hrs
  have hrep := mem_powerfulRelationRepresentationsUpTo_iff.mp
    (mem_powerfulRelationDyadicBlock.mp hrs).1
  have hn := mem_powerfulOneTermRepresentations_iff.mp hrep.1
  have hm := mem_powerfulOneTermRepresentations_iff.mp hrep.2.1
  have hnLower : (2 ^ q.1.1) ^ 2 * (2 ^ q.1.2) ^ 3 ≤ x := by
    calc
      (2 ^ q.1.1) ^ 2 * (2 ^ q.1.2) ^ 3 ≤
          rs.1.2 ^ 2 * rs.1.1 ^ 3 :=
        Nat.mul_le_mul (Nat.pow_le_pow_left hc.1.1 2)
          (Nat.pow_le_pow_left hc.2.1.1 3)
      _ ≤ x := by
        exact (Nat.le_div_iff_mul_le (pow_pos hn.1 3)).mp
          (Nat.le_sqrt'.mp hn.2.2.2.2)
  have hmLower : (2 ^ q.2.1) ^ 2 * (2 ^ q.2.2) ^ 3 ≤ x + h := by
    calc
      (2 ^ q.2.1) ^ 2 * (2 ^ q.2.2) ^ 3 ≤
          rs.2.2 ^ 2 * rs.2.1 ^ 3 :=
        Nat.mul_le_mul (Nat.pow_le_pow_left hc.2.2.1.1 2)
          (Nat.pow_le_pow_left hc.2.2.2.1 3)
      _ ≤ x + h := by
        exact (Nat.le_div_iff_mul_le (pow_pos hm.1 3)).mp
          (Nat.le_sqrt'.mp hm.2.2.2.2)
  constructor
  · calc
      (2 ^ (q.1.1 + 1)) ^ 2 * (2 ^ (q.1.2 + 1)) ^ 3 =
          32 * ((2 ^ q.1.1) ^ 2 * (2 ^ q.1.2) ^ 3) := by
        simp only [pow_succ]
        ring
      _ ≤ 32 * x := Nat.mul_le_mul_left 32 hnLower
  · calc
      (2 ^ (q.2.1 + 1)) ^ 2 * (2 ^ (q.2.2 + 1)) ^ 3 =
          32 * ((2 ^ q.2.1) ^ 2 * (2 ^ q.2.2) ^ 3) := by
        simp only [pow_succ]
        ring
      _ ≤ 32 * (x + h) := Nat.mul_le_mul_left 32 hmLower

/-- The complete monomial produced by the interpolation is bounded by
`2048*x²` on every realized block when `h ≤ x`. -/
theorem powerfulRelationDyadicBlock_interpolationMonomial_le
    {a b h x : ℕ} {q : (ℕ × ℕ) × (ℕ × ℕ)}
    (hhX : h ≤ x) (hq : q ∈ powerfulRelationDyadicIndices a b h x) :
    (2 ^ (q.1.1 + 1) * 2 ^ (q.1.2 + 1)) ^ 2 *
        (2 ^ (q.2.1 + 1) * 2 ^ (q.2.2 + 1)) ^ 2 *
        (2 ^ (q.1.2 + 1) * 2 ^ (q.2.2 + 1)) ≤
      2048 * x ^ 2 := by
  rw [powerfulRelationDyadicIndices, Finset.mem_image] at hq
  rcases hq with ⟨rs, hrs, rfl⟩
  have hs := powerfulRelationDyadicBlock_scale_products
    (show rs ∈ powerfulRelationDyadicBlock a b h x
      (powerfulRelationDyadicIndex rs) from by
        exact mem_powerfulRelationDyadicBlock.mpr ⟨hrs, rfl⟩)
  calc
    (2 ^ ((powerfulRelationDyadicIndex rs).1.1 + 1) *
          2 ^ ((powerfulRelationDyadicIndex rs).1.2 + 1)) ^ 2 *
        (2 ^ ((powerfulRelationDyadicIndex rs).2.1 + 1) *
          2 ^ ((powerfulRelationDyadicIndex rs).2.2 + 1)) ^ 2 *
        (2 ^ ((powerfulRelationDyadicIndex rs).1.2 + 1) *
          2 ^ ((powerfulRelationDyadicIndex rs).2.2 + 1)) =
        ((2 ^ ((powerfulRelationDyadicIndex rs).1.1 + 1)) ^ 2 *
          (2 ^ ((powerfulRelationDyadicIndex rs).1.2 + 1)) ^ 3) *
        ((2 ^ ((powerfulRelationDyadicIndex rs).2.1 + 1)) ^ 2 *
          (2 ^ ((powerfulRelationDyadicIndex rs).2.2 + 1)) ^ 3) := by ring
    _ ≤ (32 * x) * (32 * (x + h)) := Nat.mul_le_mul hs.1 hs.2
    _ ≤ (32 * x) * (64 * x) := by
      exact Nat.mul_le_mul_left _ (by omega)
    _ = 2048 * x ^ 2 := by ring

/-- Uniform per-block conclusion after inserting the two powerful-number
scale constraints into the interpolated estimate. -/
theorem card_powerfulRelationDyadicBlock_le_fifthRoot_majorant
    {a b h x : ℕ} {q : (ℕ × ℕ) × (ℕ × ℕ)}
    (ha : 0 < a) (hb : 0 < b) (hh : 0 < h) (hx : 2 ≤ x)
    (haX : a ≤ x) (hbX : b ≤ x) (hhX : h ≤ x)
    (hq : q ∈ powerfulRelationDyadicIndices a b h x)
    {ε : ℝ} (hε : 0 < ε) :
    ((powerfulRelationDyadicBlock a b h x q).card : ℝ) ≤
      ((2048 : ℝ) * (x : ℝ) ^ 2 *
        (squareRelationPolynomialEpsilonConstant
            (ε / ((10 * 8 + 6 : ℕ) : ℝ)) *
          (x : ℝ) ^ ε)) ^ ((5 : ℝ)⁻¹) := by
  let F := squareRelationPolynomialEpsilonConstant
      (ε / ((10 * 8 + 6 : ℕ) : ℝ)) * (x : ℝ) ^ ε
  have hF : 0 ≤ F := mul_nonneg
    (squareRelationPolynomialEpsilonConstant_pos
      (div_pos hε (by positivity))).le
    (Real.rpow_nonneg (by positivity) _)
  have hmono := powerfulRelationDyadicBlock_interpolationMonomial_le hhX hq
  have hinside :
      (((2 ^ (q.1.1 + 1) * 2 ^ (q.1.2 + 1) : ℕ) : ℝ) ^ 2 *
          ((2 ^ (q.2.1 + 1) * 2 ^ (q.2.2 + 1) : ℕ) : ℝ) ^ 2 *
          (((2 ^ (q.1.2 + 1) * 2 ^ (q.2.2 + 1) : ℕ) : ℝ) * F)) ≤
        (2048 : ℝ) * (x : ℝ) ^ 2 * F := by
    have hmonoR :
        (((2 ^ (q.1.1 + 1) * 2 ^ (q.1.2 + 1)) ^ 2 *
          (2 ^ (q.2.1 + 1) * 2 ^ (q.2.2 + 1)) ^ 2 *
          (2 ^ (q.1.2 + 1) * 2 ^ (q.2.2 + 1)) : ℕ) : ℝ) ≤
          ((2048 * x ^ 2 : ℕ) : ℝ) := by exact_mod_cast hmono
    calc
      (((2 ^ (q.1.1 + 1) * 2 ^ (q.1.2 + 1) : ℕ) : ℝ) ^ 2 *
          ((2 ^ (q.2.1 + 1) * 2 ^ (q.2.2 + 1) : ℕ) : ℝ) ^ 2 *
          (((2 ^ (q.1.2 + 1) * 2 ^ (q.2.2 + 1) : ℕ) : ℝ) * F)) =
          (((2 ^ (q.1.1 + 1) * 2 ^ (q.1.2 + 1)) ^ 2 *
            (2 ^ (q.2.1 + 1) * 2 ^ (q.2.2 + 1)) ^ 2 *
            (2 ^ (q.1.2 + 1) * 2 ^ (q.2.2 + 1)) : ℕ) : ℝ) * F := by
        push_cast
        ring
      _ ≤ ((2048 * x ^ 2 : ℕ) : ℝ) * F :=
        mul_le_mul_of_nonneg_right hmonoR hF
      _ = (2048 : ℝ) * (x : ℝ) ^ 2 * F := by norm_num
  exact (card_powerfulRelationDyadicBlock_le_interpolated
    q ha hb hh hx haX hbX hhX hε).trans
      (Real.rpow_le_rpow (by positivity) hinside (by positivity))

/-- Algebraic normalization of the fifth-root majorant. -/
theorem fifthRoot_powerfulRelationMajorant_eq
    {x C ε : ℝ} (hx : 0 ≤ x) (hC : 0 ≤ C) (hε : 0 < ε) :
    (2048 * x ^ 2 * (C * x ^ ε)) ^ ((5 : ℝ)⁻¹) =
      (2048 ^ ((5 : ℝ)⁻¹) * C ^ ((5 : ℝ)⁻¹)) *
        x ^ ((2 : ℝ) / 5 + ε / 5) := by
  have h2048 : (0 : ℝ) ≤ 2048 := by norm_num
  have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
  calc
    (2048 * x ^ 2 * (C * x ^ ε)) ^ ((5 : ℝ)⁻¹) =
        (2048 ^ ((5 : ℝ)⁻¹) * (x ^ 2) ^ ((5 : ℝ)⁻¹)) *
          (C ^ ((5 : ℝ)⁻¹) * (x ^ ε) ^ ((5 : ℝ)⁻¹)) := by
      rw [Real.mul_rpow (mul_nonneg h2048 hx2)
          (mul_nonneg hC (Real.rpow_nonneg hx _)),
        Real.mul_rpow h2048 hx2,
        Real.mul_rpow hC (Real.rpow_nonneg hx _)]
    _ = (2048 ^ ((5 : ℝ)⁻¹) * C ^ ((5 : ℝ)⁻¹)) *
        (x ^ ((2 : ℝ) * (5 : ℝ)⁻¹) *
          x ^ (ε * (5 : ℝ)⁻¹)) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul hx, ← Real.rpow_mul hx]
      ring_nf
    _ = (2048 ^ ((5 : ℝ)⁻¹) * C ^ ((5 : ℝ)⁻¹)) *
        x ^ ((2 : ℝ) / 5 + ε / 5) := by
      rw [← Real.rpow_add_of_nonneg hx (by positivity)
        (mul_nonneg hε.le (by positivity))]
      congr 2

/-- The explicit constant in the normalized per-block estimate. -/
noncomputable def powerfulRelationBlockEpsilonConstant (ε : ℝ) : ℝ :=
  (2048 : ℝ) ^ ((5 : ℝ)⁻¹) *
    (squareRelationPolynomialEpsilonConstant
      (ε / ((10 * 8 + 6 : ℕ) : ℝ))) ^ ((5 : ℝ)⁻¹)

theorem powerfulRelationBlockEpsilonConstant_pos {ε : ℝ} (hε : 0 < ε) :
    0 < powerfulRelationBlockEpsilonConstant ε := by
  unfold powerfulRelationBlockEpsilonConstant
  exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
    (Real.rpow_pos_of_pos
      (squareRelationPolynomialEpsilonConstant_pos
        (div_pos hε (by positivity))) _)

/-- Source-shaped per-block estimate after the fifth root has been
normalized. -/
theorem card_powerfulRelationDyadicBlock_le_const_mul_rpow
    {a b h x : ℕ} {q : (ℕ × ℕ) × (ℕ × ℕ)}
    (ha : 0 < a) (hb : 0 < b) (hh : 0 < h) (hx : 2 ≤ x)
    (haX : a ≤ x) (hbX : b ≤ x) (hhX : h ≤ x)
    (hq : q ∈ powerfulRelationDyadicIndices a b h x)
    {ε : ℝ} (hε : 0 < ε) :
    ((powerfulRelationDyadicBlock a b h x q).card : ℝ) ≤
      powerfulRelationBlockEpsilonConstant ε *
        (x : ℝ) ^ ((2 : ℝ) / 5 + ε / 5) := by
  have hC : 0 ≤ squareRelationPolynomialEpsilonConstant
      (ε / ((10 * 8 + 6 : ℕ) : ℝ)) :=
    (squareRelationPolynomialEpsilonConstant_pos
      (div_pos hε (by positivity))).le
  have hmain := card_powerfulRelationDyadicBlock_le_fifthRoot_majorant
    ha hb hh hx haX hbX hhX hq hε
  rw [fifthRoot_powerfulRelationMajorant_eq
    (Nat.cast_nonneg x) hC hε] at hmain
  simpa only [powerfulRelationBlockEpsilonConstant] using hmain

/-- Dyadic assembly before absorbing the number of scale quadruples. -/
theorem card_powerfulRelationRepresentationsUpTo_le_dyadic_majorant
    {a b h x : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hh : 0 < h) (hx : 2 ≤ x)
    (haX : a ≤ x) (hbX : b ≤ x) (hhX : h ≤ x)
    {ε : ℝ} (hε : 0 < ε) :
    ((powerfulRelationRepresentationsUpTo a b h x).card : ℝ) ≤
      (((Nat.log 2 (x + h) + 1) ^ 4 : ℕ) : ℝ) *
        (powerfulRelationBlockEpsilonConstant ε *
          (x : ℝ) ^ ((2 : ℝ) / 5 + ε / 5)) := by
  let M := powerfulRelationBlockEpsilonConstant ε *
    (x : ℝ) ^ ((2 : ℝ) / 5 + ε / 5)
  have hM : 0 ≤ M := mul_nonneg
    (powerfulRelationBlockEpsilonConstant_pos hε).le
    (Real.rpow_nonneg (by positivity) _)
  calc
    ((powerfulRelationRepresentationsUpTo a b h x).card : ℝ) =
        ∑ q ∈ powerfulRelationDyadicIndices a b h x,
          ((powerfulRelationDyadicBlock a b h x q).card : ℝ) := by
      exact_mod_cast
        card_powerfulRelationRepresentationsUpTo_eq_sum_dyadicBlocks a b h x
    _ ≤ ∑ _q ∈ powerfulRelationDyadicIndices a b h x, M := by
      apply Finset.sum_le_sum
      intro q hq
      exact card_powerfulRelationDyadicBlock_le_const_mul_rpow
        ha hb hh hx haX hbX hhX hq hε
    _ = ((powerfulRelationDyadicIndices a b h x).card : ℝ) * M := by simp
    _ ≤ (((Nat.log 2 (x + h) + 1) ^ 4 : ℕ) : ℝ) * M := by
      gcongr
      exact_mod_cast card_powerfulRelationDyadicIndices_le a b h x

/-! ## Absorbing the dyadic logarithms -/

/-- Comparison of the discrete base-two logarithm with the real logarithm. -/
theorem natLogTwo_cast_le_log_div {n : ℕ} (hn : 0 < n) :
    (Nat.log 2 n : ℝ) ≤ Real.log n / Real.log 2 := by
  have hpowNat : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 hn.ne'
  have hpowReal : (2 : ℝ) ^ Nat.log 2 n ≤ (n : ℝ) := by
    exact_mod_cast hpowNat
  have hlog := Real.log_le_log
    (by positivity : (0 : ℝ) < 2 ^ Nat.log 2 n) hpowReal
  rw [Real.log_pow] at hlog
  exact (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).2 (by
    simpa only [mul_comm] using hlog)

/-- The four dyadic-index sums cost an arbitrarily small power of `x`, with
an explicit constant. -/
theorem dyadicIndexCount_cast_le_const_mul_rpow
    {h x : ℕ} (hx : 2 ≤ x) (hhX : h ≤ x) {δ : ℝ} (hδ : 0 < δ) :
    (((Nat.log 2 (x + h) + 1) ^ 4 : ℕ) : ℝ) ≤
      (1 / (Real.log 2 * δ) + 2) ^ 4 * (x : ℝ) ^ (4 * δ) := by
  have hxPos : 0 < x := by omega
  have hxhPos : 0 < x + h := by omega
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hxR : (1 : ℝ) ≤ x := by exact_mod_cast (show 1 ≤ x by omega)
  have hxPowOne : (1 : ℝ) ≤ (x : ℝ) ^ δ := by
    exact Real.one_le_rpow hxR hδ.le
  have hlogX : Real.log (x : ℝ) ≤ (x : ℝ) ^ δ / δ :=
    Real.log_le_rpow_div (by positivity) hδ
  have hxhR : (x + h : ℕ) ≤ 2 * x := by omega
  have hlogXH : Real.log (x + h : ℕ) ≤ Real.log 2 + Real.log x := by
    calc
      Real.log (x + h : ℕ) ≤ Real.log (2 * x : ℕ) := by
        apply Real.log_le_log (by exact_mod_cast hxhPos)
        exact_mod_cast hxhR
      _ = Real.log 2 + Real.log x := by
        push_cast
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by exact_mod_cast hxPos.ne')]
  have hL : ((Nat.log 2 (x + h) + 1 : ℕ) : ℝ) ≤
      (1 / (Real.log 2 * δ) + 2) * (x : ℝ) ^ δ := by
    push_cast
    calc
      (Nat.log 2 (x + h) : ℝ) + 1 ≤
          Real.log (x + h : ℕ) / Real.log 2 + 1 := by
        gcongr
        exact natLogTwo_cast_le_log_div hxhPos
      _ ≤ (Real.log 2 + Real.log x) / Real.log 2 + 1 := by
        gcongr
      _ = Real.log x / Real.log 2 + 2 := by
        field_simp [hlogTwo.ne']
        ring
      _ ≤ ((x : ℝ) ^ δ / δ) / Real.log 2 + 2 := by
        gcongr
      _ ≤ ((x : ℝ) ^ δ / δ) / Real.log 2 +
          2 * (x : ℝ) ^ δ := by nlinarith
      _ = (1 / (Real.log 2 * δ) + 2) * (x : ℝ) ^ δ := by
        field_simp [hlogTwo.ne', hδ.ne']
  have hP : 0 ≤ 1 / (Real.log 2 * δ) + 2 := by positivity
  calc
    (((Nat.log 2 (x + h) + 1) ^ 4 : ℕ) : ℝ) =
        (((Nat.log 2 (x + h) + 1 : ℕ) : ℝ)) ^ 4 := by norm_num
    _ ≤ (((1 / (Real.log 2 * δ) + 2) * (x : ℝ) ^ δ)) ^ 4 :=
      pow_le_pow_left₀ (by positivity) hL 4
    _ = (1 / (Real.log 2 * δ) + 2) ^ 4 * (x : ℝ) ^ (4 * δ) := by
      rw [mul_pow]
      rw [← Real.rpow_mul_natCast (by positivity)]
      congr 2
      ring

/-! ## Corollary 2.11 for the normalized linear parameter range -/

/-- Explicit constant after both the fifth-root interpolation and the four
dyadic logarithms have been absorbed. -/
noncomputable def powerfulRelationEpsilonConstant (ε : ℝ) : ℝ :=
  (1 / (Real.log 2 * (ε / 5)) + 2) ^ 4 *
    powerfulRelationBlockEpsilonConstant ε

theorem powerfulRelationEpsilonConstant_pos {ε : ℝ} (hε : 0 < ε) :
    0 < powerfulRelationEpsilonConstant ε := by
  unfold powerfulRelationEpsilonConstant
  apply mul_pos
  · positivity
  · exact powerfulRelationBlockEpsilonConstant_pos hε

/-- Pointwise sharp count in the normalized source range
`1 ≤ a,b,h ≤ x`. -/
theorem card_powerfulRelationRepresentationsUpTo_le_const_mul_rpow
    {a b h x : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hh : 0 < h) (hx : 2 ≤ x)
    (haX : a ≤ x) (hbX : b ≤ x) (hhX : h ≤ x)
    {ε : ℝ} (hε : 0 < ε) :
    ((powerfulRelationRepresentationsUpTo a b h x).card : ℝ) ≤
      powerfulRelationEpsilonConstant ε *
        (x : ℝ) ^ ((2 : ℝ) / 5 + ε) := by
  have hεFive : 0 < ε / 5 := div_pos hε (by norm_num)
  have hdyadic := dyadicIndexCount_cast_le_const_mul_rpow
    hx hhX hεFive
  have hblock := card_powerfulRelationRepresentationsUpTo_le_dyadic_majorant
    ha hb hh hx haX hbX hhX hε
  let L := (1 / (Real.log 2 * (ε / 5)) + 2) ^ 4
  let B := powerfulRelationBlockEpsilonConstant ε
  have hLB : 0 ≤ B * (x : ℝ) ^ ((2 : ℝ) / 5 + ε / 5) :=
    mul_nonneg (powerfulRelationBlockEpsilonConstant_pos hε).le
      (Real.rpow_nonneg (by positivity) _)
  calc
    ((powerfulRelationRepresentationsUpTo a b h x).card : ℝ) ≤
        (((Nat.log 2 (x + h) + 1) ^ 4 : ℕ) : ℝ) *
          (B * (x : ℝ) ^ ((2 : ℝ) / 5 + ε / 5)) := hblock
    _ ≤ (L * (x : ℝ) ^ (4 * (ε / 5))) *
          (B * (x : ℝ) ^ ((2 : ℝ) / 5 + ε / 5)) :=
      mul_le_mul_of_nonneg_right hdyadic hLB
    _ = powerfulRelationEpsilonConstant ε *
        (x : ℝ) ^ ((2 : ℝ) / 5 + ε) := by
      dsimp [L, B, powerfulRelationEpsilonConstant]
      calc
        (1 / (Real.log 2 * (ε / 5)) + 2) ^ 4 *
              (x : ℝ) ^ (4 * (ε / 5)) *
              (powerfulRelationBlockEpsilonConstant ε *
                (x : ℝ) ^ ((2 : ℝ) / 5 + ε / 5)) =
            (1 / (Real.log 2 * (ε / 5)) + 2) ^ 4 *
              powerfulRelationBlockEpsilonConstant ε *
              ((x : ℝ) ^ (4 * (ε / 5)) *
                (x : ℝ) ^ ((2 : ℝ) / 5 + ε / 5)) := by ring
        _ = (1 / (Real.log 2 * (ε / 5)) + 2) ^ 4 *
              powerfulRelationBlockEpsilonConstant ε *
              (x : ℝ) ^
                (4 * (ε / 5) + ((2 : ℝ) / 5 + ε / 5)) := by
            rw [← Real.rpow_add (by positivity : (0 : ℝ) < x)]
        _ = (1 / (Real.log 2 * (ε / 5)) + 2) ^ 4 *
              powerfulRelationBlockEpsilonConstant ε *
              (x : ℝ) ^ ((2 : ℝ) / 5 + ε) := by
            congr 2
            ring

/-- The same pointwise result for the literal powerful-number pair set. -/
theorem card_powerfulRelationPairsUpTo_le_const_mul_rpow
    {a b h x : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hh : 0 < h) (hx : 2 ≤ x)
    (haX : a ≤ x) (hbX : b ≤ x) (hhX : h ≤ x)
    {ε : ℝ} (hε : 0 < ε) :
    ((powerfulRelationPairsUpTo a b h x).card : ℝ) ≤
      powerfulRelationEpsilonConstant ε *
        (x : ℝ) ^ ((2 : ℝ) / 5 + ε) := by
  rw [← card_powerfulRelationRepresentationsUpTo a b h x]
  exact card_powerfulRelationRepresentationsUpTo_le_const_mul_rpow
    ha hb hh hx haX hbX hhX hε

/-- Family form of Corollary 2.11 in the normalized range in which all three
positive parameters are eventually at most the main cutoff. -/
theorem powerfulRelationPairsUpTo_powerUpperBound_two_fifths
    (a b h : ℕ → ℕ)
    (haPos : ∀ᶠ X : ℕ in atTop, 0 < a X)
    (hbPos : ∀ᶠ X : ℕ in atTop, 0 < b X)
    (hhPos : ∀ᶠ X : ℕ in atTop, 0 < h X)
    (haBound : ∀ᶠ X : ℕ in atTop, a X ≤ X)
    (hbBound : ∀ᶠ X : ℕ in atTop, b X ≤ X)
    (hhBound : ∀ᶠ X : ℕ in atTop, h X ≤ X) :
    PowerUpperBound
      (fun X : ℕ => ((powerfulRelationPairsUpTo
        (a X) (b X) (h X) X).card : ℝ)) (2 / 5 : ℝ) := by
  intro ε hε
  refine Asymptotics.IsBigO.of_bound
    (powerfulRelationEpsilonConstant ε) ?_
  filter_upwards [haPos, hbPos, hhPos, haBound, hbBound, hhBound,
    Filter.eventually_ge_atTop 2] with X ha hb hh haX hbX hhX hX
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _),
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  exact card_powerfulRelationPairsUpTo_le_const_mul_rpow
    ha hb hh hX haX hbX hhX hε

/-! ## Literal signed-shift source interface -/

/-- Tao's literal finite set of positive powerful solutions to
`a*n+h=b*m`, with integer `h` and `a*n ≤ x`.  The displayed upper bound on
`m` is redundant but makes the set finite. -/
noncomputable def powerfulRelationPairsUpToInt
    (a b : ℕ) (h : ℤ) (x : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.Icc 1 x).product (Finset.Icc 1 (x + h.natAbs))).filter fun nm =>
    Powerful nm.1 ∧ Powerful nm.2 ∧
      (a : ℤ) * nm.1 + h = (b : ℤ) * nm.2 ∧
      a * nm.1 ≤ x

theorem mem_powerfulRelationPairsUpToInt
    {a b : ℕ} {h : ℤ} {x : ℕ} {nm : ℕ × ℕ} :
    nm ∈ powerfulRelationPairsUpToInt a b h x ↔
      1 ≤ nm.1 ∧ nm.1 ≤ x ∧
      1 ≤ nm.2 ∧ nm.2 ≤ x + h.natAbs ∧
      Powerful nm.1 ∧ Powerful nm.2 ∧
      (a : ℤ) * nm.1 + h = (b : ℤ) * nm.2 ∧
      a * nm.1 ≤ x := by
  classical
  simp [powerfulRelationPairsUpToInt, and_assoc]

/-- For a nonnegative shift, the signed source set is exactly the earlier
natural-shift set. -/
theorem powerfulRelationPairsUpToInt_natCast_eq
    (a b h x : ℕ) :
    powerfulRelationPairsUpToInt a b (h : ℤ) x =
      powerfulRelationPairsUpTo a b h x := by
  classical
  ext nm
  rw [mem_powerfulRelationPairsUpToInt, mem_powerfulRelationPairsUpTo]
  simp only [Int.natAbs_natCast]
  constructor
  · rintro ⟨hn, hnx, hm, hmx, hnPower, hmPower, heq, hax⟩
    exact ⟨hn, hnx, hm, hmx, hnPower, hmPower,
      by exact_mod_cast heq, hax⟩
  · rintro ⟨hn, hnx, hm, hmx, hnPower, hmPower, heq, hax⟩
    exact ⟨hn, hnx, hm, hmx, hnPower, hmPower,
      by exact_mod_cast heq, hax⟩

private theorem prodSwap_injective :
    Function.Injective (fun nm : ℕ × ℕ => (nm.2, nm.1)) := by
  rintro ⟨n₁, m₁⟩ ⟨n₂, m₂⟩ h
  simp only [Prod.mk.injEq] at h ⊢
  exact ⟨h.2, h.1⟩

/-- A negative-shift solution injects, by swapping its coordinates, into
the positive-shift relation with the coefficients interchanged. -/
theorem card_powerfulRelationPairsUpToInt_le_swap_of_neg
    {a b x : ℕ} {h : ℤ} (hb : 0 < b) (hh : h < 0) :
    (powerfulRelationPairsUpToInt a b h x).card ≤
      (powerfulRelationPairsUpTo b a h.natAbs x).card := by
  classical
  let swap := fun nm : ℕ × ℕ => (nm.2, nm.1)
  have hsubset : (powerfulRelationPairsUpToInt a b h x).image swap ⊆
      powerfulRelationPairsUpTo b a h.natAbs x := by
    intro mn hmn
    rw [Finset.mem_image] at hmn
    rcases hmn with ⟨nm, hnm, rfl⟩
    have hs := mem_powerfulRelationPairsUpToInt.mp hnm
    rw [mem_powerfulRelationPairsUpTo]
    have hhEq : h = -(h.natAbs : ℤ) := Int.eq_neg_natAbs_of_nonpos hh.le
    have heqInt : (b : ℤ) * nm.2 + (h.natAbs : ℤ) =
        (a : ℤ) * nm.1 := by
      rw [hhEq] at hs
      linarith [hs.2.2.2.2.2.2.1]
    have hbm : b * nm.2 ≤ x := by
      have hbmInt : (b : ℤ) * nm.2 ≤ (x : ℤ) := by
        have haxInt : (a : ℤ) * nm.1 ≤ (x : ℤ) := by
          exact_mod_cast hs.2.2.2.2.2.2.2
        calc
          (b : ℤ) * nm.2 ≤ (b : ℤ) * nm.2 + h.natAbs := by omega
          _ = (a : ℤ) * nm.1 := heqInt
          _ ≤ (x : ℤ) := haxInt
      exact_mod_cast hbmInt
    have hmLe : nm.2 ≤ x := by
      exact (Nat.le_mul_of_pos_left nm.2 hb).trans hbm
    have hnLe : nm.1 ≤ x + h.natAbs := hs.2.1.trans (Nat.le_add_right _ _)
    exact ⟨hs.2.2.1, hmLe, hs.1, hnLe, hs.2.2.2.2.2.1,
      hs.2.2.2.2.1, by exact_mod_cast heqInt, hbm⟩
  calc
    (powerfulRelationPairsUpToInt a b h x).card =
        ((powerfulRelationPairsUpToInt a b h x).image swap).card :=
      (Finset.card_image_iff.mpr prodSwap_injective.injOn).symm
    _ ≤ (powerfulRelationPairsUpTo b a h.natAbs x).card :=
      Finset.card_le_card hsubset

/-- Pointwise source-faithful signed form of Corollary 2.11 in the normalized
range `a,b,|h| ≤ x`. -/
theorem card_powerfulRelationPairsUpToInt_le_const_mul_rpow
    {a b x : ℕ} {h : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hh : h ≠ 0) (hx : 2 ≤ x)
    (haX : a ≤ x) (hbX : b ≤ x) (hhX : h.natAbs ≤ x)
    {ε : ℝ} (hε : 0 < ε) :
    ((powerfulRelationPairsUpToInt a b h x).card : ℝ) ≤
      powerfulRelationEpsilonConstant ε *
        (x : ℝ) ^ ((2 : ℝ) / 5 + ε) := by
  rcases lt_or_gt_of_ne hh with hhNeg | hhPos
  · have hnatPos : 0 < h.natAbs := Int.natAbs_pos.mpr hh
    calc
      ((powerfulRelationPairsUpToInt a b h x).card : ℝ) ≤
          ((powerfulRelationPairsUpTo b a h.natAbs x).card : ℝ) := by
        exact_mod_cast card_powerfulRelationPairsUpToInt_le_swap_of_neg hb hhNeg
      _ ≤ powerfulRelationEpsilonConstant ε *
          (x : ℝ) ^ ((2 : ℝ) / 5 + ε) :=
        card_powerfulRelationPairsUpTo_le_const_mul_rpow
          hb ha hnatPos hx hbX haX hhX hε
  · have hhEq : h = (h.natAbs : ℤ) := by
      rw [Int.natCast_natAbs, abs_of_pos hhPos]
    rw [hhEq, powerfulRelationPairsUpToInt_natCast_eq]
    exact card_powerfulRelationPairsUpTo_le_const_mul_rpow
      ha hb (Int.natAbs_pos.mpr hh) hx haX hbX hhX hε

/-- Increasing the source cutoff only enlarges the literal signed solution
set. -/
theorem powerfulRelationPairsUpToInt_mono
    (a b : ℕ) (h : ℤ) {x y : ℕ} (hxy : x ≤ y) :
    powerfulRelationPairsUpToInt a b h x ⊆
      powerfulRelationPairsUpToInt a b h y := by
  intro nm hnm
  rw [mem_powerfulRelationPairsUpToInt] at hnm ⊢
  exact ⟨hnm.1, hnm.2.1.trans hxy, hnm.2.2.1,
    hnm.2.2.2.1.trans (Nat.add_le_add_right hxy _),
    hnm.2.2.2.2.1, hnm.2.2.2.2.2.1,
    hnm.2.2.2.2.2.2.1, hnm.2.2.2.2.2.2.2.trans hxy⟩

/-- Exact formal meaning of a natural-valued parameter satisfying the
paper's `≪ X` convention. -/
def LinearlyBoundedNatSequence (f : ℕ → ℕ) : Prop :=
  ∃ C : ℕ, ∀ᶠ X : ℕ in atTop, f X ≤ C * X

/-- Integer-valued `≪ X`, measured by absolute value. -/
def LinearlyBoundedIntSequence (f : ℕ → ℤ) : Prop :=
  LinearlyBoundedNatSequence fun X => (f X).natAbs

/-- Source-faithful family form of Corollary 2.11: positive coefficients,
a nonzero signed shift, and all three parameters `≪ X` imply the uniform
`X^(2/5+o(1))` bound. -/
theorem powerfulRelationPairsUpToInt_powerUpperBound_two_fifths
    (a b : ℕ → ℕ) (h : ℕ → ℤ)
    (haLinear : LinearlyBoundedNatSequence a)
    (hbLinear : LinearlyBoundedNatSequence b)
    (hhLinear : LinearlyBoundedIntSequence h)
    (haPos : ∀ᶠ X : ℕ in atTop, 0 < a X)
    (hbPos : ∀ᶠ X : ℕ in atTop, 0 < b X)
    (hhNe : ∀ᶠ X : ℕ in atTop, h X ≠ 0) :
    PowerUpperBound
      (fun X : ℕ => ((powerfulRelationPairsUpToInt
        (a X) (b X) (h X) X).card : ℝ)) (2 / 5 : ℝ) := by
  obtain ⟨Ca, haBound⟩ := haLinear
  obtain ⟨Cb, hbBound⟩ := hbLinear
  obtain ⟨Ch, hhBound⟩ := hhLinear
  let C : ℕ := max 1 (max Ca (max Cb Ch))
  have hCOne : 1 ≤ C := le_max_left _ _
  have hCaC : Ca ≤ C :=
    (le_max_left Ca (max Cb Ch)).trans (le_max_right 1 _)
  have hCbC : Cb ≤ C :=
    (le_max_left Cb Ch).trans
      ((le_max_right Ca (max Cb Ch)).trans (le_max_right 1 _))
  have hChC : Ch ≤ C :=
    (le_max_right Cb Ch).trans
      ((le_max_right Ca (max Cb Ch)).trans (le_max_right 1 _))
  intro ε hε
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := div_pos hε (by norm_num)
  let r : ℝ := (2 : ℝ) / 5 + δ
  let K : ℝ := powerfulRelationEpsilonConstant δ * (C : ℝ) ^ r
  have hK : 0 ≤ K := mul_nonneg
    (powerfulRelationEpsilonConstant_pos hδ).le
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  refine Asymptotics.IsBigO.of_bound K ?_
  filter_upwards [haBound, hbBound, hhBound, haPos, hbPos, hhNe,
    Filter.eventually_ge_atTop 2] with X haX hbX hhX ha hb hh hX
  have hCX : X ≤ C * X := by
    simpa only [one_mul] using Nat.mul_le_mul_right X hCOne
  have haCX : a X ≤ C * X := haX.trans (Nat.mul_le_mul_right X hCaC)
  have hbCX : b X ≤ C * X := hbX.trans (Nat.mul_le_mul_right X hCbC)
  have hhCX : (h X).natAbs ≤ C * X :=
    hhX.trans (Nat.mul_le_mul_right X hChC)
  have hCXTwo : 2 ≤ C * X := hX.trans hCX
  have hcardMono :
      (powerfulRelationPairsUpToInt (a X) (b X) (h X) X).card ≤
        (powerfulRelationPairsUpToInt (a X) (b X) (h X) (C * X)).card :=
    Finset.card_le_card
      (powerfulRelationPairsUpToInt_mono (a X) (b X) (h X) hCX)
  have hpoint := card_powerfulRelationPairsUpToInt_le_const_mul_rpow
    ha hb hh hCXTwo haCX hbCX hhCX hδ
  have hxR : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hexp : r ≤ (2 : ℝ) / 5 + ε := by
    dsimp [r, δ]
    linarith
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _),
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  calc
    ((powerfulRelationPairsUpToInt (a X) (b X) (h X) X).card : ℝ) ≤
        ((powerfulRelationPairsUpToInt (a X) (b X) (h X) (C * X)).card : ℝ) := by
      exact_mod_cast hcardMono
    _ ≤ powerfulRelationEpsilonConstant δ *
        ((C * X : ℕ) : ℝ) ^ r := hpoint
    _ = K * (X : ℝ) ^ r := by
      dsimp [K]
      push_cast
      rw [Real.mul_rpow (Nat.cast_nonneg C) (Nat.cast_nonneg X)]
      ring
    _ ≤ K * (X : ℝ) ^ ((2 : ℝ) / 5 + ε) := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hxR hexp) hK

end Tao2026

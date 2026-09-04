import GafniTao.HeathBrownShiftFibers
import Mathlib.Data.Finset.Sigma

/-!
# Diagonal and fixed-shift decomposition of `𝓝₂`

The localized pair count is bounded by its diagonal together with two
copies of the positive-shift fibers.  The two copies retain orientation,
so no symmetry or multiplicity is silently discarded.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

noncomputable def heathBrownPairCountTwoDiagonal
    (N k H K : ℕ) (f : ℝ → ℝ) : Finset (ℕ × ℕ) := by
  classical
  exact (heathBrownPairCountTwo N k H K f).filter fun p => p.1 = p.2

noncomputable def heathBrownPairCountTwoPositive
    (N k H K : ℕ) (f : ℝ → ℝ) : Finset (ℕ × ℕ) := by
  classical
  exact (heathBrownPairCountTwo N k H K f).filter fun p => p.2 < p.1

noncomputable def heathBrownPairCountTwoNegative
    (N k H K : ℕ) (f : ℝ → ℝ) : Finset (ℕ × ℕ) := by
  classical
  exact (heathBrownPairCountTwo N k H K f).filter fun p => p.1 < p.2

noncomputable def heathBrownAllPositiveShiftFibers
    (N k H K : ℕ) (f : ℝ → ℝ) : Finset (Σ _d : ℕ, ℕ) :=
  (Finset.Icc 1 N).sigma fun d =>
    heathBrownPositiveShiftFiber N k H K f d

def heathBrownPairOfPositiveShift (q : Σ _d : ℕ, ℕ) : ℕ × ℕ :=
  (q.2 + q.1, q.2)

def heathBrownPairOfNegativeShift (q : Σ _d : ℕ, ℕ) : ℕ × ℕ :=
  (q.2, q.2 + q.1)

theorem heathBrownDistanceToInteger_neg (x : ℝ) :
    heathBrownDistanceToInteger (-x) = heathBrownDistanceToInteger x := by
  rw [heathBrownDistanceToInteger_eq_unitAddCircle_norm,
    heathBrownDistanceToInteger_eq_unitAddCircle_norm]
  simp

theorem heathBrownPairCountTwo_subset_three_parts
    {N k H K : ℕ} {f : ℝ → ℝ} :
    heathBrownPairCountTwo N k H K f ⊆
      heathBrownPairCountTwoDiagonal N k H K f ∪
        (heathBrownPairCountTwoPositive N k H K f ∪
          heathBrownPairCountTwoNegative N k H K f) := by
  intro p hp
  rcases lt_trichotomy p.1 p.2 with hlt | heq | hgt
  · simp [heathBrownPairCountTwoNegative, hp, hlt]
  · simp [heathBrownPairCountTwoDiagonal, hp, heq]
  · simp [heathBrownPairCountTwoPositive, hp, hgt]

theorem heathBrownPairCountTwoDiagonal_card_le
    {N k H K : ℕ} {f : ℝ → ℝ} :
    (heathBrownPairCountTwoDiagonal N k H K f).card ≤ N := by
  classical
  let s := heathBrownPairCountTwoDiagonal N k H K f
  have hinj : Set.InjOn Prod.fst (s : Set (ℕ × ℕ)) := by
    intro p hp q hq hpq
    have hpd : p.1 = p.2 := (Finset.mem_filter.mp hp).2
    have hqd : q.1 = q.2 := (Finset.mem_filter.mp hq).2
    apply Prod.ext
    · exact hpq
    · simpa [← hpd, ← hqd] using hpq
  have himage : s.image Prod.fst ⊆ Finset.Icc 1 N := by
    intro n hn
    rw [Finset.mem_image] at hn
    obtain ⟨p, hp, rfl⟩ := hn
    have hpCount := (Finset.mem_filter.mp hp).1
    rw [Finset.mem_Icc]
    exact ⟨(mem_heathBrownPairCountTwo.mp hpCount).1,
      (mem_heathBrownPairCountTwo.mp hpCount).2.1⟩
  calc
    s.card = (s.image Prod.fst).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.Icc 1 N).card := Finset.card_le_card himage
    _ ≤ N := by simp [Nat.card_Icc]

theorem heathBrownPairCountTwoPositive_subset_shiftImage
    {N k H K : ℕ} {f : ℝ → ℝ} :
    heathBrownPairCountTwoPositive N k H K f ⊆
      (heathBrownAllPositiveShiftFibers N k H K f).image
        heathBrownPairOfPositiveShift := by
  classical
  intro p hp
  have hpCount := (Finset.mem_filter.mp hp).1
  have hlt := (Finset.mem_filter.mp hp).2
  let d := p.1 - p.2
  have hd : 1 ≤ d := by dsimp [d]; omega
  have hdN : d ≤ N := by
    exact le_trans (Nat.sub_le _ _) (mem_heathBrownPairCountTwo.mp hpCount).2.1
  have hpFiber : p.2 ∈ heathBrownPositiveShiftFiber N k H K f d := by
    rw [mem_heathBrownPositiveShiftFiber]
    have hadd : p.2 + d = p.1 := by
      simp [d, Nat.add_sub_of_le hlt.le]
    exact ⟨(mem_heathBrownPairCountTwo.mp hpCount).2.2.1,
      hadd.symm ▸ (mem_heathBrownPairCountTwo.mp hpCount).2.1,
      by simpa [hadd] using hpCount⟩
  rw [Finset.mem_image]
  refine ⟨⟨d, p.2⟩, ?_, ?_⟩
  · simp [heathBrownAllPositiveShiftFibers, hd, hdN, hpFiber]
  · apply Prod.ext
    · simp [heathBrownPairOfPositiveShift, d, Nat.add_sub_of_le hlt.le]
    · rfl

theorem heathBrownPairCountTwoNegative_subset_shiftImage
    {N k H K : ℕ} {f : ℝ → ℝ} :
    heathBrownPairCountTwoNegative N k H K f ⊆
      (heathBrownAllPositiveShiftFibers N k H K f).image
        heathBrownPairOfNegativeShift := by
  classical
  intro p hp
  have hpCount := (Finset.mem_filter.mp hp).1
  have hlt := (Finset.mem_filter.mp hp).2
  let d := p.2 - p.1
  have hd : 1 ≤ d := by dsimp [d]; omega
  have hdN : d ≤ N := by
    exact le_trans (Nat.sub_le _ _) (mem_heathBrownPairCountTwo.mp hpCount).2.2.2.1
  have hswap : (p.2, p.1) ∈ heathBrownPairCountTwo N k H K f := by
    rw [mem_heathBrownPairCountTwo] at hpCount ⊢
    refine ⟨hpCount.2.2.1, hpCount.2.2.2.1, hpCount.1, hpCount.2.1,
      ?_, ?_, ?_⟩
    · simpa [Nat.dist_comm] using hpCount.2.2.2.2.1
    · have heq :
          heathBrownDerivativeCoordinate f (k - 2) p.2 -
              heathBrownDerivativeCoordinate f (k - 2) p.1 =
            -(heathBrownDerivativeCoordinate f (k - 2) p.1 -
              heathBrownDerivativeCoordinate f (k - 2) p.2) := by ring
      rw [heq, heathBrownDistanceToInteger_neg]
      exact hpCount.2.2.2.2.2.1
    · have heq :
          heathBrownDerivativeCoordinate f (k - 1) p.2 -
              heathBrownDerivativeCoordinate f (k - 1) p.1 =
            -(heathBrownDerivativeCoordinate f (k - 1) p.1 -
              heathBrownDerivativeCoordinate f (k - 1) p.2) := by ring
      rw [heq, heathBrownDistanceToInteger_neg]
      exact hpCount.2.2.2.2.2.2
  have hpFiber : p.1 ∈ heathBrownPositiveShiftFiber N k H K f d := by
    rw [mem_heathBrownPositiveShiftFiber]
    have hadd : p.1 + d = p.2 := by
      simp [d, Nat.add_sub_of_le hlt.le]
    exact ⟨(mem_heathBrownPairCountTwo.mp hpCount).1,
      hadd.symm ▸ (mem_heathBrownPairCountTwo.mp hpCount).2.2.2.1,
      by simpa [hadd] using hswap⟩
  rw [Finset.mem_image]
  refine ⟨⟨d, p.1⟩, ?_, ?_⟩
  · simp [heathBrownAllPositiveShiftFibers, hd, hdN, hpFiber]
  · apply Prod.ext
    · rfl
    · simp [heathBrownPairOfNegativeShift, d, Nat.add_sub_of_le hlt.le]

theorem heathBrownAllPositiveShiftFibers_card
    (N k H K : ℕ) (f : ℝ → ℝ) :
    (heathBrownAllPositiveShiftFibers N k H K f).card =
      ∑ d ∈ Finset.Icc 1 N,
        (heathBrownPositiveShiftFiber N k H K f d).card := by
  simp [heathBrownAllPositiveShiftFibers]

theorem heathBrownPairCountTwo_card_le_shift_sum
    (N k H K : ℕ) (f : ℝ → ℝ) :
    (heathBrownPairCountTwo N k H K f).card ≤
      N + 2 * ∑ d ∈ Finset.Icc 1 N,
        (heathBrownPositiveShiftFiber N k H K f d).card := by
  classical
  let dset := heathBrownPairCountTwoDiagonal N k H K f
  let pset := heathBrownPairCountTwoPositive N k H K f
  let nset := heathBrownPairCountTwoNegative N k H K f
  let fibers := heathBrownAllPositiveShiftFibers N k H K f
  have hdiag : dset.card ≤ N := heathBrownPairCountTwoDiagonal_card_le
  have hpos : pset.card ≤ fibers.card := by
    calc
      pset.card ≤ (fibers.image heathBrownPairOfPositiveShift).card :=
        Finset.card_le_card heathBrownPairCountTwoPositive_subset_shiftImage
      _ ≤ fibers.card := Finset.card_image_le
  have hneg : nset.card ≤ fibers.card := by
    calc
      nset.card ≤ (fibers.image heathBrownPairOfNegativeShift).card :=
        Finset.card_le_card heathBrownPairCountTwoNegative_subset_shiftImage
      _ ≤ fibers.card := Finset.card_image_le
  calc
    (heathBrownPairCountTwo N k H K f).card ≤
        (dset ∪ (pset ∪ nset)).card :=
      Finset.card_le_card heathBrownPairCountTwo_subset_three_parts
    _ ≤ dset.card + (pset.card + nset.card) := by
      calc
        (dset ∪ (pset ∪ nset)).card ≤
            dset.card + (pset ∪ nset).card :=
          Finset.card_union_le dset (pset ∪ nset)
        _ ≤ dset.card + (pset.card + nset.card) :=
          Nat.add_le_add_left (Finset.card_union_le pset nset) _
    _ ≤ N + (fibers.card + fibers.card) := by omega
    _ = N + 2 * ∑ d ∈ Finset.Icc 1 N,
        (heathBrownPositiveShiftFiber N k H K f d).card := by
      rw [heathBrownAllPositiveShiftFibers_card]
      omega

#print axioms heathBrownPairCountTwo_subset_three_parts
#print axioms heathBrownDistanceToInteger_neg
#print axioms heathBrownPairCountTwoDiagonal_card_le
#print axioms heathBrownPairCountTwoPositive_subset_shiftImage
#print axioms heathBrownPairCountTwoNegative_subset_shiftImage
#print axioms heathBrownAllPositiveShiftFibers_card
#print axioms heathBrownPairCountTwo_card_le_shift_sum

end

end GafniTao

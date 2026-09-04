import GafniTao.HeathBrownSpacing

/-!
# Heath-Brown's two-variable derivative counts

This file gives literal finite versions of the three counting functions in
Section 3 of Heath-Brown, arXiv:1601.04493v3: `mathcal N`, `mathcal N_1`, and
the localized `mathcal N_2`.  Keeping these as concrete filtered products is
important: later Fourier localization and fixed-difference arguments must
act on the actual pairs, not on an abstract cardinality parameter.
-/

open Finset

namespace GafniTao

noncomputable section

/-- The source derivative coordinate `f^(j)(n) / j!`. -/
noncomputable def heathBrownDerivativeCoordinate
    (f : ℝ → ℝ) (j : ℕ) (x : ℝ) : ℝ :=
  iteratedDeriv j f x / (j.factorial : ℝ)

/-- Heath-Brown's `mathcal N` from Lemma 1. -/
noncomputable def heathBrownPairCount
    (N k H : ℕ) (f : ℝ → ℝ) : Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter fun p =>
      ∀ j ∈ Finset.Icc 1 (k - 1),
        heathBrownDistanceToInteger
            (heathBrownDerivativeCoordinate f j p.1 -
              heathBrownDerivativeCoordinate f j p.2) ≤
          2 * (((H : ℝ) ^ j)⁻¹)

/-- The two-coordinate relaxation `mathcal N_1`, retaining only derivative
orders `k-2` and `k-1`. -/
noncomputable def heathBrownPairCountOne
    (N k H : ℕ) (f : ℝ → ℝ) : Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter fun p =>
      heathBrownDistanceToInteger
          (heathBrownDerivativeCoordinate f (k - 2) p.1 -
            heathBrownDerivativeCoordinate f (k - 2) p.2) ≤
        2 * (((H : ℝ) ^ (k - 2))⁻¹) ∧
      heathBrownDistanceToInteger
          (heathBrownDerivativeCoordinate f (k - 1) p.1 -
            heathBrownDerivativeCoordinate f (k - 1) p.2) ≤
        2 * (((H : ℝ) ^ (k - 1))⁻¹)

/-- The localized count `mathcal N_2` after the Fourier partition, with the
literal source threshold `4 H^{-j}` and source separation `1 + N/K`. -/
noncomputable def heathBrownPairCountTwo
    (N k H K : ℕ) (f : ℝ → ℝ) : Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter fun p =>
      Nat.dist p.1 p.2 ≤ 1 + N / K ∧
      heathBrownDistanceToInteger
          (heathBrownDerivativeCoordinate f (k - 2) p.1 -
            heathBrownDerivativeCoordinate f (k - 2) p.2) ≤
        4 * (((H : ℝ) ^ (k - 2))⁻¹) ∧
      heathBrownDistanceToInteger
          (heathBrownDerivativeCoordinate f (k - 1) p.1 -
            heathBrownDerivativeCoordinate f (k - 1) p.2) ≤
        4 * (((H : ℝ) ^ (k - 1))⁻¹)

theorem mem_heathBrownPairCount
    {N k H : ℕ} {f : ℝ → ℝ} {m n : ℕ} :
    (m, n) ∈ heathBrownPairCount N k H f ↔
      1 ≤ m ∧ m ≤ N ∧ 1 ≤ n ∧ n ≤ N ∧
      ∀ j ∈ Finset.Icc 1 (k - 1),
        heathBrownDistanceToInteger
            (heathBrownDerivativeCoordinate f j m -
              heathBrownDerivativeCoordinate f j n) ≤
          2 * (((H : ℝ) ^ j)⁻¹) := by
  simp [heathBrownPairCount, and_assoc]

theorem mem_heathBrownPairCountOne
    {N k H : ℕ} {f : ℝ → ℝ} {m n : ℕ} :
    (m, n) ∈ heathBrownPairCountOne N k H f ↔
      1 ≤ m ∧ m ≤ N ∧ 1 ≤ n ∧ n ≤ N ∧
      heathBrownDistanceToInteger
          (heathBrownDerivativeCoordinate f (k - 2) m -
            heathBrownDerivativeCoordinate f (k - 2) n) ≤
        2 * (((H : ℝ) ^ (k - 2))⁻¹) ∧
      heathBrownDistanceToInteger
          (heathBrownDerivativeCoordinate f (k - 1) m -
            heathBrownDerivativeCoordinate f (k - 1) n) ≤
        2 * (((H : ℝ) ^ (k - 1))⁻¹) := by
  simp [heathBrownPairCountOne, and_assoc]

theorem mem_heathBrownPairCountTwo
    {N k H K : ℕ} {f : ℝ → ℝ} {m n : ℕ} :
    (m, n) ∈ heathBrownPairCountTwo N k H K f ↔
      1 ≤ m ∧ m ≤ N ∧ 1 ≤ n ∧ n ≤ N ∧
      Nat.dist m n ≤ 1 + N / K ∧
      heathBrownDistanceToInteger
          (heathBrownDerivativeCoordinate f (k - 2) m -
            heathBrownDerivativeCoordinate f (k - 2) n) ≤
        4 * (((H : ℝ) ^ (k - 2))⁻¹) ∧
      heathBrownDistanceToInteger
          (heathBrownDerivativeCoordinate f (k - 1) m -
            heathBrownDerivativeCoordinate f (k - 1) n) ≤
        4 * (((H : ℝ) ^ (k - 1))⁻¹) := by
  simp [heathBrownPairCountTwo, and_assoc]

/-- The first source reduction, `mathcal N ≤ mathcal N_1`. -/
theorem heathBrownPairCount_subset_pairCountOne
    {N k H : ℕ} {f : ℝ → ℝ} (hk : 3 ≤ k) :
    heathBrownPairCount N k H f ⊆ heathBrownPairCountOne N k H f := by
  intro p hp
  rw [mem_heathBrownPairCount] at hp
  rw [mem_heathBrownPairCountOne]
  refine ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, ?_, ?_⟩
  · exact hp.2.2.2.2 (k - 2) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  · exact hp.2.2.2.2 (k - 1) (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)

theorem heathBrownPairCount_card_le_pairCountOne_card
    {N k H : ℕ} {f : ℝ → ℝ} (hk : 3 ≤ k) :
    (heathBrownPairCount N k H f).card ≤
      (heathBrownPairCountOne N k H f).card :=
  Finset.card_le_card (heathBrownPairCount_subset_pairCountOne hk)

/-- All diagonal pairs occur in each of the three counts when `H > 0`;
this records the source diagonal contribution exactly. -/
theorem diagonal_mem_heathBrownPairCountTwo
    {N k H K n : ℕ} {f : ℝ → ℝ}
    (hn : n ∈ Finset.Icc 1 N) (hH : 0 < H) :
    (n, n) ∈ heathBrownPairCountTwo N k H K f := by
  rw [mem_heathBrownPairCountTwo]
  have hpowNonneg (j : ℕ) : 0 ≤ (((H : ℝ) ^ j)⁻¹) := by positivity
  refine ⟨(Finset.mem_Icc.mp hn).1, (Finset.mem_Icc.mp hn).2,
    (Finset.mem_Icc.mp hn).1, (Finset.mem_Icc.mp hn).2, ?_, ?_, ?_⟩
  · simp [Nat.dist]
  · simp [heathBrownDerivativeCoordinate, heathBrownDistanceToInteger,
      hpowNonneg (k - 2)]
  · simp [heathBrownDerivativeCoordinate, heathBrownDistanceToInteger,
      hpowNonneg (k - 1)]

#print axioms mem_heathBrownPairCount
#print axioms mem_heathBrownPairCountOne
#print axioms mem_heathBrownPairCountTwo
#print axioms heathBrownPairCount_subset_pairCountOne
#print axioms heathBrownPairCount_card_le_pairCountOne_card
#print axioms diagonal_mem_heathBrownPairCountTwo

end

end GafniTao

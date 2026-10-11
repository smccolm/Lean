import Dubon2026.CyclicGeneratorRepeatedPeriod

/-! # Exact original two-cochain periods under actual group and coefficient maps -/

namespace Dubon2026

open scoped BigOperators

/-- Actual restriction precomposition and actual coefficient inclusion
transform a repeated original generator period by the exact repetition factor. -/
theorem representationCyclicPeriod_inflation
    {R G H : Type} [CommRing R] [Group G] [Group H]
    (A : Rep R G) (B : Rep R H) (φ : H →* G) (j : A →ₗ[R] B)
    (g : G) (h : H) (hφ : φ h = g) (n : ℕ) (hn : g ^ n = 1)
    (k : ℕ) (c : G × G → A) :
    representationCyclicTwoCochainPeriodSum B h (n * k)
        (fun p => j (c (φ p.1, φ p.2))) =
      k • j (representationCyclicTwoCochainPeriodSum A g n c) := by
  change (∑ i ∈ Finset.range (n * k), j (c (φ (h ^ i), φ h))) = _
  simp_rw [map_pow, hφ]
  rw [← map_sum]
  change j (representationCyclicTwoCochainPeriodSum A g (n * k) c) = _
  rw [representationCyclicTwoCochainPeriodSum_repeat A g n hn k c, map_nsmul]

end Dubon2026

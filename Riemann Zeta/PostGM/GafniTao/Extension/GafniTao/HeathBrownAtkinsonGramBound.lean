import GafniTao.HeathBrownAtkinsonGram
import GafniTao.HeathBrownAtkinsonBProcess

/-!
# B-process bounds for exact Atkinson Gram entries

This file connects the Gram entry in the finite Bombieri--Halász inequality
to the exact two-height Atkinson phase treated by the B-process.  It preserves
the literal interval `(K, 2K]`, proves the diagonal exactly, and handles both
orders of two distinct heights by complex conjugation.
-/

open Complex Finset
open scoped BigOperators ComplexConjugate

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

/-- The literal Atkinson Gram interval reindexed as a zero-based block. -/
theorem heathBrownAtkinsonGram_eq_positiveDifference_range
    (K : Nat) (t u : Real) :
    heathBrownAtkinsonGram K t u =
      ∑ n ∈ Finset.range K,
        unitaryPhase
          (heathBrownAtkinsonPositiveDifferenceNat t u (K + 1) n) := by
  unfold heathBrownAtkinsonGram
  have hIoc : Finset.Ioc K (2 * K) =
      Finset.Ico (K + 1) (2 * K + 1) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  rw [hIoc, Finset.sum_Ico_eq_sum_range]
  have hLength : 2 * K + 1 - (K + 1) = K := by omega
  rw [hLength]
  apply Finset.sum_congr rfl
  intro n hn
  unfold heathBrownAtkinsonPositiveDifferenceNat
  congr 2

/-- Reversing the two heights conjugates the exact Gram entry. -/
theorem heathBrownAtkinsonGram_swap
    (K : Nat) (t u : Real) :
    heathBrownAtkinsonGram K u t = star (heathBrownAtkinsonGram K t u) := by
  unfold heathBrownAtkinsonGram
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro n hn
  change unitaryPhase
      (heathBrownAtkinsonPhase t n - heathBrownAtkinsonPhase u n) =
    star (unitaryPhase
      (heathBrownAtkinsonPhase u n - heathBrownAtkinsonPhase t n))
  unfold unitaryPhase
  change Complex.exp _ = (starRingEnd Complex) (Complex.exp _)
  rw [← Complex.exp_conj]
  congr 1
  apply Complex.ext <;> simp

theorem norm_heathBrownAtkinsonGram_swap
    (K : Nat) (t u : Real) :
    ‖heathBrownAtkinsonGram K u t‖ = ‖heathBrownAtkinsonGram K t u‖ := by
  rw [heathBrownAtkinsonGram_swap, norm_star]

/-- A diagonal Atkinson Gram entry is exactly the length of `(K,2K]`. -/
theorem heathBrownAtkinsonGram_self
    (K : Nat) (t : Real) :
    heathBrownAtkinsonGram K t t = (K : Complex) := by
  rw [heathBrownAtkinsonGram_eq_positiveDifference_range]
  simp [heathBrownAtkinsonPositiveDifferenceNat, unitaryPhase]

theorem norm_heathBrownAtkinsonGram_self
    (K : Nat) (t : Real) :
    ‖heathBrownAtkinsonGram K t t‖ = K := by
  rw [heathBrownAtkinsonGram_self, Complex.norm_natCast]

/-- The exact B-process estimate for a Gram entry with the larger height in
the first slot.  The hypotheses state precisely the block/height conditions
used in the curvature proof. -/
theorem norm_heathBrownAtkinsonGram_le_of_lt
    {K : Nat} {t u : Real}
    (hu : 0 < u) (htu : u < t) (hK : 0 < K)
    (hblock : ((2 * K + 2 : Nat) : Real) ≤ u)
    (htUpper : t ≤ 2 * u) :
    ‖heathBrownAtkinsonGram K t u‖ ≤
      (((K - 1 : Nat) : Real) *
          heathBrownAtkinsonBProcessLambdaUpper t u (K + 1) (K - 1) /
            (2 * Real.pi) + 2) *
        (2 * Real.pi /
            Real.sqrt
              (heathBrownAtkinsonBProcessLambda t u (K + 1) (K - 1)) +
          2 *
            (Real.sqrt
                (heathBrownAtkinsonBProcessLambda t u (K + 1) (K - 1)) /
              heathBrownAtkinsonBProcessLambda t u (K + 1) (K - 1) + 1)) := by
  rw [heathBrownAtkinsonGram_eq_positiveDifference_range]
  have hRange : K - 1 + 1 = K := by omega
  have hNat : (K + 1) + (K - 1) + 2 = 2 * K + 2 := by omega
  have h := heathBrownAtkinsonPositiveDifference_B_process
    (K := K + 1) (N := K - 1) hu htu (by omega)
    (by simpa only [hNat] using hblock) htUpper
  simpa only [hRange] using h

/-- Symmetric off-diagonal B-process estimate, orienting the two heights by
cases without changing the norm of the Gram entry. -/
theorem norm_heathBrownAtkinsonGram_le_of_ne
    {K : Nat} {t u : Real}
    (ht : 0 < t) (hu : 0 < u) (htu : t ≠ u) (hK : 0 < K)
    (hblockT : ((2 * K + 2 : Nat) : Real) ≤ t)
    (hblockU : ((2 * K + 2 : Nat) : Real) ≤ u)
    (hcomparability : t ≤ 2 * u ∧ u ≤ 2 * t) :
    ‖heathBrownAtkinsonGram K t u‖ ≤
      if u < t then
        (((K - 1 : Nat) : Real) *
            heathBrownAtkinsonBProcessLambdaUpper t u (K + 1) (K - 1) /
              (2 * Real.pi) + 2) *
          (2 * Real.pi /
              Real.sqrt
                (heathBrownAtkinsonBProcessLambda t u (K + 1) (K - 1)) +
            2 *
              (Real.sqrt
                  (heathBrownAtkinsonBProcessLambda t u (K + 1) (K - 1)) /
                heathBrownAtkinsonBProcessLambda t u (K + 1) (K - 1) + 1))
      else
        (((K - 1 : Nat) : Real) *
            heathBrownAtkinsonBProcessLambdaUpper u t (K + 1) (K - 1) /
              (2 * Real.pi) + 2) *
          (2 * Real.pi /
              Real.sqrt
                (heathBrownAtkinsonBProcessLambda u t (K + 1) (K - 1)) +
            2 *
              (Real.sqrt
                  (heathBrownAtkinsonBProcessLambda u t (K + 1) (K - 1)) /
                heathBrownAtkinsonBProcessLambda u t (K + 1) (K - 1) + 1)) := by
  by_cases hut : u < t
  · rw [if_pos hut]
    exact norm_heathBrownAtkinsonGram_le_of_lt hu hut hK hblockU
      hcomparability.1
  · rw [if_neg hut]
    have htu' : t < u := lt_of_le_of_ne (le_of_not_gt hut) htu
    rw [← norm_heathBrownAtkinsonGram_swap K t u]
    exact norm_heathBrownAtkinsonGram_le_of_lt ht htu' hK hblockT
      hcomparability.2


end

end GafniTao

import Dubon2026.PrimeEmpirical
import Dubon2026.BadPrimeDensity
import Dubon2026.SatoTateMeasure
import Dubon2026.SelectedPrimeEnergy

/-! # Positive-density comparable prime blocks from actual Sato–Tate convergence

Arithmetic equidistribution and reality are explicit upstream inputs here.
-/

namespace Dubon2026

open Filter Set MeasureTheory
open scoped Topology

noncomputable section

/-- The actual Sato–Tate mass of the coefficient band 1 ≤ |x| ≤ 2. -/
def satoTateBandDensity : ℝ := ((satoTateProbability : Measure ℝ) satoTateBand).toReal

theorem satoTateBandDensity_pos : 0 < satoTateBandDensity :=
  ENNReal.toReal_pos (ne_of_gt satoTateBand_pos) (measure_ne_top _ _)

theorem norm_eq_abs_re_of_im_zero {z : ℂ} (hz : z.im = 0) : ‖z‖ = |z.re| := by
  have he : z = (z.re : ℂ) := Complex.ext rfl (by simpa using hz)
  rw [he, Complex.norm_real, Real.norm_eq_abs]
  rfl

/-- The exact unramified selection has positive density, derived from weak convergence. -/
theorem sato_tate_selected_prime_density {a : ℕ → ℂ} {Q : ℕ} (hQ : 0 < Q)
    (hreal : ∀ p, Nat.Prime p → ¬p ∣ Q → (a p).im = 0)
    (hST : Tendsto (primeEmpirical (fun p => (a p).re)) atTop (𝓝 satoTateProbability)) :
    Tendsto (fun N : ℕ =>
      ((selectedPrimesUpTo (fun p => ¬p ∣ Q ∧ 1 ≤ ‖a p‖ ∧ ‖a p‖ ≤ 2) N).card : ℝ) /
        Nat.primeCounting N) atTop (𝓝 satoTateBandDensity) := by
  have hd := prime_density_of_empirical_convergence hST measurableSet_satoTateBand
    satoTateBand_null_frontier
  have hh := selected_prime_density_remove_level hQ hd
  apply hh.congr'
  apply Eventually.of_forall
  intro N
  have he : selectedPrimesUpTo (fun p => ¬p ∣ Q ∧ (a p).re ∈ satoTateBand) N =
      selectedPrimesUpTo (fun p => ¬p ∣ Q ∧ 1 ≤ ‖a p‖ ∧ ‖a p‖ ≤ 2) N := by
    apply Finset.ext
    intro p
    simp only [mem_selectedPrimesUpTo]
    constructor
    · rintro ⟨hpN, hp, hbad, hband⟩
      refine ⟨hpN, hp, hbad, ?_⟩
      rw [norm_eq_abs_re_of_im_zero (hreal p hp hbad)]
      exact mem_satoTateBand.mp hband
    · rintro ⟨hpN, hp, hbad, hnorm⟩
      refine ⟨hpN, hp, hbad, ?_⟩
      rw [mem_satoTateBand, ← norm_eq_abs_re_of_im_zero (hreal p hp hbad)]
      exact hnorm
  dsimp only
  rw [he]

/-- All actual H2 requirements are derived from the arithmetic distribution input. -/
theorem sato_tate_selected_primes_H2 {a : ℕ → ℂ} {Q : ℕ} (hQ : 0 < Q)
    (hreal : ∀ p, Nat.Prime p → ¬p ∣ Q → (a p).im = 0)
    (hST : Tendsto (primeEmpirical (fun p => (a p).re)) atTop (𝓝 satoTateProbability)) :
    let B := selectedDyadicPrimes (fun p => ¬p ∣ Q ∧ 1 ≤ ‖a p‖ ∧ ‖a p‖ ≤ 2)
    IsolatedPrimeBlocks B ∧ Tendsto (fun N => (B N).card) atTop atTop ∧
      PrimeCoefficientComparability a B (1 / 2) ∧ IsolatedEnergyAsymptotic a B (1 / 2) :=
  selected_primes_H2 satoTateBandDensity_pos (sato_tate_selected_prime_density hQ hreal hST)
    (fun _ _ hp => hp.2)

end

end Dubon2026

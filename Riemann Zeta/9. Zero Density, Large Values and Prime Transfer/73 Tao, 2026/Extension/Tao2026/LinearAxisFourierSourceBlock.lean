import Tao2026.LinearAxisPrimeSourceBlock
import Tao2026.CoordinateAxisFourierSourceBlock

open ArithmeticFunction Complex Finset Filter Topology
open scoped BigOperators

namespace Tao2026

noncomputable section

/-- The pure-linear prime estimate and its nonstationary integral estimate,
assembled as the literal discrepancy of a Fourier coordinate-axis mode. -/
theorem eventually_norm_primeFourierMode_sub_integral_Ico_le_sourceRange_of_zero_quadratic
    (hVinogradov : VinogradovExponentialSumEstimate)
    {A₀ ε S : ℝ} (hA₀ : 0 < A₀) (hε : 0 < ε)
    (haexp : 0 ≤ 3 / 2 - ε) (hS : 0 ≤ S) :
    ∀ᶠ P : ℕ in atTop, ∀ (a b : ℕ) (q : ℤ × ℤ) (N M L : ℝ),
      P ≤ a → a < b → b ≤ 2 * P →
      (q.1 : ℝ) * N ≠ 0 → (q.2 : ℝ) * M = 0 → 0 < L →
      (Real.log b) ^ vaughanTypeIILogSavingPhaseExponent (S + 1) ≤ L →
      L ≤ reciprocalPhaseScale ((q.1 : ℝ) * N) ((q.2 : ℝ) * M) 2
        (4 * (P : ℝ)) →
      |(q.1 : ℝ) * N| ≤
        A₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
      ‖primeFourierModeSum (P : ℝ)
          (Set.Ico (a : ℝ) (b : ℝ)) q N M 2 -
        fourierModeIntegral (Set.Ico (a : ℝ) (b : ℝ)) q N M 2‖ ≤
        vaughanPrimeQuadraticDecayConstant * (P : ℝ) *
            (Real.log P) ^ (-S) +
          2 * (P : ℝ) / (L * Real.log P) := by
  have hprime :=
    eventually_norm_primeReciprocalPhaseSum_le_sourceRange_zero_quadratic
      hVinogradov hA₀ hε haexp hS
  filter_upwards [hprime, eventually_ge_atTop (2 : ℕ)] with P hprimeP hP
  intro a b q N M L hPa hab hbP hlinear hquadratic hL hlogLower
    hlower hNupper
  have hsum := primeFourierModeSum_Ico_eq_reciprocalPhaseSum
    hP hPa hbP q N M
  have hlower0 : L ≤
      reciprocalPhaseScale ((q.1 : ℝ) * N) 0 2 (4 * (P : ℝ)) := by
    simpa only [hquadratic] using hlower
  have hprimeBound := hprimeP a b ((q.1 : ℝ) * N)
    hPa hab hbP hlinear (hlogLower.trans hlower0) hNupper
  have hintegralBound :=
    norm_fourierModeIntegral_Ico_le_zero_quadratic_sourceScale
      (q := q) (N := N) (M := M) (P := (P : ℝ)) (L := L)
      (a := (a : ℝ)) (b := (b : ℝ)) hlinear hquadratic
      (by exact_mod_cast hP) hL hlower (by exact_mod_cast hPa)
      (by exact_mod_cast hab.le) (by exact_mod_cast hbP)
  rw [hsum]
  simpa only [hquadratic] using
    (norm_sub_le _ _).trans (add_le_add hprimeBound hintegralBound)

end

end Tao2026

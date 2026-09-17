import Tao2026.LowFrequencyPrime
import Tao2026.FourierSourceBlock

/-!
# Low-frequency Fourier-mode endpoint

This module transports the conditional low-frequency prime theorem to the
literal Fourier-mode sum and integral used by the finite Fourier assembly.
It includes the zero mode automatically.
-/

open Complex Finset Filter MeasureTheory Set
open scoped BigOperators Topology

namespace Tao2026

noncomputable section

/-- A Fourier-mode integral on a half-open interval is the corresponding
reciprocal-phase interval integral. -/
theorem fourierModeIntegral_Ico_eq_intervalIntegral
    {a b : ℕ} (hab : a ≤ b) (q : ℤ × ℤ) (N M : ℝ) :
    fourierModeIntegral (Set.Ico (a : ℝ) (b : ℝ)) q N M 2 =
      ∫ t in (a : ℝ)..(b : ℝ),
        standardAdditiveCharacter
          (reciprocalPhase ((q.1 : ℝ) * N) ((q.2 : ℝ) * M) 2 t) /
            Real.log t := by
  unfold fourierModeIntegral
  rw [integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by exact_mod_cast hab)]

/-- Conditional low-frequency estimate for every literal Fourier mode,
including `(0,0)`.  The only analytic hypothesis is the global quantitative
PNT contract. -/
theorem ClassicalMangoldtDiscrepancyLogSaving.eventually_primeFourierMode_sub_integral_Ico_le
    (hPNT : ClassicalMangoldtDiscrepancyLogSaving) (A : ℕ) (T : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ P : ℕ in atTop,
      ∀ (a b : ℕ) (q : ℤ × ℤ) (N M : ℝ),
      P ≤ a → a < b → b ≤ 2 * P →
      ‖primeFourierModeSum (P : ℝ)
          (Set.Ico (a : ℝ) (b : ℝ)) q N M 2 -
        fourierModeIntegral (Set.Ico (a : ℝ) (b : ℝ)) q N M 2‖ ≤
        (1 / Real.log P +
          (2 * Real.pi *
              (3 * reciprocalPhaseScale
                ((q.1 : ℝ) * N) ((q.2 : ℝ) * M) 2 P) /
              Real.log P +
            1 / (Real.log P) ^ 2)) *
            (4 * C * P / (Real.log P) ^ A) +
          (2 * Real.pi *
              (3 * reciprocalPhaseScale
                ((q.1 : ℝ) * N) ((q.2 : ℝ) * M) 2 P) /
              Real.log P +
            1 / (Real.log P) ^ 2) +
          P * (Real.log P) ^ (-T) := by
  obtain ⟨C, hC, hprime⟩ :=
    hPNT.eventually_primeReciprocalPhaseSum_sub_integral_le
      (j := 2) (by omega) A T
  refine ⟨C, hC, ?_⟩
  filter_upwards [hprime, eventually_ge_atTop (2 : ℕ)] with P hprimeP hP
  intro a b q N M hPa hab hbP
  rw [primeFourierModeSum_Ico_eq_reciprocalPhaseSum hP hPa hbP,
    fourierModeIntegral_Ico_eq_intervalIntegral hab.le]
  simpa using hprimeP ((q.1 : ℝ) * N) ((q.2 : ℝ) * M)
    a b hPa hab hbP

/-- Explicit zero-mode specialization of the conditional low-frequency
Fourier theorem. -/
theorem ClassicalMangoldtDiscrepancyLogSaving.eventually_primeFourierMode_zero_sub_integral_Ico_le
    (hPNT : ClassicalMangoldtDiscrepancyLogSaving) (A : ℕ) (T : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ P : ℕ in atTop,
      ∀ (a b : ℕ) (N M : ℝ),
      P ≤ a → a < b → b ≤ 2 * P →
      ‖primeFourierModeSum (P : ℝ)
          (Set.Ico (a : ℝ) (b : ℝ)) ((0, 0) : ℤ × ℤ) N M 2 -
        fourierModeIntegral (Set.Ico (a : ℝ) (b : ℝ))
          ((0, 0) : ℤ × ℤ) N M 2‖ ≤
        (1 / Real.log P + 1 / (Real.log P) ^ 2) *
            (4 * C * P / (Real.log P) ^ A) +
          1 / (Real.log P) ^ 2 +
          P * (Real.log P) ^ (-T) := by
  obtain ⟨C, hC, hmode⟩ :=
    hPNT.eventually_primeFourierMode_sub_integral_Ico_le A T
  refine ⟨C, hC, ?_⟩
  filter_upwards [hmode] with P hmodeP
  intro a b N M hPa hab hbP
  simpa [reciprocalPhaseScale] using
    hmodeP a b ((0, 0) : ℤ × ℤ) N M hPa hab hbP

end

end Tao2026

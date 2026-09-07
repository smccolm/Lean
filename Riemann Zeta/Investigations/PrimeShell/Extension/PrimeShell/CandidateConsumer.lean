import PrimeShell.ExtendedCertificate
import PrimeShell.ExtendedCertificateNumeric
import Zeta23.XiPrime.Final

noncomputable section

open Zeta23

namespace PrimeShell

open Zeta23.XiPrime

/-- The exact zero-side consequence of the certified Prime Shell spectral
value.  The remaining premise is the genuine source-matrix moment
statement for the native zeros of `xi'`; it is displayed here so that the
arithmetic work cannot be confused with the already completed spectral and
zero-side deductions. -/
theorem primeShell_candidate_of_gzMoments
    (hM : GzMoments xiDerivZeros₀
      (fun _ => concretePrimeShellAdmissible.P)
      (kappaXi primeShellLambda vFlat)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((2 / 3 : ℝ) + 1 / 100 - ε) *
          (Zeta23.XiPrime.Ncount T (2 * T) : ℝ) ≤
        Zeta23.XiPrime.N0simple T (2 * T) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ :=
    concretePrimeShellAdmissible.simple_bound_of_gzMoments
      xiDerivZeros₀ xiDerivZeros₀_rvm hM ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  have hsource := hT₀ T hT
  have hN : 0 ≤ (Zeta23.XiPrime.Ncount T (2 * T) : ℝ) := Nat.cast_nonneg _
  have hcoeff :
      (2 / 3 : ℝ) + 1 / 100 - ε ≤
        2 - kappaXi primeShellLambda vFlat - ε := by
    linarith [two_thirds_add_one_hundredth_lt_primeShell_output]
  have hleft :
      ((2 / 3 : ℝ) + 1 / 100 - ε) *
          (Zeta23.XiPrime.Ncount T (2 * T) : ℝ) ≤
        (2 - kappaXi primeShellLambda vFlat - ε) *
          (Zeta23.XiPrime.Ncount T (2 * T) : ℝ) :=
    mul_le_mul_of_nonneg_right hcoeff hN
  exact hleft.trans (by
    simpa [xiDerivZeros₀] using hsource)

end PrimeShell

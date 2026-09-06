import GafniTao.Pintz2023ShellToGlobal

/-!
# Pintz's published `23/24` cutoff

This is the source consumer needed in Gafni--Tao Section 3.  It chooses the
actual adjacent Pintz cells, applies the native 2023 detector theorem, and
then uses the cell arithmetic to obtain coefficient one.
-/

namespace GafniTao

noncomputable section

/-- The strict `sigma > 23/24` Pintz zero-density cutoff, with the project's
actual symmetric multiplicity-weighted zeta-zero count. -/
theorem pintzTwentyThreeTwentyFourCutoff_native :
    PintzTwentyThreeTwentyFourCutoff := by
  intro sigma hsigmaLower hsigmaUpper
  let eta : ℝ := 1 - sigma
  have heta : 0 < eta := by dsimp only [eta]; linarith
  have hetaUpper : eta < 1 / 24 := by dsimp only [eta]; linarith
  have hetaTwelve : eta < 1 / 12 := by linarith
  obtain ⟨k, ell, hcell⟩ := exists_pintzCell heta hetaTwelve
  have hEnvelope := pintz2023_nearOneDensity_native hcell hetaUpper
  have hSharpPrime :
      pintzTheoremOneCoefficient eta k ell ≤
        pintzTheoremOnePrimeCoefficient k ell :=
    pintzTheoremOneCoefficient_le_prime hcell
  have hPrimeOne : pintzTheoremOnePrimeCoefficient k ell ≤ 1 :=
    pintzTheoremOnePrimeCoefficient_le_one heta hetaUpper hcell
  have hCoeff : pintzTheoremOneCoefficient eta k ell ≤ 1 :=
    hSharpPrime.trans hPrimeOne
  unfold ZeroDensityEnvelope
  simpa only [eta, sub_sub_cancel, mul_one, one_mul] using
    hEnvelope.mono_exponent
      (mul_le_mul_of_nonneg_left hCoeff heta.le)

#print axioms pintzTwentyThreeTwentyFourCutoff_native

end

end GafniTao

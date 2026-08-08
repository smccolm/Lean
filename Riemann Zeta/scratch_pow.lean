import RiemannZeta.GuthMaynard.PolynomialPowers

open Complex Finset RiemannZeta.GuthMaynard
open scoped BigOperators

/-- Scratch spelling of the canonical convolution coefficient, retained for
    experiments with an explicit coefficient expansion of `powPoly`. -/
noncomputable def powCoeff_alt (N k m : ℕ) (T : ℝ) : ℂ :=
  ∑ p ∈ (Fintype.piFinset (fun (_ : Fin k) => Finset.Ioc N (2 * N))).filter
      (fun p => (∏ x : Fin k, p x) = m),
    ∏ x : Fin k, detectorCoeff (p x) T

lemma powCoeff_alt_eq_powCoeff (N k m : ℕ) (T : ℝ) :
    powCoeff_alt N k m T = powCoeff N k m T := by
  rfl

/-- Candidate explicit coefficient expansion. No equality with the structural
    power `powPoly` is claimed until the regrouping proof is complete. -/
noncomputable def powPoly_alt (N k : ℕ) (s : ℂ) (T : ℝ) : ℂ :=
  ∑ m ∈ Finset.Icc (N ^ k) ((2 * N) ^ k),
    powCoeff_alt N k m T * (m : ℂ) ^ (-s)

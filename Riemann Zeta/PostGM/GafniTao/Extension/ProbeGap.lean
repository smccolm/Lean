import GafniTao.FordExplicitData.GapCertificate
import GafniTao.FordPositiveIntegralFormula

open GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

def probeEval (p : Polynomial ℚ) (x : ℚ) : ℚ := Polynomial.eval x p
theorem probeEval_eq (p : Polynomial ℚ) (x : ℚ) :
    probeEval p x = p.eval x := rfl
attribute [irreducible] probeEval

structure ProbeGapBundle where
  source : Polynomial ℚ
  explicit : Polynomial ℚ
  source_eq : source = fordNumericalGap
  explicit_eq : explicit = fordNumericalGapCertificate

opaque probeGapBundle : ProbeGapBundle :=
  ⟨fordNumericalGap, fordNumericalGapCertificate, rfl, rfl⟩

example : probeEval probeGapBundle.source 0 =
    probeEval probeGapBundle.explicit 0 := by
  rw [probeGapBundle.source_eq, probeGapBundle.explicit_eq]
  rw [probeEval_eq, probeEval_eq]
  unfold fordNumericalGap fordNumericalNumerator fordNumericalCompactPolynomial
  rw [fordPositiveIntegral_source_eq_formula,
    fordNegativeUpperPolynomial_eq_explicit]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_add]
  have hneg : Polynomial.eval 0
      (fordBiDiagonal (fordBiIntegralPolynomial fordNegativeUpperExplicit)) = 0 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero]
    unfold fordBiDiagonal fordBiIntegralPolynomial
    simp [Polynomial.eval_eq_sum, Polynomial.sum_def]
  rw [hneg]
  have hpos : Polynomial.eval 0
      (fordPositiveIntegralFormula fordPositiveTaylorPower11) =
        Polynomial.eval 0 fordPositiveAtThreeHalvesExplicit := by
    norm_num [fordPositiveIntegralFormula, fordPositiveLiftTerm,
      fordPositiveTaylorPower11, fordPositivePhasePolynomial,
      fordBiIntegralPolynomial, fordBiEvalV, fordBiRat, fordBiY, fordBiV,
      Polynomial.sum_def, Polynomial.eval_eq_sum, Finset.sum_range_succ,
      fordPositiveAtThreeHalvesExplicit]
  rw [hpos]

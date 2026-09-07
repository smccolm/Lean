import GafniTao.Pintz2023Equation47TruncationBound

open Complex Set
open RiemannZeta.GuthMaynard
open scoped ArithmeticFunction.Moebius BigOperators

#check LSeries.hasDerivAt_term
#check LSeries.term_def₀
#check MeasureTheory.integral_congr_ae
#check Filter.Eventually.of_forall

example (n : ℕ) (rho s : ℂ) :
    DifferentiableAt ℂ
      (fun z : ℂ => ((ArithmeticFunction.moebius n : ℤ) : ℂ) *
        (n : ℂ) ^ (-(rho + z))) s := by
  have h :=
    ((LSeries.hasDerivAt_term
      (fun m => ((ArithmeticFunction.moebius m : ℤ) : ℂ)) n (rho + s)).differentiableAt.comp
        s ((differentiableAt_const rho).add differentiableAt_id))
  convert h using 1
  funext z
  simp only [Function.comp_apply]
  rw [LSeries.term_def₀ (by simp)]

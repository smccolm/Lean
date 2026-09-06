import GafniTao.Pintz2023Equation416

/-!
# Pintz (2023), equation (4.17)

This file removes the line-normalization introduced solely for the second
dyadic pigeonhole.  The result is the literal common arithmetic coefficient
against the zero-dependent complex exponent used by the Halász--Montgomery
argument.  No absolute values or phases are discarded in this rewrite.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

/-- Exact phase recombination in Pintz (4.17). -/
theorem dirichletPoly_pintz2023SmallMPoweredLineCoeff_eq_equation417
    (X h N : ℕ) (R beta t : ℝ) (baseI : Finset ℕ) :
    dirichletPoly N
        (pintz2023SmallMPoweredLineCoeff X R baseI h beta) t =
      ∑ n ∈ dyadicInterval N,
        pintz2023SmallMIntervalPowerCoeff X R baseI h n *
          (n : ℂ) ^
            (-(((beta : ℝ) : ℂ) + I * ((t : ℝ) : ℂ))) := by
  unfold dirichletPoly pintz2023SmallMPoweredLineCoeff
  apply Finset.sum_congr rfl
  intro n hn
  have hnPos : 0 < n := by
    rw [dyadicInterval, Finset.mem_Ioc] at hn
    omega
  have hnNe : (n : ℂ) ≠ 0 := by exact_mod_cast hnPos.ne'
  rw [mul_assoc, ← Complex.cpow_add _ _ hnNe]
  congr 2
  ring

#print axioms dirichletPoly_pintz2023SmallMPoweredLineCoeff_eq_equation417

end

end GafniTao

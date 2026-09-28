import TaoTrudgianYang2025

noncomputable section

#print axioms TaoTrudgianYang2025.HuxleyModel.tests_monomial
#print axioms TaoTrudgianYang2025.HuxleyModel.tests_monomial_ne_zero
#print axioms TaoTrudgianYang2025.HuxleyModel.continuous_tests
#print axioms TaoTrudgianYang2025.HuxleyModel.referenceJets_eq
#print axioms TaoTrudgianYang2025.HuxleyModel.reference_tests_ne_zero
#print axioms TaoTrudgianYang2025.HuxleyModel.continuousOn_referenceJets
#print axioms TaoTrudgianYang2025.HuxleyModel.exists_uniform_test_lower
#print axioms TaoTrudgianYang2025.HuxleyModel.approximateModelPhase_tests_uniform
#print axioms TaoTrudgianYang2025.HuxleyModel.iteratedDeriv_two_log_jet
#print axioms TaoTrudgianYang2025.HuxleyModel.approximateModelPhase_source_tests
#print axioms TaoTrudgianYang2025.HuxleyModel.aProcessShiftPhase_tests_uniform

namespace HuxleyModelRegression

open TaoTrudgianYang2025.HuxleyModel Expdb Set

-- The seventh test retains every entry of the literal printed determinant.
example (a b c d : ℝ) : tests ![a,b,c,d] 6 =
    Matrix.det ![![3*b^2+4*a*c,3*a*b,a^2],![c,b,a],![d,c,b]] := rfl

-- The logarithmic phase has both negative and positive derivative signs.
example : tests ![(2:ℝ),-6,24,-120] = ![2,-6,24,12,144,60,-720] := by
  convert tests_monomial 3 2 1 using 1 <;> norm_num

-- Strictly positive model parameter is necessary for this nondegeneracy claim.
example : tests (0 : Fin 4 → ℝ) = 0 := by
  funext i
  fin_cases i <;> norm_num [tests,Matrix.det_fin_three]

-- One delta and one c precede every phase and every CLOSED-interval point.
example {σ : ℝ} (hσ : 0 < σ) :
    ∃ δ c : ℝ, 0 < δ ∧ 0 < c ∧
      ∀ F : ℝ → ℝ, IsApproximateModelPhaseFunction F σ 5 δ →
        ∀ x ∈ phaseInterval, ∀ j,
          c ≤ |tests (fun i : Fin 4 => iteratedDerivWithin (i.val+3) F phaseInterval x) j| :=
  approximateModelPhase_tests_uniform hσ

-- The ordinary derivative/logarithmic bridge claims only the actual interior.
example {σ : ℝ} (hσ : 0 < σ) :
    ∃ δ c : ℝ, 0 < δ ∧ 0 < c ∧
      ∀ F : ℝ → ℝ, IsApproximateModelPhaseFunction F σ 5 δ →
        ∀ x ∈ Ioo (1 : ℝ) 2,
          (∀ j, c ≤ |tests (fun i : Fin 4 => iteratedDeriv (i.val+3) F x) j|) ∧
          (∀ r : ℕ, 3 ≤ r → r ≤ 4 →
            iteratedDeriv 2 (fun u => Real.log (iteratedDeriv r F u)) x ≠ 0) :=
  approximateModelPhase_source_tests hσ

end HuxleyModelRegression

-- Every actual domain-preserving A-process shift has the same test lower bound.
example {σ : ℝ} (hσ : 0 < σ) :
    ∃ δ η₀ c : ℝ, 0 < δ ∧ 0 < η₀ ∧ η₀ ≤ 1/2 ∧ 0 < c ∧
      ∀ F : ℝ → ℝ, Expdb.IsApproximateModelPhaseFunction F σ 6 δ →
        ∀ η : ℝ, 0 < η → η ≤ η₀ → ∀ x ∈ Expdb.phaseInterval, ∀ j,
          c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
            (fun i : Fin 4 => iteratedDerivWithin (i.val+3)
              (TaoTrudgianYang2025.aProcessShiftPhase F σ η) Expdb.phaseInterval x) j| :=
  TaoTrudgianYang2025.HuxleyModel.aProcessShiftPhase_tests_uniform hσ

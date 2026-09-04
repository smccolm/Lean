import GafniTao.HeathBrownTrivialBranches

/-!
# Heath-Brown Theorem 1 from the critical Vinogradov mean value theorem

All technical branches are discharged here.  The only remaining upstream
input is the exact critical VMVT estimate explicitly displayed in the theorem
signature; the following public theorem then packages the source argument as
`HeathBrownVMVTMainConjecture → HeathBrownKthDerivativeTheorem`.
-/

namespace GafniTao

noncomputable section

noncomputable def heathBrownQuarterLambdaBase (A : ℝ) : ℝ :=
  (1 / 4 : ℝ) / A

noncomputable def heathBrownSmallHBase (k : ℕ) (A : ℝ) : ℝ :=
  (8 : ℝ) ^ (-(k : ℝ)) / A

noncomputable def heathBrownLongHBase (k : ℕ) (A : ℝ) : ℝ :=
  (A ^ (1 / (k : ℝ)) / 2) ^
    (2 * heathBrownCriticalReciprocal k)

noncomputable def heathBrownGlobalConstant
    (k : ℕ) (A C epsilon : ℝ) : ℝ :=
  2 + heathBrownLemmaOneGoodConstant k A C epsilon +
    ((heathBrownQuarterLambdaBase A) ^
      heathBrownCriticalReciprocal k)⁻¹ +
    ((heathBrownSmallHBase k A) ^
      heathBrownCriticalReciprocal k)⁻¹ +
    (heathBrownLongHBase k A)⁻¹

theorem heathBrownQuarterLambdaBase_pos
    {A : ℝ} (hA : 0 < A) : 0 < heathBrownQuarterLambdaBase A := by
  unfold heathBrownQuarterLambdaBase
  positivity

theorem heathBrownSmallHBase_pos
    {k : ℕ} {A : ℝ} (hA : 0 < A) :
    0 < heathBrownSmallHBase k A := by
  unfold heathBrownSmallHBase
  positivity

theorem heathBrownLongHBase_pos
    {k : ℕ} {A : ℝ} (hA : 0 < A) :
    0 < heathBrownLongHBase k A := by
  unfold heathBrownLongHBase
  positivity

theorem heathBrownKthDerivativeFactor_nonneg
    (k : ℕ) {N lambda : ℝ} (hN : 0 ≤ N) (hlambda : 0 < lambda) :
    0 ≤ heathBrownKthDerivativeFactor k N lambda := by
  unfold heathBrownKthDerivativeFactor
  positivity

theorem heathBrown_scaled_factor_nonneg
    (k : ℕ) {N lambda epsilon : ℝ}
    (hN : 0 ≤ N) (hlambda : 0 < lambda) :
    0 ≤ N ^ (1 + epsilon) * heathBrownKthDerivativeFactor k N lambda :=
  mul_nonneg (Real.rpow_nonneg hN _)
    (heathBrownKthDerivativeFactor_nonneg k hN hlambda)

theorem heathBrownGlobalConstant_pos
    {k : ℕ} {A C epsilon : ℝ}
    (hk : 3 ≤ k) (hA : 0 < A) (hC : 0 < C) (hepsilon : 0 < epsilon) :
    0 < heathBrownGlobalConstant k A C epsilon := by
  unfold heathBrownGlobalConstant
  have hgood := heathBrownLemmaOneGoodConstant_pos hk hA hC hepsilon
  have hquarter := heathBrownQuarterLambdaBase_pos hA
  have hsmallH := heathBrownSmallHBase_pos (k := k) hA
  have hlongH := heathBrownLongHBase_pos (k := k) hA
  positivity

private theorem bound_lift_to_global
    {k : ℕ} {A C epsilon coefficient target value : ℝ}
    (hcomponent : coefficient ≤ heathBrownGlobalConstant k A C epsilon)
    (htarget : 0 ≤ target) (hvalue : value ≤ coefficient * target) :
    value ≤ heathBrownGlobalConstant k A C epsilon * target :=
  hvalue.trans (mul_le_mul_of_nonneg_right hcomponent htarget)

/-- Fully assembled source theorem for a supplied critical VMVT constant. -/
theorem norm_heathBrownExponentialSum_le_factor_of_critical_vmvt
    {N k : ℕ} {f : ℝ → ℝ} {A lambda epsilon C : ℝ}
    (hk : 3 ≤ k) (hN : 1 ≤ N) (hA : 0 < A) (hlambda : 0 < lambda)
    (hepsilon : 0 < epsilon)
    (_hfContinuous : ContinuousOn f (Set.Icc 0 (N : ℝ)))
    (hf : ContDiffOn ℝ k f (Set.Ioo 0 (N : ℝ)))
    (hkBounds : ∀ x ∈ Set.Ioo (0 : ℝ) (N : ℝ),
      lambda ≤ iteratedDeriv k f x ∧
        iteratedDeriv k f x ≤ A * lambda)
    (hC : 0 < C)
    (hVMVT : FordVinogradovMomentBound
      (heathBrownCriticalMoment k) (k - 1) C
        (epsilon * (heathBrownCriticalMoment k : ℝ))) :
    ‖heathBrownExponentialSum N f‖ ≤
      heathBrownGlobalConstant k A C epsilon *
        (N : ℝ) ^ (1 + epsilon) *
          heathBrownKthDerivativeFactor k N lambda := by
  let target := (N : ℝ) ^ (1 + epsilon) *
    heathBrownKthDerivativeFactor k N lambda
  have htarget : 0 ≤ target := by
    dsimp only [target]
    exact heathBrown_scaled_factor_nonneg k (by positivity) hlambda
  have hgood0 : 0 ≤ heathBrownLemmaOneGoodConstant k A C epsilon :=
    (heathBrownLemmaOneGoodConstant_pos hk hA hC hepsilon).le
  have hquarterPos := heathBrownQuarterLambdaBase_pos hA
  have hsmallHPos := heathBrownSmallHBase_pos (k := k) hA
  have hlongHPos := heathBrownLongHBase_pos (k := k) hA
  have hquarterCoeff0 : 0 ≤
      ((heathBrownQuarterLambdaBase A) ^
        heathBrownCriticalReciprocal k)⁻¹ := by positivity
  have hsmallHCoeff0 : 0 ≤
      ((heathBrownSmallHBase k A) ^
        heathBrownCriticalReciprocal k)⁻¹ := by positivity
  have hlongHCoeff0 : 0 ≤ (heathBrownLongHBase k A)⁻¹ := by positivity
  have htwoGlobal : (2 : ℝ) ≤ heathBrownGlobalConstant k A C epsilon := by
    unfold heathBrownGlobalConstant
    linarith
  have hgoodGlobal : heathBrownLemmaOneGoodConstant k A C epsilon ≤
      heathBrownGlobalConstant k A C epsilon := by
    unfold heathBrownGlobalConstant
    linarith
  have hquarterGlobal :
      ((heathBrownQuarterLambdaBase A) ^
        heathBrownCriticalReciprocal k)⁻¹ ≤
      heathBrownGlobalConstant k A C epsilon := by
    unfold heathBrownGlobalConstant
    linarith
  have hsmallHGlobal :
      ((heathBrownSmallHBase k A) ^
        heathBrownCriticalReciprocal k)⁻¹ ≤
      heathBrownGlobalConstant k A C epsilon := by
    unfold heathBrownGlobalConstant
    linarith
  have hlongHGlobal : (heathBrownLongHBase k A)⁻¹ ≤
      heathBrownGlobalConstant k A C epsilon := by
    unfold heathBrownGlobalConstant
    linarith
  by_cases hNlarge : 3 ≤ N
  · by_cases hlambdaOne : lambda ≤ 1
    · by_cases hsmall : A * lambda ≤ 1 / 4
      · by_cases hlargeH : 8 ≤ heathBrownHChoice k A lambda
        · by_cases hHN : heathBrownHChoice k A lambda ≤ N - 2
          · have hgood := norm_heathBrownExponentialSum_le_factor_good_of_vmvt
              hk hNlarge hA hlambda hlambdaOne hepsilon hsmall hlargeH hHN
              hf hkBounds hC hVMVT
            have hgood' : ‖heathBrownExponentialSum N f‖ ≤
                heathBrownLemmaOneGoodConstant k A C epsilon * target := by
              simpa only [target, mul_assoc] using hgood
            simpa only [target, mul_assoc] using
              (bound_lift_to_global hgoodGlobal htarget hgood')
          · have hHN' : N - 2 < heathBrownHChoice k A lambda :=
              lt_of_not_ge hHN
            have hthird := heathBrown_third_lower_of_H_gt_N_sub_two
              hNlarge hk hA hlambda hHN'
            have hbound := norm_heathBrownExponentialSum_le_of_third_lower
              hN hk f hlambda hepsilon hlongHPos hthird
            have hbound' : ‖heathBrownExponentialSum N f‖ ≤
                (heathBrownLongHBase k A)⁻¹ * target := by
              simpa only [target, mul_assoc] using hbound
            simpa only [target, mul_assoc] using
              (bound_lift_to_global hlongHGlobal htarget hbound')
        · have hHlt : heathBrownHChoice k A lambda < 8 :=
            lt_of_not_ge hlargeH
          have hlowerStrict := heathBrown_lambda_lower_of_H_lt_eight
            hk hA hlambda hHlt
          have hbound := norm_heathBrownExponentialSum_le_of_lambda_lower
            hN hk f hlambda hepsilon hsmallHPos hlowerStrict.le
          have hbound' : ‖heathBrownExponentialSum N f‖ ≤
              ((heathBrownSmallHBase k A) ^
                heathBrownCriticalReciprocal k)⁻¹ * target := by
            simpa only [target, mul_assoc] using hbound
          simpa only [target, mul_assoc] using
            (bound_lift_to_global hsmallHGlobal htarget hbound')
      · have hAlambda : (1 / 4 : ℝ) < A * lambda := lt_of_not_ge hsmall
        have hlower : heathBrownQuarterLambdaBase A < lambda := by
          unfold heathBrownQuarterLambdaBase
          exact (div_lt_iff₀ hA).2 (by simpa only [mul_comm] using hAlambda)
        have hbound := norm_heathBrownExponentialSum_le_of_lambda_lower
          hN hk f hlambda hepsilon hquarterPos hlower.le
        have hbound' : ‖heathBrownExponentialSum N f‖ ≤
            ((heathBrownQuarterLambdaBase A) ^
              heathBrownCriticalReciprocal k)⁻¹ * target := by
          simpa only [target, mul_assoc] using hbound
        simpa only [target, mul_assoc] using
          (bound_lift_to_global hquarterGlobal htarget hbound')
    · have hlower : (1 : ℝ) ≤ lambda := le_of_not_ge hlambdaOne
      have hbound := norm_heathBrownExponentialSum_le_of_lambda_lower
        hN hk f hlambda hepsilon (by norm_num : (0 : ℝ) < 1) hlower
      have hbound' : ‖heathBrownExponentialSum N f‖ ≤ target := by
        simpa only [Real.one_rpow, inv_one, one_mul, target] using hbound
      have hfinal := hbound'.trans (by
        change target ≤ heathBrownGlobalConstant k A C epsilon * target
        have hglobalOne : (1 : ℝ) ≤ heathBrownGlobalConstant k A C epsilon :=
          le_trans (by norm_num) htwoGlobal
        nlinarith)
      simpa only [target, mul_assoc] using hfinal
  · have hNsmall : N < 3 := lt_of_not_ge hNlarge
    have hbound := norm_heathBrownExponentialSum_le_small_N_factor
      hN hNsmall hk f hlambda hepsilon
    have hbound' : ‖heathBrownExponentialSum N f‖ ≤ 2 * target := by
      simpa only [target, mul_assoc] using hbound
    simpa only [target, mul_assoc] using
      (bound_lift_to_global htwoGlobal htarget hbound')

/-- Heath-Brown Theorem 1, conditional only on its genuine upstream VMVT
main-conjecture theorem. -/
theorem heathBrownKthDerivativeTheorem_of_vmvt
    (hVMVT : HeathBrownVMVTMainConjecture) :
    HeathBrownKthDerivativeTheorem := by
  intro k A epsilon hk hA hepsilon
  have hsPos : (0 : ℝ) < heathBrownCriticalMoment k :=
    heathBrownCriticalMoment_pos (by omega : 2 ≤ k)
  obtain ⟨C, hC, hcritical⟩ := hVMVT.critical
    (by omega : 2 ≤ k) (mul_pos hepsilon hsPos)
  refine ⟨heathBrownGlobalConstant k A C epsilon,
    heathBrownGlobalConstant_pos hk hA hC hepsilon, ?_⟩
  intro N lambda f hN hlambda hfContinuous hfDiff hkBounds
  exact norm_heathBrownExponentialSum_le_factor_of_critical_vmvt
    hk hN hA hlambda hepsilon hfContinuous hfDiff hkBounds hC hcritical

#print axioms heathBrownQuarterLambdaBase_pos
#print axioms heathBrownSmallHBase_pos
#print axioms heathBrownLongHBase_pos
#print axioms heathBrownKthDerivativeFactor_nonneg
#print axioms heathBrown_scaled_factor_nonneg
#print axioms heathBrownGlobalConstant_pos
#print axioms norm_heathBrownExponentialSum_le_factor_of_critical_vmvt
#print axioms heathBrownKthDerivativeTheorem_of_vmvt

end

end GafniTao

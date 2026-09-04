import GafniTao.HeathBrownFactorAlignment

/-!
# The source final case split for Heath-Brown Lemma 1

If the third critical monomial exceeds `N`, the trivial exponential-sum
bound already proves Theorem 1.  Otherwise the preceding algebra shows that
the auxiliary `lambda^(-1/k)` term is dominated by that same monomial.
-/

namespace GafniTao

noncomputable section

noncomputable def heathBrownThirdTerm
    (N k : ℕ) (lambda : ℝ) : ℝ :=
  let r := heathBrownCriticalReciprocal k
  (N : ℝ) ^ (1 - 2 * r) *
    lambda ^ (-2 * r / (k : ℝ))

noncomputable def heathBrownLemmaOneGoodConstant
    (k : ℕ) (A C epsilon : ℝ) : ℝ :=
  1 + 2 * heathBrownLemmaOneFourTermConstant k A C epsilon

theorem heathBrownThirdTerm_le_threeTerm
    {N k : ℕ} (hN : 1 ≤ N) {lambda : ℝ} (hlambda : 0 < lambda) :
    heathBrownThirdTerm N k lambda ≤ heathBrownThreeTerm N k lambda := by
  unfold heathBrownThirdTerm heathBrownThreeTerm
  dsimp only
  have hfirst : 0 ≤
      (N : ℝ) ^ (1 - heathBrownCriticalReciprocal k) := by positivity
  have hmiddle : 0 ≤
      (N : ℝ) * lambda ^ heathBrownCriticalReciprocal k := by positivity
  linarith

theorem heathBrownFourTerm_le_two_threeTerm
    {N k : ℕ} (hN : 1 ≤ N) (hk : 3 ≤ k)
    {lambda : ℝ} (hlambda : 0 < lambda)
    (hthird : heathBrownThirdTerm N k lambda ≤ N) :
    heathBrownFourTerm N k lambda ≤
      2 * heathBrownThreeTerm N k lambda := by
  have hlambdaTerm := heathBrown_lambda_term_le_third_of_third_le_N
    hN hk hlambda (by simpa only [heathBrownThirdTerm] using hthird)
  have hthirdThree := heathBrownThirdTerm_le_threeTerm (k := k) hN hlambda
  have hlambdaThree : lambda ^ (-(1 / (k : ℝ))) ≤
      heathBrownThreeTerm N k lambda :=
    hlambdaTerm.trans (by
      simpa only [heathBrownThirdTerm] using hthirdThree)
  unfold heathBrownFourTerm
  linarith

theorem heathBrownLemmaOneGoodConstant_pos
    {k : ℕ} {A C epsilon : ℝ}
    (hk : 3 ≤ k) (hA : 0 < A) (hC : 0 < C) (hepsilon : 0 < epsilon) :
    0 < heathBrownLemmaOneGoodConstant k A C epsilon := by
  unfold heathBrownLemmaOneGoodConstant
  have := heathBrownLemmaOneFourTermConstant_pos hk hA hC hepsilon
  positivity

theorem norm_heathBrownExponentialSum_le_factor_good_of_vmvt
    {N k : ℕ} {f : ℝ → ℝ} {A lambda epsilon C : ℝ}
    (hk : 3 ≤ k) (hN : 3 ≤ N) (hA : 0 < A) (hlambda : 0 < lambda)
    (hlambdaOne : lambda ≤ 1) (hepsilon : 0 < epsilon)
    (hsmall : A * lambda ≤ 1 / 4)
    (hlargeH : 8 ≤ heathBrownHChoice k A lambda)
    (hHN : heathBrownHChoice k A lambda ≤ N - 2)
    (hf : ContDiffOn ℝ k f (Set.Ioo 0 (N : ℝ)))
    (hkBounds : ∀ x ∈ Set.Ioo (0 : ℝ) (N : ℝ),
      lambda ≤ iteratedDeriv k f x ∧
        iteratedDeriv k f x ≤ A * lambda)
    (hC : 0 < C)
    (hVMVT : FordVinogradovMomentBound
      (heathBrownCriticalMoment k) (k - 1) C
        (epsilon * (heathBrownCriticalMoment k : ℝ))) :
    ‖heathBrownExponentialSum N f‖ ≤
      heathBrownLemmaOneGoodConstant k A C epsilon *
        (N : ℝ) ^ (1 + epsilon) *
          heathBrownKthDerivativeFactor k N lambda := by
  have hNOne : 1 ≤ N := by omega
  have hscaleIdentity := heathBrownThreeTerm_scaled_identity
    hNOne (by omega : 2 ≤ k) lambda epsilon
  by_cases hthird : heathBrownThirdTerm N k lambda ≤ (N : ℝ)
  · have hfour := norm_heathBrownExponentialSum_le_fourTerm_open_of_vmvt
      hk hN hA hlambda hlambdaOne hepsilon hsmall hlargeH hHN hf hkBounds hC hVMVT
    have hfourTerms := heathBrownFourTerm_le_two_threeTerm
      hNOne hk hlambda hthird
    have hCfour0 : 0 ≤
        heathBrownLemmaOneFourTermConstant k A C epsilon :=
      (heathBrownLemmaOneFourTermConstant_pos hk hA hC hepsilon).le
    have hproduct0 : 0 ≤
        (N : ℝ) ^ epsilon * heathBrownThreeTerm N k lambda :=
      mul_nonneg (by positivity)
        (heathBrownThreeTerm_pos (k := k) hNOne hlambda).le
    calc
      ‖heathBrownExponentialSum N f‖ ≤
          heathBrownLemmaOneFourTermConstant k A C epsilon *
            (N : ℝ) ^ epsilon * heathBrownFourTerm N k lambda := hfour
      _ ≤ heathBrownLemmaOneFourTermConstant k A C epsilon *
            (N : ℝ) ^ epsilon *
              (2 * heathBrownThreeTerm N k lambda) := by gcongr
      _ = 2 * heathBrownLemmaOneFourTermConstant k A C epsilon *
            ((N : ℝ) ^ epsilon * heathBrownThreeTerm N k lambda) := by ring
      _ ≤ heathBrownLemmaOneGoodConstant k A C epsilon *
            ((N : ℝ) ^ epsilon * heathBrownThreeTerm N k lambda) := by
        have hfourPos := heathBrownLemmaOneFourTermConstant_pos
          hk hA hC hepsilon
        unfold heathBrownLemmaOneGoodConstant
        exact mul_le_mul_of_nonneg_right (by linarith) hproduct0
      _ = heathBrownLemmaOneGoodConstant k A C epsilon *
            (N : ℝ) ^ (1 + epsilon) *
              heathBrownKthDerivativeFactor k N lambda := by
        rw [hscaleIdentity]
        ring
  · have hthirdStrict : (N : ℝ) < heathBrownThirdTerm N k lambda :=
      lt_of_not_ge hthird
    have htrivial := norm_heathBrownExponentialSum_le N f
    have hthree := heathBrownThirdTerm_le_threeTerm (k := k) hNOne hlambda
    have hNone : (1 : ℝ) ≤ (N : ℝ) ^ epsilon :=
      Real.one_le_rpow (by exact_mod_cast hNOne) hepsilon.le
    have hthree0 := (heathBrownThreeTerm_pos (k := k) hNOne hlambda).le
    calc
      ‖heathBrownExponentialSum N f‖ ≤ (N : ℝ) := by exact_mod_cast htrivial
      _ ≤ heathBrownThreeTerm N k lambda := hthirdStrict.le.trans hthree
      _ ≤ (N : ℝ) ^ epsilon * heathBrownThreeTerm N k lambda := by
        nlinarith
      _ ≤ heathBrownLemmaOneGoodConstant k A C epsilon *
            ((N : ℝ) ^ epsilon * heathBrownThreeTerm N k lambda) := by
        have hgoodOne : 1 ≤ heathBrownLemmaOneGoodConstant k A C epsilon := by
          unfold heathBrownLemmaOneGoodConstant
          have hfourPos := heathBrownLemmaOneFourTermConstant_pos
            hk hA hC hepsilon
          nlinarith
        nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ epsilon)
          hthree0]
      _ = heathBrownLemmaOneGoodConstant k A C epsilon *
            (N : ℝ) ^ (1 + epsilon) *
              heathBrownKthDerivativeFactor k N lambda := by
        rw [hscaleIdentity]
        ring

#print axioms heathBrownThirdTerm_le_threeTerm
#print axioms heathBrownFourTerm_le_two_threeTerm
#print axioms heathBrownLemmaOneGoodConstant_pos
#print axioms norm_heathBrownExponentialSum_le_factor_good_of_vmvt

end

end GafniTao

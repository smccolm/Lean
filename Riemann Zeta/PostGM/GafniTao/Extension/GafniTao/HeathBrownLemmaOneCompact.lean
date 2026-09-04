import GafniTao.HeathBrownLemmaOneSourceScale

/-!
# Heath-Brown Lemma 1 on a compact interior interval

This is the first theorem in the chain whose left side is the actual source
exponential sum.  It consumes the critical Vinogradov mean-value estimate,
the derivative-pair count, and the exact finite averaging argument.
-/

namespace GafniTao

noncomputable section

theorem norm_heathBrownExponentialSum_le_sourceScale_of_vmvt
    {U : Set ℝ} (hU : IsOpen U)
    {N k : ℕ} {f : ℝ → ℝ} {A lambda epsilon C : ℝ}
    (hk : 3 ≤ k) (hN : 1 ≤ N) (hA : 0 < A) (hlambda : 0 < lambda)
    (hlambdaOne : lambda ≤ 1) (hepsilon : 0 < epsilon)
    (hsmall : A * lambda ≤ 1 / 4)
    (hlargeH : 8 ≤ heathBrownHChoice k A lambda)
    (hHN : heathBrownHChoice k A lambda ≤ N)
    (hf : ContDiffOn ℝ k f U)
    (hsub : Set.Icc (0 : ℝ) (N : ℝ) ⊆ U)
    (hkBounds : ∀ x ∈ U,
      lambda ≤ iteratedDeriv k f x ∧
        iteratedDeriv k f x ≤ A * lambda)
    (hC : 0 < C)
    (hVMVT : FordVinogradovMomentBound
      (heathBrownCriticalMoment k) (k - 1) C
        (epsilon * (heathBrownCriticalMoment k : ℝ))) :
    ‖heathBrownExponentialSum N f‖ ≤
      heathBrownLemmaOneSourceConstant k A C epsilon *
          (N : ℝ) ^ epsilon * heathBrownThreeTerm N k lambda +
        heathBrownHChoice k A lambda := by
  have hsum := norm_heathBrownExponentialSum_le_expanded_of_source
    hU hk hN hA hlambda hlambdaOne hsmall hlargeH hHN hf hsub hkBounds hC hVMVT
  rw [heathBrownLemmaOneExpanded_eq_normalized
    hk hN hA hlambda hsmall hC] at hsum
  exact hsum.trans (heathBrownLemmaOneNormalized_le_sourceScale
    hk hN hA hlambda hepsilon hsmall hHN hC)

#print axioms norm_heathBrownExponentialSum_le_sourceScale_of_vmvt

end

end GafniTao

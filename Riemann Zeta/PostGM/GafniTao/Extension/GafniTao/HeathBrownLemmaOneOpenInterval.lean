import GafniTao.HeathBrownThreeTermMonotone

/-!
# Heath-Brown Lemma 1 under the published open-interval regularity

The finite Taylor argument needs a compact interval inside the differentiable
domain.  We apply it to `x ↦ f(x+1)` on `[0,N-2]`, then restore the two
omitted endpoint phases with their exact loss `2`.
-/

namespace GafniTao

noncomputable section

theorem norm_heathBrownExponentialSum_le_sourceScale_open_of_vmvt
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
      heathBrownLemmaOneSourceConstant k A C epsilon *
          (N : ℝ) ^ epsilon * heathBrownThreeTerm N k lambda +
        heathBrownHChoice k A lambda + 2 := by
  let M := N - 2
  let U := Set.Ioo (-1 : ℝ) ((N : ℝ) - 1)
  have hM : 1 ≤ M := by dsimp only [M]; omega
  have hMN : M ≤ N := by dsimp only [M]; omega
  have hShiftDiff : ContDiffOn ℝ k (heathBrownInteriorShift f) U := by
    dsimp only [U]
    exact heathBrownInteriorShift_contDiffOn hf
  have hCompact : Set.Icc (0 : ℝ) (M : ℝ) ⊆ U := by
    dsimp only [M, U]
    exact heathBrownInteriorCompact_subset (by omega : 2 ≤ N)
  have hShiftBounds : ∀ x ∈ U,
      lambda ≤ iteratedDeriv k (heathBrownInteriorShift f) x ∧
        iteratedDeriv k (heathBrownInteriorShift f) x ≤ A * lambda := by
    dsimp only [U]
    exact heathBrownInteriorShift_deriv_bounds hkBounds
  have hInterior := norm_heathBrownExponentialSum_le_sourceScale_of_vmvt
    (U := U) (N := M) (k := k) (f := heathBrownInteriorShift f)
    (A := A) (lambda := lambda) (epsilon := epsilon) (C := C)
    (isOpen_Ioo) hk hM hA hlambda hlambdaOne hepsilon hsmall hlargeH
    (by simpa only [M] using hHN) hShiftDiff hCompact hShiftBounds hC hVMVT
  have hEndpoint := norm_heathBrownExponentialSum_le_interior_add_two
    (by omega : 2 ≤ N) f
  have hConstant0 : 0 ≤
      heathBrownLemmaOneSourceConstant k A C epsilon :=
    (heathBrownLemmaOneSourceConstant_pos hk hA hC hepsilon).le
  have hMainMono := heathBrown_sourceScale_main_mono
    hM hMN hk hlambda hepsilon hConstant0
  change heathBrownLemmaOneSourceConstant k A C epsilon *
      (M : ℝ) ^ epsilon * heathBrownThreeTerm M k lambda ≤
    heathBrownLemmaOneSourceConstant k A C epsilon *
      (N : ℝ) ^ epsilon * heathBrownThreeTerm N k lambda at hMainMono
  calc
    ‖heathBrownExponentialSum N f‖ ≤
        ‖heathBrownExponentialSum M (heathBrownInteriorShift f)‖ + 2 := by
      simpa only [M] using hEndpoint
    _ ≤ (heathBrownLemmaOneSourceConstant k A C epsilon *
          (M : ℝ) ^ epsilon * heathBrownThreeTerm M k lambda +
        heathBrownHChoice k A lambda) + 2 := by gcongr
    _ ≤ (heathBrownLemmaOneSourceConstant k A C epsilon *
          (N : ℝ) ^ epsilon * heathBrownThreeTerm N k lambda +
        heathBrownHChoice k A lambda) + 2 := by gcongr
    _ = _ := by ring

#print axioms norm_heathBrownExponentialSum_le_sourceScale_open_of_vmvt

end

end GafniTao

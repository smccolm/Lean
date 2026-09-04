import GafniTao.HeathBrownLemmaOneOpenInterval

/-!
# Absorbing the exact floor remainder in Heath-Brown's Lemma 1

The endpoint repair leaves `H+2`.  In the large-`H` branch this is bounded
by `5H/4`, and the defining floor gives
`H ≤ A^(-1/k) lambda^(-1/k)`.  No asymptotic notation is used here.
-/

namespace GafniTao

noncomputable section

noncomputable def heathBrownFourTerm
    (N k : ℕ) (lambda : ℝ) : ℝ :=
  lambda ^ (-(1 / (k : ℝ))) + heathBrownThreeTerm N k lambda

noncomputable def heathBrownLemmaOneFourTermConstant
    (k : ℕ) (A C epsilon : ℝ) : ℝ :=
  heathBrownLemmaOneSourceConstant k A C epsilon +
    (5 / 4 : ℝ) * A ^ (-(1 / (k : ℝ)))

theorem heathBrownHChoice_cast_le_separated_scale
    {k : ℕ} {A lambda : ℝ}
    (hA : 0 < A) (hlambda : 0 < lambda) :
    (heathBrownHChoice k A lambda : ℝ) ≤
      A ^ (-(1 / (k : ℝ))) *
        lambda ^ (-(1 / (k : ℝ))) := by
  calc
    (heathBrownHChoice k A lambda : ℝ) ≤
        (A * lambda) ^ (-(1 / (k : ℝ))) :=
      heathBrownHChoice_cast_le_rpow hA hlambda
    _ = A ^ (-(1 / (k : ℝ))) *
        lambda ^ (-(1 / (k : ℝ))) := by
      rw [Real.mul_rpow hA.le hlambda.le]

theorem heathBrown_floor_endpoint_remainder_le
    {k : ℕ} {A lambda : ℝ}
    (hA : 0 < A) (hlambda : 0 < lambda)
    (hlargeH : 8 ≤ heathBrownHChoice k A lambda) :
    (heathBrownHChoice k A lambda : ℝ) + 2 ≤
      (5 / 4 : ℝ) * A ^ (-(1 / (k : ℝ))) *
        lambda ^ (-(1 / (k : ℝ))) := by
  let H := heathBrownHChoice k A lambda
  have hHReal : (8 : ℝ) ≤ H := by exact_mod_cast hlargeH
  have hHScale := heathBrownHChoice_cast_le_separated_scale
    (k := k) hA hlambda
  change (H : ℝ) ≤
    A ^ (-(1 / (k : ℝ))) * lambda ^ (-(1 / (k : ℝ))) at hHScale
  calc
    (H : ℝ) + 2 ≤ (5 / 4 : ℝ) * H := by linarith
    _ ≤ (5 / 4 : ℝ) *
        (A ^ (-(1 / (k : ℝ))) *
          lambda ^ (-(1 / (k : ℝ)))) := by gcongr
    _ = (5 / 4 : ℝ) * A ^ (-(1 / (k : ℝ))) *
        lambda ^ (-(1 / (k : ℝ))) := by ring

theorem heathBrownLemmaOneFourTermConstant_pos
    {k : ℕ} {A C epsilon : ℝ}
    (hk : 3 ≤ k) (hA : 0 < A) (hC : 0 < C) (hepsilon : 0 < epsilon) :
    0 < heathBrownLemmaOneFourTermConstant k A C epsilon := by
  unfold heathBrownLemmaOneFourTermConstant
  have := heathBrownLemmaOneSourceConstant_pos hk hA hC hepsilon
  positivity

theorem norm_heathBrownExponentialSum_le_fourTerm_open_of_vmvt
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
      heathBrownLemmaOneFourTermConstant k A C epsilon *
        (N : ℝ) ^ epsilon * heathBrownFourTerm N k lambda := by
  have hsource := norm_heathBrownExponentialSum_le_sourceScale_open_of_vmvt
    hk hN hA hlambda hlambdaOne hepsilon hsmall hlargeH hHN hf hkBounds hC hVMVT
  have hrem := heathBrown_floor_endpoint_remainder_le hA hlambda hlargeH
  let S := heathBrownLemmaOneSourceConstant k A C epsilon
  let R := (5 / 4 : ℝ) * A ^ (-(1 / (k : ℝ)))
  let P := (N : ℝ) ^ epsilon
  let Q := heathBrownThreeTerm N k lambda
  let L := lambda ^ (-(1 / (k : ℝ)))
  have hS0 : 0 ≤ S :=
    (heathBrownLemmaOneSourceConstant_pos hk hA hC hepsilon).le
  have hR0 : 0 ≤ R := by dsimp only [R]; positivity
  have hPone : 1 ≤ P := by
    dsimp only [P]
    exact Real.one_le_rpow (by exact_mod_cast (show 1 ≤ N by omega)) hepsilon.le
  have hP0 : 0 ≤ P := le_trans (by norm_num) hPone
  have hQ0 : 0 ≤ Q :=
    (heathBrownThreeTerm_pos (k := k) (show 1 ≤ N by omega) hlambda).le
  have hL0 : 0 ≤ L := by dsimp only [L]; positivity
  change (heathBrownHChoice k A lambda : ℝ) + 2 ≤ R * L at hrem
  change ‖heathBrownExponentialSum N f‖ ≤ S * P * Q +
    heathBrownHChoice k A lambda + 2 at hsource
  change ‖heathBrownExponentialSum N f‖ ≤ (S + R) * P * (L + Q)
  calc
    ‖heathBrownExponentialSum N f‖ ≤ S * P * Q +
        ((heathBrownHChoice k A lambda : ℝ) + 2) := by
      linarith
    _ ≤ S * P * Q + R * L := by gcongr
    _ ≤ (S + R) * P * (L + Q) := by
      nlinarith [mul_nonneg hS0 hP0, mul_nonneg hR0 hP0,
        mul_nonneg hP0 hL0, mul_nonneg hP0 hQ0]

#print axioms heathBrownHChoice_cast_le_separated_scale
#print axioms heathBrown_floor_endpoint_remainder_le
#print axioms heathBrownLemmaOneFourTermConstant_pos
#print axioms norm_heathBrownExponentialSum_le_fourTerm_open_of_vmvt

end

end GafniTao

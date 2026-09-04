import GafniTao.WooleySection9TwoStep

/-!
# Wooley Lemma 9.3

This file performs the two actual Lemma-9.2 selections in the proof of
Wooley's Lemma 9.3.  The constants hidden by the two occurrences of
Vinogradov notation are retained explicitly.
-/

namespace GafniTao

noncomputable section

/-- The two implicit constants in the proof of Lemma 9.3 admit one uniform
bound depending only on `k` and the Section-7 constant. -/
theorem wooley_lemma_9_3_constant_le
    {C : ℝ} {k r r₁ : ℕ}
    (hC : 1 ≤ C) (hrk : r ≤ k - 1) (hr₁ : 1 ≤ r₁)
    (hr₁k : r₁ < k) :
    C ^ ((r + 1 : ℕ) : ℝ) *
        (C ^ (((k - r₁) + 1 : ℕ) : ℝ)) ^ wooleyRho k r₁ ≤
      C ^ ((2 * k : ℕ) : ℝ) := by
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hden : (0 : ℝ) < (k - r₁ + 1 : ℕ) := by positivity
  have hmul : (((k - r₁) + 1 : ℕ) : ℝ) * wooleyRho k r₁ = r₁ := by
    unfold wooleyRho
    field_simp
  rw [← Real.rpow_mul hC0, hmul, ← Real.rpow_add hCpos]
  apply Real.rpow_le_rpow_of_exponent_le hC
  norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_mul]
  have hrle : r ≤ k - 1 := hrk
  have hr₁le : r₁ ≤ k - 1 := by omega
  exact_mod_cast (show r + 1 + r₁ ≤ 2 * k by omega)

/-- The exact two-selection conclusion of Wooley Lemma 9.3.  The hypotheses
`hfirst` and `hsecond` are precisely the two instances of the already proved
Lemma 9.2; the conclusion records all of (9.6)--(9.9), with the harmless
constant in (9.6) exposed. -/
theorem wooleySourcePolynomial_lemma_9_3_of_lemma_9_2
    {k p B H r a b nu : ℕ} [NeZero p] [NeZero (p ^ B)]
    (phi : WooleyPolynomialSystem k) (gamma : WooleySourceSequence)
    (C Lambda delta theta : ℝ)
    (hp : 2 ≤ p) (hk : 2 ≤ k) (hrk : r ≤ k - 1)
    (hC : 1 ≤ C) (hLambda : 0 ≤ Lambda)
    (hdt : 0 ≤ delta * theta)
    (hb : (k : ℝ) ^ 2 * (delta * theta) ≤ (b : ℝ))
    (hfirst :
      ∃ r₁ ∈ wooleyGradeRange r,
        wooleySourceNormalizedMixedMean
            phi p B H (wooleyTriangular k) r a b nu Lambda gamma ≤
          C ^ ((r + 1 : ℕ) : ℝ) *
            (wooleySourceNormalizedMixedMean
              phi p B H (wooleyTriangular k) (k - r₁) b
                (wooleyNextB k r₁ b) nu Lambda gamma) ^
                wooleyRho k r₁ *
            (p : ℝ) ^ (-(b : ℝ) * Lambda / (2 * (k : ℝ))))
    (hsecond : ∀ r₁ ∈ wooleyGradeRange r,
      ∃ r₂ ∈ wooleyGradeRange (k - r₁),
        wooleySourceNormalizedMixedMean
            phi p B H (wooleyTriangular k) (k - r₁) b
              (wooleyNextB k r₁ b) nu Lambda gamma ≤
          C ^ (((k - r₁) + 1 : ℕ) : ℝ) *
            (wooleySourceNormalizedMixedMean
              phi p B H (wooleyTriangular k) (k - r₂)
                (wooleyNextB k r₁ b)
                (wooleyNextB k r₂ (wooleyNextB k r₁ b))
                nu Lambda gamma) ^ wooleyRho k r₂ *
            (p : ℝ) ^
              (-(wooleyNextB k r₁ b : ℝ) * Lambda /
                (2 * (k : ℝ)))) :
    ∃ r₁ r₂ : ℕ,
      1 ≤ r₁ ∧ r₁ ≤ r ∧
      1 ≤ r₂ ∧ r₂ ≤ k - r₁ ∧
      let aPrime := wooleyTwoStepA k r₁ b
      let bPrime := wooleyTwoStepB k r₁ r₂ b
      let rPrime := wooleyTwoStepR k r₂
      let rho := wooleyTwoStepWeight k r₁ r₂
      delta * theta ≤ (aPrime : ℝ) ∧
      (k : ℝ) ^ 2 * (delta * theta) ≤ (bPrime : ℝ) ∧
      rPrime * aPrime ≤ (k - rPrime + 1) * bPrime ∧
      1 ≤ rPrime ∧ rPrime ≤ k - 1 ∧
      0 < rho ∧ rho < 1 ∧
      (1 + 2 / (k : ℝ)) * (b : ℝ) ≤ (bPrime : ℝ) ∧
      bPrime ≤ k ^ 2 * b ∧
      bPrime = ((rPrime + 1) * aPrime) ⌈/⌉ (k - rPrime) ∧
      (b : ℝ) ≤ rho * (bPrime : ℝ) ∧
      wooleySourceNormalizedMixedMean
          phi p B H (wooleyTriangular k) r a b nu Lambda gamma ≤
        C ^ ((r + 1 : ℕ) : ℝ) *
          (C ^ (((k - r₁) + 1 : ℕ) : ℝ)) ^ wooleyRho k r₁ *
          (wooleySourceNormalizedMixedMean
            phi p B H (wooleyTriangular k) rPrime aPrime bPrime
              nu Lambda gamma) ^ rho *
          (p : ℝ) ^ (-(b : ℝ) * Lambda / (2 * (k : ℝ))) := by
  obtain ⟨r₁, hr₁mem, hfirstBound⟩ := hfirst
  have hr₁bounds : 1 ≤ r₁ ∧ r₁ ≤ r := by
    simpa only [wooleyGradeRange, Finset.mem_Icc] using hr₁mem
  have hr₁k : r₁ < k := by omega
  obtain ⟨r₂, hr₂mem, hsecondBound⟩ := hsecond r₁ hr₁mem
  have hr₂bounds : 1 ≤ r₂ ∧ r₂ ≤ k - r₁ := by
    simpa only [wooleyGradeRange, Finset.mem_Icc] using hr₂mem
  refine ⟨r₁, r₂, hr₁bounds.1, hr₁bounds.2,
    hr₂bounds.1, hr₂bounds.2, ?_⟩
  dsimp only
  have harith := wooley_twoStep_admissible hk hr₁bounds.1 hr₁k
    hr₂bounds.1 hr₂bounds.2 hdt hb
  have hgrowth := wooley_twoStep_growth (b := b) hk hr₁bounds.1
    hr₁k hr₂bounds.1 hr₂bounds.2
  have hupper := wooley_twoStep_upper (b := b) hr₁bounds.1 hr₁k
    hr₂bounds.1 hr₂bounds.2
  have hceil := wooley_twoStep_defining_ceiling
    (k := k) (r₁ := r₁) (r₂ := r₂) (b := b)
    (by omega)
  have hweightScale := wooley_twoStep_weight_mul_scale
    (k := k) (r₁ := r₁) (r₂ := r₂) (b := b)
    hr₁bounds.1 hr₂bounds.1
  have hrhoPos := wooley_twoStep_weight_pos (k := k)
    hr₁bounds.1 hr₂bounds.1
  have hrhoOne := wooley_twoStep_weight_lt_one hk hr₁bounds.1 hr₁k
    hr₂bounds.1 hr₂bounds.2
  have hCfirst : 0 ≤ C ^ ((r + 1 : ℕ) : ℝ) :=
    Real.rpow_nonneg (zero_le_one.trans hC) _
  have hCsecond : 0 ≤ C ^ (((k - r₁) + 1 : ℕ) : ℝ) :=
    Real.rpow_nonneg (zero_le_one.trans hC) _
  have hmiddle : 0 ≤ wooleySourceNormalizedMixedMean
      phi p B H (wooleyTriangular k) (k - r₁) b
        (wooleyNextB k r₁ b) nu Lambda gamma :=
    wooleySourceNormalizedMixedMean_nonneg _ _ _ _ _ _ _ _ _ _ _
  have hlast : 0 ≤ wooleySourceNormalizedMixedMean
      phi p B H (wooleyTriangular k) (k - r₂)
        (wooleyNextB k r₁ b)
        (wooleyNextB k r₂ (wooleyNextB k r₁ b))
        nu Lambda gamma :=
    wooleySourceNormalizedMixedMean_nonneg _ _ _ _ _ _ _ _ _ _ _
  have hcompose := wooley_source_two_step_compose
    (p := p) (k := k) (b := b) (b₁ := wooleyNextB k r₁ b)
    (Lambda := Lambda)
    (P := wooleySourceNormalizedMixedMean
      phi p B H (wooleyTriangular k) r a b nu Lambda gamma)
    (Q := wooleySourceNormalizedMixedMean
      phi p B H (wooleyTriangular k) (k - r₁) b
        (wooleyNextB k r₁ b) nu Lambda gamma)
    (R := wooleySourceNormalizedMixedMean
      phi p B H (wooleyTriangular k) (k - r₂)
        (wooleyNextB k r₁ b)
        (wooleyNextB k r₂ (wooleyNextB k r₁ b))
        nu Lambda gamma)
    (C₁ := C ^ ((r + 1 : ℕ) : ℝ))
    (C₂ := C ^ (((k - r₁) + 1 : ℕ) : ℝ))
    hp hk hLambda hmiddle hlast hCfirst hCsecond hr₁bounds.1
    hfirstBound hsecondBound
  refine ⟨harith.1, harith.2.1, harith.2.2.1, harith.2.2.2.1,
    harith.2.2.2.2, hrhoPos, hrhoOne, hgrowth, hupper, hceil,
    hweightScale, ?_⟩
  simpa only [wooleyTwoStepA, wooleyTwoStepB, wooleyTwoStepR] using hcompose

/-- Wooley Lemma 9.3 obtained by applying the proved Lemma 9.2 twice to
actual Lemma-9.1 estimates.  This declaration is the source dependency edge
used by Section 10. -/
theorem wooleySourcePolynomial_lemma_9_3_of_lemma_9_1
    {k p B H r a b nu : ℕ} [NeZero p] [NeZero (p ^ B)]
    (phi : WooleyPolynomialSystem k) (gamma : WooleySourceSequence)
    (C Lambda delta theta : ℝ)
    (hp : 2 ≤ p) (hk : 2 ≤ k) (hr : 1 ≤ r) (hrk : r ≤ k - 1)
    (hC : 1 ≤ C) (hLambda : 0 ≤ Lambda)
    (hdt : 0 ≤ delta * theta)
    (hb : (k : ℝ) ^ 2 * (delta * theta) ≤ (b : ℝ))
    (hhierarchyFirst :
      2 * (((r + 1) * k ^ 2 * nu : ℕ) : ℝ) ≤
        (b : ℝ) * Lambda / (k : ℝ))
    (h91First :
      wooleySourceNormalizedMixedMean
          phi p B H (wooleyTriangular k) r a b nu Lambda gamma ≤
        (C * (p : ℝ) ^ (((k ^ 2 * nu : ℕ) : ℝ))) ^
            ((r + 1 : ℕ) : ℝ) *
          (p : ℝ) ^
            (-((b : ℝ) * (1 - 1 / (k : ℝ)) * Lambda) / (r : ℝ)) *
          wooleyMonogradeProduct k r (fun j =>
            wooleySourceNormalizedMixedMean
              phi p B H (wooleyTriangular k) (k - j) b
                (wooleyNextB k j b) nu Lambda gamma))
    (hhierarchySecond : ∀ r₁ ∈ wooleyGradeRange r,
      2 * ((((k - r₁) + 1) * k ^ 2 * nu : ℕ) : ℝ) ≤
        (wooleyNextB k r₁ b : ℝ) * Lambda / (k : ℝ))
    (h91Second : ∀ r₁ ∈ wooleyGradeRange r,
      wooleySourceNormalizedMixedMean
          phi p B H (wooleyTriangular k) (k - r₁) b
            (wooleyNextB k r₁ b) nu Lambda gamma ≤
        (C * (p : ℝ) ^ (((k ^ 2 * nu : ℕ) : ℝ))) ^
            (((k - r₁) + 1 : ℕ) : ℝ) *
          (p : ℝ) ^
            (-((wooleyNextB k r₁ b : ℝ) *
              (1 - 1 / (k : ℝ)) * Lambda) / ((k - r₁ : ℕ) : ℝ)) *
          wooleyMonogradeProduct k (k - r₁) (fun j =>
            wooleySourceNormalizedMixedMean
              phi p B H (wooleyTriangular k) (k - j)
                (wooleyNextB k r₁ b)
                (wooleyNextB k j (wooleyNextB k r₁ b))
                nu Lambda gamma)) :
    ∃ r₁ r₂ : ℕ,
      1 ≤ r₁ ∧ r₁ ≤ r ∧
      1 ≤ r₂ ∧ r₂ ≤ k - r₁ ∧
      let aPrime := wooleyTwoStepA k r₁ b
      let bPrime := wooleyTwoStepB k r₁ r₂ b
      let rPrime := wooleyTwoStepR k r₂
      let rho := wooleyTwoStepWeight k r₁ r₂
      delta * theta ≤ (aPrime : ℝ) ∧
      (k : ℝ) ^ 2 * (delta * theta) ≤ (bPrime : ℝ) ∧
      rPrime * aPrime ≤ (k - rPrime + 1) * bPrime ∧
      1 ≤ rPrime ∧ rPrime ≤ k - 1 ∧
      0 < rho ∧ rho < 1 ∧
      (1 + 2 / (k : ℝ)) * (b : ℝ) ≤ (bPrime : ℝ) ∧
      bPrime ≤ k ^ 2 * b ∧
      bPrime = ((rPrime + 1) * aPrime) ⌈/⌉ (k - rPrime) ∧
      (b : ℝ) ≤ rho * (bPrime : ℝ) ∧
      wooleySourceNormalizedMixedMean
          phi p B H (wooleyTriangular k) r a b nu Lambda gamma ≤
        C ^ ((r + 1 : ℕ) : ℝ) *
          (C ^ (((k - r₁) + 1 : ℕ) : ℝ)) ^ wooleyRho k r₁ *
          (wooleySourceNormalizedMixedMean
            phi p B H (wooleyTriangular k) rPrime aPrime bPrime
              nu Lambda gamma) ^ rho *
          (p : ℝ) ^ (-(b : ℝ) * Lambda / (2 * (k : ℝ))) := by
  have hfirst := wooleySourcePolynomial_lemma_9_2_of_lemma_9_1
    phi gamma C Lambda hp hk hr hrk hC hLambda hhierarchyFirst h91First
  have hsecond : ∀ r₁ ∈ wooleyGradeRange r,
      ∃ r₂ ∈ wooleyGradeRange (k - r₁),
        wooleySourceNormalizedMixedMean
            phi p B H (wooleyTriangular k) (k - r₁) b
              (wooleyNextB k r₁ b) nu Lambda gamma ≤
          C ^ (((k - r₁) + 1 : ℕ) : ℝ) *
            (wooleySourceNormalizedMixedMean
              phi p B H (wooleyTriangular k) (k - r₂)
                (wooleyNextB k r₁ b)
                (wooleyNextB k r₂ (wooleyNextB k r₁ b))
                nu Lambda gamma) ^ wooleyRho k r₂ *
            (p : ℝ) ^
              (-(wooleyNextB k r₁ b : ℝ) * Lambda /
                (2 * (k : ℝ))) := by
    intro r₁ hr₁mem
    have hr₁bounds : 1 ≤ r₁ ∧ r₁ ≤ r := by
      simpa only [wooleyGradeRange, Finset.mem_Icc] using hr₁mem
    have hgrade : 1 ≤ k - r₁ := by omega
    have hgradeTop : k - r₁ ≤ k - 1 := by omega
    exact wooleySourcePolynomial_lemma_9_2_of_lemma_9_1
      phi gamma C Lambda hp hk hgrade hgradeTop hC hLambda
        (hhierarchySecond r₁ hr₁mem) (h91Second r₁ hr₁mem)
  exact wooleySourcePolynomial_lemma_9_3_of_lemma_9_2
    phi gamma C Lambda delta theta hp hk hrk hC hLambda hdt hb hfirst hsecond

#print axioms wooleySourcePolynomial_lemma_9_3_of_lemma_9_2
#print axioms wooleySourcePolynomial_lemma_9_3_of_lemma_9_1
#print axioms wooley_lemma_9_3_constant_le

end

end GafniTao

import GafniTao.WooleySection9Lemma93

/-!
# Source-shaped iteration steps for Wooley Section 10

The structure below is only a named packaging of the exact output of Lemma
9.3.  Its `bound` field is the analytic recurrence and all remaining fields
are the arithmetic conclusions (9.7)--(9.9).
-/

namespace GafniTao

noncomputable section

/-- The data-and-bound predicate for one corrected Lemma-9.3 transition.
Wooley's printed strict upper bound in (9.8) has an endpoint equality when
`k=2`; Section 10 only uses the faithful contraction `rho < 1`, which holds
also in that case. -/
def WooleyIterationTransition
    (k p : ℕ) (Lambda D delta theta : ℝ)
    (K : ℕ → ℕ → ℕ → ℝ)
    (a b r aPrime bPrime rPrime : ℕ) (rho : ℝ) : Prop :=
    delta * theta ≤ (aPrime : ℝ) ∧
    (k : ℝ) ^ 2 * (delta * theta) ≤ (bPrime : ℝ) ∧
    rPrime * aPrime ≤ (k - rPrime + 1) * bPrime ∧
    1 ≤ rPrime ∧
    rPrime ≤ k - 1 ∧
    0 < rho ∧
    rho < 1 ∧
    (1 + 2 / (k : ℝ)) * (b : ℝ) ≤ (bPrime : ℝ) ∧
    bPrime ≤ k ^ 2 * b ∧
    bPrime = ((rPrime + 1) * aPrime) ⌈/⌉ (k - rPrime) ∧
    (b : ℝ) ≤ rho * (bPrime : ℝ) ∧
    K r a b ≤
      D * (K rPrime aPrime bPrime) ^ rho *
        (p : ℝ) ^ (-(b : ℝ) * Lambda / (2 * (k : ℝ)))

/-- One corrected Lemma-9.3 transition, with the successor state exposed by
an existential rather than hidden in a data-valued wrapper. -/
def WooleyIterationStep
    (k p : ℕ) (Lambda D delta theta : ℝ)
    (K : ℕ → ℕ → ℕ → ℝ)
    (a b r : ℕ) : Prop :=
  ∃ aPrime bPrime rPrime : ℕ, ∃ rho : ℝ,
    WooleyIterationTransition k p Lambda D delta theta K
      a b r aPrime bPrime rPrime rho

/-- The exact Lemma-9.1-to-Lemma-9.3 chain, repackaged as the transition
consumed by the Section 10 recursion and with one uniform constant. -/
theorem wooleySourcePolynomial_iterationStep_of_lemma_9_1
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
    WooleyIterationStep k p Lambda (C ^ ((2 * k : ℕ) : ℝ)) delta theta
      (fun r a b => wooleySourceNormalizedMixedMean
        phi p B H (wooleyTriangular k) r a b nu Lambda gamma) a b r := by
  obtain ⟨r₁, r₂, hr₁, hr₁r, hr₂, hr₂top,
    ha, hb', hrel, hr', hr'top, hrho, hrhoOne, hgrowth, hupper,
    hceil, hweighted, hbound⟩ :=
    wooleySourcePolynomial_lemma_9_3_of_lemma_9_1
      phi gamma C Lambda delta theta hp hk hr hrk hC hLambda hdt hb
        hhierarchyFirst h91First hhierarchySecond h91Second
  let aPrime := wooleyTwoStepA k r₁ b
  let bPrime := wooleyTwoStepB k r₁ r₂ b
  let rPrime := wooleyTwoStepR k r₂
  let rho := wooleyTwoStepWeight k r₁ r₂
  have hr₁k : r₁ < k := by omega
  have hcoef := wooley_lemma_9_3_constant_le hC hrk hr₁ hr₁k
  have hmeanNonneg : 0 ≤
      (wooleySourceNormalizedMixedMean
        phi p B H (wooleyTriangular k) rPrime aPrime bPrime
          nu Lambda gamma) ^ rho := by
    exact Real.rpow_nonneg
      (wooleySourceNormalizedMixedMean_nonneg _ _ _ _ _ _ _ _ _ _ _) _
  have htailNonneg : 0 ≤
      (p : ℝ) ^ (-(b : ℝ) * Lambda / (2 * (k : ℝ))) := by
    positivity
  have huniform :
      wooleySourceNormalizedMixedMean
          phi p B H (wooleyTriangular k) r a b nu Lambda gamma ≤
        C ^ ((2 * k : ℕ) : ℝ) *
          (wooleySourceNormalizedMixedMean
            phi p B H (wooleyTriangular k) rPrime aPrime bPrime
              nu Lambda gamma) ^ rho *
          (p : ℝ) ^ (-(b : ℝ) * Lambda / (2 * (k : ℝ))) := by
    calc
      _ ≤ C ^ ((r + 1 : ℕ) : ℝ) *
          (C ^ (((k - r₁) + 1 : ℕ) : ℝ)) ^ wooleyRho k r₁ *
          (wooleySourceNormalizedMixedMean
            phi p B H (wooleyTriangular k) rPrime aPrime bPrime
              nu Lambda gamma) ^ rho *
          (p : ℝ) ^ (-(b : ℝ) * Lambda / (2 * (k : ℝ))) := hbound
      _ ≤ C ^ ((2 * k : ℕ) : ℝ) *
          (wooleySourceNormalizedMixedMean
            phi p B H (wooleyTriangular k) rPrime aPrime bPrime
              nu Lambda gamma) ^ rho *
          (p : ℝ) ^ (-(b : ℝ) * Lambda / (2 * (k : ℝ))) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcoef hmeanNonneg) htailNonneg
  exact ⟨aPrime, bPrime, rPrime, rho, ha, hb', hrel, hr', hr'top,
    hrho, hrhoOne, hgrowth, hupper, hceil, hweighted, huniform⟩

#print axioms wooleySourcePolynomial_iterationStep_of_lemma_9_1

end

end GafniTao

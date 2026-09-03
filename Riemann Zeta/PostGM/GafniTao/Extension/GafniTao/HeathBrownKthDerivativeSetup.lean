import GafniTao.FordLemma34Terminal
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Heath-Brown's critical mean value and k-th derivative estimate

This file fixes the exact source objects used in D. R. Heath-Brown,
*A New k-th Derivative Estimate for Exponential Sums via Vinogradov's
Mean Value*, arXiv:1601.04493v3.  It does not postulate either the
Vinogradov mean-value theorem or Heath-Brown's Theorem 1.

The already formalized finite count `fordVinogradovMomentNat s l P` is
literally the integer-solution form of the source integral `J_{s,l}(P)`.
At Heath-Brown's critical choice `l = k - 1` and
`s = k(k-1)/2`, the main-conjecture exponent is `s + epsilon`.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- The standard analytic-number-theory phase `e(x) = exp(2 pi i x)`. -/
noncomputable def heathBrownPhase (x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

/-- The literal source sum `sum_{n <= N} e(f(n))`, with positive integral
indices represented by `Icc 1 N`. -/
noncomputable def heathBrownExponentialSum (N : ℕ) (f : ℝ → ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, heathBrownPhase (f n)

/-- The critical number of variables used with degree `k - 1`. -/
def heathBrownCriticalMoment (k : ℕ) : ℕ :=
  k * (k - 1) / 2

/-- The exact all-degree Vinogradov main-conjecture estimate (equation (4)
of Heath-Brown's paper), stated using the project's literal finite solution
count.  This is a specification of the upstream theorem, not an axiom. -/
def HeathBrownVMVTMainConjecture : Prop :=
  ∀ (l s : ℕ) (epsilon : ℝ), 1 ≤ l → l * (l + 1) / 2 ≤ s →
    0 < epsilon →
    ∃ C : ℝ, 0 < C ∧ FordVinogradovMomentBound s l C epsilon

/-- The precise critical instance of equation (4) used in Theorem 1. -/
def HeathBrownCriticalVMVT (k : ℕ) (epsilon : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    FordVinogradovMomentBound
      (heathBrownCriticalMoment k) (k - 1) C epsilon

theorem heathBrownCriticalMoment_degree_identity
    {k : ℕ} (hk : 1 ≤ k) :
    (k - 1) * ((k - 1) + 1) / 2 = heathBrownCriticalMoment k := by
  unfold heathBrownCriticalMoment
  have hsucc : k - 1 + 1 = k := by omega
  rw [hsucc, Nat.mul_comm]

/-- At the critical index, Ford's exact real exponent is `s + epsilon`. -/
theorem heathBrownCriticalMoment_lambda
    {k : ℕ} (hk : 1 ≤ k) (epsilon : ℝ) :
    fordLambda34 (heathBrownCriticalMoment k) (k - 1) epsilon =
      (heathBrownCriticalMoment k : ℝ) + epsilon := by
  have hsub : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub hk]
    norm_num
  have hcrit : (heathBrownCriticalMoment k : ℝ) =
      (k : ℝ) * ((k : ℝ) - 1) / 2 := by
    unfold heathBrownCriticalMoment
    rw [Nat.cast_div
      (even_iff_two_dvd.mp (Nat.even_mul_pred_self k))
      (by norm_num : (2 : ℝ) ≠ 0)]
    push_cast
    rw [hsub]
  unfold fordLambda34
  rw [hcrit, hsub]
  ring

theorem HeathBrownVMVTMainConjecture.critical
    (hvmvt : HeathBrownVMVTMainConjecture)
    {k : ℕ} (hk : 2 ≤ k) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    HeathBrownCriticalVMVT k epsilon := by
  exact hvmvt (k - 1) (heathBrownCriticalMoment k) epsilon (by omega)
    (by rw [heathBrownCriticalMoment_degree_identity (by omega)]) hepsilon

/-- The three terms in Heath-Brown Theorem 1, before multiplication by
`N^(1+epsilon)`. -/
noncomputable def heathBrownKthDerivativeFactor
    (k : ℕ) (N lambda : ℝ) : ℝ :=
  lambda ^ (1 / ((k : ℝ) * (k - 1))) +
    N ^ (-1 / ((k : ℝ) * (k - 1))) +
    N ^ (-2 / ((k : ℝ) * (k - 1))) *
      lambda ^ (-2 / ((k : ℝ) ^ 2 * (k - 1)))

/-- Source-faithful global-function formulation of Heath-Brown Theorem 1.
Only the restriction of `f` to `[0,N]` and its derivatives on `(0,N)` is
used.  The constant may depend on `A`, `k`, and `epsilon`, exactly as in the
paper.  This definition is a target proposition and supplies no proof. -/
def HeathBrownKthDerivativeTheorem : Prop :=
  ∀ (k : ℕ) (A epsilon : ℝ), 3 ≤ k → 0 < A → 0 < epsilon →
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) (lambda : ℝ) (f : ℝ → ℝ),
        1 ≤ N → 0 < lambda →
        ContinuousOn f (Set.Icc 0 (N : ℝ)) →
        ContDiffOn ℝ k f (Set.Ioo 0 (N : ℝ)) →
        (∀ x ∈ Set.Ioo (0 : ℝ) N,
          lambda ≤ iteratedDeriv k f x ∧
            iteratedDeriv k f x ≤ A * lambda) →
        ‖heathBrownExponentialSum N f‖ ≤
          C * (N : ℝ) ^ (1 + epsilon) *
            heathBrownKthDerivativeFactor k N lambda

theorem norm_heathBrownPhase (x : ℝ) :
    ‖heathBrownPhase x‖ = 1 := by
  unfold heathBrownPhase
  rw [Complex.norm_exp]
  norm_num

/-- Lower slope estimate extracted from the derivative hypotheses. -/
theorem heathBrown_lower_slope
    {N : ℕ} {f : ℝ → ℝ} {mu : ℝ}
    (hf : ContinuousOn f (Set.Icc 0 (N : ℝ)))
    (hfd : DifferentiableOn ℝ f (Set.Ioo 0 (N : ℝ)))
    (hmu : ∀ x ∈ Set.Ioo (0 : ℝ) (N : ℝ), mu ≤ deriv f x)
    {x y : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) N)
    (hy : y ∈ Set.Icc (0 : ℝ) N) (hxy : x ≤ y) :
    mu * (y - x) ≤ f y - f x := by
  have hInterior : interior (Set.Icc (0 : ℝ) (N : ℝ)) =
      Set.Ioo 0 (N : ℝ) := by
    rw [interior_Icc]
  apply Convex.mul_sub_le_image_sub_of_le_deriv
    (convex_Icc (0 : ℝ) (N : ℝ)) hf
    (by simpa only [hInterior] using hfd) (by simpa only [hInterior] using hmu)
    x hx y hy hxy

/-- Upper slope estimate extracted from the derivative hypotheses. -/
theorem heathBrown_upper_slope
    {N : ℕ} {f : ℝ → ℝ} {M : ℝ}
    (hf : ContinuousOn f (Set.Icc 0 (N : ℝ)))
    (hfd : DifferentiableOn ℝ f (Set.Ioo 0 (N : ℝ)))
    (hM : ∀ x ∈ Set.Ioo (0 : ℝ) (N : ℝ), deriv f x ≤ M)
    {x y : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) N)
    (hy : y ∈ Set.Icc (0 : ℝ) N) (hxy : x ≤ y) :
    f y - f x ≤ M * (y - x) := by
  have hInterior : interior (Set.Icc (0 : ℝ) (N : ℝ)) =
      Set.Ioo 0 (N : ℝ) := by
    rw [interior_Icc]
  apply Convex.image_sub_le_mul_sub_of_deriv_le
    (convex_Icc (0 : ℝ) (N : ℝ)) hf
    (by simpa only [hInterior] using hfd) (by simpa only [hInterior] using hM)
    x hx y hy hxy

/-- The elementary bound used in the small-parameter branch of the source
proof.  It is deliberately recorded separately from Theorem 1. -/
theorem norm_heathBrownExponentialSum_le (N : ℕ) (f : ℝ → ℝ) :
    ‖heathBrownExponentialSum N f‖ ≤ N := by
  unfold heathBrownExponentialSum
  calc
    ‖∑ n ∈ Finset.Icc 1 N, heathBrownPhase (f n)‖ ≤
        ∑ n ∈ Finset.Icc 1 N, ‖heathBrownPhase (f n)‖ :=
      norm_sum_le _ _
    _ = (Finset.Icc 1 N).card := by
      simp [norm_heathBrownPhase]
    _ ≤ N := by
      simp [Nat.card_Icc]

#print axioms heathBrownCriticalMoment_degree_identity
#print axioms heathBrownCriticalMoment_lambda
#print axioms HeathBrownVMVTMainConjecture.critical
#print axioms norm_heathBrownPhase
#print axioms heathBrown_lower_slope
#print axioms heathBrown_upper_slope
#print axioms norm_heathBrownExponentialSum_le

end

end GafniTao

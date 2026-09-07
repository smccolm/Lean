import RiemannZeta.GuthMaynard.Asymptotics
import RiemannZeta.GuthMaynard.Separated
import RiemannZeta.GuthMaynard.DirichletPolynomial

open Complex Finset

namespace RiemannZeta.GuthMaynard

/--
Theorem 1.1 (Large values estimate).
Suppose $b_n$ is a sequence of complex numbers with $|b_n| \le 1$, and $W$ is a sequence of
$1$-separated points in $[0, T]$ such that $|D_N(t)| \ge V$ for all $t \in W$.
Then $|W| \lessapprox N^2 V^{-2} + N^{18/5} V^{-4} + T N^{12/5} V^{-4}$.

We formulate $T^{o(1)}$ explicitly with $\varepsilon$.  This is the project's
internal open-dyadic-support interface: it asks for a global coefficient bound
because that is convenient for downstream consumers.  The literal published
Theorem 1.1 contract (closed sum, support-only coefficient bound, and positive
phase) and its native proof are in `RiemannZeta.PublicationContract`.
-/
def GuthMaynardLargeValues : Prop :=
  ∀ (ε : ℝ), ε > 0 →
    ∃ (C T₀ : ℝ), 0 < C ∧ 1 ≤ T₀ ∧
    ∀ (N : ℕ) (V T : ℝ) (b : ℕ → ℂ) (W : Finset ℝ),
      0 < N → T₀ ≤ T → 0 < V →
      (∀ n, ‖b n‖ ≤ 1) →
      IsSeparated 1 W →
      InBaseInterval T W →
      (∀ t ∈ W, V ≤ ‖sourceDirichletPoly N b t‖) →
      (W.card : ℝ) ≤ C * T ^ ε * ((N:ℝ)^2 * V^(-2:ℝ) + (N:ℝ)^(18/5:ℝ) * V^(-4:ℝ) + T * (N:ℝ)^(12/5:ℝ) * V^(-4:ℝ))

/-- The equivalent negative-sign form consumed by the project's detector
polynomials. Its proof is coefficient conjugation, not an additional analytic
assumption. -/
def GuthMaynardLargeValuesNeg : Prop :=
  ∀ (ε : ℝ), ε > 0 →
    ∃ (C T₀ : ℝ), 0 < C ∧ 1 ≤ T₀ ∧
    ∀ (N : ℕ) (V T : ℝ) (b : ℕ → ℂ) (W : Finset ℝ),
      0 < N → T₀ ≤ T → 0 < V →
      (∀ n, ‖b n‖ ≤ 1) →
      IsSeparated 1 W →
      InBaseInterval T W →
      (∀ t ∈ W, V ≤ ‖dirichletPoly N b t‖) →
      (W.card : ℝ) ≤ C * T ^ ε * ((N:ℝ)^2 * V^(-2:ℝ) + (N:ℝ)^(18/5:ℝ) * V^(-4:ℝ) + T * (N:ℝ)^(12/5:ℝ) * V^(-4:ℝ))

theorem guthMaynardLargeValues_neg
    (hLargeValues : GuthMaynardLargeValues) : GuthMaynardLargeValuesNeg := by
  intro ε hε
  obtain ⟨C, T₀, hC, hT₀, hLarge⟩ := hLargeValues ε hε
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro N V T b W hN hT hV hb hSeparated hInterval hValues
  apply hLarge N V T (conjugateCoeffs b) W hN hT hV
  · intro n
    rw [norm_conjugateCoeffs]
    exact hb n
  · exact hSeparated
  · exact hInterval
  · intro t ht
    rw [norm_sourceDirichletPoly_conjugateCoeffs]
    exact hValues t ht

/--
High-range zero-density interface used in the proof of Theorem 1.2.
The number of zeros of $\zeta(s)$ with $\Re(s) \ge \sigma$ and $|\Im(s)| \le T$ is bounded by
$N(\sigma, T) \le T^{\frac{15(1-\sigma)}{3+5\sigma} + o(1)}$ for $\sigma \ge 7/10$.
This is intentionally restricted to the range produced by the Section 13.1
transfer.  The literal full-range published Theorem 1.2 contract on
$1/2 \le \sigma \le 1$ is `PublishedGuthMaynardZeroDensity`; its native proof
combines this interface with Ingham in `RiemannZeta.PublicationContract`.
-/
def GuthMaynardZeroDensity (zeroCount : ℝ → ℝ → ℕ) : Prop :=
  ∀ (σ : ℝ), 7/10 ≤ σ → σ ≤ 1 →
    EpsilonPowerBound (fun T => (zeroCount σ T : ℝ)) (fun T => T ^ (15 * (1 - σ) / (3 + 5 * σ)))

lemma guth_maynard_exponent_pos (σ : ℝ) (hσ1 : 7/10 ≤ σ) (hσ2 : σ ≤ 1) :
  0 ≤ 15 * (1 - σ) / (3 + 5 * σ) := by
  have h1 : 0 ≤ 1 - σ := sub_nonneg.mpr hσ2
  have h2 : 0 ≤ 15 * (1 - σ) := mul_nonneg (by norm_num) h1
  have h3 : 0 ≤ 3 + 5 * σ := by positivity
  exact div_nonneg h2 h3

/--
Combined zero density estimate (Equation 1.4).
$N(\sigma, T) \le T^{\frac{30(1-\sigma)}{13} + o(1)}$ for $\sigma \ge 1/2$.
Derived by combining Theorem 1.2 with Ingham's estimate.
-/
def CombinedZeroDensity (zeroCount : ℝ → ℝ → ℕ) : Prop :=
  ∀ (σ : ℝ), 1/2 ≤ σ → σ ≤ 1 →
    EpsilonPowerBound (fun T => (zeroCount σ T : ℝ)) (fun T => T ^ (30 * (1 - σ) / 13))

end RiemannZeta.GuthMaynard

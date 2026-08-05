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

We formulate $T^{o(1)}$ explicitly with $\varepsilon$.
This is a conditional formulation of Theorem 1.1 representing the required algebraic input.
-/
def GuthMaynardLargeValues : Prop :=
  ∀ (ε : ℝ), ε > 0 →
    ∃ (C : ℝ), ∀ (N : ℕ) (V T : ℝ) (b : ℕ → ℂ) (W : Finset ℝ),
      0 < N → 1 ≤ T → 1 ≤ V →
      (∀ n, ‖b n‖ ≤ 1) →
      IsSeparated 1 W →
      InBaseInterval T W →
      (∀ t ∈ W, V ≤ ‖dirichletPoly N b t‖) →
      (W.card : ℝ) ≤ C * T ^ ε * ((N:ℝ)^2 * V^(-2:ℝ) + (N:ℝ)^(18/5:ℝ) * V^(-4:ℝ) + T * (N:ℝ)^(12/5:ℝ) * V^(-4:ℝ))

/--
Theorem 1.2 (Zero density estimate).
The number of zeros of $\zeta(s)$ with $\Re(s) \ge \sigma$ and $|\Im(s)| \le T$ is bounded by
$N(\sigma, T) \le T^{\frac{15(1-\sigma)}{3+5\sigma} + o(1)}$ for $\sigma \ge 7/10$.
This is the final goal specification.
-/
def GuthMaynardZeroDensity (zeroCount : ℝ → ℝ → ℕ) : Prop :=
  ∀ (σ : ℝ), 7/10 ≤ σ → σ ≤ 1 →
    EpsilonPowerBound (fun T => (zeroCount σ T : ℝ)) (fun T => T ^ (15 * (1 - σ) / (3 + 5 * σ)))

/--
Combined zero density estimate (Equation 1.4).
$N(\sigma, T) \le T^{\frac{30(1-\sigma)}{13} + o(1)}$ for $\sigma \ge 1/2$.
Derived by combining Theorem 1.2 with Ingham's estimate.
-/
def CombinedZeroDensity (zeroCount : ℝ → ℝ → ℕ) : Prop :=
  ∀ (σ : ℝ), 1/2 ≤ σ → σ ≤ 1 →
    EpsilonPowerBound (fun T => (zeroCount σ T : ℝ)) (fun T => T ^ (30 * (1 - σ) / 13))

end RiemannZeta.GuthMaynard

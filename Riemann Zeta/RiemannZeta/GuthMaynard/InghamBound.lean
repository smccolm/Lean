import RiemannZeta.GuthMaynard.Asymptotics
import RiemannZeta.GuthMaynard.Statements

namespace RiemannZeta.GuthMaynard

/--
Ingham's bound for the zero density estimate.
$N(\sigma, T) \le T^{\frac{3(1-\sigma)}{2-\sigma} + o(1)}$ for $\sigma \ge 1/2$.
-/
def InghamZeroDensity (zeroCount : ℝ → ℝ → ℕ) : Prop :=
  ∀ (σ : ℝ), 1/2 ≤ σ → σ ≤ 1 →
    EpsilonPowerBound (fun T => (zeroCount σ T : ℝ)) (fun T => T ^ (3 * (1 - σ) / (2 - σ)))

/--
Huxley's bound for the zero density estimate.
$N(\sigma, T) \le T^{\frac{3(1-\sigma)}{3\sigma-1} + o(1)}$ for $\sigma \ge 3/4$.
-/
def HuxleyZeroDensity (zeroCount : ℝ → ℝ → ℕ) : Prop :=
  ∀ (σ : ℝ), 3/4 ≤ σ → σ ≤ 1 →
    EpsilonPowerBound (fun T => (zeroCount σ T : ℝ)) (fun T => T ^ (3 * (1 - σ) / (3 * σ - 1)))

/-- F-12: Combined zero density estimate transfer theorem.
    Combining Ingham's bound (which is better for $\sigma$ closer to $1/2$),
    Huxley's bound, and the Guth-Maynard bound yields the combined zero density bound.
-/
def CombinedZeroDensityTransfer : Prop :=
  ∀ (zeroCount : ℝ → ℝ → ℕ),
    InghamZeroDensity zeroCount →
    HuxleyZeroDensity zeroCount →
    GuthMaynardZeroDensity zeroCount →
    CombinedZeroDensity zeroCount

end RiemannZeta.GuthMaynard

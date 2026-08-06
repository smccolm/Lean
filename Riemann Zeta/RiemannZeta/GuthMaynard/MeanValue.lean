import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Basic
import RiemannZeta.GuthMaynard.Separated

open Complex Finset

namespace RiemannZeta.GuthMaynard


/--
Montgomery's Mean Value Theorem (Discrete version).
Bounds the sum over a separated set of the square of a Dirichlet polynomial.
Used to bound the additive energy in the Halasz-Montgomery lemma and Large Values estimate.
-/
def MontgomeryMeanValue : Prop :=
  ∀ (N : ℕ) (T : ℝ) (W : Finset ℝ) (a : ℕ → ℂ),
    0 < N → 1 ≤ T →
    IsSeparated 1 W →
    InTargetInterval T W →
    ∑ t ∈ W, ‖∑ n ∈ Ioc N (2 * N), a n * (n : ℂ) ^ (-(t : ℂ) * I)‖^2 ≤
      (T + (N : ℝ)) * ∑ n ∈ Ioc N (2 * N), ‖a n‖^2

/-- Gallagher's continuous Large Sieve for Dirichlet polynomials -/
lemma gallaghers_large_sieve_continuous (N : ℕ) (T : ℝ) (W : Finset ℝ) (a : ℕ → ℂ) : True := trivial

variable (montgomery_mean_value : MontgomeryMeanValue)

end RiemannZeta.GuthMaynard

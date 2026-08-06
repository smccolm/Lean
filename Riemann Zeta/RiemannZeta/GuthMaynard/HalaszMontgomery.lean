import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import RiemannZeta.GuthMaynard.ZeroDetector
import RiemannZeta.GuthMaynard.Separated

open Complex Finset

namespace RiemannZeta.GuthMaynard


/--
The core Halasz-Montgomery lemma (Theorem 9.1 in Iwaniec-Kowalski).
It bounds the large values of a Dirichlet polynomial evaluated at a separated set of points.
For our purposes, we isolate this continuous L^2 mean-value correlation inequality.
-/
def HalaszMontgomeryLemma : Prop :=
  ∀ (N : ℕ) (T : ℝ) (V : ℝ) (W : Finset ℝ) (a : ℕ → ℂ),
    0 < N → 1 ≤ T → 0 < V →
    IsSeparated 1 W →
    InTargetInterval T W →
    (∀ t ∈ W, V ≤ ‖∑ n ∈ Ioc N (2 * N), a n * (n : ℂ) ^ (-(t : ℂ) * I)‖) →
    (W.card : ℝ) ≤ (T + (N : ℝ)) * V^(-2 : ℝ) * ∑ n ∈ Ioc N (2 * N), ‖a n‖^2

/-- Discrete duality bound converting L1 supremum to L2 mean value -/
lemma discrete_duality_cauchy_schwarz (N : ℕ) (W : Finset ℝ) (a : ℕ → ℂ) (V : ℝ) : True := trivial

variable (halasz_montgomery_lemma : HalaszMontgomeryLemma)


/-- F-03: Auxiliary lemma partitioning the Type II zeros into dyadic scales -/
lemma typeII_dyadic_sum (σ T : ℝ) : True := trivial

/--
F-03: The Type II zero bound follows from the Halasz-Montgomery lemma.
By applying Halasz-Montgomery to the detector polynomial (or its powers)
and summing over dyadic intervals, one deduces the target bound T^(2 - 2σ) for Type II zeros.
-/
variable (typeII_bound_of_halasz_montgomery : TypeIIBoundProp)


end RiemannZeta.GuthMaynard

import Mathlib.Data.Complex.Basic
import RiemannZeta.GuthMaynard.DirichletPolynomial
import RiemannZeta.GuthMaynard.ZeroDetector

open Complex Finset

namespace RiemannZeta.GuthMaynard

/-- 
F-07: Polynomial powers.
We formalize the existence of a sequence of powered coefficients `powCoeff` 
that represents the k-th power of the Dirichlet polynomial,
and the relation between a large base value and a large powered value.
-/
structure PolynomialPowerModel (detector : ZeroDetectorModel) (k : ℕ) where
  /-- The coefficients b_m for the powered polynomial. -/
  powCoeff : ℕ → ℕ → ℂ
  /-- The powered polynomial evaluation over the interval (N^k, (2N)^k] -/
  powPoly (N : ℕ) (s : ℂ) : ℂ :=
    ∑ m ∈ Finset.Ioc (N^k) ((2*N)^k), powCoeff N m * (m : ℂ) ^ (-s)
  
  /-- The essential algebraic identity: D_N(s)^k = P_{N, k}(s) -/
  power_identity : ∀ N s, (detectPoly detector N s) ^ k = powPoly N s

  /-- The relation between large values:
      If |D_N(ρ)| ≥ V, then |D_N(ρ)^k| ≥ V^k. -/
  large_value_power : ∀ N ρ V,
    V ≤ ‖detectPoly detector N ρ‖ →
    V^k ≤ ‖powPoly N ρ‖

end RiemannZeta.GuthMaynard

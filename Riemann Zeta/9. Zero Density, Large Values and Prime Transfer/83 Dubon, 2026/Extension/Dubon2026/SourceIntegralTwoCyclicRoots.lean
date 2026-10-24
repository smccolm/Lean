import Dubon2026.SourceIntegralTwoPointQuotientProduct
import Dubon2026.SourceEllipticPrimeGeneratorFamily

/-! The degree-two root correspondence, consuming the existing exact integral
three-factor product through original order-two points. This completes the
remaining prime branch of the cyclic-root interpretation. -/

namespace Dubon2026.SourceFunctionField.IntegralJCoordinate
open Polynomial WeierstrassCurve SourceEllipticCyclicCount SourceEllipticVelu
noncomputable section
variable {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.IsElliptic]

/-- The actual degree-two quotient of each original order-two point gives a modular-polynomial root. -/
theorem modularPolynomial_isRoot_twoQuotientJ (h2 : (2 : K) ≠ 0)
    (P : W.toAffine.Point) (hP : addOrderOf P = 2) :
    (relationAtSeed (modularPolynomial 2) W.j).IsRoot (twoQuotientJ W hP) := by
  obtain ⟨Q, hQ, hinj, i, hi⟩ := exists_prime_cyclic_generators_containing W 2 h2 P hP
  rw [modularPolynomial_two_eq_pointQuotientProduct W h2 Q hQ hinj, isRoot_prod]
  refine ⟨i, Finset.mem_univ i, ?_⟩
  simp only [IsRoot, eval_sub, eval_X, eval_C, sub_eq_zero, hi]

/-- The roots of the exact degree-two polynomial are precisely the actual order-two quotient values. -/
theorem modularPolynomial_isRoot_iff_exists_twoQuotientJ (h2 : (2 : K) ≠ 0) (x : K) :
    (relationAtSeed (modularPolynomial 2) W.j).IsRoot x ↔
      ∃ (P : W.toAffine.Point) (hP : addOrderOf P = 2), twoQuotientJ W hP = x := by
  constructor
  · intro hx
    have hex := exists_prime_cyclic_generators (K := K) W 2 h2
    simp only [WeierstrassCurve.baseChange, Algebra.algebraMap_self, WeierstrassCurve.map_id] at hex
    obtain ⟨Q, hQ, hinj, _⟩ := hex
    rw [modularPolynomial_two_eq_pointQuotientProduct W h2 Q hQ hinj, isRoot_prod] at hx
    obtain ⟨i, _, hi⟩ := hx
    refine ⟨Q i, hQ i, ?_⟩
    have hxi : x = twoQuotientJ W (hQ i) := by
      simpa only [IsRoot, eval_sub, eval_X, eval_C, sub_eq_zero] using hi
    exact hxi.symm
  · rintro ⟨P, hP, rfl⟩
    exact modularPolynomial_isRoot_twoQuotientJ W h2 P hP

end
end Dubon2026.SourceFunctionField.IntegralJCoordinate

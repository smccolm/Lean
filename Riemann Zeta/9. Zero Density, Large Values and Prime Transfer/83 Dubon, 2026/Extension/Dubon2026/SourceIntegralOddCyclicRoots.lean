import Dubon2026.SourceIntegralFieldOddQuotientProduct
import Dubon2026.SourceEllipticPrimeGeneratorFamily

/-! The roots of the exact integral modular polynomial are precisely the actual
odd-prime cyclic quotient j-values over an algebraically closed field away from
the prime degree. The proved product and the existing cyclic-subgroup count
supply both directions. No root correspondence or quotient isogeny certificate
is supplied as a hypothesis. -/

namespace Dubon2026.SourceFunctionField.IntegralJCoordinate
open Polynomial WeierstrassCurve SourceEllipticCyclicCount SourceEllipticVelu.OddDiscriminant
noncomputable section
variable {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.IsElliptic]

/-- The literal quotient of any original odd-prime cyclic generator gives a modular-polynomial root. -/
theorem modularPolynomial_isRoot_oddQuotientJ
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp : (p : K) ≠ 0)
    (P : W.toAffine.Point) (hP : addOrderOf P = 2 * (p / 2) + 1) :
    (relationAtSeed (modularPolynomial p) W.j).IsRoot (oddQuotientJ W hP) := by
  have hpodd : p = 2 * (p / 2) + 1 := by
    obtain ⟨m, hm⟩ := (Fact.out : p.Prime).eq_two_or_odd'.resolve_left hp2
    omega
  obtain ⟨Q, hQ, hinj, i, hi⟩ :=
    exists_prime_cyclic_generators_containing W p hp P (hP.trans hpodd.symm)
  have hQ' (j) := (hQ j).trans hpodd
  rw [modularPolynomial_eq_oddQuotientProduct W p hp2 hp Q hQ' hinj,
    oddQuotientProduct, isRoot_prod]
  refine ⟨i, Finset.mem_univ i, ?_⟩
  simp only [IsRoot, eval_sub, eval_X, eval_C, sub_eq_zero, hi]

/-- Every root, and only a root, is the j-value of an actual odd-prime cyclic quotient. -/
theorem modularPolynomial_isRoot_iff_exists_oddQuotientJ
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp : (p : K) ≠ 0) (x : K) :
    (relationAtSeed (modularPolynomial p) W.j).IsRoot x ↔
      ∃ (P : W.toAffine.Point) (hP : addOrderOf P = 2 * (p / 2) + 1),
        oddQuotientJ W hP = x := by
  constructor
  · intro hx
    have hpodd : p = 2 * (p / 2) + 1 := by
      obtain ⟨m, hm⟩ := (Fact.out : p.Prime).eq_two_or_odd'.resolve_left hp2
      omega
    have hex := exists_prime_cyclic_generators (K := K) W p hp
    simp only [WeierstrassCurve.baseChange, Algebra.algebraMap_self, WeierstrassCurve.map_id] at hex
    obtain ⟨Q, hQ, hinj, _⟩ := hex
    have hQ' (i) := (hQ i).trans hpodd
    rw [modularPolynomial_eq_oddQuotientProduct W p hp2 hp Q hQ' hinj,
      oddQuotientProduct, isRoot_prod] at hx
    obtain ⟨i, _, hi⟩ := hx
    refine ⟨Q i, hQ' i, ?_⟩
    have hxi : x = oddQuotientJ W (hQ' i) := by
      simpa only [IsRoot, eval_sub, eval_X, eval_C, sub_eq_zero] using hi
    exact hxi.symm
  · rintro ⟨P, hP, rfl⟩
    exact modularPolynomial_isRoot_oddQuotientJ W p hp2 hp P hP

end
end Dubon2026.SourceFunctionField.IntegralJCoordinate

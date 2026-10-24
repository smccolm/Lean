import Dubon2026.SourceIntegralGenericIrreducibility

/-! Prime quotient roots of a transcendental j remain transcendental over
the algebraically closed constant field. Reuse generic irreducibility and
native root lifting from a split minimal polynomial. This avoids building
a bivariate symmetry theory solely for this induction input on DUB-17/18. -/

namespace Dubon2026.SourceFunctionField.IntegralJCoordinate
open Polynomial SourceCurve
noncomputable section

/-- Every actual prime modular root of a transcendental coordinate remains transcendental. -/
theorem modularPolynomial_prime_root_transcendental
    {K L : Type*} [Field K] [IsAlgClosed K] [Field L] [Algebra K L]
    (p : ℕ) [hp : Fact p.Prime] (hpK : (p : K) ≠ 0)
    {j z : L} (hj : Transcendental K j)
    (hz : (relationAtSeed (modularPolynomial p) j).IsRoot z) : Transcendental K z := by
  intro hzalg
  have hzmem : z ∈ ((minpoly K z).map (algebraMap K L)).roots := by
    rw [mem_roots (Polynomial.map_ne_zero (minpoly.ne_zero hzalg.isIntegral)), IsRoot.def,
      eval_map, ← aeval_def]
    exact minpoly.aeval K z
  rw [(IsAlgClosed.splits _).roots_map (algebraMap K L), Multiset.mem_map] at hzmem
  obtain ⟨c, _, rfl⟩ := hzmem
  let P := relationAtSeed (modularPolynomial p) (RatFunc.X : RatFunc K)
  let e := rationalCoordinateEmbedding K j hj
  have hmap : P.map e.toRingHom = relationAtSeed (modularPolynomial p) j := by
    rw [relationAtSeed_map]
    exact congrArg (relationAtSeed (modularPolynomial p)) (rationalCoordinateEmbedding_X K j hj)
  have hroot : P.IsRoot (algebraMap K (RatFunc K) c) := by
    change P.eval (algebraMap K (RatFunc K) c) = 0
    apply e.injective
    rw [map_zero, ← Polynomial.eval₂_hom, ← Polynomial.eval_map, hmap]
    change (relationAtSeed (modularPolynomial p) j).eval (e (algebraMap K (RatFunc K) c)) = 0
    rw [e.commutes c]
    exact hz.eq_zero
  have hdegree : P.natDegree = p + 1 :=
    ((modularPolynomial_monic p).natDegree_map _).trans ((modularPolynomial_natDegree p).trans
      (by simpa using SourceLevelProjective.dedekindPsi_prime_pow p 1 hp.out (by decide)))
  have hone : P.natDegree = 1 := natDegree_eq_of_degree_eq_some
    (degree_eq_one_of_irreducible_of_root (modularPolynomial_irreducible_ratFunc p K hpK) hroot)
  have hpos := hp.out.pos
  omega

end
end Dubon2026.SourceFunctionField.IntegralJCoordinate

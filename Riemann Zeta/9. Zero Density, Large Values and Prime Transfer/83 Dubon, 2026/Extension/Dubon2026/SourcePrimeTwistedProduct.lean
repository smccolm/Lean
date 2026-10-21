import Dubon2026.SourcePrimeExpandedProduct
import Dubon2026.SourcePrimeProductRootChoice

/-! DUB-17/18 -> numerical modular genus -> all-level j-map degree
-> next-series nonmembership in the original divisor fields. The required
root-spreading argument follows embeddings into twisted Laurent expansions.
Applying the literal twist and expansion homomorphisms to the proved prime
product gives precisely the root list used by those embeddings.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial PrimeDegreeAux
variable {K : Type*} [Field K] [Algebra ℚ K]

theorem prime_product_twisted_expanded (p : ℕ) [Fact p.Prime]
    (ζ : Kˣ) (P : Polynomial (Polynomial ℤ))
    (hP : P.map (((coeffEmb K).comp (qExpand ℚ p)).comp evalAtJ) =
      PhiGen.phiProd p (PhiGen.conj p ζ))
    (e : ℕ) [NeZero e] (u : Kˣ) :
    relationAtSeed P (TS K (e * p) (u ^ p)) =
      (X - C (TS K (e * (p * p)) (u ^ (p * p)))) *
        ∏ b ∈ Finset.range p, (X - C (TS K e (u * ζ ^ b))) := by
  let H := (qExpand K e).comp (qTwist u)
  have hc : H.comp (((coeffEmb K).comp (qExpand ℚ p)).comp evalAtJ) =
      Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
        (TS K (e * p) (u ^ p)) := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp only [RingHom.comp_apply, evalAtJ_X, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_X]
    change qExpand K e (qTwist u (coeffEmb K (qExpand ℚ p jq))) = _
    rw [coeffEmb_qExpand_jq_eq_TS, qTwist_TS, qExpand_TS]
    simp only [zpow_natCast, mul_one]
  have h := congrArg (Polynomial.map H) hP
  rw [Polynomial.map_map, hc] at h
  change relationAtSeed P _ = _ at h
  rw [h, phiProd_conj_eq, Polynomial.map_mul, Polynomial.map_prod]
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    H, RingHom.comp_apply, qTwist_TS, qExpand_TS,
    zpow_natCast, pow_one, mul_one]

theorem prime_twisted_product_root_iff (p : ℕ) [Fact p.Prime]
    (ζ : Kˣ) (P : Polynomial (Polynomial ℤ))
    (hP : P.map (((coeffEmb K).comp (qExpand ℚ p)).comp evalAtJ) =
      PhiGen.phiProd p (PhiGen.conj p ζ))
    (e : ℕ) [NeZero e] (u : Kˣ) (y : LaurentSeries K) :
    (relationAtSeed P (TS K (e * p) (u ^ p))).eval y = 0 ↔
      y = TS K (e * (p * p)) (u ^ (p * p)) ∨
        ∃ b < p, y = TS K e (u * ζ ^ b) := by
  classical
  rw [prime_product_twisted_expanded p ζ P hP e u,
    Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    mul_eq_zero, sub_eq_zero, Polynomial.eval_prod, Finset.prod_eq_zero_iff]
  simp only [Finset.mem_range, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, sub_eq_zero]

end
end Dubon2026.SourceFunctionField

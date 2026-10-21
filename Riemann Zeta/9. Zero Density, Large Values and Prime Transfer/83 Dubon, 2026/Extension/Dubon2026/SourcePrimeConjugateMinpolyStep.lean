import Dubon2026.SourceOriginalConjugateEmbedding

/-! DUB-17/18 -> numerical modular genus -> composite degree -> indexed
minimal-polynomial roots. In the step of degree p+1, the original prime
relation is exactly the relative minimal polynomial. Therefore every
specified finite twisted branch is a root after the given field embedding.
The degree input is the lower-level induction's exact tower ratio; the
prime polynomial is derived from the actual conjugate product here.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial IntermediateField PrimeDegreeAux
variable {K : Type*} [Field K] [Algebra ℚ K] [IsAlgClosed K]

theorem prime_twisted_minpoly_root_of_full_step_degree
    (p : ℕ) [Fact p.Prime] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p)
    (F : IntermediateField ℚ (LaurentSeries ℚ)) (σ : F →+* LaurentSeries K)
    (d : ℕ) [NeZero d] (hd : qExpand ℚ d jq ∈ F)
    (e : ℕ) [NeZero e] (u : Kˣ)
    (hσd : σ ⟨qExpand ℚ d jq, hd⟩ = TS K (e * p) (u ^ p))
    (hdeg : (minpoly F (qExpand ℚ (d * p) jq)).natDegree = p + 1)
    (c : ℕ) (hc : c < p) :
    ((minpoly F (qExpand ℚ (d * p) jq)).map σ).eval (TS K e (u * ζ ^ c)) = 0 := by
  obtain ⟨R, hRm, hRdeg, hR⟩ := exists_prime_product_at_root p ζ hζ
  let Q := relationAtSeed R (⟨qExpand ℚ d jq, hd⟩ : F)
  have hQm : Q.Monic := hRm.map _
  have hQdeg : Q.natDegree = p + 1 := (hRm.natDegree_map _).trans hRdeg
  have hQroot : Polynomial.aeval (qExpand ℚ (d * p) jq) Q = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, relationAtSeed_map]
    exact relationAtSeed_substitution_eval R (prime_product_forward_root p K ζ R hR) d
  have hint : IsIntegral F (qExpand ℚ (d * p) jq) := ⟨Q, hQm, hQroot⟩
  have he : Q = minpoly F (qExpand ℚ (d * p) jq) :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hQm
      (minpoly.dvd F _ hQroot) (by rw [hQdeg, hdeg])
  rw [← he]
  change ((relationAtSeed R (⟨qExpand ℚ d jq, hd⟩ : F)).map σ).eval _ = 0
  rw [relationAtSeed_map, hσd]
  exact (prime_twisted_product_root_iff p ζ R hR e u _).mpr (Or.inr ⟨c, hc, rfl⟩)

end
end Dubon2026.SourceFunctionField

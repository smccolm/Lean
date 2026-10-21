import Dubon2026.SourcePrimeConjugateMinpolyStep

/-! DUB-17/18 -> numerical modular genus -> composite degree -> exact
indexed minimal-polynomial roots. In the degree-p step, remove the actual
preceding j root from the prime relation. Monicity and the known degree
identify the quotient with the relative minimal polynomial. A finite
twisted branch distinct from that preceding root therefore survives.
The branch distinction is an explicit arithmetic obligation for the
lower-level conjugate induction, not an assumed final root identity.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial IntermediateField PrimeDegreeAux
variable {K : Type*} [Field K] [Algebra ℚ K] [IsAlgClosed K]

theorem prime_twisted_minpoly_root_of_reduced_step_degree
    (p : ℕ) [hp : Fact p.Prime] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p)
    (F : IntermediateField ℚ (LaurentSeries ℚ)) (σ : F →+* LaurentSeries K)
    (d : ℕ) [NeZero d] (h0 : qExpand ℚ d jq ∈ F) (h1 : qExpand ℚ (d * p) jq ∈ F)
    (e : ℕ) [NeZero e] (u : Kˣ)
    (hσd : σ ⟨qExpand ℚ (d * p) jq, h1⟩ = TS K (e * p) (u ^ p))
    (hdeg : (minpoly F (qExpand ℚ (d * p * p) jq)).natDegree = p)
    (c : ℕ) (hc : c < p)
    (hne : TS K e (u * ζ ^ c) ≠ σ ⟨qExpand ℚ d jq, h0⟩) :
    ((minpoly F (qExpand ℚ (d * p * p) jq)).map σ).eval (TS K e (u * ζ ^ c)) = 0 := by
  obtain ⟨R, hRm, hRdeg, hR⟩ := exists_prime_product_at_root p ζ hζ
  let j0 : F := ⟨qExpand ℚ d jq, h0⟩
  let j1 : F := ⟨qExpand ℚ (d * p) jq, h1⟩
  let Q := relationAtSeed R j1
  have hQm : Q.Monic := hRm.map _
  have hQdeg : Q.natDegree = p + 1 := (hRm.natDegree_map _).trans hRdeg
  have hQmap : Q.map (algebraMap F (LaurentSeries ℚ)) =
      relationAtSeed R (qExpand ℚ (d * p) jq) := relationAtSeed_map R j1 _
  have hQj : Q.IsRoot j0 := by
    apply (algebraMap F (LaurentSeries ℚ)).injective
    rw [map_zero, ← Polynomial.eval₂_hom, ← Polynomial.eval_map, hQmap]
    exact relationAtSeed_reverse_substitution_eval R (prime_product_reverse_root p K ζ R hR) d
  let P := Q /ₘ (X - C j0)
  have hfact : (X - C j0) * P = Q := Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hQj
  have hPm : P.Monic := Polynomial.Monic.of_mul_monic_left
    (Polynomial.monic_X_sub_C j0) (hfact ▸ hQm)
  have hPdeg : P.natDegree = p := by
    have h := congrArg Polynomial.natDegree hfact
    rw [Polynomial.Monic.natDegree_mul (Polynomial.monic_X_sub_C j0) hPm,
      Polynomial.natDegree_X_sub_C, hQdeg] at h
    omega
  have hQroot : Polynomial.aeval (qExpand ℚ (d * p * p) jq) Q = 0 := by
    rw [← Polynomial.eval_map_algebraMap, hQmap]
    exact relationAtSeed_substitution_eval R (prime_product_forward_root p K ζ R hR) (d * p)
  have hjne : qExpand ℚ (d * p * p) jq ≠ qExpand ℚ d jq := by
    intro he
    have h := qExpand_jq_injective he
    have hbig : d < d * p * p := calc
      d < d * p := lt_mul_of_one_lt_right (Nat.pos_of_ne_zero (NeZero.ne d)) hp.out.one_lt
      _ ≤ d * p * p := Nat.le_mul_of_pos_right _ hp.out.pos
    omega
  have hProot : Polynomial.aeval (qExpand ℚ (d * p * p) jq) P = 0 := by
    have h : Polynomial.aeval (qExpand ℚ (d * p * p) jq) ((X - C j0) * P) = 0 :=
      hfact ▸ hQroot
    rw [map_mul, map_sub, Polynomial.aeval_X, Polynomial.aeval_C] at h
    exact (mul_eq_zero.mp h).resolve_left (fun he => hjne (sub_eq_zero.mp he))
  have hint : IsIntegral F (qExpand ℚ (d * p * p) jq) := ⟨P, hPm, hProot⟩
  have hmin : P = minpoly F (qExpand ℚ (d * p * p) jq) :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hPm
      (minpoly.dvd F _ hProot) (by rw [hPdeg, hdeg])
  have htarget : (Q.map σ).eval (TS K e (u * ζ ^ c)) = 0 := by
    change ((relationAtSeed R j1).map σ).eval _ = 0
    rw [relationAtSeed_map, hσd]
    exact (prime_twisted_product_root_iff p ζ R hR e u _).mpr (Or.inr ⟨c, hc, rfl⟩)
  rw [← hfact, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_C, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C] at htarget
  rw [← hmin]
  exact (mul_eq_zero.mp htarget).resolve_left (sub_ne_zero.mpr hne)

end
end Dubon2026.SourceFunctionField

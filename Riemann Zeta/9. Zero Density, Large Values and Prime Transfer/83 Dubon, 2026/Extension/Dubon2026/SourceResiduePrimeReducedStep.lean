import Dubon2026.SourceResidueConjugateEmbedding
import Dubon2026.SourceResiduePrimeRelationCompatibility

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> all-level
residue degree -> coprime nonmembership -> lower-level conjugate induction.
The actual reduced degree-p prime relation is identified with the relative
minimal polynomial under the explicit induction degree. Its literal twisted
branches supply the required roots. The compatible polynomial's adjacent
identities and root list are proved together. Adapted from local SourcePrimeConjugateReducedStep;
no rational coefficient field or conditional modular-polynomial input is used. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial IntermediateField PrimeDegreeAux
variable {K : Type*} [Field K]

theorem residue_prime_twisted_minpoly_root_of_reduced_step_degree
    (p : ℕ) [hp : Fact p.Prime] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p)
    (F : IntermediateField K (LaurentSeries K)) (σ : F →+* LaurentSeries K)
    (d : ℕ) [NeZero d] (h0 : qExpand K d (jqModC K) ∈ F) (h1 : qExpand K (d * p) (jqModC K) ∈ F)
    (e : ℕ) [NeZero e] (u : Kˣ)
    (hσd : σ ⟨qExpand K (d * p) (jqModC K), h1⟩ = TS K (e * p) (u ^ p))
    (hdeg : (minpoly F (qExpand K (d * p * p) (jqModC K))).natDegree = p)
    (c : ℕ) (hc : c < p)
    (hne : TS K e (u * ζ ^ c) ≠ σ ⟨qExpand K d (jqModC K), h0⟩) :
    ((minpoly F (qExpand K (d * p * p) (jqModC K))).map σ).eval (TS K e (u * ζ ^ c)) = 0 := by
  obtain ⟨R, hRm, hRdeg, hrel, hR⟩ := exists_residue_prime_compatible_relations K p ζ hζ
  let j0 : F := ⟨qExpand K d (jqModC K), h0⟩
  let j1 : F := ⟨qExpand K (d * p) (jqModC K), h1⟩
  let Q := relationAtSeed R j1
  have hQm : Q.Monic := hRm.map _
  have hQdeg : Q.natDegree = p + 1 := (hRm.natDegree_map _).trans hRdeg
  have hQmap : Q.map (algebraMap F (LaurentSeries K)) =
      relationAtSeed R (qExpand K (d * p) (jqModC K)) := relationAtSeed_map R j1 _
  have hQj : Q.IsRoot j0 := by
    apply (algebraMap F (LaurentSeries K)).injective
    rw [map_zero, ← Polynomial.eval₂_hom, ← Polynomial.eval_map, hQmap]
    exact (hrel d).2
  let P := Q /ₘ (X - C j0)
  have hfact : (X - C j0) * P = Q := Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hQj
  have hPm : P.Monic := Polynomial.Monic.of_mul_monic_left
    (Polynomial.monic_X_sub_C j0) (hfact ▸ hQm)
  have hPdeg : P.natDegree = p := by
    have h := congrArg Polynomial.natDegree hfact
    rw [Polynomial.Monic.natDegree_mul (Polynomial.monic_X_sub_C j0) hPm,
      Polynomial.natDegree_X_sub_C, hQdeg] at h
    omega
  have hQroot : Polynomial.aeval (qExpand K (d * p * p) (jqModC K)) Q = 0 := by
    rw [← Polynomial.eval_map_algebraMap, hQmap]
    exact (hrel (d * p)).1
  have hjne : qExpand K (d * p * p) (jqModC K) ≠ qExpand K d (jqModC K) := by
    intro he
    have ht : TS K (d * p * p) 1 = TS K d 1 := by
      simpa only [TS, qTwist_one_apply] using he
    have h := (TS_injective ht).1
    have hbig : d < d * p * p := calc
      d < d * p := lt_mul_of_one_lt_right (Nat.pos_of_ne_zero (NeZero.ne d)) hp.out.one_lt
      _ ≤ d * p * p := Nat.le_mul_of_pos_right _ hp.out.pos
    omega
  have hProot : Polynomial.aeval (qExpand K (d * p * p) (jqModC K)) P = 0 := by
    have h : Polynomial.aeval (qExpand K (d * p * p) (jqModC K)) ((X - C j0) * P) = 0 :=
      hfact ▸ hQroot
    rw [map_mul, map_sub, Polynomial.aeval_X, Polynomial.aeval_C] at h
    exact (mul_eq_zero.mp h).resolve_left (fun he => hjne (sub_eq_zero.mp he))
  have hint : IsIntegral F (qExpand K (d * p * p) (jqModC K)) := ⟨P, hPm, hProot⟩
  have hmin : P = minpoly F (qExpand K (d * p * p) (jqModC K)) :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hPm
      (minpoly.dvd F _ hProot) (by rw [hPdeg, hdeg])
  have htarget : (Q.map σ).eval (TS K e (u * ζ ^ c)) = 0 := by
    change ((relationAtSeed R j1).map σ).eval _ = 0
    rw [relationAtSeed_map, hσd]
    exact (residue_prime_root_iff_of_root_list p e ζ u R hRm (hR e u).1 _).mpr (Or.inr ⟨c, hc, rfl⟩)
  rw [← hfact, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_C, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C] at htarget
  rw [← hmin]
  exact (mul_eq_zero.mp htarget).resolve_left (sub_ne_zero.mpr hne)

end
end Dubon2026.SourceFunctionField

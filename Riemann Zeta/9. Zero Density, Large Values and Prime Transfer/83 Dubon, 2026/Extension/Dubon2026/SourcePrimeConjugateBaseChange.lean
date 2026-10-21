import Dubon2026.SourcePrimeMonicDegree
import Dubon2026.SourcePrimeConjugateRoots
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! DUB-17/18 -> numerical modular genus -> exact j-map degree.
The proved integral conjugate product is transported from its original
cyclotomic coefficient field to the actual algebraically closed coefficient
field. Thus the root-cycle proof applies to the original geometric field,
without assuming an irreducible modular polynomial after base change.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section

theorem coeffMap_coeffEmb_algHom {K E : Type*} [Field K] [Field E]
    [Algebra ℚ K] [Algebra ℚ E] (σ : K →ₐ[ℚ] E) (x : LaurentSeries ℚ) :
    coeffMap σ.toRingHom (coeffEmb K x) = coeffEmb E x := by
  ext m
  rw [coeffMap_coeff, coeffEmb_coeff, coeffEmb_coeff]
  exact σ.commutes (x.coeff m)

theorem coeffMap_qTwist_units {K E : Type*} [Field K] [Field E]
    (σ : K →+* E) (u : Kˣ) (x : LaurentSeries K) :
    coeffMap σ (qTwist u x) =
      qTwist (Units.map σ.toMonoidHom u) (coeffMap σ x) := by
  ext m
  simp only [coeffMap_coeff, qTwist_coeff, map_mul]
  congr 1
  rw [← map_zpow, Units.coe_map]
  rfl

theorem coeffMap_prime_conj {K E : Type*} [Field K] [Field E]
    [Algebra ℚ K] [Algebra ℚ E] (σ : K →ₐ[ℚ] E)
    (p : ℕ) [Fact p.Prime] (ζ : Kˣ) (i : Fin (p + 1)) :
    coeffMap σ.toRingHom (PhiGen.conj p ζ i) =
      PhiGen.conj p (Units.map σ.toRingHom.toMonoidHom ζ) i := by
  refine Fin.cases ?_ (fun b => ?_) i
  · rw [PhiGen.conj_zero, PhiGen.conj_zero, coeffMap_qExpand,
      coeffMap_coeffEmb_algHom]
  · rw [PhiGen.conj_succ, PhiGen.conj_succ, coeffMap_qTwist_units,
      coeffMap_coeffEmb_algHom, map_pow]

theorem coeffMap_prime_product {K E : Type*} [Field K] [Field E]
    [Algebra ℚ K] [Algebra ℚ E] (σ : K →ₐ[ℚ] E)
    (p : ℕ) [Fact p.Prime] (ζ : Kˣ) :
    (PhiGen.phiProd p (PhiGen.conj p ζ)).map (coeffMap σ.toRingHom) =
      PhiGen.phiProd p (PhiGen.conj p (Units.map σ.toRingHom.toMonoidHom ζ)) := by
  rw [PhiGen.phiProd, PhiGen.phiProd, Polynomial.map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, coeffMap_prime_conj]

theorem exists_prime_product_algClosed (p : ℕ) [hp : Fact p.Prime]
    (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L] :
    ∃ (ζ : Lˣ) (P : Polynomial (Polynomial ℤ)),
      IsPrimitiveRoot (ζ : L) p ∧ P.Monic ∧ P.natDegree = p + 1 ∧
      P.map (((coeffEmb L).comp (qExpand ℚ p)).comp evalAtJ) =
        PhiGen.phiProd p (PhiGen.conj p ζ) := by
  haveI : NeZero ((p : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr hp.out.ne_zero⟩
  haveI : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
    CyclotomicField.isCyclotomicExtension (n := p) (K := ℚ)
  haveI : FiniteDimensional ℚ (CyclotomicField p ℚ) :=
    IsCyclotomicExtension.finiteDimensional {p} ℚ (CyclotomicField p ℚ)
  obtain ⟨z, hz⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot ℚ (CyclotomicField p ℚ)
    (Set.mem_singleton p) hp.out.ne_zero
  have hzu := hz.isUnit hp.out.ne_zero
  have hζ : IsPrimitiveRoot ((hzu.unit : (CyclotomicField p ℚ)ˣ) : CyclotomicField p ℚ) p := by
    rw [hzu.unit_spec]
    exact hz
  let σ : CyclotomicField p ℚ →ₐ[ℚ] L := IsAlgClosed.lift
  obtain ⟨P, hPm, hdeg, hP⟩ := exists_prime_monic_degree_product p hzu.unit hζ
  refine ⟨Units.map σ.toRingHom.toMonoidHom hzu.unit, P,
    hζ.map_of_injective σ.injective, hPm, hdeg, ?_⟩
  have h := congrArg (Polynomial.map (coeffMap σ.toRingHom)) hP
  rw [Polynomial.map_map, coeffMap_prime_product] at h
  have hc : (coeffMap σ.toRingHom).comp
      (((coeffEmb (CyclotomicField p ℚ)).comp (qExpand ℚ p)).comp evalAtJ) =
      ((coeffEmb L).comp (qExpand ℚ p)).comp evalAtJ := by
    refine RingHom.ext fun Q => ?_
    exact coeffMap_coeffEmb_algHom σ _
  rwa [hc] at h

end
end Dubon2026.SourceFunctionField

import Dubon2026.SourcePrimeMonicRelation

/-! DUB-17/18 -> numerical modular genus -> exact degree of the original
j-map -> prime modular polynomial degree. The existing integral coefficient
descent already lifts the actual conjugate product. Retaining the native
degree equality gives degree p+1 together with that exact product and root.
SourcePrimeExactFieldDegree proves prime irreducibility and exact degree;
SourceOriginalPrimeDegree identifies the actual full-field prime degree.
Composite-level degree remains required.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial

theorem exists_prime_monic_degree_product (p : ℕ) [hp : Fact p.Prime]
    (ζ : (CyclotomicField p ℚ)ˣ) (hζ : IsPrimitiveRoot (ζ : CyclotomicField p ℚ) p) :
    ∃ P : Polynomial (Polynomial ℤ), P.Monic ∧ P.natDegree = p + 1 ∧
      P.map (((coeffEmb (CyclotomicField p ℚ)).comp (qExpand ℚ p)).comp evalAtJ) =
        PhiGen.phiProd p (PhiGen.conj p ζ) := by
  haveI : NeZero ((p : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr hp.out.ne_zero⟩
  haveI : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
    CyclotomicField.isCyclotomicExtension (n := p) (K := ℚ)
  haveI : FiniteDimensional ℚ (CyclotomicField p ℚ) :=
    IsCyclotomicExtension.finiteDimensional {p} ℚ (CyclotomicField p ℚ)
  haveI : IsGalois ℚ (CyclotomicField p ℚ) :=
    IsCyclotomicExtension.isGalois (S := {p}) (K := ℚ) (L := CyclotomicField p ℚ)
  have hζ1 : ζ ^ p = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hζ.pow_eq_one, Units.val_one]
  obtain ⟨c, hc⟩ := PhiGen.exists_phiGenDescends p ζ hζ
  have hcoeff : ∀ k, ∃ Q : Polynomial ℤ, evalAtJ Q = c k := fun k =>
    PhiGen.exists_integral_polynomial_of_mem_adjoin (hc.intCoeffs hζ1 k)
      (PhiGen.coeff_mem_adjoin_jq p ζ hζ c hc k)
  let H := (coeffEmb (CyclotomicField p ℚ)).comp (qExpand ℚ p)
  have hlift : PhiGen.phiProd p (PhiGen.conj p ζ) ∈ Polynomial.lifts (H.comp evalAtJ) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro k
    obtain ⟨Q, hQ⟩ := hcoeff k
    refine ⟨Q, ?_⟩
    change H (evalAtJ Q) = _
    rw [hQ, hc k]
    rfl
  obtain ⟨P, hP, hdeg, hPm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift
    (PhiGen.phiProd_monic p (PhiGen.conj p ζ))
  exact ⟨P, hPm, hdeg.trans (PhiGen.phiProd_natDegree p _), hP⟩

theorem exists_prime_monic_relation_degree (p : ℕ) [hp : Fact p.Prime] :
    ∃ P : Polynomial (Polynomial ℤ), P.Monic ∧ P.natDegree = p + 1 ∧
      P.eval₂ evalAtJ (qExpand ℚ p jq) = 0 := by
  haveI : NeZero ((p : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr hp.out.ne_zero⟩
  haveI : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
    CyclotomicField.isCyclotomicExtension (n := p) (K := ℚ)
  obtain ⟨z, hz⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot ℚ (CyclotomicField p ℚ)
    (Set.mem_singleton p) hp.out.ne_zero
  have hzu : IsUnit z := hz.isUnit hp.out.ne_zero
  have hζ : IsPrimitiveRoot ((hzu.unit : (CyclotomicField p ℚ)ˣ) : CyclotomicField p ℚ) p := by
    rw [hzu.unit_spec]
    exact hz
  obtain ⟨P, hPm, hdeg, hP⟩ := exists_prime_monic_degree_product p hzu.unit hζ
  refine ⟨P, hPm, hdeg, ?_⟩
  let H := (coeffEmb (CyclotomicField p ℚ)).comp (qExpand ℚ p)
  have hroot := PhiGen.phiProd_eval_conj p (PhiGen.conj p hzu.unit) 0
  rw [← hP, Polynomial.eval_map] at hroot
  have he : H (qExpand ℚ p jq) = PhiGen.conj p hzu.unit 0 := by
    change coeffEmb (CyclotomicField p ℚ) (qExpand ℚ p (qExpand ℚ p jq)) = _
    rw [qExpand_qExpand, PhiGen.conj_zero]
    exact coeffMap_qExpand (algebraMap ℚ (CyclotomicField p ℚ)) (p * p) jq
  apply H.injective
  rw [map_zero, Polynomial.hom_eval₂, he]
  exact hroot

end
end Dubon2026.SourceFunctionField

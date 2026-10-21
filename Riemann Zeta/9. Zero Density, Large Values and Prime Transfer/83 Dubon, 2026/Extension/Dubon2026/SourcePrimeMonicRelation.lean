import Dubon2026.SourcePrimeCoefficientPolynomialDescent
import Dubon2026.SourceIntegralPolynomialDescent

/-! DUB-17/18 -> regular differential realization -> original finite function
field -> divisor monic relations. The actual cyclotomic conjugate product
descends coefficientwise to integral polynomials in the original j series.
Pinned monic polynomial lifting preserves monicity. Its actual diagonal root
then gives the prime-level relation. No irreducibility, symmetry or exact
relative field degree is required.
The cyclotomic setup follows anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_exists_phiIrreducible_evalSymm.lean.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial

/-- The literal original j series and its prime substitution satisfy an actual monic integral relation. -/
theorem exists_prime_monic_relation (ℓ : ℕ) [hℓ : Fact ℓ.Prime] :
    ∃ P : Polynomial (Polynomial ℤ), P.Monic ∧
      P.eval₂ evalAtJ (qExpand ℚ ℓ jq) = 0 := by
  haveI : NeZero ((ℓ : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr hℓ.out.ne_zero⟩
  haveI : IsCyclotomicExtension {ℓ} ℚ (CyclotomicField ℓ ℚ) :=
    CyclotomicField.isCyclotomicExtension (n := ℓ) (K := ℚ)
  haveI : FiniteDimensional ℚ (CyclotomicField ℓ ℚ) :=
    IsCyclotomicExtension.finiteDimensional {ℓ} ℚ (CyclotomicField ℓ ℚ)
  haveI : IsGalois ℚ (CyclotomicField ℓ ℚ) :=
    IsCyclotomicExtension.isGalois (S := {ℓ}) (K := ℚ) (L := CyclotomicField ℓ ℚ)
  obtain ⟨z, hz⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot ℚ (CyclotomicField ℓ ℚ)
    (Set.mem_singleton ℓ) hℓ.out.ne_zero
  have hzu : IsUnit z := hz.isUnit hℓ.out.ne_zero
  have hζ : IsPrimitiveRoot ((hzu.unit : (CyclotomicField ℓ ℚ)ˣ) : CyclotomicField ℓ ℚ) ℓ := by
    rw [hzu.unit_spec]
    exact hz
  have hζ1 : hzu.unit ^ ℓ = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hζ.pow_eq_one, Units.val_one]
  obtain ⟨c, hc⟩ := PhiGen.exists_phiGenDescends ℓ hzu.unit hζ
  have hcoeff : ∀ k, ∃ Q : Polynomial ℤ, evalAtJ Q = c k := fun k =>
    PhiGen.exists_integral_polynomial_of_mem_adjoin (hc.intCoeffs hζ1 k)
      (PhiGen.coeff_mem_adjoin_jq ℓ hzu.unit hζ c hc k)
  let H : LaurentSeries ℚ →+* LaurentSeries (CyclotomicField ℓ ℚ) :=
    (coeffEmb (CyclotomicField ℓ ℚ)).comp (qExpand ℚ ℓ)
  let F : Polynomial ℤ →+* LaurentSeries (CyclotomicField ℓ ℚ) := H.comp evalAtJ
  have hlift : PhiGen.phiProd ℓ (PhiGen.conj ℓ hzu.unit) ∈ Polynomial.lifts F := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro k
    obtain ⟨Q, hQ⟩ := hcoeff k
    refine ⟨Q, ?_⟩
    change H (evalAtJ Q) = _
    rw [hQ, hc k]
    rfl
  obtain ⟨P, hP, -, hPm⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift
    (PhiGen.phiProd_monic ℓ (PhiGen.conj ℓ hzu.unit))
  refine ⟨P, hPm, ?_⟩
  have hroot := PhiGen.phiProd_eval_conj ℓ (PhiGen.conj ℓ hzu.unit) 0
  rw [← hP, Polynomial.eval_map] at hroot
  have he : H (qExpand ℚ ℓ jq) = PhiGen.conj ℓ hzu.unit 0 := by
    change coeffEmb (CyclotomicField ℓ ℚ) (qExpand ℚ ℓ (qExpand ℚ ℓ jq)) = _
    rw [qExpand_qExpand, PhiGen.conj_zero]
    exact coeffMap_qExpand (algebraMap ℚ (CyclotomicField ℓ ℚ)) (ℓ * ℓ) jq
  apply H.injective
  rw [map_zero, Polynomial.hom_eval₂, he]
  exact hroot

end
end Dubon2026.SourceFunctionField

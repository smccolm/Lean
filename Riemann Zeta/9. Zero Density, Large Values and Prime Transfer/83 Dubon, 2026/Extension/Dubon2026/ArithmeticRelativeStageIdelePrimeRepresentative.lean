import Dubon2026.ArithmeticRelativeStageIdelePrimeInvariant
import Dubon2026.ArithmeticRelativeStageIdeleRepresentativeComparison

/-! # Canonical original-prime values have actual arithmetic representatives

Use the proved orbit-prime bijection and representative comparison to
express each canonical prime invariant at a single actual automorphism.
This connects DUB-17's arithmetic local base-change formula to the
canonical total; no compatibility of local choices is assumed.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup

variable (a : 𝓞 ℚ)
  (F H : IntermediateField ℚ (rationalUnramifiedExtension a))
  [FiniteDimensional ℚ F] [FiniteDimensional ℚ H] (hFH : F ≤ H)
  [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    IsGalois F H]

/-- Every canonical original-prime invariant is the invariant at a constructed arithmetic representative which induces exactly that original prime. -/
theorem rationalArithmeticRelativeStageIdelePrimeInvariant_exists_representative
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    ∃ (p : ℕ) (hp : p.Prime) (σ : rationalArithmeticGaloisGroup a),
      rationalArithmeticOrbitPrime a p hp F (QuotientGroup.mk σ) = w ∧
      rationalArithmeticRelativeStageIdelePrimeInvariant a F H hFH w =
        rationalArithmeticRelativeStageIdeleRepresentativeInvariant a p hp F H hFH σ := by
  let p := rationalArithmeticOriginalPrimeBase a F w
  let v : {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) //
      originalIntegerPrimeBelow F v = rationalPrimePlace p.val p.property} :=
    ⟨w, rationalArithmeticOriginalPrimeBase_below a F w⟩
  let e := rationalArithmeticOrbitPrimeEquiv a p.val p.property F
  let c := (e.symm v).out
  have he : rationalArithmeticOrbitPrime a p.val p.property F c = w :=
    (rationalArithmeticOrbitPrimeEquiv_out a p.val p.property F (e.symm v)).symm.trans
      (congrArg Subtype.val (e.apply_symm_apply v))
  have hc : (QuotientGroup.mk c.out :
      rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a F) = c :=
    Quotient.out_eq' c
  refine ⟨p.val, p.property, c.out,
    (congrArg (rationalArithmeticOrbitPrime a p.val p.property F) hc).trans he, ?_⟩
  exact (rationalArithmeticRelativeStageIdeleRepresentativeInvariant_out
    a p.val p.property F H hFH c).symm

end
end Dubon2026

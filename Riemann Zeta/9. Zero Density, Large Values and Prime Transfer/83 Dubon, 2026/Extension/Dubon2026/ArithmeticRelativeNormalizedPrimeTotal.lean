import Dubon2026.ArithmeticRelativeNormalizedPrimeLift
import Dubon2026.ArithmeticRelativeIdelePrimeOrbitSupport
import Dubon2026.ArithmeticRelativeStageIdeleTotalInvariant

/-! # The canonical total of the normalized original local trace

Choose the actual upper prime already used by the canonical base-prime
coordinate. The local normalization and proved base-prime support reduce
the genuine total to that coordinate. This is the needed normalization
at the canonical prime representatives in DUB-17's class-invariant chain.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField BigOperators

/-- One and the same original local class normalizes both its local prime coordinate and its global canonical total; this proposition alone asserts no existence. -/
def OriginalLocalTraceJointNormalization
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (localInvariant total : groupCohomology (originalFullIdeleRep K L) 2 →+ AddCircle (1 : ℚ)) : Prop :=
    letI : Fintype (Gal(L/K) ⧸ OriginalFiniteDecompositionGroup K L w) := Fintype.ofFinite _
    ∃ y : groupCohomology (originalAdicUnitRep K L w) 2,
      localInvariant (originalSinglePrimeIdeleH2Lift K L w y) =
        (↑((1 : ℚ) / Nat.card (OriginalFiniteDecompositionGroup K L w)) : AddCircle (1 : ℚ)) ∧
      total (originalSinglePrimeIdeleH2Lift K L w y) =
        (↑((1 : ℚ) / Nat.card (OriginalFiniteDecompositionGroup K L w)) : AddCircle (1 : ℚ))

attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup

variable (a : 𝓞 ℚ)
  (F H : IntermediateField ℚ (rationalUnramifiedExtension a))
  [FiniteDimensional ℚ F] [FiniteDimensional ℚ H] (hFH : F ≤ H)
  [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    IsGalois F H]

/-- At every original base prime, its actual canonical upper-prime representative has a constructed local class whose genuine trace has canonical total equal to the reciprocal decomposition degree. -/
theorem rationalArithmeticRelativeStage_exists_canonical_prime_normalized_trace
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    letI : Module F H := Algebra.toModule
    letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
    letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
    letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
    let p := rationalArithmeticOriginalPrimeBase a F v
    let c := ((rationalArithmeticOrbitPrimeEquiv a p.val p.property F).symm
      ⟨v, rationalArithmeticOriginalPrimeBase_below a F v⟩).out
    OriginalLocalTraceJointNormalization F H
      (rationalArithmeticOrbitPrime a p.val p.property H (QuotientGroup.mk c.out))
      (rationalArithmeticRelativeStageIdeleOrbitInvariant a p.val p.property F H hFH c)
      (rationalArithmeticRelativeStageIdeleTotalInvariant a F H hFH) := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
  letI : IsGalois F H := hGal
  let p := rationalArithmeticOriginalPrimeBase a F v
  let z : {z : IsDedekindDomain.HeightOneSpectrum (𝓞 F) //
      originalIntegerPrimeBelow F z = rationalPrimePlace p.val p.property} :=
    ⟨v, rationalArithmeticOriginalPrimeBase_below a F v⟩
  let e := rationalArithmeticOrbitPrimeEquiv a p.val p.property F
  let c := (e.symm z).out
  let w := rationalArithmeticOrbitPrime a p.val p.property H (QuotientGroup.mk c.out)
  letI : Fintype Gal(H/F) := AlgEquiv.fintype F H
  letI : Finite (Gal(H/F) ⧸ OriginalFiniteDecompositionGroup F H w) :=
    @Quotient.finite (Gal(H/F)) (@Fintype.finite _ (AlgEquiv.fintype F H))
      (QuotientGroup.leftRel (OriginalFiniteDecompositionGroup F H w))
  letI : Fintype (Gal(H/F) ⧸ OriginalFiniteDecompositionGroup F H w) := Fintype.ofFinite _
  obtain ⟨y, hy⟩ := rationalArithmeticRelativeStage_exists_normalized_local_trace
    (hGal := hGal) a p.val p.property F H hFH c
  have he : rationalArithmeticOrbitPrime a p.val p.property F c = v :=
    (rationalArithmeticOrbitPrimeEquiv_out a p.val p.property F (e.symm z)).symm.trans
      (congrArg Subtype.val (e.apply_symm_apply z))
  have hb : originalFinitePrimeBelow F H w = v := by
    have hbelow : originalFinitePrimeBelow F H w =
        rationalArithmeticOrbitPrime a p.val p.property F c := by
      simpa only [rationalArithmeticOrbitCoset_project_out a F H hFH c] using
        rationalArithmeticOrbitPrime_under a p.val p.property F H hFH (QuotientGroup.mk c.out)
    exact hbelow.trans he
  have hs : ∀ t : IsDedekindDomain.HeightOneSpectrum (𝓞 H),
      originalFinitePrimeBelow F H t ≠ originalFinitePrimeBelow F H w →
      originalFullIdeleAdicH2 F H t (originalSinglePrimeIdeleH2Lift F H w y) = 0 :=
    fun t ht => originalSinglePrimeIdeleH2Lift_other_base F H w t ht y
  have hz : ∀ v' : IsDedekindDomain.HeightOneSpectrum (𝓞 F), v' ≠ v →
      rationalArithmeticRelativeStageIdelePrimeInvariant a F H hFH v'
        (originalSinglePrimeIdeleH2Lift F H w y) = 0 := by
    intro v' hv'
    apply rationalArithmeticRelativeStageIdelePrimeInvariant_base_support a F H hFH w _ hs v'
    exact fun h => hv' (h.trans hb)
  refine ⟨y, hy, ?_⟩
  exact (rationalArithmeticRelativeStageIdeleTotalInvariant_apply a F H hFH
    (originalSinglePrimeIdeleH2Lift F H w y)).trans ((finsum_eq_single _ v hz).trans hy)

end
end Dubon2026

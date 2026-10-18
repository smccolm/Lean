import Dubon2026.OriginalFiniteRelationPrimeSupport
import Dubon2026.ArithmeticRelativeStageIdeleTotalInvariant

/-! Reduce the actual arithmetic total of the constructed relation class
to its specified finite base-prime family. The support follows from the
literal relation coordinates, with no local-invariant support premise.
This is the finite-sum step in DUB-17's reverse-localization argument. -/
namespace Dubon2026
noncomputable section
open CategoryTheory NumberField IsDedekindDomain
open scoped NumberField Classical BigOperators
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance 1100] Rep.hV1 Rep.hV2
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup
  finitePrimeRelationCosets

variable (a : 𝓞 ℚ)
  (F H : IntermediateField ℚ (rationalUnramifiedExtension a))
  [FiniteDimensional ℚ F] [FiniteDimensional ℚ H] [hFH : Fact (F ≤ H)]
  [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH.out).toAlgebra
    IsGalois F H]

/-- The literal finite-stage inclusion used in the canonical arithmetic total. -/
local instance finiteRelationTotalStageAlgebra : Algebra F H :=
  (IntermediateField.inclusion hFH.out).toAlgebra

/-- The module structure from that literal inclusion. -/
local instance finiteRelationTotalStageModule : Module F H :=
  @Algebra.toModule F H _ _ (finiteRelationTotalStageAlgebra a F H)

/-- The scalar action from that literal inclusion. -/
local instance finiteRelationTotalStageSMul : SMul F H :=
  @Algebra.toSMul F H _ _ (finiteRelationTotalStageAlgebra a F H)

/-- The inclusion is an actual rational algebra map. -/
local instance finiteRelationTotalStageTower : IsScalarTower ℚ F H :=
  IsScalarTower.of_algHom (IntermediateField.inclusion hFH.out)

/-- Finite degree over the actual lower arithmetic stage. -/
local instance finiteRelationTotalStageFinite : FiniteDimensional F H :=
  FiniteDimensional.right ℚ F H

/-- The given finite Galois arithmetic stage retains its original action. -/
local instance finiteRelationTotalStageGalois : IsGalois F H := hGal

/-- Vanishing at the actual upper primes over a specified base prime kills
that canonical prime invariant; its orbit representative is constructed. -/
theorem arithmeticRelativePrimeInvariant_zero_of_fibre
    (x : rationalArithmeticRelativeStageIdeleH2 a F H hFH.out)
    (v : HeightOneSpectrum (𝓞 F))
    (hx : ∀ u : HeightOneSpectrum (𝓞 H), originalFinitePrimeBelow F H u = v →
      originalFullIdeleAdicH2 F H u x = 0) :
    rationalArithmeticRelativeStageIdelePrimeInvariant a F H hFH.out v x = 0 := by
  let p := rationalArithmeticOriginalPrimeBase a F v
  let z : {u : HeightOneSpectrum (𝓞 F) //
      originalIntegerPrimeBelow F u = rationalPrimePlace p.val p.property} :=
    ⟨v, rationalArithmeticOriginalPrimeBase_below a F v⟩
  let e := rationalArithmeticOrbitPrimeEquiv a p.val p.property F
  let c := (e.symm z).out
  have hc : rationalArithmeticOrbitPrime a p.val p.property F c = v :=
    (rationalArithmeticOrbitPrimeEquiv_out a p.val p.property F (e.symm z)).symm.trans
      (congrArg Subtype.val (e.apply_symm_apply z))
  have hb : originalFinitePrimeBelow F H
      (rationalArithmeticOrbitPrime a p.val p.property H (QuotientGroup.mk c.out)) =
      rationalArithmeticOrbitPrime a p.val p.property F c := by
    simpa only [rationalArithmeticOrbitCoset_project_out a F H hFH.out c] using
      rationalArithmeticOrbitPrime_under a p.val p.property F H hFH.out (QuotientGroup.mk c.out)
  exact rationalArithmeticRelativeStageIdeleOrbitInvariant_eq_zero_of_adic
    a p.val p.property F H hFH.out c x (hx _ (hb.trans hc))

variable (S : Finset (HeightOneSpectrum (𝓞 H)))
  (hS : ∀ (σ : Gal(H/F)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv F H σ v ∈ S)
  (T : Finset (HeightOneSpectrum (𝓞 F))) (w : T → S)
  (B : Rep.{0} ℤ Gal(H/F))

/-- The canonical total of the actual finite S-place relation obstruction
is precisely the finite sum over its given base-prime family. -/
theorem arithmeticFiniteRelation_total_eq_sum
    (hw : ∀ v : T, originalFinitePrimeBelow F H (w v).val = v.val)
    (φ : ∀ v : T,
      Rep.res (OriginalFiniteDecompositionGroup F H (w v).val).subtype (originalRelationModule B) ⟶
        originalAdicUnitRep F H (w v).val)
    (y : groupCohomology B 1) :
    let u := (groupCohomology.functor ℤ Gal(H/F) 2).map (originalSPlaceFullIdeleInclusion F H S hS)
      (originalRelationExtensionObstruction B (supportedUnrestrictedUnitRep F H S hS)
        (originalFinitePrimeSPlaceRelation F H S hS T w B φ) y)
    rationalArithmeticRelativeStageIdeleTotalInvariant a F H hFH.out u =
      ∑ v ∈ T, rationalArithmeticRelativeStageIdelePrimeInvariant a F H hFH.out v u := by
  intro u
  apply finsum_eq_sum_of_support_subset
  intro v hv
  by_contra hvT
  apply hv
  apply arithmeticRelativePrimeInvariant_zero_of_fibre a F H u v
  intro t ht
  exact originalFinitePrimeSPlaceRelation_adic_zero F H S hS T w B hw φ t
    (fun h => hvT (ht ▸ h)) y

end
end Dubon2026

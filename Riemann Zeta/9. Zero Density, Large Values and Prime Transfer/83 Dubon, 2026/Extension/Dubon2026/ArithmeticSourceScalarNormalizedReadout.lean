import Dubon2026.ArithmeticSourceScalarRealizedClass
import Dubon2026.OriginalScalarNormalizedReadout

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat
variable (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Use the original arithmetic union inclusion. -/
local instance sourceNormalizedReadoutUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := AlgebraicClosure ℚ) a) :=
  (originalUnramifiedGaloisUnion (Ω := AlgebraicClosure ℚ) a).algebra'

variable [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := AlgebraicClosure ℚ) a))]
  (P : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := AlgebraicClosure ℚ) a))

/-- Use the actual finite stage inclusion. -/
local instance sourceNormalizedReadoutFiniteAlgebra {L : Type} [Field L] [Algebra ℚ L]
    (F : FiniteGaloisIntermediateField ℚ L) : Algebra ℚ F := F.algebra'

variable (B : Rep.{0} ℤ Gal(P/ℚ))

variable [TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ (AlgebraicClosure ℚ) a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ (AlgebraicClosure ℚ) a ha)]
  [TopologicalSpace (arithmeticFiniteCoefficientSourceClassHom (AlgebraicClosure ℚ) a ha P B)]
  [DiscreteTopology (arithmeticFiniteCoefficientSourceClassHom (AlgebraicClosure ℚ) a ha P B)]

/-- Integer scalar multiplication on the original discrete Hom is continuous. -/
local instance sourceNormalizedReadoutHomContinuousSMul :
    @ContinuousSMul ℤ (arithmeticFiniteCoefficientSourceClassHom (AlgebraicClosure ℚ) a ha P B)
      (arithmeticFiniteCoefficientSourceClassHom (AlgebraicClosure ℚ) a ha P B).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticFiniteCoefficientSourceClassHom (AlgebraicClosure ℚ) a ha P B)
    (arithmeticFiniteCoefficientSourceClassHom (AlgebraicClosure ℚ) a ha P B).hV2.toSMul _ _ continuous_of_discreteTopology

/-- The canonical scalar readout of the exact source obstruction,
using its realized Sylow class and the proved idele-total-normalized invariant. -/
def arithmeticSourceScalarNormalizedReadout
    (c : continuousRepresentationCocyclesOne (arithmeticFiniteCoefficientSourceClassHom (AlgebraicClosure ℚ) a ha P B))
    (r : ArithmeticSourceClassRelationData (AlgebraicClosure ℚ) a ha P B c)
    (F : OriginalUnramifiedGaloisStage (Ω := AlgebraicClosure ℚ) a) (i : r.stage →ₐ[ℚ] F.val)
    (L : OriginalUnramifiedGaloisStage (Ω := AlgebraicClosure ℚ) a)
    (hFL : F.val.toIntermediateField ≤ L.val.toIntermediateField)
    (p : ℕ) [Fact p.Prime] (hpa : (p : 𝓞 ℚ) ∣ a) (S : Sylow p Gal(L.val/ℚ)) :
    groupCohomology (arithmeticSourceScalarStageCoefficient (AlgebraicClosure ℚ) a ha P B c r F i L hFL) 1 →+
      AddCircle (1 : ℚ) :=
  (originalScalarRealizedClassInvariant a L p hpa S).comp
    (arithmeticSourceScalarRealizedClass (AlgebraicClosure ℚ) a ha P B c r F i L hFL p S).toAddMonoidHom

omit [TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ (AlgebraicClosure ℚ) a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ (AlgebraicClosure ℚ) a ha)] in
/-- Vanishing of the original scalar relation obstruction is equivalent
to vanishing of its constructed canonical normalized readout. -/
theorem arithmeticSourceScalarObstruction_eq_zero_iff_normalizedReadout
    (c : continuousRepresentationCocyclesOne (arithmeticFiniteCoefficientSourceClassHom (AlgebraicClosure ℚ) a ha P B))
    (r : ArithmeticSourceClassRelationData (AlgebraicClosure ℚ) a ha P B c)
    (F : OriginalUnramifiedGaloisStage (Ω := AlgebraicClosure ℚ) a) (i : r.stage →ₐ[ℚ] F.val)
    (L : OriginalUnramifiedGaloisStage (Ω := AlgebraicClosure ℚ) a)
    (hFL : F.val.toIntermediateField ≤ L.val.toIntermediateField)
    (p : ℕ) [Fact p.Prime] (hpa : (p : 𝓞 ℚ) ∣ a) (S : Sylow p Gal(L.val/ℚ))
    (hB : ∀ b : B, p • b = 0)
    (y : groupCohomology (arithmeticSourceScalarStageCoefficient (AlgebraicClosure ℚ) a ha P B c r F i L hFL) 1) :
    let BL := arithmeticSourceScalarStageCoefficient (AlgebraicClosure ℚ) a ha P B c r F i L hFL
    let C := arithmeticOriginalStageClassRep (AlgebraicClosure ℚ) a ha L
    let ψ := arithmeticSourceScalarStageRelationTransport (AlgebraicClosure ℚ) a ha P B c r F i L hFL
    (originalRelationExtensionObstruction BL C ψ).hom y = 0 ↔
      arithmeticSourceScalarNormalizedReadout a ha P B c r F i L hFL p hpa S y = 0 := by
  let f := originalScalarRealizedClassInvariant a L p hpa S
  have hf : Function.Injective f := originalScalarRealizedClassInvariant_injective a L p hpa S
  have hz (z) : f z = 0 ↔ z = 0 := hf.eq_iff' (map_zero f)
  exact (arithmeticSourceScalarObstruction_eq_zero_iff_realizedClass
    (AlgebraicClosure ℚ) a ha P B c r F i L hFL p S hB y).trans
    (hz (arithmeticSourceScalarRealizedClass (AlgebraicClosure ℚ) a ha P B c r F i L hFL p S y)).symm

omit [TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ (AlgebraicClosure ℚ) a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ (AlgebraicClosure ℚ) a ha)] in
/-- The normalized scalar value is killed by the coefficient prime,
as required for the finite-prime pairing separation step. -/
theorem arithmeticSourceScalarNormalizedReadout_nsmul_zero
    (c : continuousRepresentationCocyclesOne (arithmeticFiniteCoefficientSourceClassHom (AlgebraicClosure ℚ) a ha P B))
    (r : ArithmeticSourceClassRelationData (AlgebraicClosure ℚ) a ha P B c)
    (F : OriginalUnramifiedGaloisStage (Ω := AlgebraicClosure ℚ) a) (i : r.stage →ₐ[ℚ] F.val)
    (L : OriginalUnramifiedGaloisStage (Ω := AlgebraicClosure ℚ) a)
    (hFL : F.val.toIntermediateField ≤ L.val.toIntermediateField)
    (p : ℕ) [Fact p.Prime] (hpa : (p : 𝓞 ℚ) ∣ a) (S : Sylow p Gal(L.val/ℚ))
    (hB : ∀ b : B, p • b = 0)
    (y : groupCohomology (arithmeticSourceScalarStageCoefficient (AlgebraicClosure ℚ) a ha P B c r F i L hFL) 1) :
    p • arithmeticSourceScalarNormalizedReadout a ha P B c r F i L hFL p hpa S y = 0 := by
  let f := originalScalarRealizedClassInvariant a L p hpa S
  let z := arithmeticSourceScalarRealizedClass (AlgebraicClosure ℚ) a ha P B c r F i L hFL p S y
  have h := congrArg f (arithmeticSourceScalarRealizedClass_nsmul_zero
    (AlgebraicClosure ℚ) a ha P B c r F i L hFL p S hB y)
  exact (map_nsmul f p z).symm.trans (h.trans (map_zero f))

end
end Dubon2026

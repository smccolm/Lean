import Dubon2026.OriginalSourceClassSaturationValuation
import Dubon2026.ArithmeticTorsionClassStageLifting

/-! The source-class image is saturated under the coefficient prime after
an actual enlargement in the same unramified union. The existing Kummer
root stage and literal idele correction discharge this lifting obligation
for DUB-17's constructed relation extension. -/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  [IsAlgClosure K Ω] (a : 𝓞 K) (ha : a ≠ 0)
  (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 K) ∣ a)
  (E : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))

local instance sourceClassRootStageNumberField : NumberField E := NumberField.of_module_finite K E

include hqa in
private theorem representative_lift
    (x : (AdeleRing (𝓞 E) E)ˣ)
    (s : ArithmeticSPlaceClassFiniteStageRep K Ω a ha E)
    (hx : q • (originalIdeleClassesModOutsideRepHom K E
      (arithmeticSUnitFiniteStageSupport K Ω a ha E)
      (originalExceptionalIntegerSupport_galoisStable E K a ha)).hom
        (Additive.ofMul (QuotientGroup.mk' (numberFieldPrincipalIdele E).range x)) =
          (arithmeticSourceClassStageComparison K Ω a ha E).hom s) :
    ∃ (F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
      (hEF : E ≤ F) (z : ArithmeticSPlaceClassFiniteStageRep K Ω a ha F),
      (arithmeticSourceClassStageComparison K Ω a ha F).hom z =
        arithmeticClassesModOutsideTransitionMap K Ω a ha E F hEF
          ((originalIdeleClassesModOutsideRepHom K E
            (arithmeticSUnitFiniteStageSupport K Ω a ha E)
            (originalExceptionalIntegerSupport_galoisStable E K a ha)).hom
              (Additive.ofMul (QuotientGroup.mk' (numberFieldPrincipalIdele E).range x))) := by
  obtain ⟨u, hu, hu'⟩ := originalSourceClassPower_exists_base_valuation_witness K E _ _ q x s hx
  have hv : ∀ v : HeightOneSpectrum (𝓞 E), algebraMap (𝓞 K) (𝓞 E) a ∉ v.asIdeal →
      ∃ c : Eˣ, v.valuation E (u : E) = v.valuation E (c : E) ^ q := by
    intro v hv
    apply hu' v
    simpa only [arithmeticSUnitFiniteStageSupport, mem_originalExceptionalIntegerSupport] using hv
  obtain ⟨F, hEF, β, hβ⟩ := arithmeticValuationDivisibleUnit_exists_root_stage K Ω a ha q hqa E u hv
  letI : NumberField F := NumberField.of_module_finite K F
  letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
  haveI : IsScalarTower K E F := .of_algebraMap_eq' rfl
  have hβ' : (β : F) ^ q = algebraMap E F (u : E) := congrArg Units.val hβ
  obtain ⟨z, hz⟩ := originalSourceClass_exists_of_root_correction K E F
    (arithmeticSUnitFiniteStageSupport K Ω a ha E)
    (arithmeticSUnitFiniteStageSupport K Ω a ha F)
    (originalExceptionalIntegerSupport_galoisStable E K a ha)
    (originalExceptionalIntegerSupport_galoisStable F K a ha)
    (arithmeticSPlaceFiniteStage_support K Ω a ha E F hEF)
    q (Fact.out : q.Prime).pos x u hu β hβ'
  exact ⟨F, hEF, z, hz⟩

include hqa in
/-- If the coefficient-prime multiple of an actual full class is an
S-place class, the original class itself lifts after a constructed finite
enlargement, with its precise original transition value. -/
theorem arithmeticSourceClassPower_exists_source_stage
    (c : arithmeticClassesModOutsideStageRep K Ω a ha E)
    (s : ArithmeticSPlaceClassFiniteStageRep K Ω a ha E)
    (hc : q • c = (arithmeticSourceClassStageComparison K Ω a ha E).hom s) :
    ∃ (F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
      (hEF : E ≤ F) (z : ArithmeticSPlaceClassFiniteStageRep K Ω a ha F),
      (arithmeticSourceClassStageComparison K Ω a ha F).hom z =
        arithmeticClassesModOutsideTransitionMap K Ω a ha E F hEF c := by
  induction c using Submodule.Quotient.induction_on with
  | H c =>
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (numberFieldPrincipalIdele E).range c.toMul
    have hx' : Additive.ofMul (QuotientGroup.mk' (numberFieldPrincipalIdele E).range x) = c :=
      congrArg Additive.ofMul hx
    cases hx'
    exact representative_lift K Ω a ha q hqa E x s hc

end
end Dubon2026

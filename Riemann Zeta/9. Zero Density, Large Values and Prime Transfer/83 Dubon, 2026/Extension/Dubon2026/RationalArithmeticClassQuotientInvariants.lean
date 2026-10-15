import Dubon2026.ArithmeticClassQuotientTransitionInjectivity
import Dubon2026.ArithmeticClassesModOutsideH1

/-! # Original rational arithmetic class-quotient invariants

Absolute unramifiedness is proved for every original arithmetic stage.
The actual base quotient therefore equals its finite-stage invariants,
without a class-descent or local-vanishing hypothesis. This discharges
the finite invariant coefficient comparison on DUB-17's class-formation
route; global invariant maps and Ext duality remain separate obligations.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- The original rational full classes modulo units outside the unchanged exceptional support. -/
abbrev rationalArithmeticBaseClassQuotient :=
  originalIdeleClassesModOutsideRep ℚ ℚ (originalExceptionalIntegerSupport ℚ a ha)
    (fun σ v => by
      have he : σ = 1 := Subsingleton.elim _ _
      rw [he, numberFieldGaloisPlaceEquiv_one])

variable (Ω : Type) [Field Ω] [Algebra ℚ Ω]

/-- The original union carries its literal rational field inclusion. -/
local instance classFiniteInvariantUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

variable (F : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))

/-- The original finite arithmetic field carries its literal rational field inclusion. -/
local instance classFiniteInvariantStageAlgebra : Algebra ℚ F := F.algebra'
/-- The original finite arithmetic field is a number field. -/
local instance classFiniteInvariantStageNumberField : NumberField F := NumberField.of_module_finite ℚ F

/-- The genuine base class quotient is exactly the actual finite arithmetic class-quotient invariant coefficient. -/
def rationalArithmeticClassQuotientInvariantEquiv :
    rationalArithmeticBaseClassQuotient a ha ≃ₗ[ℤ]
      (arithmeticClassesModOutsideStageRep ℚ Ω a ha F).ρ.invariants :=
  originalClassesModOutsideBaseInvariantEquiv ℚ F
    (originalExceptionalIntegerSupport ℚ a ha) (arithmeticSUnitFiniteStageSupport ℚ Ω a ha F)
    (fun σ v => by
      have he : σ = 1 := Subsingleton.elim _ _
      rw [he, numberFieldGaloisPlaceEquiv_one])
    (originalExceptionalIntegerSupport_galoisStable F ℚ a ha)
    (originalExceptionalIntegerSupport_baseChange ℚ F a ha)
    (rationalArithmeticFiniteStage_outside_unramified Ω a ha F)

/-- The actual invariant equivalence retains the original base-field idele-class representative. -/
theorem rationalArithmeticClassQuotientInvariantEquiv_mk
    (c : OriginalNumberFieldIdeleClassGroup ℚ) :
    (rationalArithmeticClassQuotientInvariantEquiv a ha Ω F
      (Submodule.Quotient.mk (Additive.ofMul c))).val =
      (originalIdeleClassesModOutsideRepHom ℚ F (arithmeticSUnitFiniteStageSupport ℚ Ω a ha F)
        (originalExceptionalIntegerSupport_galoisStable F ℚ a ha)).hom
        (Additive.ofMul (originalIdeleClassBaseChangeMap ℚ F c)) := rfl

/-- Every original rational arithmetic invariant quotient class has a unique genuine base quotient preimage. -/
theorem rationalArithmeticClassQuotientInvariant_unique_base
    (x : (arithmeticClassesModOutsideStageRep ℚ Ω a ha F).ρ.invariants) :
    ∃! c : rationalArithmeticBaseClassQuotient a ha,
      rationalArithmeticClassQuotientInvariantEquiv a ha Ω F c = x :=
  (rationalArithmeticClassQuotientInvariantEquiv a ha Ω F).toEquiv.bijective.existsUnique x

end
end Dubon2026

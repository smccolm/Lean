import Dubon2026.OriginalRationalNormFieldExistence
import Dubon2026.OriginalEmbeddedNormFieldStageRoots

/-! # Enlarged-stage invariant norm roots from the constructed norm field

The actual original-base norm field now supplies both containment and
ramification to the proved stage construction. Thus no norm-field or
normalization premise remains. The input base is unramified outside the
original integer; the exact arithmetic consumer derives that condition
from membership in the original union. Prime divisibility of the enlarged
relative degree remains a separate cyclotomic enlargement step.
-/
namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2 Submodule.module
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
variable (E Ω : Type) [Field E] [NumberField E] [Field Ω]
  [Algebra ℚ Ω] [Algebra E Ω] [IsScalarTower ℚ E Ω] [IsAlgClosure ℚ Ω]

/-- The constructed original norm field supplies invariant roots of all
actual quotient norms at an original unramified Galois stage above any
prescribed stage, preserving the given base embedding. -/
theorem originalNumberField_exists_enlarged_stage_norm_roots
    (a : 𝓞 ℚ) (ha : a ≠ 0)
    (P : OriginalUnramifiedGaloisStage (Ω := Ω) a)
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (ζ : E) (hζ : IsPrimitiveRoot ζ p)
    (hBase : ∀ v : HeightOneSpectrum (𝓞 E), algebraMap (𝓞 ℚ) (𝓞 E) a ∉ v.asIdeal →
      (v.asIdeal.under (𝓞 ℚ)).ramificationIdx v.asIdeal = 1) :
    let S := originalExceptionalIntegerSupport E (algebraMap (𝓞 ℚ) (𝓞 E) a)
      (originalIntegerMap_ne_zero (L := E) a ha)
    ∃ N : OriginalUnramifiedGaloisStage (Ω := Ω) a,
      letI : Algebra ℚ N.val := N.val.algebra'
      ∃ j : E →ₐ[ℚ] N.val,
      (∀ x : E, (j x : Ω) = algebraMap E Ω x) ∧
      P.val.toIntermediateField ≤ N.val.toIntermediateField ∧
      letI : Algebra E N.val := j.toRingHom.toAlgebra
      letI : IsScalarTower ℚ E N.val := IsScalarTower.of_algHom j
      letI : FiniteDimensional E N.val := FiniteDimensional.right ℚ E N.val
      OriginalOutsideQuotientInvariantNormRoots E N.val S p := by
  obtain ⟨L, hL, hNL, hEL, hFinite, hGal, hn, hu⟩ :=
    originalNumberField_exists_rational_power_norm_field E a ha p hp2 ζ hζ
  letI := hL
  letI := hNL
  letI := hEL
  letI := hFinite
  letI := hGal
  exact originalEmbeddedNormField_exists_stage_invariant_norm_roots ℚ E L Ω a ha P _
    (fun σ v => originalExceptionalIntegerSupport_galoisStable E ℚ a ha
      (σ.restrictScalars ℚ) v) p hBase hu hn

end
end Dubon2026

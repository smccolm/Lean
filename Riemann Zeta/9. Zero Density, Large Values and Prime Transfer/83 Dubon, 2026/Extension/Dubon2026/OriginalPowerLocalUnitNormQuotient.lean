import Dubon2026.OriginalNormRamificationSupport
import Dubon2026.OriginalIdeleClassNativeNormQuotient

/-! # The actual power/local-unit quotient surjects onto the original norm quotient

This is the precise cardinal comparison needed in DUB-17's norm-index
upper bound. The original class local-condition subgroup is merely
written in additive notation for the existing literal norm quotient.
No cardinal estimate or finiteness for the power quotient is asserted
without proof; those remain the selected-prime/S-unit calculation.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
variable (K : Type) [Field K] [NumberField K]

/-- The original class power/local-unit subgroup expressed in the canonical additive integer module. -/
def originalIdeleClassPowerLocalUnitSubmodule (n : ℕ) (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    Submodule ℤ (Additive (OriginalNumberFieldIdeleClassGroup K)) :=
  ({ carrier := {x | x.toMul ∈ originalIdeleClassPowerLocalUnitSubgroup K n S T}
     zero_mem' := (originalIdeleClassPowerLocalUnitSubgroup K n S T).one_mem
     add_mem' := fun hx hy => (originalIdeleClassPowerLocalUnitSubgroup K n S T).mul_mem hx hy
     neg_mem' := fun hx => (originalIdeleClassPowerLocalUnitSubgroup K n S T).inv_mem hx } :
      AddSubgroup (Additive (OriginalNumberFieldIdeleClassGroup K))).toIntSubmodule

/-- The actual original class quotient by the source power/local-unit subgroup, in additive notation. -/
abbrev OriginalIdeleClassPowerLocalUnitQuotient (n : ℕ) (S T : Finset (HeightOneSpectrum (𝓞 K))) :=
  Additive (OriginalNumberFieldIdeleClassGroup K) ⧸ originalIdeleClassPowerLocalUnitSubmodule K n S T

variable (L : Type) [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
attribute [local instance] IsCyclic.commGroup
variable (S T : Finset (HeightOneSpectrum (𝓞 K)))
  (hT : ∀ w : HeightOneSpectrum (𝓞 L), originalFinitePrimeBelow K L w ∈ T →
    OriginalFiniteDecompositionGroup K L w = ⊥)

include hT in
attribute [-instance] UniformSpace.Completion.instSMul in
/-- The proved actual class norm containment is the same inclusion in the original additive norm quotient. -/
theorem originalPowerLocalUnitSubmodule_le_normRange :
    originalIdeleClassPowerLocalUnitSubmodule K (Module.finrank K L)
      (S ∪ originalNormRamificationSupport K L) T ≤ (originalIdeleClassNormLinear K L).range := by
  intro x hx
  obtain ⟨y, hy⟩ := originalIdeleClassPowerLocalUnitSubgroup_le_norm_enlarged K L S T hT hx
  exact ⟨Additive.ofMul y, congrArg Additive.ofMul hy⟩

attribute [-instance] UniformSpace.Completion.instSMul in
/-- The canonical map of actual original class quotients induced by the proved local norm containment. -/
def originalPowerLocalUnitNormQuotientMap :
    OriginalIdeleClassPowerLocalUnitQuotient K (Module.finrank K L)
      (S ∪ originalNormRamificationSupport K L) T →ₗ[ℤ] OriginalIdeleClassNormQuotient K L :=
  (originalIdeleClassPowerLocalUnitSubmodule K (Module.finrank K L)
    (S ∪ originalNormRamificationSupport K L) T).mapQ (originalIdeleClassNormLinear K L).range
      LinearMap.id (originalPowerLocalUnitSubmodule_le_normRange K L S T hT)

attribute [-instance] UniformSpace.Completion.instSMul in
/-- Every actual original norm class comes from the original power/local-unit quotient. -/
theorem originalPowerLocalUnitNormQuotientMap_surjective :
    Function.Surjective (originalPowerLocalUnitNormQuotientMap K L S T hT) := by
  intro x
  obtain ⟨c, rfl⟩ := (originalIdeleClassNormLinear K L).range.mkQ_surjective x
  exact ⟨(originalIdeleClassPowerLocalUnitSubmodule K (Module.finrank K L)
    (S ∪ originalNormRamificationSupport K L) T).mkQ c, rfl⟩

include hT in
attribute [-instance] UniformSpace.Completion.instSMul in
/-- Finiteness and the selected-prime cardinal calculation for the actual power quotient suffice for the required original norm-quotient upper bound. -/
theorem originalIdeleClassNormQuotient_card_le_powerLocalUnitQuotient
    [Finite (OriginalIdeleClassPowerLocalUnitQuotient K (Module.finrank K L)
      (S ∪ originalNormRamificationSupport K L) T)] :
    Nat.card (OriginalIdeleClassNormQuotient K L) ≤
      Nat.card (OriginalIdeleClassPowerLocalUnitQuotient K (Module.finrank K L)
        (S ∪ originalNormRamificationSupport K L) T) :=
  Nat.card_le_card_of_surjective _ (originalPowerLocalUnitNormQuotientMap_surjective K L S T hT)

end
end Dubon2026

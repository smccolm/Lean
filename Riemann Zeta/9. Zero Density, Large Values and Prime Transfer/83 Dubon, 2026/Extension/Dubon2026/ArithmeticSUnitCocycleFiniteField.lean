import Dubon2026.ArithmeticSUnitRepresentation
import Dubon2026.ContinuousGaloisTwoCocycleFiniteField

/-! # Original continuous S-unit cocycles at actual finite Galois fields

Common open normal periods fix the actual coefficient values. The original
Galois correspondence therefore gives a finite field inside the same
unramified union, retaining both the S-unit values and the restriction fibers.
This is the first descent input for the continuous arithmetic Ext comparison.
-/

namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  (a : 𝓞 K) (ha : a ≠ 0)
  [TopologicalSpace (originalArithmeticSUnitRepresentation K Ω a ha)]
  [DiscreteTopology (originalArithmeticSUnitRepresentation K Ω a ha)]

local instance : @ContinuousSMul ℤ (originalArithmeticSUnitRepresentation K Ω a ha)
    (originalArithmeticSUnitRepresentation K Ω a ha).hV2.toSMul inferInstance inferInstance :=
  ⟨continuous_of_discreteTopology⟩

/-- Every actual continuous arithmetic S-unit two-cocycle has its original values and common periods at one actual finite Galois field in the same unramified union. -/
theorem originalArithmeticSUnitTwoCocycle_exists_finiteField
    (c : continuousRepresentationCocyclesTwo (originalArithmeticSUnitRepresentation K Ω a ha)) :
    ∃ F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a),
      (∀ g h : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K),
        (c.val (g, h)).toMul.val.val ∈ F.toIntermediateField) ∧
      (∀ g h u v : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K),
        AlgEquiv.restrictNormalHom F u = 1 → AlgEquiv.restrictNormalHom F v = 1 →
          c.val (g * u, h * v) = c.val (g, h)) := by
  let Γ := originalUnramifiedGaloisUnion (Ω := Ω) a
  let A := originalArithmeticSUnitRepresentation K Ω a ha
  letI : IsGalois K Γ := originalUnramifiedGaloisUnion_isGalois a
  obtain ⟨U, hperiod, hfixed⟩ := continuousTwoCocycle_exists_openNormal_periods_and_fixed A c
  let H : ClosedSubgroup Gal(Γ/K) := ⟨U.toSubgroup, U.isClosed⟩
  let E := IntermediateField.fixedField U.toSubgroup
  have hfix : E.fixingSubgroup = U.toSubgroup := InfiniteGalois.fixingSubgroup_fixedField H
  letI : FiniteDimensional K E := by
    apply (InfiniteGalois.isOpen_iff_finite E).mp
    simpa only [hfix] using U.isOpen
  letI : IsGalois K E := by
    apply (InfiniteGalois.normal_iff_isGalois E).mp
    rw [hfix]
    infer_instance
  let F : FiniteGaloisIntermediateField K Γ := ⟨E⟩
  refine ⟨F, ?_, ?_⟩
  · intro g h
    apply (IntermediateField.mem_fixedField_iff _ _).mpr
    intro u hu
    exact congrArg (fun z : A => z.toMul.val.val) (hfixed u hu g h)
  · intro g h u v hu hv
    have hmu : u ∈ E.fixingSubgroup :=
      (FiniteGaloisIntermediateField.mem_fixingSubgroup_iff u F).mpr hu
    have hmv : v ∈ E.fixingSubgroup :=
      (FiniteGaloisIntermediateField.mem_fixingSubgroup_iff v F).mpr hv
    rw [hfix] at hmu hmv
    exact hperiod g h u v hmu hmv

end
end Dubon2026

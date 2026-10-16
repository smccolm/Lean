import Dubon2026.OriginalClassH2InvariantFromGenerator

/-! # Normalized original class invariants from a constructed witness

Unpack the full-order witness before the arithmetic specialization.
The existing original full-order theorem proves all subgroup normalization
and exact-image conclusions used in DUB-17's finite-stage invariant chain.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [-instance] SubfieldClass.instSMulRat
attribute [local instance 1100] Rep.hV2 AddCommGroup.toAddCommMonoid

/-- An existing full-order original class gives the original normalized global and subgroup invariants with exact images and the restriction-index formula. -/
theorem originalIdeleClass_invariant_system_of_full_order_witness
    (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E]
    [Algebra K E] [FiniteDimensional K E] [IsGalois K E] :
    (∃ u : groupCohomology (originalIdeleClassRep K E) 2,
      addOrderOf u = Module.finrank K E) →
    ∃ u : groupCohomology (originalIdeleClassRep K E) 2,
      addOrderOf u = Module.finrank K E ∧
      ∃ invG : groupCohomology (originalIdeleClassRep K E) 2 →+ AddCircle (1 : ℚ),
        Function.Injective invG ∧
        (∀ z : AddCircle (1 : ℚ), z ∈ invG.range ↔ Module.finrank K E • z = 0) ∧
        invG u = ↑((1 : ℚ) / Module.finrank K E) ∧
        ∀ S : Subgroup Gal(E/K),
          ∃ invS : groupCohomology (Rep.res S.subtype (originalIdeleClassRep K E)) 2 →+ AddCircle (1 : ℚ),
            Function.Injective invS ∧
            (∀ z : AddCircle (1 : ℚ), z ∈ invS.range ↔ Nat.card S • z = 0) ∧
            ∀ x : groupCohomology (originalIdeleClassRep K E) 2,
              invS ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (originalIdeleClassRep K E))) 2).hom x) =
                S.index • invG x := by
  rintro ⟨u, hu⟩
  exact ⟨u, hu, originalIdeleClass_exists_invariants_of_full_order K E u hu⟩

/-- The original injective normalized subgroup invariants identify every restriction kernel with annihilation by the actual subgroup index. -/
theorem originalIdeleClass_restriction_kernel_of_invariant_system
    (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E]
    [Algebra K E]
    (h : ∃ u : groupCohomology (originalIdeleClassRep K E) 2,
      addOrderOf u = Module.finrank K E ∧
      ∃ invG : groupCohomology (originalIdeleClassRep K E) 2 →+ AddCircle (1 : ℚ),
        Function.Injective invG ∧
        (∀ z : AddCircle (1 : ℚ), z ∈ invG.range ↔ Module.finrank K E • z = 0) ∧
        invG u = ↑((1 : ℚ) / Module.finrank K E) ∧
        ∀ S : Subgroup Gal(E/K),
          ∃ invS : groupCohomology (Rep.res S.subtype (originalIdeleClassRep K E)) 2 →+ AddCircle (1 : ℚ),
            Function.Injective invS ∧
            (∀ z : AddCircle (1 : ℚ), z ∈ invS.range ↔ Nat.card S • z = 0) ∧
            ∀ x : groupCohomology (originalIdeleClassRep K E) 2,
              invS ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (originalIdeleClassRep K E))) 2).hom x) =
                S.index • invG x) :
    ∃ invG : groupCohomology (originalIdeleClassRep K E) 2 →+ AddCircle (1 : ℚ),
      Function.Injective invG ∧
      (∀ z : AddCircle (1 : ℚ), z ∈ invG.range ↔ Module.finrank K E • z = 0) ∧
      ∀ (S : Subgroup Gal(E/K)) (x : groupCohomology (originalIdeleClassRep K E) 2),
        (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (originalIdeleClassRep K E))) 2).hom x = 0 ↔
          S.index • invG x = 0 := by
  obtain ⟨_, _, invG, hiG, hrG, _, hsub⟩ := h
  refine ⟨invG, hiG, hrG, ?_⟩
  intro S x
  obtain ⟨invS, hiS, _, hs⟩ := hsub S
  constructor
  · intro hx
    rw [← hs x, hx, map_zero]
  · intro hx
    apply hiS
    rw [map_zero, hs x, hx]

end
end Dubon2026

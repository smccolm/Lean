import Dubon2026.ContinuousCorestrictionMackey
import Dubon2026.ContinuousCorestrictionCoefficientMap

/-! # The original Mackey formula with its actual coefficient embedding

This combines the native coefficient/corestriction square with the proved
orbit formula. It is the exact interface for DUB-17's completion-unit map.
-/

namespace Dubon2026
noncomputable section
open scoped BigOperators

variable {R D G : Type} [CommRing R] [Group D] [Group G]
  [TopologicalSpace R] [TopologicalSpace D] [TopologicalSpace G]
  [IsTopologicalGroup D] [IsTopologicalGroup G]
  (A : Rep R G) [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (φ : D →* G) (hφ : Continuous φ)
  (B : Rep R D) [TopologicalSpace B] [IsTopologicalAddGroup B] [ContinuousSMul R B]
  (hB : Continuous (fun z : D × B => B.ρ z.1 z.2))
  (f : A →ₗ[R] B) (hf : Continuous f) (hfρ : ∀ d x, f (A.ρ (φ d) x) = B.ρ d (f x))
  (S : Subgroup G) (hS : IsOpen (S : Set G))
  [Fintype (G ⧸ S)] [Fintype (cosetOrbitIndex φ S)]
  [∀ ω : cosetOrbitIndex φ S, Fintype (D ⧸ cosetOrbitStabilizer φ S ω.out)]

/-- Actual coefficient embedding, restriction and transfer give the sum
of actual local stabilizer transfers, with no Mackey premise assumed. -/
theorem continuousCoefficientH2Map_restriction_corestriction_orbits
    (c : continuousRepresentationCocyclesTwo (restrictedCoefficientRep A S.subtype)) :
    continuousCoefficientH2Map (restrictedCoefficientRep A φ) B f hf hfρ
        (restrictedCoefficientAction_continuous A φ hφ hA) hB
        (continuousRepresentationH2Restriction A hA φ hφ
          (continuousRepresentationH2Corestriction A hA S hS (Submodule.Quotient.mk c))) =
      ∑ ω : cosetOrbitIndex φ S,
        continuousRepresentationH2Corestriction B hB (cosetOrbitStabilizer φ S ω.out)
          (cosetOrbitStabilizer_isOpen φ hφ S hS ω.out)
          (Submodule.Quotient.mk
            (continuousCoefficientCocycleTwoMap
              (restrictedCoefficientRep (restrictedCoefficientRep A φ) (cosetOrbitStabilizer φ S ω.out).subtype)
              (restrictedCoefficientRep B (cosetOrbitStabilizer φ S ω.out).subtype)
              f hf (fun d x => hfρ d x) (continuousCosetOrbitCocycle A hA φ hφ S ω.out c))) := by
  rw [continuousRepresentationH2Corestriction_mackey, map_sum]
  apply Finset.sum_congr rfl
  intro ω _
  rw [continuousCoefficientH2Map_corestriction, continuousCoefficientH2Map_mk]

end
end Dubon2026

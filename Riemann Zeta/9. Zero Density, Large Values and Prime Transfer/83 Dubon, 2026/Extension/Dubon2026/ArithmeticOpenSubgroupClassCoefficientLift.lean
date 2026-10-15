import Dubon2026.CompactCoefficientColimitLift
import Dubon2026.ArithmeticClassQuotientTransitionInjectivity

/-! # Original open-subgroup class cocycles lift to an arithmetic coefficient stage

The existing compact coefficient-colimit cochain lift and the proved
injective original stage inclusions retain the literal cocycle identity.
This separates coefficient lifting from
finite Galois image descent for the open-subgroup class H1 input required
by DUB-17's arithmetic class formation and global duality.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  (a : 𝓞 K) (ha : a ≠ 0)
  [DecidableEq (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  [TopologicalSpace (arithmeticClassesModOutsideColimitRep K Ω a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep K Ω a ha)]

/-- Each original finite arithmetic class quotient carries its discrete coefficient topology. -/
local instance openClassLiftStageTopology (F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a)) :
    TopologicalSpace (arithmeticGlobalClassesModOutsideStageRep K Ω a ha F) := ⊥
/-- The original finite arithmetic class coefficient topology is discrete. -/
local instance openClassLiftStageDiscrete (F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a)) :
    DiscreteTopology (arithmeticGlobalClassesModOutsideStageRep K Ω a ha F) := ⟨rfl⟩

/-- The original open-subgroup cocycle lifts with unchanged values to a continuous cocycle in one actual coefficient stage. -/
theorem arithmeticOpenSubgroupClassOneCocycle_exists_coefficient_lift
    (H : OpenSubgroup Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K))
    (c : H → arithmeticClassesModOutsideColimitRep K Ω a ha) (hc : Continuous c)
    (hcc : ∀ g h, c (g * h) =
      (arithmeticClassesModOutsideColimitRep K Ω a ha).ρ g.val (c h) + c g) :
    ∃ E : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a),
      ∃ b : H → arithmeticGlobalClassesModOutsideStageRep K Ω a ha E,
        Continuous b ∧
        (∀ g h, b (g * h) =
          (arithmeticGlobalClassesModOutsideStageRep K Ω a ha E).ρ g.val (b h) + b g) ∧
        ∀ g : H, (coefficientRepresentationColimitOf
          (arithmeticGlobalClassesModOutsideStageRep K Ω a ha)
          (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha) E).hom (b g) = c g := by
  letI : IsGalois K (originalUnramifiedGaloisUnion (Ω := Ω) a) := originalUnramifiedGaloisUnion_isGalois a
  letI : IsTopologicalGroup H := inferInstanceAs (IsTopologicalGroup H.toSubgroup)
  letI : CompactSpace H := isCompact_iff_compactSpace.mp H.isClosed.isCompact
  obtain ⟨E, b, hbc, hb⟩ := @compactCoefficientColimit_exists_lift ℤ
    (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    _ _ _ _ _ (fun F => arithmeticGlobalClassesModOutsideStageRep K Ω a ha F)
    (fun F => (arithmeticGlobalClassesModOutsideStageRep K Ω a ha F).hV1)
    (fun F => (arithmeticGlobalClassesModOutsideStageRep K Ω a ha F).hV2)
    (fun E F h => (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha E F h).hom.toLinearMap)
    (inferInstance : TopologicalSpace (arithmeticClassesModOutsideColimitRep K Ω a ha))
    (inferInstance : DiscreteTopology (arithmeticClassesModOutsideColimitRep K Ω a ha))
    (fun F => (inferInstance : TopologicalSpace (arithmeticGlobalClassesModOutsideStageRep K Ω a ha F)))
    (fun F => (inferInstance : DiscreteTopology (arithmeticGlobalClassesModOutsideStageRep K Ω a ha F)))
    H inferInstance inferInstance c hc
  have hb' (g : H) : (coefficientRepresentationColimitOf
      (arithmeticGlobalClassesModOutsideStageRep K Ω a ha)
      (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha) E).hom (b g) = c g := hb g
  refine ⟨E, b, hbc, ?_, hb'⟩
  intro g h
  apply arithmeticClassesModOutsideColimitOf_injective K Ω a ha E
  rw [map_add, Rep.hom_comm_apply]
  rw [hb', hb', hb']
  exact hcc g h

end
end Dubon2026

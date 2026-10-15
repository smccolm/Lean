import Dubon2026.CompactCoefficientColimitLift
import Dubon2026.ArithmeticClassQuotientTransitionInjectivity

/-! # Original open-subgroup class two-cocycles lift to an actual coefficient stage

Compact cochain lifting and faithful original stage maps retain the
literal two-cocycle identity. This is needed to construct the H2 invariant
maps in DUB-17's arithmetic P-class formation; no invariant map is assumed.
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

/-- The original finite class coefficient has its discrete topology. -/
local instance openClassTwoLiftStageTopology
    (F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a)) :
    TopologicalSpace (arithmeticGlobalClassesModOutsideStageRep K Ω a ha F) := ⊥
/-- The original finite class coefficient topology is discrete. -/
local instance openClassTwoLiftStageDiscrete
    (F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a)) :
    DiscreteTopology (arithmeticGlobalClassesModOutsideStageRep K Ω a ha F) := ⟨rfl⟩

/-- Every actual continuous class two-cocycle on an original open subgroup lifts with unchanged values and identity to an original finite coefficient stage. -/
theorem arithmeticOpenSubgroupClassTwoCocycle_exists_coefficient_lift
    (H : OpenSubgroup Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K))
    (c : H × H → arithmeticClassesModOutsideColimitRep K Ω a ha) (hc : Continuous c)
    (hcc : ∀ g h k, c (g * h, k) + c (g, h) =
      (arithmeticClassesModOutsideColimitRep K Ω a ha).ρ g.val (c (h, k)) + c (g, h * k)) :
    ∃ E : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a),
      ∃ b : H × H → arithmeticGlobalClassesModOutsideStageRep K Ω a ha E,
        Continuous b ∧
        (∀ g h k, b (g * h, k) + b (g, h) =
          (arithmeticGlobalClassesModOutsideStageRep K Ω a ha E).ρ g.val (b (h, k)) + b (g, h * k)) ∧
        ∀ z : H × H, (coefficientRepresentationColimitOf
          (arithmeticGlobalClassesModOutsideStageRep K Ω a ha)
          (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha) E).hom (b z) = c z := by
  letI : IsGalois K (originalUnramifiedGaloisUnion (Ω := Ω) a) := originalUnramifiedGaloisUnion_isGalois a
  letI : IsTopologicalGroup H := inferInstanceAs (IsTopologicalGroup H.toSubgroup)
  letI : CompactSpace H := isCompact_iff_compactSpace.mp H.isClosed.isCompact
  have hLift := @compactCoefficientColimit_exists_lift ℤ
    (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    _ _ _ _ _ (fun F => arithmeticGlobalClassesModOutsideStageRep K Ω a ha F)
    (fun F => (arithmeticGlobalClassesModOutsideStageRep K Ω a ha F).hV1)
    (fun F => (arithmeticGlobalClassesModOutsideStageRep K Ω a ha F).hV2)
    (fun E F h => (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha E F h).hom.toLinearMap)
    (inferInstance : TopologicalSpace (arithmeticClassesModOutsideColimitRep K Ω a ha))
    (inferInstance : DiscreteTopology (arithmeticClassesModOutsideColimitRep K Ω a ha))
    (fun F => (inferInstance : TopologicalSpace (arithmeticGlobalClassesModOutsideStageRep K Ω a ha F)))
    (fun F => (inferInstance : DiscreteTopology (arithmeticGlobalClassesModOutsideStageRep K Ω a ha F)))
    (H × H) inferInstance inferInstance c hc
  obtain ⟨E, b, hbc, hb⟩ := hLift
  have hb' (z : H × H) : (coefficientRepresentationColimitOf
      (arithmeticGlobalClassesModOutsideStageRep K Ω a ha)
      (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha) E).hom (b z) = c z := hb z
  refine ⟨E, b, hbc, ?_, hb'⟩
  intro g h k
  apply arithmeticClassesModOutsideColimitOf_injective K Ω a ha E
  rw [map_add, map_add, Rep.hom_comm_apply, hb', hb', hb', hb']
  exact hcc g h k

end
end Dubon2026

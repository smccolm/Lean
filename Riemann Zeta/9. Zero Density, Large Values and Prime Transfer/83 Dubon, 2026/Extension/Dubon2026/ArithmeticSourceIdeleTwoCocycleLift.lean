import Dubon2026.CompactCoefficientColimitLift
import Dubon2026.ArithmeticSourceIdeleStageInjectivity

/-! # Actual source-idele two-cocycle coefficient lift

Reuse the existing compact lifting and finite-period arguments with the
actual S-place source coefficients. Faithful stage maps preserve every
cocycle value and identity. This supplies a finite idele representative
for the source-induced class cup in DUB-17's normalized local pairing
comparison; no surjectivity on arbitrary full-class H2 is asserted.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  (a : 𝓞 K) (ha : a ≠ 0)
  [DecidableEq (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  [TopologicalSpace (arithmeticSPlaceColimitRep K Ω a ha)]
  [DiscreteTopology (arithmeticSPlaceColimitRep K Ω a ha)]

/-- The original finite source-idele coefficient has its discrete topology. -/
local instance sourceIdeleTwoLiftStageTopology
    (F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a)) :
    TopologicalSpace (arithmeticGlobalSPlaceStageRep K Ω a ha F) := ⊥
/-- The original finite source-idele coefficient topology is discrete. -/
local instance sourceIdeleTwoLiftStageDiscrete
    (F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a)) :
    DiscreteTopology (arithmeticGlobalSPlaceStageRep K Ω a ha F) := ⟨rfl⟩

/-- Every actual continuous source-idele two-cocycle on an original open subgroup lifts with unchanged values and identity to an original finite coefficient stage. -/
theorem arithmeticSourceIdeleTwoCocycle_exists_coefficient_lift
    (H : OpenSubgroup Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K))
    (c : H × H → arithmeticSPlaceColimitRep K Ω a ha) (hc : Continuous c)
    (hcc : ∀ g h k, c (g * h, k) + c (g, h) =
      (arithmeticSPlaceColimitRep K Ω a ha).ρ g.val (c (h, k)) + c (g, h * k)) :
    ∃ E : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a),
      ∃ b : H × H → arithmeticGlobalSPlaceStageRep K Ω a ha E,
        Continuous b ∧
        (∀ g h k, b (g * h, k) + b (g, h) =
          (arithmeticGlobalSPlaceStageRep K Ω a ha E).ρ g.val (b (h, k)) + b (g, h * k)) ∧
        ∀ z : H × H, (coefficientRepresentationColimitOf
          (arithmeticGlobalSPlaceStageRep K Ω a ha)
          (arithmeticGlobalSPlaceStageTransition K Ω a ha) E).hom (b z) = c z := by
  letI : IsGalois K (originalUnramifiedGaloisUnion (Ω := Ω) a) := originalUnramifiedGaloisUnion_isGalois a
  letI : IsTopologicalGroup H := inferInstanceAs (IsTopologicalGroup H.toSubgroup)
  letI : CompactSpace H := isCompact_iff_compactSpace.mp H.isClosed.isCompact
  have hLift := @compactCoefficientColimit_exists_lift ℤ
    (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    _ _ _ _ _ (fun F => arithmeticGlobalSPlaceStageRep K Ω a ha F)
    (fun F => (arithmeticGlobalSPlaceStageRep K Ω a ha F).hV1)
    (fun F => (arithmeticGlobalSPlaceStageRep K Ω a ha F).hV2)
    (fun E F h => (arithmeticGlobalSPlaceStageTransition K Ω a ha E F h).hom.toLinearMap)
    (inferInstance : TopologicalSpace (arithmeticSPlaceColimitRep K Ω a ha))
    (inferInstance : DiscreteTopology (arithmeticSPlaceColimitRep K Ω a ha))
    (fun F => (inferInstance : TopologicalSpace (arithmeticGlobalSPlaceStageRep K Ω a ha F)))
    (fun F => (inferInstance : DiscreteTopology (arithmeticGlobalSPlaceStageRep K Ω a ha F)))
    (H × H) inferInstance inferInstance c hc
  obtain ⟨E, b, hbc, hb⟩ := hLift
  have hb' (z : H × H) : (coefficientRepresentationColimitOf
      (arithmeticGlobalSPlaceStageRep K Ω a ha)
      (arithmeticGlobalSPlaceStageTransition K Ω a ha) E).hom (b z) = c z := hb z
  refine ⟨E, b, hbc, ?_, hb'⟩
  intro g h k
  apply arithmeticSPlaceColimitOf_injective K Ω a ha E
  rw [map_add, map_add, Rep.hom_comm_apply, hb', hb', hb', hb']
  exact hcc g h k

end
end Dubon2026

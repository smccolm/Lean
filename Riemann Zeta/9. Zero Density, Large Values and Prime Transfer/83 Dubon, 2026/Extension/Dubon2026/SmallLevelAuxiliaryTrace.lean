import Dubon2026.SmallLevelAuxiliaryFreeness
import Dubon2026.AuxiliaryCoordinateCoinvariants
import Dubon2026.AuxiliaryCoinvariantsCongr

/-! # CHT's trace identifies auxiliary coinvariants with base-level forms

This assembles the actual weighted function space, the level-quotient action
and the unnormalized trace. Arithmetic double-coset finiteness and the source
unitary/Hecke realization are not inferred from this algebraic comparison.
-/

namespace Dubon2026

noncomputable section

variable {R G W : Type*} [CommRing R] [Group G] [AddCommGroup W] [Module R W]
variable (Γ U V : Subgroup G) (hVU : V ≤ U) (ρ : Representation R U W)
variable (hsmall : ∀ (s : G) (u : U), s * u * s⁻¹ ∈ Γ → u = 1)
variable [(V.subgroupOf U).Normal] [Fintype (U ⧸ V.subgroupOf U)]

open scoped BigOperators

/-- The actual auxiliary coinvariant quotient is isomorphic to the base-level forms. -/
def smallLevelAuxiliaryCoinvariantEquiv :
    (auxiliaryAutomorphicAction Γ U V hVU ρ hsmall).Coinvariants ≃ₗ[R]
      algebraicAutomorphicForms Γ U ρ :=
  (auxiliaryCoinvariantsCongr (R := R) (D := U ⧸ V.subgroupOf U)
    (X := algebraicAutomorphicForms Γ V (ρ.comp (V.inclusion hVU)))
    (Y := DoubleCoset.Quotient (G := G) Γ U → U ⧸ V.subgroupOf U → W)
    (auxiliaryAutomorphicAction Γ U V hVU ρ hsmall)
    (quotientRightTranslation (R := R) (D := U ⧸ V.subgroupOf U)
      (J := DoubleCoset.Quotient (G := G) Γ U) (W := W))
    (smallLevelAuxiliaryEvaluation Γ U V hVU ρ hsmall)
    (auxiliaryAutomorphicAction_evaluation Γ U V hVU ρ hsmall)).trans
    ((auxiliaryCoordinateCoinvariantEquiv (R := R) (D := U ⧸ V.subgroupOf U)
      (J := DoubleCoset.Quotient (G := G) Γ U) (W := W)).trans
      (smallLevelAutomorphicEvaluation Γ U ρ hsmall).symm)

/-- The isomorphism is the sum of actual quotient translates at every point. -/
theorem smallLevelAuxiliaryCoinvariantEquiv_trace
    (f : algebraicAutomorphicForms Γ V (ρ.comp (V.inclusion hVU))) (g : G) :
    (smallLevelAuxiliaryCoinvariantEquiv Γ U V hVU ρ hsmall
      (Representation.Coinvariants.mk (auxiliaryAutomorphicAction Γ U V hVU ρ hsmall) f)).val g =
      ∑ d : U ⧸ V.subgroupOf U, (auxiliaryAutomorphicAction Γ U V hVU ρ hsmall d f).val g := by
  let t := smallLevelRightFactor Γ U g
  let q := DoubleCoset.mk Γ U g
  let F := smallLevelAuxiliaryEvaluation Γ U V hVU ρ hsmall f
  change ρ t⁻¹ (∑ d : U ⧸ V.subgroupOf U, F q d) =
    ∑ d : U ⧸ V.subgroupOf U, ρ t⁻¹ (F q (QuotientGroup.mk t * d))
  rw [map_sum]
  exact (Equiv.sum_comp (Equiv.mulLeft (QuotientGroup.mk t)) (fun d => ρ t⁻¹ (F q d))).symm

/-- The trace uses the original weight action and right translation, with no division. -/
theorem smallLevelAuxiliaryCoinvariantEquiv_weighted_trace
    (f : algebraicAutomorphicForms Γ V (ρ.comp (V.inclusion hVU))) (g : G) :
    (smallLevelAuxiliaryCoinvariantEquiv Γ U V hVU ρ hsmall
      (Representation.Coinvariants.mk (auxiliaryAutomorphicAction Γ U V hVU ρ hsmall) f)).val g =
      ∑ d : U ⧸ V.subgroupOf U, ρ d.out (f.val (g * (d.out : G))) := by
  rw [smallLevelAuxiliaryCoinvariantEquiv_trace]
  apply Finset.sum_congr rfl
  intro d _
  have he := auxiliaryAutomorphicAction_mk_apply Γ U V hVU ρ hsmall d.out f g
  simpa only [QuotientGroup.mk, Quotient.out_eq'] using he

end
end Dubon2026

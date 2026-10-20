import Dubon2026.SmallLevelAuxiliaryCoordinates

/-! # The actual level-quotient action in auxiliary coordinates

The transported action is identified pointwise with the original weighted
right translation from CHT Section 3.3. This identity is required before the
regular coordinates can supply the group-algebra freeness used by DUB-17.
-/

namespace Dubon2026

noncomputable section

variable {R D J W : Type*} [CommRing R] [Group D] [AddCommGroup W] [Module R W]

/-- Right translations on the actual quotient coordinates. -/
def quotientRightTranslation : Representation R D (J → D → W) where
  toFun d :=
    { toFun := fun f j x => f j (x * d)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by ext f j x; simp
  map_mul' a b := by ext f j x; simp [mul_assoc]

variable {G : Type*} [Group G]
variable (Γ U V : Subgroup G) (hVU : V ≤ U) (ρ : Representation R U W)
variable (hsmall : ∀ (s : G) (u : U), s * u * s⁻¹ ∈ Γ → u = 1)
variable [(V.subgroupOf U).Normal]

/-- The level quotient acts through the proved weighted coordinate isomorphism. -/
def auxiliaryAutomorphicAction : Representation R (U ⧸ V.subgroupOf U)
    (algebraicAutomorphicForms Γ V (ρ.comp (V.inclusion hVU))) :=
  (smallLevelAuxiliaryEvaluation Γ U V hVU ρ hsmall).symm.conjRingEquiv.toMonoidHom.comp
    quotientRightTranslation

/-- The action is the original weighted right translation, not an abstract proxy. -/
theorem auxiliaryAutomorphicAction_mk_apply (u : U)
    (f : algebraicAutomorphicForms Γ V (ρ.comp (V.inclusion hVU))) (g : G) :
    (auxiliaryAutomorphicAction Γ U V hVU ρ hsmall (QuotientGroup.mk u) f).val g =
      ρ u (f.val (g * u)) := by
  change ρ (smallLevelRightFactor Γ U g)⁻¹
    (auxiliaryWeightedValue Γ U V hVU ρ f (DoubleCoset.mk Γ U g).out
      (QuotientGroup.mk (smallLevelRightFactor Γ U g) * QuotientGroup.mk u)) = _
  rw [← QuotientGroup.mk_mul, auxiliaryWeightedValue_mk]
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_left]
  congr 1
  obtain ⟨γ, he⟩ := smallLevelRightFactor_spec Γ U g
  apply Eq.symm
  refine (congrArg (fun x : G => f.val (x * (u : G))) he).trans ?_
  simp only [mul_assoc, Subgroup.coe_mul, f.property.1]

/-- Evaluation intertwines the actual action with right translation. -/
theorem auxiliaryAutomorphicAction_evaluation (d : U ⧸ V.subgroupOf U)
    (f : algebraicAutomorphicForms Γ V (ρ.comp (V.inclusion hVU))) :
    smallLevelAuxiliaryEvaluation Γ U V hVU ρ hsmall
      (auxiliaryAutomorphicAction Γ U V hVU ρ hsmall d f) =
      quotientRightTranslation (R := R) d
        (smallLevelAuxiliaryEvaluation Γ U V hVU ρ hsmall f) := by
  exact (smallLevelAuxiliaryEvaluation Γ U V hVU ρ hsmall).apply_symm_apply _

end
end Dubon2026

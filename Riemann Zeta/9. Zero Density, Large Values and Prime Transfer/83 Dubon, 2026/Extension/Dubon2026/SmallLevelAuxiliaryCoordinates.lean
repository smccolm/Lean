import Dubon2026.SmallLevelAlgebraicAutomorphicForms
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # Weighted coordinates at an auxiliary level

For CHT Lemma 3.3.1, evaluation at the base-level double cosets and at U/V
removes the coefficient twist. The subgroup and the weight representation are
the actual inputs; no coordinate isomorphism is assumed.
-/

namespace Dubon2026

noncomputable section

variable {R G W : Type*} [CommRing R] [Group G] [AddCommGroup W] [Module R W]
variable (Γ U V : Subgroup G) (hVU : V ≤ U) (ρ : Representation R U W)

/-- Twisted evaluation is unchanged by multiplying the right coordinate by V. -/
theorem auxiliary_weighted_value_right
    (f : algebraicAutomorphicForms Γ V (ρ.comp (V.inclusion hVU)))
    (g : G) (u : U) (v : V) :
    ρ (u * V.inclusion hVU v) (f.val (g * (u * V.inclusion hVU v : U))) =
      ρ u (f.val (g * u)) := by
  change ρ (u * V.inclusion hVU v) (f.val (g * ((u : G) * (v : G)))) = _
  rw [← mul_assoc, f.property.2]
  change ρ (u * V.inclusion hVU v) (ρ (V.inclusion hVU v)⁻¹ (f.val (g * u))) = _
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_right]

/-- Twisted values descend to the original level quotient. -/
def auxiliaryWeightedValue
    (f : algebraicAutomorphicForms Γ V (ρ.comp (V.inclusion hVU)))
    (g : G) : U ⧸ V.subgroupOf U → W :=
  Quotient.lift (fun u : U => ρ u (f.val (g * u))) (by
    intro a b hab
    have hv' : a⁻¹ * b ∈ V.subgroupOf U := QuotientGroup.leftRel_apply.mp hab
    have hv : ((a⁻¹ * b : U) : G) ∈ V := hv'
    let v : V := ⟨(a⁻¹ * b : U), hv⟩
    have he : a * V.inclusion hVU v = b := by
      apply Subtype.ext
      change (a : G) * ((a : G)⁻¹ * (b : G)) = (b : G)
      simp
    simpa only [he] using (auxiliary_weighted_value_right Γ U V hVU ρ f g a v).symm)

/-- The quotient coordinate evaluates to the original twisted function value. -/
theorem auxiliaryWeightedValue_mk
    (f : algebraicAutomorphicForms Γ V (ρ.comp (V.inclusion hVU)))
    (g : G) (u : U) :
    auxiliaryWeightedValue Γ U V hVU ρ f g (QuotientGroup.mk u) =
      ρ u (f.val (g * u)) := rfl

/-- Smallness constructs all auxiliary forms from their actual quotient coordinates. -/
def smallLevelAuxiliaryEvaluation
    (hsmall : ∀ (s : G) (u : U), s * u * s⁻¹ ∈ Γ → u = 1) :
    algebraicAutomorphicForms Γ V (ρ.comp (V.inclusion hVU)) ≃ₗ[R]
      (DoubleCoset.Quotient (G := G) Γ U → U ⧸ V.subgroupOf U → W) where
  toFun f q := auxiliaryWeightedValue Γ U V hVU ρ f q.out
  map_add' f g := by
    funext q x
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
    exact map_add (ρ u) _ _
  map_smul' a f := by
    funext q x
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
    exact map_smul (ρ u) a _
  invFun w := ⟨fun g => ρ (smallLevelRightFactor Γ U g)⁻¹
      (w (DoubleCoset.mk Γ U g) (QuotientGroup.mk (smallLevelRightFactor Γ U g))), by
    constructor
    · intro γ g
      simp only [smallLevelRightFactor_left Γ U hsmall, smallLevel_doubleCoset_left]
    · intro g v
      change ρ (smallLevelRightFactor Γ U (g * (V.inclusion hVU v : U)))⁻¹
        (w (DoubleCoset.mk Γ U (g * (V.inclusion hVU v : U)))
          (QuotientGroup.mk (smallLevelRightFactor Γ U (g * (V.inclusion hVU v : U))))) = _
      rw [smallLevelRightFactor_right Γ U hsmall, smallLevel_doubleCoset_right]
      have hq : (QuotientGroup.mk (smallLevelRightFactor Γ U g * V.inclusion hVU v) :
          U ⧸ V.subgroupOf U) = QuotientGroup.mk (smallLevelRightFactor Γ U g) := by
        apply Eq.symm
        apply Quotient.sound
        apply QuotientGroup.leftRel_apply.mpr
        simpa only [inv_mul_cancel_left] using v.property
      rw [hq]
      simp only [mul_inv_rev, map_mul, Module.End.mul_apply, MonoidHom.comp_apply, map_inv]⟩
  left_inv f := by
    apply Subtype.ext
    funext g
    change ρ (smallLevelRightFactor Γ U g)⁻¹
      (ρ (smallLevelRightFactor Γ U g)
        (f.val ((DoubleCoset.mk Γ U g).out * smallLevelRightFactor Γ U g))) = f.val g
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    obtain ⟨γ, he⟩ := smallLevelRightFactor_spec Γ U g
    apply Eq.symm
    refine (congrArg f.val he).trans ?_
    rw [mul_assoc, f.property.1]
  right_inv w := by
    funext q x
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
    change ρ u (ρ (smallLevelRightFactor Γ U (q.out * u))⁻¹
      (w (DoubleCoset.mk Γ U (q.out * u))
        (QuotientGroup.mk (smallLevelRightFactor Γ U (q.out * u))))) = w q (QuotientGroup.mk u)
    rw [smallLevelRightFactor_right Γ U hsmall, smallLevelRightFactor_out Γ U hsmall,
      one_mul, smallLevel_doubleCoset_right, DoubleCoset.out_eq']
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

end
end Dubon2026

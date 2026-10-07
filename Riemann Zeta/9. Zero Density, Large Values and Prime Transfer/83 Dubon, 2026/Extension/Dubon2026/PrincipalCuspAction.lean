import Dubon2026.ModularDegeneracy
import Mathlib.RepresentationTheory.Basic

/-! # The actual finite congruence action on principal-level cusp forms -/

namespace Dubon2026

open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups Pointwise ModularForm

noncomputable section

/-- Integral conjugation preserves the real image of a normal modular subgroup. -/
theorem normalModularSubgroup_le_conj (H : Subgroup SL(2, ℤ)) [H.Normal]
    (γ : SL(2, ℤ)) :
    H.map (mapGL ℝ) ≤ ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • H.map (mapGL ℝ) := by
  rintro g ⟨δ, hδ, rfl⟩
  rw [Subgroup.mem_smul_pointwise_iff_exists]
  refine ⟨mapGL ℝ (γ * δ * γ⁻¹), ⟨_, Subgroup.Normal.conj_mem inferInstance δ hδ γ, rfl⟩, ?_⟩
  change (mapGL ℝ γ)⁻¹ * mapGL ℝ (γ * δ * γ⁻¹) * mapGL ℝ γ = mapGL ℝ δ
  simp [map_mul, mul_assoc]

/-- Left action on genuine cusp forms, using the inverse in the right slash action. -/
def normalCuspAction (H : Subgroup SL(2, ℤ)) [H.Normal] (k : ℤ) :
    Representation ℂ SL(2, ℤ) (CuspForm (H.map (mapGL ℝ)) k) where
  toFun γ := {
    toFun f := cuspRestrictSubgroup (normalModularSubgroup_le_conj H γ⁻¹)
      (CuspForm.translate f (mapGL ℝ γ⁻¹))
    map_add' f g := by
      ext τ
      change ((⇑(f + g) ∣[k] mapGL ℝ γ⁻¹) τ) = _
      simp only [CuspForm.coe_add, SlashAction.add_slash, Pi.add_apply]
      rfl
    map_smul' c f := by
      ext τ
      change (((c • ⇑f) ∣[k] γ⁻¹) τ) = c • ((⇑f ∣[k] γ⁻¹) τ)
      rw [ModularForm.SL_smul_slash]
      rfl
  }
  map_one' := by
    ext f τ
    change ((⇑f ∣[k] mapGL ℝ (1 : SL(2, ℤ))⁻¹) τ) = f τ
    simp
  map_mul' γ δ := by
    ext f τ
    change ((⇑f ∣[k] mapGL ℝ (γ * δ)⁻¹) τ) =
      (((⇑f ∣[k] mapGL ℝ δ⁻¹) ∣[k] mapGL ℝ γ⁻¹) τ)
    rw [mul_inv_rev, map_mul, SlashAction.slash_mul]

/-- The representation is literally slash by the inverse integral matrix. -/
theorem normalCuspAction_apply (H : Subgroup SL(2, ℤ)) [H.Normal] (k : ℤ)
    (γ : SL(2, ℤ)) (f : CuspForm (H.map (mapGL ℝ)) k) :
    ⇑(normalCuspAction H k γ f) = ⇑f ∣[k] mapGL ℝ γ⁻¹ := rfl

/-- The principal invariance subgroup acts trivially, so the action descends to its quotient. -/
theorem normalCuspAction_ker (H : Subgroup SL(2, ℤ)) [H.Normal] (k : ℤ) :
    H ≤ (normalCuspAction H k).ker := by
  intro γ hγ
  apply LinearMap.ext
  intro f
  apply DFunLike.coe_injective
  exact f.slash_action_eq' _ ⟨γ⁻¹, H.inv_mem hγ, rfl⟩

local instance principalNormal (N : ℕ) : (Gamma N).Normal := Gamma_normal N

/-- The actual principal-level action factors through the finite congruence quotient. -/
def principalCuspRepresentation (N : ℕ) (k : ℤ) :
    Representation ℂ (SL(2, ℤ) ⧸ Gamma N) (CuspForm ((Gamma N).map (mapGL ℝ)) k) :=
  QuotientGroup.lift (Gamma N) (normalCuspAction (Gamma N) k)
    (normalCuspAction_ker (Gamma N) k)

/-- Evaluation on an integral representative is the actual slash action. -/
theorem principalCuspRepresentation_mk (N : ℕ) (k : ℤ) (γ : SL(2, ℤ))
    (f : CuspForm ((Gamma N).map (mapGL ℝ)) k) :
    ⇑(principalCuspRepresentation N k (QuotientGroup.mk γ) f) =
      ⇑f ∣[k] mapGL ℝ γ⁻¹ := rfl

end
end Dubon2026

import Mathlib.FieldTheory.Normal.Basic
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # The actual original Galois action on a stable subgroup and its quotient -/

namespace Dubon2026
noncomputable section

variable {F K V : Type*} [Field F] [Field K] [Algebra F K] [CommGroup V]

/-- Original stability in both directions follows from the given action and the inverse Galois element. -/
private theorem galoisStableSubgroup_map
    (ρ : (K ≃ₐ[F] K) →* MulAut V) (H : Subgroup V)
    (hH : ∀ (g : K ≃ₐ[F] K) (v : V), v ∈ H → ρ g v ∈ H) (g : K ≃ₐ[F] K) :
    H.map (ρ g).toMonoidHom = H := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact hH g w hw
  · intro hv
    refine ⟨ρ g⁻¹ v, hH g⁻¹ v hv, ?_⟩
    rw [map_inv]
    exact (ρ g).apply_symm_apply v

/-- Restrict the specified original Galois action to the same stable original subgroup. -/
def galoisModuleSubgroupAction
    (ρ : (K ≃ₐ[F] K) →* MulAut V) (H : Subgroup V)
    (hH : ∀ (g : K ≃ₐ[F] K) (v : V), v ∈ H → ρ g v ∈ H) :
    (K ≃ₐ[F] K) →* MulAut H where
  toFun g := ((ρ g).subgroupMap H).trans (MulEquiv.subgroupCongr (galoisStableSubgroup_map ρ H hH g))
  map_one' := by
    apply MulEquiv.ext
    intro v
    apply Subtype.ext
    change ρ 1 v.val = v.val
    rw [map_one]
    rfl
  map_mul' g h := by
    apply MulEquiv.ext
    intro v
    apply Subtype.ext
    change ρ (g * h) v.val = ρ g (ρ h v.val)
    rw [map_mul]
    rfl

/-- The restricted action retains the original element and its original action value. -/
theorem galoisModuleSubgroupAction_apply
    (ρ : (K ≃ₐ[F] K) →* MulAut V) (H : Subgroup V)
    (hH : ∀ (g : K ≃ₐ[F] K) (v : V), v ∈ H → ρ g v ∈ H)
    (g : K ≃ₐ[F] K) (v : H) :
    (galoisModuleSubgroupAction ρ H hH g v).val = ρ g v.val := by
  rfl

/-- Descend the specified original Galois action to the genuine group quotient by the same stable subgroup. -/
def galoisModuleQuotientAction
    (ρ : (K ≃ₐ[F] K) →* MulAut V) (H : Subgroup V)
    (hH : ∀ (g : K ≃ₐ[F] K) (v : V), v ∈ H → ρ g v ∈ H) :
    (K ≃ₐ[F] K) →* MulAut (V ⧸ H) where
  toFun g := QuotientGroup.congr H H (ρ g) (galoisStableSubgroup_map ρ H hH g)
  map_one' := by
    apply MulEquiv.ext
    intro z
    induction z using Quotient.inductionOn with
    | h v =>
      change QuotientGroup.mk (ρ 1 v) = QuotientGroup.mk v
      rw [map_one]
      rfl
  map_mul' g h := by
    apply MulEquiv.ext
    intro z
    induction z using Quotient.inductionOn with
    | h v =>
      change QuotientGroup.mk (ρ (g * h) v) = QuotientGroup.mk (ρ g (ρ h v))
      rw [map_mul]
      rfl

/-- The genuine quotient Galois action evaluates on the same original representative. -/
theorem galoisModuleQuotientAction_mk
    (ρ : (K ≃ₐ[F] K) →* MulAut V) (H : Subgroup V)
    (hH : ∀ (g : K ≃ₐ[F] K) (v : V), v ∈ H → ρ g v ∈ H)
    (g : K ≃ₐ[F] K) (v : V) :
    galoisModuleQuotientAction ρ H hH g (QuotientGroup.mk v) =
      QuotientGroup.mk (ρ g v) := by
  rfl

end
end Dubon2026

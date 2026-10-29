import Dubon2026.SourceCoefficientDualAction

/-! DUB-17/18 -> original all-weight arithmetic association -> the
genuine coefficient-valued Tate Galois action. Combine a proved action on
the original coefficient module with the existing contragredient action
on Tate sequences. This is the action needed by the derived Frobenius
normalization; Hecke stability follows from the two actual commutations. -/
namespace Dubon2026
noncomputable section
variable {R S T V G : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup T] [Module R T] [AddCommGroup V]
  [Module R V] [Module S V] [IsScalarTower R S V] [Group G]

/-- The genuine coefficient action paired with the inverse Tate action. -/
def sourceTwistedCoefficientDualAction (τ : G →* Module.End S V) (ρ : G →* Module.End R T) :
    G →* Module.End S (T →ₗ[R] V) where
  toFun σ :=
    { toFun := fun φ => ((τ σ).restrictScalars R).comp (φ.comp (ρ σ⁻¹))
      map_add' := fun φ ψ => by
        apply LinearMap.ext
        intro x
        exact (τ σ).map_add _ _
      map_smul' := fun c φ => by
        apply LinearMap.ext
        intro x
        exact (τ σ).map_smul c _ }
  map_one' := by
    apply LinearMap.ext
    intro φ
    apply LinearMap.ext
    intro x
    change τ 1 (φ (ρ 1⁻¹ x)) = φ x
    rw [inv_one, map_one, map_one]
    rfl
  map_mul' σ δ := by
    apply LinearMap.ext
    intro φ
    apply LinearMap.ext
    intro x
    change τ (σ * δ) (φ (ρ ((σ * δ)⁻¹) x)) = τ σ (τ δ (φ (ρ δ⁻¹ (ρ σ⁻¹ x))))
    rw [map_mul, mul_inv_rev, map_mul]
    rfl

theorem sourceTwistedCoefficientDualAction_operator
    (τ : G →* Module.End S V) (ρ : G →* Module.End R T)
    (σ : G) (b : Module.End S V) (H : Module.End R T)
    (hT : Commute (ρ σ⁻¹) H) (hV : Commute (τ σ) b) (φ : T →ₗ[R] V) :
    sourceTwistedCoefficientDualAction τ ρ σ ((b.restrictScalars R).comp (φ.comp H)) =
      (b.restrictScalars R).comp ((sourceTwistedCoefficientDualAction τ ρ σ φ).comp H) := by
  apply LinearMap.ext
  intro x
  change τ σ (b (φ (H (ρ σ⁻¹ x)))) = b (τ σ (φ (ρ σ⁻¹ (H x))))
  have ht : ρ σ⁻¹ (H x) = H (ρ σ⁻¹ x) := LinearMap.congr_fun hT.eq x
  rw [ht]
  exact LinearMap.congr_fun hV.eq _

end
end Dubon2026

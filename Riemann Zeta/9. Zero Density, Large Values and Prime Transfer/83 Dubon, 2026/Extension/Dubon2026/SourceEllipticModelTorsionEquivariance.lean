import Dubon2026.SourceEllipticModelTorsionReduction
import Dubon2026.SourceEllipticGaloisTorsionMap
import Dubon2026.SourceEllipticInertiaPointReduction

/-! Equivariance of the original curve's actual torsion reduction through
the good model. The cocycle identity derives the coordinate relationships;
the existing torsion-integrality theorem supplies the integral-point input.
This is the actual action/reduction bridge for the DUB-17/18 fiber census. -/
namespace Dubon2026.SourceEllipticReduction
open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing
open SourceEllipticVariableChange SourceEllipticFunctionField SourceEllipticVelu
noncomputable section
variable {F M : Type*} [Field F] [Field M] [Algebra F M] [DecidableEq M]
variable {A : ValuationSubring M} [DecidableEq (ResidueField A)]

private theorem point_zero_heq {R : Type*} [Field R] [DecidableEq R]
    {V V' : WeierstrassCurve R} (h : V = V') :
    HEq (0 : V.toAffine.Point) (0 : V'.toAffine.Point) := by
  subst V'
  rfl

theorem modelReduction_inertia_of_torsion
    (E : WeierstrassCurve F) (W : WeierstrassCurve A) (κ : VariableChange M)
    (hκ : κ • E.baseChange M = W.map A.subtype)
    (hΔ : (W.map (residue A)).Δ ≠ 0) {N : ℕ} (hN : IsUnit (N : A))
    (g : VariableChange A) (σ : M ≃ₐ[F] M) (hσ : σ ∈ A.decompositionSubgroup F)
    (hσI : (⟨σ, hσ⟩ : A.decompositionSubgroup F) ∈ A.inertiaSubgroup F)
    (hg : g.map A.subtype = κ * (κ.map (σ : M →+* M))⁻¹)
    (hfix : g.map (residue A) • W.map (residue A) = W.map (residue A))
    (P : (E.baseChange M).toAffine.Point) (hP : N • P = 0) :
    HEq (vcInvFun (g.map (residue A)) (W.map (residue A)).toAffine
      (reducePoint hΔ (modelPointEquiv E W κ hκ P)))
      (reducePoint hΔ (modelPointEquiv E W κ hκ (Point.map (σ : M →ₐ[F] M) P))) := by
  let e := modelPointEquiv E W κ hκ
  change HEq (vcInvFun _ _ (reducePoint hΔ (e P)))
    (reducePoint hΔ (e (Point.map (σ : M →ₐ[F] M) P)))
  rcases P with _ | ⟨x, y, h⟩
  · change HEq (vcInvFun _ _ (reducePoint hΔ (e 0)))
      (reducePoint hΔ (e (Point.map (σ : M →ₐ[F] M) 0)))
    simp only [map_zero, reducePoint_zero, vcInvFun_zero]
    exact point_zero_heq hfix
  have hP0 := Point.some_ne_zero h
  have hNP : N • e (Point.some x y h) = 0 := by rw [← map_nsmul, hP, map_zero]
  rcases hQ₁ : e (Point.some x y h) with _ | ⟨x₁, y₁, h₁⟩
  · exact (hP0 (e.injective (hQ₁.trans (map_zero e).symm))).elim
  rcases hQ₂ : e (Point.map (σ : M →ₐ[F] M) (Point.some x y h)) with _ | ⟨x₂, y₂, h₂⟩
  · have hz := e.injective (hQ₂.trans (map_zero e).symm)
    exact (hP0 (Point.map_injective (σ : M →ₐ[F] M)
      (hz.trans (map_zero (Point.map (σ : M →ₐ[F] M))).symm))).elim
  have hc₁ := modelPointEquiv_coords E W κ hκ (Point.some x y h)
  change coordsOrZero (e (Point.some x y h)) = _ at hc₁
  rw [hQ₁] at hc₁
  change (x₁, y₁) = (vcXInv κ x, vcYInv κ x y) at hc₁
  obtain ⟨hx₁, hy₁⟩ := Prod.mk.inj hc₁
  have hc₂ := modelPointEquiv_coords E W κ hκ
    (Point.map (σ : M →ₐ[F] M) (Point.some x y h))
  change coordsOrZero (e (Point.map (σ : M →ₐ[F] M) (Point.some x y h))) = _ at hc₂
  rw [hQ₂, Point.map_some] at hc₂
  change (x₂, y₂) = (vcXInv κ (σ x), vcYInv κ (σ x) (σ y)) at hc₂
  obtain ⟨hx₂, hy₂⟩ := Prod.mk.inj hc₂
  have hκfac : κ = g.map A.subtype * κ.map (σ : M →+* M) := by
    rw [hg, inv_mul_cancel_right]
  have hmx (z : M) : σ (vcXInv κ z) = vcXInv (κ.map (σ : M →+* M)) (σ z) :=
    map_vcXInv (σ : M →+* M) κ z
  have hmy (z w : M) : σ (vcYInv κ z w) =
      vcYInv (κ.map (σ : M →+* M)) (σ z) (σ w) :=
    map_vcYInv (σ : M →+* M) κ z w
  have hxrel : x₂ = vcXInv (g.map A.subtype) (σ x₁) := by
    rw [hx₂, hx₁, hmx]
    conv_lhs => rw [hκfac, vcXInv_mul]
  have hyrel : y₂ = vcYInv (g.map A.subtype) (σ x₁) (σ y₁) := by
    rw [hy₂, hx₁, hy₁, hmx, hmy]
    conv_lhs => rw [hκfac, vcYInv_mul]
  have hxmem : x₁ ∈ A := torsion_x_mem_valuationSubring A W h₁ N hN (hQ₁ ▸ hNP)
  exact reducePoint_inertia_coordinates hΔ g hfix σ hσ hσI h₁ h₂ hxmem hxrel hyrel

theorem modelTorsionReduction_inertia
    (E : WeierstrassCurve F) (W : WeierstrassCurve A) (κ : VariableChange M)
    (hκ : κ • E.baseChange M = W.map A.subtype)
    (hΔ : (W.map (residue A)).Δ ≠ 0) {N : ℕ} (hN : IsUnit (N : A))
    (g : VariableChange A) (σ : M ≃ₐ[F] M) (hσ : σ ∈ A.decompositionSubgroup F)
    (hσI : (⟨σ, hσ⟩ : A.decompositionSubgroup F) ∈ A.inertiaSubgroup F)
    (hg : g.map A.subtype = κ * (κ.map (σ : M →+* M))⁻¹)
    (hfix : g.map (residue A) • W.map (residue A) = W.map (residue A))
    (P : Submodule.torsionBy ℤ (E.baseChange M).toAffine.Point (N : ℤ)) :
    HEq (vcInvFun (g.map (residue A)) (W.map (residue A)).toAffine
      (modelTorsionReduction E W κ hκ hΔ hN P))
      (modelTorsionReduction E W κ hκ hΔ hN (galoisTorsionMap E N σ P)) := by
  simp only [modelTorsionReduction_apply, galoisTorsionMap_apply]
  apply modelReduction_inertia_of_torsion E W κ hκ hΔ hN g σ hσ hσI hg hfix P
  simpa only [Submodule.mem_torsionBy_iff, natCast_zsmul] using P.property

end
end Dubon2026.SourceEllipticReduction

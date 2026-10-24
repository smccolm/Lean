import Dubon2026.SourceEllipticInverseCoordinateResidue
import Dubon2026.SourceEllipticInertiaConjugate
import Dubon2026.SourceEllipticTorsionReductionHom

/-! Coordinate-level equivariance of actual point reduction under the
derived inertia change. The integrality premise is available for every
nonzero prime-to-residue torsion point from the existing division-polynomial
proof. This is the concrete point bridge for the DUB-17/18 inertia census. -/
namespace Dubon2026.SourceEllipticReduction
open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing
open SourceEllipticVariableChange SourceEllipticFunctionField
noncomputable section

private theorem point_some_heq {R : Type*} [Field R] {V V' : WeierstrassCurve R}
    (hV : V = V') {x y x' y' : R} (hx : x = x') (hy : y = y')
    {h : V.toAffine.Nonsingular x y} {h' : V'.toAffine.Nonsingular x' y'} :
    HEq (Point.some x y h) (Point.some x' y' h') := by
  subst V'
  subst x'
  subst y'
  rfl

theorem reducePoint_inertia_coordinates
    {F M : Type*} [Field F] [Field M] [Algebra F M] {A : ValuationSubring M}
    {W : WeierstrassCurve A} (hΔ : (W.map (residue A)).Δ ≠ 0)
    (g : VariableChange A)
    (hfix : g.map (residue A) • W.map (residue A) = W.map (residue A))
    (σ : M ≃ₐ[F] M) (hσ : σ ∈ A.decompositionSubgroup F)
    (hσI : (⟨σ, hσ⟩ : A.decompositionSubgroup F) ∈ A.inertiaSubgroup F)
    {x₁ y₁ x₂ y₂ : M} (h₁ : (W.map A.subtype).toAffine.Nonsingular x₁ y₁)
    (h₂ : (W.map A.subtype).toAffine.Nonsingular x₂ y₂) (hx₁ : x₁ ∈ A)
    (hx₂ : x₂ = vcXInv (g.map A.subtype) (σ x₁))
    (hy₂ : y₂ = vcYInv (g.map A.subtype) (σ x₁) (σ y₁)) :
    HEq (vcInvFun (g.map (residue A)) (W.map (residue A)).toAffine
      (reducePoint hΔ (Point.some x₁ y₁ h₁)))
      (reducePoint hΔ (Point.some x₂ y₂ h₂)) := by
  subst x₂
  subst y₂
  have hy₁ : y₁ ∈ A := equation_y_mem_valuationSubring A W h₁.1 hx₁
  have hσx : σ x₁ ∈ A := (decompRingHom σ hσ ⟨x₁, hx₁⟩).2
  have hσy : σ y₁ ∈ A := (decompRingHom σ hσ ⟨y₁, hy₁⟩).2
  have hx' := vcXInv_mem g hσx
  have hy' := vcYInv_mem g hσx hσy
  have hresx : residue A ⟨σ x₁, hσx⟩ = residue A ⟨x₁, hx₁⟩ :=
    RingHom.congr_fun (residue_comp_decompRingHom σ hσ hσI) ⟨x₁, hx₁⟩
  have hresy : residue A ⟨σ y₁, hσy⟩ = residue A ⟨y₁, hy₁⟩ :=
    RingHom.congr_fun (residue_comp_decompRingHom σ hσ hσI) ⟨y₁, hy₁⟩
  rw [reducePoint_some_of_mem hΔ h₁ hx₁, reducePoint_some_of_mem hΔ h₂ hx']
  change HEq (Point.some _ _ _) (Point.some _ _ _)
  apply point_some_heq hfix
  · rw [residue_vcXInv g hσx hx', hresx]
  · rw [residue_eq_of_coe_eq A _ (v := ⟨vcYInv (g.map A.subtype) (σ x₁) (σ y₁), hy'⟩) rfl,
      residue_vcYInv g hσx hσy hy', hresx, hresy]

end
end Dubon2026.SourceEllipticReduction

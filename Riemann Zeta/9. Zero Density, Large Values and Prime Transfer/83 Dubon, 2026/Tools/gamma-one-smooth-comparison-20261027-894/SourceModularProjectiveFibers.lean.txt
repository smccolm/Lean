import Dubon2026.CongruenceTraceDomain
import Dubon2026.SourceModularProjectiveKernel

/-! DUB-17/18 -> original all-weight arithmetic association -> Gamma1 Picard/H1
-> Abel-Jacobi converse -> analytic reciprocity -> invariant integral limit.
The existing generic projective subgroup domain is reused. This module proves
the exact two-element fibers of the actual integral-to-projective map, so
the central-sign factor in the source integral is derived, not assumed. -/
namespace Dubon2026.SourceSmoothedUnfolding
noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane MeasureTheory Set
open scoped MatrixGroups Pointwise ENNReal
variable (Γ : Subgroup SL(2, ℤ))

/-- The actual projection of the integral subgroup onto its projective image. -/
def projection : Γ →* projectiveIntegralSubgroup Γ :=
  (QuotientGroup.mk' (Subgroup.center SL(2, ℤ))).subgroupMap Γ

theorem projection_surjective : Function.Surjective (projection Γ) :=
  MonoidHom.subgroupMap_surjective _ Γ

theorem mem_projection_ker (a : Γ) :
    a ∈ (projection Γ).ker ↔ a.val = 1 ∨ a.val = -1 := by
  rw [MonoidHom.mem_ker, Subtype.ext_iff]
  change (QuotientGroup.mk a.val : PSL(2, ℤ)) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff, SourceModularFreeProduct.mem_center_iff_eq]

theorem projection_ker_card (hΓ : (-1 : SL(2, ℤ)) ∈ Γ) :
    Nat.card (projection Γ).ker = 2 := by
  let n : (projection Γ).ker :=
    ⟨⟨-1, hΓ⟩, (mem_projection_ker Γ _).mpr (Or.inr rfl)⟩
  apply Nat.card_eq_two_iff.mpr
  refine ⟨1, n, ?_, ?_⟩
  · intro h
    have he := congrArg (fun x : (projection Γ).ker => x.val.val 0 0) h
    norm_num [n] at he
  · ext a
    simp only [mem_insert_iff, mem_singleton_iff, mem_univ, iff_true]
    rcases (mem_projection_ker Γ a.val).mp a.property with h | h
    · left
      exact Subtype.ext (Subtype.ext h)
    · right
      exact Subtype.ext (Subtype.ext h)

theorem projection_fiber_card (hΓ : (-1 : SL(2, ℤ)) ∈ Γ)
    (g : projectiveIntegralSubgroup Γ) :
    Nat.card ((projection Γ) ⁻¹' {g}) = 2 :=
  (Nat.card_congr (MonoidHom.fiberEquivKerOfSurjective (projection_surjective Γ) g)).trans
    (projection_ker_card Γ hΓ)

theorem tsum_projection (hΓ : (-1 : SL(2, ℤ)) ∈ Γ)
    (f : projectiveIntegralSubgroup Γ → ℝ≥0∞) :
    ∑' a : Γ, f (projection Γ a) = 2 * ∑' g, f g := by
  rw [← ENNReal.tsum_fiberwise (fun a : Γ => f (projection Γ a)) (projection Γ)]
  calc
    ∑' g, ∑' a : (projection Γ) ⁻¹' {g}, f (projection Γ a) =
        ∑' g, (2 : ℝ≥0∞) * f g := by
      apply tsum_congr
      intro g
      have hc := projection_fiber_card Γ hΓ g
      haveI : Finite ((projection Γ) ⁻¹' {g}) := Nat.finite_of_card_ne_zero (by omega)
      letI : Fintype ((projection Γ) ⁻¹' {g}) := Fintype.ofFinite _
      simp only [show ∀ a : (projection Γ) ⁻¹' {g}, projection Γ a = g
        from fun a => a.property, tsum_fintype, Finset.sum_const, Finset.card_univ,
        ← Nat.card_eq_fintype_card, hc, nsmul_eq_mul, Nat.cast_ofNat]
    _ = 2 * ∑' g, f g := ENNReal.tsum_mul_left

end
end Dubon2026.SourceSmoothedUnfolding

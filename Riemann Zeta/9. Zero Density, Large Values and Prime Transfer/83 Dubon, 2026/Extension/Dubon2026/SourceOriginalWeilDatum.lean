import Dubon2026.SourceOriginalWeilEvaluationGalois

/-! DUB-17/18 -> original Frobenius determinant -> arithmetic pairing
on original Picard torsion. These are the literal disjoint divisor/function
representatives used by the divisorial Weil formula. Rationality of every
original place is already supplied by the proved residue identification.
The ratio is nonzero and transforms semilinearly under the actual original
arithmetic action. Independence of representatives and nondegeneracy are
not fields of this structure and remain proof obligations.
Adapted from Def_AlgebraicCurve_WeilDatum,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]
local notation "FF" => modularFunctionFieldOver N L

/-- Actual disjoint divisors with principal multiples, before Picard-quotient descent. -/
structure OriginalWeilDatum (n : ℕ) where
  /-- First integer divisor. -/
  D₁ : Divisor L FF
  /-- Second integer divisor. -/
  D₂ : Divisor L FF
  /-- Function whose divisor is the first multiple. -/
  f₁ : FF
  /-- Function whose divisor is the second multiple. -/
  f₂ : FF
  f₁_ne_zero : f₁ ≠ 0
  f₂_ne_zero : f₂ ≠ 0
  ord_f₁ : ∀ v : Place L FF, v.ord f₁ = n * D₁ v
  ord_f₂ : ∀ v : Place L FF, v.ord f₂ = n * D₂ v
  disjoint : ∀ v : Place L FF, D₁ v = 0 ∨ D₂ v = 0

namespace OriginalWeilDatum
variable {N L} {n : ℕ} (d : OriginalWeilDatum N L n)

/-- The literal divisorial Weil ratio on the original function field. -/
def pairing : L := originalDivisorEval N L d.f₁ d.D₂ / originalDivisorEval N L d.f₂ d.D₁

theorem pairing_ne_zero : d.pairing ≠ 0 := by
  apply div_ne_zero
  · apply originalDivisorEval_ne_zero N L d.f₁ d.f₁_ne_zero
    intro v hv
    rw [d.ord_f₁, (d.disjoint v).resolve_right (Finsupp.mem_support_iff.mp hv), mul_zero]
  · apply originalDivisorEval_ne_zero N L d.f₂ d.f₂_ne_zero
    intro v hv
    rw [d.ord_f₂, (d.disjoint v).resolve_left (Finsupp.mem_support_iff.mp hv), mul_zero]

/-- Exchange the two actual divisor/function pairs. -/
def symm : OriginalWeilDatum N L n where
  D₁ := d.D₂
  D₂ := d.D₁
  f₁ := d.f₂
  f₂ := d.f₁
  f₁_ne_zero := d.f₂_ne_zero
  f₂_ne_zero := d.f₁_ne_zero
  ord_f₁ := d.ord_f₂
  ord_f₂ := d.ord_f₁
  disjoint v := (d.disjoint v).symm

theorem symm_pairing : d.symm.pairing = d.pairing⁻¹ := by
  exact (inv_div _ _).symm

/-- Transport the literal representatives by the original coefficient and place actions. -/
def arithmetic (σ : L ≃ₐ[ℚ] L) : OriginalWeilDatum N L n where
  D₁ := originalArithmeticDivisorEquiv N σ d.D₁
  D₂ := originalArithmeticDivisorEquiv N σ d.D₂
  f₁ := originalArithmeticRingAut N σ d.f₁
  f₂ := originalArithmeticRingAut N σ d.f₂
  f₁_ne_zero := (map_ne_zero _).mpr d.f₁_ne_zero
  f₂_ne_zero := (map_ne_zero _).mpr d.f₂_ne_zero
  ord_f₁ v := by
    obtain ⟨w, rfl⟩ := (originalArithmeticPlaceEquiv N σ).surjective v
    change (originalArithmeticPlace N σ w).ord (originalArithmeticRingAut N σ d.f₁) =
      n * originalArithmeticDivisorEquiv N σ d.D₁ (originalArithmeticPlace N σ w)
    rw [originalArithmeticPlace_ord_action, originalArithmeticDivisorEquiv_apply, d.ord_f₁]
  ord_f₂ v := by
    obtain ⟨w, rfl⟩ := (originalArithmeticPlaceEquiv N σ).surjective v
    change (originalArithmeticPlace N σ w).ord (originalArithmeticRingAut N σ d.f₂) =
      n * originalArithmeticDivisorEquiv N σ d.D₂ (originalArithmeticPlace N σ w)
    rw [originalArithmeticPlace_ord_action, originalArithmeticDivisorEquiv_apply, d.ord_f₂]
  disjoint v := by
    obtain ⟨w, rfl⟩ := (originalArithmeticPlaceEquiv N σ).surjective v
    change originalArithmeticDivisorEquiv N σ d.D₁ (originalArithmeticPlace N σ w) = 0 ∨
      originalArithmeticDivisorEquiv N σ d.D₂ (originalArithmeticPlace N σ w) = 0
    rw [originalArithmeticDivisorEquiv_apply, originalArithmeticDivisorEquiv_apply]
    exact d.disjoint w

theorem arithmetic_pairing (σ : L ≃ₐ[ℚ] L) : (d.arithmetic σ).pairing = σ d.pairing := by
  change originalDivisorEval N L (originalArithmeticRingAut N σ d.f₁)
      (originalArithmeticDivisorEquiv N σ d.D₂) /
    originalDivisorEval N L (originalArithmeticRingAut N σ d.f₂)
      (originalArithmeticDivisorEquiv N σ d.D₁) = σ (_ / _)
  rw [originalDivisorEval_arithmetic, originalDivisorEval_arithmetic, map_div₀]

/-- Add first representatives that share the second divisor and function. -/
def addLeft (d' : OriginalWeilDatum N L n) (hD : d.D₂ = d'.D₂) : OriginalWeilDatum N L n where
  D₁ := d.D₁ + d'.D₁
  D₂ := d.D₂
  f₁ := d.f₁ * d'.f₁
  f₂ := d.f₂
  f₁_ne_zero := mul_ne_zero d.f₁_ne_zero d'.f₁_ne_zero
  f₂_ne_zero := d.f₂_ne_zero
  ord_f₁ v := by
    rw [v.ord_mul d.f₁_ne_zero d'.f₁_ne_zero, d.ord_f₁, d'.ord_f₁, Finsupp.add_apply, mul_add]
  ord_f₂ := d.ord_f₂
  disjoint v := by
    rcases eq_or_ne (d.D₂ v) 0 with h | h
    · exact Or.inr h
    · left
      rw [Finsupp.add_apply, (d.disjoint v).resolve_right h,
        (d'.disjoint v).resolve_right (hD ▸ h), add_zero]

theorem addLeft_pairing (d' : OriginalWeilDatum N L n) (hD : d.D₂ = d'.D₂)
    (hf : d.f₂ = d'.f₂) : (d.addLeft d' hD).pairing = d.pairing * d'.pairing := by
  have hnum : originalDivisorEval N L (d.f₁ * d'.f₁) d.D₂ =
      originalDivisorEval N L d.f₁ d.D₂ * originalDivisorEval N L d'.f₁ d.D₂ := by
    apply originalDivisorEval_mul
    · intro v hv
      apply v.mem_of_ord_nonneg
      rw [d.ord_f₁, (d.disjoint v).resolve_right (Finsupp.mem_support_iff.mp hv), mul_zero]
    · intro v hv
      apply v.mem_of_ord_nonneg
      rw [d'.ord_f₁, (d'.disjoint v).resolve_right (Finsupp.mem_support_iff.mp (hD ▸ hv)), mul_zero]
  have hden : originalDivisorEval N L d.f₂ (d.D₁ + d'.D₁) =
      originalDivisorEval N L d.f₂ d.D₁ * originalDivisorEval N L d.f₂ d'.D₁ := by
    apply originalDivisorEval_add
    intro v hv
    rcases hv with hv | hv
    · apply originalPlaceEval_ne_zero_of_ord_eq_zero N L v d.f₂_ne_zero
      rw [d.ord_f₂, (d.disjoint v).resolve_left (Finsupp.mem_support_iff.mp hv), mul_zero]
    · rw [hf]
      apply originalPlaceEval_ne_zero_of_ord_eq_zero N L v d'.f₂_ne_zero
      rw [d'.ord_f₂, (d'.disjoint v).resolve_left (Finsupp.mem_support_iff.mp hv), mul_zero]
  change originalDivisorEval N L (d.f₁ * d'.f₁) d.D₂ /
      originalDivisorEval N L d.f₂ (d.D₁ + d'.D₁) = _
  simp only [pairing]
  rw [hnum, hden, div_mul_div_comm, hD, hf]

end OriginalWeilDatum
end
end Dubon2026.SourceFunctionField

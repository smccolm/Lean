import Dubon2026.AdelicQuadraticCharacterValues

/-! # Genuine quadratic idele-class characters are determined by their original integral finite values -/

namespace Dubon2026

noncomputable section
open NumberField IsDedekindDomain

/-- Two actual quadratic rational idele-class characters agreeing on the original integral finite units agree on every original full idele. -/
theorem adelicQuadraticCharacter_eq_of_integral
    (ψ φ : (AdeleRing ℤ ℚ)ˣ →* ℂ)
    (hψq : ∀ a, ψ a ^ 2 = 1) (hφq : ∀ a, φ a ^ 2 = 1)
    (hψp : ∀ q : ℚˣ, ψ (Units.map (algebraMap ℚ (AdeleRing ℤ ℚ)).toMonoidHom q) = 1)
    (hφp : ∀ q : ℚˣ, φ (Units.map (algebraMap ℚ (AdeleRing ℤ ℚ)).toMonoidHom q) = 1)
    (hi : ∀ u : finiteAdeleIntegerSubringˣ,
      ψ (rationalIdeleFiniteEmbedding (Units.map finiteAdeleIntegerSubring.subtype.toMonoidHom u)) =
        φ (rationalIdeleFiniteEmbedding (Units.map finiteAdeleIntegerSubring.subtype.toMonoidHom u))) : ψ = φ := by
  have hf (a : (FiniteAdeleRing ℤ ℚ)ˣ) :
      ψ (rationalIdeleFiniteEmbedding a) = φ (rationalIdeleFiniteEmbedding a) := by
    rw [adelicQuadraticCharacter_finite_integral ψ hψq hψp,
      adelicQuadraticCharacter_finite_integral φ hφq hφp]
    exact hi _
  have hneg : ψ (rationalIdeleRealEmbedding (-1)) = φ (rationalIdeleRealEmbedding (-1)) := by
    let a := Units.map (algebraMap ℚ (FiniteAdeleRing ℤ ℚ)).toMonoidHom (-1 : ℚˣ)
    have hr : Units.map (Rat.castHom ℝ).toMonoidHom (-1 : ℚˣ) = -1 := by
      apply Units.ext
      change ((-1 : ℚ) : ℝ) = -1
      norm_num
    have hψ := hψp (-1)
    have hφ := hφp (-1)
    rw [rationalIdele_principal_factor, map_mul, hr] at hψ hφ
    have hn : ψ (rationalIdeleFiniteEmbedding a) ≠ 0 := by
      intro hz
      have hs := hψq (rationalIdeleFiniteEmbedding a)
      rw [hz, zero_pow (by decide)] at hs
      exact zero_ne_one hs
    apply mul_right_cancel₀ hn
    calc
      _ = 1 := hψ
      _ = _ := by rw [hf a]; exact hφ.symm
  have hr (r : ℝˣ) : ψ (rationalIdeleRealEmbedding r) = φ (rationalIdeleRealEmbedding r) := by
    by_cases hpos : 0 < r.val
    · rw [adelicQuadraticCharacter_real_positive ψ hψq r hpos,
        adelicQuadraticCharacter_real_positive φ hφq r hpos]
    · have hn : r.val < 0 := lt_of_le_of_ne (le_of_not_gt hpos) (Units.ne_zero r)
      rw [adelicQuadraticCharacter_real_negative ψ hψq r hn,
        adelicQuadraticCharacter_real_negative φ hφq r hn]
      exact hneg
  apply MonoidHom.ext
  intro a
  rw [adelicQuadraticCharacter_coordinate_value ψ hψq hψp,
    adelicQuadraticCharacter_coordinate_value φ hφq hφp, hr, hi]

end
end Dubon2026

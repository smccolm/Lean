import Dubon2026.AdelicDirichletCharacter

/-! # Rational triviality of the genuine continuous Dirichlet idèle character -/

namespace Dubon2026

noncomputable section
open NumberField IsDedekindDomain

variable {D : ℕ} [NeZero D] (χ : DirichletCharacter ℂ D)

/-- The actual finite character at minus one is the inverse original Dirichlet parity. -/
theorem finiteIdeleDirichletCharacter_neg_one :
    finiteIdeleDirichletCharacter χ (-1) = (χ (-1))⁻¹ := by
  have he : Units.map finiteAdeleIntegerSubring.subtype.toMonoidHom
      (-1 : finiteAdeleIntegerSubringˣ) = (-1 : (FiniteAdeleRing ℤ ℚ)ˣ) := Units.ext rfl
  have hr : finiteAdeleResidue D (-1 : finiteAdeleIntegerSubringˣ).val = -1 := by
    change finiteAdeleResidue D (-1) = -1
    rw [map_neg, map_one]
  simpa only [he, hr] using finiteIdeleDirichletCharacter_integral χ (-1)

/-- The actual real and finite parity factors cancel on the principal negative identity. -/
theorem adelicDirichletCharacter_neg_one : adelicDirichletCharacter χ (-1) = 1 := by
  have hr : rationalIdeleRealHom (-1) = -1 := by
    apply Units.ext
    change ((RingHom.fst ℝ (FiniteAdeleRing ℤ ℚ)).comp
      rationalAdeleRealFiniteRingEquiv.toRingHom) (-1) = (-1 : ℝ)
    rw [map_neg, map_one]
  have hf : rationalIdeleFiniteHom (-1) = -1 := by
    apply Units.ext
    change ((RingHom.snd ℝ (FiniteAdeleRing ℤ ℚ)).comp
      rationalAdeleRealFiniteRingEquiv.toRingHom) (-1) = (-1 : FiniteAdeleRing ℤ ℚ)
    rw [map_neg, map_one]
  rw [adelicDirichletCharacter_apply, hr, hf, realDirichletSignCharacter_negative χ _ (by norm_num),
    finiteIdeleDirichletCharacter_neg_one]
  exact mul_inv_cancel₀ (IsUnit.map χ (isUnit_neg_one : IsUnit (-1 : ZMod D))).ne_zero

/-- The constructed continuous character is trivial on every original principal rational idele, with both rational signs included. -/
theorem adelicDirichletCharacter_rational (q : ℚˣ) :
    adelicDirichletCharacter χ (Units.map (algebraMap ℚ (AdeleRing ℤ ℚ)).toMonoidHom q) = 1 := by
  rcases (Units.ne_zero q).lt_or_gt with hq | hq
  · have he : q = (-1) * (-q) := by simp
    have hm : Units.map (algebraMap ℚ (AdeleRing ℤ ℚ)).toMonoidHom (-1 : ℚˣ) = -1 := by
      apply Units.ext
      change algebraMap ℚ (AdeleRing ℤ ℚ) (-1) = (-1 : AdeleRing ℤ ℚ)
      rw [map_neg, map_one]
    rw [he, map_mul, map_mul, hm, adelicDirichletCharacter_neg_one, one_mul]
    exact adelicDirichletCharacter_positive_rational χ (-q) (neg_pos.mpr hq)
  · exact adelicDirichletCharacter_positive_rational χ q hq

end
end Dubon2026

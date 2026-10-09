import Dubon2026.RealQuadraticCharacter
import Dubon2026.RationalIdeleCoordinates
import Dubon2026.FiniteIdeleIntegralNormalization

/-! # Original real and finite values of genuine quadratic rational idele-class characters -/

namespace Dubon2026

noncomputable section
open NumberField IsDedekindDomain

/-- A genuine quadratic character of the original full ideles is trivial on every embedded positive real unit. -/
theorem adelicQuadraticCharacter_real_positive (ψ : (AdeleRing ℤ ℚ)ˣ →* ℂ)
    (hq : ∀ a, ψ a ^ 2 = 1) (r : ℝˣ) (hr : 0 < r.val) :
    ψ (rationalIdeleRealEmbedding r) = 1 :=
  realQuadraticCharacter_positive (ψ.comp rationalIdeleRealEmbedding) (fun u => hq (rationalIdeleRealEmbedding u)) r hr

/-- On actual negative real units the original quadratic idele character has exactly its original real minus-one value. -/
theorem adelicQuadraticCharacter_real_negative (ψ : (AdeleRing ℤ ℚ)ˣ →* ℂ)
    (hq : ∀ a, ψ a ^ 2 = 1) (r : ℝˣ) (hr : r.val < 0) :
    ψ (rationalIdeleRealEmbedding r) = ψ (rationalIdeleRealEmbedding (-1)) :=
  realQuadraticCharacter_negative (ψ.comp rationalIdeleRealEmbedding) (fun u => hq (rationalIdeleRealEmbedding u)) r hr

/-- Actual principal rational triviality forces the original finite restriction to be trivial on positive rational units. -/
theorem adelicQuadraticCharacter_finite_positive (ψ : (AdeleRing ℤ ℚ)ˣ →* ℂ)
    (hq : ∀ a, ψ a ^ 2 = 1)
    (hp : ∀ q : ℚˣ, ψ (Units.map (algebraMap ℚ (AdeleRing ℤ ℚ)).toMonoidHom q) = 1)
    (q : ℚˣ) (hqpos : 0 < q.val) :
    ψ (rationalIdeleFiniteEmbedding (Units.map (algebraMap ℚ (FiniteAdeleRing ℤ ℚ)).toMonoidHom q)) = 1 := by
  have hr : 0 < (Units.map (Rat.castHom ℝ).toMonoidHom q).val := by
    change (0 : ℝ) < (q.val : ℝ)
    exact_mod_cast hqpos
  have h := hp q
  rw [rationalIdele_principal_factor, map_mul, adelicQuadraticCharacter_real_positive ψ hq _ hr,
    one_mul] at h
  exact h

/-- The actual positive-rational/integral-unit factorization determines every finite character value from its original integral unit. -/
theorem adelicQuadraticCharacter_finite_integral (ψ : (AdeleRing ℤ ℚ)ˣ →* ℂ)
    (hq : ∀ a, ψ a ^ 2 = 1)
    (hp : ∀ q : ℚˣ, ψ (Units.map (algebraMap ℚ (AdeleRing ℤ ℚ)).toMonoidHom q) = 1)
    (a : (FiniteAdeleRing ℤ ℚ)ˣ) :
    ψ (rationalIdeleFiniteEmbedding a) = ψ (rationalIdeleFiniteEmbedding
      (Units.map finiteAdeleIntegerSubring.subtype.toMonoidHom (finiteIdeleIntegralUnitPart a))) := by
  let q : ℚˣ := Units.mk0 (finiteIdelePositiveRationalPart a) (ne_of_gt (finiteIdelePositiveRationalPart_pos a))
  have he : a = Units.map (algebraMap ℚ (FiniteAdeleRing ℤ ℚ)).toMonoidHom q *
      Units.map finiteAdeleIntegerSubring.subtype.toMonoidHom (finiteIdeleIntegralUnitPart a) :=
    Units.ext (finiteIdeleIntegralUnitPart_spec a)
  calc
    _ = ψ (rationalIdeleFiniteEmbedding (Units.map (algebraMap ℚ (FiniteAdeleRing ℤ ℚ)).toMonoidHom q *
        Units.map finiteAdeleIntegerSubring.subtype.toMonoidHom (finiteIdeleIntegralUnitPart a))) :=
      congrArg (fun b => ψ (rationalIdeleFiniteEmbedding b)) he
    _ = _ := by
      rw [map_mul, map_mul, adelicQuadraticCharacter_finite_positive ψ hq hp q
        (finiteIdelePositiveRationalPart_pos a), one_mul]

/-- Every original full quadratic idele-class value is exactly its real-coordinate value times the value on the canonically normalized original integral finite unit. -/
theorem adelicQuadraticCharacter_coordinate_value (ψ : (AdeleRing ℤ ℚ)ˣ →* ℂ)
    (hq : ∀ a, ψ a ^ 2 = 1)
    (hp : ∀ q : ℚˣ, ψ (Units.map (algebraMap ℚ (AdeleRing ℤ ℚ)).toMonoidHom q) = 1)
    (a : (AdeleRing ℤ ℚ)ˣ) :
    ψ a = ψ (rationalIdeleRealEmbedding (rationalIdeleRealHom a)) *
      ψ (rationalIdeleFiniteEmbedding (Units.map finiteAdeleIntegerSubring.subtype.toMonoidHom
        (finiteIdeleIntegralUnitPart (rationalIdeleFiniteHom a)))) := by
  calc
    ψ a = ψ (rationalIdeleRealEmbedding (rationalIdeleRealHom a) *
        rationalIdeleFiniteEmbedding (rationalIdeleFiniteHom a)) :=
      congrArg ψ (rationalIdele_real_mul_finite a).symm
    _ = _ := by rw [map_mul, adelicQuadraticCharacter_finite_integral ψ hq hp]

end
end Dubon2026

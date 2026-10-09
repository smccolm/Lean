import Dubon2026.FiniteIdelePositiveUnitUniqueness

/-! # The canonical integral-unit normalization of a genuine rational finite idele -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain

/-- The positive rational factor in the proved genuine finite-idele factorization. -/
def finiteIdelePositiveRationalPart (a : (FiniteAdeleRing ℤ ℚ)ˣ) : ℚ :=
  (finiteIdele_positive_rational_integral_unit a).choose

/-- The chosen original rational factor is positive. -/
theorem finiteIdelePositiveRationalPart_pos (a : (FiniteAdeleRing ℤ ℚ)ˣ) :
    0 < finiteIdelePositiveRationalPart a :=
  (finiteIdele_positive_rational_integral_unit a).choose_spec.1

/-- The actual everywhere-integral unit after removing the positive rational factor. -/
def finiteIdeleIntegralUnitPart (a : (FiniteAdeleRing ℤ ℚ)ˣ) : finiteAdeleIntegerSubringˣ :=
  (finiteIdele_positive_rational_integral_unit a).choose_spec.2.choose

/-- The canonical factors multiply to the original finite idele. -/
theorem finiteIdeleIntegralUnitPart_spec (a : (FiniteAdeleRing ℤ ℚ)ˣ) :
    a.val = algebraMap ℚ (FiniteAdeleRing ℤ ℚ) (finiteIdelePositiveRationalPart a) *
      (finiteIdeleIntegralUnitPart a).val.val :=
  (finiteIdele_positive_rational_integral_unit a).choose_spec.2.choose_spec

/-- The actual integral normalization preserves the identity. -/
theorem finiteIdeleIntegralUnitPart_one : finiteIdeleIntegralUnitPart 1 = 1 := by
  apply finiteIdele_integral_factor_unique (finiteIdelePositiveRationalPart 1) 1
    (finiteIdelePositiveRationalPart_pos 1) zero_lt_one
  simpa only [map_one, Units.val_one, OneMemClass.coe_one, mul_one] using
    (finiteIdeleIntegralUnitPart_spec 1).symm

/-- Uniqueness of the positive-rational factorization proves multiplicativity of the original integral normalization. -/
theorem finiteIdeleIntegralUnitPart_mul (a b : (FiniteAdeleRing ℤ ℚ)ˣ) :
    finiteIdeleIntegralUnitPart (a * b) = finiteIdeleIntegralUnitPart a * finiteIdeleIntegralUnitPart b := by
  apply finiteIdele_integral_factor_unique (finiteIdelePositiveRationalPart (a * b))
    (finiteIdelePositiveRationalPart a * finiteIdelePositiveRationalPart b)
    (finiteIdelePositiveRationalPart_pos (a * b))
    (mul_pos (finiteIdelePositiveRationalPart_pos a) (finiteIdelePositiveRationalPart_pos b))
  calc
    _ = (a * b).val := (finiteIdeleIntegralUnitPart_spec (a * b)).symm
    _ = a.val * b.val := rfl
    _ = _ := by
      rw [finiteIdeleIntegralUnitPart_spec a, finiteIdeleIntegralUnitPart_spec b, map_mul]
      change _ = _ * ((finiteIdeleIntegralUnitPart a).val.val * (finiteIdeleIntegralUnitPart b).val.val)
      ring

/-- The genuine multiplicative retraction from rational finite ideles to their integral-unit factors. -/
def finiteIdeleIntegralUnitHom : (FiniteAdeleRing ℤ ℚ)ˣ →* finiteAdeleIntegerSubringˣ where
  toFun := finiteIdeleIntegralUnitPart
  map_one' := finiteIdeleIntegralUnitPart_one
  map_mul' := finiteIdeleIntegralUnitPart_mul

/-- An original integral unit has itself as its canonical integral factor. -/
theorem finiteIdeleIntegralUnitHom_integral (u : finiteAdeleIntegerSubringˣ) :
    finiteIdeleIntegralUnitHom (Units.map finiteAdeleIntegerSubring.subtype.toMonoidHom u) = u := by
  apply finiteIdele_integral_factor_unique
    (finiteIdelePositiveRationalPart (Units.map finiteAdeleIntegerSubring.subtype.toMonoidHom u)) 1
    (finiteIdelePositiveRationalPart_pos _) zero_lt_one
  simpa only [map_one, one_mul] using
    (finiteIdeleIntegralUnitPart_spec (Units.map finiteAdeleIntegerSubring.subtype.toMonoidHom u)).symm

/-- Every original positive principal rational idele has trivial integral normalization. -/
theorem finiteIdeleIntegralUnitHom_positive_rational (q : ℚ) (hq : 0 < q) :
    finiteIdeleIntegralUnitHom
      (Units.map (algebraMap ℚ (FiniteAdeleRing ℤ ℚ)).toMonoidHom (Units.mk0 q (ne_of_gt hq))) = 1 := by
  apply finiteIdele_integral_factor_unique
    (finiteIdelePositiveRationalPart
      (Units.map (algebraMap ℚ (FiniteAdeleRing ℤ ℚ)).toMonoidHom (Units.mk0 q (ne_of_gt hq)))) q
    (finiteIdelePositiveRationalPart_pos _) hq
  simpa only [Units.val_one, OneMemClass.coe_one, mul_one] using
    (finiteIdeleIntegralUnitPart_spec
      (Units.map (algebraMap ℚ (FiniteAdeleRing ℤ ℚ)).toMonoidHom (Units.mk0 q (ne_of_gt hq)))).symm

end
end Dubon2026

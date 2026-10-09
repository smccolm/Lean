import Dubon2026.LocalInducedUpperValue
import Dubon2026.FinitePlaceHeckeRepresentativeEntries
import Dubon2026.FinitePlaceHeckeRadialCosets

/-! # Exact original matrix branches for the genuine local induced Hecke sum -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup

/-- The original extended Euclidean coefficients at a prime and level one are exactly zero and one. -/
theorem prime_level_one_bezout (p : ℕ) (hp : p.Prime) :
    Int.gcdA p 1 = 0 ∧ Int.gcdB p 1 = 1 := by
  have he : Nat.xgcd p 1 = (0, 1) := by
    have hd : (1 : ℤ) / p = 0 :=
      Int.ediv_eq_zero_of_lt (by norm_num) (by exact_mod_cast hp.one_lt)
    unfold Nat.xgcd
    rw [Nat.xgcdAux_rec hp.pos, Nat.mod_eq_of_lt hp.one_lt,
      Nat.xgcdAux_rec (by decide : 0 < 1), Nat.mod_one, Nat.xgcd_zero_left]
    simp [hd]
  constructor
  · change (Nat.xgcd p 1).1 = 0
    rw [he]
  · change (Nat.xgcd p 1).2 = 1
    rw [he]

/-- Every original translation branch is literally its original upper unipotent times the original inverse-prime diagonal. -/
theorem finitePlaceHecke_some_inverse_pair (p : ℕ) [NeZero p] (v : HeightOneSpectrum ℤ)
    (a : ZMod p) :
    (finitePlaceHeckeGamma 1 p (Nat.coprime_one_right p) v (some a))⁻¹ *
      (GeneralLinearGroup.map (finiteAdelePlace v) (finiteAdelicHeckeDiagonal p))⁻¹ =
    toGL (ringUpperUnipotent (-(a.val : v.adicCompletion ℚ))) *
      gl2UnitDiagonalPair 1 (finitePlacePrimeUnit p v)⁻¹ := by
  congr 1
  · apply Units.ext
    rw [finitePlaceHeckeGamma_some_inv_val]
    rfl
  · rw [finitePlaceHeckeDiagonal_eq_pair]
    rfl

/-- The original level-one Bezout branch has an explicit genuine lower-Borel and integral swap factorization. -/
theorem finitePlaceHecke_none_inverse_pair (p : ℕ) [NeZero p] (hp : p.Prime)
    (v : HeightOneSpectrum ℤ) :
    (finitePlaceHeckeGamma 1 p (Nat.coprime_one_right p) v none)⁻¹ *
      (GeneralLinearGroup.map (finiteAdelePlace v) (finiteAdelicHeckeDiagonal p))⁻¹ =
    (toGL (ringLowerUnipotent (p : v.adicCompletion ℚ)) *
      gl2UnitDiagonalPair (finitePlacePrimeUnit p v)⁻¹ (-1)) * gl2CoordinateSwap := by
  have hp0 : (p : v.adicCompletion ℚ) ≠ 0 := by
    simpa only [finitePlacePrimeUnit_val] using (finitePlacePrimeUnit p v).ne_zero
  apply Units.ext
  rw [Units.val_mul, finitePlaceHeckeGamma_none_inv_val, finitePlaceHeckeDiagonal_inverse_val,
    Nat.cast_one,
    (prime_level_one_bezout p hp).1, (prime_level_one_bezout p hp).2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gl2UnitDiagonalPair, ringLowerUnipotent, toGL, gl2CoordinateSwap,
      Matrix.mul_apply, Fin.sum_univ_two, Units.val_inv_eq_inv_val, finitePlacePrimeUnit_val, hp0]

end
end Dubon2026

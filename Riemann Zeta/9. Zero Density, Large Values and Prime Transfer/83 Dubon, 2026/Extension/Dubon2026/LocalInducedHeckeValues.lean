import Dubon2026.LocalInducedHeckeCosetMatrices

/-! # The exact original spherical values on every genuine local Hecke branch -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup

/-- The original zero-residue Hecke branch has exactly the inverse second inducing value. -/
theorem finitePlaceInducedSpherical_hecke_zero (p : ℕ) [NeZero p] (hp : p.Prime)
    (z₁ z₂ : ℂˣ) :
    (finitePlaceInducedSpherical (rationalPrimePlace p hp) z₁ z₂).val
      ((finitePlaceHeckeGamma 1 p (Nat.coprime_one_right p) (rationalPrimePlace p hp) (some 0))⁻¹ *
        (GeneralLinearGroup.map (finiteAdelePlace (rationalPrimePlace p hp))
          (finiteAdelicHeckeDiagonal p))⁻¹) = (z₂⁻¹ : ℂˣ) := by
  rw [finitePlaceHecke_some_inverse_pair]
  have hzero : toGL (ringUpperUnipotent (-(0 : ZMod p).val :
      (rationalPrimePlace p hp).adicCompletion ℚ)) = 1 := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [toGL, ringUpperUnipotent]
  rw [hzero, one_mul]
  exact finitePlaceInducedSpherical_second_inverse_prime p hp z₁ z₂

/-- Each original nonzero residue Hecke branch has exactly the inverse first inducing value. -/
theorem finitePlaceInducedSpherical_hecke_nonzero (p : ℕ) [NeZero p] (hp : p.Prime)
    (z₁ z₂ : ℂˣ) (a : ZMod p) (ha : a ≠ 0) :
    (finitePlaceInducedSpherical (rationalPrimePlace p hp) z₁ z₂).val
      ((finitePlaceHeckeGamma 1 p (Nat.coprime_one_right p) (rationalPrimePlace p hp) (some a))⁻¹ *
        (GeneralLinearGroup.map (finiteAdelePlace (rationalPrimePlace p hp))
          (finiteAdelicHeckeDiagonal p))⁻¹) = (z₁⁻¹ : ℂˣ) := by
  let v := rationalPrimePlace p hp
  obtain ⟨u, hu⟩ := rationalPrimePlace_integer_unit p hp (a.val : ℤ)
    (zmod_nonzero_val_not_dvd p a ha)
  let uF : (v.adicCompletion ℚ)ˣ :=
    Units.map (v.adicCompletionIntegers ℚ).toSubring.subtype.toMonoidHom u
  have hv : uF.val = (a.val : v.adicCompletion ℚ) := by simpa using hu
  rw [finitePlaceHecke_some_inverse_pair, ← hv]
  rw [finitePlaceInducedSpherical_upper_inverse v z₁ z₂ uF (finitePlacePrimeUnit p v)
    u.val.property u.inv.property (by
      rw [finitePlacePrimeUnit_val]
      exact natCast_mem (v.adicCompletionIntegers ℚ) p)]
  rw [finitePlaceUnramifiedCharacter_prime]

/-- The original Bezout Hecke branch has exactly the inverse first inducing value. -/
theorem finitePlaceInducedSpherical_hecke_none (p : ℕ) [NeZero p] (hp : p.Prime)
    (z₁ z₂ : ℂˣ) :
    (finitePlaceInducedSpherical (rationalPrimePlace p hp) z₁ z₂).val
      ((finitePlaceHeckeGamma 1 p (Nat.coprime_one_right p) (rationalPrimePlace p hp) none)⁻¹ *
        (GeneralLinearGroup.map (finiteAdelePlace (rationalPrimePlace p hp))
          (finiteAdelicHeckeDiagonal p))⁻¹) = (z₁⁻¹ : ℂˣ) := by
  let v := rationalPrimePlace p hp
  let b := gl2LowerUnipotent (p : v.adicCompletion ℚ) *
    gl2LowerDiagonalPair (finitePlacePrimeUnit p v)⁻¹ (-1)
  let k : finitePlaceGL2Gamma0 1 v := ⟨gl2CoordinateSwap, finitePlace_coordinateSwap_integral v⟩
  rw [finitePlaceHecke_none_inverse_pair p hp]
  change (finitePlaceInducedSpherical v z₁ z₂).val (b.val * k.val) = _
  rw [show (finitePlaceInducedSpherical v z₁ z₂).val (b.val * k.val) =
      finitePlaceLowerCharacter v z₁ z₂ b from iwasawaInducedSection_mul _ _ _ _ _ _ b k]
  rw [map_mul, finitePlaceLowerCharacter_unipotent, one_mul]
  change ((finitePlaceUnramifiedCharacter v z₁
    (gl2LowerDiagonalHom 0 (gl2LowerDiagonalPair (finitePlacePrimeUnit p v)⁻¹ (-1))) *
    finitePlaceUnramifiedCharacter v z₂
    (gl2LowerDiagonalHom 1 (gl2LowerDiagonalPair (finitePlacePrimeUnit p v)⁻¹ (-1))) : ℂˣ) : ℂ) = _
  rw [gl2LowerDiagonalHom_pair_zero, gl2LowerDiagonalHom_pair_one, map_inv,
    finitePlaceUnramifiedCharacter_neg_integral v z₂ 1
      (v.adicCompletionIntegers ℚ).one_mem (v.adicCompletionIntegers ℚ).one_mem,
    mul_one, finitePlaceUnramifiedCharacter_prime]

end
end Dubon2026

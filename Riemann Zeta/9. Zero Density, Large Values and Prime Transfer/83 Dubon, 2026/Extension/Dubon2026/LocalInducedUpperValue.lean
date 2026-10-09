import Dubon2026.LocalInducedUpperFactor

/-! # The actual spherical value of the original upper inverse-diagonal branch -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup

/-- The original inducing character is trivial on every actual lower unipotent. -/
theorem finitePlaceLowerCharacter_unipotent (v : HeightOneSpectrum ℤ) (z₁ z₂ : ℂˣ)
    (t : v.adicCompletion ℚ) :
    finitePlaceLowerCharacter v z₁ z₂ (gl2LowerUnipotent t) = 1 := by
  change ((finitePlaceUnramifiedCharacter v z₁ (gl2LowerDiagonalHom 0 (gl2LowerUnipotent t)) *
    finitePlaceUnramifiedCharacter v z₂ (gl2LowerDiagonalHom 1 (gl2LowerUnipotent t)) : ℂˣ) : ℂ) = 1
  rw [gl2LowerDiagonalHom_unipotent, gl2LowerDiagonalHom_unipotent, map_one, map_one,
    one_mul, Units.val_one]

/-- The original spherical section takes its exact first-character inverse value on each upper inverse-diagonal matrix with an original integral unit translation. -/
theorem finitePlaceInducedSpherical_upper_inverse (v : HeightOneSpectrum ℤ) (z₁ z₂ : ℂˣ)
    (a q : (v.adicCompletion ℚ)ˣ)
    (ha : a.val ∈ v.adicCompletionIntegers ℚ)
    (hai : a.inv ∈ v.adicCompletionIntegers ℚ)
    (hq : q.val ∈ v.adicCompletionIntegers ℚ) :
    (finitePlaceInducedSpherical v z₁ z₂).val
      (toGL (ringUpperUnipotent (-a.val)) * gl2UnitDiagonalPair 1 q⁻¹) =
      ((finitePlaceUnramifiedCharacter v z₁ q)⁻¹ : ℂˣ) := by
  let b := gl2LowerUnipotent (-(a⁻¹).val) * gl2LowerDiagonalPair (-a * q⁻¹) a⁻¹
  let k : finitePlaceGL2Gamma0 1 v :=
    ⟨toGL (ringUpperUnipotent (-(q * a⁻¹).val)) * gl2CoordinateSwap,
      finitePlace_upper_inverse_factor_integral v a q hai hq⟩
  rw [gl2_upper_inverse_diagonal_factor]
  change (finitePlaceInducedSpherical v z₁ z₂).val (b.val * k.val) = _
  rw [show (finitePlaceInducedSpherical v z₁ z₂).val (b.val * k.val) =
      finitePlaceLowerCharacter v z₁ z₂ b from iwasawaInducedSection_mul _ _ _ _ _ _ b k]
  rw [map_mul, finitePlaceLowerCharacter_unipotent, one_mul]
  change ((finitePlaceUnramifiedCharacter v z₁
    (gl2LowerDiagonalHom 0 (gl2LowerDiagonalPair (-a * q⁻¹) a⁻¹)) *
    finitePlaceUnramifiedCharacter v z₂
    (gl2LowerDiagonalHom 1 (gl2LowerDiagonalPair (-a * q⁻¹) a⁻¹)) : ℂˣ) : ℂ) = _
  rw [gl2LowerDiagonalHom_pair_zero, gl2LowerDiagonalHom_pair_one, map_mul,
    finitePlaceUnramifiedCharacter_neg_integral v z₁ a ha hai, one_mul,
    map_inv, map_inv, finitePlaceUnramifiedCharacter_integral v z₂ a ha hai,
    inv_one, mul_one]

end
end Dubon2026

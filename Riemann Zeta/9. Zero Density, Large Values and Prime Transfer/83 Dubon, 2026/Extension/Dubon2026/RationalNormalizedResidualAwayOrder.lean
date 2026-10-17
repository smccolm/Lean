import Dubon2026.RationalCyclotomicPrincipalCharacterSum

/-! # Removing one prime power preserves every other local order and the sign

The native normalized-residual proof already contains the complete
valuation calculation independent of a cyclotomic field. Exposing this
calculation lets DUB-17 use it for the noncyclic two-power containing field
without reproving local reciprocity or assuming its desired compatibility.
-/
namespace Dubon2026
noncomputable section
open IsDedekindDomain HeightOneSpectrum

/-- Removing the normalized conductor-prime power leaves every other
original rational local order unchanged. -/
theorem rationalPrimeNormalizedResidual_away_order
    (p : ℕ) (hp : p.Prime) (v : HeightOneSpectrum ℤ)
    (hvp : Rat.HeightOneSpectrum.natGenerator v ≠ p) (q : ℚˣ) :
    localFieldUnitOrder
      (rationalPrimeLocalField (Rat.HeightOneSpectrum.natGenerator v)
        (Rat.HeightOneSpectrum.prime_natGenerator v))
      (Additive.ofMul (rationalPrimeRationalUnit (Rat.HeightOneSpectrum.natGenerator v)
        (Rat.HeightOneSpectrum.prime_natGenerator v) (rationalPrimeNormalizedResidual p hp q))) =
    localFieldUnitOrder
      (rationalPrimeLocalField (Rat.HeightOneSpectrum.natGenerator v)
        (Rat.HeightOneSpectrum.prime_natGenerator v))
      (Additive.ofMul (rationalPrimeRationalUnit (Rat.HeightOneSpectrum.natGenerator v)
        (Rat.HeightOneSpectrum.prime_natGenerator v) q)) := by
  let l := Rat.HeightOneSpectrum.natGenerator v
  let hl : l.Prime := Rat.HeightOneSpectrum.prime_natGenerator v
  let K := rationalPrimeLocalField l hl
  let z := localFieldUnitOrder (rationalPrimeLocalField p hp)
    (Additive.ofMul (rationalPrimeRationalUnit p hp q))
  have hprimeVal : v.valuation ℚ (p : ℚ) = 1 :=
    rationalHeightOneSpectrum_valuation_prime_eq_one_of_ne v p hp hvp
  have hprimeOrder : localFieldUnitOrder K
      (Additive.ofMul (rationalPrimeRationalUnit l hl
        (rationalPrimeRationalPrimeUnit p hp))) = 0 := by
    change localFieldUnitOrder (rationalPrimeLocalField l hl)
      (Additive.ofMul (Units.map
        (algebraMap ℚ (rationalPrimeLocalField l hl)).toMonoidHom
        (rationalPrimeRationalPrimeUnit p hp))) = 0
    rw [rationalPrimeLocalField_rational_order]
    change -WithZero.log ((rationalPrimePlace l hl).valuation ℚ (p : ℚ)) = 0
    rw [show rationalPrimePlace l hl = v by
      exact rationalPrimePlace_of_natGenerator v, hprimeVal]
    simp
  have horder : localFieldUnitOrder K
      (Additive.ofMul (rationalPrimeRationalUnit l hl
        (rationalPrimeNormalizedResidual p hp q))) =
      localFieldUnitOrder K
        (Additive.ofMul (rationalPrimeRationalUnit l hl q)) := by
    have hunit : rationalPrimeRationalUnit l hl
        (rationalPrimeNormalizedResidual p hp q) =
        rationalPrimeRationalUnit l hl q /
          rationalPrimeRationalUnit l hl
            (rationalPrimeRationalPrimeUnit p hp) ^ z := by
      apply Units.ext
      simp [rationalPrimeNormalizedResidual, rationalPrimeRationalUnit,
        rationalPrimeRationalPrimeUnit, z]
    rw [hunit]
    change localFieldUnitOrder K
        (Additive.ofMul (rationalPrimeRationalUnit l hl q) -
          z • Additive.ofMul (rationalPrimeRationalUnit l hl
            (rationalPrimeRationalPrimeUnit p hp))) = _
    rw [map_sub, map_zsmul, hprimeOrder, smul_zero, sub_zero]
  exact horder

/-- Dividing a rational unit by a positive prime power preserves its sign. -/
theorem rationalPrimeNormalizedResidual_positive_iff
    (p : ℕ) (hp : p.Prime) (q : ℚˣ) :
    0 < (rationalPrimeNormalizedResidual p hp q).val ↔ 0 < q.val := by
  simp only [rationalPrimeNormalizedResidual, Units.val_div_eq_div_val,
    Units.val_zpow_eq_zpow_val]
  change 0 < q.val / (p : ℚ) ^
    localFieldUnitOrder (rationalPrimeLocalField p hp)
      (Additive.ofMul (rationalPrimeRationalUnit p hp q)) ↔ 0 < q.val
  exact div_pos_iff_of_pos_right (zpow_pos (Nat.cast_pos.mpr hp.pos) _)

end
end Dubon2026

import Dubon2026.ArithmeticCyclotomicCoefficientCharacter

/-! Root fixing at the constructed auxiliary power level implies triviality
of the original arithmetic cyclotomic coefficient character. This discharges
the character premises in DUB-17's actual twisted trace-cocycle detection. -/

namespace Dubon2026
noncomputable section
open scoped NumberField

/-- Fixing any actual primitive root forces the original finite arithmetic
cyclotomic character to be one, independently of its chosen defining root. -/
theorem rationalArithmeticCyclotomicCharacter_eq_one_of_fixed_root
    (a : 𝓞 ℚ) (q : ℕ) [NeZero q] (hqa : (q : 𝓞 ℚ) ∣ a)
    {ζ : rationalUnramifiedExtension a} (hζ : IsPrimitiveRoot ζ q)
    (g : rationalArithmeticGaloisGroup a)
    (hfix : let U := rationalUnramifiedExtension a
      letI : Algebra ℚ U := U.algebra'
      (show Gal(U/ℚ) from g) ζ = ζ) :
    rationalArithmeticCyclotomicCharacter a q hqa g = 1 := by
  apply Units.ext
  apply ZMod.val_injective
  apply hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
  have hg := rationalArithmeticCyclotomicCharacter_apply_root a q hqa g hζ
  have h1 := rationalArithmeticCyclotomicCharacter_apply_root a q hqa 1 hζ
  rw [map_one] at h1
  exact hg.symm.trans (hfix.trans h1)

/-- Fixing the original primitive power root fixes its primitive q-th
power descendant and therefore kills the original q-cyclotomic character. -/
theorem rationalArithmeticCyclotomicCharacter_eq_one_of_fixed_power_root
    (a : 𝓞 ℚ) (q n : ℕ) [NeZero q] (hqa : (q : 𝓞 ℚ) ∣ a)
    {ζ : rationalUnramifiedExtension a} (hζ : IsPrimitiveRoot ζ (q ^ (n + 1)))
    (g : rationalArithmeticGaloisGroup a)
    (hfix : let U := rationalUnramifiedExtension a
      letI : Algebra ℚ U := U.algebra'
      (show Gal(U/ℚ) from g) ζ = ζ) :
    rationalArithmeticCyclotomicCharacter a q hqa g = 1 := by
  have hμ : IsPrimitiveRoot (ζ ^ (q ^ n)) q :=
    IsPrimitiveRoot.pow (pow_pos (NeZero.pos q) _) hζ (pow_succ q n)
  apply rationalArithmeticCyclotomicCharacter_eq_one_of_fixed_root a q hqa hμ g
  let U := rationalUnramifiedExtension a
  letI : Algebra ℚ U := U.algebra'
  change (show Gal(U/ℚ) from g) (ζ ^ (q ^ n)) = ζ ^ (q ^ n)
  rw [map_pow, hfix]

/-- The same original root condition discharges the scalar-character
premise for the actual arithmetic twisted trace-zero representation. -/
theorem rationalArithmeticCyclotomicCoefficient_eq_one_of_fixed_power_root
    (a : 𝓞 ℚ) (q n : ℕ) [NeZero q] (hqa : (q : 𝓞 ℚ) ∣ a)
    (k : Type) [CommRing k] [CharP k q] [TopologicalSpace k]
    {ζ : rationalUnramifiedExtension a} (hζ : IsPrimitiveRoot ζ (q ^ (n + 1)))
    (g : rationalArithmeticGaloisGroup a)
    (hfix : let U := rationalUnramifiedExtension a
      letI : Algebra ℚ U := U.algebra'
      (show Gal(U/ℚ) from g) ζ = ζ) :
    rationalArithmeticCyclotomicCoefficientCharacter a q hqa k g = 1 := by
  change finiteCyclotomicCoefficientMap q k (rationalArithmeticCyclotomicCharacter a q hqa g) = 1
  rw [rationalArithmeticCyclotomicCharacter_eq_one_of_fixed_power_root a q n hqa hζ g hfix,
    map_one]

end
end Dubon2026

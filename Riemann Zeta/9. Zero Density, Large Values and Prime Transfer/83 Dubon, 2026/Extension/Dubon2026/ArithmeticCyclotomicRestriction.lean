import Dubon2026.RationalArithmeticCyclotomicCharacter
import Dubon2026.RationalPrimeCyclotomicCharacter

/-! # The original arithmetic cyclotomic character restricts to the actual local character -/

namespace Dubon2026
noncomputable section
open scoped NumberField

/-- Compare the genuine exponent actions on an original primitive root and its
image under the same embedding that defines arithmetic restriction. This proves
equality of the entire continuous characters at the actual prime completion. -/
theorem rationalArithmeticCyclotomicCharacter_restriction
    (a : 𝓞 ℚ) (n : ℕ) [NeZero n] (hna : (n : 𝓞 ℚ) ∣ a)
    (p : ℕ) (hp : p.Prime) :
    (rationalArithmeticCyclotomicCharacter a n hna).comp
        (rationalPrimeArithmeticRestriction a p hp) =
      rationalPrimeCyclotomicCharacter p hp n := by
  let U := rationalUnramifiedExtension a
  letI : Algebra ℚ U := U.algebra'
  obtain ⟨ζ, hζ⟩ :=
    originalQUnramifiedUnion_exists_primitiveRoot (Ω := AlgebraicClosure ℚ) a n hna
  let e : U →ₐ[ℚ] rationalPrimeLocalClosure p hp := rationalArithmeticLocalEmbedding a
  have heζ : IsPrimitiveRoot (e ζ) n := hζ.map_of_injective e.injective
  apply ContinuousMonoidHom.ext
  intro g
  apply Units.ext
  apply ZMod.val_injective
  apply heζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
  let j := rationalPrimeArithmeticRestriction a p hp
  change (e ζ) ^ (rationalArithmeticCyclotomicCharacter a n hna (j g) : ZMod n).val =
    (e ζ) ^ (rationalPrimeCyclotomicCharacter p hp n g : ZMod n).val
  calc
    (e ζ) ^ (rationalArithmeticCyclotomicCharacter a n hna (j g) : ZMod n).val =
        e (ζ ^ (rationalArithmeticCyclotomicCharacter a n hna (j g) : ZMod n).val) :=
      (map_pow e _ _).symm
    _ = e ((show U ≃ₐ[ℚ] U from j g) ζ) :=
      congrArg e (rationalArithmeticCyclotomicCharacter_apply_root a n hna (j g) hζ).symm
    _ = g (e ζ) := rationalPrimeArithmeticRestriction_commutes a p hp g ζ
    _ = (e ζ) ^ (rationalPrimeCyclotomicCharacter p hp n g : ZMod n).val :=
      rationalPrimeCyclotomicCharacter_apply_root p hp n g heζ

end
end Dubon2026

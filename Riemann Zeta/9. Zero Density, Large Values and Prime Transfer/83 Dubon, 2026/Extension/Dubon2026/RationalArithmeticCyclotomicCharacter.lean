import Dubon2026.PrimitiveRootCyclotomicContinuity
import Dubon2026.RationalArithmeticGaloisGroup
import Dubon2026.UnramifiedUnionCyclotomicRoots

/-! # The genuine finite cyclotomic character of the actual arithmetic Galois group -/

namespace Dubon2026
noncomputable section
open scoped NumberField

/-- Construct the finite cyclotomic character on the original rational arithmetic
Galois group using the primitive root already proved to lie in its actual extension.
Its topology is the original Krull topology and continuity is derived. -/
def rationalArithmeticCyclotomicCharacter (a : 𝓞 ℚ) (n : ℕ) [NeZero n]
    (hna : (n : 𝓞 ℚ) ∣ a) : rationalArithmeticGaloisGroup a →ₜ* (ZMod n)ˣ := by
  let U := rationalUnramifiedExtension a
  letI : Algebra ℚ U := U.algebra'
  letI : IsGalois ℚ U := originalUnramifiedGaloisUnion_isGalois a
  have hx : ∃ μ : U, IsPrimitiveRoot μ n :=
    originalQUnramifiedUnion_exists_primitiveRoot (Ω := AlgebraicClosure ℚ) a n hna
  let μ := Classical.choose hx
  have hμ : IsPrimitiveRoot μ n := Classical.choose_spec hx
  exact ⟨hμ.autToPow ℚ, primitiveRootCyclotomicCharacter_continuous hμ⟩

/-- The constructed continuous character is the actual Galois exponent on every
primitive root in the original arithmetic extension, not a separately supplied
character or a trivial fallback. -/
theorem rationalArithmeticCyclotomicCharacter_apply_root
    (a : 𝓞 ℚ) (n : ℕ) [NeZero n] (hna : (n : 𝓞 ℚ) ∣ a)
    (g : rationalArithmeticGaloisGroup a)
    {ζ : rationalUnramifiedExtension a} (hζ : IsPrimitiveRoot ζ n) :
    (let U := rationalUnramifiedExtension a
     letI : Algebra ℚ U := U.algebra'
     (show U ≃ₐ[ℚ] U from g) ζ) =
      ζ ^ (rationalArithmeticCyclotomicCharacter a n hna g : ZMod n).val := by
  let U := rationalUnramifiedExtension a
  letI : Algebra ℚ U := U.algebra'
  have hx : ∃ μ : U, IsPrimitiveRoot μ n :=
    originalQUnramifiedUnion_exists_primitiveRoot (Ω := AlgebraicClosure ℚ) a n hna
  exact primitiveRootCyclotomicCharacter_apply_root (F := ℚ)
    (Classical.choose_spec hx) (show U ≃ₐ[ℚ] U from g) hζ

end
end Dubon2026

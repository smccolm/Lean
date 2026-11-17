import Dubon2026.ArithmeticSupportRestriction
import Dubon2026.RationalArithmeticCyclotomicCharacter

/-! DUB-17/18 -> actual CM residual construction. Enlarging the ramification
support preserves the original cyclotomic character through the proved
surjective restriction. Both characters are compared on a genuine primitive
root, so no new determinant compatibility assumption is introduced. -/
namespace Dubon2026.SourceDickson
noncomputable section
open scoped NumberField

/-- Use the original rational algebra structures on both arithmetic extensions. -/
private local instance originalSupportCyclotomicAlgebra (a : 𝓞 ℚ) :
    Algebra ℚ (rationalUnramifiedExtension a) := (rationalUnramifiedExtension a).algebra'

/-- Cyclotomic characters commute with restriction along an enlargement of the
actual ramification support. -/
theorem original_support_cyclotomic_compatibility
    (a b : 𝓞 ℚ) (hab : a ∣ b) (n : ℕ) [NeZero n]
    (hna : (n : 𝓞 ℚ) ∣ a) (hnb : (n : 𝓞 ℚ) ∣ b)
    (g : rationalArithmeticGaloisGroup b) :
    rationalArithmeticCyclotomicCharacter a n hna
        (rationalArithmeticSupportRestriction a b hab g) =
      rationalArithmeticCyclotomicCharacter b n hnb g := by
  obtain ⟨ζ, hζ⟩ := originalQUnramifiedUnion_exists_primitiveRoot
    (Ω := AlgebraicClosure ℚ) a n hna
  let e := rationalArithmeticSupportInclusion a b hab
  have heζ : IsPrimitiveRoot (e ζ) n := hζ.map_of_injective e.injective
  have ha := rationalArithmeticCyclotomicCharacter_apply_root a n hna
    (rationalArithmeticSupportRestriction a b hab g) hζ
  have hb := rationalArithmeticCyclotomicCharacter_apply_root b n hnb g heζ
  have hc := rationalArithmeticSupportRestriction_commutes a b hab g ζ
  have hpowers := (congrArg e ha).symm.trans (hc.trans hb)
  simp only [map_pow] at hpowers
  apply Units.ext
  apply ZMod.val_injective
  exact heζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) hpowers

end
end Dubon2026.SourceDickson

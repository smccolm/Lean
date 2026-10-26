import Dubon2026.SourceArithmeticSupportPowers
import Dubon2026.UnramifiedUnionCyclotomicRoots
import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter

/-! DUB-17/18 -> arithmetic automorphy -> actual fixed-determinant
deformations. Every p-power root belongs to the original arithmetic
extension of support a when p divides a. Reuse the proved support-power
inclusion, so the native p-adic cyclotomic character has its actual root
action on this same extension. -/
namespace Dubon2026
noncomputable section
open scoped NumberField

theorem sourceArithmetic_exists_primePower_root
    (a : 𝓞 ℚ) (p : ℕ) [Fact p.Prime]
    (hpa : (p : 𝓞 ℚ) ∣ a) (n : ℕ) :
    ∃ z : rationalUnramifiedExtension a, IsPrimitiveRoot z (p ^ n) := by
  letI : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
  have hdiv : ((p ^ n : ℕ) : 𝓞 ℚ) ∣ a ^ n := by
    simpa only [Nat.cast_pow] using pow_dvd_pow_of_dvd hpa n
  obtain ⟨z, hz⟩ := originalQUnramifiedUnion_exists_primitiveRoot
    (Ω := AlgebraicClosure ℚ) (a ^ n) (p ^ n) hdiv
  have hle : rationalUnramifiedExtension (a ^ n) ≤
      rationalUnramifiedExtension a :=
    sourceUnramifiedUnion_mono_dvd_pow n (dvd_refl (a ^ n))
  let j := IntermediateField.inclusion hle
  exact ⟨j z, hz.map_of_injective j.injective⟩

/-- The native continuous p-adic cyclotomic character on the original arithmetic group. -/
def sourceArithmeticPadicCyclotomicCharacter
    (a : 𝓞 ℚ) (p : ℕ) [Fact p.Prime] :
    rationalArithmeticGaloisGroup a →ₜ* ℤ_[p]ˣ := by
  let U := rationalUnramifiedExtension a
  letI : Algebra ℚ U := U.algebra'
  exact ⟨(cyclotomicCharacter U p).comp
    (MulSemiringAction.toRingAut Gal(U/ℚ) U),
    cyclotomicCharacter.continuous p ℚ U⟩

theorem sourceArithmeticPadicCyclotomicCharacter_root
    (a : 𝓞 ℚ) (p : ℕ) [Fact p.Prime]
    (hpa : (p : 𝓞 ℚ) ∣ a)
    (g : rationalArithmeticGaloisGroup a) (n : ℕ)
    (z : rationalUnramifiedExtension a) (hz : z ^ p ^ n = 1) :
    (show rationalUnramifiedExtension a ≃ₐ[ℚ]
      rationalUnramifiedExtension a from g) z =
      z ^ ((sourceArithmeticPadicCyclotomicCharacter a p g : ℤ_[p]).toZModPow n).val := by
  let U := rationalUnramifiedExtension a
  letI : Algebra ℚ U := U.algebra'
  letI (i : ℕ) : HasEnoughRootsOfUnity U (p ^ i) :=
    ⟨sourceArithmetic_exists_primePower_root a p hpa i, rootsOfUnity.isCyclic _ _⟩
  exact cyclotomicCharacter.spec p (show U ≃ₐ[ℚ] U from g).toRingEquiv z hz

end
end Dubon2026

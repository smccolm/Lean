import Dubon2026.SourceArithmeticPadicCyclotomic
import Dubon2026.SourcePadicWittCoefficient
import Dubon2026.RationalArithmeticCyclotomicCharacter

/-! DUB-17/18 -> arithmetic automorphy -> actual determinant lift.
The native p-adic character reduces to the existing original finite
cyclotomic character by their actions on the same primitive root. -/
namespace Dubon2026
noncomputable section
open scoped NumberField

theorem sourcePadicInt_toZMod_from_pow_one
    (p : ℕ) [Fact p.Prime] (x : ℤ_[p]) :
    PadicInt.toZMod x =
      ZMod.castHom (show p ∣ p ^ 1 by simp) (ZMod p) (x.toZModPow 1) := by
  have he := sourcePadicInt_charP_map p
    ((ZMod.castHom (show p ∣ p ^ 1 by simp) (ZMod p)).comp
      (PadicInt.toZModPow 1)) x
  simpa only [RingHom.comp_apply, ZMod.castHom_apply, ZMod.cast_id] using he.symm

theorem sourceArithmeticPadicCyclotomicCharacter_reduction
    (a : 𝓞 ℚ) (p : ℕ) [Fact p.Prime] [NeZero p]
    (hpa : (p : 𝓞 ℚ) ∣ a)
    (g : rationalArithmeticGaloisGroup a) :
    PadicInt.toZMod (sourceArithmeticPadicCyclotomicCharacter a p g : ℤ_[p]) =
      (rationalArithmeticCyclotomicCharacter a p hpa g : ZMod p) := by
  let U := rationalUnramifiedExtension a
  letI : Algebra ℚ U := U.algebra'
  obtain ⟨z, hz⟩ := originalQUnramifiedUnion_exists_primitiveRoot
    (Ω := AlgebraicClosure ℚ) a p hpa
  have hpadic := sourceArithmeticPadicCyclotomicCharacter_root a p hpa g 1 z
    (by simpa only [pow_one] using hz.pow_eq_one)
  have hfinite := rationalArithmeticCyclotomicCharacter_apply_root a p hpa g hz
  rw [sourcePadicInt_toZMod_from_pow_one]
  apply ZMod.val_injective
  apply hz.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
  have hcast :
      (ZMod.castHom (show p ∣ p ^ 1 by simp) (ZMod p)
        ((sourceArithmeticPadicCyclotomicCharacter a p g : ℤ_[p]).toZModPow 1)).val =
      ((sourceArithmeticPadicCyclotomicCharacter a p g : ℤ_[p]).toZModPow 1).val := by
    rw [ZMod.castHom_apply]
    apply ZMod.val_cast_eq_val_of_lt
    simpa only [pow_one] using
      (ZMod.val_lt ((sourceArithmeticPadicCyclotomicCharacter a p g : ℤ_[p]).toZModPow 1))
  rw [hcast, ← hpadic]
  exact hfinite

end
end Dubon2026

import Dubon2026.ArithmeticCyclotomicCharacterSurjective

/-! DUB-17/18 -> original auxiliary-prime detection -> a nontrivial squared
cyclotomic scalar in the actual original coefficient field. Reuse native
surjectivity of the actual arithmetic root action. -/
namespace Dubon2026
noncomputable section
open scoped NumberField

/-- The actual arithmetic cyclotomic coefficient character has a nontrivial
squared value in every original coefficient field of characteristic p > 3. -/
theorem originalArithmeticCyclotomicCoefficient_exists_square_ne_one
    (a : 𝓞 ℚ) (p : ℕ) [Fact p.Prime] (hpa : (p : 𝓞 ℚ) ∣ a)
    (F : Type) [Field F] [CharP F p] [TopologicalSpace F] (hp3 : 3 < p) :
    ∃ g : rationalArithmeticGaloisGroup a,
      rationalArithmeticCyclotomicCoefficientCharacter a p hpa F g ^ 2 ≠ 1 := by
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hle := Nat.le_of_dvd (by decide : 0 < 2)
      ((CharP.cast_eq_zero_iff (ZMod p) p 2).mp hz)
    omega
  obtain ⟨g, hg⟩ := rationalArithmeticCyclotomicCharacter_surjective a p hpa
    (Units.mk0 2 htwo)
  refine ⟨g, ?_⟩
  have he : rationalArithmeticCyclotomicCoefficientCharacter a p hpa F g = 2 := by
    change ZMod.castHom (dvd_refl p) F
      (rationalArithmeticCyclotomicCharacter a p hpa g : ZMod p) = 2
    rw [hg]
    change (ZMod.castHom (dvd_refl p) F) (2 : ZMod p) = (2 : F)
    exact map_ofNat (ZMod.castHom (dvd_refl p) F) 2
  rw [he]
  intro hs
  have hz : (3 : F) = 0 := by linear_combination hs
  have hle := Nat.le_of_dvd (by decide : 0 < 3)
    ((CharP.cast_eq_zero_iff F p 3).mp hz)
  omega

end
end Dubon2026

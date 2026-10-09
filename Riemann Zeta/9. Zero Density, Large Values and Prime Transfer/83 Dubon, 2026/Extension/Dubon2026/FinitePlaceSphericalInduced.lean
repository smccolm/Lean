import Dubon2026.IwasawaInducedSection
import Dubon2026.FinitePlaceGL2Iwasawa
import Dubon2026.GL2LowerDiagonalCharacter
import Dubon2026.FinitePlaceLevelTopology

/-! # The actual original local unramified induced space and its genuine spherical section -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

/-- The actual smooth local induction from the original lower Borel and its genuine unramified diagonal characters. -/
abbrev FinitePlaceInducedSpace (v : HeightOneSpectrum ℤ) (z₁ z₂ : ℂˣ) :=
  smoothInducedCharacterSpace (gl2UpperZeroSubgroup (v.adicCompletion ℚ))
    (finitePlaceLowerCharacter v z₁ z₂)

/-- The genuine normalized spherical section in the actual original smooth induced function space. -/
def finitePlaceInducedSpherical (v : HeightOneSpectrum ℤ) (z₁ z₂ : ℂˣ) :
    FinitePlaceInducedSpace v z₁ z₂ :=
  iwasawaInducedSection _ _ (finitePlaceLowerCharacter v z₁ z₂) (finitePlaceGL2_iwasawa v)
    (finitePlaceGL2Gamma0_isOpen 1 v) (finitePlaceLowerCharacter_integral v z₁ z₂)

/-- The original spherical section has value one at the actual identity matrix. -/
theorem finitePlaceInducedSpherical_one (v : HeightOneSpectrum ℤ) (z₁ z₂ : ℂˣ) :
    (finitePlaceInducedSpherical v z₁ z₂).val 1 = 1 :=
  iwasawaInducedSection_one _ _ _ _ _ _

/-- The genuine spherical section is a nonzero vector in the actual local induced space. -/
theorem finitePlaceInducedSpherical_ne_zero (v : HeightOneSpectrum ℤ) (z₁ z₂ : ℂˣ) :
    finitePlaceInducedSpherical v z₁ z₂ ≠ 0 := by
  intro hz
  have he := finitePlaceInducedSpherical_one v z₁ z₂
  rw [hz] at he
  exact zero_ne_one he

/-- The original integral local group fixes the actual spherical section at every original matrix argument. -/
theorem finitePlaceInducedSpherical_fixed (v : HeightOneSpectrum ℤ) (z₁ z₂ : ℂˣ)
    (k : finitePlaceGL2Gamma0 1 v) :
    smoothInducedCharacterRepresentation _ (finitePlaceLowerCharacter v z₁ z₂)
      k.val (finitePlaceInducedSpherical v z₁ z₂) = finitePlaceInducedSpherical v z₁ z₂ := by
  apply Subtype.ext
  funext g
  obtain ⟨b, j, rfl⟩ := finitePlaceGL2_iwasawa v g
  change (finitePlaceInducedSpherical v z₁ z₂).val ((b.val * j.val) * k.val) =
    (finitePlaceInducedSpherical v z₁ z₂).val (b.val * j.val)
  have he : (b.val * j.val) * k.val = b.val * (j * k).val := mul_assoc _ _ _
  rw [he]
  exact (iwasawaInducedSection_mul _ _ _ _ _ _ b (j * k)).trans
    (iwasawaInducedSection_mul _ _ _ _ _ _ b j).symm

/-- Every actual integral-fixed vector of the genuine induced representation is its identity value times the original normalized spherical section. -/
theorem finitePlaceInducedSpherical_fixed_line (v : HeightOneSpectrum ℤ) (z₁ z₂ : ℂˣ)
    (f : FinitePlaceInducedSpace v z₁ z₂)
    (hf : ∀ k : finitePlaceGL2Gamma0 1 v,
      smoothInducedCharacterRepresentation _ (finitePlaceLowerCharacter v z₁ z₂) k.val f = f) :
    f = f.val 1 • finitePlaceInducedSpherical v z₁ z₂ :=
  iwasawaInducedSection_fixed_line _ _ _ _ _ _ f hf

end
end Dubon2026

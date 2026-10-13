import Dubon2026.OriginalKummerGaloisFinite

/-! # The actual pairing of original power classes with original automorphisms

The two variables multiply by the original field laws. Independence of
the chosen roots and representatives uses the already proved equality of
ratios for equal field power classes. This finite pairing will calculate
the S-unit Kummer degree needed by DUB-17's global norm-index route.
-/

namespace Dubon2026
noncomputable section
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]

/-- The original radical class defines its actual Galois ratio character. -/
def originalKummerClassCharacter (n : ℕ) (hn : 0 < n)
    (hζ : (primitiveRoots n K).Nonempty) (Δ : Subgroup Kˣ)
    (c : originalKummerClassSubgroup n Δ) :
    Gal(originalKummerRadicalField (Ω := Ω) n Δ/K) →*
      (originalKummerRadicalField (Ω := Ω) n Δ)ˣ := by
  letI : NeZero n := ⟨hn.ne'⟩
  exact galoisRadicalRatioHom n hζ (originalKummerClassRepresentative n Δ c).val
    (originalKummerClassRoot n hn Δ c) (originalKummerClassRoot_pow n hn Δ c)

/-- Multiplication of the original power classes multiplies their original ratio characters. -/
theorem originalKummerClassCharacter_mul (n : ℕ) (hn : 0 < n)
    (hζ : (primitiveRoots n K).Nonempty) (Δ : Subgroup Kˣ)
    (c d : originalKummerClassSubgroup n Δ) :
    originalKummerClassCharacter (Ω := Ω) n hn hζ Δ (c * d) =
      originalKummerClassCharacter n hn hζ Δ c *
        originalKummerClassCharacter n hn hζ Δ d := by
  letI : NeZero n := ⟨hn.ne'⟩
  apply MonoidHom.ext
  intro g
  have hpow : (originalKummerClassRoot (Ω := Ω) n hn Δ c *
      originalKummerClassRoot n hn Δ d) ^ n =
      Units.map (algebraMap K (originalKummerRadicalField (Ω := Ω) n Δ)).toMonoidHom
        ((originalKummerClassRepresentative n Δ c).val *
          (originalKummerClassRepresentative n Δ d).val) := by
    rw [mul_pow, originalKummerClassRoot_pow, originalKummerClassRoot_pow, map_mul]
  have hclass : QuotientGroup.mk' (powMonoidHom (α := Kˣ) n).range
      (originalKummerClassRepresentative n Δ (c * d)).val =
      QuotientGroup.mk' _ ((originalKummerClassRepresentative n Δ c).val *
        (originalKummerClassRepresentative n Δ d).val) := by
    rw [map_mul, originalKummerClassRepresentative_spec,
      originalKummerClassRepresentative_spec, originalKummerClassRepresentative_spec]
    rfl
  have h := galois_radical_ratios_eq_of_power_class n hζ
    (originalKummerClassRepresentative n Δ (c * d)).val
    ((originalKummerClassRepresentative n Δ c).val *
      (originalKummerClassRepresentative n Δ d).val)
    (originalKummerClassRoot (Ω := Ω) n hn Δ (c * d))
    (originalKummerClassRoot n hn Δ c * originalKummerClassRoot n hn Δ d)
    (originalKummerClassRoot_pow n hn Δ (c * d)) hpow hclass g
  change g • originalKummerClassRoot n hn Δ (c * d) /
    originalKummerClassRoot n hn Δ (c * d) = _
  rw [h, smul_mul', mul_div_mul_comm]
  rfl

/-- The actual original radical pairing is a homomorphism in the original class variable. -/
def originalKummerClassPairing (n : ℕ) (hn : 0 < n)
    (hζ : (primitiveRoots n K).Nonempty) (Δ : Subgroup Kˣ) :
    originalKummerClassSubgroup n Δ →*
      (Gal(originalKummerRadicalField (Ω := Ω) n Δ/K) →*
        (originalKummerRadicalField (Ω := Ω) n Δ)ˣ) :=
  MonoidHom.mk' (originalKummerClassCharacter n hn hζ Δ)
    (originalKummerClassCharacter_mul n hn hζ Δ)

end
end Dubon2026

import Dubon2026.SmoothInducedCharacter

/-! # The actual normalized spherical section of a smooth induced character -/

namespace Dubon2026

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (B K : Subgroup G) (χ : B →* ℂ)
    (hdec : ∀ g : G, ∃ b : B, ∃ k : K, g = b.val * k.val)

/-- The value of the inducing character on the actual subgroup component of an Iwasawa factorization. -/
def iwasawaInducedSectionValue (g : G) : ℂ := χ (hdec g).choose

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Triviality on the genuine subgroup intersection makes the inducing value independent of the chosen original factorization. -/
theorem iwasawaInducedSectionValue_mul
    (hχ : ∀ b : B, b.val ∈ K → χ b = 1) (b : B) (k : K) :
    iwasawaInducedSectionValue B K χ hdec (b.val * k.val) = χ b := by
  let b' : B := (hdec (b.val * k.val)).choose
  let k' : K := (hdec (b.val * k.val)).choose_spec.choose
  have he : b'.val * k'.val = b.val * k.val :=
    (hdec (b.val * k.val)).choose_spec.choose_spec.symm
  have hs : b.val⁻¹ * b'.val = k.val * k'.val⁻¹ := by
    calc
      _ = b.val⁻¹ * (b'.val * k'.val) * k'.val⁻¹ := by simp [mul_assoc]
      _ = _ := by rw [he]; simp
  have hk : (b⁻¹ * b').val ∈ K := by
    change b.val⁻¹ * b'.val ∈ K
    rw [hs]
    exact K.mul_mem k.property (K.inv_mem k'.property)
  change χ b' = χ b
  calc
    χ b' = χ (b * (b⁻¹ * b')) := by rw [mul_inv_cancel_left]
    _ = χ b * χ (b⁻¹ * b') := map_mul χ _ _
    _ = χ b := by rw [hχ _ hk, mul_one]

/-- The genuine spherical section belongs to the actual smooth induced space; its normalization comes from the original identity value. -/
def iwasawaInducedSection (hK : IsOpen (K : Set G))
    (hχ : ∀ b : B, b.val ∈ K → χ b = 1) : smoothInducedCharacterSpace B χ := by
  refine ⟨iwasawaInducedSectionValue B K χ hdec, ?_, K, hK, ?_⟩
  · intro a g
    obtain ⟨b, k, rfl⟩ := hdec g
    have he : a.val * (b.val * k.val) = (a * b).val * k.val := mul_assoc _ _ _ |>.symm
    rw [he, iwasawaInducedSectionValue_mul B K χ hdec hχ,
      iwasawaInducedSectionValue_mul B K χ hdec hχ, map_mul]
  · intro h hh g
    obtain ⟨b, k, rfl⟩ := hdec g
    have he : (b.val * k.val) * h = b.val * (k * (⟨h, hh⟩ : K)).val := mul_assoc _ _ _
    rw [he, iwasawaInducedSectionValue_mul B K χ hdec hχ,
      iwasawaInducedSectionValue_mul B K χ hdec hχ]

omit [IsTopologicalGroup G] in
/-- The actual spherical section has the literal inducing value on every original Iwasawa pair. -/
theorem iwasawaInducedSection_mul (hK : IsOpen (K : Set G))
    (hχ : ∀ b : B, b.val ∈ K → χ b = 1) (b : B) (k : K) :
    (iwasawaInducedSection B K χ hdec hK hχ).val (b.val * k.val) = χ b :=
  iwasawaInducedSectionValue_mul B K χ hdec hχ b k

omit [IsTopologicalGroup G] in
/-- The original identity value of the genuine spherical section is exactly one. -/
theorem iwasawaInducedSection_one (hK : IsOpen (K : Set G))
    (hχ : ∀ b : B, b.val ∈ K → χ b = 1) :
    (iwasawaInducedSection B K χ hdec hK hχ).val 1 = 1 := by
  simpa only [Subgroup.coe_one, one_mul, map_one] using
    iwasawaInducedSection_mul B K χ hdec hK hχ 1 1

/-- Every actual fixed induced vector lies on the original normalized spherical line. -/
theorem iwasawaInducedSection_fixed_line (hK : IsOpen (K : Set G))
    (hχ : ∀ b : B, b.val ∈ K → χ b = 1)
    (f : smoothInducedCharacterSpace B χ)
    (hf : ∀ k : K, smoothInducedCharacterRepresentation B χ k.val f = f) :
    f = f.val 1 • iwasawaInducedSection B K χ hdec hK hχ := by
  apply Subtype.ext
  funext g
  obtain ⟨b, k, rfl⟩ := hdec g
  change f.val (b.val * k.val) = f.val 1 * (iwasawaInducedSection B K χ hdec hK hχ).val (b.val * k.val)
  rw [smoothInducedCharacter_fixed_value B K χ f hf, iwasawaInducedSection_mul, mul_comm]

end
end Dubon2026

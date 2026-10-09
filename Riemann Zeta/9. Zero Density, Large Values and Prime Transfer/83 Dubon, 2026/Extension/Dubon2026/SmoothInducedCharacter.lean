import Dubon2026.RepresentationScalarTwist
import Mathlib.Topology.Algebra.Group.Basic

/-! # The actual smooth induced representation of a subgroup character -/

namespace Dubon2026

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Genuine subgroup-covariant functions whose right-translation stabilizer contains an open subgroup. The inducing character includes any desired normalization factor explicitly. -/
def smoothInducedCharacterSpace (B : Subgroup G) (χ : B →* ℂ) : Submodule ℂ (G → ℂ) where
  carrier f := (∀ b : B, ∀ g : G, f (b.val * g) = χ b * f g) ∧
    ∃ H : Subgroup G, IsOpen (H : Set G) ∧ ∀ h ∈ H, ∀ g, f (g * h) = f g
  zero_mem' := ⟨by simp, ⊤, isOpen_univ, by simp⟩
  add_mem' := by
    rintro f j ⟨hf, H, hH, hfi⟩ ⟨hj, J, hJ, hji⟩
    refine ⟨?_, H ⊓ J, hH.inter hJ, ?_⟩
    · intro b g
      change f (b.val * g) + j (b.val * g) = χ b * (f g + j g)
      rw [hf, hj, mul_add]
    · intro h hh g
      change f (g * h) + j (g * h) = f g + j g
      rw [hfi h hh.1, hji h hh.2]
  smul_mem' := by
    rintro c f ⟨hf, H, hH, hfi⟩
    refine ⟨?_, H, hH, ?_⟩
    · intro b g
      change c * f (b.val * g) = χ b * (c * f g)
      rw [hf]
      ring
    · intro h hh g
      change c * f (g * h) = c * f g
      rw [hfi h hh]

/-- Right translation preserves the actual smooth induced function space. -/
theorem smoothInducedCharacterSpace_translate (B : Subgroup G) (χ : B →* ℂ)
    (f : smoothInducedCharacterSpace B χ) (a : G) :
    (fun g => f.val (g * a)) ∈ smoothInducedCharacterSpace B χ := by
  obtain ⟨hf, H, hH, hi⟩ := f.property
  refine ⟨?_, H.comap (MulAut.conj a⁻¹).toMonoidHom, ?_, ?_⟩
  · intro b g
    simpa only [mul_assoc] using hf b (g * a)
  · exact hH.preimage (continuous_const.mul continuous_id |>.mul continuous_const)
  · intro h hh g
    change a⁻¹ * h * (a⁻¹)⁻¹ ∈ H at hh
    rw [inv_inv] at hh
    have he := hi (a⁻¹ * h * a) hh (g * a)
    simpa only [mul_assoc, mul_inv_cancel_left] using he

/-- The literal right-translation action on the genuine smooth induced character space. -/
def smoothInducedCharacterRepresentation (B : Subgroup G) (χ : B →* ℂ) :
    Representation ℂ G (smoothInducedCharacterSpace B χ) where
  toFun a :=
    { toFun f := ⟨fun g => f.val (g * a), smoothInducedCharacterSpace_translate B χ f a⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  map_one' := by
    ext f g
    change f.val (g * 1) = f.val g
    rw [mul_one]
  map_mul' a b := by
    ext f g
    change f.val (g * (a * b)) = f.val ((g * a) * b)
    rw [mul_assoc]

/-- The constructed representation uses the actual right translate of each original function. -/
theorem smoothInducedCharacterRepresentation_apply (B : Subgroup G) (χ : B →* ℂ)
    (a g : G) (f : smoothInducedCharacterSpace B χ) :
    (smoothInducedCharacterRepresentation B χ a f).val g = f.val (g * a) := rfl

/-- Every vector of the actual induced representation has a genuine open stabilizer. -/
theorem smoothInducedCharacterRepresentation_smooth (B : Subgroup G) (χ : B →* ℂ)
    (f : smoothInducedCharacterSpace B χ) :
    ∃ H : Subgroup G, IsOpen (H : Set G) ∧
      ∀ h ∈ H, smoothInducedCharacterRepresentation B χ h f = f := by
  obtain ⟨H, hH, hi⟩ := f.property.2
  refine ⟨H, hH, ?_⟩
  intro h hh
  apply Subtype.ext
  funext g
  exact hi h hh g

/-- Under an actual subgroup factorization, every genuinely compact-subgroup-fixed induced function is determined by its original identity value. -/
theorem smoothInducedCharacter_fixed_value (B K : Subgroup G) (χ : B →* ℂ)
    (f : smoothInducedCharacterSpace B χ)
    (hf : ∀ k : K, smoothInducedCharacterRepresentation B χ k.val f = f)
    (b : B) (k : K) : f.val (b.val * k.val) = χ b * f.val 1 := by
  rw [f.property.1]
  have he := congrArg (fun j : smoothInducedCharacterSpace B χ => j.val 1) (hf k)
  change f.val (1 * k.val) = f.val 1 at he
  rw [one_mul] at he
  rw [he]

end
end Dubon2026

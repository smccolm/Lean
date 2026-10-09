import Dubon2026.SmoothInducedCharacter
import Mathlib.RepresentationTheory.Irreducible

/-! # The genuine coefficient map into smooth character induction -/

namespace Dubon2026

noncomputable section

variable {G V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (B : Subgroup G) (χ : B →* ℂ)
    (hρ : ∀ x : V, ∃ H : Subgroup G, IsOpen (H : Set G) ∧ ∀ h ∈ H, ρ h x = x)
    (ℓ : V →ₗ[ℂ] ℂ) (hℓ : ∀ b : B, ∀ x : V, ℓ (ρ b.val x) = χ b * ℓ x)

/-- A genuine Borel eigenfunctional gives the actual coefficient-function intertwiner into the smooth induced representation. Its covariance and open stabilizers are derived from the original action. -/
def smoothInducedFrobeniusMap
    (hρ : ∀ x : V, ∃ H : Subgroup G, IsOpen (H : Set G) ∧ ∀ h ∈ H, ρ h x = x)
    (ℓ : V →ₗ[ℂ] ℂ) (hℓ : ∀ b : B, ∀ x : V, ℓ (ρ b.val x) = χ b * ℓ x) :
    Representation.IntertwiningMap ρ (smoothInducedCharacterRepresentation B χ) where
  toLinearMap :=
    { toFun x := ⟨fun g => ℓ (ρ g x), by
        constructor
        · intro b g
          change ℓ (ρ (b.val * g) x) = χ b * ℓ (ρ g x)
          rw [map_mul, Module.End.mul_apply, hℓ]
        · obtain ⟨H, hH, hx⟩ := hρ x
          refine ⟨H, hH, ?_⟩
          intro h hh g
          change ℓ (ρ (g * h) x) = ℓ (ρ g x)
          rw [map_mul, Module.End.mul_apply, hx h hh]⟩
      map_add' x y := by
        apply Subtype.ext
        funext g
        change ℓ (ρ g (x + y)) = ℓ (ρ g x) + ℓ (ρ g y)
        rw [map_add, map_add]
      map_smul' c x := by
        apply Subtype.ext
        funext g
        change ℓ (ρ g (c • x)) = c • ℓ (ρ g x)
        rw [map_smul, map_smul] }
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    funext a
    change ℓ (ρ a (ρ g x)) = ℓ (ρ (a * g) x)
    rw [map_mul, Module.End.mul_apply]

/-- The genuine induced coefficient map is the literal original matrix coefficient at every group element. -/
theorem smoothInducedFrobeniusMap_apply (x : V) (g : G) :
    (smoothInducedFrobeniusMap ρ B χ hρ ℓ hℓ x).val g = ℓ (ρ g x) := rfl

/-- Evaluation at the actual identity recovers the original eigenfunctional exactly. -/
theorem smoothInducedFrobeniusMap_one (x : V) :
    (smoothInducedFrobeniusMap ρ B χ hρ ℓ hℓ x).val 1 = ℓ x := by
  rw [smoothInducedFrobeniusMap_apply, map_one, Module.End.one_apply]

/-- For an actual irreducible smooth representation, a nonzero original Borel eigenfunctional gives an injective genuine induced coefficient map. -/
theorem smoothInducedFrobeniusMap_injective [ρ.IsIrreducible] (hne : ℓ ≠ 0) :
    Function.Injective (smoothInducedFrobeniusMap ρ B χ hρ ℓ hℓ) := by
  apply (Representation.IsIrreducible.injective_or_eq_zero
    (smoothInducedFrobeniusMap ρ B χ hρ ℓ hℓ)).resolve_right
  intro hz
  apply hne
  apply LinearMap.ext
  intro x
  have he := smoothInducedFrobeniusMap_one ρ B χ hρ ℓ hℓ x
  rw [hz] at he
  exact he.symm

omit hρ ℓ hℓ in
/-- Every genuine intertwiner into the original smooth induced representation is determined by its original identity evaluation. -/
theorem smoothInduced_intertwiner_coefficient
    (T : Representation.IntertwiningMap ρ (smoothInducedCharacterRepresentation B χ))
    (x : V) (g : G) : (T x).val g = (T (ρ g x)).val 1 := by
  have he := Representation.IntertwiningMap.isIntertwining ρ
    (smoothInducedCharacterRepresentation B χ) T g x
  have hh := congrArg (fun f : smoothInducedCharacterSpace B χ => f.val 1) he
  change (T (ρ g x)).val 1 = (T x).val (1 * g) at hh
  simpa only [one_mul] using hh.symm

end
end Dubon2026

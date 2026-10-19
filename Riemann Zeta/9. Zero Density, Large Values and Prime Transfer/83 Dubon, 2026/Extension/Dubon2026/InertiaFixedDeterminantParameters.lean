import Dubon2026.InertiaCharacterAugmentationComparison
import Dubon2026.FixedDeterminantCharacterParameters

/-! The actual inertia determinant removes the last scalar parameter,
retaining the exact unramified augmentation quotient. This gives the
fixed-determinant number of auxiliary parameters required by the
arithmetic patching dependency of Dubon Theorem 2.6. -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G D A : Type*} [Group G] [Group D] [CommRing A] {n : ℕ}

/-- A trivial determinant on the original inertia representation forces
the product of its actual labelled quotient characters to be one. -/
theorem inertiaCharacter_product_eq_one
    (ρ : G →* GeneralLinearGroup (Fin (n + 1)) A) (I : Subgroup G) (π : G →* D)
    (W : GeneralLinearGroup (Fin (n + 1)) A) (κ : D →* (Fin (n + 1) → A)ˣ)
    (hκ : ∀ g ∈ I, diagonal (κ (π g)).val = (MulAut.conj W (ρ g)).val)
    (hs : ∀ d, ∃ g ∈ I, π g = d)
    (hdet : ∀ g ∈ I, GeneralLinearGroup.det (ρ g) = 1) :
    ∀ d, ∏ i, (κ d).val i = 1 := by
  let Dm := Units.map (diagonalRingHom (Fin (n + 1)) A).toMonoidHom
  intro d
  obtain ⟨g, hg, rfl⟩ := hs d
  have he : Dm (κ (π g)) = MulAut.conj W (ρ g) := Units.ext (hκ g hg)
  have hd := congrArg GeneralLinearGroup.det he
  simp only [MulAut.conj_apply, map_mul, map_inv, hdet g hg, mul_one, mul_inv_cancel] at hd
  have hv := congrArg Units.val hd
  change (diagonal (κ (π g)).val).det = 1 at hv
  simpa only [det_diagonal] using hv

/-- The n retained scalar parameters for an actual rank n+1 inertia lift
have exactly its original unramified matrix relation ideal. -/
theorem inertiaCharacter_fixedDeterminant_augmentationIdeal_eq
    (O : Type*) [CommRing O] [Algebra O A]
    (ρ : G →* GeneralLinearGroup (Fin (n + 1)) A) (I : Subgroup G) (π : G →* D)
    (W : GeneralLinearGroup (Fin (n + 1)) A) (κ : D →* (Fin (n + 1) → A)ˣ)
    (hκ : ∀ g ∈ I, diagonal (κ (π g)).val = (MulAut.conj W (ρ g)).val)
    (hs : ∀ d, ∃ g ∈ I, π g = d)
    (hdet : ∀ g ∈ I, GeneralLinearGroup.det (ρ g) = 1) :
    auxiliaryCharacterAugmentationIdeal O (auxiliaryInitialCharacters κ) =
      matrixRepresentationRelationIdeal ρ I :=
  (auxiliaryInitialCharacters_augmentationIdeal_eq O κ
    (inertiaCharacter_product_eq_one ρ I π W κ hκ hs hdet)).trans
      (inertiaCharacter_augmentationIdeal_eq O ρ I π W κ hκ hs)

end
end Dubon2026

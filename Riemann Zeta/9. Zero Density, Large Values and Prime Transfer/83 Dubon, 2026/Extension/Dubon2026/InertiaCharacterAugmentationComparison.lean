import Dubon2026.AuxiliaryCharacterAugmentation
import Dubon2026.MatrixRepresentationRelationIdeals

/-! The actual matrix ideal imposing unramifiedness equals the image of
the literal augmentation ideal under the inertia character map. This
identifies the two coefficient quotients required by the auxiliary local
deformation comparison on the Dubon Theorem 2.6 patching chain. -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G D ι A B : Type*} [Group G] [Group D] [Fintype ι] [DecidableEq ι]
  [CommRing A] [CommRing B]

/-- A surjective diagonal inertia presentation identifies the exact
unramifiedness condition after every original coefficient change. -/
theorem inertiaCharacter_coefficient_kernel_iff
    (ρ : G →* GeneralLinearGroup ι A) (I : Subgroup G) (π : G →* D)
    (W : GeneralLinearGroup ι A) (κ : D →* (ι → A)ˣ)
    (hκ : ∀ g ∈ I, diagonal (κ (π g)).val = (MulAut.conj W (ρ g)).val)
    (hs : ∀ d, ∃ g ∈ I, π g = d) (f : A →+* B) :
    I ≤ ((GeneralLinearGroup.map f).comp ρ).ker ↔
      ∀ d i, f ((κ d).val i) = 1 := by
  let Dm := Units.map (diagonalRingHom ι A).toMonoidHom
  have he (g) (hg : g ∈ I) : Dm (κ (π g)) = MulAut.conj W (ρ g) := Units.ext (hκ g hg)
  constructor
  · intro h d i
    obtain ⟨g, hg, rfl⟩ := hs d
    have hm := congrArg (GeneralLinearGroup.map f) (he g hg)
    have hz : GeneralLinearGroup.map f (ρ g) = 1 := h hg
    simp only [MulAut.conj_apply, map_mul, map_inv, hz, mul_one, mul_inv_cancel] at hm
    have hi := congrArg (fun M : GeneralLinearGroup ι B => M.val i i) hm
    simpa [Dm] using hi
  · intro h g hg
    have hz : GeneralLinearGroup.map f (Dm (κ (π g))) = 1 := by
      apply Units.ext
      ext i j
      by_cases hij : i = j
      · subst j
        simpa [Dm] using h (π g) i
      · simp [Dm, hij]
    rw [he g hg] at hz
    apply (MulAut.conj (GeneralLinearGroup.map f W)).injective
    simpa only [MulAut.conj_apply, map_mul, map_inv, map_one, mul_one, mul_inv_cancel] using hz

/-- The literal augmentation specialization is exactly the original
matrix relation quotient imposing unramified inertia. -/
theorem inertiaCharacter_augmentationIdeal_eq
    (O : Type*) [CommRing O] [Algebra O A]
    (ρ : G →* GeneralLinearGroup ι A) (I : Subgroup G) (π : G →* D)
    (W : GeneralLinearGroup ι A) (κ : D →* (ι → A)ˣ)
    (hκ : ∀ g ∈ I, diagonal (κ (π g)).val = (MulAut.conj W (ρ g)).val)
    (hs : ∀ d, ∃ g ∈ I, π g = d) :
    auxiliaryCharacterAugmentationIdeal O κ = matrixRepresentationRelationIdeal ρ I := by
  let J := auxiliaryCharacterAugmentationIdeal O κ
  let K := matrixRepresentationRelationIdeal ρ I
  apply le_antisymm
  · have hk := matrixRepresentationRelationIdeal_quotient_kills ρ I
    have hc := (inertiaCharacter_coefficient_kernel_iff ρ I π W κ hκ hs
      (Ideal.Quotient.mk K)).mp hk
    have hj := (auxiliaryCharacterAugmentationIdeal_le_kernel_iff O κ
      (Ideal.Quotient.mk K)).mpr hc
    simpa only [Ideal.mk_ker] using hj
  · have hj : J ≤ RingHom.ker (Ideal.Quotient.mk J) := by rw [Ideal.mk_ker]
    have hc := (auxiliaryCharacterAugmentationIdeal_le_kernel_iff O κ
      (Ideal.Quotient.mk J)).mp hj
    have hk := (inertiaCharacter_coefficient_kernel_iff ρ I π W κ hκ hs
      (Ideal.Quotient.mk J)).mpr hc
    have hi := (matrixRepresentationRelationIdeal_le_kernel_iff ρ I
      (Ideal.Quotient.mk J)).mpr hk
    simpa only [Ideal.mk_ker] using hi

end
end Dubon2026

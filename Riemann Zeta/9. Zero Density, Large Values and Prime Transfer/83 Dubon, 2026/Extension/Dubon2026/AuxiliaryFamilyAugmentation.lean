import Dubon2026.AuxiliaryFamilyGroupAlgebra
import Dubon2026.AuxiliaryCharacterAugmentation

/-! The one augmentation ideal for the actual finite auxiliary family
has image equal to the sum of its original local augmentation images.
Consequently the already proved local inertia comparisons assemble into
the joint unramified coefficient quotient required by arithmetic patching
on the Dubon Theorem 2.6 dependency chain. -/

namespace Dubon2026
noncomputable section

variable (O : Type*) [CommRing O]
  {S ι A B : Type*} [Fintype S] [Fintype ι] [CommRing A] [Algebra O A] [CommRing B]
  {D : S → Type*} [∀ s, Group (D s)]

/-- Extend the literal augmentation ideal of the whole auxiliary group
along its actual scalar parameter map. -/
def auxiliaryFamilyAugmentationIdeal (κ : ∀ s, D s →* (ι → A)ˣ) : Ideal A :=
  Ideal.map (auxiliaryFamilyGroupAlgebra O κ).toRingHom
    (RingHom.ker (coefficientGroupAlgebraAugmentation O (∀ s, ι → D s)).toRingHom)

/-- The one family augmentation ideal is killed exactly when every
original scalar parameter at every auxiliary prime becomes one. -/
theorem auxiliaryFamilyAugmentationIdeal_le_kernel_iff
    (κ : ∀ s, D s →* (ι → A)ˣ) (f : A →+* B) :
    auxiliaryFamilyAugmentationIdeal O κ ≤ RingHom.ker f ↔
      ∀ s d i, f ((κ s d).val i) = 1 := by
  classical
  let F := auxiliaryFamilyGroupAlgebra O κ
  let ε := coefficientGroupAlgebraAugmentation O (∀ s, ι → D s)
  constructor
  · intro h s d i
    let x := MonoidAlgebra.of O (∀ s, ι → D s) (Pi.mulSingle s (Pi.mulSingle i d)) - 1
    have hx : x ∈ RingHom.ker ε.toRingHom := by
      change ε (MonoidAlgebra.of O (∀ s, ι → D s) (Pi.mulSingle s (Pi.mulSingle i d)) - 1) = 0
      rw [map_sub, coefficientGroupAlgebraAugmentation_of, map_one, sub_self]
    have hf := h (Ideal.mem_map_of_mem F.toRingHom hx)
    change f (F (MonoidAlgebra.of O (∀ s, ι → D s) (Pi.mulSingle s (Pi.mulSingle i d)) - 1)) = 0 at hf
    rw [map_sub, map_one, auxiliaryFamilyGroupAlgebra_of_single, map_sub, map_one,
      sub_eq_zero] at hf
    exact hf
  · intro h
    have he : f.comp F.toRingHom = (f.comp (algebraMap O A)).comp ε.toRingHom := by
      apply MonoidAlgebra.ringHom_ext
      · intro r
        change f (F (algebraMap O (MonoidAlgebra O (∀ s, ι → D s)) r)) =
          f (algebraMap O A (ε (algebraMap O (MonoidAlgebra O (∀ s, ι → D s)) r)))
        rw [F.commutes, ε.commutes]
        rfl
      · intro d
        change f (F (MonoidAlgebra.of O (∀ s, ι → D s) d)) =
          f (algebraMap O A (ε (MonoidAlgebra.of O (∀ s, ι → D s) d)))
        rw [auxiliaryFamilyGroupAlgebra_of, coefficientGroupAlgebraAugmentation_of,
          map_one, map_one, map_prod]
        simp only [map_prod, h, Finset.prod_const_one]
    apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    change (f.comp F.toRingHom) x = 0
    rw [he]
    change f (algebraMap O A (ε x)) = 0
    change ε x = 0 at hx
    rw [hx, map_zero, map_zero]

/-- The image of the actual family augmentation is precisely the sum
of the original individual augmentation ideals. -/
theorem auxiliaryFamilyAugmentationIdeal_eq_iSup
    (κ : ∀ s, D s →* (ι → A)ˣ) :
    auxiliaryFamilyAugmentationIdeal O κ = ⨆ s, auxiliaryCharacterAugmentationIdeal O (κ s) := by
  let J := auxiliaryFamilyAugmentationIdeal O κ
  let K := ⨆ s, auxiliaryCharacterAugmentationIdeal O (κ s)
  have hc (L : Ideal A) : J ≤ RingHom.ker (Ideal.Quotient.mk L) ↔ K ≤ RingHom.ker (Ideal.Quotient.mk L) := by
    change auxiliaryFamilyAugmentationIdeal O κ ≤ _ ↔ (⨆ s, auxiliaryCharacterAugmentationIdeal O (κ s)) ≤ _
    rw [auxiliaryFamilyAugmentationIdeal_le_kernel_iff, iSup_le_iff]
    simp_rw [auxiliaryCharacterAugmentationIdeal_le_kernel_iff]
  apply le_antisymm
  · have h : K ≤ RingHom.ker (Ideal.Quotient.mk K) := by rw [Ideal.mk_ker]
    have hj := (hc K).mpr h
    simpa only [Ideal.mk_ker] using hj
  · have h : J ≤ RingHom.ker (Ideal.Quotient.mk J) := by rw [Ideal.mk_ker]
    have hk := (hc J).mp h
    simpa only [Ideal.mk_ker] using hk

end
end Dubon2026

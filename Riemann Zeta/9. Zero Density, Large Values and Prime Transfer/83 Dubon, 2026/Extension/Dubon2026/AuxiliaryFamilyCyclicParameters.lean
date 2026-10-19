import Dubon2026.AuxiliaryFamilyAugmentation
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-! The finite cyclic auxiliary family needs one scalar parameter per
character coordinate, not one per group element. The exact span identity
is the input for a uniformly bounded power-series parameter algebra in
the arithmetic patching dependency for DUB-17. -/

namespace Dubon2026
noncomputable section

/-- Monoid generators of the original auxiliary groups give exactly
the scalar generators of the actual character augmentation ideal. -/
theorem auxiliaryFamilyAugmentationIdeal_eq_span_generators
    (O : Type*) [CommRing O] {S ι A : Type*}
    [Fintype S] [Fintype ι] [CommRing A] [Algebra O A]
    {D : S → Type*} [∀ s, Group (D s)]
    (κ : ∀ s, D s →* (ι → A)ˣ)
    (g : ∀ s, D s) (hg : ∀ s d, ∃ n : ℕ, g s ^ n = d) :
    auxiliaryFamilyAugmentationIdeal O κ =
      Ideal.span (Set.range fun si : S × ι => ((κ si.1 (g si.1)).val si.2) - 1) := by
  let J := auxiliaryFamilyAugmentationIdeal O κ
  let K := Ideal.span (Set.range fun si : S × ι => ((κ si.1 (g si.1)).val si.2) - 1)
  have hJ : J ≤ RingHom.ker (Ideal.Quotient.mk J) := by rw [Ideal.mk_ker]
  have hkill := (auxiliaryFamilyAugmentationIdeal_le_kernel_iff O κ (Ideal.Quotient.mk J)).mp hJ
  apply le_antisymm
  · have hK : J ≤ RingHom.ker (Ideal.Quotient.mk K) := by
      apply (auxiliaryFamilyAugmentationIdeal_le_kernel_iff O κ _).mpr
      intro s d i
      have hx : ((κ s (g s)).val i) - 1 ∈ K := Ideal.subset_span ⟨(s, i), rfl⟩
      have hv : Ideal.Quotient.mk K ((κ s (g s)).val i) = 1 := by
        have hz := (Ideal.Quotient.eq_zero_iff_mem).mpr hx
        simpa only [map_sub, map_one, sub_eq_zero] using hz
      obtain ⟨n, rfl⟩ := hg s d
      simp only [map_pow, Units.val_pow_eq_pow_val, Pi.pow_apply, hv, one_pow]
    simpa only [Ideal.mk_ker] using hK
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨s, i⟩, rfl⟩
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change Ideal.Quotient.mk J (((κ s (g s)).val i) - 1) = 0
    rw [map_sub, map_one, hkill s (g s) i, sub_self]

/-- Finite cyclicity constructs the original generators and the exact
augmentation span without assuming a scalar-generating certificate. -/
theorem auxiliaryFamilyAugmentationIdeal_exists_cyclic_generators
    (O : Type*) [CommRing O] {S ι A : Type*}
    [Fintype S] [Fintype ι] [CommRing A] [Algebra O A]
    {D : S → Type*} [∀ s, Group (D s)] [∀ s, Finite (D s)] [∀ s, IsCyclic (D s)]
    (κ : ∀ s, D s →* (ι → A)ˣ) :
    ∃ g : ∀ s, D s, (∀ s d, ∃ n : ℕ, g s ^ n = d) ∧
      auxiliaryFamilyAugmentationIdeal O κ =
        Ideal.span (Set.range fun si : S × ι => ((κ si.1 (g si.1)).val si.2) - 1) := by
  choose g hg using fun s => IsCyclic.exists_monoid_generator (α := D s)
  have hpow : ∀ s d, ∃ n : ℕ, g s ^ n = d := fun s d =>
    (Submonoid.mem_powers_iff _ _).mp (hg s d)
  exact ⟨g, hpow, auxiliaryFamilyAugmentationIdeal_eq_span_generators O κ g hpow⟩

end
end Dubon2026

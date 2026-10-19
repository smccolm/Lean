import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Ideal.Quotient.Index

/-! A fixed quotient and a bounded generating set for its kernel give
a uniform bound on maximal-ideal generators. Applied to the actual
common-parameter augmentation, this serves the uniform finite quotient
condition in DUB-17's existing arithmetic patching dependency. -/

namespace Dubon2026
noncomputable section
open IsLocalRing

/-- Lift the generators of the original base maximal ideal and add
the genuine kernel generators. Their number is uniformly bounded. -/
theorem localQuotient_exists_bounded_maximal_generators
    {R A η : Type*} [CommRing R] [IsLocalRing R] [CommRing A] [IsLocalRing A]
    [Fintype η] (f : R →+* A) (hf : Function.Surjective f)
    (v : η → R) (hker : RingHom.ker f = Ideal.span (Set.range v))
    (s : Finset A) (hs : Ideal.span (s : Set A) = maximalIdeal A) :
    ∃ t : Finset R, Ideal.span (t : Set R) = maximalIdeal R ∧
      t.card ≤ Fintype.card η + s.card := by
  classical
  letI := IsLocalHom.of_surjective f hf
  let lift : A → R := fun a => Classical.choose (hf a)
  have hlift (a : A) : f (lift a) = a := Classical.choose_spec (hf a)
  let t : Finset R := Finset.univ.image v ∪ s.image lift
  let K : Ideal R := Ideal.span (t : Set R)
  have hkernel : RingHom.ker f ≤ K := by
    rw [hker]
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    apply Ideal.subset_span
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  have hK : K ≤ maximalIdeal R := by
    apply Ideal.span_le.mpr
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      have hi : v i ∈ RingHom.ker f := hker.symm ▸ Ideal.subset_span (Set.mem_range_self i)
      exact fun hu => (hu.map f).ne_zero hi
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      have ha' : a ∈ maximalIdeal A := hs ▸ Ideal.subset_span ha
      intro hu
      apply ha'
      simpa only [hlift] using hu.map f
  have hmap : Ideal.map f K = maximalIdeal A := by
    apply le_antisymm
    · exact (Ideal.map_mono hK).trans (map_maximalIdeal_le f)
    · rw [← hs]
      apply Ideal.span_le.mpr
      intro a ha
      rw [← hlift a]
      apply Ideal.mem_map_of_mem
      apply Ideal.subset_span
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
  have hcomap := Ideal.comap_map_of_surjective f hf K
  rw [hmap, maximalIdeal_comap] at hcomap
  have hk : Ideal.comap f ⊥ ≤ K := hkernel
  have hspan : K = maximalIdeal R := by
    simpa only [sup_of_le_left hk] using hcomap.symm
  refine ⟨t, hspan, ?_⟩
  exact (Finset.card_union_le _ _).trans
    ((Nat.add_le_add (Finset.card_image_le) (Finset.card_image_le)).trans_eq (by simp))

end
end Dubon2026

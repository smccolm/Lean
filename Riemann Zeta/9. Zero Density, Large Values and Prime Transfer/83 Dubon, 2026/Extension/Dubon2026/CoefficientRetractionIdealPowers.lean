import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Ideal.Maps

/-! # Original maximal-ideal powers are reflected by a genuine coefficient retraction -/

namespace Dubon2026
noncomputable section

variable {O R : Type*} [CommRing O] [CommRing R] [IsLocalRing R] [Algebra O R]

/-- A local coefficient inclusion with a genuine retraction reflects every original maximal-ideal power, not only the first residue ideal. -/
theorem coefficientRetraction_maximalIdeal_pow_comap
    (S : Subalgebra O R) [IsLocalRing S] [IsLocalHom S.val.toRingHom]
    (f : R →ₐ[O] S) (hfix : ∀ x : S, f x = x) (n : ℕ) :
    ((IsLocalRing.maximalIdeal R) ^ n).comap S.val.toRingHom =
      (IsLocalRing.maximalIdeal S) ^ n := by
  have hsurj : Function.Surjective f := fun x => ⟨x.val, hfix x⟩
  have hfm := IsLocalRing.map_maximalIdeal_of_surjective f.toRingHom hsurj
  have hinc : (IsLocalRing.maximalIdeal S).map S.val.toRingHom ≤
      IsLocalRing.maximalIdeal R := by
    apply Ideal.map_le_iff_le_comap.mpr
    rw [IsLocalRing.maximalIdeal_comap]
  apply le_antisymm
  · intro x hx
    have hfx : f x.val ∈ ((IsLocalRing.maximalIdeal R) ^ n).map f.toRingHom :=
      Ideal.mem_map_of_mem f.toRingHom hx
    rw [Ideal.map_pow, hfm, hfix] at hfx
    exact hfx
  · apply Ideal.map_le_iff_le_comap.mp
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono hinc n

end
end Dubon2026

import Dubon2026.AuxiliaryCharacterGroupAlgebra
import Mathlib.RingTheory.Ideal.Maps

/-! The image of the literal augmentation ideal imposes exactly triviality
of all labelled inertia characters. This is the algebraic comparison
required to identify the auxiliary unramified specialization on the
Dubon Theorem 2.6 arithmetic patching dependency chain. -/

namespace Dubon2026
noncomputable section

variable (O : Type*) [CommRing O]
  {D ι A B : Type*} [Group D] [Fintype ι] [CommRing A] [Algebra O A] [CommRing B]

/-- The actual extension of the group-algebra augmentation ideal along
the scalar character parameter map. -/
def auxiliaryCharacterAugmentationIdeal (κ : D →* (ι → A)ˣ) : Ideal A :=
  Ideal.map (auxiliaryCharacterGroupAlgebra O κ).toRingHom
    (RingHom.ker (coefficientGroupAlgebraAugmentation O (ι → D)).toRingHom)

/-- Killing the actual augmentation ideal is exactly killing each
original labelled character after the given coefficient map. -/
theorem auxiliaryCharacterAugmentationIdeal_le_kernel_iff
    (κ : D →* (ι → A)ˣ) (f : A →+* B) :
    auxiliaryCharacterAugmentationIdeal O κ ≤ RingHom.ker f ↔
      ∀ d i, f ((κ d).val i) = 1 := by
  classical
  let F := auxiliaryCharacterGroupAlgebra O κ
  let ε := coefficientGroupAlgebraAugmentation O (ι → D)
  constructor
  · intro h d i
    let x := MonoidAlgebra.of O (ι → D) (Pi.mulSingle i d) - 1
    have hx : x ∈ RingHom.ker ε.toRingHom := by
      change ε (MonoidAlgebra.of O (ι → D) (Pi.mulSingle i d) - 1) = 0
      rw [map_sub, coefficientGroupAlgebraAugmentation_of, map_one, sub_self]
    have hf := h (Ideal.mem_map_of_mem F.toRingHom hx)
    change f (F (MonoidAlgebra.of O (ι → D) (Pi.mulSingle i d) - 1)) = 0 at hf
    rw [map_sub, map_one, auxiliaryCharacterGroupAlgebra_of_single, map_sub, map_one,
      sub_eq_zero] at hf
    exact hf
  · intro h
    have he : f.comp F.toRingHom = (f.comp (algebraMap O A)).comp ε.toRingHom := by
      apply MonoidAlgebra.ringHom_ext
      · intro r
        change f (F (algebraMap O (MonoidAlgebra O (ι → D)) r)) =
          f (algebraMap O A (ε (algebraMap O (MonoidAlgebra O (ι → D)) r)))
        rw [F.commutes, ε.commutes]
        rfl
      · intro d
        change f (F (MonoidAlgebra.of O (ι → D) d)) =
          f (algebraMap O A (ε (MonoidAlgebra.of O (ι → D) d)))
        rw [auxiliaryCharacterGroupAlgebra_of, coefficientGroupAlgebraAugmentation_of,
          map_one, map_one, map_prod]
        simp only [h, Finset.prod_const_one]
    apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    change (f.comp F.toRingHom) x = 0
    rw [he]
    change f (algebraMap O A (ε x)) = 0
    change ε x = 0 at hx
    rw [hx, map_zero, map_zero]

end
end Dubon2026

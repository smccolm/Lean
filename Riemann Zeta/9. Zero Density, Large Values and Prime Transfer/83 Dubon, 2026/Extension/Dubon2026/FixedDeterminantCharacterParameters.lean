import Dubon2026.AuxiliaryCharacterAugmentation
import Mathlib.Algebra.BigOperators.Fin

/-! With trivial inertia determinant, the last labelled character is
determined by the others. Thus the actual auxiliary parameter group has
rank one less than the representation, with the same augmentation
specialization. This is the fixed-determinant parameter count needed by
the Dubon Theorem 2.6 arithmetic patching chain. -/

namespace Dubon2026
noncomputable section

variable {D A B : Type*} [Group D] [CommRing A] [CommRing B] {n : ℕ}

/-- Retain the first n of the original n+1 labelled diagonal characters. -/
def auxiliaryInitialCharacters (κ : D →* (Fin (n + 1) → A)ˣ) : D →* (Fin n → A)ˣ :=
  (Units.map (Pi.ringHom (fun i : Fin n =>
    Pi.evalRingHom (fun _ : Fin (n + 1) => A) i.castSucc)).toMonoidHom).comp κ

/-- Each retained parameter is the same original labelled character. -/
theorem auxiliaryInitialCharacters_apply (κ : D →* (Fin (n + 1) → A)ˣ) (d : D) (i : Fin n) :
    (auxiliaryInitialCharacters κ d).val i = (κ d).val i.castSucc := rfl

/-- A trivial determinant makes triviality of the first n characters
equivalent to triviality of all n+1 after every coefficient change. -/
theorem auxiliaryInitialCharacters_trivial_iff
    (κ : D →* (Fin (n + 1) → A)ˣ) (hdet : ∀ d, ∏ i, (κ d).val i = 1) (f : A →+* B) :
    (∀ d i, f ((auxiliaryInitialCharacters κ d).val i) = 1) ↔
      ∀ d i, f ((κ d).val i) = 1 := by
  constructor
  · intro h d i
    have hi (j : Fin n) : f ((κ d).val j.castSucc) = 1 := h d j
    refine Fin.lastCases ?_ (fun j => hi j) i
    have he := congrArg f (hdet d)
    rw [map_prod, map_one, Fin.prod_univ_castSucc] at he
    simpa only [hi, Finset.prod_const_one, one_mul] using he
  · intro h d i
    exact h d i.castSucc

/-- The fixed-determinant scalar map from n copies of the fixed inertia
quotient has exactly the same augmentation image as the full n+1 map. -/
theorem auxiliaryInitialCharacters_augmentationIdeal_eq
    (O : Type*) [CommRing O] [Algebra O A]
    (κ : D →* (Fin (n + 1) → A)ˣ) (hdet : ∀ d, ∏ i, (κ d).val i = 1) :
    auxiliaryCharacterAugmentationIdeal O (auxiliaryInitialCharacters κ) =
      auxiliaryCharacterAugmentationIdeal O κ := by
  let J := auxiliaryCharacterAugmentationIdeal O (auxiliaryInitialCharacters κ)
  let K := auxiliaryCharacterAugmentationIdeal O κ
  have hc (L : Ideal A) :
      J ≤ RingHom.ker (Ideal.Quotient.mk L) ↔ K ≤ RingHom.ker (Ideal.Quotient.mk L) := by
    rw [auxiliaryCharacterAugmentationIdeal_le_kernel_iff,
      auxiliaryCharacterAugmentationIdeal_le_kernel_iff]
    exact auxiliaryInitialCharacters_trivial_iff κ hdet (Ideal.Quotient.mk L)
  apply le_antisymm
  · have h : K ≤ RingHom.ker (Ideal.Quotient.mk K) := by rw [Ideal.mk_ker]
    have hj := (hc K).mpr h
    simpa only [Ideal.mk_ker] using hj
  · have h : J ≤ RingHom.ker (Ideal.Quotient.mk J) := by rw [Ideal.mk_ker]
    have hk := (hc J).mp h
    simpa only [Ideal.mk_ker] using hk

end
end Dubon2026

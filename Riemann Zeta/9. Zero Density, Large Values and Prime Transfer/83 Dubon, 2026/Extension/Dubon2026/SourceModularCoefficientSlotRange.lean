import Dubon2026.SourceModularCoefficientSlotPlaces
import Dubon2026.SourceOriginalSlotRange

/-! DUB-17/18 -> reverse genus inequality -> cusp count -> exact widths.
The existing all-level coefficient-field generation forces the image of
every actual conjugate embedding into the common expansion subfield.
The generic expansion-range lemma is reused from the original-field proof. -/

noncomputable section

namespace Dubon2026.SourceFunctionField

open IntermediateField ConjugateSlots PrimeDegreeAux

variable (N : ℕ) [NeZero N] (K : Type*) [Field K] [IsAlgClosed K]

/-- The two actual modular coordinates generate the full coefficient field internally. -/
theorem coeff_internal_pair_adjoin_top (hNK : (N : K) ≠ 0) :
    IntermediateField.adjoin K
      ({jCoeff N K, ⟨qExpand K N (jqModC K), jqd_mem_coeff_field N K dvd_rfl⟩} :
        Set (modularFunctionFieldCoeff N K)) = ⊤ := by
  apply IntermediateField.map_injective (modularFunctionFieldCoeff N K).val
  refine (IntermediateField.adjoin_map K _ (modularFunctionFieldCoeff N K).val).trans ?_
  rw [Set.image_insert_eq, Set.image_singleton]
  exact (residue_full_generation_and_degree N hNK).1.symm.trans
    ((IntermediateField.fieldRange_val (S := modularFunctionFieldCoeff N K)).symm.trans
      (AlgHom.fieldRange_eq_map (modularFunctionFieldCoeff N K).val))

/-- The actual slot embedding has image in its precise common expansion subfield. -/
theorem coeff_slot_embedding_range (hNK : (N : K) ≠ 0)
    (ζ : Kˣ) (a b : ℕ) [NeZero a] (ha : a ∣ N)
    (ι : modularFunctionFieldCoeff N K →ₐ[K] LaurentSeries K)
    (hj : ι (jCoeff N K) = TS K N 1)
    (hjN : ι ⟨qExpand K N (jqModC K), jqd_mem_coeff_field N K dvd_rfl⟩ = slotValue ζ a b)
    (x : modularFunctionFieldCoeff N K) :
    letI : NeZero (a * Nat.gcd a (N / a)) :=
      ⟨Nat.mul_ne_zero (NeZero.ne a) (Nat.gcd_ne_zero_left (NeZero.ne a))⟩
    ι x ∈ (qExpandAlgHom K (a * Nat.gcd a (N / a))).fieldRange := by
  letI : NeZero (a * Nat.gcd a (N / a)) :=
    ⟨Nat.mul_ne_zero (NeZero.ne a) (Nat.gcd_ne_zero_left (NeZero.ne a))⟩
  have hdN : a * Nat.gcd a (N / a) ∣ N :=
    (Nat.mul_dvd_mul_left a (Nat.gcd_dvd_right _ _)).trans (by rw [Nat.mul_div_cancel' ha])
  have hda : a * Nat.gcd a (N / a) ∣ a * a := Nat.mul_dvd_mul_left a (Nat.gcd_dvd_left _ _)
  have hx : x ∈ IntermediateField.adjoin K
      ({jCoeff N K, ⟨qExpand K N (jqModC K), jqd_mem_coeff_field N K dvd_rfl⟩} :
        Set (modularFunctionFieldCoeff N K)) := by
    rw [coeff_internal_pair_adjoin_top N K hNK]
    exact IntermediateField.mem_top
  induction hx using IntermediateField.adjoin_induction with
  | mem y hy =>
    rcases hy with rfl | hy
    · rw [hj, TS, qTwist_one_apply]
      exact qExpand_mem_fieldRange_of_dvd K _ N hdN _
    · rcases hy with rfl
      rw [hjN, slotValue_eq, TS]
      exact qExpand_mem_fieldRange_of_dvd K _ (a * a) hda _
  | algebraMap c => rw [ι.commutes]; exact IntermediateField.algebraMap_mem _ c
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | inv y _ hy => rw [map_inv₀]; exact inv_mem hy
  | mul y z _ _ hy hz => rw [map_mul]; exact mul_mem hy hz

end Dubon2026.SourceFunctionField

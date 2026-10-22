import Dubon2026.SourceOriginalSlotPlaces

/-! DUB-17/18 -> numerical modular genus -> cusp widths. The image of
each actual conjugate embedding lies in the precise common expansion
subfield determined by a*gcd(a,N/a). Generation by the two actual j
coordinates derives this range property for every field element. It will
force the place-normalization integer to equal that common exponent.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, the slot_range argument in
S_ModularCurve_card_poles_jqModC_modularFunctionFieldFullC_eq_cuspCount.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open IntermediateField ConjugateSlots PrimeDegreeAux
variable (L : Type*) [Field L]

/-- Literal expansion as a homomorphism fixing the coefficient field. -/
def qExpandAlgHom (e : ℕ) [NeZero e] : LaurentSeries L →ₐ[L] LaurentSeries L where
  toRingHom := qExpand L e
  commutes' c := by
    change qExpand L e (algebraMap L (LaurentSeries L) c) = _
    rw [SourceDifferential.algebraMap_laurentSeries_apply_alt, qExpand_single, mul_zero]

theorem qExpand_mem_fieldRange_of_dvd (e d : ℕ) [NeZero e] [NeZero d]
    (hed : e ∣ d) (f : LaurentSeries L) :
    qExpand L d f ∈ (qExpandAlgHom L e).fieldRange := by
  obtain ⟨k, hk⟩ := hed
  have hk0 : k ≠ 0 := fun he => NeZero.ne d (by rw [hk, he, mul_zero])
  haveI : NeZero k := ⟨hk0⟩
  refine ⟨qExpand L k f, ?_⟩
  change qExpand L e (qExpand L k f) = qExpand L d f
  rw [qExpand_qExpand]
  exact qExpand_congr hk.symm f

variable [Algebra ℚ L]

theorem original_slot_embedding_range (N : ℕ) [NeZero N]
    (ζ : Lˣ) (a b : ℕ) [NeZero a] (ha : a ∣ N)
    (ι : modularFunctionFieldOver N L →ₐ[L] LaurentSeries L)
    (hj : ι (jOver N L) = TS L N 1)
    (hjN : ι (jNOver N L) = slotValue ζ a b)
    (x : modularFunctionFieldOver N L) :
    letI : NeZero (a * Nat.gcd a (N / a)) :=
      ⟨Nat.mul_ne_zero (NeZero.ne a) (Nat.gcd_ne_zero_left (NeZero.ne a))⟩
    ι x ∈ (qExpandAlgHom L (a * Nat.gcd a (N / a))).fieldRange := by
  letI : NeZero (a * Nat.gcd a (N / a)) :=
    ⟨Nat.mul_ne_zero (NeZero.ne a) (Nat.gcd_ne_zero_left (NeZero.ne a))⟩
  have hdN : a * Nat.gcd a (N / a) ∣ N :=
    (Nat.mul_dvd_mul_left a (Nat.gcd_dvd_right _ _)).trans (by rw [Nat.mul_div_cancel' ha])
  have hda : a * Nat.gcd a (N / a) ∣ a * a := Nat.mul_dvd_mul_left a (Nat.gcd_dvd_left _ _)
  have hx : x ∈ IntermediateField.adjoin L ({jOver N L, jNOver N L} : Set (modularFunctionFieldOver N L)) := by
    rw [original_internal_pair_adjoin_top]
    exact IntermediateField.mem_top
  induction hx using IntermediateField.adjoin_induction with
  | mem y hy =>
    rcases hy with rfl | hy
    · rw [hj, TS, qTwist_one_apply]
      exact qExpand_mem_fieldRange_of_dvd L _ N hdN _
    · rcases hy with rfl
      rw [hjN, slotValue_eq, TS]
      exact qExpand_mem_fieldRange_of_dvd L _ (a * a) hda _
  | algebraMap c => rw [ι.commutes]; exact IntermediateField.algebraMap_mem _ c
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | inv y _ hy => rw [map_inv₀]; exact inv_mem hy
  | mul y z _ _ hy hz => rw [map_mul]; exact mul_mem hy hz

end
end Dubon2026.SourceFunctionField

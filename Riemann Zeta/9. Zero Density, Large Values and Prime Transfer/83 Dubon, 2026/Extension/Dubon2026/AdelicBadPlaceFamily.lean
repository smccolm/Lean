import Dubon2026.AdelicBadPlaceFinite

/-! # A genuine finite indexed family of all original bad places -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain

/-- The actual finite family lists each original bad finite place exactly once. -/
def adelicBadPlaceFamily (N : ℕ) [NeZero N] : Fin (Fintype.card (AdelicBadPlace N)) → HeightOneSpectrum ℤ :=
  fun i => ((Fintype.equivFin (AdelicBadPlace N)).symm i).val

/-- Every genuine listed bad place is actually bad for the original level. -/
theorem adelicBadPlaceFamily_bad (N : ℕ) [NeZero N] (i : Fin (Fintype.card (AdelicBadPlace N))) :
    ¬ IsGoodAdelicPlace N (adelicBadPlaceFamily N i) :=
  ((Fintype.equivFin (AdelicBadPlace N)).symm i).property

/-- The actual finite bad-place family has no repeated genuine place. -/
theorem adelicBadPlaceFamily_injective (N : ℕ) [NeZero N] : Function.Injective (adelicBadPlaceFamily N) := by
  intro i j he
  exact (Fintype.equivFin (AdelicBadPlace N)).symm.injective (Subtype.ext he)

/-- Every actual bad place occurs in the original finite indexed family. -/
theorem adelicBadPlaceFamily_surjective_bad (N : ℕ) [NeZero N] (v : HeightOneSpectrum ℤ)
    (hv : ¬ IsGoodAdelicPlace N v) : ∃ i, adelicBadPlaceFamily N i = v := by
  refine ⟨Fintype.equivFin (AdelicBadPlace N) ⟨v, hv⟩, ?_⟩
  exact congrArg Subtype.val ((Fintype.equivFin (AdelicBadPlace N)).symm_apply_apply ⟨v, hv⟩)

/-- An actual original good place differs from every coordinate in the genuine bad-place family. -/
theorem goodAdelicPlace_ne_badFamily (N : ℕ) [NeZero N] (v : HeightOneSpectrum ℤ)
    (hv : IsGoodAdelicPlace N v) (i : Fin (Fintype.card (AdelicBadPlace N))) : v ≠ adelicBadPlaceFamily N i := by
  intro he
  exact adelicBadPlaceFamily_bad N i (he ▸ hv)

end
end Dubon2026

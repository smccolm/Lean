import GafniTao.FordLShiftRaisedMoment

/-!
# Ford Lemma 3.3: the harmless constant phase

The raw shifted Weyl sum differs from the full Weyl sum of Ford's raised
system by one Fourier character independent of the summation variable.  That
character has norm one, so the absolute values agree exactly.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

theorem fordLShiftedWeylSum_true_eq_phase_mul_raised
    {k d T P : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (hT : 0 < T) (m : ℕ) (hm : 0 < m)
    (h : FordPositiveShift P m) (α : UnitAddTorus (Fin k)) :
    fordLShiftedWeylSum Ψ m (true, h) α =
      UnitAddTorus.mFourier (fordLDifferencePhase Ψ (h.1 * m)) α *
        fordPolynomialFullWeylSum (P := P)
          (fordIntegerDifferenceSystem Ψ hT (h.1 * m)
            (Nat.mul_pos (by
              have hh := h.property
              rw [Finset.mem_Icc] at hh
              omega) hm)) α := by
  unfold fordLShiftedWeylSum fordPolynomialFullWeylSum fordCharacterSum
  simp_rw [fordLSignedShiftMoment_true_eq_phase_add_raised Ψ hT m hm h,
    UnitAddTorus.mFourier_add]
  rw [Finset.mul_sum]

theorem norm_mFourier_apply {k : ℕ} (n : Fin k → ℤ)
    (α : UnitAddTorus (Fin k)) :
    ‖UnitAddTorus.mFourier n α‖ = 1 := by
  simp [UnitAddTorus.mFourier, norm_prod]

theorem norm_fordLShiftedWeylSum_true_eq_raised
    {k d T P : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (hT : 0 < T) (m : ℕ) (hm : 0 < m)
    (h : FordPositiveShift P m) (α : UnitAddTorus (Fin k)) :
    ‖fordLShiftedWeylSum Ψ m (true, h) α‖ =
      ‖fordPolynomialFullWeylSum (P := P)
        (fordIntegerDifferenceSystem Ψ hT (h.1 * m)
          (Nat.mul_pos (by
            have hh := h.property
            rw [Finset.mem_Icc] at hh
            omega) hm)) α‖ := by
  rw [fordLShiftedWeylSum_true_eq_phase_mul_raised Ψ hT m hm h,
    norm_mul, norm_mFourier_apply, one_mul]

#print axioms fordLShiftedWeylSum_true_eq_phase_mul_raised
#print axioms norm_fordLShiftedWeylSum_true_eq_raised

end

end GafniTao

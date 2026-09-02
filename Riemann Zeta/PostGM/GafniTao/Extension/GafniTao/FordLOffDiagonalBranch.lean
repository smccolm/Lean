import GafniTao.FordLShiftCauchy

/-!
# Ford Lemma 3.3: closure of the off-diagonal integral estimate

The exact enlargement, finite Jensen selection, type-raising identity, and
Cauchy--Schwarz estimate are composed here.  The first theorem retains the
literal natural quotient `P / p^r`; the second converts it to Ford's displayed
real factor `p^(-r*k)` without pretending that natural division is exact.
-/

namespace GafniTao

noncomputable section

theorem exists_fordLOffDiagonalCount_le_oneShift_sqrt
    {k d T P p r : ℕ} [NeZero (p ^ r)]
    (Ψ : FordIntegerPolynomialSystem k d T) (s Q q : ℕ)
    (hk : 1 ≤ k) (hH : 1 ≤ P / (p ^ r))
    (hT : 0 < T) (hpq : 0 < p * q) :
    ∃ h : FordPositiveShift P (p ^ r),
      (fordLOffDiagonalCount Ψ s P Q p q r : ℝ) ≤
        (((2 * (P / (p ^ r)) : ℕ) : ℝ) ^ k) *
          (√(fordKCount
              (fordIntegerDifferenceSystem Ψ hT (h.1 * (p ^ r))
                (Nat.mul_pos (by
                  have hh := h.property
                  rw [Finset.mem_Icc] at hh
                  omega) (NeZero.pos (p ^ r))))
              s P Q (p * q) : ℝ) *
            √(fordVinogradovMomentNat s k Q : ℝ)) := by
  obtain ⟨h, hmax⟩ := exists_fordL_aggregateIntegral_le_oneShift
    Ψ (p ^ r) p q s Q hk hH
  refine ⟨h, ?_⟩
  calc
    (fordLOffDiagonalCount Ψ s P Q p q r : ℝ) ≤
        ∫ α : UnitAddTorus (Fin k),
          fordLShiftAmplitude (P := P) Ψ (p ^ r) α ^ k *
            ‖fordPowerFullWeylSum k Q (p * q) α‖ ^ (2 * s)
          ∂fordTorusMeasure k :=
      fordLOffDiagonalCount_le_aggregateIntegral Ψ s P Q p q r
    _ ≤ (((2 * (P / (p ^ r)) : ℕ) : ℝ) ^ k) *
        fordLPositiveShiftIntegral Ψ (p ^ r) p q s Q h := hmax
    _ ≤ (((2 * (P / (p ^ r)) : ℕ) : ℝ) ^ k) *
        (√(fordKCount
            (fordIntegerDifferenceSystem Ψ hT (h.1 * (p ^ r))
              (Nat.mul_pos (by
                have hh := h.property
                rw [Finset.mem_Icc] at hh
                omega) (NeZero.pos (p ^ r))))
            s P Q (p * q) : ℝ) *
          √(fordVinogradovMomentNat s k Q : ℝ)) := by
      gcongr
      exact fordLPositiveShiftIntegral_le_count_sqrt
        Ψ hT (p ^ r) (NeZero.pos (p ^ r)) p q s Q hpq h

theorem ford_natural_shift_coefficient_le_source
    {P p r k : ℕ} (hp : 0 < p) :
    (((2 * (P / (p ^ r)) : ℕ) : ℝ) ^ k) ≤
      ((2 * P : ℕ) : ℝ) ^ k *
        (((p : ℝ) ^ (r * k))⁻¹) := by
  have hpr : (0 : ℝ) < (p : ℝ) ^ r := by positivity
  have hbase : ((2 * (P / (p ^ r)) : ℕ) : ℝ) ≤
      ((2 * P : ℕ) : ℝ) / ((p : ℝ) ^ r) := by
    push_cast
    calc
      2 * ((P / (p ^ r) : ℕ) : ℝ) ≤
          2 * ((P : ℝ) / ((p ^ r : ℕ) : ℝ)) := by
        gcongr
        exact Nat.cast_div_le
      _ = (2 * (P : ℝ)) / ((p : ℝ) ^ r) := by
        push_cast
        ring
  calc
    (((2 * (P / (p ^ r)) : ℕ) : ℝ) ^ k) ≤
        (((2 * P : ℕ) : ℝ) / (p : ℝ) ^ r) ^ k :=
      pow_le_pow_left₀ (by positivity) hbase k
    _ = ((2 * P : ℕ) : ℝ) ^ k *
        (((p : ℝ) ^ (r * k))⁻¹) := by
      rw [div_pow, div_eq_mul_inv, ← pow_mul]

theorem exists_fordLOffDiagonalCount_le_source_sqrt
    {k d T P p r : ℕ} [NeZero (p ^ r)]
    (Ψ : FordIntegerPolynomialSystem k d T) (s Q q : ℕ)
    (hk : 1 ≤ k) (hH : 1 ≤ P / (p ^ r))
    (hT : 0 < T) (hpq : 0 < p * q) (hp : 0 < p) :
    ∃ h : FordPositiveShift P (p ^ r),
      (fordLOffDiagonalCount Ψ s P Q p q r : ℝ) ≤
        ((2 * P : ℕ) : ℝ) ^ k *
          (((p : ℝ) ^ (r * k))⁻¹ *
            (√(fordKCount
                (fordIntegerDifferenceSystem Ψ hT (h.1 * (p ^ r))
                  (Nat.mul_pos (by
                    have hh := h.property
                    rw [Finset.mem_Icc] at hh
                    omega) (NeZero.pos (p ^ r))))
                s P Q (p * q) : ℝ) *
              √(fordVinogradovMomentNat s k Q : ℝ))) := by
  obtain ⟨h, hbound⟩ := exists_fordLOffDiagonalCount_le_oneShift_sqrt
    Ψ s Q q hk hH hT hpq
  refine ⟨h, hbound.trans ?_⟩
  have hcoeff := ford_natural_shift_coefficient_le_source
    (P := P) (p := p) (r := r) (k := k) hp
  have hroot : 0 ≤
      √(fordKCount
          (fordIntegerDifferenceSystem Ψ hT (h.1 * (p ^ r))
            (Nat.mul_pos (by
              have hh := h.property
              rw [Finset.mem_Icc] at hh
              omega) (NeZero.pos (p ^ r))))
          s P Q (p * q) : ℝ) *
        √(fordVinogradovMomentNat s k Q : ℝ) := by positivity
  calc
    (((2 * (P / (p ^ r)) : ℕ) : ℝ) ^ k) *
        (√(fordKCount
            (fordIntegerDifferenceSystem Ψ hT (h.1 * (p ^ r))
              (Nat.mul_pos (by
                have hh := h.property
                rw [Finset.mem_Icc] at hh
                omega) (NeZero.pos (p ^ r))))
            s P Q (p * q) : ℝ) *
          √(fordVinogradovMomentNat s k Q : ℝ)) ≤
      (((2 * P : ℕ) : ℝ) ^ k * (((p : ℝ) ^ (r * k))⁻¹) *
        (√(fordKCount
            (fordIntegerDifferenceSystem Ψ hT (h.1 * (p ^ r))
              (Nat.mul_pos (by
                have hh := h.property
                rw [Finset.mem_Icc] at hh
                omega) (NeZero.pos (p ^ r))))
            s P Q (p * q) : ℝ) *
          √(fordVinogradovMomentNat s k Q : ℝ))) := by
        exact mul_le_mul_of_nonneg_right hcoeff hroot
    _ = _ := by ring

#print axioms exists_fordLOffDiagonalCount_le_oneShift_sqrt
#print axioms ford_natural_shift_coefficient_le_source
#print axioms exists_fordLOffDiagonalCount_le_source_sqrt

end

end GafniTao

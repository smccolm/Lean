import GafniTao.FordLOffDiagonalBranch

/-!
# Ford Lemma 3.3: exact finite source assembly

This file closes both alternatives in Ford's proof.  The output is a genuine
type-`(d+1,T')` integer polynomial system with `T ≤ T' ≤ P*T`, and the
displayed bound retains Ford's two alternatives and the exact inverse
`p^(r*k)` factor.
-/

namespace GafniTao

noncomputable section

theorem ford_offDiagonal_positive_implies_shift_range
    {k d T P p r s Q q : ℕ} [NeZero (p ^ r)]
    (Ψ : FordIntegerPolynomialSystem k d T)
    (hk : 1 ≤ k)
    (hoff : 0 < fordLOffDiagonalCount Ψ s P Q p q r) :
    1 ≤ P / (p ^ r) := by
  have hcard : 0 < Nat.card (FordLOffDiagonalSolution Ψ s P Q p q r) := by
    simpa [fordLOffDiagonalCount] using hoff
  obtain ⟨v⟩ := (Nat.card_pos_iff.mp hcard).1
  let i : Fin k := ⟨0, by omega⟩
  let u := fordLOffDiagonalParameterOf v
  have hh := ((u i).2).property
  exact (Finset.mem_Icc.mp hh).1.trans (Finset.mem_Icc.mp hh).2

theorem ford_lemma_3_3_finite_source
    {k d T P p r s Q q : ℕ}
    (Ψ : FordIntegerPolynomialSystem k d T)
    (_hsd : d ≤ s) (hr2 : 2 ≤ r) (hrk : r ≤ k)
    (_hdk : d ≤ k - 2) (hq : 1 ≤ q) (hp : Nat.Prime p)
    (hT : 0 < T) (hP : 0 < P) :
    ∃ (T' : ℕ) (Υ : FordIntegerPolynomialSystem k (d + 1) T'),
      T ≤ T' ∧ T' ≤ P * T ∧
      (fordLCount Ψ s P Q p q r : ℝ) ≤
        ((2 * P : ℕ) : ℝ) ^ k *
          max ((k ^ k * fordVinogradovMomentNat s k Q : ℕ) : ℝ)
            (2 * (((p : ℝ) ^ (r * k))⁻¹) *
              √((fordVinogradovMomentNat s k Q : ℝ) *
                (fordKCount Υ s P Q (p * q) : ℝ))) := by
  have hk : 1 ≤ k := by omega
  have hp0 : 0 < p := hp.pos
  have hpr : 0 < p ^ r := pow_pos hp0 r
  letI : NeZero (p ^ r) := ⟨hpr.ne'⟩
  have hpq : 0 < p * q := Nat.mul_pos hp0 (by omega)
  by_cases hbranch : fordLOffDiagonalCount Ψ s P Q p q r ≤
      fordLDiagonalCount Ψ s P Q p q r
  · let Υ₀ := fordIntegerDifferenceSystem Ψ hT 1 (by omega)
    refine ⟨1 * T, Υ₀, ?_, ?_, ?_⟩
    · simp
    · simpa using Nat.le_mul_of_pos_left T hP
    · have hdiag := fordL_diagonal_branch_bound
        Ψ s Q q hk hpq hbranch
      have hdiagR : (fordLCount Ψ s P Q p q r : ℝ) ≤
          (((2 * P) ^ k * k ^ k * fordVinogradovMomentNat s k Q : ℕ) : ℝ) :=
        by exact_mod_cast hdiag
      calc
        (fordLCount Ψ s P Q p q r : ℝ) ≤
            (((2 * P) ^ k * k ^ k * fordVinogradovMomentNat s k Q : ℕ) : ℝ) :=
          hdiagR
        _ = ((2 * P : ℕ) : ℝ) ^ k *
            ((k ^ k * fordVinogradovMomentNat s k Q : ℕ) : ℝ) := by
          push_cast
          ring
        _ ≤ ((2 * P : ℕ) : ℝ) ^ k *
            max ((k ^ k * fordVinogradovMomentNat s k Q : ℕ) : ℝ)
              (2 * (((p : ℝ) ^ (r * k))⁻¹) *
                √((fordVinogradovMomentNat s k Q : ℝ) *
                  (fordKCount Υ₀ s P Q (p * q) : ℝ))) := by
          gcongr
          exact le_max_left _ _
  · have hreverse : fordLDiagonalCount Ψ s P Q p q r ≤
        fordLOffDiagonalCount Ψ s P Q p q r := by omega
    by_cases hoff0 : fordLOffDiagonalCount Ψ s P Q p q r = 0
    · have hL0 : fordLCount Ψ s P Q p q r = 0 := by
        rw [fordLCount_eq_diagonal_add_offDiagonal]
        omega
      let Υ₀ := fordIntegerDifferenceSystem Ψ hT 1 (by omega)
      refine ⟨1 * T, Υ₀, ?_, ?_, ?_⟩
      · simp
      · simpa using Nat.le_mul_of_pos_left T hP
      · rw [hL0, Nat.cast_zero]
        exact mul_nonneg (pow_nonneg (by positivity) _)
          ((show (0 : ℝ) ≤
              ((k ^ k * fordVinogradovMomentNat s k Q : ℕ) : ℝ) by
                positivity).trans (le_max_left _ _))
    · have hoffpos : 0 < fordLOffDiagonalCount Ψ s P Q p q r :=
        Nat.pos_of_ne_zero hoff0
      have hH : 1 ≤ P / (p ^ r) :=
        ford_offDiagonal_positive_implies_shift_range Ψ hk hoffpos
      obtain ⟨h, hoffBound⟩ := exists_fordLOffDiagonalCount_le_source_sqrt
        Ψ s Q q hk hH hT hpq hp0
      have hhpos : 0 < h.1 := by
        have hh := h.property
        rw [Finset.mem_Icc] at hh
        omega
      have hypos : 0 < h.1 * (p ^ r) := Nat.mul_pos hhpos hpr
      have hyP : h.1 * (p ^ r) ≤ P := by
        have hh := h.property
        rw [Finset.mem_Icc] at hh
        exact (Nat.le_div_iff_mul_le hpr).1 hh.2
      let T' := (h.1 * (p ^ r)) * T
      let Υ := fordIntegerDifferenceSystem Ψ hT (h.1 * (p ^ r)) hypos
      have hscale := fordIntegerDifferenceSystem_T_bounds
        (T := T) (P := P) hypos hyP
      refine ⟨T', Υ, hscale.1, hscale.2, ?_⟩
      have hLoff : fordLCount Ψ s P Q p q r ≤
          2 * fordLOffDiagonalCount Ψ s P Q p q r := by
        rw [fordLCount_eq_diagonal_add_offDiagonal]
        omega
      have hLoffR : (fordLCount Ψ s P Q p q r : ℝ) ≤
          2 * (fordLOffDiagonalCount Ψ s P Q p q r : ℝ) := by
        exact_mod_cast hLoff
      have hroot :
          √(fordKCount Υ s P Q (p * q) : ℝ) *
              √(fordVinogradovMomentNat s k Q : ℝ) =
            √((fordVinogradovMomentNat s k Q : ℝ) *
              (fordKCount Υ s P Q (p * q) : ℝ)) := by
        rw [Real.sqrt_mul (by positivity :
          (0 : ℝ) ≤ (fordVinogradovMomentNat s k Q : ℝ))]
        ring
      calc
        (fordLCount Ψ s P Q p q r : ℝ) ≤
            2 * (fordLOffDiagonalCount Ψ s P Q p q r : ℝ) := hLoffR
        _ ≤ 2 * (((2 * P : ℕ) : ℝ) ^ k *
            (((p : ℝ) ^ (r * k))⁻¹ *
              (√(fordKCount Υ s P Q (p * q) : ℝ) *
                √(fordVinogradovMomentNat s k Q : ℝ)))) := by
          gcongr
        _ = ((2 * P : ℕ) : ℝ) ^ k *
            (2 * (((p : ℝ) ^ (r * k))⁻¹) *
              √((fordVinogradovMomentNat s k Q : ℝ) *
                (fordKCount Υ s P Q (p * q) : ℝ))) := by
          rw [hroot]
          ring
        _ ≤ ((2 * P : ℕ) : ℝ) ^ k *
            max ((k ^ k * fordVinogradovMomentNat s k Q : ℕ) : ℝ)
              (2 * (((p : ℝ) ^ (r * k))⁻¹) *
                √((fordVinogradovMomentNat s k Q : ℝ) *
                  (fordKCount Υ s P Q (p * q) : ℝ))) := by
          gcongr
          exact le_max_right _ _

#print axioms ford_offDiagonal_positive_implies_shift_range
#print axioms ford_lemma_3_3_finite_source

end

end GafniTao

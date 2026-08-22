import RiemannZeta.GuthMaynard.HughesYoungGlobalBounds
import RiemannZeta.GuthMaynard.HughesYoungPointwiseDFIAssembly
import RiemannZeta.GuthMaynard.HughesYoungCentralBetaBridge

open Asymptotics Complex Finset Filter MeasureTheory Set Topology
open scoped BigOperators ContDiff FourierTransform Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Native Hughes--Young fourth-moment assembly

This module performs the final quantitative summations after the exact DFI
Theorem 1 consumer.  It begins with the literal active diagonal; no source
conclusion is assumed as an input.
-/

/-- A conductor-scale product cutoff for the native Hughes--Young assembly.
The exponent `2.01` leaves a fixed power margin for the opening-line tail,
while keeping every DFI box at the scale used in the source argument. -/
noncomputable def hughesYoungConductorRadius (T : ℝ) : ℕ :=
  ⌈T ^ (201 / 100 : ℝ)⌉₊

/-- The fixed Hughes--Young smoothing scale used to make the large-DFI box
partition independent of the epsilon requested by the final asymptotic
statement.  It is a literal instance of (78), since `T / (T / 8) = 8`.
The deliberately small exponent leaves the strict power margin needed in
the global equation-(80) summation. -/
noncomputable def hughesYoungDFISmoothingScale (T : ℝ) : ℝ :=
  8 * T ^ (1 / 10000 : ℝ)

theorem one_le_hughesYoungDFISmoothingScale {T : ℝ} (hT : 1 ≤ T) :
    1 ≤ hughesYoungDFISmoothingScale T := by
  have hp : 1 ≤ T ^ (1 / 10000 : ℝ) :=
    Real.one_le_rpow hT (by norm_num)
  unfold hughesYoungDFISmoothingScale
  nlinarith

theorem hughesYoungConductorRadius_pos {T : ℝ} (hT : 1 ≤ T) :
    0 < hughesYoungConductorRadius T := by
  unfold hughesYoungConductorRadius
  exact Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (zero_lt_one.trans_le hT) _)

theorem hughesYoungConductorRadius_lower (T : ℝ) :
    T ^ (201 / 100 : ℝ) ≤ (hughesYoungConductorRadius T : ℝ) := by
  unfold hughesYoungConductorRadius
  exact Nat.le_ceil _

/-- Sharp upper companion to the conductor-radius definition. -/
theorem hughesYoungConductorRadius_le_two_mul_rpow
    {T : ℝ} (hT : 1 ≤ T) :
    (hughesYoungConductorRadius T : ℝ) ≤
      2 * T ^ (201 / 100 : ℝ) := by
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hp : 1 ≤ T ^ (201 / 100 : ℝ) :=
    Real.one_le_rpow hT (by norm_num)
  have hceil := Nat.ceil_lt_add_one
    (Real.rpow_nonneg hT0.le (201 / 100 : ℝ))
  unfold hughesYoungConductorRadius
  linarith

theorem hughesYoungConductorRadius_le_two_mul_cube
    {T : ℝ} (hT : 1 ≤ T) :
    (hughesYoungConductorRadius T : ℝ) ≤ 2 * T ^ (3 : ℝ) := by
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hpow : T ^ (201 / 100 : ℝ) ≤ T ^ (3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hT (by norm_num)
  have hone : 1 ≤ T ^ (3 : ℝ) := Real.one_le_rpow hT (by norm_num)
  have hceil := Nat.ceil_lt_add_one
    (Real.rpow_nonneg hT0.le (201 / 100 : ℝ))
  unfold hughesYoungConductorRadius
  linarith

theorem oneHundredSixtyTwo_mul_rpow_seven_le_rpow_thirty
    {T : ℝ} (hT : 2 ≤ T) :
    (162 : ℝ) * T ^ (7 : ℝ) ≤ T ^ (30 : ℝ) := by
  have hpow : (162 : ℝ) ≤ T ^ (23 : ℝ) := by
    calc
      (162 : ℝ) ≤ 2 ^ (23 : ℕ) := by norm_num
      _ ≤ T ^ (23 : ℕ) := by gcongr
      _ = T ^ (23 : ℝ) := by simp
  rw [show T ^ (30 : ℝ) = T ^ (23 : ℝ) * T ^ (7 : ℝ) by
    rw [← Real.rpow_add (by positivity)]
    norm_num]
  gcongr

/-- The existing logarithmic depth covers the conductor-scale cutoff for
every actual pair of mollifier indices. -/
theorem hughesYoungConductor_cover {T : ℝ} (hT : 2 ≤ T)
    {h k : ℕ}
    (hh : h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2))
    (hk : k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2)) :
    ((((hughesYoungReducedLeft h k) *
      (hughesYoungReducedRight h k) * hughesYoungConductorRadius T : ℕ) : ℝ)) ≤
        hughesYoungDyadicRatio ^ (hughesYoungGlobalDepth T + 1) := by
  have hT1 : 1 ≤ T := by linarith
  have hcut := detectorCutoff_le_three_mul T hT1
  have hrr := hughesYoungConductorRadius_le_two_mul_cube hT1
  have hh' : (h : ℝ) ≤ (3 * T) ^ 2 := by
    have hhcast : (h : ℝ) ≤ ((detectorCutoff T : ℝ) ^ 2) := by
      exact_mod_cast (Finset.mem_Icc.mp hh).2
    exact hhcast.trans (pow_le_pow_left₀ (by positivity) hcut 2)
  have hk' : (k : ℝ) ≤ (3 * T) ^ 2 := by
    have hkcast : (k : ℝ) ≤ ((detectorCutoff T : ℝ) ^ 2) := by
      exact_mod_cast (Finset.mem_Icc.mp hk).2
    exact hkcast.trans (pow_le_pow_left₀ (by positivity) hcut 2)
  have ha : (hughesYoungReducedLeft h k : ℝ) ≤ h := by
    exact_mod_cast hughesYoungReducedLeft_le h k
  have hb : (hughesYoungReducedRight h k : ℝ) ≤ k := by
    exact_mod_cast hughesYoungReducedRight_le h k
  have hraw :
      ((hughesYoungReducedLeft h k : ℝ) *
        (hughesYoungReducedRight h k : ℝ) *
          (hughesYoungConductorRadius T : ℝ)) ≤
            162 * T ^ (7 : ℝ) := by
    calc
      _ ≤ ((3 * T) ^ 2) * ((3 * T) ^ 2) *
          (2 * T ^ (3 : ℝ)) := by
        gcongr
        · exact ha.trans hh'
        · exact hb.trans hk'
      _ = 162 * T ^ (7 : ℝ) := by
        simp only [Real.rpow_ofNat]
        ring
  simp only [Nat.cast_mul]
  exact hraw.trans
    ((oneHundredSixtyTwo_mul_rpow_seven_le_rpow_thirty hT).trans
      (rpow_thirty_le_globalDepth hT1))

set_option maxRecDepth 100000 in
/-- At order `1000`, the part of the opened zeta product beyond the
conductor-scale radius is power-saving.  This is the quantitative replacement
for the earlier `T^5` cutoff: the finite family passed to DFI now has the
source conductor size. -/
theorem exists_norm_hughesYoungConductorOpeningRemainder_le_height :
    ∃ C : ℝ, 0 < C ∧ ∀ {T : ℝ}, Real.exp 1 ≤ T →
      ‖hughesYoungActiveWholeSmoothedRemainder 1000 T
          (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)‖ ≤ C * T := by
  obtain ⟨L, hL, hrem⟩ :=
    exists_norm_hughesYoungActiveWholeSmoothedRemainder_le
      1000 (by norm_num) (1 / 2 : ℝ) (by norm_num) (by norm_num)
  let C : ℝ :=
    (15 / 4) * 81 ^ 2 * (1 / Real.pi) *
      (256 * Real.exp (400 * (1000 : ℝ) ^ 2) *
        2007 ^ (4008 : ℕ) *
        (hughesYoungReferenceDivisorPairMass (1 / 2) + 1) * L)
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos
      (mul_pos (mul_pos (by norm_num) (by norm_num)) (by positivity))
      (mul_pos
        (mul_pos (mul_pos (by positivity) (by positivity))
          (by linarith [hughesYoungReferenceDivisorPairMass_nonneg (1 / 2)])) hL)
  refine ⟨C, hC, ?_⟩
  intro T hT
  have hT1 : 1 ≤ T := by linarith [Real.exp_one_gt_d9]
  have hT2 : 2 ≤ T := by linarith [Real.exp_one_gt_two]
  have hT0 : 0 < T := zero_lt_one.trans_le hT1
  have hR := hughesYoungConductorRadius_pos hT1
  have hcover : ∀ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∀ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        (((hughesYoungReducedLeft h k) *
          (hughesYoungReducedRight h k) * hughesYoungConductorRadius T : ℕ) : ℝ) ≤
            hughesYoungDyadicRatio ^ (hughesYoungGlobalDepth T + 1) := by
    intro h hh k hk
    exact hughesYoungConductor_cover hT2 hh hk
  have hraw := hrem hT hR hcover
  have hraw' :
      ‖hughesYoungActiveWholeSmoothedRemainder 1000 T
          (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)‖ ≤
        (15 * T / 4) * hughesYoungMollifierCoefficientMass T ^ 2 *
          (1 / Real.pi) *
          ((256 * Real.exp (400 * (1000 : ℝ) ^ 2) *
            ((2007 : ℝ) * T) ^ (4008 : ℕ) *
            (hughesYoungConductorRadius T : ℝ) ^ (-1999 : ℝ) *
            hughesYoungReferenceDivisorPairMass (1 / 2)) * L) := by
    convert hraw using 1
    all_goals norm_num
  have hmass := hughesYoungMollifierCoefficientMass_le_height_fourth hT1
  have hmass0 := hughesYoungMollifierCoefficientMass_nonneg T
  have hpair0 := hughesYoungReferenceDivisorPairMass_nonneg (1 / 2)
  have hpair : hughesYoungReferenceDivisorPairMass (1 / 2) ≤
      hughesYoungReferenceDivisorPairMass (1 / 2) + 1 := by linarith
  have hrneg : (hughesYoungConductorRadius T : ℝ) ^ (-1999 : ℝ) ≤
      T ^ (-401799 / 100 : ℝ) := by
    have hlower : T ^ (201 / 100 : ℝ) ≤
        (hughesYoungConductorRadius T : ℝ) :=
      hughesYoungConductorRadius_lower T
    have hneg := Real.rpow_le_rpow_of_nonpos
      (Real.rpow_pos_of_pos hT0 (201 / 100 : ℝ)) hlower
        (by norm_num : (-1999 : ℝ) ≤ 0)
    calc
      _ ≤ (T ^ (201 / 100 : ℝ)) ^ (-1999 : ℝ) := hneg
      _ = T ^ (-401799 / 100 : ℝ) := by
        rw [← Real.rpow_mul hT0.le]
        norm_num
  have hbound :
      (15 * T / 4) * hughesYoungMollifierCoefficientMass T ^ 2 *
          (1 / Real.pi) *
          ((256 * Real.exp (400 * (1000 : ℝ) ^ 2) *
            ((2007 : ℝ) * T) ^ (4008 : ℕ) *
            (hughesYoungConductorRadius T : ℝ) ^ (-1999 : ℝ) *
            hughesYoungReferenceDivisorPairMass (1 / 2)) * L) ≤
        C * T ^ (-99 / 100 : ℝ) := by
    calc
      _ ≤
          (15 * T / 4) * (81 * T ^ (4 : ℝ)) ^ 2 *
            (1 / Real.pi) *
            ((256 * Real.exp (400 * (1000 : ℝ) ^ 2) *
              ((2007 : ℝ) * T) ^ (4008 : ℕ) *
              T ^ (-401799 / 100 : ℝ) *
              (hughesYoungReferenceDivisorPairMass (1 / 2) + 1)) * L) := by
        gcongr
    _ = C * T ^ (-99 / 100 : ℝ) := by
      have hfour : (T ^ (4 : ℝ)) ^ 2 = T ^ (8 : ℝ) := by
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul hT0.le]
        norm_num
      have hpowers :
          T * T ^ (8 : ℝ) * T ^ (4008 : ℕ) *
              T ^ (-401799 / 100 : ℝ) =
            T ^ (-99 / 100 : ℝ) := by
        calc
          _ = T ^ (1 : ℝ) * T ^ (8 : ℝ) * T ^ (4008 : ℝ) *
                T ^ (-401799 / 100 : ℝ) := by
            rw [Real.rpow_one]
            exact congrArg
              (fun x : ℝ => T * T ^ (8 : ℝ) * x *
                T ^ (-401799 / 100 : ℝ))
              (Real.rpow_natCast T 4008).symm
          _ = T ^ ((1 : ℝ) + 8) * T ^ (4008 : ℝ) *
                T ^ (-401799 / 100 : ℝ) := by
            rw [← Real.rpow_add hT0]
          _ = T ^ ((1 : ℝ) + 8 + 4008) *
                T ^ (-401799 / 100 : ℝ) := by
            rw [← Real.rpow_add hT0]
          _ = T ^ ((1 : ℝ) + 8 + 4008 - 401799 / 100) := by
            rw [← Real.rpow_add hT0]
            congr 1
            ring
          _ = T ^ (-99 / 100 : ℝ) := by norm_num
      rw [mul_pow, hfour]
      calc
        _ = C * (T * T ^ (8 : ℝ) * T ^ (4008 : ℕ) *
            T ^ (-401799 / 100 : ℝ)) := by
          dsimp only [C]
          set_option exponentiation.threshold 5000 in ring
        _ = C * T ^ (-99 / 100 : ℝ) := by rw [hpowers]
  have hlast : C * T ^ (-99 / 100 : ℝ) ≤ C * T := by
    have hp : T ^ (-99 / 100 : ℝ) ≤ T := by
      calc
        T ^ (-99 / 100 : ℝ) ≤ T ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num)
        _ = T := by simp
    exact mul_le_mul_of_nonneg_left hp hC.le
  exact hraw'.trans (hbound.trans hlast)

/-- One uniform arithmetic cutoff containing every coordinate in every
active dyadic box for mollifier indices at most the squared detector cutoff. -/
noncomputable def hughesYoungActiveArithmeticCutoff (T : ℝ) (R : ℕ) : ℕ :=
  4 * ((detectorCutoff T) ^ 2 * (detectorCutoff T) ^ 2 * R) + 1

/-- The complete active diagonal is bounded by the established literal
`hm = kn` arithmetic majorant, with only the number of dyadic boxes lost.
This is the global consumer of the finite diagonal theorem. -/
theorem exists_norm_hughesYoungActiveFiniteDiagonal_le :
    ∃ C W : ℝ, 0 < C ∧ 0 < W ∧
      ∀ {T H : ℝ} {R K : ℕ}, Real.exp 1 ≤ T → 0 ≤ H →
      ‖hughesYoungActiveFiniteDiagonal T H R K‖ ≤
        ((K + 2 : ℕ) : ℝ) ^ 2 *
          ((15 * T / 4) * (1 / Real.pi) *
            (Real.log T * Real.exp (4 * C) * W *
              Real.sqrt (Real.pi / 80))) *
          hughesYoungFiniteDiagonalArithmeticMajorant T
            ((detectorCutoff T) ^ 2)
            (hughesYoungActiveArithmeticCutoff T R) := by
  obtain ⟨C, W, hC, hW, hterm⟩ :=
    exists_norm_integral_hughesYoungFiniteArithmeticTerm_diagonal_le
  refine ⟨C, W, hC, hW, ?_⟩
  intro T H R K hT hH
  let ell : ℕ := (detectorCutoff T) ^ 2
  let B : ℕ := 4 * (ell * ell * R) + 1
  let F : ℝ := (15 * T / 4) * (1 / Real.pi) *
    (Real.log T * Real.exp (4 * C) * W * Real.sqrt (Real.pi / 80))
  have hF0 : 0 ≤ F := by
    have hT1 : 1 ≤ T := by linarith [Real.exp_one_gt_d9]
    have hlog : 0 ≤ Real.log T := Real.log_nonneg hT1
    dsimp only [F]
    positivity
  have hbox : ∀ h ∈ Finset.Icc 1 ell, ∀ k ∈ Finset.Icc 1 ell,
      ∀ ij ∈ hughesYoungActiveDyadicBoxes
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
      ‖hughesYoungFullDyadicDiagonalBox T (hughesYoungSmallContour T)
          H h k ij.1 ij.2‖ ≤
        F * (∑ m ∈ Finset.Icc 1 B, ∑ n ∈ Finset.Icc 1 B,
          if h * m = k * n then
            ‖shortMobiusSquareCoeff T h‖ *
              ‖shortMobiusSquareCoeff T k‖ *
              (m.divisors.card : ℝ) * (n.divisors.card : ℝ) *
              (((h * m : ℕ) : ℝ))⁻¹
          else 0) := by
    intro h hhmem k hkmem ij hij
    have hh : 0 < h := (Finset.mem_Icc.mp hhmem).1
    have hk : 0 < k := (Finset.mem_Icc.mp hkmem).1
    have ha : hughesYoungReducedLeft h k ≤ h := hughesYoungReducedLeft_le h k
    have hb : hughesYoungReducedRight h k ≤ k := hughesYoungReducedRight_le h k
    have hab : hughesYoungReducedLeft h k * hughesYoungReducedRight h k * R ≤
        ell * ell * R := by
      gcongr
      · exact ha.trans (Finset.mem_Icc.mp hhmem).2
      · exact hb.trans (Finset.mem_Icc.mp hkmem).2
    have hBi : hughesYoungFullDyadicBound ij.1 ≤ B := by
      exact (hughesYoungFullDyadicBound_le_four_mul_activeConductor_add_one_left
        hij).trans (by dsimp only [B]; omega)
    have hBj : hughesYoungFullDyadicBound ij.2 ≤ B := by
      exact (hughesYoungFullDyadicBound_le_four_mul_activeConductor_add_one_right
        hij).trans (by dsimp only [B]; omega)
    unfold hughesYoungFullDyadicDiagonalBox
    calc
      ‖∑ m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
          ∑ n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.2),
            if quadraticDivisorShift h k m n = 0 then
              hughesYoungFullDyadicIntegratedTerm T
                (hughesYoungSmallContour T) H h k ij.1 ij.2 (m, n)
            else 0‖ ≤
        ∑ m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
          ∑ n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.2),
            ‖if quadraticDivisorShift h k m n = 0 then
              hughesYoungFullDyadicIntegratedTerm T
                (hughesYoungSmallContour T) H h k ij.1 ij.2 (m, n)
            else 0‖ := (norm_sum_le _ _).trans
              (Finset.sum_le_sum fun m _ => norm_sum_le _ _)
      _ ≤ ∑ m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
          ∑ n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.2),
            F * (if h * m = k * n then
              ‖shortMobiusSquareCoeff T h‖ *
                ‖shortMobiusSquareCoeff T k‖ *
                (m.divisors.card : ℝ) * (n.divisors.card : ℝ) *
                (((h * m : ℕ) : ℝ))⁻¹
            else 0) := by
        apply Finset.sum_le_sum
        intro m hm
        apply Finset.sum_le_sum
        intro n hn
        have hm0 : 0 < m := (Finset.mem_Icc.mp hm).1
        have hn0 : 0 < n := (Finset.mem_Icc.mp hn).1
        by_cases hd : h * m = k * n
        · have hs : quadraticDivisorShift h k m n = 0 :=
            (quadraticDivisorShift_eq_zero_iff h k m n).2 hd
          rw [if_pos hs, if_pos hd]
          exact (norm_hughesYoungFullDyadicIntegratedTerm_le hh hk).trans
            ((hterm hT hH hh hk hm0 hn0 hd).trans_eq (by dsimp only [F]; ring))
        · have hs : quadraticDivisorShift h k m n ≠ 0 := fun hs =>
            hd ((quadraticDivisorShift_eq_zero_iff h k m n).1 hs)
          simp [hd, hs]
      _ = F * (∑ m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
          ∑ n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.2),
            if h * m = k * n then
              ‖shortMobiusSquareCoeff T h‖ *
                ‖shortMobiusSquareCoeff T k‖ *
                (m.divisors.card : ℝ) * (n.divisors.card : ℝ) *
                (((h * m : ℕ) : ℝ))⁻¹
            else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m _
        rw [Finset.mul_sum]
      _ ≤ F * (∑ m ∈ Finset.Icc 1 B, ∑ n ∈ Finset.Icc 1 B,
          if h * m = k * n then
            ‖shortMobiusSquareCoeff T h‖ *
              ‖shortMobiusSquareCoeff T k‖ *
              (m.divisors.card : ℝ) * (n.divisors.card : ℝ) *
              (((h * m : ℕ) : ℝ))⁻¹
          else 0) := by
        apply mul_le_mul_of_nonneg_left _ hF0
        calc
          (∑ m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
              ∑ n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.2),
                if h * m = k * n then
                  ‖shortMobiusSquareCoeff T h‖ *
                    ‖shortMobiusSquareCoeff T k‖ *
                    (m.divisors.card : ℝ) * (n.divisors.card : ℝ) *
                    (((h * m : ℕ) : ℝ))⁻¹ else 0) ≤
            ∑ m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
              ∑ n ∈ Finset.Icc 1 B,
                if h * m = k * n then
                  ‖shortMobiusSquareCoeff T h‖ *
                    ‖shortMobiusSquareCoeff T k‖ *
                    (m.divisors.card : ℝ) * (n.divisors.card : ℝ) *
                    (((h * m : ℕ) : ℝ))⁻¹ else 0 := by
              apply Finset.sum_le_sum
              intro m _hm
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · exact Finset.Icc_subset_Icc_right hBj
              · intro n _hn _hnnot
                positivity
          _ ≤ ∑ m ∈ Finset.Icc 1 B, ∑ n ∈ Finset.Icc 1 B,
                if h * m = k * n then
                  ‖shortMobiusSquareCoeff T h‖ *
                    ‖shortMobiusSquareCoeff T k‖ *
                    (m.divisors.card : ℝ) * (n.divisors.card : ℝ) *
                    (((h * m : ℕ) : ℝ))⁻¹ else 0 := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · exact Finset.Icc_subset_Icc_right hBi
              · intro m _hm _hmnot
                positivity
  unfold hughesYoungActiveFiniteDiagonal hughesYoungActiveDyadicDiagonal
  let A : ℕ → ℕ → ℝ := fun h k =>
    ∑ m ∈ Finset.Icc 1 B, ∑ n ∈ Finset.Icc 1 B,
      if h * m = k * n then
        ‖shortMobiusSquareCoeff T h‖ * ‖shortMobiusSquareCoeff T k‖ *
          (m.divisors.card : ℝ) * (n.divisors.card : ℝ) *
          (((h * m : ℕ) : ℝ))⁻¹ else 0
  have hA0 : ∀ h k, 0 ≤ A h k := by
    intro h k
    dsimp only [A]
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  calc
    ‖∑ h ∈ Finset.Icc 1 ell, ∑ k ∈ Finset.Icc 1 ell,
        ∑ ij ∈ hughesYoungActiveDyadicBoxes
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
          hughesYoungFullDyadicDiagonalBox T (hughesYoungSmallContour T)
            H h k ij.1 ij.2‖ ≤
      ∑ h ∈ Finset.Icc 1 ell, ∑ k ∈ Finset.Icc 1 ell,
        ∑ ij ∈ hughesYoungActiveDyadicBoxes
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
          ‖hughesYoungFullDyadicDiagonalBox T (hughesYoungSmallContour T)
            H h k ij.1 ij.2‖ := (norm_sum_le _ _).trans
        (Finset.sum_le_sum fun h _ => (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun k _ => norm_sum_le _ _))
    _ ≤ ∑ h ∈ Finset.Icc 1 ell, ∑ k ∈ Finset.Icc 1 ell,
        ∑ _ij ∈ hughesYoungActiveDyadicBoxes
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
          F * A h k := by
      apply Finset.sum_le_sum
      intro h hh
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum
      intro ij hij
      simpa only [A] using hbox h hh k hk ij hij
    _ ≤ ∑ h ∈ Finset.Icc 1 ell, ∑ k ∈ Finset.Icc 1 ell,
        (((K + 2 : ℕ) : ℝ) ^ 2) * (F * A h k) := by
      apply Finset.sum_le_sum
      intro h _hh
      apply Finset.sum_le_sum
      intro k _hk
      rw [Finset.sum_const, nsmul_eq_mul]
      push_cast
      have hcardNat := card_hughesYoungActiveDyadicBoxes_le
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K
      have hcard : ((hughesYoungActiveDyadicBoxes
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K).card : ℝ) ≤
          (((K + 2) ^ 2 : ℕ) : ℝ) := by exact_mod_cast hcardNat
      norm_num at hcard
      exact mul_le_mul_of_nonneg_right hcard
        (mul_nonneg hF0 (hA0 h k))
    _ = (((K + 2 : ℕ) : ℝ) ^ 2) * F *
        hughesYoungFiniteDiagonalArithmeticMajorant T ell B := by
      unfold hughesYoungFiniteDiagonalArithmeticMajorant
      dsimp only [A]
      simp_rw [Finset.mul_sum]
      ring
    _ = _ := by
      simp only [ell, B, hughesYoungActiveArithmeticCutoff]
      ring

/-- The logarithmic number of active dyadic generations costs an arbitrarily
small power of the height. -/
theorem hughesYoungGlobalDepth_add_two_le_rpow
    {δ T : ℝ} (hδ : 0 < δ) (hT : Real.exp 1 ≤ T) :
    ((hughesYoungGlobalDepth T + 2 : ℕ) : ℝ) ≤
      (100 / δ + 3) * T ^ δ := by
  have hT1 : 1 ≤ T := by linarith [Real.exp_one_gt_d9]
  have hlog0 : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hceil := Nat.ceil_lt_add_one
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 100) hlog0)
  have hlog := Real.log_le_rpow_div (zero_le_one.trans hT1) hδ
  have hpow1 : 1 ≤ T ^ δ := Real.one_le_rpow hT1 hδ.le
  unfold hughesYoungGlobalDepth
  push_cast
  exact (calc
    (⌈100 * Real.log T⌉₊ : ℝ) + 2 <
        100 * Real.log T + 3 := by linarith
    _ ≤ 100 * (T ^ δ / δ) + 3 := by gcongr
    _ ≤ (100 / δ + 3) * T ^ δ := by
      rw [show (100 / δ + 3) * T ^ δ =
          100 * (T ^ δ / δ) + 3 * T ^ δ by field_simp]
      linarith).le

/-- Uniform polynomial control of the arithmetic cutoff used by every active
dyadic diagonal box. -/
theorem hughesYoungActiveArithmeticCutoff_le
    {T : ℝ} (hT : Real.exp 1 ≤ T) :
    (hughesYoungActiveArithmeticCutoff T (hughesYoungGlobalRadius T) : ℝ) ≤
      649 * T ^ (9 : ℝ) := by
  have hT1 : 1 ≤ T := by linarith [Real.exp_one_gt_d9]
  have hcut := detectorCutoff_le_three_mul T hT1
  have hell : (((detectorCutoff T) ^ 2 : ℕ) : ℝ) ≤ 9 * T ^ (2 : ℝ) := by
    rw [Nat.cast_pow, Real.rpow_two]
    nlinarith
  have hellReal : (detectorCutoff T : ℝ) ^ 2 ≤ 9 * T ^ (2 : ℝ) := by
    simpa only [Nat.cast_pow] using hell
  have hellReal : (detectorCutoff T : ℝ) ^ 2 ≤ 9 * T ^ (2 : ℝ) := by
    simpa only [Nat.cast_pow] using hell
  have hR := hughesYoungGlobalRadius_le hT1
  have hprod : ((((detectorCutoff T) ^ 2 * (detectorCutoff T) ^ 2 *
      hughesYoungGlobalRadius T : ℕ) : ℝ)) ≤ 162 * T ^ (9 : ℝ) := by
    push_cast
    calc
      _ ≤ (9 * T ^ (2 : ℝ)) * (9 * T ^ (2 : ℝ)) *
          (2 * T ^ (5 : ℝ)) := by gcongr
      _ = 162 * T ^ (9 : ℝ) := by
        simp only [Real.rpow_ofNat]
        ring
  have hp : 1 ≤ T ^ (9 : ℝ) := Real.one_le_rpow hT1 (by norm_num)
  calc
    (hughesYoungActiveArithmeticCutoff T (hughesYoungGlobalRadius T) : ℝ) =
        4 * ((((detectorCutoff T) ^ 2 * (detectorCutoff T) ^ 2 *
          hughesYoungGlobalRadius T : ℕ) : ℝ)) + 1 := by
          unfold hughesYoungActiveArithmeticCutoff
          push_cast
          ring
    _ ≤ 4 * (162 * T ^ (9 : ℝ)) + 1 := by gcongr
    _ ≤ 649 * T ^ (9 : ℝ) := by nlinarith

/-- Polynomial control of the active arithmetic cutoff at the corrected
conductor radius. -/
theorem hughesYoungConductorArithmeticCutoff_le
    {T : ℝ} (hT : Real.exp 1 ≤ T) :
    (hughesYoungActiveArithmeticCutoff T (hughesYoungConductorRadius T) : ℝ) ≤
      649 * T ^ (7 : ℝ) := by
  have hT1 : 1 ≤ T := by linarith [Real.exp_one_gt_d9]
  have hcut := detectorCutoff_le_three_mul T hT1
  have hell : (((detectorCutoff T) ^ 2 : ℕ) : ℝ) ≤ 9 * T ^ (2 : ℝ) := by
    rw [Nat.cast_pow, Real.rpow_two]
    nlinarith
  have hellReal : (detectorCutoff T : ℝ) ^ 2 ≤ 9 * T ^ (2 : ℝ) := by
    simpa only [Nat.cast_pow] using hell
  have hR := hughesYoungConductorRadius_le_two_mul_cube hT1
  have hprod : ((((detectorCutoff T) ^ 2 * (detectorCutoff T) ^ 2 *
      hughesYoungConductorRadius T : ℕ) : ℝ)) ≤ 162 * T ^ (7 : ℝ) := by
    push_cast
    calc
      _ ≤ (9 * T ^ (2 : ℝ)) * (9 * T ^ (2 : ℝ)) *
          (2 * T ^ (3 : ℝ)) := by
        gcongr
      _ = 162 * T ^ (7 : ℝ) := by
        simp only [Real.rpow_ofNat]
        ring
  have hp : 1 ≤ T ^ (7 : ℝ) := Real.one_le_rpow hT1 (by norm_num)
  calc
    (hughesYoungActiveArithmeticCutoff T (hughesYoungConductorRadius T) : ℝ) =
        4 * ((((detectorCutoff T) ^ 2 * (detectorCutoff T) ^ 2 *
          hughesYoungConductorRadius T : ℕ) : ℝ)) + 1 := by
      unfold hughesYoungActiveArithmeticCutoff
      push_cast
      ring
    _ ≤ 4 * (162 * T ^ (7 : ℝ)) + 1 := by gcongr
    _ ≤ 649 * T ^ (7 : ℝ) := by nlinarith

/-- The combined mollifier and active-box cutoff remains polynomial at the
conductor radius.  The deliberately loose exponent `11` lets the generic
diagonal epsilon-assembly be reused verbatim. -/
theorem hughesYoungConductorCombinedArithmeticCutoff_le
    {T : ℝ} (hT : Real.exp 1 ≤ T) :
    ((((detectorCutoff T) ^ 2 *
      hughesYoungActiveArithmeticCutoff T (hughesYoungConductorRadius T) : ℕ) : ℝ)) ≤
      5841 * T ^ (11 : ℝ) := by
  have hT1 : 1 ≤ T := by linarith [Real.exp_one_gt_d9]
  have hcut := detectorCutoff_le_three_mul T hT1
  have hell : (((detectorCutoff T) ^ 2 : ℕ) : ℝ) ≤ 9 * T ^ (2 : ℝ) := by
    rw [Nat.cast_pow, Real.rpow_two]
    nlinarith
  have hellReal : (detectorCutoff T : ℝ) ^ 2 ≤ 9 * T ^ (2 : ℝ) := by
    simpa only [Nat.cast_pow] using hell
  have hB := hughesYoungConductorArithmeticCutoff_le hT
  have hTpow : T ^ (9 : ℝ) ≤ T ^ (11 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num)
  calc
    _ = (detectorCutoff T : ℝ) ^ 2 *
        (hughesYoungActiveArithmeticCutoff T (hughesYoungConductorRadius T) : ℝ) := by
      push_cast
      ring
    _ ≤ (9 * T ^ (2 : ℝ)) * (649 * T ^ (7 : ℝ)) := by
      gcongr
    _ = 5841 * T ^ (9 : ℝ) := by
      simp only [Real.rpow_ofNat]
      ring
    _ ≤ 5841 * T ^ (11 : ℝ) := by gcongr

/-- The combined mollifier and active-box cutoff is polynomial in the
height. -/
theorem hughesYoungCombinedArithmeticCutoff_le
    {T : ℝ} (hT : Real.exp 1 ≤ T) :
    ((((detectorCutoff T) ^ 2 *
      hughesYoungActiveArithmeticCutoff T (hughesYoungGlobalRadius T) : ℕ) : ℝ)) ≤
      5841 * T ^ (11 : ℝ) := by
  have hT1 : 1 ≤ T := by linarith [Real.exp_one_gt_d9]
  have hcut := detectorCutoff_le_three_mul T hT1
  have hell : (((detectorCutoff T) ^ 2 : ℕ) : ℝ) ≤ 9 * T ^ (2 : ℝ) := by
    rw [Nat.cast_pow, Real.rpow_two]
    nlinarith
  have hellReal : (detectorCutoff T : ℝ) ^ 2 ≤ 9 * T ^ (2 : ℝ) := by
    simpa only [Nat.cast_pow] using hell
  have hB := hughesYoungActiveArithmeticCutoff_le hT
  calc
    _ = (detectorCutoff T : ℝ) ^ 2 *
        (hughesYoungActiveArithmeticCutoff T (hughesYoungGlobalRadius T) : ℝ) := by
          push_cast
          ring
    _ ≤ (9 * T ^ (2 : ℝ)) * (649 * T ^ (9 : ℝ)) := by gcongr
    _ = 5841 * T ^ (11 : ℝ) := by
      simp only [Real.rpow_ofNat]
      ring

/-- The literal active diagonal with its chosen finite radius is reduced to
one explicit epsilon-power arithmetic expression. -/
theorem exists_norm_hughesYoungActiveFiniteDiagonal_le_power
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ C W ca cd : ℝ,
      0 < C ∧ 0 < W ∧ 0 < ca ∧ 0 < cd ∧
      ∀ {T H : ℝ} {R K : ℕ}, Real.exp 1 ≤ T → 0 ≤ H →
        ‖hughesYoungActiveFiniteDiagonal T H R K‖ ≤
          ((K + 2 : ℕ) : ℝ) ^ 2 *
          ((15 * T / 4) * (1 / Real.pi) *
            (Real.log T * Real.exp (4 * C) * W *
              Real.sqrt (Real.pi / 80))) *
          ca ^ 2 * cd ^ 4 *
          ((((detectorCutoff T) ^ 2 *
            hughesYoungActiveArithmeticCutoff T R : ℕ) : ℝ)) ^ (6 * δ) *
          (((harmonic ((detectorCutoff T) ^ 2 *
            hughesYoungActiveArithmeticCutoff T R) : ℚ) : ℝ)) := by
  obtain ⟨C, W, hC, hW, hdiag⟩ :=
    exists_norm_hughesYoungActiveFiniteDiagonal_le
  obtain ⟨ca, hca, hcoeff⟩ := shortMobiusSquareCoeff_bound δ hδ
  obtain ⟨cd, hcd, hdiv⟩ := divisorCountBound_native δ hδ
  refine ⟨C, W, ca, cd, hC, hW, hca, hcd, ?_⟩
  intro T H R K hT hH
  let ell : ℕ := (detectorCutoff T) ^ 2
  let B : ℕ := hughesYoungActiveArithmeticCutoff T R
  let cutoff : ℕ := ell * B
  let F : ℝ := (15 * T / 4) * (1 / Real.pi) *
    (Real.log T * Real.exp (4 * C) * W * Real.sqrt (Real.pi / 80))
  have hT0 : 0 < T := (Real.exp_pos 1).trans_le hT
  have hF0 : 0 ≤ F := by
    have hT1 : 1 ≤ T := by linarith [Real.exp_one_gt_d9]
    have hlog : 0 ≤ Real.log T := Real.log_nonneg hT1
    dsimp only [F]
    positivity
  have hdiag' := hdiag (T := T) (H := H) (R := R) (K := K) hT hH
  have hmajor := hughesYoungFiniteDiagonalArithmeticMajorant_le T ell B
  have hsmooth := smoothTwistedDiagonalMajorant_le
    (ell := ell) (cutoff := cutoff) hT0.le
    (shortMobiusSquareCoeff T) hδ.le hca.le hcd.le
    (fun h hh => hcoeff T h (Finset.mem_Icc.mp hh).1) hdiv
  have hsum :
      (∑ q ∈ Finset.Icc 1 cutoff,
        smoothTwistedDiagonalFiber ell q (shortMobiusSquareCoeff T) ^ 2 *
          (q : ℝ)⁻¹) ≤
        ca ^ 2 * cd ^ 4 * (cutoff : ℝ) ^ (6 * δ) *
          (((harmonic cutoff : ℚ) : ℝ)) := by
    unfold smoothTwistedDiagonalMajorant at hsmooth
    have hfactor : 0 < 5 * T / 2 := by positivity
    nlinarith
  change _ ≤ (((K + 2 : ℕ) : ℝ) ^ 2) * F *
    ca ^ 2 * cd ^ 4 * (cutoff : ℝ) ^ (6 * δ) *
      (((harmonic cutoff : ℚ) : ℝ))
  calc
    _ ≤ (((K + 2 : ℕ) : ℝ) ^ 2) * F *
        hughesYoungFiniteDiagonalArithmeticMajorant T ell B := by
      simpa only [F, ell, B] using hdiag'
    _ ≤ (((K + 2 : ℕ) : ℝ) ^ 2) * F *
        (∑ q ∈ Finset.Icc 1 cutoff,
          smoothTwistedDiagonalFiber ell q (shortMobiusSquareCoeff T) ^ 2 *
            (q : ℝ)⁻¹) := by
      gcongr
    _ ≤ (((K + 2 : ℕ) : ℝ) ^ 2) * F *
        (ca ^ 2 * cd ^ 4 * (cutoff : ℝ) ^ (6 * δ) *
          (((harmonic cutoff : ℚ) : ℝ))) := by
      gcongr
    _ = _ := by ring

/-- The exact active Hughes--Young diagonal has the required `T^(1+ε)`
growth for any radius whose combined arithmetic cutoff has the displayed
fixed polynomial bound. -/
theorem hughesYoungActiveFiniteDiagonal_epsilonPowerBound_of_radius
    (radius : ℝ → ℕ)
    (hcutoff : ∀ {T : ℝ}, Real.exp 1 ≤ T →
      ((((detectorCutoff T) ^ 2 *
        hughesYoungActiveArithmeticCutoff T (radius T) : ℕ) : ℝ)) ≤
          5841 * T ^ (11 : ℝ)) :
    EpsilonPowerBound
      (fun T => ‖hughesYoungActiveFiniteDiagonal T (T / 8)
        (radius T) (hughesYoungGlobalDepth T)‖)
      (fun T => T) := by
  intro ε hε
  let δ : ℝ := ε / 100
  have hδ : 0 < δ := div_pos hε (by norm_num)
  obtain ⟨C, W, ca, cd, hC, hW, hca, hcd, hdiag⟩ :=
    exists_norm_hughesYoungActiveFiniteDiagonal_le_power δ hδ
  let A : ℝ :=
    (100 / δ + 3) ^ 2 *
      ((15 / 4) * (1 / Real.pi) *
        (δ⁻¹ * Real.exp (4 * C) * W * Real.sqrt (Real.pi / 80))) *
      ca ^ 2 * cd ^ 4 * (1 + δ⁻¹) * (5841 : ℝ) ^ (7 * δ)
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  apply IsBigO.of_bound A
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with T hT
  have hT1 : 1 ≤ T := by linarith [Real.exp_one_gt_d9]
  have hT0 : 0 < T := zero_lt_one.trans_le hT1
  let Q : ℕ := (detectorCutoff T) ^ 2 *
    hughesYoungActiveArithmeticCutoff T (radius T)
  have hQone : 1 ≤ Q := by
    dsimp only [Q]
    have hc : 0 < detectorCutoff T := by simp [detectorCutoff]
    have hB : 0 < hughesYoungActiveArithmeticCutoff T
        (radius T) := by
      unfold hughesYoungActiveArithmeticCutoff
      omega
    exact Nat.mul_pos (pow_pos hc 2) hB
  have hQ0 : (0 : ℝ) ≤ Q := by positivity
  have hQbound : (Q : ℝ) ≤ 5841 * T ^ (11 : ℝ) := by
    simpa only [Q] using hcutoff hT
  have hHarm := harmonic_le_epsilon_rpow hδ Q
  have hmax : max 1 ((Q : ℝ) ^ δ) = (Q : ℝ) ^ δ :=
    max_eq_right (Real.one_le_rpow (by exact_mod_cast hQone) hδ.le)
  rw [hmax] at hHarm
  have hQpower : (Q : ℝ) ^ (7 * δ) ≤
      (5841 : ℝ) ^ (7 * δ) * T ^ (77 * δ) := by
    calc
      (Q : ℝ) ^ (7 * δ) ≤
          (5841 * T ^ (11 : ℝ)) ^ (7 * δ) := by
            exact Real.rpow_le_rpow hQ0 hQbound (by positivity)
      _ = (5841 : ℝ) ^ (7 * δ) *
          (T ^ (11 : ℝ)) ^ (7 * δ) := by
            rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hT0.le _)]
      _ = (5841 : ℝ) ^ (7 * δ) * T ^ (77 * δ) := by
            rw [← Real.rpow_mul hT0.le]
            congr 1
            ring
  have hQcombine : (Q : ℝ) ^ (6 * δ) *
      (((harmonic Q : ℚ) : ℝ)) ≤
        (1 + δ⁻¹) * (5841 : ℝ) ^ (7 * δ) * T ^ (77 * δ) := by
    calc
      _ ≤ (Q : ℝ) ^ (6 * δ) *
          ((1 + δ⁻¹) * (Q : ℝ) ^ δ) := by
            gcongr
      _ = (1 + δ⁻¹) * (Q : ℝ) ^ (7 * δ) := by
            have hQRpos : (0 : ℝ) < Q := by exact_mod_cast hQone
            rw [show 7 * δ = 6 * δ + δ by ring,
              Real.rpow_add hQRpos]
            ring
      _ ≤ (1 + δ⁻¹) *
          ((5841 : ℝ) ^ (7 * δ) * T ^ (77 * δ)) :=
            mul_le_mul_of_nonneg_left hQpower (by positivity)
      _ = _ := by ring
  have hdepth := hughesYoungGlobalDepth_add_two_le_rpow hδ hT
  have hdepthSq : (((hughesYoungGlobalDepth T + 2 : ℕ) : ℝ) ^ 2) ≤
      (100 / δ + 3) ^ 2 * T ^ (2 * δ) := by
    calc
      _ ≤ ((100 / δ + 3) * T ^ δ) ^ 2 := by gcongr
      _ = (100 / δ + 3) ^ 2 * T ^ (2 * δ) := by
        rw [mul_pow]
        rw [show (T ^ δ) ^ 2 = T ^ (2 * δ) by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]
          ring_nf]
  have hlog : Real.log T ≤ δ⁻¹ * T ^ δ := by
    have := Real.log_le_rpow_div hT0.le hδ
    simpa [div_eq_mul_inv, mul_comm] using this
  let G : ℝ := (15 / 4) * (1 / Real.pi) *
    (δ⁻¹ * Real.exp (4 * C) * W * Real.sqrt (Real.pi / 80))
  have hfactor0 : 0 ≤ (15 * T / 4) * (1 / Real.pi) *
      (Real.log T * Real.exp (4 * C) * W * Real.sqrt (Real.pi / 80)) := by
    have hlog0 : 0 ≤ Real.log T := Real.log_nonneg hT1
    positivity
  have hfactor : (15 * T / 4) * (1 / Real.pi) *
      (Real.log T * Real.exp (4 * C) * W * Real.sqrt (Real.pi / 80)) ≤
        G * T ^ (1 + δ) := by
    calc
      _ ≤ (15 * T / 4) * (1 / Real.pi) *
          ((δ⁻¹ * T ^ δ) * Real.exp (4 * C) * W *
            Real.sqrt (Real.pi / 80)) := by gcongr
      _ = G * T ^ (1 + δ) := by
        dsimp only [G]
        have hp : T * T ^ δ = T ^ (1 + δ) := by
          calc
            T * T ^ δ = T ^ (1 : ℝ) * T ^ δ := by rw [Real.rpow_one]
            _ = T ^ ((1 : ℝ) + δ) := (Real.rpow_add hT0 1 δ).symm
        rw [← hp]
        ring
  have hharm0 : 0 ≤ (((harmonic Q : ℚ) : ℝ)) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    positivity
  have hpowcombine : T ^ (2 * δ) * T ^ (1 + δ) * T ^ (77 * δ) =
      T ^ (1 + 80 * δ) := by
    rw [← Real.rpow_add hT0, ← Real.rpow_add hT0]
    congr 1
    ring
  have hraw := hdiag (T := T) (H := T / 8)
    (R := radius T) (K := hughesYoungGlobalDepth T)
    hT (by positivity)
  have hbound :
      ‖hughesYoungActiveFiniteDiagonal T (T / 8)
        (radius T) (hughesYoungGlobalDepth T)‖ ≤
        A * T ^ (1 + 80 * δ) := by
    calc
      _ ≤ (((hughesYoungGlobalDepth T + 2 : ℕ) : ℝ) ^ 2) *
          ((15 * T / 4) * (1 / Real.pi) *
            (Real.log T * Real.exp (4 * C) * W * Real.sqrt (Real.pi / 80))) *
          ca ^ 2 * cd ^ 4 * (Q : ℝ) ^ (6 * δ) *
          (((harmonic Q : ℚ) : ℝ)) := by simpa only [Q] using hraw
      _ = (((hughesYoungGlobalDepth T + 2 : ℕ) : ℝ) ^ 2) *
          ((15 * T / 4) * (1 / Real.pi) *
            (Real.log T * Real.exp (4 * C) * W * Real.sqrt (Real.pi / 80))) *
          ca ^ 2 * cd ^ 4 *
          ((Q : ℝ) ^ (6 * δ) * (((harmonic Q : ℚ) : ℝ))) := by ring
      _ ≤ ((100 / δ + 3) ^ 2 * T ^ (2 * δ)) *
          (G * T ^ (1 + δ)) * ca ^ 2 * cd ^ 4 *
          ((1 + δ⁻¹) * (5841 : ℝ) ^ (7 * δ) *
            T ^ (77 * δ)) := by gcongr
      _ = A * T ^ (1 + 80 * δ) := by
        dsimp only [A, G]
        rw [← hpowcombine]
        ring
  have hexp : 1 + 80 * δ ≤ 1 + ε := by
    dsimp only [δ]
    linarith
  have hpow : T ^ (1 + 80 * δ) ≤ T ^ (1 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hT1 hexp
  have htarget : ‖T ^ ε * |T|‖ = T ^ (1 + ε) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      (Real.rpow_nonneg hT0.le _) (abs_nonneg T)), abs_of_pos hT0]
    calc
      T ^ ε * T = T ^ ε * T ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = T ^ (ε + 1) := (Real.rpow_add hT0 ε 1).symm
      _ = T ^ (1 + ε) := by ring_nf
  rw [Real.norm_eq_abs, abs_abs,
    abs_of_nonneg (norm_nonneg (hughesYoungActiveFiniteDiagonal T (T / 8)
      (radius T) (hughesYoungGlobalDepth T))), htarget]
  exact hbound.trans (mul_le_mul_of_nonneg_left hpow hA)

/-- The diagonal bound at the original oversized radius. -/
theorem hughesYoungActiveFiniteDiagonal_epsilonPowerBound :
    EpsilonPowerBound
      (fun T => ‖hughesYoungActiveFiniteDiagonal T (T / 8)
        (hughesYoungGlobalRadius T) (hughesYoungGlobalDepth T)‖)
      (fun T => T) :=
  hughesYoungActiveFiniteDiagonal_epsilonPowerBound_of_radius
    hughesYoungGlobalRadius (fun hT =>
      hughesYoungCombinedArithmeticCutoff_le hT)

/-- The diagonal bound at the conductor-scale radius used by the native
Hughes--Young consumer. -/
theorem hughesYoungConductorFiniteDiagonal_epsilonPowerBound :
    EpsilonPowerBound
      (fun T => ‖hughesYoungActiveFiniteDiagonal T (T / 8)
        (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)‖)
      (fun T => T) :=
  hughesYoungActiveFiniteDiagonal_epsilonPowerBound_of_radius
    hughesYoungConductorRadius (fun hT =>
      hughesYoungConductorCombinedArithmeticCutoff_le hT)

/-! ## Hughes--Young equation (80) at the native conductor scale -/

theorem detectorCutoff_sq_le_nine_mul_rpow_one_fiftieth
    {T : ℝ} (hT : 1 ≤ T) :
    (((detectorCutoff T) ^ 2 : ℕ) : ℝ) ≤
      9 * T ^ (1 / 50 : ℝ) := by
  have hcut := detectorCutoff_le_three_mul_rpow_one_hundredth hT
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  calc
    (((detectorCutoff T) ^ 2 : ℕ) : ℝ) =
        (detectorCutoff T : ℝ) ^ 2 := by norm_num
    _ ≤ (3 * T ^ (1 / 100 : ℝ)) ^ 2 := by gcongr
    _ = 9 * T ^ (1 / 50 : ℝ) := by
      rw [mul_pow]
      rw [show (T ^ (1 / 100 : ℝ)) ^ 2 = T ^ (1 / 50 : ℝ) by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]
        congr 1
        norm_num]
      norm_num

theorem detectorSquareProduct_mul_conductorRadius_le
    {T : ℝ} (hT : 1 ≤ T) :
    (((((detectorCutoff T) ^ 2 : ℕ) : ℝ) ^ 2) *
        (hughesYoungConductorRadius T : ℝ)) ≤
      162 * T ^ (41 / 20 : ℝ) := by
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hell := detectorCutoff_sq_le_nine_mul_rpow_one_fiftieth hT
  have hR := hughesYoungConductorRadius_le_two_mul_rpow hT
  calc
    _ ≤ (9 * T ^ (1 / 50 : ℝ)) ^ 2 *
        (2 * T ^ (201 / 100 : ℝ)) := by gcongr
    _ = 162 * T ^ (41 / 20 : ℝ) := by
      rw [mul_pow]
      rw [show (T ^ (1 / 50 : ℝ)) ^ 2 = T ^ (1 / 25 : ℝ) by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]
        congr 1
        norm_num]
      calc
        9 ^ 2 * T ^ (1 / 25 : ℝ) *
            (2 * T ^ (201 / 100 : ℝ)) =
          162 * (T ^ (1 / 25 : ℝ) * T ^ (201 / 100 : ℝ)) := by ring
        _ = 162 * T ^ (41 / 20 : ℝ) := by
          rw [← Real.rpow_add hT0]
          congr 1
          ring

theorem hughesYoungDFISmoothingScale_rpow_nine_fourths_le
    {T : ℝ} (hT : 1 ≤ T) :
    hughesYoungDFISmoothingScale T ^ (9 / 4 : ℝ) ≤
      (8 : ℝ) ^ (9 / 4 : ℝ) * T ^ (9 / 40000 : ℝ) := by
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  unfold hughesYoungDFISmoothingScale
  rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hT0.le _)]
  rw [← Real.rpow_mul hT0.le]
  apply le_of_eq
  congr 1
  ring

/-- Hughes--Young equation (80), after summing every large comparable DFI
box at the actual mollifier cutoff and conductor radius.  The proof keeps
the fixed exponent `33159 / 40000` visible; in particular this is a genuine
power saving before the epsilon losses are absorbed. -/
theorem hughesYoungConductorLargeDFIPointwiseDiscrepancy_epsilonPowerBound :
    EpsilonPowerBound
      (fun T => ‖hughesYoungActiveLargeDFIPointwiseDiscrepancy T
        (hughesYoungDFISmoothingScale T) (hughesYoungConductorRadius T)
        (hughesYoungGlobalDepth T)‖)
      (fun T => T) := by
  intro ε hε
  let δ : ℝ := min (ε / 100) (1 / 100)
  have hδ0 : 0 < δ := by
    dsimp only [δ]
    exact lt_min (div_pos hε (by norm_num)) (by norm_num)
  have hδ4 : δ < 4 := (min_le_right _ _).trans_lt (by norm_num)
  obtain ⟨Cγ, C, L, hCγ, hC, hL, hDFI⟩ :=
    exists_norm_hughesYoungActiveLargeDFIPointwiseDiscrepancy_le_equation80
      δ hδ0 hδ4
  obtain ⟨ca, hca, hcoeff⟩ := shortMobiusSquareCoeff_bound δ hδ0
  let D : ℝ := 100 / δ + 3
  let E : ℝ := 34759 / 40000 + (509 / 100) * δ
  let A : ℝ :=
    81 * D ^ 2 *
      ((16 * (4 : ℝ) ^ (1 / 4 : ℝ)) *
        (δ⁻¹ * Real.exp (4 * Cγ) * C * L)) *
      (ca * (9 : ℝ) ^ δ) ^ 2 * 9 *
      (8 : ℝ) ^ (9 / 4 : ℝ) *
      (162 : ℝ) ^ (3 / 8 + δ) * 81
  have hA : 0 ≤ A := by
    dsimp only [A, D]
    positivity
  apply IsBigO.of_bound A
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with T hT
  have hT1 : 1 ≤ T := by linarith [Real.exp_one_gt_d9]
  have hT0 : 0 < T := zero_lt_one.trans_le hT1
  let ell : ℝ := (((detectorCutoff T) ^ 2 : ℕ) : ℝ)
  have hell0 : 0 ≤ ell := by dsimp only [ell]; positivity
  have hell : ell ≤ 9 * T ^ (1 / 50 : ℝ) := by
    simpa only [ell] using detectorCutoff_sq_le_nine_mul_rpow_one_fiftieth hT1
  have hellSq : ell ^ 2 ≤ 81 * T ^ (1 / 25 : ℝ) := by
    calc
      ell ^ 2 ≤ (9 * T ^ (1 / 50 : ℝ)) ^ 2 := by gcongr
      _ = 81 * T ^ (1 / 25 : ℝ) := by
        rw [mul_pow]
        rw [show (T ^ (1 / 50 : ℝ)) ^ 2 = T ^ (1 / 25 : ℝ) by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]
          congr 1
          norm_num]
        norm_num
  have hellPow : ell ^ δ ≤
      (9 : ℝ) ^ δ * T ^ (δ / 50) := by
    calc
      ell ^ δ ≤ (9 * T ^ (1 / 50 : ℝ)) ^ δ :=
        Real.rpow_le_rpow hell0 hell hδ0.le
      _ = (9 : ℝ) ^ δ * (T ^ (1 / 50 : ℝ)) ^ δ := by
        rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hT0.le _)]
      _ = (9 : ℝ) ^ δ * T ^ (δ / 50) := by
        rw [← Real.rpow_mul hT0.le]
        congr 1
        ring
  have hcoeffUniform : ∀ n ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ‖shortMobiusSquareCoeff T n‖ ≤ ca * ell ^ δ := by
    intro n hn
    have hnle : (n : ℝ) ≤ ell := by
      dsimp only [ell]
      exact_mod_cast (Finset.mem_Icc.mp hn).2
    exact (hcoeff T n (Finset.mem_Icc.mp hn).1).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg n) hnle hδ0.le) hca.le)
  have hcoeffSq : (ca * ell ^ δ) ^ 2 ≤
      (ca * (9 : ℝ) ^ δ) ^ 2 * T ^ (δ / 25) := by
    calc
      (ca * ell ^ δ) ^ 2 ≤
          (ca * ((9 : ℝ) ^ δ * T ^ (δ / 50))) ^ 2 := by gcongr
      _ = (ca * (9 : ℝ) ^ δ) ^ 2 * T ^ (δ / 25) := by
        calc
          (ca * ((9 : ℝ) ^ δ * T ^ (δ / 50))) ^ 2 =
              (ca * (9 : ℝ) ^ δ) ^ 2 * (T ^ (δ / 50)) ^ 2 := by ring
          _ = (ca * (9 : ℝ) ^ δ) ^ 2 * T ^ (δ / 25) := by
            rw [show (T ^ (δ / 50)) ^ 2 = T ^ (δ / 25) by
              rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]
              congr 1
              ring]
  have hdepth := hughesYoungGlobalDepth_add_two_le_rpow hδ0 hT
  have hdepthSq :
      (((hughesYoungGlobalDepth T + 2 : ℕ) : ℝ) ^ 2) ≤
        D ^ 2 * T ^ (2 * δ) := by
    calc
      _ ≤ (D * T ^ δ) ^ 2 := by gcongr
      _ = D ^ 2 * T ^ (2 * δ) := by
        rw [mul_pow]
        rw [show (T ^ δ) ^ 2 = T ^ (2 * δ) by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]
          congr 1
          ring]
  have hlog : Real.log T ≤ δ⁻¹ * T ^ δ := by
    have hraw := Real.log_le_rpow_div hT0.le hδ0
    simpa only [div_eq_mul_inv, mul_comm] using hraw
  have hP := hughesYoungDFISmoothingScale_rpow_nine_fourths_le hT1
  have hprod := detectorSquareProduct_mul_conductorRadius_le hT1
  have hprodPow :
      (ell ^ 2 * (hughesYoungConductorRadius T : ℝ)) ^ (3 / 8 + δ) ≤
        (162 : ℝ) ^ (3 / 8 + δ) *
          T ^ ((41 / 20) * (3 / 8 + δ)) := by
    have hq : 0 ≤ 3 / 8 + δ := by positivity
    calc
      _ ≤ (162 * T ^ (41 / 20 : ℝ)) ^ (3 / 8 + δ) := by
        exact Real.rpow_le_rpow
          (mul_nonneg (sq_nonneg ell)
            (Nat.cast_nonneg (hughesYoungConductorRadius T)))
          (by simpa only [ell] using hprod) hq
      _ = (162 : ℝ) ^ (3 / 8 + δ) *
          (T ^ (41 / 20 : ℝ)) ^ (3 / 8 + δ) := by
        rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hT0.le _)]
      _ = (162 : ℝ) ^ (3 / 8 + δ) *
          T ^ ((41 / 20) * (3 / 8 + δ)) := by
        rw [← Real.rpow_mul hT0.le]
  have hP1 : 1 ≤ hughesYoungDFISmoothingScale T :=
    one_le_hughesYoungDFISmoothingScale hT1
  have hsource := hDFI (T := T) (P := hughesYoungDFISmoothingScale T)
    (R := hughesYoungConductorRadius T) (K := hughesYoungGlobalDepth T) hT hP1
  have hmajor := hughesYoungActiveLargeDFIEquation80ErrorMajorant_le
    (Cγ := Cγ) (C := C) (L := L) (ε := δ) (T := T)
      (P := hughesYoungDFISmoothingScale T) (A := ca * ell ^ δ)
      (R := hughesYoungConductorRadius T) (K := hughesYoungGlobalDepth T)
      hT (zero_le_one.trans hP1) hC.le hL.le hδ0.le
      (mul_nonneg hca.le (Real.rpow_nonneg hell0 _)) hcoeffUniform
  have hfixed : 34759 / 40000 + (509 / 100) * δ ≤
      9 / 10 + 6 * δ := by linarith
  have hδeps : 9 / 10 + 6 * δ ≤ 1 + ε := by
    have hd : δ ≤ ε / 100 := min_le_left _ _
    linarith
  have hEeps : E ≤ 1 + ε := by
    dsimp only [E]
    exact hfixed.trans hδeps
  have hpowE : T ^ E ≤ T ^ (1 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hT1 hEeps
  have hinner0 : 0 ≤
      (16 * (4 : ℝ) ^ (1 / 4 : ℝ)) *
        (Real.log T * Real.exp (4 * Cγ) * C * L) *
        (ca * ell ^ δ) ^ 2 * ell *
        hughesYoungDFISmoothingScale T ^ (9 / 4 : ℝ) *
        (ell ^ 2 * (hughesYoungConductorRadius T : ℝ)) ^ (3 / 8 + δ) *
        ell ^ 2 := by
    have hlog0 : 0 ≤ Real.log T := Real.log_nonneg hT1
    positivity
  have hassembled :
      ell ^ 2 * (((hughesYoungGlobalDepth T + 2 : ℕ) : ℝ) ^ 2) *
        ((16 * (4 : ℝ) ^ (1 / 4 : ℝ)) *
          (Real.log T * Real.exp (4 * Cγ) * C * L) *
          (ca * ell ^ δ) ^ 2 * ell *
          hughesYoungDFISmoothingScale T ^ (9 / 4 : ℝ) *
          (ell ^ 2 * (hughesYoungConductorRadius T : ℝ)) ^ (3 / 8 + δ) *
          ell ^ 2) ≤
        A * T ^ E := by
    calc
      _ ≤ (81 * T ^ (1 / 25 : ℝ)) *
          (D ^ 2 * T ^ (2 * δ)) *
          ((16 * (4 : ℝ) ^ (1 / 4 : ℝ)) *
            ((δ⁻¹ * T ^ δ) * Real.exp (4 * Cγ) * C * L) *
            ((ca * (9 : ℝ) ^ δ) ^ 2 * T ^ (δ / 25)) *
            (9 * T ^ (1 / 50 : ℝ)) *
            ((8 : ℝ) ^ (9 / 4 : ℝ) * T ^ (9 / 40000 : ℝ)) *
            ((162 : ℝ) ^ (3 / 8 + δ) *
              T ^ ((41 / 20) * (3 / 8 + δ))) *
            (81 * T ^ (1 / 25 : ℝ))) := by gcongr
      _ = A * T ^ E := by
        dsimp only [A, E]
        rw [show T ^ (34759 / 40000 + (509 / 100) * δ) =
            T ^ (1 / 25 : ℝ) * T ^ (2 * δ) * T ^ δ *
              T ^ (δ / 25) * T ^ (1 / 50 : ℝ) *
              T ^ (9 / 40000 : ℝ) *
              T ^ ((41 / 20) * (3 / 8 + δ)) *
              T ^ (1 / 25 : ℝ) by
          rw [← Real.rpow_add hT0, ← Real.rpow_add hT0,
            ← Real.rpow_add hT0, ← Real.rpow_add hT0,
            ← Real.rpow_add hT0, ← Real.rpow_add hT0,
            ← Real.rpow_add hT0]
          congr 1
          ring]
        ring
  have hnorm :
      ‖hughesYoungActiveLargeDFIPointwiseDiscrepancy T
        (hughesYoungDFISmoothingScale T) (hughesYoungConductorRadius T)
        (hughesYoungGlobalDepth T)‖ ≤ A * T ^ E := by
    exact hsource.trans (hmajor.trans (by simpa only [ell] using hassembled))
  have htarget : ‖T ^ ε * |T|‖ = T ^ (1 + ε) := by
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (Real.rpow_nonneg hT0.le _) (abs_nonneg T)), abs_of_pos hT0]
    calc
      T ^ ε * T = T ^ ε * T ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = T ^ (ε + 1) := (Real.rpow_add hT0 ε 1).symm
      _ = T ^ (1 + ε) := by ring_nf
  rw [Real.norm_eq_abs, abs_abs,
    abs_of_nonneg (norm_nonneg
      (hughesYoungActiveLargeDFIPointwiseDiscrepancy T
        (hughesYoungDFISmoothingScale T) (hughesYoungConductorRadius T)
        (hughesYoungGlobalDepth T))), htarget]
  exact hnorm.trans (mul_le_mul_of_nonneg_left hpowE hA)

end RiemannZeta.GuthMaynard

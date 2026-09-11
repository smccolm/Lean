import Tao2026.LargeSieveCircle
import Tao2026.WeylDifferencing
import Mathlib.Analysis.PSeries

/-!
# Separated-frequency Fejér large sieve

This file proves an explicit classical large-sieve inequality for finite real
circle frequencies separated by `1 / L`. Centered representatives and radial
bins give the bounded packing multiplicity needed to sum the squared
Dirichlet (Fejér) kernel without a logarithmic loss.
-/

open Finset
open scoped BigOperators ComplexConjugate

namespace Tao2026

noncomputable section

theorem circleDirichletKernel_eq_phaseExponentialSum
    (H : ℕ) (theta : ℝ) :
    circleDirichletKernel H theta =
      phaseExponentialSum (fun n => (n : ℝ) * theta) H := by
  unfold circleDirichletKernel phaseExponentialSum phaseExponentialSequence
  simpa using (Fin.sum_univ_eq_sum_range
    (fun n => standardAdditiveCharacter ((n : ℝ) * theta)) H)

theorem circleFejerKernel_le_inv_distance_sq
    (H : ℕ) {theta : ℝ} (htheta : 0 < nearestIntegerDistance theta) :
    circleFejerKernel H theta ≤
      1 / (4 * nearestIntegerDistance theta ^ 2) := by
  rw [circleFejerKernel, Complex.normSq_eq_norm_sq,
    circleDirichletKernel_eq_phaseExponentialSum]
  have hnorm := norm_phaseExponentialSum_affine_le_nearestIntegerDistance
    theta 0 H htheta
  have hnorm' :
      ‖phaseExponentialSum (fun n => (n : ℝ) * theta) H‖ ≤
        1 / (2 * nearestIntegerDistance theta) := by
    simpa using hnorm
  have hnonneg : 0 ≤
      ‖phaseExponentialSum (fun n => (n : ℝ) * theta) H‖ := norm_nonneg _
  calc
    ‖phaseExponentialSum (fun n => (n : ℝ) * theta) H‖ ^ 2 ≤
        (1 / (2 * nearestIntegerDistance theta)) ^ 2 := by
      exact (sq_le_sq₀ hnonneg (by positivity)).2 hnorm'
    _ = 1 / (4 * nearestIntegerDistance theta ^ 2) := by ring

def indexFiber {A : Type*} (S : Finset A) (bin : A → ℕ) (d : ℕ) :
    Finset A := S.filter fun a => bin a = d

theorem sum_kernel_le_eight_mul_sq
    {A : Type*} [Fintype A] [DecidableEq A] (a : A) (L : ℕ)
    (K : A → ℝ) (bin : A → ℕ)
    (hdiag : K a ≤ 4 * (L : ℝ) ^ 2)
    (hbin : ∀ b ∈ (Finset.univ.erase a), 1 ≤ bin b ∧ bin b ≤ L)
    (hfiber : ∀ d,
      (indexFiber (Finset.univ.erase a) bin d).card ≤ 2)
    (hmajor : ∀ b ∈ (Finset.univ.erase a),
      K b ≤ (L : ℝ) ^ 2 * (((bin b : ℕ) : ℝ) ^ 2)⁻¹) :
    ∑ b, K b ≤ 8 * (L : ℝ) ^ 2 := by
  classical
  let S : Finset A := Finset.univ.erase a
  have hmaps : ∀ b ∈ S, bin b ∈ Finset.Ioo 0 (L + 1) := by
    intro b hb
    have h := hbin b hb
    exact Finset.mem_Ioo.mpr ⟨h.1, Nat.lt_succ_of_le h.2⟩
  have hregrp :
      ∑ b ∈ S, K b =
        ∑ d ∈ Finset.Ioo 0 (L + 1),
          ∑ b ∈ indexFiber S bin d, K b := by
    simpa only [indexFiber] using
      (Finset.sum_fiberwise_of_maps_to hmaps K).symm
  have hoff : ∑ b ∈ S, K b ≤ 4 * (L : ℝ) ^ 2 := by
    rw [hregrp]
    calc
      ∑ d ∈ Finset.Ioo 0 (L + 1),
          ∑ b ∈ indexFiber S bin d, K b ≤
        ∑ d ∈ Finset.Ioo 0 (L + 1),
          2 * ((L : ℝ) ^ 2 * (((d : ℕ) : ℝ) ^ 2)⁻¹) := by
            apply Finset.sum_le_sum
            intro d hd
            calc
              ∑ b ∈ indexFiber S bin d, K b ≤
                  ∑ _b ∈ indexFiber S bin d,
                    (L : ℝ) ^ 2 * (((d : ℕ) : ℝ) ^ 2)⁻¹ := by
                apply Finset.sum_le_sum
                intro b hb
                have hbS := (Finset.mem_filter.mp hb).1
                have hbeq := (Finset.mem_filter.mp hb).2
                simpa only [S, hbeq] using hmajor b hbS
              _ = (indexFiber S bin d).card *
                    ((L : ℝ) ^ 2 * (((d : ℕ) : ℝ) ^ 2)⁻¹) := by
                simp only [sum_const, nsmul_eq_mul]
              _ ≤ 2 * ((L : ℝ) ^ 2 * (((d : ℕ) : ℝ) ^ 2)⁻¹) := by
                apply mul_le_mul_of_nonneg_right
                · exact_mod_cast hfiber d
                · positivity
      _ = 2 * (L : ℝ) ^ 2 *
          ∑ d ∈ Finset.Ioo 0 (L + 1), (((d : ℕ) : ℝ) ^ 2)⁻¹ := by
            simp_rw [Finset.mul_sum]
            ring_nf
      _ ≤ 2 * (L : ℝ) ^ 2 * 2 := by
            apply mul_le_mul_of_nonneg_left
            · simpa using (sum_Ioo_inv_sq_le (α := ℝ) 0 (L + 1))
            · positivity
      _ = 4 * (L : ℝ) ^ 2 := by ring
  calc
    ∑ b, K b = ∑ b ∈ S, K b + K a := by
      exact (Finset.sum_erase_add _ _ (by simp)).symm
    _ ≤ 4 * (L : ℝ) ^ 2 + 4 * (L : ℝ) ^ 2 :=
      add_le_add hoff hdiag
    _ = 8 * (L : ℝ) ^ 2 := by ring

theorem circleDirichletKernel_zero (H : ℕ) :
    circleDirichletKernel H 0 = H := by
  unfold circleDirichletKernel
  simp [standardAdditiveCharacter]

theorem circleFejerKernel_zero (H : ℕ) :
    circleFejerKernel H 0 = (H : ℝ) ^ 2 := by
  rw [circleFejerKernel, circleDirichletKernel_zero,
    Complex.normSq_natCast]
  ring

def circleDistanceBin (L : ℕ) (theta : ℝ) : ℕ :=
  Nat.floor ((L : ℝ) * nearestIntegerDistance theta)

def circleDistanceBinFiber {A : Type*} [Fintype A] [DecidableEq A]
    (alpha : A → ℝ) (a : A) (L d : ℕ) : Finset A :=
  indexFiber (Finset.univ.erase a)
    (fun b => circleDistanceBin L (alpha b - alpha a)) d

theorem circleDistanceBin_bounds
    {L : ℕ} (hL : 0 < L) {theta : ℝ}
    (hsep : 1 / (L : ℝ) ≤ nearestIntegerDistance theta) :
    1 ≤ circleDistanceBin L theta ∧
      circleDistanceBin L theta ≤ L := by
  have hLreal : (0 : ℝ) < L := by positivity
  have hscaledLower : (1 : ℝ) ≤
      (L : ℝ) * nearestIntegerDistance theta := by
    have h := (div_le_iff₀ hLreal).mp hsep
    nlinarith
  have hlower : 1 ≤ circleDistanceBin L theta := by
    apply Nat.le_floor
    norm_num
    exact hscaledLower
  have hscaledUpper :
      (L : ℝ) * nearestIntegerDistance theta ≤ (L : ℝ) := by
    have hdist := nearestIntegerDistance_le_half theta
    calc
      (L : ℝ) * nearestIntegerDistance theta ≤ (L : ℝ) * (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hdist (by positivity)
      _ ≤ (L : ℝ) := by
        have hLn : (0 : ℝ) ≤ L := by positivity
        nlinarith
  have hupper : circleDistanceBin L theta ≤ L := by
    have hfloor : ((circleDistanceBin L theta : ℕ) : ℝ) ≤
        (L : ℝ) * nearestIntegerDistance theta := by
      exact Nat.floor_le (mul_nonneg (Nat.cast_nonneg _)
        (nearestIntegerDistance_nonneg _))
    exact_mod_cast hfloor.trans hscaledUpper
  exact ⟨hlower, hupper⟩

theorem circleFejerKernel_le_bin_majorant
    {L : ℕ} (hL : 0 < L) {theta : ℝ}
    (hsep : 1 / (L : ℝ) ≤ nearestIntegerDistance theta) :
    circleFejerKernel (2 * L) theta ≤
      (L : ℝ) ^ 2 *
        (((circleDistanceBin L theta : ℕ) : ℝ) ^ 2)⁻¹ := by
  let d := nearestIntegerDistance theta
  let B : ℝ := circleDistanceBin L theta
  have hLreal : (0 : ℝ) < L := by positivity
  have hd : 0 < d := (div_pos zero_lt_one hLreal).trans_le hsep
  have hBnat : 1 ≤ circleDistanceBin L theta :=
    (circleDistanceBin_bounds hL hsep).1
  have hB : 0 < B := by
    dsimp only [B]
    exact_mod_cast (zero_lt_one.trans_le hBnat)
  have hfloor : B ≤ (L : ℝ) * d := by
    exact Nat.floor_le (mul_nonneg (Nat.cast_nonneg _)
      (nearestIntegerDistance_nonneg _))
  have hinv : 1 / d ≤ (L : ℝ) / B := by
    rw [div_le_div_iff₀ hd hB]
    simpa only [one_mul] using hfloor
  have hsquare : (1 / d) ^ 2 ≤ ((L : ℝ) / B) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).2 hinv
  calc
    circleFejerKernel (2 * L) theta ≤ 1 / (4 * d ^ 2) :=
      circleFejerKernel_le_inv_distance_sq _ hd
    _ ≤ (1 / d) ^ 2 := by
      have : 0 ≤ d ^ 2 := sq_nonneg d
      field_simp
      nlinarith
    _ ≤ ((L : ℝ) / B) ^ 2 := hsquare
    _ = (L : ℝ) ^ 2 *
        (((circleDistanceBin L theta : ℕ) : ℝ) ^ 2)⁻¹ := by
      simp only [B]
      field_simp

theorem sum_circleFejerKernel_le_of_binFiber_card
    {A : Type*} [Fintype A] [DecidableEq A]
    (alpha : A → ℝ) (a : A) {L : ℕ} (hL : 0 < L)
    (hsep : ∀ b ≠ a,
      1 / (L : ℝ) ≤ nearestIntegerDistance (alpha b - alpha a))
    (hfiber : ∀ d, (circleDistanceBinFiber alpha a L d).card ≤ 2) :
    ∑ b, circleFejerKernel (2 * L) (alpha b - alpha a) ≤
      8 * (L : ℝ) ^ 2 := by
  apply sum_kernel_le_eight_mul_sq a L
    (fun b => circleFejerKernel (2 * L) (alpha b - alpha a))
    (fun b => circleDistanceBin L (alpha b - alpha a))
  · rw [sub_self, circleFejerKernel_zero]
    push_cast
    ring_nf
    exact le_rfl
  · intro b hb
    exact circleDistanceBin_bounds hL (hsep b (Finset.ne_of_mem_erase hb))
  · exact hfiber
  · intro b hb
    exact circleFejerKernel_le_bin_majorant hL
      (hsep b (Finset.ne_of_mem_erase hb))

def centeredCircleRepresentative (theta : ℝ) : ℝ :=
  theta - (round theta : ℝ)

@[simp]
theorem abs_centeredCircleRepresentative (theta : ℝ) :
    |centeredCircleRepresentative theta| = nearestIntegerDistance theta :=
  rfl

theorem centeredCircleRepresentative_pair_separated
    {A : Type*} (alpha : A → ℝ) (a b c : A) {L : ℕ}
    (hpair : ∀ x y, x ≠ y →
      1 / (L : ℝ) ≤ nearestIntegerDistance (alpha x - alpha y))
    (hbc : b ≠ c) :
    1 / (L : ℝ) ≤
      |centeredCircleRepresentative (alpha b - alpha a) -
        centeredCircleRepresentative (alpha c - alpha a)| := by
  let m : ℤ := round (alpha b - alpha a) - round (alpha c - alpha a)
  have hnear := nearestIntegerDistance_le_abs_sub_int (alpha b - alpha c) m
  calc
    1 / (L : ℝ) ≤ nearestIntegerDistance (alpha b - alpha c) :=
      hpair b c hbc
    _ ≤ |(alpha b - alpha c) - (m : ℝ)| := hnear
    _ = |centeredCircleRepresentative (alpha b - alpha a) -
        centeredCircleRepresentative (alpha c - alpha a)| := by
      congr 1
      unfold centeredCircleRepresentative m
      push_cast
      ring

theorem abs_sub_abs_lt_inv_of_same_bin
    {L d : ℕ} (hL : 0 < L) {x y : ℝ}
    (hbinx : circleDistanceBin L x = d)
    (hbiny : circleDistanceBin L y = d) :
    |(|centeredCircleRepresentative x| -
        |centeredCircleRepresentative y|)| < 1 / (L : ℝ) := by
  have hLreal : (0 : ℝ) < L := by positivity
  let X : ℝ := (L : ℝ) * |centeredCircleRepresentative x|
  let Y : ℝ := (L : ℝ) * |centeredCircleRepresentative y|
  have hXnonneg : 0 ≤ X := by positivity
  have hYnonneg : 0 ≤ Y := by positivity
  have hfloorX : Nat.floor X = d := by
    simpa only [X, circleDistanceBin,
      abs_centeredCircleRepresentative] using hbinx
  have hfloorY : Nat.floor Y = d := by
    simpa only [Y, circleDistanceBin,
      abs_centeredCircleRepresentative] using hbiny
  have hXlower : (d : ℝ) ≤ X := by
    rw [← hfloorX]
    exact Nat.floor_le hXnonneg
  have hYlower : (d : ℝ) ≤ Y := by
    rw [← hfloorY]
    exact Nat.floor_le hYnonneg
  have hXupper : X < (d : ℝ) + 1 := by
    simpa only [hfloorX, Nat.cast_add, Nat.cast_one] using
      (Nat.lt_floor_add_one X)
  have hYupper : Y < (d : ℝ) + 1 := by
    simpa only [hfloorY, Nat.cast_add, Nat.cast_one] using
      (Nat.lt_floor_add_one Y)
  have hXY : |X - Y| < 1 := by
    rw [abs_lt]
    constructor <;> linarith
  have hscale :
      |X - Y| = (L : ℝ) *
        |(|centeredCircleRepresentative x| -
          |centeredCircleRepresentative y|)| := by
    unfold X Y
    rw [← mul_sub, abs_mul, abs_of_pos hLreal]
  rw [hscale] at hXY
  exact (lt_div_iff₀ hLreal).mpr (by simpa [mul_comm] using hXY)

theorem abs_centered_sub_eq_abs_sub_abs_of_same_sign
    {x y : ℝ}
    (hsign : decide (centeredCircleRepresentative x < 0) =
      decide (centeredCircleRepresentative y < 0)) :
    |centeredCircleRepresentative x -
        centeredCircleRepresentative y| =
      |(|centeredCircleRepresentative x| -
        |centeredCircleRepresentative y|)| := by
  by_cases hx : centeredCircleRepresentative x < 0
  · have hy : centeredCircleRepresentative y < 0 := by
      simpa [hx] using hsign
    rw [abs_of_neg hx, abs_of_neg hy]
    rw [show -centeredCircleRepresentative x -
        -centeredCircleRepresentative y =
      -(centeredCircleRepresentative x -
        centeredCircleRepresentative y) by ring, abs_neg]
  · have hx0 : 0 ≤ centeredCircleRepresentative x := le_of_not_gt hx
    have hy : ¬ centeredCircleRepresentative y < 0 := by
      simpa [hx] using hsign
    have hy0 : 0 ≤ centeredCircleRepresentative y := le_of_not_gt hy
    rw [abs_of_nonneg hx0, abs_of_nonneg hy0]

theorem circleDistanceBinFiber_card_le_two_of_pairwise
    {A : Type*} [Fintype A] [DecidableEq A]
    (alpha : A → ℝ) (a : A) {L : ℕ} (hL : 0 < L)
    (hpair : ∀ b c, b ≠ c →
      1 / (L : ℝ) ≤ nearestIntegerDistance (alpha b - alpha c))
    (d : ℕ) :
    (circleDistanceBinFiber alpha a L d).card ≤ 2 := by
  let sign : A → Bool := fun b =>
    decide (centeredCircleRepresentative (alpha b - alpha a) < 0)
  have hinj : Set.InjOn sign (circleDistanceBinFiber alpha a L d) := by
    intro b hb c hc hsign
    by_contra hbc
    have hsep := centeredCircleRepresentative_pair_separated
      alpha a b c hpair hbc
    have hbmem := Finset.mem_filter.mp hb
    have hcmem := Finset.mem_filter.mp hc
    have hsmall := abs_sub_abs_lt_inv_of_same_bin hL
      hbmem.2 hcmem.2
    have habs := abs_centered_sub_eq_abs_sub_abs_of_same_sign
      (x := alpha b - alpha a) (y := alpha c - alpha a) hsign
    rw [habs] at hsep
    exact (not_lt_of_ge hsep) hsmall
  calc
    (circleDistanceBinFiber alpha a L d).card =
        ((circleDistanceBinFiber alpha a L d).image sign).card := by
      symm
      exact Finset.card_image_iff.mpr hinj
    _ ≤ (Finset.univ : Finset Bool).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = 2 := by decide

theorem sum_circleFejerKernel_le_of_pairwise
    {A : Type*} [Fintype A] [DecidableEq A]
    (alpha : A → ℝ) (a : A) {L : ℕ} (hL : 0 < L)
    (hpair : ∀ b c, b ≠ c →
      1 / (L : ℝ) ≤ nearestIntegerDistance (alpha b - alpha c)) :
    ∑ b, circleFejerKernel (2 * L) (alpha b - alpha a) ≤
      8 * (L : ℝ) ^ 2 := by
  apply sum_circleFejerKernel_le_of_binFiber_card alpha a hL
  · intro b hba
    exact hpair b a hba
  · exact circleDistanceBinFiber_card_le_two_of_pairwise
      alpha a hL hpair

theorem circleDirichletKernel_neg (H : ℕ) (theta : ℝ) :
    circleDirichletKernel H (-theta) =
      conj (circleDirichletKernel H theta) := by
  unfold circleDirichletKernel
  rw [map_sum]
  apply sum_congr rfl
  intro h _
  rw [show ((h : ℕ) : ℝ) * -theta =
      -(((h : ℕ) : ℝ) * theta) by ring,
    standardAdditiveCharacter_neg]

@[simp]
theorem circleFejerKernel_neg (H : ℕ) (theta : ℝ) :
    circleFejerKernel H (-theta) = circleFejerKernel H theta := by
  unfold circleFejerKernel
  rw [circleDirichletKernel_neg,
    Complex.normSq_conj]

theorem circleAnalysis_energy_le_of_pairwise_separated
    {A : Type*} [Fintype A] [DecidableEq A]
    {L : ℕ} (hL : 0 < L) (alpha : A → ℝ) (f : Fin L → ℂ)
    (hpair : ∀ a b, a ≠ b →
      1 / (L : ℝ) ≤ nearestIntegerDistance (alpha a - alpha b)) :
    ∑ a, Complex.normSq (finiteAnalysis
        (fun a (n : Fin L) => circleCharacterVector alpha a n) f a) ≤
      (8 * L : ℝ) * ∑ n, Complex.normSq (f n) := by
  apply circleAnalysis_energy_le_of_fejer_bounds alpha f (8 * L)
  · positivity
  · intro a
    convert sum_circleFejerKernel_le_of_pairwise alpha a hL hpair using 1
    ring
  · intro b
    have hrow := sum_circleFejerKernel_le_of_pairwise alpha b hL hpair
    calc
      ∑ a, circleFejerKernel (2 * L) (alpha b - alpha a) =
          ∑ a, circleFejerKernel (2 * L) (alpha a - alpha b) := by
        apply sum_congr rfl
        intro a _
        rw [show alpha b - alpha a = -(alpha a - alpha b) by ring,
          circleFejerKernel_neg]
      _ ≤ 8 * (L : ℝ) ^ 2 := hrow
      _ = (8 * L : ℝ) * L := by
        ring

end

end Tao2026

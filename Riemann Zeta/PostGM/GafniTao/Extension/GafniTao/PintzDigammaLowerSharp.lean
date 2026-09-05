import GafniTao.PintzDigammaSharp

/-!
# A sharp lower real-part bound for digamma

The companion upper bound in `PintzDigammaSharp` is not enough to compare a
Gamma factor with the reciprocal of a horizontally displaced Gamma factor.
Here the same absolutely convergent series is split at
`ceil |Im z| + 1`.  The harmonic head supplies the coefficient-one logarithm;
the real parts removed from that head and the remaining norm-tail are both
uniformly bounded on a compact positive real-part strip.
-/

open Complex Filter Finset Nat

namespace GafniTao

noncomputable section

set_option maxHeartbeats 1200000

/-- On a compact substrip of the right half-plane, the real part of digamma
is at least `log (|Im z| + 2)` minus a uniform constant. -/
theorem exists_log_sub_le_re_digamma {a b : ℝ} (ha : 0 < a) :
    ∃ D : ℝ, 0 < D ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
      Real.log (|z.im| + 2) - D ≤ (Complex.digamma z).re := by
  let c : ℝ := min a 1
  have hc : 0 < c := lt_min ha one_pos
  have hc1 : c ≤ 1 := min_le_right _ _
  let K : ℝ := 4 * (|b| + 2) * max 1 ((a ^ 2)⁻¹)
  let D : ℝ := K + (|b| + 2) / c +
    |Real.eulerMascheroniConstant| + 1
  have hK : 0 < K := by
    dsimp only [K]
    have : 0 < |b| + 2 := by positivity
    positivity
  have hD : 0 < D := by
    dsimp only [D]
    positivity
  refine ⟨D, hD, ?_⟩
  intro z hza hzb
  have hre : 0 < z.re := ha.trans_le hza
  have hb0 : 0 < b := hre.trans_le hzb
  have hzc : c ≤ z.re := (min_le_left a 1).trans hza
  have hpoles : ∀ n : ℕ, z ≠ -(n : ℂ) := by
    intro n hz
    have hzre := congrArg Complex.re hz
    simp only [neg_re, natCast_re] at hzre
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  let f : ℕ → ℂ := fun n =>
    ((n : ℂ) + 1)⁻¹ - (z + n)⁻¹
  have hsum : HasSum f
      (Complex.digamma z + Real.eulerMascheroniConstant) := by
    have h := Complex.hasSum_digamma hpoles
    have heq :
        (fun n : ℕ => 1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + z)) = f := by
      funext n
      simp only [f, one_div]
      rw [add_comm (n : ℂ) z]
    rwa [heq] at h
  let N : ℕ := ⌈|z.im|⌉₊ + 1
  let y : ℝ := |z.im|
  have hy : 0 ≤ y := by dsimp only [y]; positivity
  have hN1 : 1 ≤ N := by dsimp only [N]; omega
  have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans_le hN1R
  have hyN : y ≤ (N : ℝ) := by
    dsimp only [N, y]
    push_cast
    exact le_trans (Nat.le_ceil _) (by linarith)
  have hNUpper : (N : ℝ) ≤ y + 2 := by
    dsimp only [N, y]
    push_cast
    have hceil := Nat.ceil_lt_add_one (abs_nonneg z.im)
    linarith
  have hlogN : Real.log (y + 2) ≤ Real.log ((N : ℝ) + 1) := by
    apply Real.log_le_log (by linarith)
    dsimp only [N, y]
    push_cast
    have := Nat.le_ceil |z.im|
    linarith
  have haInv : (0 : ℝ) < (a ^ 2)⁻¹ := inv_pos.mpr (sq_pos_of_pos ha)
  have hmaxOne : 1 ≤ max 1 ((a ^ 2)⁻¹) := le_max_left _ _
  have hmaxInv : (a ^ 2)⁻¹ ≤ max 1 ((a ^ 2)⁻¹) := le_max_right _ _
  have hscale : 1 + y ^ 2 ≤ max 1 ((a ^ 2)⁻¹) * (a ^ 2 + y ^ 2) := by
    have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
    have hone : (1 : ℝ) = (a ^ 2)⁻¹ * a ^ 2 := by field_simp
    have hfirst : 1 ≤ max 1 ((a ^ 2)⁻¹) * a ^ 2 := by
      calc
        1 = (a ^ 2)⁻¹ * a ^ 2 := hone
        _ ≤ max 1 ((a ^ 2)⁻¹) * a ^ 2 :=
          mul_le_mul_of_nonneg_right hmaxInv ha2.le
    have hsecond : y ^ 2 ≤ max 1 ((a ^ 2)⁻¹) * y ^ 2 := by
      nlinarith [sq_nonneg y]
    nlinarith
  have hquadratic : ((N : ℝ) * (b + (N : ℝ))) ≤
      K * (a ^ 2 + y ^ 2) := by
    have hbTwo : 0 < |b| + 2 := by positivity
    have hfirst : (N : ℝ) ≤ 2 * (y + 1) := by linarith
    have hsecond : b + (N : ℝ) ≤ (|b| + 2) * (y + 1) := by
      have hbAbs : b ≤ |b| := le_abs_self b
      nlinarith
    have hyOne : 0 ≤ y + 1 := by linarith
    have hsquare : (y + 1) ^ 2 ≤ 2 * (1 + y ^ 2) := by
      nlinarith [sq_nonneg (y - 1)]
    calc
      (N : ℝ) * (b + (N : ℝ)) ≤
          (2 * (y + 1)) * ((|b| + 2) * (y + 1)) := by gcongr
      _ = 2 * (|b| + 2) * (y + 1) ^ 2 := by ring
      _ ≤ 4 * (|b| + 2) * (1 + y ^ 2) := by
        have := mul_le_mul_of_nonneg_left hsquare
          (show 0 ≤ 2 * (|b| + 2) by positivity)
        nlinarith
      _ ≤ 4 * (|b| + 2) *
          (max 1 ((a ^ 2)⁻¹) * (a ^ 2 + y ^ 2)) := by gcongr
      _ = K * (a ^ 2 + y ^ 2) := by simp only [K]; ring
  have hinvHead (n : ℕ) (hn : n ∈ Finset.range N) :
      0 ≤ ((z + n)⁻¹).re ∧ ((z + n)⁻¹).re ≤
        (b + (N : ℝ)) / (a ^ 2 + y ^ 2) := by
    have hnN : n < N := Finset.mem_range.mp hn
    have hnReal : (n : ℝ) ≤ N := by exact_mod_cast hnN.le
    have hnumPos : 0 < z.re + n := by positivity
    have hnumUpper : z.re + n ≤ b + (N : ℝ) := by linarith
    have hden : a ^ 2 + y ^ 2 ≤ Complex.normSq (z + n) := by
      rw [Complex.normSq_apply]
      simp only [add_re, natCast_re, add_im, natCast_im, add_zero, y]
      have hsq : a ^ 2 ≤ (z.re + (n : ℝ)) ^ 2 := by
        have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        nlinarith
      nlinarith [sq_abs z.im]
    rw [Complex.inv_re]
    constructor
    · exact div_nonneg hnumPos.le (Complex.normSq_nonneg _)
    · have hupperNonneg : 0 ≤ b + (N : ℝ) := by positivity
      exact div_le_div₀ hupperNonneg hnumUpper (by positivity) hden
  have hremoved :
      ∑ n ∈ Finset.range N, ((z + n)⁻¹).re ≤ K := by
    calc
      ∑ n ∈ Finset.range N, ((z + n)⁻¹).re ≤
          ∑ _n ∈ Finset.range N,
            (b + (N : ℝ)) / (a ^ 2 + y ^ 2) := by
        gcongr with n hn
        exact (hinvHead n hn).2
      _ = (N : ℝ) * ((b + (N : ℝ)) /
          (a ^ 2 + y ^ 2)) := by simp
      _ ≤ K := by
        have hdenPos : 0 < a ^ 2 + y ^ 2 := by positivity
        calc
          (N : ℝ) * ((b + (N : ℝ)) / (a ^ 2 + y ^ 2)) =
              ((N : ℝ) * (b + (N : ℝ))) /
                (a ^ 2 + y ^ 2) := by ring
          _ ≤ K := (div_le_iff₀ hdenPos).2 hquadratic
  have hhead : Real.log (y + 2) - K ≤
      ∑ n ∈ Finset.range N, (f n).re := by
    have hformula :
        ∑ n ∈ Finset.range N, (f n).re =
          ((harmonic N : ℚ) : ℝ) -
            ∑ n ∈ Finset.range N, ((z + n)⁻¹).re := by
      simp only [f, sub_re]
      rw [sum_sub_distrib]
      congr 1
      calc
        ∑ n ∈ Finset.range N, (((n : ℂ) + 1)⁻¹).re =
            ∑ n ∈ Finset.range N, ((n : ℝ) + 1)⁻¹ := by
          apply Finset.sum_congr rfl
          intro n _hn
          rw [Complex.inv_re, Complex.normSq_apply]
          norm_num
        _ = ((harmonic N : ℚ) : ℝ) :=
          Complex.sum_inv_natCast_add_one_real N
    rw [hformula]
    have hharm : Real.log ((N : ℝ) + 1) ≤ ((harmonic N : ℚ) : ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_one] using log_add_one_le_harmonic N
    linarith
  have hmaj : Summable (fun m : ℕ =>
      (‖z‖ + 1) / (c * ((m : ℝ) + 1) ^ 2)) := by
    refine (Complex.summable_one_div_natCast_add_one_sq.mul_left
      ((‖z‖ + 1) / c)).congr fun m => ?_
    rw [mul_one_div, div_div]
  have hnormsum : Summable (fun n : ℕ => ‖f n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => Complex.norm_inv_add_one_sub_inv_le hc hc1 hzc
        (le_refl ‖z‖) n) hmaj
  have hshiftNorm : Summable (fun i : ℕ => ‖f (i + N)‖) :=
    (summable_nat_add_iff N).mpr hnormsum
  have hshiftMaj : Summable (fun i : ℕ =>
      (‖z‖ + 1) / (c * (((i + N : ℕ) : ℝ) + 1) ^ 2)) :=
    (summable_nat_add_iff N).mpr hmaj
  have hzNorm : ‖z‖ ≤ b + y := by
    have h₁ : ‖z‖ ≤ |z.re| + |z.im| := norm_le_abs_re_add_abs_im z
    have h₂ : |z.re| = z.re := abs_of_pos hre
    rw [h₂] at h₁
    exact h₁.trans (by dsimp only [y]; linarith)
  have hkey : ‖z‖ + 1 ≤ (|b| + 2) * (N : ℝ) := by
    have hbAbs : b ≤ |b| := le_abs_self b
    have hbN : |b| ≤ |b| * (N : ℝ) := by
      nlinarith [mul_nonneg (abs_nonneg b) (sub_nonneg.mpr hN1R)]
    nlinarith
  have htailNorm : ‖∑' i : ℕ, f (i + N)‖ ≤ (|b| + 2) / c := by
    calc
      ‖∑' i : ℕ, f (i + N)‖ ≤ ∑' i : ℕ, ‖f (i + N)‖ :=
        norm_tsum_le_tsum_norm hshiftNorm
      _ ≤ ∑' i : ℕ,
          (‖z‖ + 1) / (c * (((i + N : ℕ) : ℝ) + 1) ^ 2) :=
        hshiftNorm.tsum_le_tsum
          (fun i => Complex.norm_inv_add_one_sub_inv_le hc hc1 hzc
            (le_refl ‖z‖) (i + N)) hshiftMaj
      _ = (‖z‖ + 1) / c *
          ∑' i : ℕ, 1 / (((i + N : ℕ) : ℝ) + 1) ^ 2 := by
        rw [← tsum_mul_left]
        exact tsum_congr fun i => by rw [mul_one_div, div_div]
      _ ≤ (‖z‖ + 1) / c * (N : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_left
          (Complex.tsum_one_div_natCast_add_add_one_sq_le hN1)
          (by positivity)
      _ = ((‖z‖ + 1) * (N : ℝ)⁻¹) / c := by ring
      _ ≤ (|b| + 2) / c := by
        have hquot : (‖z‖ + 1) * (N : ℝ)⁻¹ ≤ |b| + 2 := by
          rw [← div_eq_mul_inv, div_le_iff₀ hNpos]
          exact hkey
        gcongr
  have hsplit :
      (∑ n ∈ Finset.range N, f n) + ∑' i : ℕ, f (i + N) =
        ∑' n : ℕ, f n :=
    hsum.summable.sum_add_tsum_nat_add N
  have htailRe : -((|b| + 2) / c) ≤ (∑' i : ℕ, f (i + N)).re := by
    have hneg : -‖∑' i : ℕ, f (i + N)‖ ≤
        (∑' i : ℕ, f (i + N)).re :=
      neg_le_of_abs_le (Complex.abs_re_le_norm _)
    calc
      -((|b| + 2) / c) ≤ -‖∑' i : ℕ, f (i + N)‖ := neg_le_neg htailNorm
      _ ≤ (∑' i : ℕ, f (i + N)).re := hneg
  have hseriesRe : Real.log (y + 2) - K - (|b| + 2) / c ≤
      (∑' n : ℕ, f n).re := by
    rw [← hsplit, add_re]
    rw [show Real.log (y + 2) - K - (|b| + 2) / c =
      (Real.log (y + 2) - K) + (-((|b| + 2) / c)) by ring]
    simpa only [Complex.re_sum, add_comm N] using add_le_add hhead htailRe
  have hdigamma : Complex.digamma z =
      (∑' n : ℕ, f n) - (Real.eulerMascheroniConstant : ℂ) := by
    rw [hsum.tsum_eq]
    ring
  rw [hdigamma, sub_re, Complex.ofReal_re]
  have hgamma : Real.eulerMascheroniConstant ≤
      |Real.eulerMascheroniConstant| := le_abs_self _
  dsimp only [D]
  dsimp only [y] at hseriesRe ⊢
  linarith

#print axioms exists_log_sub_le_re_digamma

set_option maxHeartbeats 200000

end

end GafniTao

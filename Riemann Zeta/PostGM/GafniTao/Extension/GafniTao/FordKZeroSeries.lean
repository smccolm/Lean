import GafniTao.FordKSourceSeries
import GafniTao.SharpPerronZeroShell

/-!
# The multiplicity-weighted zero series in Ford's contour identity

Ford's equation `(I2)` contains a sum over every nontrivial zeta zero.  This
file constructs that sum from the literal finite symmetric sets `zeroSet 0 R`.
The unit shell estimates retain analytic multiplicity and give absolute
convergence from the quadratic decay of the pole-subtracted Laplace transform.
-/

open Complex Filter Set Finset MeasureTheory
open scoped BigOperators Topology

namespace GafniTao

noncomputable section

/-- The literal multiplicity-weighted Ford contribution of one nontrivial
zeta zero. -/
noncomputable def fordKZeroTerm
    (F₀ : ℂ → ℂ) (s rho : ℂ) : ℂ :=
  (zeroMultiplicity rho : ℂ) * F₀ (s - rho)

/-- The zeros whose ordinates enter between the consecutive heights `n` and
`n+1`, with the same half-open convention as the selected-height transfer. -/
noncomputable def fordKZeroNatShell (n : ℕ) : Finset ℂ :=
  sharpPerronZeroShell (n : ℝ) (n + 1 : ℕ)

/-- The contribution of one literal unit shell. -/
noncomputable def fordKZeroShellSum
    (F₀ : ℂ → ℂ) (s : ℂ) (n : ℕ) : ℂ :=
  ∑ rho ∈ fordKZeroNatShell n, fordKZeroTerm F₀ s rho

theorem fordKZeroNatShell_multiplicity_le
    {n : ℕ} (hn : 8 ≤ n) :
    (((∑ rho ∈ fordKZeroNatShell n,
        zeroMultiplicity rho : ℕ) : ℝ)) ≤
      4 * globalLocalZeroLogConstant * Real.log ((n : ℝ) + 2) := by
  simpa [fordKZeroNatShell, Nat.cast_add, Nat.cast_one] using
    (sharpPerronZeroShell_multiplicity_le
      (T := (n : ℝ)) (R := ((n : ℝ) + 1)) (by exact_mod_cast hn)
      (by constructor <;> norm_num))

/-- Far from the ordinate of `s`, a zero in the `n`th shell is at complex
distance at least `n/2` from `s`. -/
theorem fordKZeroNatShell_half_le_norm_sub
    {s rho : ℂ} {n : ℕ}
    (hn : 2 * (|s.im| + 1) ≤ (n : ℝ))
    (hrho : rho ∈ fordKZeroNatShell n) :
    (n : ℝ) / 2 ≤ ‖s - rho‖ := by
  have hshell := Finset.mem_filter.mp hrho
  have him : (n : ℝ) < |rho.im| := hshell.2
  have htri : |rho.im| ≤ |s.im - rho.im| + |s.im| := by
    calc
      |rho.im| = |(rho.im - s.im) + s.im| := by ring_nf
      _ ≤ |rho.im - s.im| + |s.im| := abs_add_le _ _
      _ = |s.im - rho.im| + |s.im| := by rw [abs_sub_comm]
  have himNorm : |s.im - rho.im| ≤ ‖s - rho‖ := by
    simpa only [sub_im] using Complex.abs_im_le_norm (s - rho)
  linarith

/-- Pointwise quadratic majorant for a Ford zero term in a sufficiently far
unit shell. -/
theorem norm_fordKZeroTerm_le_shell
    {F₀ : ℂ → ℂ} {s rho : ℂ} {D eta : ℝ} {n : ℕ}
    (hs : 1 < s.re) (hD : 0 ≤ D)
    (hn : 2 * (|s.im| + max eta 0 + 1) ≤ (n : ℝ))
    (hF₀ : ∀ z : ℂ, 0 ≤ z.re → eta ≤ ‖z‖ →
      ‖F₀ z‖ ≤ D / ‖z‖ ^ 2)
    (hrho : rho ∈ fordKZeroNatShell n) :
    ‖fordKZeroTerm F₀ s rho‖ ≤
      (zeroMultiplicity rho : ℝ) * (4 * D / (n : ℝ) ^ 2) := by
  have hzero := mem_zeroSet_zero_data (Finset.mem_filter.mp hrho).1
  have hre : 0 ≤ (s - rho).re := by
    simp only [sub_re]
    linarith [hzero.2.1]
  have hnBase : 2 * (|s.im| + 1) ≤ (n : ℝ) := by
    have hmax : 0 ≤ max eta 0 := le_max_right _ _
    linarith
  have hdist := fordKZeroNatShell_half_le_norm_sub hnBase hrho
  have hnNonneg : 0 ≤ (n : ℝ) := by positivity
  have hnEta : eta ≤ (n : ℝ) / 2 := by
    have heta : eta ≤ max eta 0 := le_max_left _ _
    linarith [abs_nonneg s.im, le_max_right eta 0]
  have hF := hF₀ (s - rho) hre (hnEta.trans hdist)
  have hnPos : 0 < (n : ℝ) := by
    have : 2 ≤ (n : ℝ) := by
      have habs : 0 ≤ |s.im| := abs_nonneg _
      have hmax : 0 ≤ max eta 0 := le_max_right _ _
      linarith
    linarith
  have hquot : D / ‖s - rho‖ ^ 2 ≤ 4 * D / (n : ℝ) ^ 2 := by
    have hsq : ((n : ℝ) / 2) ^ 2 ≤ ‖s - rho‖ ^ 2 := by nlinarith
    calc
      D / ‖s - rho‖ ^ 2 ≤ D / (((n : ℝ) / 2) ^ 2) := by
        exact div_le_div_of_nonneg_left hD (by positivity) hsq
      _ = 4 * D / (n : ℝ) ^ 2 := by field_simp; ring
  rw [fordKZeroTerm, norm_mul, RCLike.norm_natCast]
  exact mul_le_mul_of_nonneg_left (hF.trans hquot) (by positivity)

/-- A literal shell has the summable `log(n)/n²` majorant. -/
theorem norm_fordKZeroShellSum_le
    {F₀ : ℂ → ℂ} {s : ℂ} {D eta : ℝ} {n : ℕ}
    (hs : 1 < s.re) (hD : 0 ≤ D) (hnEight : 8 ≤ n)
    (hnFar : 2 * (|s.im| + max eta 0 + 1) ≤ (n : ℝ))
    (hF₀ : ∀ z : ℂ, 0 ≤ z.re → eta ≤ ‖z‖ →
      ‖F₀ z‖ ≤ D / ‖z‖ ^ 2) :
    ‖fordKZeroShellSum F₀ s n‖ ≤
      16 * globalLocalZeroLogConstant * D *
        (Real.log ((n : ℝ) + 2) / (n : ℝ) ^ 2) := by
  unfold fordKZeroShellSum
  calc
    ‖∑ rho ∈ fordKZeroNatShell n, fordKZeroTerm F₀ s rho‖ ≤
        ∑ rho ∈ fordKZeroNatShell n, ‖fordKZeroTerm F₀ s rho‖ :=
      norm_sum_le _ _
    _ ≤ ∑ rho ∈ fordKZeroNatShell n,
        (zeroMultiplicity rho : ℝ) * (4 * D / (n : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro rho hrho
      exact norm_fordKZeroTerm_le_shell hs hD hnFar hF₀ hrho
    _ = (((∑ rho ∈ fordKZeroNatShell n,
          zeroMultiplicity rho : ℕ) : ℝ)) *
          (4 * D / (n : ℝ) ^ 2) := by
      rw [Nat.cast_sum, Finset.sum_mul]
    _ ≤ (4 * globalLocalZeroLogConstant * Real.log ((n : ℝ) + 2)) *
          (4 * D / (n : ℝ) ^ 2) := by
      gcongr
      exact fordKZeroNatShell_multiplicity_le hnEight
    _ = 16 * globalLocalZeroLogConstant * D *
          (Real.log ((n : ℝ) + 2) / (n : ℝ) ^ 2) := by ring

set_option maxHeartbeats 800000 in
/-- The numerical `log(n+2)/n²` majorant used by the zero shells is
summable. -/
theorem summable_ford_log_nat_add_two_div_sq :
    Summable (fun n : ℕ =>
      Real.log ((n : ℝ) + 2) / (n : ℝ) ^ 2) := by
  have hp : Summable (fun n : ℕ => 4 / (n : ℝ) ^ (3 / 2 : ℝ)) := by
    simpa [div_eq_mul_inv] using
      (Real.summable_one_div_nat_rpow.mpr
        (by norm_num : (1 : ℝ) < 3 / 2)).mul_left 4
  refine Summable.of_norm_bounded_eventually hp ?_
  rw [Nat.cofinite_eq_atTop]
  refine Filter.eventually_atTop.2 ⟨2, ?_⟩
  intro n hnNat
  have hnReal : (2 : ℝ) ≤ n := by exact_mod_cast hnNat
  have hlogNonneg : 0 ≤ Real.log ((n : ℝ) + 2) :=
    Real.log_nonneg (by linarith)
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hlogNonneg (by positivity))]
  have hn : (0 : ℝ) < n + 2 := by positivity
  have hlog := Real.log_le_rpow_div (show (0 : ℝ) ≤ n + 2 by positivity)
    (show (0 : ℝ) < 1 / 2 by norm_num)
  have hcomp : (n : ℝ) + 2 ≤ 2 * (n : ℝ) := by linarith
  have hnpos : (0 : ℝ) < n := by linarith
  have hpow : ((n : ℝ) + 2) ^ (1 / 2 : ℝ) ≤
      2 * (n : ℝ) ^ (1 / 2 : ℝ) := by
    calc
      ((n : ℝ) + 2) ^ (1 / 2 : ℝ) ≤
          (2 * (n : ℝ)) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hcomp (by norm_num)
      _ = 2 ^ (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) := by
        rw [Real.mul_rpow (by norm_num) hnpos.le]
      _ ≤ 2 * (n : ℝ) ^ (1 / 2 : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hnpos.le _)
        calc
          (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 2 := by norm_num
  calc
    Real.log ((n : ℝ) + 2) / (n : ℝ) ^ 2 ≤
        (2 * ((n : ℝ) + 2) ^ (1 / 2 : ℝ)) / (n : ℝ) ^ 2 := by
      gcongr
      simpa [div_eq_mul_inv, mul_comm] using hlog
    _ ≤ (4 * (n : ℝ) ^ (1 / 2 : ℝ)) / (n : ℝ) ^ 2 := by
      exact div_le_div_of_nonneg_right (by linarith [hpow]) (by positivity)
    _ = 4 / (n : ℝ) ^ (3 / 2 : ℝ) := by
      field_simp [hnpos.ne', (Real.rpow_pos_of_pos hnpos _).ne']
      rw [show (n : ℝ) ^ 2 = (n : ℝ) ^ (2 : ℝ) by
        exact (Real.rpow_natCast (n : ℝ) 2).symm]
      rw [← Real.rpow_add hnpos]
      norm_num

/-- Absolute convergence of the actual multiplicity-weighted Ford zero
shells. -/
theorem summable_fordKZeroShellSum
    {F₀ : ℂ → ℂ} {s : ℂ} {D eta : ℝ}
    (hs : 1 < s.re) (hD : 0 ≤ D)
    (hF₀ : ∀ z : ℂ, 0 ≤ z.re → eta ≤ ‖z‖ →
      ‖F₀ z‖ ≤ D / ‖z‖ ^ 2) :
    Summable (fordKZeroShellSum F₀ s) := by
  let C : ℝ := 16 * globalLocalZeroLogConstant * D
  have hmajor : Summable (fun n : ℕ =>
      C * (Real.log ((n : ℝ) + 2) / (n : ℝ) ^ 2)) :=
    summable_ford_log_nat_add_two_div_sq.mul_left C
  refine hmajor.of_norm_bounded_eventually_nat ?_
  obtain ⟨N, hN⟩ := exists_nat_ge
    (max 8 (2 * (|s.im| + max eta 0 + 1)))
  refine Filter.eventually_atTop.2 ⟨N, ?_⟩
  intro n hn
  have hnReal : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hnEight : 8 ≤ n := by
    have : (8 : ℝ) ≤ N := (le_max_left _ _).trans hN
    exact_mod_cast this.trans hnReal
  have hnFar : 2 * (|s.im| + max eta 0 + 1) ≤ (n : ℝ) :=
    (le_max_right _ _).trans (hN.trans hnReal)
  simpa [C] using norm_fordKZeroShellSum_le hs hD hnEight hnFar hF₀

/-- Ford's complete nontrivial-zero contribution, defined as the absolutely
convergent sum of literal unit shells.  The height-zero finite set is retained
explicitly so no real-axis convention is hidden. -/
noncomputable def fordKZeroSeries (F₀ : ℂ → ℂ) (s : ℂ) : ℂ :=
  (∑ rho ∈ zeroSet 0 0, fordKZeroTerm F₀ s rho) +
    ∑' n : ℕ, fordKZeroShellSum F₀ s n

/-- The symmetric finite zero sum at integral height is exactly the initial
height-zero contribution plus the first `N` literal unit shells. -/
theorem sum_zeroSet_nat_eq_sum_fordKZeroShellSum
    (F₀ : ℂ → ℂ) (s : ℂ) (N : ℕ) :
    (∑ rho ∈ zeroSet 0 N, fordKZeroTerm F₀ s rho) =
      (∑ rho ∈ zeroSet 0 0, fordKZeroTerm F₀ s rho) +
        ∑ n ∈ Finset.range N, fordKZeroShellSum F₀ s n := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hsplit := sum_zeroSet_eq_sum_shell_add
        (T := (N : ℝ)) (R := ((N : ℝ) + 1)) (by positivity)
        (by norm_num) (fordKZeroTerm F₀ s)
      rw [show ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 by norm_num]
      rw [hsplit, ih, Finset.sum_range_succ]
      have hshell :
          (∑ rho ∈ sharpPerronZeroShell (N : ℝ) ((N : ℝ) + 1),
            fordKZeroTerm F₀ s rho) = fordKZeroShellSum F₀ s N := by
        simp only [fordKZeroShellSum, fordKZeroNatShell, Nat.cast_add,
          Nat.cast_one]
      rw [hshell]
      ring

/-- The actual finite, multiplicity-weighted zero sums converge to Ford's
complete zero series along integral heights. -/
theorem tendsto_sum_zeroSet_nat_fordKZeroTerm
    {F₀ : ℂ → ℂ} {s : ℂ} {D eta : ℝ}
    (hs : 1 < s.re) (hD : 0 ≤ D)
    (hF₀ : ∀ z : ℂ, 0 ≤ z.re → eta ≤ ‖z‖ →
      ‖F₀ z‖ ≤ D / ‖z‖ ^ 2) :
    Tendsto
      (fun N : ℕ => ∑ rho ∈ zeroSet 0 N, fordKZeroTerm F₀ s rho)
      atTop (nhds (fordKZeroSeries F₀ s)) := by
  have hsum := (summable_fordKZeroShellSum hs hD hF₀).hasSum.tendsto_sum_nat
  have hadd : Tendsto
      (fun N : ℕ =>
        (∑ rho ∈ zeroSet 0 0, fordKZeroTerm F₀ s rho) +
          ∑ n ∈ Finset.range N, fordKZeroShellSum F₀ s n)
      atTop
      (nhds ((∑ rho ∈ zeroSet 0 0, fordKZeroTerm F₀ s rho) +
        ∑' n : ℕ, fordKZeroShellSum F₀ s n)) :=
    tendsto_const_nhds.add hsum
  simpa only [fordKZeroSeries, sum_zeroSet_nat_eq_sum_fordKZeroShellSum]
    using hadd

/-- The zero contribution introduced by replacing a large requested height
`T` with a selected height in `[T,T+1]` has the same summable quadratic
majorant. -/
theorem norm_fordK_selectedZeroShellSum_le
    {F₀ : ℂ → ℂ} {s : ℂ} {D eta T R : ℝ}
    (hs : 1 < s.re) (hD : 0 ≤ D) (hT : 8 ≤ T)
    (hR : R ∈ Set.Icc T (T + 1))
    (hfar : 2 * (|s.im| + max eta 0 + 1) ≤ T)
    (hF₀ : ∀ z : ℂ, 0 ≤ z.re → eta ≤ ‖z‖ →
      ‖F₀ z‖ ≤ D / ‖z‖ ^ 2) :
    ‖∑ rho ∈ sharpPerronZeroShell T R, fordKZeroTerm F₀ s rho‖ ≤
      16 * globalLocalZeroLogConstant * D *
        (Real.log (T + 2) / T ^ 2) := by
  have hTpos : 0 < T := by linarith
  have hmult := sharpPerronZeroShell_multiplicity_le hT hR
  calc
    ‖∑ rho ∈ sharpPerronZeroShell T R, fordKZeroTerm F₀ s rho‖ ≤
        ∑ rho ∈ sharpPerronZeroShell T R, ‖fordKZeroTerm F₀ s rho‖ :=
      norm_sum_le _ _
    _ ≤ ∑ rho ∈ sharpPerronZeroShell T R,
        (zeroMultiplicity rho : ℝ) * (4 * D / T ^ 2) := by
      apply Finset.sum_le_sum
      intro rho hrho
      have hzero := mem_zeroSet_zero_data (Finset.mem_filter.mp hrho).1
      have hre : 0 ≤ (s - rho).re := by
        simp only [sub_re]
        linarith [hzero.2.1]
      have him : T < |rho.im| := (Finset.mem_filter.mp hrho).2
      have htri : |rho.im| ≤ |s.im - rho.im| + |s.im| := by
        calc
          |rho.im| = |(rho.im - s.im) + s.im| := by ring_nf
          _ ≤ |rho.im - s.im| + |s.im| := abs_add_le _ _
          _ = |s.im - rho.im| + |s.im| := by rw [abs_sub_comm]
      have himNorm : |s.im - rho.im| ≤ ‖s - rho‖ := by
        simpa only [sub_im] using Complex.abs_im_le_norm (s - rho)
      have hdist : T / 2 ≤ ‖s - rho‖ := by
        have hbase : 2 * (|s.im| + 1) ≤ T := by
          linarith [le_max_right eta 0]
        linarith
      have hetaDist : eta ≤ ‖s - rho‖ := by
        have hetaT : eta ≤ T / 2 := by
          linarith [le_max_left eta 0, abs_nonneg s.im,
            le_max_right eta 0]
        exact hetaT.trans hdist
      have hF := hF₀ (s - rho) hre hetaDist
      have hsq : (T / 2) ^ 2 ≤ ‖s - rho‖ ^ 2 := by nlinarith
      have hquot : D / ‖s - rho‖ ^ 2 ≤ 4 * D / T ^ 2 := by
        calc
          D / ‖s - rho‖ ^ 2 ≤ D / (T / 2) ^ 2 := by
            exact div_le_div_of_nonneg_left hD (by positivity) hsq
          _ = 4 * D / T ^ 2 := by field_simp; ring
      rw [fordKZeroTerm, norm_mul, RCLike.norm_natCast]
      exact mul_le_mul_of_nonneg_left (hF.trans hquot) (by positivity)
    _ = (((∑ rho ∈ sharpPerronZeroShell T R,
          zeroMultiplicity rho : ℕ) : ℝ)) * (4 * D / T ^ 2) := by
      rw [Nat.cast_sum, Finset.sum_mul]
    _ ≤ (4 * globalLocalZeroLogConstant * Real.log (T + 2)) *
          (4 * D / T ^ 2) := by
      gcongr
    _ = 16 * globalLocalZeroLogConstant * D *
          (Real.log (T + 2) / T ^ 2) := by ring

/-- Absolute convergence of the literal surrogate integrand on Ford's full
left vertical line. -/
theorem integrable_fordKSurrogate_leftLine
    {F₀ : ℂ → ℂ} {s : ℂ} {D eta : ℝ}
    (hs : 1 < s.re) (hetaUpper : eta ≤ 3 / 2)
    (hFdiff : ∀ z : ℂ, 0 < z.re → DifferentiableAt ℂ F₀ z)
    (hF₀ : ∀ z : ℂ, 0 ≤ z.re → eta ≤ ‖z‖ →
      ‖F₀ z‖ ≤ D / ‖z‖ ^ 2) :
    Integrable (fun u : ℝ =>
      fordKSurrogateIntegrand s F₀ (fordLeftLinePoint u)) := by
  obtain ⟨C, hC, hlog⟩ := exists_norm_riemannZeta_logDeriv_ford_leftLine_le
  have hsrepr : ((s.re : ℝ) : ℂ) + (s.im : ℂ) * I = s := by
    apply Complex.ext <;> simp
  have hmeas : AEStronglyMeasurable (fun u : ℝ =>
      (-deriv riemannZeta (fordLeftLinePoint u) /
          riemannZeta (fordLeftLinePoint u)) *
        F₀ ((((s.re : ℝ) : ℂ) + (s.im : ℂ) * I) -
          fordLeftLinePoint u)) := by
    simpa only [hsrepr] using
      (continuous_fordLeftLine_logDeriv_mul hs hFdiff).aestronglyMeasurable
  have hraw := integrable_fordLeftLine_logDeriv_mul_of_aestronglyMeasurable
    (F₀ := F₀) (sigma := s.re) (t := s.im) (D := D) (eta := eta)
    (C := C) hs hetaUpper hF₀ (by simpa [fordLeftLinePoint] using hlog)
    hC.le hmeas
  rw [hsrepr] at hraw
  apply hraw.congr
  filter_upwards [] with u
  have hEq := fordKSurrogateIntegrand_eq
    (s := s) (w := fordLeftLinePoint u) (F₀ := F₀)
    (by
      intro h
      have hre := congrArg Complex.re h
      norm_num at hre)
    (ford_leftLine_zeta_ne_zero u)
  calc
    (-deriv riemannZeta (fordLeftLinePoint u) /
          riemannZeta (fordLeftLinePoint u)) *
        F₀ (s - fordLeftLinePoint u) =
        -(deriv riemannZeta (fordLeftLinePoint u) /
          riemannZeta (fordLeftLinePoint u)) *
        F₀ (s - fordLeftLinePoint u) := by ring
    _ = fordKSurrogateIntegrand s F₀ (fordLeftLinePoint u) := by
      simpa [logDeriv_apply] using hEq.symm

/-- The normalized complete left-edge integral occurring in Ford `(I2)`. -/
noncomputable def fordKLeftLineIntegral (s : ℂ) (F₀ : ℂ → ℂ) : ℂ :=
  (1 / (2 * Real.pi * I)) •
    (I • ∫ u : ℝ, fordKSurrogateIntegrand s F₀ (fordLeftLinePoint u))

/-- The finite normalized left edges converge to the complete absolutely
convergent left-line integral. -/
theorem tendsto_fordK_leftLine_full
    {F₀ : ℂ → ℂ} {s : ℂ} {D eta : ℝ}
    (hs : 1 < s.re) (hetaUpper : eta ≤ 3 / 2)
    (hFdiff : ∀ z : ℂ, 0 < z.re → DifferentiableAt ℂ F₀ z)
    (hF₀ : ∀ z : ℂ, 0 ≤ z.re → eta ≤ ‖z‖ →
      ‖F₀ z‖ ≤ D / ‖z‖ ^ 2) :
    Tendsto
      (fun R : ℝ => VIntegral'
        (fordKSurrogateIntegrand s F₀) (-(1 / 2)) (-R) R)
      atTop (nhds (fordKLeftLineIntegral s F₀)) := by
  have hint := integrable_fordKSurrogate_leftLine hs hetaUpper hFdiff hF₀
  have hlim := MeasureTheory.intervalIntegral_tendsto_integral hint
    tendsto_neg_atTop_atBot tendsto_id
  have hI : Tendsto
      (fun R : ℝ => I • ∫ u in -R..R,
        fordKSurrogateIntegrand s F₀ (fordLeftLinePoint u))
      atTop
      (nhds (I • ∫ u : ℝ,
        fordKSurrogateIntegrand s F₀ (fordLeftLinePoint u))) :=
    tendsto_const_nhds.smul hlim
  have hscaled : Tendsto
      (fun R : ℝ => (1 / (2 * Real.pi * I) : ℂ) •
        (I • ∫ u in -R..R,
          fordKSurrogateIntegrand s F₀ (fordLeftLinePoint u)))
      atTop
      (nhds ((1 / (2 * Real.pi * I) : ℂ) •
        (I • ∫ u : ℝ,
          fordKSurrogateIntegrand s F₀ (fordLeftLinePoint u)))) :=
    tendsto_const_nhds.smul hI
  simpa only [VIntegral', VIntegral, fordLeftLinePoint,
    fordKLeftLineIntegral, ofReal_neg, ofReal_div, ofReal_one] using hscaled

end

end GafniTao

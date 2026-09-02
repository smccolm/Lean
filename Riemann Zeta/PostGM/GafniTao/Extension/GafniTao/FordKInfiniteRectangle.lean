import GafniTao.FordKZeroSeries

/-!
# Ford's infinite selected-rectangle identity

This file takes the limit of the exact finite residue rectangles.  The right
edge, complete zero series, two horizontal edges, and full left edge are kept
as separate limits before the final identity is assembled.
-/

open Complex Filter Set Finset MeasureTheory
open scoped BigOperators Topology

namespace GafniTao

noncomputable section

/-- The `log²(T)/T²` horizontal-edge factor tends to zero on integral
heights. -/
theorem tendsto_ford_log_sq_nat_div_sq_zero :
    Tendsto (fun n : ℕ => Real.log (n : ℝ) ^ 2 / (n : ℝ) ^ 2)
      atTop (nhds 0) := by
  have hbaseReal := Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hbase : Tendsto
      (fun n : ℕ => Real.log (n : ℝ) ^ 2 / (n : ℝ))
      atTop (nhds 0) := by
    simpa using hbaseReal.comp hcast
  apply squeeze_zero'
  · filter_upwards [Filter.eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
    positivity
  · filter_upwards [Filter.eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
    have hnReal : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnReal
    have hnpos : (0 : ℝ) < n := by linarith
    exact div_le_div_of_nonneg_left (sq_nonneg _)
      hnpos (by nlinarith [sq_nonneg ((n : ℝ) - 1)])
  · exact hbase

/-- Any selected height lying in `[n,n+1]` tends to infinity. -/
theorem tendsto_ford_selectedHeight_atTop
    {R : ℕ → ℝ}
    (hR : ∀ᶠ n : ℕ in atTop, R n ∈ Set.Icc (n : ℝ) ((n : ℝ) + 1)) :
    Tendsto R atTop atTop := by
  rw [Filter.tendsto_atTop]
  intro b
  obtain ⟨N, hN⟩ := exists_nat_ge b
  filter_upwards [hR, Filter.eventually_atTop.2 ⟨N, fun n hn => hn⟩] with n hnR hn
  exact hN.trans (by exact_mod_cast hn) |>.trans hnR.1

/-- Finite zero sums at any selected heights in `[n,n+1]` converge to the
same complete Ford zero series as the integral-height sums. -/
theorem tendsto_sum_zeroSet_selected_fordKZeroTerm
    {F₀ : ℂ → ℂ} {s : ℂ} {D eta : ℝ} {R : ℕ → ℝ}
    (hs : 1 < s.re) (hD : 0 ≤ D)
    (hF₀ : ∀ z : ℂ, 0 ≤ z.re → eta ≤ ‖z‖ →
      ‖F₀ z‖ ≤ D / ‖z‖ ^ 2)
    (hR : ∀ᶠ n : ℕ in atTop, R n ∈ Set.Icc (n : ℝ) ((n : ℝ) + 1)) :
    Tendsto
      (fun n : ℕ => ∑ rho ∈ zeroSet 0 (R n), fordKZeroTerm F₀ s rho)
      atTop (nhds (fordKZeroSeries F₀ s)) := by
  have hint := tendsto_sum_zeroSet_nat_fordKZeroTerm hs.le hD hF₀
  let E : ℕ → ℂ := fun n =>
    ∑ rho ∈ sharpPerronZeroShell (n : ℝ) (R n), fordKZeroTerm F₀ s rho
  have hmajor : Tendsto (fun n : ℕ =>
      16 * globalLocalZeroLogConstant * D *
        (Real.log ((n : ℝ) + 2) / (n : ℝ) ^ 2)) atTop (nhds 0) := by
    simpa using
      (summable_ford_log_nat_add_two_div_sq.tendsto_atTop_zero).const_mul
        (16 * globalLocalZeroLogConstant * D)
  have hEnorm : Tendsto (fun n => ‖E n‖) atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun n => norm_nonneg _
    · filter_upwards [hR,
        Filter.eventually_atTop.2 ⟨8, fun n hn => hn⟩,
        Filter.eventually_atTop.2
          ⟨⌈2 * (|s.im| + max eta 0 + 1)⌉₊,
            fun n hn => hn⟩] with n hnR hnEight hnFar
      have hnEight' : 8 ≤ n := hnEight
      have hnFarReal : 2 * (|s.im| + max eta 0 + 1) ≤ (n : ℝ) := by
        exact (Nat.le_ceil _).trans (by exact_mod_cast hnFar)
      simpa [E] using norm_fordK_selectedZeroShellSum_le
        hs hD (by exact_mod_cast hnEight') hnR hnFarReal hF₀
    · exact hmajor
  have hE : Tendsto E atTop (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hEnorm
  have hadd := hE.add hint
  have hadd' : Tendsto
      (fun n => E n + ∑ rho ∈ zeroSet 0 n, fordKZeroTerm F₀ s rho)
      atTop (nhds (fordKZeroSeries F₀ s)) := by
    simpa only [zero_add] using hadd
  apply hadd'.congr'
  filter_upwards [hR,
      Filter.eventually_atTop.2 ⟨0, fun n hn => hn⟩] with n hnR _hn
  have hsplit := sum_zeroSet_eq_sum_shell_add
    (T := (n : ℝ)) (R := R n) (by positivity) hnR.1 (fordKZeroTerm F₀ s)
  simpa [E] using hsplit.symm

/-- Limit assembly for any sequence of genuine selected rectangles satisfying
the exact finite Ford identity and the two quantitative horizontal bounds. -/
theorem fordK_infinite_rectangle_of_selected
    {f : ℝ → ℝ} {s : ℂ} {alpha D eta Ctop Cbottom : ℝ}
    {R : ℕ → ℝ}
    (hs : 1 < s.re) (halpha : 1 < alpha) (ha : alpha < s.re)
    (hD : 0 ≤ D) (hetaUpper : eta ≤ 3 / 2)
    (hetaRight : eta ≤ s.re - alpha)
    (hfcont : ContinuousOn f (Set.Ioi 0))
    (hfdiff : ∀ y : ℝ, 0 < y → DifferentiableAt ℝ f y)
    (hFdiff : ∀ z : ℂ, 0 < z.re → DifferentiableAt ℂ (fordLaplaceF0 f) z)
    (hAbs : ∀ z : ℂ, 0 < z.re → IntegrableOn (fun y : ℝ =>
      Complex.exp (-z * (y : ℂ)) * (f y : ℂ)) (Set.Ioi 0))
    (hF₀ : ∀ z : ℂ, 0 ≤ z.re → eta ≤ ‖z‖ →
      ‖fordLaplaceF0 f z‖ ≤ D / ‖z‖ ^ 2)
    (hR : ∀ᶠ n : ℕ in atTop, R n ∈ Set.Icc (n : ℝ) ((n : ℝ) + 1))
    (hidentity : ∀ᶠ n in atTop,
      VIntegral' (fordKSurrogateIntegrand s (fordLaplaceF0 f)) alpha (-(R n)) (R n) =
        fordLaplaceF0 f (s - 1) -
            ∑ rho ∈ zeroSet 0 (R n), fordKZeroTerm (fordLaplaceF0 f) s rho -
          HIntegral' (fordKSurrogateIntegrand s (fordLaplaceF0 f))
            (-(1 / 2)) alpha (-(R n)) +
          HIntegral' (fordKSurrogateIntegrand s (fordLaplaceF0 f))
            (-(1 / 2)) alpha (R n) +
          VIntegral' (fordKSurrogateIntegrand s (fordLaplaceF0 f))
            (-(1 / 2)) (-(R n)) (R n))
    (htop : ∀ᶠ n in atTop,
      ‖HIntegral' (fordKSurrogateIntegrand s (fordLaplaceF0 f))
        (-(1 / 2)) alpha (R n)‖ ≤
        (Ctop * (alpha + 1 / 2) * D) *
          (Real.log (n : ℝ) ^ 2 / (n : ℝ) ^ 2))
    (hbottom : ∀ᶠ n in atTop,
      ‖HIntegral' (fordKSurrogateIntegrand s (fordLaplaceF0 f))
        (-(1 / 2)) alpha (-(R n))‖ ≤
        (Cbottom * (alpha + 1 / 2) * D) *
          (Real.log (n : ℝ) ^ 2 / (n : ℝ) ^ 2)) :
    fordKDirichlet f s + (f 0 : ℂ) *
        (deriv riemannZeta s / riemannZeta s) =
      fordLaplaceF0 f (s - 1) - fordKZeroSeries (fordLaplaceF0 f) s +
        fordKLeftLineIntegral s (fordLaplaceF0 f) := by
  have hRt := tendsto_ford_selectedHeight_atTop hR
  have hright : Tendsto (fun n => VIntegral'
      (fordKSurrogateIntegrand s (fordLaplaceF0 f)) alpha (-(R n)) (R n))
      atTop (nhds (fordKDirichlet f s + (f 0 : ℂ) *
        (deriv riemannZeta s / riemannZeta s))) := by
    simpa only [Function.comp_apply] using
      (tendsto_fordK_rightLine_eq_K_add_logDeriv
        hs halpha ha hD hetaRight hfcont hfdiff hFdiff hAbs hF₀).comp hRt
  have hzero := tendsto_sum_zeroSet_selected_fordKZeroTerm hs hD hF₀ hR
  have hleft : Tendsto (fun n => VIntegral'
      (fordKSurrogateIntegrand s (fordLaplaceF0 f))
        (-(1 / 2)) (-(R n)) (R n)) atTop
      (nhds (fordKLeftLineIntegral s (fordLaplaceF0 f))) := by
    simpa only [Function.comp_apply] using
      (tendsto_fordK_leftLine_full hs hetaUpper hFdiff hF₀).comp hRt
  have hnum := tendsto_ford_log_sq_nat_div_sq_zero
  have htopZero : Tendsto (fun n =>
      HIntegral' (fordKSurrogateIntegrand s (fordLaplaceF0 f))
        (-(1 / 2)) alpha (R n)) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) htop
    simpa only [mul_zero] using hnum.const_mul (Ctop * (alpha + 1 / 2) * D)
  have hbottomZero : Tendsto (fun n =>
      HIntegral' (fordKSurrogateIntegrand s (fordLaplaceF0 f))
        (-(1 / 2)) alpha (-(R n))) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) hbottom
    simpa only [mul_zero] using hnum.const_mul (Cbottom * (alpha + 1 / 2) * D)
  have hrhs : Tendsto (fun n =>
      fordLaplaceF0 f (s - 1) -
          (∑ rho ∈ zeroSet 0 (R n), fordKZeroTerm (fordLaplaceF0 f) s rho) -
        HIntegral' (fordKSurrogateIntegrand s (fordLaplaceF0 f))
          (-(1 / 2)) alpha (-(R n)) +
        HIntegral' (fordKSurrogateIntegrand s (fordLaplaceF0 f))
          (-(1 / 2)) alpha (R n) +
        VIntegral' (fordKSurrogateIntegrand s (fordLaplaceF0 f))
          (-(1 / 2)) (-(R n)) (R n))
      atTop (nhds (fordLaplaceF0 f (s - 1) -
        fordKZeroSeries (fordLaplaceF0 f) s +
        fordKLeftLineIntegral s (fordLaplaceF0 f))) := by
    simpa only [sub_zero, add_zero] using
      (((tendsto_const_nhds.sub hzero).sub hbottomZero).add htopZero).add hleft
  have hright' := hright.congr' hidentity
  have heq := tendsto_nhds_unique hright' hrhs
  simpa using heq

/-- Ford's complete infinite rectangle identity, with the good heights
constructed from the proved finite selected-height theorem.  No selected
sequence or contour identity remains as a hypothesis. -/
theorem fordK_infinite_rectangle_native
    {f : ℝ → ℝ} {s : ℂ} {alpha D eta : ℝ}
    (hs : 1 < s.re) (halpha : 1 < alpha) (ha : alpha < s.re)
    (ht : 0 ≤ s.im) (hD : 0 ≤ D)
    (hetaUpper : eta ≤ 3 / 2) (hetaRight : eta ≤ s.re - alpha)
    (hfcont : ContinuousOn f (Set.Ioi 0))
    (hfdiff : ∀ y : ℝ, 0 < y → DifferentiableAt ℝ f y)
    (hFdiff : ∀ z : ℂ, 0 < z.re → DifferentiableAt ℂ (fordLaplaceF0 f) z)
    (hAbs : ∀ z : ℂ, 0 < z.re → IntegrableOn (fun y : ℝ =>
      Complex.exp (-z * (y : ℂ)) * (f y : ℂ)) (Set.Ioi 0))
    (hF₀ : ∀ z : ℂ, 0 ≤ z.re → eta ≤ ‖z‖ →
      ‖fordLaplaceF0 f z‖ ≤ D / ‖z‖ ^ 2) :
    fordKDirichlet f s + (f 0 : ℂ) *
        (deriv riemannZeta s / riemannZeta s) =
      fordLaplaceF0 f (s - 1) - fordKZeroSeries (fordLaplaceF0 f) s +
        fordKLeftLineIntegral s (fordLaplaceF0 f) := by
  obtain ⟨Ctop, Cbottom, hCtop, hCbottom, hselected⟩ :=
    exists_fordK_selected_rectangle_with_horizontal_bounds
  let Good : ℕ → Prop := fun n =>
    8 ≤ n ∧ 2 * s.im ≤ (n : ℝ) ∧ eta ≤ (n : ℝ) / 2
  have hGood : ∀ᶠ n : ℕ in atTop, Good n := by
    obtain ⟨N, hN⟩ := exists_nat_ge (max 8 (max (2 * s.im) (2 * eta)))
    refine Filter.eventually_atTop.2 ⟨N, ?_⟩
    intro n hn
    have hnReal : (N : ℝ) ≤ n := by exact_mod_cast hn
    have hall : max 8 (max (2 * s.im) (2 * eta)) ≤ (n : ℝ) :=
      hN.trans hnReal
    refine ⟨?_, ?_, ?_⟩
    · exact_mod_cast (le_max_left 8 (max (2 * s.im) (2 * eta))).trans hall
    · exact (le_max_left (2 * s.im) (2 * eta)).trans
        ((le_max_right 8 _).trans hall)
    · have := (le_max_right (2 * s.im) (2 * eta)).trans
        ((le_max_right 8 _).trans hall)
      linarith
  let Selected : ℕ → ℝ → Prop := fun n R =>
    R ∈ Set.Icc (n : ℝ) ((n : ℝ) + 1) ∧
    VIntegral' (fordKSurrogateIntegrand s (fordLaplaceF0 f)) alpha (-R) R =
      fordLaplaceF0 f (s - 1) -
          ∑ rho ∈ zeroSet 0 R, fordKZeroTerm (fordLaplaceF0 f) s rho -
        HIntegral' (fordKSurrogateIntegrand s (fordLaplaceF0 f))
          (-(1 / 2)) alpha (-R) +
        HIntegral' (fordKSurrogateIntegrand s (fordLaplaceF0 f))
          (-(1 / 2)) alpha R +
        VIntegral' (fordKSurrogateIntegrand s (fordLaplaceF0 f))
          (-(1 / 2)) (-R) R ∧
    ‖HIntegral' (fordKSurrogateIntegrand s (fordLaplaceF0 f))
      (-(1 / 2)) alpha R‖ ≤
        (Ctop * (alpha + 1 / 2) * D) *
          (Real.log (n : ℝ) ^ 2 / (n : ℝ) ^ 2) ∧
    ‖HIntegral' (fordKSurrogateIntegrand s (fordLaplaceF0 f))
      (-(1 / 2)) alpha (-R)‖ ≤
        (Cbottom * (alpha + 1 / 2) * D) *
          (Real.log (n : ℝ) ^ 2 / (n : ℝ) ^ 2)
  have hex : ∀ n : ℕ, Good n → ∃ R : ℝ, Selected n R := by
    intro n hn
    obtain ⟨R, hR, _hfar, _hstrict, hid, htop, hbottom⟩ :=
      hselected (s := s) (F₀ := fordLaplaceF0 f) (alpha := alpha)
        (D := D) (eta := eta) (T := (n : ℝ)) (by exact_mod_cast hn.1)
        halpha ha ht hn.2.1 hD hn.2.2 hFdiff hF₀
    refine ⟨R, hR, ?_, ?_, ?_⟩
    · simpa [fordKZeroTerm] using hid
    · simpa only [mul_div_assoc] using htop
    · simpa only [mul_div_assoc] using hbottom
  let R : ℕ → ℝ := fun n => if h : Good n then Classical.choose (hex n h) else n
  have hspec : ∀ {n : ℕ}, Good n → Selected n (R n) := by
    intro n hn
    simpa only [R, dif_pos hn] using Classical.choose_spec (hex n hn)
  have hR : ∀ᶠ n : ℕ in atTop,
      R n ∈ Set.Icc (n : ℝ) ((n : ℝ) + 1) := by
    filter_upwards [hGood] with n hn
    have h := hspec hn
    dsimp [Selected] at h
    exact h.1
  have hid : ∀ᶠ n : ℕ in atTop,
      VIntegral' (fordKSurrogateIntegrand s (fordLaplaceF0 f)) alpha (-(R n)) (R n) =
        fordLaplaceF0 f (s - 1) -
            ∑ rho ∈ zeroSet 0 (R n), fordKZeroTerm (fordLaplaceF0 f) s rho -
          HIntegral' (fordKSurrogateIntegrand s (fordLaplaceF0 f))
            (-(1 / 2)) alpha (-(R n)) +
          HIntegral' (fordKSurrogateIntegrand s (fordLaplaceF0 f))
            (-(1 / 2)) alpha (R n) +
          VIntegral' (fordKSurrogateIntegrand s (fordLaplaceF0 f))
            (-(1 / 2)) (-(R n)) (R n) := by
    filter_upwards [hGood] with n hn
    have h := hspec hn
    dsimp [Selected] at h
    exact h.2.1
  have htop : ∀ᶠ n : ℕ in atTop,
      ‖HIntegral' (fordKSurrogateIntegrand s (fordLaplaceF0 f))
        (-(1 / 2)) alpha (R n)‖ ≤
        (Ctop * (alpha + 1 / 2) * D) *
          (Real.log (n : ℝ) ^ 2 / (n : ℝ) ^ 2) := by
    filter_upwards [hGood] with n hn
    have h := hspec hn
    dsimp [Selected] at h
    exact h.2.2.1
  have hbottom : ∀ᶠ n : ℕ in atTop,
      ‖HIntegral' (fordKSurrogateIntegrand s (fordLaplaceF0 f))
        (-(1 / 2)) alpha (-(R n))‖ ≤
        (Cbottom * (alpha + 1 / 2) * D) *
          (Real.log (n : ℝ) ^ 2 / (n : ℝ) ^ 2) := by
    filter_upwards [hGood] with n hn
    have h := hspec hn
    dsimp [Selected] at h
    exact h.2.2.2
  exact fordK_infinite_rectangle_of_selected hs halpha ha hD hetaUpper
    hetaRight hfcont hfdiff hFdiff hAbs hF₀ hR hid htop hbottom

end

end GafniTao

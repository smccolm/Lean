import RiemannZeta.GuthMaynard.HughesYoungActiveComplementSmallContourTail

open Asymptotics Complex Filter

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Native Hughes--Young completion

This downstream module assembles the source-faithful contour and DFI
estimates into the native twisted fourth-moment theorem.  It is kept below
the active-complement contour stack to avoid an import cycle through
`HughesYoungNativeMoment`.
-/

/-- The complete active product-truncation complement has native
Hughes--Young size.  This is an actual consumer of the lower-endpoint
estimate, the exact lower/non-lower decomposition, and the finite
source-line contour estimate. -/
theorem hughesYoungConductorActiveComplementIntegratedCentral_epsilonPowerBound :
    EpsilonPowerBound
      (fun T => ‖hughesYoungActiveComplementIntegratedCentral T
        (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)‖)
      (fun T => T) := by
  intro ε hε
  have hsum :=
    (hughesYoungFiniteLowerBoundaryIntegratedCentral_epsilonPowerBound.add
      hughesYoungConductorNonLowerActiveComplementIntegratedCentralSource_epsilonPowerBound)
      ε hε
  obtain ⟨C, hC, hbound⟩ := hsum.exists_nonneg
  apply IsBigO.of_bound C
  filter_upwards [hbound.bound, eventually_ge_atTop (Real.exp 4)] with T hsumT hT
  have hsource :=
    hughesYoungNonLowerActiveComplementIntegratedCentralSource_eq
      hT (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)
  have hdecomp :=
    hughesYoungActiveComplementIntegratedCentral_eq_lower_add_nonLower
      T (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)
  have htri :
      ‖hughesYoungActiveComplementIntegratedCentral T
          (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)‖ ≤
        ‖hughesYoungFiniteLowerBoundaryIntegratedCentral T
          (hughesYoungGlobalDepth T)‖ +
        ‖hughesYoungNonLowerActiveComplementIntegratedCentralSource T
          (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)‖ := by
    rw [hdecomp, hsource]
    exact norm_add_le _ _
  have hfinal := htri.trans <| by
    simpa only [Real.norm_eq_abs, abs_of_nonneg
      (add_nonneg (norm_nonneg _) (norm_nonneg _))] using hsumT
  simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hfinal

/-! ## The complete regular non-large central family -/

/-- The mollifier cutoff and the native Fourier scale leave no integral
near frequency on a regular box whose arithmetic support inequality fails.
This is the quantitative relation omitted by the earlier supported-box
consumer. -/
theorem eventually_hughesYoungDFISmoothingScale_mul_two_detectorCutoff_sq_lt :
    ∀ᶠ T : ℝ in atTop,
      hughesYoungDFISmoothingScale T *
          (2 * (((detectorCutoff T) ^ 2 : ℕ) : ℝ)) < T := by
  have hgrow : Tendsto (fun T : ℝ => T ^ (9799 / 10000 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  filter_upwards [eventually_ge_atTop (1 : ℝ),
      hgrow.eventually (eventually_gt_atTop (144 : ℝ))] with T hT hpow
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hcut := detectorCutoff_sq_le_nine_mul_rpow_one_fiftieth hT
  calc
    hughesYoungDFISmoothingScale T *
          (2 * (((detectorCutoff T) ^ 2 : ℕ) : ℝ)) ≤
        (8 * T ^ (1 / 10000 : ℝ)) *
          (2 * (9 * T ^ (1 / 50 : ℝ))) := by
      unfold hughesYoungDFISmoothingScale
      gcongr
    _ = 144 * T ^ (201 / 10000 : ℝ) := by
      rw [show T ^ (201 / 10000 : ℝ) =
          T ^ (1 / 10000 : ℝ) * T ^ (1 / 50 : ℝ) by
        rw [← Real.rpow_add hT0]
        norm_num]
      ring
    _ < T ^ (9799 / 10000 : ℝ) * T ^ (201 / 10000 : ℝ) :=
      mul_lt_mul_of_pos_right hpow (Real.rpow_pos_of_pos hT0 _)
    _ = T := by
      rw [← Real.rpow_add hT0, ← Real.rpow_one T]
      norm_num

/-- Every regular active box outside the optimized DFI range has an empty
near central family.  Besides the small-`U` and non-comparable alternatives,
the two arithmetic-support failures force the physical dyadic scale below
the mollifier cutoff, hence below the first possible Fourier frequency. -/
theorem hughesYoungNearPointwiseSignedCentralBox_eq_zero_of_regularNonLarge_native
    {T : ℝ} {R K h k : ℕ} {ij : ℕ × ℕ}
    (hT : 0 < T)
    (hsmall : 320 * hughesYoungDFISmoothingScale T *
        hughesYoungDFISmoothingScale T < T)
    (hcutoff : hughesYoungDFISmoothingScale T *
        (2 * (((detectorCutoff T) ^ 2 : ℕ) : ℝ)) < T)
    (hhmem : h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2))
    (hkmem : k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2))
    (hij : ij ∈ hughesYoungCentralRegularNonLargeBoxes
      (hughesYoungDFISmoothingScale T)
      (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K) :
    hughesYoungNearPointwiseSignedCentralBox T
        (hughesYoungSmallContour T) (T / 8)
        (hughesYoungDFISmoothingScale T)
        (hughesYoungFullDyadicScale ij.1)
        (hughesYoungFullDyadicScale ij.2) h k
        (hughesYoungFullDyadicBound ij.1)
        (hughesYoungFullDyadicBound ij.2) = 0 := by
  let ell : ℕ := (detectorCutoff T) ^ 2
  let a : ℕ := hughesYoungReducedLeft h k
  let b : ℕ := hughesYoungReducedRight h k
  let X : ℝ := hughesYoungFullDyadicScale ij.1
  let Y : ℝ := hughesYoungFullDyadicScale ij.2
  let P : ℝ := hughesYoungDFISmoothingScale T
  have hregular := (Finset.mem_filter.mp hij).1
  have hpos := (Finset.mem_filter.mp hregular).2
  have hX : 0 < X := by dsimp only [X]; exact hughesYoungFullDyadicScale_pos _
  have hY : 0 < Y := by dsimp only [Y]; exact hughesYoungFullDyadicScale_pos _
  have hP : 0 < P := by dsimp only [P, hughesYoungDFISmoothingScale]; positivity
  have haell : (a : ℝ) ≤ (ell : ℝ) := by
    exact_mod_cast (hughesYoungReducedLeft_le h k).trans
      (Finset.mem_Icc.mp hhmem).2
  have hbell : (b : ℝ) ≤ (ell : ℝ) := by
    exact_mod_cast (hughesYoungReducedRight_le h k).trans
      (Finset.mem_Icc.mp hkmem).2
  by_cases hleft : 4 * Y < X
  · exact hughesYoungNearPointwiseSignedCentralBox_eq_zero_of_left_separated
      hX hY hleft
  by_cases hright : 4 * X < Y
  · exact hughesYoungNearPointwiseSignedCentralBox_eq_zero_of_right_separated
      hX hY hright
  have hXY : X ≤ 4 * Y := le_of_not_gt hleft
  have hYX : Y ≤ 4 * X := le_of_not_gt hright
  rcases hughesYoungCentralRegularNonLargeBoxes_cases hij with
      hbadA | hbadB | hU | hleft' | hright'
  · apply hughesYoungNearPointwiseSignedCentralBox_eq_zero_of_nearShifts_empty
    apply hughesYoungNearShifts_eq_empty_of_mul_lt hT hY
    have hYell : Y < 2 * (ell : ℝ) := by
      have hXa : 2 * X < (a : ℝ) := lt_of_not_ge hbadA
      linarith
    calc
      P * Y < P * (2 * (ell : ℝ)) := mul_lt_mul_of_pos_left hYell hP
      _ < T := by simpa only [P, ell] using hcutoff
  · apply hughesYoungNearPointwiseSignedCentralBox_eq_zero_of_nearShifts_empty
    apply hughesYoungNearShifts_eq_empty_of_mul_lt hT hY
    have hYell : Y < 2 * (ell : ℝ) := by
      have hYb : 2 * Y < (b : ℝ) := lt_of_not_ge hbadB
      have hell0 : 0 ≤ (ell : ℝ) := Nat.cast_nonneg _
      linarith
    calc
      P * Y < P * (2 * (ell : ℝ)) := mul_lt_mul_of_pos_left hYell hP
      _ < T := by simpa only [P, ell] using hcutoff
  · have hYsmall : Y < 320 * P :=
      hughesYoung_secondScale_lt_threeHundredTwenty_mul_of_optimalU_lt
        hP hX hY hYX hU
    exact hughesYoungNearPointwiseSignedCentralBox_eq_zero_of_native_smallScale
      hT hsmall hY hYsmall
  · exact False.elim (hleft hleft')
  · exact False.elim (hright hright')

/-- Equation (81) for every regular non-large active box, including the
two arithmetic-support-failure branches. -/
theorem hughesYoungIntegratedCompleteCentral_eq_far_of_regularNonLarge_native
    {T : ℝ} {R K h k : ℕ} {ij : ℕ × ℕ}
    (hT : 16 ≤ T)
    (hP : 1 ≤ hughesYoungDFISmoothingScale T)
    (hPT : hughesYoungDFISmoothingScale T ≤ T)
    (hsmall : 320 * hughesYoungDFISmoothingScale T *
        hughesYoungDFISmoothingScale T < T)
    (hcutoff : hughesYoungDFISmoothingScale T *
        (2 * (((detectorCutoff T) ^ 2 : ℕ) : ℝ)) < T)
    (hhmem : h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2))
    (hkmem : k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2))
    (hij : ij ∈ hughesYoungCentralRegularNonLargeBoxes
      (hughesYoungDFISmoothingScale T)
      (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K) :
    hughesYoungIntegratedFiniteCompleteSignedCentralBox T
        (hughesYoungSmallContour T) (T / 8)
        (hughesYoungFullDyadicScale ij.1)
        (hughesYoungFullDyadicScale ij.2) h k
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
        (hughesYoungFullDyadicBound ij.1)
        (hughesYoungFullDyadicBound ij.2) =
      hughesYoungIntegratedPointwiseSignedCentral T
        (hughesYoungSmallContour T) (T / 8)
        (hughesYoungFullDyadicScale ij.1)
        (hughesYoungFullDyadicScale ij.2) h k
        (hughesYoungFarShifts T (hughesYoungDFISmoothingScale T)
          (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2)
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
          (hughesYoungFullDyadicBound ij.1)
          (hughesYoungFullDyadicBound ij.2)) := by
  have hregular := (Finset.mem_filter.mp hij).1
  have hpos := (Finset.mem_filter.mp hregular).2
  have hX : 1 ≤ hughesYoungFullDyadicScale ij.1 := by
    obtain ⟨i, hiEq⟩ := Nat.exists_eq_succ_of_ne_zero hpos.1.ne'
    rw [hiEq]
    simpa only [Nat.succ_eq_add_one] using one_le_hughesYoungFullDyadicScale_succ i
  have hY : 1 ≤ hughesYoungFullDyadicScale ij.2 := by
    obtain ⟨j, hjEq⟩ := Nat.exists_eq_succ_of_ne_zero hpos.2.ne'
    rw [hjEq]
    simpa only [Nat.succ_eq_add_one] using one_le_hughesYoungFullDyadicScale_succ j
  have hc := hughesYoungSmallContour_spec
    (Real.exp_one_lt_three.le.trans (by linarith : (3 : ℝ) ≤ T))
  let U : ℝ := (hughesYoungDFISmoothingScale T)⁻¹ *
    min (hughesYoungFullDyadicScale ij.1)
      (hughesYoungFullDyadicScale ij.2)
  have hU : 0 < U := by dsimp only [U]; positivity
  have hEq := hughesYoungNearPointwiseSignedCentralBox_eq_integratedComplete_sub_far
    (T := T) (c := hughesYoungSmallContour T) (H := T / 8)
    (P := hughesYoungDFISmoothingScale T) (U := U)
    (X := hughesYoungFullDyadicScale ij.1)
    (Y := hughesYoungFullDyadicScale ij.2) (h := h) (k := k)
    (M := hughesYoungFullDyadicBound ij.1)
    (N := hughesYoungFullDyadicBound ij.2)
    hT hc.1 hc.2.1 (by positivity) le_rfl (lt_of_lt_of_le zero_lt_one hP)
    hPT hX hY
    (Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hhmem).1)
    (Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hkmem).1)
    hP hU le_rfl
  rw [hughesYoungNearPointwiseSignedCentralBox_eq_zero_of_regularNonLarge_native
    (lt_of_lt_of_le (by norm_num) hT) hsmall hcutoff hhmem hkmem hij] at hEq
  exact sub_eq_zero.mp hEq.symm

/-- The equation-(65) far family over all regular active non-large boxes. -/
noncomputable def hughesYoungRegularNonLargeIntegratedCentralTail
    (T P : ℝ) (R K : ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∑ ij ∈ hughesYoungCentralRegularNonLargeBoxes P
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
        hughesYoungIntegratedPointwiseSignedCentral T
          (hughesYoungSmallContour T) (T / 8)
          (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k
          (hughesYoungFarShifts T P
            (hughesYoungFullDyadicScale ij.1)
            (hughesYoungFullDyadicScale ij.2)
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
            (hughesYoungFullDyadicBound ij.1)
            (hughesYoungFullDyadicBound ij.2))

/-- Finite-sum form of the strengthened regular equation-(81) identity. -/
theorem hughesYoungActiveRegularNonLargeIntegratedCompleteCentral_eq_tail_native
    {T : ℝ} (hT : 16 ≤ T)
    (hP : 1 ≤ hughesYoungDFISmoothingScale T)
    (hPT : hughesYoungDFISmoothingScale T ≤ T)
    (hsmall : 320 * hughesYoungDFISmoothingScale T *
        hughesYoungDFISmoothingScale T < T)
    (hcutoff : hughesYoungDFISmoothingScale T *
        (2 * (((detectorCutoff T) ^ 2 : ℕ) : ℝ)) < T)
    (R K : ℕ) :
    hughesYoungActiveRegularNonLargeIntegratedCompleteCentral T
        (hughesYoungDFISmoothingScale T) R K =
      hughesYoungRegularNonLargeIntegratedCentralTail T
        (hughesYoungDFISmoothingScale T) R K := by
  classical
  unfold hughesYoungActiveRegularNonLargeIntegratedCompleteCentral
    hughesYoungRegularNonLargeIntegratedCentralTail
  apply Finset.sum_congr rfl
  intro h hhmem
  apply Finset.sum_congr rfl
  intro k hkmem
  apply Finset.sum_congr rfl
  intro ij hij
  exact hughesYoungIntegratedCompleteCentral_eq_far_of_regularNonLarge_native
    hT hP hPT hsmall hcutoff hhmem hkmem hij

/-- The equation-(65) static mass has the same uniform polynomial envelope
on every regular active non-large box.  Unlike the older supported wrapper,
this statement consumes only the properties actually used by the estimate:
active-rectangle membership and positive dyadic indices. -/
theorem hughesYoungFarSignedCentralStaticMass_le_regularNonLargeEnvelope
    {T P : ℝ} {R K h k : ℕ} {ij : ℕ × ℕ}
    (hT : Real.exp 1 ≤ T)
    (hhmem : h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2))
    (hkmem : k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2))
    (hij : ij ∈ hughesYoungCentralRegularNonLargeBoxes P
      (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K) :
    hughesYoungFarSignedCentralStaticMass T (hughesYoungSmallContour T) P
        (hughesYoungFullDyadicScale ij.1) (hughesYoungFullDyadicScale ij.2)
        h k (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
        (hughesYoungFullDyadicBound ij.1) (hughesYoungFullDyadicBound ij.2) ≤
      3 * (15 + 4 * |Real.eulerMascheroniConstant|) ^ 2 *
        hughesYoungCentralTailSeriesConstant *
        ((((detectorCutoff T) ^ 2 : ℕ) : ℝ)) ^ (11 : ℕ) *
        (hughesYoungActiveArithmeticCutoff T R : ℝ) ^ (6 : ℕ) := by
  let ell : ℕ := (detectorCutoff T) ^ 2
  let B : ℕ := hughesYoungActiveArithmeticCutoff T R
  have hT1 : 1 ≤ T := by linarith [Real.exp_one_gt_d9]
  have hc := hughesYoungSmallContour_spec hT
  have hh : 0 < h := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hhmem).1
  have hk : 0 < k := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hkmem).1
  have hhle : h ≤ ell := by simpa only [ell] using (Finset.mem_Icc.mp hhmem).2
  have hkle : k ≤ ell := by simpa only [ell] using (Finset.mem_Icc.mp hkmem).2
  have ha : 0 < hughesYoungReducedLeft h k := hughesYoungReducedLeft_pos hh
  have hb : 0 < hughesYoungReducedRight h k := hughesYoungReducedRight_pos hh hk
  have haell : hughesYoungReducedLeft h k ≤ ell :=
    (hughesYoungReducedLeft_le h k).trans hhle
  have hbell : hughesYoungReducedRight h k ≤ ell :=
    (hughesYoungReducedRight_le h k).trans hkle
  have hregular := (Finset.mem_filter.mp hij).1
  have hactive := (Finset.mem_filter.mp hregular).1
  have hpos := (Finset.mem_filter.mp hregular).2
  have hX : 1 ≤ hughesYoungFullDyadicScale ij.1 := by
    obtain ⟨i, hiEq⟩ := Nat.exists_eq_succ_of_ne_zero hpos.1.ne'
    rw [hiEq]
    simpa only [Nat.succ_eq_add_one] using one_le_hughesYoungFullDyadicScale_succ i
  have hY : 1 ≤ hughesYoungFullDyadicScale ij.2 := by
    obtain ⟨j, hjEq⟩ := Nat.exists_eq_succ_of_ne_zero hpos.2.ne'
    rw [hjEq]
    simpa only [Nat.succ_eq_add_one] using one_le_hughesYoungFullDyadicScale_succ j
  have hMnat : hughesYoungFullDyadicBound ij.1 ≤ B := by
    have hraw := hughesYoungFullDyadicBound_le_four_mul_activeConductor_add_one_left
      hactive
    have hprod : hughesYoungReducedLeft h k * hughesYoungReducedRight h k * R ≤
        ell * ell * R := Nat.mul_le_mul_right R (Nat.mul_le_mul haell hbell)
    unfold B hughesYoungActiveArithmeticCutoff
    exact hraw.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 4 hprod) 1)
  have hNnat : hughesYoungFullDyadicBound ij.2 ≤ B := by
    have hraw := hughesYoungFullDyadicBound_le_four_mul_activeConductor_add_one_right
      hactive
    have hprod : hughesYoungReducedLeft h k * hughesYoungReducedRight h k * R ≤
        ell * ell * R := Nat.mul_le_mul_right R (Nat.mul_le_mul haell hbell)
    unfold B hughesYoungActiveArithmeticCutoff
    exact hraw.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 4 hprod) 1)
  have hXB : hughesYoungFullDyadicScale ij.1 ≤ (B : ℝ) := by
    have htwo := two_mul_hughesYoungFullDyadicScale_le_bound ij.1
    exact (by linarith : hughesYoungFullDyadicScale ij.1 ≤
      (hughesYoungFullDyadicBound ij.1 : ℝ)).trans (by exact_mod_cast hMnat)
  have hYB : hughesYoungFullDyadicScale ij.2 ≤ (B : ℝ) := by
    have htwo := two_mul_hughesYoungFullDyadicScale_le_bound ij.2
    exact (by linarith : hughesYoungFullDyadicScale ij.2 ≤
      (hughesYoungFullDyadicBound ij.2 : ℝ)).trans (by exact_mod_cast hNnat)
  have hell1 : 1 ≤ ell := by
    have hcut : 0 < detectorCutoff T := by unfold detectorCutoff; omega
    simpa only [ell] using Nat.one_le_pow 2 (detectorCutoff T) hcut
  have hB1 : 1 ≤ B := by unfold B hughesYoungActiveArithmeticCutoff; omega
  have hR : 0 < R := by
    have hprod := (Finset.mem_filter.mp hactive).2
    have hprodPos : 0 < hughesYoungFullDyadicScale ij.1 *
        hughesYoungFullDyadicScale ij.2 := mul_pos
      (hughesYoungFullDyadicScale_pos ij.1) (hughesYoungFullDyadicScale_pos ij.2)
    have hcastPos : 0 < ((hughesYoungReducedLeft h k *
        hughesYoungReducedRight h k * R : ℕ) : ℝ) := hprodPos.trans_le hprod
    have hnatPos : 0 < hughesYoungReducedLeft h k *
        hughesYoungReducedRight h k * R := by exact_mod_cast hcastPos
    exact pos_of_mul_pos_right hnatPos (Nat.zero_le _)
  have hellB : ell ≤ B := by
    unfold B hughesYoungActiveArithmeticCutoff
    change ell ≤ 4 * (ell * ell * R) + 1
    have hsquare : ell ≤ ell * ell := Nat.le_mul_of_pos_right ell hell1
    have hRmul : ell * ell ≤ ell * ell * R :=
      Nat.le_mul_of_pos_right (ell * ell) hR
    exact hsquare.trans (hRmul.trans (by omega))
  simpa only [ell, B] using hughesYoungFarSignedCentralStaticMass_le_polynomial
    hT1 hc.1.le hc.2.1 hX hY (by exact_mod_cast hell1) (by exact_mod_cast hB1)
    hh hk ha hb (by exact_mod_cast hhle) (by exact_mod_cast hkle)
    (by exact_mod_cast haell) (by exact_mod_cast hbell) (by exact_mod_cast hellB)
    hXB hYB (by exact_mod_cast hMnat) (by exact_mod_cast hNnat)

/-- Equation-(65) decay summed over every regular active non-large box. -/
theorem exists_scaled_norm_hughesYoungRegularNonLargeIntegratedCentralTail_le
    (j : ℕ) :
    ∃ Cγ L : ℝ, 0 < Cγ ∧ 0 < L ∧ ∃ Cw : ℕ → ℝ,
      (∀ i, 0 < Cw i) ∧
      ∀ {T P : ℝ} {R K : ℕ},
      Real.exp 1 ≤ T → 16 ≤ T → 1 ≤ P → P ≤ T →
      4 * Cγ * hughesYoungSmallContour T ≤ 1 →
      (P / (5 * T)) ^ j *
          ‖hughesYoungRegularNonLargeIntegratedCentralTail T P R K‖ ≤
        (((((detectorCutoff T) ^ 2 : ℕ) : ℝ) ^ 2) *
          (((K + 2 : ℕ) : ℝ) ^ 2)) *
        hughesYoungCentralTailPolynomialEnvelope Cw L j T
          ((((detectorCutoff T) ^ 2 : ℕ) : ℝ))
          (hughesYoungActiveArithmeticCutoff T R : ℝ) := by
  obtain ⟨Cγ, L, hCγ, hL, Cw, hCw, hlocal⟩ :=
    exists_norm_hughesYoungIntegratedFarSignedCentral_full_bound j
  refine ⟨Cγ, L, hCγ, hL, Cw, hCw, ?_⟩
  intro T P R K hT hT16 hP hPT hcontour
  classical
  let S := Finset.Icc 1 ((detectorCutoff T) ^ 2)
  let A : ℝ := (P / (5 * T)) ^ j
  let E : ℝ := hughesYoungCentralTailPolynomialEnvelope Cw L j T
    ((((detectorCutoff T) ^ 2 : ℕ) : ℝ))
    (hughesYoungActiveArithmeticCutoff T R : ℝ)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact hughesYoungCentralTailPolynomialEnvelope_nonneg hT hL.le hCw
      (by positivity) (by positivity)
  have hc := hughesYoungSmallContour_spec hT
  have hbox : ∀ h ∈ S, ∀ k ∈ S,
      ∀ ij ∈ hughesYoungCentralRegularNonLargeBoxes P
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
      A * ‖hughesYoungIntegratedPointwiseSignedCentral T
          (hughesYoungSmallContour T) (T / 8)
          (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k
          (hughesYoungFarShifts T P
            (hughesYoungFullDyadicScale ij.1)
            (hughesYoungFullDyadicScale ij.2)
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
            (hughesYoungFullDyadicBound ij.1)
            (hughesYoungFullDyadicBound ij.2))‖ ≤ E := by
    intro h hhmem k hkmem ij hij
    have hh : 0 < h := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hhmem).1
    have hk : 0 < k := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hkmem).1
    have hregular := (Finset.mem_filter.mp hij).1
    have hpos := (Finset.mem_filter.mp hregular).2
    have hX : 1 ≤ hughesYoungFullDyadicScale ij.1 := by
      obtain ⟨i, hiEq⟩ := Nat.exists_eq_succ_of_ne_zero hpos.1.ne'
      rw [hiEq]
      simpa only [Nat.succ_eq_add_one] using one_le_hughesYoungFullDyadicScale_succ i
    have hY : 1 ≤ hughesYoungFullDyadicScale ij.2 := by
      obtain ⟨i, hiEq⟩ := Nat.exists_eq_succ_of_ne_zero hpos.2.ne'
      rw [hiEq]
      simpa only [Nat.succ_eq_add_one] using one_le_hughesYoungFullDyadicScale_succ i
    have hraw := hlocal (T := T) (c := hughesYoungSmallContour T)
      (H := T / 8) (P := P)
      (X := hughesYoungFullDyadicScale ij.1)
      (Y := hughesYoungFullDyadicScale ij.2) (h := h) (k := k)
      (M := hughesYoungFullDyadicBound ij.1)
      (N := hughesYoungFullDyadicBound ij.2)
      hT16 hc.1 hc.2.1 hcontour (by positivity) le_rfl
      (lt_of_lt_of_le zero_lt_one hP) hPT
      (by linarith) (by linarith) hh hk
    have hmass := hughesYoungFarSignedCentralStaticMass_le_regularNonLargeEnvelope
      hT hhmem hkmem hij
    have hfactor : 0 ≤ T *
        hughesYoungFarSignedCentralStaticMass T (hughesYoungSmallContour T) P
          (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
          (hughesYoungFullDyadicBound ij.1)
          (hughesYoungFullDyadicBound ij.2) :=
      mul_nonneg (by positivity) (hughesYoungFarSignedCentralStaticMass_nonneg
        (by positivity) (zero_le_one.trans hX) (zero_le_one.trans hY) h k
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
        (hughesYoungFullDyadicBound ij.1) (hughesYoungFullDyadicBound ij.2))
    have hanalytic : 0 ≤ (((15 * T / 4) * (hughesYoungSmallContour T)⁻¹ *
        Real.exp 100 * (6 * T) *
        hughesYoungHeightInputDerivativeConstant Cw j * ((T / 16)⁻¹) ^ j) * L) := by
      have hheight := hughesYoungHeightInputDerivativeConstant_pos hCw j
      have hsmallInv : 0 ≤ (hughesYoungSmallContour T)⁻¹ := inv_nonneg.mpr hc.1.le
      positivity
    calc
      _ ≤ T * hughesYoungFarSignedCentralStaticMass T
          (hughesYoungSmallContour T) P
          (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
          (hughesYoungFullDyadicBound ij.1) (hughesYoungFullDyadicBound ij.2) *
        (((15 * T / 4) * (hughesYoungSmallContour T)⁻¹ * Real.exp 100 *
          (6 * T) * hughesYoungHeightInputDerivativeConstant Cw j *
          ((T / 16)⁻¹) ^ j) * L) := by simpa only [A] using hraw
      _ ≤ T * (3 * (15 + 4 * |Real.eulerMascheroniConstant|) ^ 2 *
          hughesYoungCentralTailSeriesConstant *
          ((((detectorCutoff T) ^ 2 : ℕ) : ℝ)) ^ (11 : ℕ) *
          (hughesYoungActiveArithmeticCutoff T R : ℝ) ^ (6 : ℕ)) *
        (((15 * T / 4) * (hughesYoungSmallContour T)⁻¹ * Real.exp 100 *
          (6 * T) * hughesYoungHeightInputDerivativeConstant Cw j *
          ((T / 16)⁻¹) ^ j) * L) := by gcongr
      _ = E := by rfl
  unfold hughesYoungRegularNonLargeIntegratedCentralTail
  change A * ‖∑ h ∈ S, ∑ k ∈ S,
      ∑ ij ∈ hughesYoungCentralRegularNonLargeBoxes P
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
        hughesYoungIntegratedPointwiseSignedCentral T
          (hughesYoungSmallContour T) (T / 8)
          (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k
          (hughesYoungFarShifts T P
            (hughesYoungFullDyadicScale ij.1)
            (hughesYoungFullDyadicScale ij.2)
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
            (hughesYoungFullDyadicBound ij.1)
            (hughesYoungFullDyadicBound ij.2))‖ ≤ _
  calc
    _ ≤ A * ∑ h ∈ S, ∑ k ∈ S,
        ∑ ij ∈ hughesYoungCentralRegularNonLargeBoxes P
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
          ‖hughesYoungIntegratedPointwiseSignedCentral T
            (hughesYoungSmallContour T) (T / 8)
            (hughesYoungFullDyadicScale ij.1)
            (hughesYoungFullDyadicScale ij.2) h k
            (hughesYoungFarShifts T P
              (hughesYoungFullDyadicScale ij.1)
              (hughesYoungFullDyadicScale ij.2)
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
              (hughesYoungFullDyadicBound ij.1)
              (hughesYoungFullDyadicBound ij.2))‖ := by
      exact mul_le_mul_of_nonneg_left
        ((norm_sum_le _ _).trans (Finset.sum_le_sum fun h _ =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ =>
            norm_sum_le _ _))) hA
    _ = ∑ h ∈ S, ∑ k ∈ S,
        ∑ ij ∈ hughesYoungCentralRegularNonLargeBoxes P
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
          A * ‖hughesYoungIntegratedPointwiseSignedCentral T
            (hughesYoungSmallContour T) (T / 8)
            (hughesYoungFullDyadicScale ij.1)
            (hughesYoungFullDyadicScale ij.2) h k
            (hughesYoungFarShifts T P
              (hughesYoungFullDyadicScale ij.1)
              (hughesYoungFullDyadicScale ij.2)
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
              (hughesYoungFullDyadicBound ij.1)
              (hughesYoungFullDyadicBound ij.2))‖ := by simp_rw [Finset.mul_sum]
    _ ≤ ∑ _h ∈ S, ∑ _k ∈ S, (((K + 2 : ℕ) : ℝ) ^ 2) * E := by
      apply Finset.sum_le_sum
      intro h hhmem
      apply Finset.sum_le_sum
      intro k hkmem
      calc
        _ ≤ ∑ _ij ∈ hughesYoungCentralRegularNonLargeBoxes P
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
            E := Finset.sum_le_sum (hbox h hhmem k hkmem)
        _ = ((hughesYoungCentralRegularNonLargeBoxes P
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K).card : ℝ) * E := by simp
        _ ≤ (((K + 2 : ℕ) : ℝ) ^ 2) * E := by
          apply mul_le_mul_of_nonneg_right _ hE
          exact_mod_cast (calc
            (hughesYoungCentralRegularNonLargeBoxes P
                (hughesYoungReducedLeft h k)
                (hughesYoungReducedRight h k) R K).card ≤
              (hughesYoungActiveDyadicBoxes
                (hughesYoungReducedLeft h k)
                (hughesYoungReducedRight h k) R K).card := by
                  apply Finset.card_le_card
                  intro ij hij
                  exact (Finset.mem_filter.mp
                    (Finset.mem_filter.mp hij).1).1
            _ ≤ (K + 2) ^ 2 := card_hughesYoungActiveDyadicBoxes_le _ _ _ _)
    _ = (S.card : ℝ) ^ 2 * (((K + 2 : ℕ) : ℝ) ^ 2) * E := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ (((((detectorCutoff T) ^ 2 : ℕ) : ℝ) ^ 2) *
          (((K + 2 : ℕ) : ℝ) ^ 2)) * E := by
      have hcardNat : S.card ≤ (detectorCutoff T) ^ 2 := by simp [S]
      have hcard : (S.card : ℝ) ≤ (((detectorCutoff T) ^ 2 : ℕ) : ℝ) := by
        exact_mod_cast hcardNat
      gcongr
    _ = _ := by rfl

/-- The complete regular non-large central family is negligible at the
conductor radius.  This is the unrestricted source consumer: no physical
support predicate remains in its statement. -/
theorem hughesYoungActiveRegularNonLargeIntegratedCompleteCentral_epsilonPowerBound_native :
    EpsilonPowerBound
      (fun T => ‖hughesYoungActiveRegularNonLargeIntegratedCompleteCentral T
        (hughesYoungDFISmoothingScale T) (hughesYoungConductorRadius T)
        (hughesYoungGlobalDepth T)‖)
      (fun T => T) := by
  intro ε hε
  obtain ⟨Cγ, L, hCγ, hL, Cw, hCw, hscaled⟩ :=
    exists_scaled_norm_hughesYoungRegularNonLargeIntegratedCentralTail_le
      4000000
  let C : ℝ := 3 * (15 + 4 * |Real.eulerMascheroniConstant|) ^ 2 *
    hughesYoungCentralTailSeriesConstant * 9 ^ 11 * 649 ^ 6 *
    (15 / 4) * Real.exp 100 * 6 *
    hughesYoungHeightInputDerivativeConstant Cw 4000000 * L
  let A : ℝ := 81 * 103 ^ 2 * C
  have hC : 0 ≤ C := by
    dsimp only [C]
    have hheight := hughesYoungHeightInputDerivativeConstant_pos hCw 4000000
    exact mul_nonneg
      (mul_nonneg hughesYoungCentralTailNumericalConstant_nonneg hheight.le) hL.le
  have hA : 0 ≤ A := by dsimp only [A]; exact mul_nonneg (by norm_num) hC
  apply IsBigO.of_bound A
  filter_upwards [eventually_hughesYoungNativeNonLargeDecayBases,
      eventually_hughesYoungDFISmoothingScale_native_range,
      eventually_four_mul_hughesYoungSmallContour_le_one hCγ,
      eventually_threeHundredTwenty_mul_hughesYoungDFISmoothingScale_sq_lt,
      eventually_hughesYoungDFISmoothingScale_mul_two_detectorCutoff_sq_lt,
      eventually_ge_atTop (16 : ℝ)] with
      T hBases hRange hContour hSmall hCutoff hT16
  have hT : Real.exp 1 ≤ T := hBases.1
  have hT1 : 1 ≤ T := by linarith [Real.exp_one_gt_d9]
  have hT0 : 0 < T := zero_lt_one.trans_le hT1
  have hP0 : 0 < hughesYoungDFISmoothingScale T :=
    zero_lt_one.trans_le hRange.2.1
  let Q : ℝ := (((detectorCutoff T) ^ 2 : ℕ) : ℝ) ^ 2 *
    ((hughesYoungGlobalDepth T + 2 : ℕ) : ℝ) ^ 2
  let E : ℝ := hughesYoungCentralTailPolynomialEnvelope Cw L 4000000 T
    ((((detectorCutoff T) ^ 2 : ℕ) : ℝ))
    (hughesYoungActiveArithmeticCutoff T (hughesYoungConductorRadius T) : ℝ)
  let B : ℝ := (hughesYoungDFISmoothingScale T / (5 * T)) ^ (4000000 : ℕ)
  let F : ℝ := (5 * T / hughesYoungDFISmoothingScale T) ^ (4000000 : ℕ)
  have hB : 0 < B := by dsimp only [B]; exact pow_pos (div_pos hP0 (by positivity)) _
  have hBF : B * F = 1 := by
    dsimp only [B, F]
    rw [← mul_pow]
    have hbase : hughesYoungDFISmoothingScale T / (5 * T) *
        (5 * T / hughesYoungDFISmoothingScale T) = 1 := by
      field_simp [ne_of_gt hP0, ne_of_gt hT0]
    rw [hbase, one_pow]
  have hRaw := hscaled (T := T) (P := hughesYoungDFISmoothingScale T)
    (R := hughesYoungConductorRadius T) (K := hughesYoungGlobalDepth T)
    hT hT16 hRange.2.1 hRange.2.2 hContour.2
  have hUnscaled :
      ‖hughesYoungRegularNonLargeIntegratedCentralTail T
        (hughesYoungDFISmoothingScale T) (hughesYoungConductorRadius T)
        (hughesYoungGlobalDepth T)‖ ≤ Q * (F * E) := by
    have hMultiplied : B *
        ‖hughesYoungRegularNonLargeIntegratedCentralTail T
          (hughesYoungDFISmoothingScale T) (hughesYoungConductorRadius T)
          (hughesYoungGlobalDepth T)‖ ≤ B * (Q * (F * E)) := by
      calc
        _ ≤ Q * E := by simpa only [B, Q, E] using hRaw
        _ = B * (Q * (F * E)) := by
          calc
            Q * E = (B * F) * (Q * E) := by rw [hBF, one_mul]
            _ = B * (Q * (F * E)) := by ac_rfl
    exact le_of_mul_le_mul_left hMultiplied hB
  have hEnvelope : F * E ≤ C * T ^ (-32 : ℝ) := by
    simpa only [F, E, C] using
      hughesYoungNativeCentralTailEnvelope_le_rpow_neg_thirty_two
        hT hL.le hCw hBases.2.2.2
  have hCut := detectorCutoff_sq_le_nine_mul_rpow_one_fiftieth hT1
  have hCutLoose : (((detectorCutoff T) ^ 2 : ℕ) : ℝ) ≤ 9 * T ^ (2 : ℝ) :=
    hCut.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num)) (by norm_num))
  have hCutSq : ((((detectorCutoff T) ^ 2 : ℕ) : ℝ) ^ 2) ≤
      81 * T ^ (4 : ℝ) := by
    calc
      _ ≤ (9 * T ^ (2 : ℝ)) ^ 2 := by gcongr
      _ = 81 * T ^ (4 : ℝ) := by
        rw [mul_pow]
        rw [show (T ^ (2 : ℝ)) ^ 2 = T ^ (4 : ℝ) by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]
          norm_num]
        norm_num
  have hDepth := hughesYoungGlobalDepth_add_two_le_rpow
    (show (0 : ℝ) < 1 by norm_num) hT
  have hDepthSq : (((hughesYoungGlobalDepth T + 2 : ℕ) : ℝ) ^ 2) ≤
      103 ^ 2 * T ^ (2 : ℝ) := by
    have hDepth' : ((hughesYoungGlobalDepth T + 2 : ℕ) : ℝ) ≤
        103 * T ^ (1 : ℝ) := by
      norm_num at hDepth ⊢
      exact hDepth
    calc
      _ ≤ (103 * T ^ (1 : ℝ)) ^ 2 := by gcongr
      _ = 103 ^ 2 * T ^ (2 : ℝ) := by rw [Real.rpow_one, Real.rpow_two]; ring
  have hQ : Q ≤ 81 * 103 ^ 2 * T ^ (6 : ℝ) := by
    dsimp only [Q]
    calc
      _ ≤ (81 * T ^ (4 : ℝ)) * (103 ^ 2 * T ^ (2 : ℝ)) := by gcongr
      _ = 81 * 103 ^ 2 * T ^ (6 : ℝ) := by
        rw [show T ^ (6 : ℝ) = T ^ (4 : ℝ) * T ^ (2 : ℝ) by
          rw [← Real.rpow_add hT0]
          norm_num]
        ring
  have hE0 : 0 ≤ E := by
    dsimp only [E]
    exact hughesYoungCentralTailPolynomialEnvelope_nonneg hT hL.le hCw
      (by positivity) (by positivity)
  have hFE0 : 0 ≤ F * E := mul_nonneg
    (by dsimp only [F]; exact pow_nonneg (div_nonneg (by positivity) hP0.le) _) hE0
  have hBound :
      ‖hughesYoungRegularNonLargeIntegratedCentralTail T
        (hughesYoungDFISmoothingScale T) (hughesYoungConductorRadius T)
        (hughesYoungGlobalDepth T)‖ ≤ A * T ^ (-26 : ℝ) := by
    calc
      _ ≤ Q * (F * E) := hUnscaled
      _ ≤ (81 * 103 ^ 2 * T ^ (6 : ℝ)) * (C * T ^ (-32 : ℝ)) :=
        mul_le_mul hQ hEnvelope hFE0 (by positivity)
      _ = A * T ^ (-26 : ℝ) := by
        dsimp only [A]
        rw [show T ^ (-26 : ℝ) = T ^ (6 : ℝ) * T ^ (-32 : ℝ) by
          rw [← Real.rpow_add hT0]
          norm_num]
        ring
  have hPow : T ^ (-26 : ℝ) ≤ T ^ (1 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
  have hTarget : ‖T ^ ε * |T|‖ = T ^ (1 + ε) := by
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (Real.rpow_nonneg hT0.le _) (abs_nonneg T)), abs_of_pos hT0]
    calc
      T ^ ε * T = T ^ ε * T ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = T ^ (ε + 1) := (Real.rpow_add hT0 _ _).symm
      _ = T ^ (1 + ε) := by ring_nf
  rw [hughesYoungActiveRegularNonLargeIntegratedCompleteCentral_eq_tail_native
    hT16 hRange.2.1 hRange.2.2 hSmall hCutoff]
  rw [Real.norm_eq_abs, abs_abs,
    abs_of_nonneg (norm_nonneg
      (hughesYoungRegularNonLargeIntegratedCentralTail T
        (hughesYoungDFISmoothingScale T) (hughesYoungConductorRadius T)
        (hughesYoungGlobalDepth T))), hTarget]
  exact hBound.trans (mul_le_mul_of_nonneg_left hPow hA)

/-! ## The isolated-boundary part of the non-large central family -/

/-- The complete signed central contribution from the active boxes meeting
one of the two isolated index-zero faces.  This is the central analogue of
`hughesYoungActiveBoundaryOffDiagonal`; it is kept separate because DFI is
never applied on these boxes. -/
noncomputable def hughesYoungActiveBoundaryIntegratedCompleteCentral
    (T : ℝ) (R K : ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∑ ij ∈ hughesYoungActiveBoundaryBoxes
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
        hughesYoungIntegratedFiniteCompleteSignedCentralBox T
          (hughesYoungSmallContour T) (T / 8)
          (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
          (hughesYoungFullDyadicBound ij.1)
          (hughesYoungFullDyadicBound ij.2)

/-- Exact regular/boundary partition of the complete active central source. -/
theorem hughesYoungActiveIntegratedCompleteCentral_eq_regular_add_boundary
    (T : ℝ) (R K : ℕ) :
    hughesYoungActiveIntegratedCompleteCentral T R K =
      hughesYoungActiveRegularIntegratedCompleteCentral T R K +
        hughesYoungActiveBoundaryIntegratedCompleteCentral T R K := by
  classical
  unfold hughesYoungActiveIntegratedCompleteCentral
    hughesYoungActiveRegularIntegratedCompleteCentral
    hughesYoungActiveBoundaryIntegratedCompleteCentral
    hughesYoungCentralRegularBoxes hughesYoungActiveBoundaryBoxes
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h _hh
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _hk
  exact (Finset.sum_filter_add_sum_filter_not
    (s := hughesYoungActiveDyadicBoxes
      (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K)
    (p := fun ij => 0 < ij.1 ∧ 0 < ij.2)
    (f := fun ij =>
      hughesYoungIntegratedFiniteCompleteSignedCentralBox T
        (hughesYoungSmallContour T) (T / 8)
        (hughesYoungFullDyadicScale ij.1)
        (hughesYoungFullDyadicScale ij.2) h k
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
        (hughesYoungFullDyadicBound ij.1)
        (hughesYoungFullDyadicBound ij.2))).symm

/-- The literal non-large central family consists of the regular non-large
boxes and every isolated boundary box.  This identity closes the set-level
gap between the DFI predicate and the source dyadic partition. -/
theorem hughesYoungActiveNonLargeDFIIntegratedCompleteCentral_eq_regular_add_boundary
    (T P : ℝ) (R K : ℕ) :
    hughesYoungActiveNonLargeDFIIntegratedCompleteCentral T P R K =
      hughesYoungActiveRegularNonLargeIntegratedCompleteCentral T P R K +
        hughesYoungActiveBoundaryIntegratedCompleteCentral T R K := by
  have hall := hughesYoungActiveIntegratedCompleteCentral_eq_large_add_nonLarge
    T P R K
  have hregular :=
    hughesYoungActiveRegularIntegratedCompleteCentral_eq_large_add_nonLarge
      T P R K
  have hboundary :=
    hughesYoungActiveIntegratedCompleteCentral_eq_regular_add_boundary T R K
  linear_combination -hall + hregular + hboundary

/-- The initial dyadic scale lies below one. -/
theorem hughesYoungFullDyadicScale_zero_le_one :
    hughesYoungFullDyadicScale 0 ≤ 1 := by
  simp only [hughesYoungFullDyadicScale]
  exact (div_le_one hughesYoungDyadicRatio_pos).2
    one_lt_hughesYoungDyadicRatio.le

/-- On an active box meeting an isolated lower face, the retained
near-shift central source vanishes at the native smoothing scale.  If the
other scale is remote this is dyadic-support disjointness; otherwise both
scales are bounded and the nonzero integral shift window is empty. -/
theorem hughesYoungNearSignedCentralSum_eq_zero_of_boundary_native
    {T c u : ℝ} {R K h k : ℕ} {ij : ℕ × ℕ}
    (hT : 0 < T)
    (hP : 1 ≤ hughesYoungDFISmoothingScale T)
    (hsmall : 320 * hughesYoungDFISmoothingScale T *
        hughesYoungDFISmoothingScale T < T)
    (hij : ij ∈ hughesYoungActiveBoundaryBoxes
      (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K) :
    ∑ r ∈ hughesYoungNearShifts T (hughesYoungDFISmoothingScale T)
        (hughesYoungFullDyadicScale ij.1)
        (hughesYoungFullDyadicScale ij.2)
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
        (hughesYoungFullDyadicBound ij.1)
        (hughesYoungFullDyadicBound ij.2),
      dfiSignedCentralSeries
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) r
        (hughesYoungReducedCleanedShiftWeight T c u
          (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k r) = 0 := by
  classical
  have hboundary := (Finset.mem_filter.mp hij).2
  have hzero : ij.1 = 0 ∨ ij.2 = 0 := by omega
  have hX0 : 0 < hughesYoungFullDyadicScale ij.1 :=
    hughesYoungFullDyadicScale_pos ij.1
  have hY0 : 0 < hughesYoungFullDyadicScale ij.2 :=
    hughesYoungFullDyadicScale_pos ij.2
  rcases hzero with hi | hj
  · by_cases hsep : 4 * hughesYoungFullDyadicScale ij.1 <
        hughesYoungFullDyadicScale ij.2
    · apply Finset.sum_eq_zero
      intro r hr
      exact dfiSignedCentralSeries_reducedCleaned_eq_zero_of_right_separated
        hX0 hY0 hsep hr
    · have hXle : hughesYoungFullDyadicScale ij.1 ≤ 1 := by
        simpa only [hi] using hughesYoungFullDyadicScale_zero_le_one
      have hYle : hughesYoungFullDyadicScale ij.2 ≤ 4 := by
        have hcomp : hughesYoungFullDyadicScale ij.2 ≤
            4 * hughesYoungFullDyadicScale ij.1 := le_of_not_gt hsep
        linarith
      have hPY : hughesYoungDFISmoothingScale T *
          hughesYoungFullDyadicScale ij.2 < T := by
        have hP0 : 0 ≤ hughesYoungDFISmoothingScale T :=
          zero_le_one.trans hP
        have hfirst : hughesYoungDFISmoothingScale T *
            hughesYoungFullDyadicScale ij.2 ≤
              4 * hughesYoungDFISmoothingScale T := by nlinarith
        have hsecond : 4 * hughesYoungDFISmoothingScale T ≤
            320 * hughesYoungDFISmoothingScale T *
              hughesYoungDFISmoothingScale T := by nlinarith
        exact hfirst.trans_lt (hsecond.trans_lt hsmall)
      rw [hughesYoungNearShifts_eq_empty_of_mul_lt hT hY0 hPY]
      simp
  · have hYle : hughesYoungFullDyadicScale ij.2 ≤ 1 := by
      simpa only [hj] using hughesYoungFullDyadicScale_zero_le_one
    have hPY : hughesYoungDFISmoothingScale T *
        hughesYoungFullDyadicScale ij.2 < T := by
      have hP0 : 0 ≤ hughesYoungDFISmoothingScale T :=
        zero_le_one.trans hP
      have hfirst : hughesYoungDFISmoothingScale T *
          hughesYoungFullDyadicScale ij.2 ≤
            hughesYoungDFISmoothingScale T := by nlinarith
      have hsecond : hughesYoungDFISmoothingScale T ≤
          320 * hughesYoungDFISmoothingScale T *
            hughesYoungDFISmoothingScale T := by nlinarith
      exact hfirst.trans_lt (hsecond.trans_lt hsmall)
    rw [hughesYoungNearShifts_eq_empty_of_mul_lt hT hY0 hPY]
    simp

/-- Boundary equation (81): after the preceding source-level vanishing,
the complete finite central box is exactly its equation-(65) far family. -/
theorem hughesYoungIntegratedCompleteCentral_eq_far_of_boundary_native
    {T : ℝ} {R K h k : ℕ} {ij : ℕ × ℕ}
    (hT : 0 < T)
    (hP : 1 ≤ hughesYoungDFISmoothingScale T)
    (hsmall : 320 * hughesYoungDFISmoothingScale T *
        hughesYoungDFISmoothingScale T < T)
    (hij : ij ∈ hughesYoungActiveBoundaryBoxes
      (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K) :
    hughesYoungIntegratedFiniteCompleteSignedCentralBox T
        (hughesYoungSmallContour T) (T / 8)
        (hughesYoungFullDyadicScale ij.1)
        (hughesYoungFullDyadicScale ij.2) h k
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
        (hughesYoungFullDyadicBound ij.1)
        (hughesYoungFullDyadicBound ij.2) =
      hughesYoungIntegratedPointwiseSignedCentral T
        (hughesYoungSmallContour T) (T / 8)
        (hughesYoungFullDyadicScale ij.1)
        (hughesYoungFullDyadicScale ij.2) h k
        (hughesYoungFarShifts T (hughesYoungDFISmoothingScale T)
          (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2)
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
          (hughesYoungFullDyadicBound ij.1)
          (hughesYoungFullDyadicBound ij.2)) := by
  unfold hughesYoungIntegratedFiniteCompleteSignedCentralBox
    hughesYoungIntegratedPointwiseSignedCentral
  apply intervalIntegral.integral_congr
  intro u _hu
  change (T : ℂ) *
      hughesYoungFiniteCompleteSignedCentralBox T
        (hughesYoungSmallContour T) u
        (hughesYoungFullDyadicScale ij.1)
        (hughesYoungFullDyadicScale ij.2) h k
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
        (hughesYoungFullDyadicBound ij.1)
        (hughesYoungFullDyadicBound ij.2) =
    (T : ℂ) *
      ∑ r ∈ hughesYoungFarShifts T (hughesYoungDFISmoothingScale T)
        (hughesYoungFullDyadicScale ij.1)
        (hughesYoungFullDyadicScale ij.2)
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
        (hughesYoungFullDyadicBound ij.1)
        (hughesYoungFullDyadicBound ij.2),
        dfiSignedCentralSeries
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) r
          (hughesYoungReducedCleanedShiftWeight T
            (hughesYoungSmallContour T) u
            (hughesYoungFullDyadicScale ij.1)
            (hughesYoungFullDyadicScale ij.2) h k r)
  rw [hughesYoungFiniteCompleteSignedCentralBox_eq_near_add_far]
  rw [hughesYoungNearSignedCentralSum_eq_zero_of_boundary_native
    hT hP hsmall hij]
  simp only [zero_add, hughesYoungFarSignedCentralBox]

/-- The equation-(65) tail over every active isolated-boundary box. -/
noncomputable def hughesYoungBoundaryIntegratedCentralTail
    (T P : ℝ) (R K : ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∑ ij ∈ hughesYoungActiveBoundaryBoxes
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
        hughesYoungIntegratedPointwiseSignedCentral T
          (hughesYoungSmallContour T) (T / 8)
          (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k
          (hughesYoungFarShifts T P
            (hughesYoungFullDyadicScale ij.1)
            (hughesYoungFullDyadicScale ij.2)
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
            (hughesYoungFullDyadicBound ij.1)
            (hughesYoungFullDyadicBound ij.2))

/-- Finite-sum boundary form of equation (81). -/
theorem hughesYoungActiveBoundaryIntegratedCompleteCentral_eq_tail_native
    {T : ℝ} (hT : 0 < T)
    (hP : 1 ≤ hughesYoungDFISmoothingScale T)
    (hsmall : 320 * hughesYoungDFISmoothingScale T *
        hughesYoungDFISmoothingScale T < T)
    (R K : ℕ) :
    hughesYoungActiveBoundaryIntegratedCompleteCentral T R K =
      hughesYoungBoundaryIntegratedCentralTail T
        (hughesYoungDFISmoothingScale T) R K := by
  classical
  unfold hughesYoungActiveBoundaryIntegratedCompleteCentral
    hughesYoungBoundaryIntegratedCentralTail
  apply Finset.sum_congr rfl
  intro h _hh
  apply Finset.sum_congr rfl
  intro k _hk
  apply Finset.sum_congr rfl
  intro ij hij
  exact hughesYoungIntegratedCompleteCentral_eq_far_of_boundary_native
    hT hP hsmall hij

/-- Source-entry polynomial mass estimate for every active boundary box. -/
theorem hughesYoungFarSignedCentralStaticMass_le_boundaryEnvelope
    {T P : ℝ} {R K h k : ℕ} {ij : ℕ × ℕ}
    (hT : Real.exp 1 ≤ T)
    (hhmem : h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2))
    (hkmem : k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2))
    (hij : ij ∈ hughesYoungActiveBoundaryBoxes
      (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K) :
    hughesYoungFarSignedCentralStaticMass T (hughesYoungSmallContour T) P
        (hughesYoungFullDyadicScale ij.1) (hughesYoungFullDyadicScale ij.2)
        h k (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
        (hughesYoungFullDyadicBound ij.1) (hughesYoungFullDyadicBound ij.2) ≤
      48 * (15 + 4 * |Real.eulerMascheroniConstant|) ^ 2 *
        hughesYoungCentralTailSeriesConstant *
        ((((detectorCutoff T) ^ 2 : ℕ) : ℝ)) ^ (11 : ℕ) *
        (hughesYoungActiveArithmeticCutoff T R : ℝ) ^ (6 : ℕ) := by
  let ell : ℕ := (detectorCutoff T) ^ 2
  let B : ℕ := hughesYoungActiveArithmeticCutoff T R
  have hT1 : 1 ≤ T := by linarith [Real.exp_one_gt_d9]
  have hc := hughesYoungSmallContour_spec hT
  have hh : 0 < h := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hhmem).1
  have hk : 0 < k := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hkmem).1
  have hhle : h ≤ ell := by simpa only [ell] using (Finset.mem_Icc.mp hhmem).2
  have hkle : k ≤ ell := by simpa only [ell] using (Finset.mem_Icc.mp hkmem).2
  have ha : 0 < hughesYoungReducedLeft h k := hughesYoungReducedLeft_pos hh
  have hb : 0 < hughesYoungReducedRight h k := hughesYoungReducedRight_pos hh hk
  have haell : hughesYoungReducedLeft h k ≤ ell :=
    (hughesYoungReducedLeft_le h k).trans hhle
  have hbell : hughesYoungReducedRight h k ≤ ell :=
    (hughesYoungReducedRight_le h k).trans hkle
  have hactive := (Finset.mem_filter.mp hij).1
  have hMnat : hughesYoungFullDyadicBound ij.1 ≤ B := by
    have hraw := hughesYoungFullDyadicBound_le_four_mul_activeConductor_add_one_left
      hactive
    have hprod : hughesYoungReducedLeft h k * hughesYoungReducedRight h k * R ≤
        ell * ell * R := Nat.mul_le_mul_right R (Nat.mul_le_mul haell hbell)
    unfold B hughesYoungActiveArithmeticCutoff
    exact hraw.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 4 hprod) 1)
  have hNnat : hughesYoungFullDyadicBound ij.2 ≤ B := by
    have hraw := hughesYoungFullDyadicBound_le_four_mul_activeConductor_add_one_right
      hactive
    have hprod : hughesYoungReducedLeft h k * hughesYoungReducedRight h k * R ≤
        ell * ell * R := Nat.mul_le_mul_right R (Nat.mul_le_mul haell hbell)
    unfold B hughesYoungActiveArithmeticCutoff
    exact hraw.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 4 hprod) 1)
  have hXB : hughesYoungFullDyadicScale ij.1 ≤ (B : ℝ) := by
    have htwo := two_mul_hughesYoungFullDyadicScale_le_bound ij.1
    exact (by linarith : hughesYoungFullDyadicScale ij.1 ≤
      (hughesYoungFullDyadicBound ij.1 : ℝ)).trans (by exact_mod_cast hMnat)
  have hYB : hughesYoungFullDyadicScale ij.2 ≤ (B : ℝ) := by
    have htwo := two_mul_hughesYoungFullDyadicScale_le_bound ij.2
    exact (by linarith : hughesYoungFullDyadicScale ij.2 ≤
      (hughesYoungFullDyadicBound ij.2 : ℝ)).trans (by exact_mod_cast hNnat)
  have hell1 : 1 ≤ ell := by
    have hcut : 0 < detectorCutoff T := by unfold detectorCutoff; omega
    simpa only [ell] using Nat.one_le_pow 2 (detectorCutoff T) hcut
  have hB1 : 1 ≤ B := by unfold B hughesYoungActiveArithmeticCutoff; omega
  have hR : 0 < R := by
    have hprod := (Finset.mem_filter.mp hactive).2
    have hprodPos : 0 < hughesYoungFullDyadicScale ij.1 *
        hughesYoungFullDyadicScale ij.2 := mul_pos
      (hughesYoungFullDyadicScale_pos ij.1) (hughesYoungFullDyadicScale_pos ij.2)
    have hcastPos : 0 < ((hughesYoungReducedLeft h k *
        hughesYoungReducedRight h k * R : ℕ) : ℝ) := hprodPos.trans_le hprod
    have hnatPos : 0 < hughesYoungReducedLeft h k *
        hughesYoungReducedRight h k * R := by exact_mod_cast hcastPos
    exact pos_of_mul_pos_right hnatPos (Nat.zero_le _)
  have hellB : ell ≤ B := by
    unfold B hughesYoungActiveArithmeticCutoff
    change ell ≤ 4 * (ell * ell * R) + 1
    have hsquare : ell ≤ ell * ell := Nat.le_mul_of_pos_right ell hell1
    have hRmul : ell * ell ≤ ell * ell * R :=
      Nat.le_mul_of_pos_right (ell * ell) hR
    exact hsquare.trans (hRmul.trans (by omega))
  simpa only [ell, B] using
    hughesYoungFarSignedCentralStaticMass_le_polynomial_of_half
      hT1 hc.1.le hc.2.1
      (one_half_le_hughesYoungFullDyadicScale ij.1)
      (one_half_le_hughesYoungFullDyadicScale ij.2)
      (by exact_mod_cast hell1) (by exact_mod_cast hB1)
      hh hk ha hb (by exact_mod_cast hhle) (by exact_mod_cast hkle)
      (by exact_mod_cast haell) (by exact_mod_cast hbell)
      (by exact_mod_cast hellB) hXB hYB
      (by exact_mod_cast hMnat) (by exact_mod_cast hNnat)

/-- Equation-(65) decay summed over the complete active boundary family. -/
theorem exists_scaled_norm_hughesYoungBoundaryIntegratedCentralTail_le
    (j : ℕ) :
    ∃ Cγ L : ℝ, 0 < Cγ ∧ 0 < L ∧ ∃ Cw : ℕ → ℝ,
      (∀ i, 0 < Cw i) ∧
      ∀ {T P : ℝ} {R K : ℕ},
      Real.exp 1 ≤ T → 16 ≤ T → 1 ≤ P → P ≤ T →
      4 * Cγ * hughesYoungSmallContour T ≤ 1 →
      (P / (5 * T)) ^ j *
          ‖hughesYoungBoundaryIntegratedCentralTail T P R K‖ ≤
        (((((detectorCutoff T) ^ 2 : ℕ) : ℝ) ^ 2) *
          (((K + 2 : ℕ) : ℝ) ^ 2)) *
        (16 * hughesYoungCentralTailPolynomialEnvelope Cw L j T
          ((((detectorCutoff T) ^ 2 : ℕ) : ℝ))
          (hughesYoungActiveArithmeticCutoff T R : ℝ)) := by
  obtain ⟨Cγ, L, hCγ, hL, Cw, hCw, hlocal⟩ :=
    exists_norm_hughesYoungIntegratedFarSignedCentral_full_bound j
  refine ⟨Cγ, L, hCγ, hL, Cw, hCw, ?_⟩
  intro T P R K hT hT16 hP hPT hcontour
  classical
  let S := Finset.Icc 1 ((detectorCutoff T) ^ 2)
  let A : ℝ := (P / (5 * T)) ^ j
  let E0 : ℝ := hughesYoungCentralTailPolynomialEnvelope Cw L j T
    ((((detectorCutoff T) ^ 2 : ℕ) : ℝ))
    (hughesYoungActiveArithmeticCutoff T R : ℝ)
  let E : ℝ := 16 * E0
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hE0 : 0 ≤ E0 := by
    dsimp only [E0]
    exact hughesYoungCentralTailPolynomialEnvelope_nonneg hT hL.le hCw
      (by positivity) (by positivity)
  have hE : 0 ≤ E := mul_nonneg (by norm_num) hE0
  have hc := hughesYoungSmallContour_spec hT
  have hbox : ∀ h ∈ S, ∀ k ∈ S,
      ∀ ij ∈ hughesYoungActiveBoundaryBoxes
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
      A * ‖hughesYoungIntegratedPointwiseSignedCentral T
          (hughesYoungSmallContour T) (T / 8)
          (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k
          (hughesYoungFarShifts T P
            (hughesYoungFullDyadicScale ij.1)
            (hughesYoungFullDyadicScale ij.2)
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
            (hughesYoungFullDyadicBound ij.1)
            (hughesYoungFullDyadicBound ij.2))‖ ≤ E := by
    intro h hhmem k hkmem ij hij
    have hh : 0 < h := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hhmem).1
    have hk : 0 < k := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hkmem).1
    have hX := one_half_le_hughesYoungFullDyadicScale ij.1
    have hY := one_half_le_hughesYoungFullDyadicScale ij.2
    have hraw := hlocal (T := T) (c := hughesYoungSmallContour T)
      (H := T / 8) (P := P)
      (X := hughesYoungFullDyadicScale ij.1)
      (Y := hughesYoungFullDyadicScale ij.2) (h := h) (k := k)
      (M := hughesYoungFullDyadicBound ij.1)
      (N := hughesYoungFullDyadicBound ij.2)
      hT16 hc.1 hc.2.1 hcontour (by positivity) le_rfl
      (lt_of_lt_of_le zero_lt_one hP) hPT hX hY hh hk
    have hmass := hughesYoungFarSignedCentralStaticMass_le_boundaryEnvelope
      (P := P) hT hhmem hkmem hij
    have hfactor : 0 ≤ T *
        hughesYoungFarSignedCentralStaticMass T (hughesYoungSmallContour T) P
          (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
          (hughesYoungFullDyadicBound ij.1) (hughesYoungFullDyadicBound ij.2) :=
      mul_nonneg (by positivity) (hughesYoungFarSignedCentralStaticMass_nonneg
        (by positivity) (by linarith) (by linarith) h k
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
        (hughesYoungFullDyadicBound ij.1) (hughesYoungFullDyadicBound ij.2))
    have hanalytic : 0 ≤ (((15 * T / 4) * (hughesYoungSmallContour T)⁻¹ *
        Real.exp 100 * (6 * T) *
        hughesYoungHeightInputDerivativeConstant Cw j * ((T / 16)⁻¹) ^ j) * L) := by
      have hheight := hughesYoungHeightInputDerivativeConstant_pos hCw j
      have hsmallInv : 0 ≤ (hughesYoungSmallContour T)⁻¹ := inv_nonneg.mpr hc.1.le
      positivity
    calc
      _ ≤ T * hughesYoungFarSignedCentralStaticMass T
          (hughesYoungSmallContour T) P
          (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
          (hughesYoungFullDyadicBound ij.1) (hughesYoungFullDyadicBound ij.2) *
        (((15 * T / 4) * (hughesYoungSmallContour T)⁻¹ * Real.exp 100 *
          (6 * T) * hughesYoungHeightInputDerivativeConstant Cw j *
          ((T / 16)⁻¹) ^ j) * L) := by simpa only [A] using hraw
      _ ≤ T * (48 * (15 + 4 * |Real.eulerMascheroniConstant|) ^ 2 *
          hughesYoungCentralTailSeriesConstant *
          ((((detectorCutoff T) ^ 2 : ℕ) : ℝ)) ^ (11 : ℕ) *
          (hughesYoungActiveArithmeticCutoff T R : ℝ) ^ (6 : ℕ)) *
        (((15 * T / 4) * (hughesYoungSmallContour T)⁻¹ * Real.exp 100 *
          (6 * T) * hughesYoungHeightInputDerivativeConstant Cw j *
          ((T / 16)⁻¹) ^ j) * L) := by gcongr
      _ = E := by dsimp only [E, E0, hughesYoungCentralTailPolynomialEnvelope]; ring
  unfold hughesYoungBoundaryIntegratedCentralTail
  change A * ‖∑ h ∈ S, ∑ k ∈ S,
      ∑ ij ∈ hughesYoungActiveBoundaryBoxes
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
        hughesYoungIntegratedPointwiseSignedCentral T
          (hughesYoungSmallContour T) (T / 8)
          (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k
          (hughesYoungFarShifts T P
            (hughesYoungFullDyadicScale ij.1)
            (hughesYoungFullDyadicScale ij.2)
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
            (hughesYoungFullDyadicBound ij.1)
            (hughesYoungFullDyadicBound ij.2))‖ ≤ _
  calc
    _ ≤ A * ∑ h ∈ S, ∑ k ∈ S,
        ∑ ij ∈ hughesYoungActiveBoundaryBoxes
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
          ‖hughesYoungIntegratedPointwiseSignedCentral T
            (hughesYoungSmallContour T) (T / 8)
            (hughesYoungFullDyadicScale ij.1)
            (hughesYoungFullDyadicScale ij.2) h k
            (hughesYoungFarShifts T P
              (hughesYoungFullDyadicScale ij.1)
              (hughesYoungFullDyadicScale ij.2)
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
              (hughesYoungFullDyadicBound ij.1)
              (hughesYoungFullDyadicBound ij.2))‖ := by
      exact mul_le_mul_of_nonneg_left
        ((norm_sum_le _ _).trans (Finset.sum_le_sum fun h _ =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ =>
            norm_sum_le _ _))) hA
    _ = ∑ h ∈ S, ∑ k ∈ S,
        ∑ ij ∈ hughesYoungActiveBoundaryBoxes
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
          A * ‖hughesYoungIntegratedPointwiseSignedCentral T
            (hughesYoungSmallContour T) (T / 8)
            (hughesYoungFullDyadicScale ij.1)
            (hughesYoungFullDyadicScale ij.2) h k
            (hughesYoungFarShifts T P
              (hughesYoungFullDyadicScale ij.1)
              (hughesYoungFullDyadicScale ij.2)
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
              (hughesYoungFullDyadicBound ij.1)
              (hughesYoungFullDyadicBound ij.2))‖ := by simp_rw [Finset.mul_sum]
    _ ≤ ∑ _h ∈ S, ∑ _k ∈ S, (((K + 2 : ℕ) : ℝ) ^ 2) * E := by
      apply Finset.sum_le_sum
      intro h hhmem
      apply Finset.sum_le_sum
      intro k hkmem
      calc
        _ ≤ ∑ _ij ∈ hughesYoungActiveBoundaryBoxes
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
            E := Finset.sum_le_sum (hbox h hhmem k hkmem)
        _ = ((hughesYoungActiveBoundaryBoxes
            (hughesYoungReducedLeft h k)
            (hughesYoungReducedRight h k) R K).card : ℝ) * E := by simp
        _ ≤ (((K + 2 : ℕ) : ℝ) ^ 2) * E := by
          apply mul_le_mul_of_nonneg_right _ hE
          exact_mod_cast (calc
            (hughesYoungActiveBoundaryBoxes
                (hughesYoungReducedLeft h k)
                (hughesYoungReducedRight h k) R K).card ≤
              (hughesYoungActiveDyadicBoxes
                (hughesYoungReducedLeft h k)
                (hughesYoungReducedRight h k) R K).card := by
                  apply Finset.card_le_card
                  intro ij hij
                  exact (Finset.mem_filter.mp hij).1
            _ ≤ (K + 2) ^ 2 := card_hughesYoungActiveDyadicBoxes_le _ _ _ _)
    _ = (S.card : ℝ) ^ 2 * (((K + 2 : ℕ) : ℝ) ^ 2) * E := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ (((((detectorCutoff T) ^ 2 : ℕ) : ℝ) ^ 2) *
          (((K + 2 : ℕ) : ℝ) ^ 2)) * E := by
      have hcardNat : S.card ≤ (detectorCutoff T) ^ 2 := by simp [S]
      have hcard : (S.card : ℝ) ≤ (((detectorCutoff T) ^ 2 : ℕ) : ℝ) := by
        exact_mod_cast hcardNat
      gcongr
    _ = _ := by rfl

/-- The isolated boundary part of the complete non-large central family is
negligible at the conductor radius.  This is the quantitative form of the
boundary equation-(81) identity, including the half-scale dyadic faces. -/
theorem hughesYoungActiveBoundaryIntegratedCompleteCentral_epsilonPowerBound_native :
    EpsilonPowerBound
      (fun T => ‖hughesYoungActiveBoundaryIntegratedCompleteCentral T
        (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)‖)
      (fun T => T) := by
  intro ε hε
  obtain ⟨Cγ, L, hCγ, hL, Cw, hCw, hscaled⟩ :=
    exists_scaled_norm_hughesYoungBoundaryIntegratedCentralTail_le 4000000
  let C : ℝ := 16 * (3 * (15 + 4 * |Real.eulerMascheroniConstant|) ^ 2 *
    hughesYoungCentralTailSeriesConstant * 9 ^ 11 * 649 ^ 6 *
    (15 / 4) * Real.exp 100 * 6) *
    hughesYoungHeightInputDerivativeConstant Cw 4000000 * L
  let A : ℝ := 81 * 103 ^ 2 * C
  have hC : 0 ≤ C := by
    dsimp only [C]
    have hheight := hughesYoungHeightInputDerivativeConstant_pos hCw 4000000
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by positivity)
        hughesYoungCentralTailNumericalConstant_nonneg) hheight.le) hL.le
  have hA : 0 ≤ A := by dsimp only [A]; exact mul_nonneg (by norm_num) hC
  apply IsBigO.of_bound A
  filter_upwards [eventually_hughesYoungNativeNonLargeDecayBases,
      eventually_hughesYoungDFISmoothingScale_native_range,
      eventually_four_mul_hughesYoungSmallContour_le_one hCγ,
      eventually_threeHundredTwenty_mul_hughesYoungDFISmoothingScale_sq_lt,
      eventually_ge_atTop (16 : ℝ)] with
      T hBases hRange hContour hSmall hT16
  have hT : Real.exp 1 ≤ T := hBases.1
  have hT1 : 1 ≤ T := by linarith [Real.exp_one_gt_d9]
  have hT0 : 0 < T := zero_lt_one.trans_le hT1
  have hP0 : 0 < hughesYoungDFISmoothingScale T :=
    zero_lt_one.trans_le hRange.2.1
  let Q : ℝ := (((detectorCutoff T) ^ 2 : ℕ) : ℝ) ^ 2 *
    ((hughesYoungGlobalDepth T + 2 : ℕ) : ℝ) ^ 2
  let E0 : ℝ := hughesYoungCentralTailPolynomialEnvelope Cw L 4000000 T
    ((((detectorCutoff T) ^ 2 : ℕ) : ℝ))
    (hughesYoungActiveArithmeticCutoff T (hughesYoungConductorRadius T) : ℝ)
  let E : ℝ := 16 * E0
  let B : ℝ := (hughesYoungDFISmoothingScale T / (5 * T)) ^ (4000000 : ℕ)
  let F : ℝ := (5 * T / hughesYoungDFISmoothingScale T) ^ (4000000 : ℕ)
  have hB : 0 < B := by dsimp only [B]; exact pow_pos (div_pos hP0 (by positivity)) _
  have hBF : B * F = 1 := by
    dsimp only [B, F]
    rw [← mul_pow]
    have hbase : hughesYoungDFISmoothingScale T / (5 * T) *
        (5 * T / hughesYoungDFISmoothingScale T) = 1 := by
      field_simp [ne_of_gt hP0, ne_of_gt hT0]
    rw [hbase, one_pow]
  have hRaw := hscaled (T := T) (P := hughesYoungDFISmoothingScale T)
    (R := hughesYoungConductorRadius T) (K := hughesYoungGlobalDepth T)
    hT hT16 hRange.2.1 hRange.2.2 hContour.2
  have hUnscaled :
      ‖hughesYoungBoundaryIntegratedCentralTail T
        (hughesYoungDFISmoothingScale T) (hughesYoungConductorRadius T)
        (hughesYoungGlobalDepth T)‖ ≤ Q * (F * E) := by
    have hMultiplied : B *
        ‖hughesYoungBoundaryIntegratedCentralTail T
          (hughesYoungDFISmoothingScale T) (hughesYoungConductorRadius T)
          (hughesYoungGlobalDepth T)‖ ≤ B * (Q * (F * E)) := by
      calc
        _ ≤ Q * E := by simpa only [B, Q, E] using hRaw
        _ = B * (Q * (F * E)) := by
          calc
            Q * E = (B * F) * (Q * E) := by rw [hBF, one_mul]
            _ = B * (Q * (F * E)) := by ac_rfl
    exact le_of_mul_le_mul_left hMultiplied hB
  have hEnvelope : F * E ≤ C * T ^ (-32 : ℝ) := by
    have hbase := hughesYoungNativeCentralTailEnvelope_le_rpow_neg_thirty_two
      (Cw := Cw) (L := L) hT hL.le hCw hBases.2.2.2
    calc
      F * E = 16 * (F * E0) := by
        rw [show E = 16 * E0 by rfl]
        ac_rfl
      _ ≤ 16 * (3 * (15 + 4 * |Real.eulerMascheroniConstant|) ^ 2 *
          hughesYoungCentralTailSeriesConstant * 9 ^ 11 * 649 ^ 6 *
          (15 / 4) * Real.exp 100 * 6 *
          hughesYoungHeightInputDerivativeConstant Cw 4000000 * L *
          T ^ (-32 : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        simpa only [F, E0] using hbase
      _ = C * T ^ (-32 : ℝ) := by dsimp only [C]; ring
  have hCut := detectorCutoff_sq_le_nine_mul_rpow_one_fiftieth hT1
  have hCutLoose : (((detectorCutoff T) ^ 2 : ℕ) : ℝ) ≤ 9 * T ^ (2 : ℝ) :=
    hCut.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num)) (by norm_num))
  have hCutSq : ((((detectorCutoff T) ^ 2 : ℕ) : ℝ) ^ 2) ≤
      81 * T ^ (4 : ℝ) := by
    calc
      _ ≤ (9 * T ^ (2 : ℝ)) ^ 2 := by gcongr
      _ = 81 * T ^ (4 : ℝ) := by
        rw [mul_pow]
        rw [show (T ^ (2 : ℝ)) ^ 2 = T ^ (4 : ℝ) by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]
          norm_num]
        norm_num
  have hDepth := hughesYoungGlobalDepth_add_two_le_rpow
    (show (0 : ℝ) < 1 by norm_num) hT
  have hDepthSq : (((hughesYoungGlobalDepth T + 2 : ℕ) : ℝ) ^ 2) ≤
      103 ^ 2 * T ^ (2 : ℝ) := by
    have hDepth' : ((hughesYoungGlobalDepth T + 2 : ℕ) : ℝ) ≤
        103 * T ^ (1 : ℝ) := by
      norm_num at hDepth ⊢
      exact hDepth
    calc
      _ ≤ (103 * T ^ (1 : ℝ)) ^ 2 := by gcongr
      _ = 103 ^ 2 * T ^ (2 : ℝ) := by rw [Real.rpow_one, Real.rpow_two]; ring
  have hQ : Q ≤ 81 * 103 ^ 2 * T ^ (6 : ℝ) := by
    dsimp only [Q]
    calc
      _ ≤ (81 * T ^ (4 : ℝ)) * (103 ^ 2 * T ^ (2 : ℝ)) := by gcongr
      _ = 81 * 103 ^ 2 * T ^ (6 : ℝ) := by
        rw [show T ^ (6 : ℝ) = T ^ (4 : ℝ) * T ^ (2 : ℝ) by
          rw [← Real.rpow_add hT0]
          norm_num]
        ring
  have hE0 : 0 ≤ E0 := by
    dsimp only [E0]
    exact hughesYoungCentralTailPolynomialEnvelope_nonneg hT hL.le hCw
      (by positivity) (by positivity)
  have hFE : 0 ≤ F * E := mul_nonneg
    (by dsimp only [F]; exact pow_nonneg (div_nonneg (by positivity) hP0.le) _)
    (by dsimp only [E]; positivity)
  have hBound :
      ‖hughesYoungBoundaryIntegratedCentralTail T
        (hughesYoungDFISmoothingScale T) (hughesYoungConductorRadius T)
        (hughesYoungGlobalDepth T)‖ ≤ A * T ^ (-26 : ℝ) := by
    calc
      _ ≤ Q * (F * E) := hUnscaled
      _ ≤ (81 * 103 ^ 2 * T ^ (6 : ℝ)) * (C * T ^ (-32 : ℝ)) :=
        mul_le_mul hQ hEnvelope hFE (by positivity)
      _ = A * T ^ (-26 : ℝ) := by
        dsimp only [A]
        rw [show T ^ (-26 : ℝ) = T ^ (6 : ℝ) * T ^ (-32 : ℝ) by
          rw [← Real.rpow_add hT0]
          norm_num]
        ring
  have hPow : T ^ (-26 : ℝ) ≤ T ^ (1 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
  have hTarget : ‖T ^ ε * |T|‖ = T ^ (1 + ε) := by
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (Real.rpow_nonneg hT0.le _) (abs_nonneg T)), abs_of_pos hT0]
    calc
      T ^ ε * T = T ^ ε * T ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = T ^ (ε + 1) := (Real.rpow_add hT0 _ _).symm
      _ = T ^ (1 + ε) := by ring_nf
  rw [hughesYoungActiveBoundaryIntegratedCompleteCentral_eq_tail_native
    hT0 hRange.2.1 hSmall]
  rw [Real.norm_eq_abs, abs_abs,
    abs_of_nonneg (norm_nonneg
      (hughesYoungBoundaryIntegratedCentralTail T
        (hughesYoungDFISmoothingScale T) (hughesYoungConductorRadius T)
        (hughesYoungGlobalDepth T))), hTarget]
  exact hBound.trans (mul_le_mul_of_nonneg_left hPow hA)

/-- The entire complete non-large DFI central family has native
Hughes--Young size.  The proof consumes the exact regular/boundary partition,
so neither the isolated dyadic faces nor their half scales are omitted. -/
theorem hughesYoungActiveNonLargeDFIIntegratedCompleteCentral_epsilonPowerBound_native :
    EpsilonPowerBound
      (fun T => ‖hughesYoungActiveNonLargeDFIIntegratedCompleteCentral T
        (hughesYoungDFISmoothingScale T) (hughesYoungConductorRadius T)
        (hughesYoungGlobalDepth T)‖)
      (fun T => T) := by
  intro ε hε
  have hsum :=
    (hughesYoungActiveRegularNonLargeIntegratedCompleteCentral_epsilonPowerBound_native.add
      hughesYoungActiveBoundaryIntegratedCompleteCentral_epsilonPowerBound_native) ε hε
  obtain ⟨C, hC, hbound⟩ := hsum.exists_nonneg
  apply IsBigO.of_bound C
  filter_upwards [hbound.bound] with T hsumT
  have hdecomp :=
    hughesYoungActiveNonLargeDFIIntegratedCompleteCentral_eq_regular_add_boundary
      T (hughesYoungDFISmoothingScale T) (hughesYoungConductorRadius T)
        (hughesYoungGlobalDepth T)
  have htri :
      ‖hughesYoungActiveNonLargeDFIIntegratedCompleteCentral T
          (hughesYoungDFISmoothingScale T) (hughesYoungConductorRadius T)
          (hughesYoungGlobalDepth T)‖ ≤
        ‖hughesYoungActiveRegularNonLargeIntegratedCompleteCentral T
          (hughesYoungDFISmoothingScale T) (hughesYoungConductorRadius T)
          (hughesYoungGlobalDepth T)‖ +
        ‖hughesYoungActiveBoundaryIntegratedCompleteCentral T
          (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)‖ := by
    rw [hdecomp]
    exact norm_add_le _ _
  have hfinal := htri.trans <| by
    simpa only [Real.norm_eq_abs, abs_of_nonneg
      (add_nonneg (norm_nonneg _) (norm_nonneg _))] using hsumT
  simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hfinal

/-- The complete source complementary to the large-DFI boxes has native
Hughes--Young size.  This theorem performs the cancellation-preserving
source decomposition before taking norms. -/
theorem hughesYoungNativeComplementarySource_epsilonPowerBound_native :
    EpsilonPowerBound
      (fun T => ‖hughesYoungNativeComplementarySource T
        (hughesYoungDFISmoothingScale T) (hughesYoungConductorRadius T)
        (hughesYoungGlobalDepth T)‖)
      (fun T => T) := by
  intro ε hε
  have hsum :=
    ((hughesYoungConductorActiveNonLargeDFIOffDiagonal_epsilonPowerBound.add
      hughesYoungActiveNonLargeDFIIntegratedCompleteCentral_epsilonPowerBound_native).add
      hughesYoungConductorActiveComplementIntegratedCentral_epsilonPowerBound) ε hε
  obtain ⟨C, hC, hbound⟩ := hsum.exists_nonneg
  apply IsBigO.of_bound C
  filter_upwards [hbound.bound, eventually_ge_atTop (Real.exp 3)] with T hsumT hT
  have hsource :=
    hughesYoungNativeComplementarySource_eq_nonLargeDifference_sub_activeComplement
      (P := hughesYoungDFISmoothingScale T) hT
      (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)
  have htri :
      ‖hughesYoungNativeComplementarySource T
          (hughesYoungDFISmoothingScale T) (hughesYoungConductorRadius T)
          (hughesYoungGlobalDepth T)‖ ≤
        ‖hughesYoungActiveNonLargeDFIOffDiagonal T
          (hughesYoungDFISmoothingScale T) (hughesYoungConductorRadius T)
          (hughesYoungGlobalDepth T)‖ +
        ‖hughesYoungActiveNonLargeDFIIntegratedCompleteCentral T
          (hughesYoungDFISmoothingScale T) (hughesYoungConductorRadius T)
          (hughesYoungGlobalDepth T)‖ +
        ‖hughesYoungActiveComplementIntegratedCentral T
          (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)‖ := by
    rw [hsource]
    calc
      _ ≤ ‖hughesYoungActiveNonLargeDFIOffDiagonal T
            (hughesYoungDFISmoothingScale T) (hughesYoungConductorRadius T)
            (hughesYoungGlobalDepth T) -
          hughesYoungActiveNonLargeDFIIntegratedCompleteCentral T
            (hughesYoungDFISmoothingScale T) (hughesYoungConductorRadius T)
            (hughesYoungGlobalDepth T)‖ +
          ‖hughesYoungActiveComplementIntegratedCentral T
            (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)‖ := norm_sub_le _ _
      _ ≤ _ := by gcongr; exact norm_sub_le _ _
  have hfinal := htri.trans <| by
    simpa only [Real.norm_eq_abs, abs_of_nonneg
      (add_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _))]
      using hsumT
  simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hfinal

/-- Every error term in the exact source-order off-diagonal identity is
negligible after the complete shifted central source has been retained. -/
theorem hughesYoungNativeOffDiagonalRemainder_epsilonPowerBound_native :
    EpsilonPowerBound
      (fun T => ‖hughesYoungNativeOffDiagonalRemainder T
        (hughesYoungDFISmoothingScale T) (hughesYoungConductorRadius T)
        (hughesYoungGlobalDepth T)‖)
      (fun T => T) := by
  intro ε hε
  have hsum :=
    (((((hughesYoungFiniteEquation84IntegratedShiftTail_epsilonPowerBound.add
      hughesYoungFinitePureSmallContourTail_epsilonPowerBound).add
      hughesYoungNativeComplementarySource_epsilonPowerBound_native).add
      hughesYoungConductorActiveLargeDFIIntegratedCentralTail_epsilonPowerBound).add
      hughesYoungConductorLargeDFIPointwiseDiscrepancy_epsilonPowerBound).add
      hughesYoungConductorActiveLargeDFIFarOffDiagonal_epsilonPowerBound) ε hε
  obtain ⟨C, hC, hbound⟩ := hsum.exists_nonneg
  apply IsBigO.of_bound C
  filter_upwards [hbound.bound] with T hsumT
  let a := hughesYoungFiniteEquation84IntegratedShiftTail T
    (hughesYoungGlobalDepth T)
  let b := hughesYoungFinitePureSmallContourTail T (hughesYoungGlobalDepth T)
  let c := hughesYoungNativeComplementarySource T
    (hughesYoungDFISmoothingScale T) (hughesYoungConductorRadius T)
    (hughesYoungGlobalDepth T)
  let d := hughesYoungActiveLargeDFIIntegratedCentralTail T
    (hughesYoungDFISmoothingScale T) (hughesYoungConductorRadius T)
    (hughesYoungGlobalDepth T)
  let e := hughesYoungActiveLargeDFIPointwiseDiscrepancy T
    (hughesYoungDFISmoothingScale T) (hughesYoungConductorRadius T)
    (hughesYoungGlobalDepth T)
  let f := hughesYoungActiveLargeDFIFarOffDiagonal T
    (hughesYoungDFISmoothingScale T) (hughesYoungConductorRadius T)
    (hughesYoungGlobalDepth T)
  have htri :
      ‖hughesYoungNativeOffDiagonalRemainder T
          (hughesYoungDFISmoothingScale T) (hughesYoungConductorRadius T)
          (hughesYoungGlobalDepth T)‖ ≤
        ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ + ‖f‖ := by
    change ‖-a - b + c - d + e + f‖ ≤ _
    calc
      _ ≤ ‖-a - b + c - d + e‖ + ‖f‖ := norm_add_le _ _
      _ ≤ (‖-a - b + c - d‖ + ‖e‖) + ‖f‖ := by gcongr; exact norm_add_le _ _
      _ ≤ ((‖-a - b + c‖ + ‖d‖) + ‖e‖) + ‖f‖ := by gcongr; exact norm_sub_le _ _
      _ ≤ (((‖-a - b‖ + ‖c‖) + ‖d‖) + ‖e‖) + ‖f‖ := by gcongr; exact norm_add_le _ _
      _ ≤ ((((‖-a‖ + ‖b‖) + ‖c‖) + ‖d‖) + ‖e‖) + ‖f‖ := by
        gcongr
        exact norm_sub_le _ _
      _ = ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ + ‖f‖ := by rw [norm_neg]
  have hfinal := htri.trans <| by
    simpa only [a, b, c, d, e, f, Real.norm_eq_abs,
      abs_of_nonneg (add_nonneg
        (add_nonneg
          (add_nonneg
            (add_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))
              (norm_nonneg _)) (norm_nonneg _)) (norm_nonneg _))
        (norm_nonneg _))] using hsumT
  simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hfinal

/-- The complete finite active off-diagonal moment has native fourth-moment
size.  This is the Hughes--Young consumer of the exact DFI error theorem. -/
theorem hughesYoungConductorActiveFiniteOffDiagonal_epsilonPowerBound_native :
    EpsilonPowerBound
      (fun T => ‖hughesYoungActiveFiniteOffDiagonal T (T / 8)
        (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)‖)
      (fun T => T) := by
  intro ε hε
  have hsum :=
    (hughesYoungCompleteShiftedIntegratedCentral_epsilonPowerBound.add
      hughesYoungNativeOffDiagonalRemainder_epsilonPowerBound_native) ε hε
  obtain ⟨C, hC, hbound⟩ := hsum.exists_nonneg
  apply IsBigO.of_bound C
  filter_upwards [hbound.bound, eventually_ge_atTop (Real.exp 3),
      eventually_ge_atTop (16 : ℝ),
      eventually_hughesYoungDFISmoothingScale_native_range] with
      T hsumT hT hT16 hRange
  have hdecomp :=
    hughesYoungActiveFiniteOffDiagonal_eq_completeShifted_add_remainder
      (P := hughesYoungDFISmoothingScale T) hT hT16
      hRange.2.1 hRange.2.2
      (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)
  have htri :
      ‖hughesYoungActiveFiniteOffDiagonal T (T / 8)
          (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)‖ ≤
        ‖hughesYoungCompleteShiftedIntegratedCentral T‖ +
        ‖hughesYoungNativeOffDiagonalRemainder T
          (hughesYoungDFISmoothingScale T) (hughesYoungConductorRadius T)
          (hughesYoungGlobalDepth T)‖ := by
    rw [hdecomp]
    exact norm_add_le _ _
  have hfinal := htri.trans <| by
    simpa only [Real.norm_eq_abs, abs_of_nonneg
      (add_nonneg (norm_nonneg _) (norm_nonneg _))] using hsumT
  simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hfinal

/-- The complete finite active smoothed moment, with its diagonal and
off-diagonal parts both assembled, has native fourth-moment size. -/
theorem hughesYoungConductorActiveFiniteSmoothedMoment_epsilonPowerBound_native :
    EpsilonPowerBound
      (fun T => ‖hughesYoungActiveFiniteSmoothedMoment T (T / 8)
        (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)‖)
      (fun T => T) := by
  intro ε hε
  have hsum :=
    (hughesYoungConductorFiniteDiagonal_epsilonPowerBound.add
      hughesYoungConductorActiveFiniteOffDiagonal_epsilonPowerBound_native) ε hε
  obtain ⟨C, hC, hbound⟩ := hsum.exists_nonneg
  apply IsBigO.of_bound C
  filter_upwards [hbound.bound, eventually_ge_atTop (Real.exp 1)] with T hsumT hT
  have hdecomp := hughesYoungActiveFiniteSmoothedMoment_eq_diagonal_add_offDiagonal
    hT (T / 8) (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)
  have htri :
      ‖hughesYoungActiveFiniteSmoothedMoment T (T / 8)
          (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)‖ ≤
        ‖hughesYoungActiveFiniteDiagonal T (T / 8)
          (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)‖ +
        ‖hughesYoungActiveFiniteOffDiagonal T (T / 8)
          (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)‖ := by
    rw [hdecomp]
    exact norm_add_le _ _
  have hfinal := htri.trans <| by
    simpa only [Real.norm_eq_abs, abs_of_nonneg
      (add_nonneg (norm_nonneg _) (norm_nonneg _))] using hsumT
  simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hfinal

/-! ## The active finite-height truncation -/

/-- Uniform polynomial majorant for one active mollifier-pair vertical tail. -/
theorem hughesYoungActiveVerticalTailPairMajorant_le_terminal_native
    {T H C D : ℝ} (hT : Real.exp 1 ≤ T) (hD : 0 ≤ D)
    (a b R K : ℕ) :
    hughesYoungActiveVerticalTailPairMajorant C D T H a b R K ≤
      (((K + 2) ^ 2 : ℕ) : ℝ) *
        (hughesYoungFullDyadicBound (K + 1) : ℝ) ^ 4 *
        ((Real.log T * Real.exp (4 * C) * D) *
          (Real.exp (-40 * H ^ 2) * Real.sqrt (Real.pi / 40))) := by
  classical
  let B := hughesYoungFullDyadicBound (K + 1)
  let E : ℝ := (Real.log T * Real.exp (4 * C) * D) *
    (Real.exp (-40 * H ^ 2) * Real.sqrt (Real.pi / 40))
  have hT1 : (1 : ℝ) ≤ T := by linarith [Real.exp_one_gt_d9]
  have hE0 : 0 ≤ E := by
    dsimp only [E]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (Real.log_nonneg hT1) (Real.exp_pos _).le) hD)
      (mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _))
  have hbox : ∀ ij ∈ hughesYoungActiveDyadicBoxes a b R K,
      (∑ _m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
        ∑ _n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.2),
          (Real.log T * Real.exp (4 * C) * D *
              (max (hughesYoungFullDyadicBound ij.1)
                (hughesYoungFullDyadicBound ij.2) : ℝ) ^ 2) *
            (Real.exp (-40 * H ^ 2) * Real.sqrt (Real.pi / 40))) ≤
        (B : ℝ) ^ 4 * E := by
    intro ij hij
    have hrect := (Finset.mem_filter.mp hij).1
    have hi : ij.1 < K + 2 := by
      exact (Finset.mem_product.mp hrect).1 |> Finset.mem_range.mp
    have hj : ij.2 < K + 2 := by
      exact (Finset.mem_product.mp hrect).2 |> Finset.mem_range.mp
    have hiB : hughesYoungFullDyadicBound ij.1 ≤ B :=
      hughesYoungFullDyadicBound_le_terminal hi
    have hjB : hughesYoungFullDyadicBound ij.2 ≤ B :=
      hughesYoungFullDyadicBound_le_terminal hj
    have hmaxB : max (hughesYoungFullDyadicBound ij.1)
        (hughesYoungFullDyadicBound ij.2) ≤ B := max_le hiB hjB
    have hterm :
        (Real.log T * Real.exp (4 * C) * D *
              (max (hughesYoungFullDyadicBound ij.1)
                (hughesYoungFullDyadicBound ij.2) : ℝ) ^ 2) *
            (Real.exp (-40 * H ^ 2) * Real.sqrt (Real.pi / 40)) ≤
          (B : ℝ) ^ 2 * E := by
      dsimp only [E]
      have hmaxCast : (max (hughesYoungFullDyadicBound ij.1)
          (hughesYoungFullDyadicBound ij.2) : ℝ) ≤ B := by exact_mod_cast hmaxB
      have hfront : 0 ≤ Real.log T * Real.exp (4 * C) * D :=
        mul_nonneg (mul_nonneg (Real.log_nonneg hT1) (Real.exp_pos _).le) hD
      have hgauss : 0 ≤ Real.exp (-40 * H ^ 2) * Real.sqrt (Real.pi / 40) :=
        mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _)
      calc
        _ ≤ (Real.log T * Real.exp (4 * C) * D * (B : ℝ) ^ 2) *
            (Real.exp (-40 * H ^ 2) * Real.sqrt (Real.pi / 40)) := by gcongr
        _ = (B : ℝ) ^ 2 *
            ((Real.log T * Real.exp (4 * C) * D) *
              (Real.exp (-40 * H ^ 2) * Real.sqrt (Real.pi / 40))) := by ring
    have hcardI : ((Finset.Icc 1
        (hughesYoungFullDyadicBound ij.1)).card : ℝ) ≤ B := by
      exact_mod_cast ((by simp : (Finset.Icc 1
        (hughesYoungFullDyadicBound ij.1)).card ≤
          hughesYoungFullDyadicBound ij.1).trans hiB)
    have hcardJ : ((Finset.Icc 1
        (hughesYoungFullDyadicBound ij.2)).card : ℝ) ≤ B := by
      exact_mod_cast ((by simp : (Finset.Icc 1
        (hughesYoungFullDyadicBound ij.2)).card ≤
          hughesYoungFullDyadicBound ij.2).trans hjB)
    calc
      _ ≤ ∑ _m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
          ∑ _n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.2),
            (B : ℝ) ^ 2 * E := by
        apply Finset.sum_le_sum
        intro m hm
        apply Finset.sum_le_sum
        intro n hn
        exact hterm
      _ = ((Finset.Icc 1 (hughesYoungFullDyadicBound ij.1)).card : ℝ) *
          ((Finset.Icc 1 (hughesYoungFullDyadicBound ij.2)).card : ℝ) *
            ((B : ℝ) ^ 2 * E) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring
      _ ≤ (B : ℝ) * (B : ℝ) * ((B : ℝ) ^ 2 * E) := by gcongr
      _ = (B : ℝ) ^ 4 * E := by ring
  have hcard : ((hughesYoungActiveDyadicBoxes a b R K).card : ℝ) ≤
      (((K + 2) ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast card_hughesYoungActiveDyadicBoxes_le a b R K
  unfold hughesYoungActiveVerticalTailPairMajorant
  calc
    _ ≤ ∑ ij ∈ hughesYoungActiveDyadicBoxes a b R K,
        (B : ℝ) ^ 4 * E := Finset.sum_le_sum hbox
    _ = ((hughesYoungActiveDyadicBoxes a b R K).card : ℝ) *
        ((B : ℝ) ^ 4 * E) := by simp
    _ ≤ (((K + 2) ^ 2 : ℕ) : ℝ) * ((B : ℝ) ^ 4 * E) := by gcongr
    _ = _ := by dsimp only [B, E]; ring

/-- The active global vertical-tail majorant loses only the squared
mollifier coefficient mass beyond the finite dyadic polynomial. -/
theorem hughesYoungActiveVerticalTailMajorant_le_terminal_native
    {T H C D : ℝ} (hT : Real.exp 1 ≤ T) (hD : 0 ≤ D)
    (R K : ℕ) :
    hughesYoungActiveVerticalTailMajorant C D T H R K ≤
      hughesYoungMollifierCoefficientMass T ^ 2 * (1 / Real.pi) *
        ((((K + 2) ^ 2 : ℕ) : ℝ) *
          (hughesYoungFullDyadicBound (K + 1) : ℝ) ^ 4 *
          ((Real.log T * Real.exp (4 * C) * D) *
            (Real.exp (-40 * H ^ 2) * Real.sqrt (Real.pi / 40)))) := by
  classical
  let S := Finset.Icc 1 ((detectorCutoff T) ^ 2)
  let E : ℝ := ((((K + 2) ^ 2 : ℕ) : ℝ) *
    (hughesYoungFullDyadicBound (K + 1) : ℝ) ^ 4 *
    ((Real.log T * Real.exp (4 * C) * D) *
      (Real.exp (-40 * H ^ 2) * Real.sqrt (Real.pi / 40))))
  have hE0 : 0 ≤ E := by
    have hT1 : (1 : ℝ) ≤ T := by linarith [Real.exp_one_gt_d9]
    dsimp only [E]
    exact mul_nonneg (mul_nonneg (by positivity) (by positivity))
      (mul_nonneg
        (mul_nonneg (mul_nonneg (Real.log_nonneg hT1) (Real.exp_pos _).le) hD)
        (mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _)))
  unfold hughesYoungActiveVerticalTailMajorant
  calc
    _ ≤ ∑ h ∈ S, ∑ k ∈ S,
        ‖shortMobiusSquareCoeff T h‖ * ‖shortMobiusSquareCoeff T k‖ *
          (1 / Real.pi) * E := by
      apply Finset.sum_le_sum
      intro h hh
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_left
        (hughesYoungActiveVerticalTailPairMajorant_le_terminal_native hT hD
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K)
        (mul_nonneg
          (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity))
    _ = (∑ h ∈ S, ‖shortMobiusSquareCoeff T h‖) ^ 2 *
        (1 / Real.pi) * E := by
      let a : ℕ → ℝ := fun n => ‖shortMobiusSquareCoeff T n‖
      have hprod :
          (∑ h ∈ S, a h) * (∑ k ∈ S, a k) =
            ∑ h ∈ S, ∑ k ∈ S, a h * a k := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro h _hh
        rw [Finset.mul_sum]
      calc
        (∑ h ∈ S, ∑ k ∈ S,
            ‖shortMobiusSquareCoeff T h‖ * ‖shortMobiusSquareCoeff T k‖ *
              (1 / Real.pi) * E) =
            (∑ h ∈ S, ∑ k ∈ S, a h * a k) * (1 / Real.pi) * E := by
          dsimp only [a]
          rw [Finset.sum_mul, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro h _hh
          rw [Finset.sum_mul, Finset.sum_mul]
        _ = ((∑ h ∈ S, a h) * (∑ k ∈ S, a k)) *
              (1 / Real.pi) * E := by rw [hprod]
        _ = (∑ h ∈ S, ‖shortMobiusSquareCoeff T h‖) ^ 2 *
              (1 / Real.pi) * E := by rw [pow_two]
    _ = _ := by
      unfold hughesYoungMollifierCoefficientMass
      rfl

/-- At height `T/8`, the whole active contour and its finite-height
realization differ by less than every positive power of the fourth-moment
scale. -/
theorem hughesYoungConductorActiveVerticalTail_epsilonPowerBound_native :
    EpsilonPowerBound
      (fun T =>
        ‖hughesYoungActiveWholeSmoothedMoment T
              (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T) -
            hughesYoungActiveFiniteSmoothedMoment T (T / 8)
              (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)‖)
      (fun T => T) := by
  intro ε hε
  obtain ⟨C, D, hC, hD, htail⟩ :=
    exists_norm_hughesYoungActiveWholeSmoothedMoment_sub_finite_le
  let A : ℝ :=
    (15 / 4) * 81 ^ 2 * (1 / Real.pi) * 103 ^ 2 * 7 ^ 4 *
      Real.exp (4 * C) * D * Real.sqrt (Real.pi / 40)
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hbaseRpow : Tendsto (fun T : ℝ =>
      T ^ (412 : ℝ) * Real.exp (-(5 / 8 : ℝ) * T ^ 2))
      atTop (nhds 0) :=
    (rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg
      (by norm_num : (0 : ℝ) < 5 / 8) 412).tendsto_zero_of_tendsto
        (Real.tendsto_exp_atBot.comp
          (tendsto_id.const_mul_atTop_of_neg
            (by norm_num : (-(1 / 2 : ℝ)) < 0)))
  have hbase : Tendsto (fun T : ℝ =>
      T ^ (412 : ℕ) * Real.exp (-(5 / 8 : ℝ) * T ^ 2))
      atTop (nhds 0) := by
    simpa only [← Real.rpow_natCast] using hbaseRpow
  have hlimit : Tendsto (fun T : ℝ =>
      A * (T ^ (412 : ℕ) * Real.exp (-(5 / 8 : ℝ) * T ^ 2)))
      atTop (nhds 0) := by
    simpa only [mul_zero] using hbase.const_mul A
  have hsmall : ∀ᶠ T : ℝ in atTop,
      A * (T ^ (412 : ℕ) * Real.exp (-(5 / 8 : ℝ) * T ^ 2)) ≤ 1 :=
    (hlimit.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono
      fun _ h => h.le
  apply IsBigO.of_bound 1
  filter_upwards [hsmall, eventually_ge_atTop (Real.exp 1)] with T hsmallT hT
  have hT1 : 1 ≤ T := by linarith [Real.exp_one_gt_d9]
  have hT2 : 2 ≤ T := by linarith [Real.exp_one_gt_two]
  have hT0 : 0 < T := zero_lt_one.trans_le hT1
  have hR : 0 < hughesYoungConductorRadius T :=
    hughesYoungConductorRadius_pos hT1
  have hcover : ∀ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∀ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        (((hughesYoungReducedLeft h k) *
          (hughesYoungReducedRight h k) * hughesYoungConductorRadius T : ℕ) : ℝ) ≤
            hughesYoungDyadicRatio ^ (hughesYoungGlobalDepth T + 1) := by
    intro h hh k hk
    exact hughesYoungConductor_cover hT2 hh hk
  have hraw := htail (q := 1000) (by norm_num) hR
    (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 2 * (1000 : ℝ) - 1 / 2)
    hT (by positivity : (0 : ℝ) ≤ T / 8) hcover
  have hterminal := hughesYoungActiveVerticalTailMajorant_le_terminal_native
    (C := C) (H := T / 8) hT hD.le
      (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)
  have hmass := hughesYoungMollifierCoefficientMass_le_height_fourth hT1
  have hmass0 := hughesYoungMollifierCoefficientMass_nonneg T
  have hmass' : hughesYoungMollifierCoefficientMass T ≤
      81 * T ^ (4 : ℕ) := by
    rw [← Real.rpow_natCast]
    exact hmass
  have hdepth := hughesYoungGlobalDepth_add_two_le_rpow
    (by norm_num : (0 : ℝ) < 1) hT
  norm_num [Real.rpow_one] at hdepth
  have hfull := hughesYoungTerminalFullDyadicBound_le_seven_mul_pow_hundred hT
  have hlog : Real.log T ≤ T := Real.log_le_self hT0.le
  have hlog0 : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hmajorant :
      (15 * T / 4) * hughesYoungActiveVerticalTailMajorant C D T (T / 8)
          (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T) ≤
        A * (T ^ (412 : ℕ) * Real.exp (-(5 / 8 : ℝ) * T ^ 2)) := by
    calc
      _ ≤ (15 * T / 4) *
          (hughesYoungMollifierCoefficientMass T ^ 2 * (1 / Real.pi) *
            ((((hughesYoungGlobalDepth T + 2) ^ 2 : ℕ) : ℝ) *
              (hughesYoungFullDyadicBound (hughesYoungGlobalDepth T + 1) : ℝ) ^ 4 *
              ((Real.log T * Real.exp (4 * C) * D) *
                (Real.exp (-40 * (T / 8) ^ 2) *
                  Real.sqrt (Real.pi / 40))))) := by gcongr
      _ ≤ (15 * T / 4) *
          ((81 * T ^ (4 : ℕ)) ^ 2 * (1 / Real.pi) *
            ((103 * T) ^ 2 * (7 * T ^ (100 : ℕ)) ^ 4 *
              ((T * Real.exp (4 * C) * D) *
                (Real.exp (-40 * (T / 8) ^ 2) *
                  Real.sqrt (Real.pi / 40))))) := by
            push_cast
            gcongr
      _ = A * (T ^ (412 : ℕ) *
          Real.exp (-(5 / 8 : ℝ) * T ^ 2)) := by
            dsimp only [A]
            ring_nf
  have hbound := hraw.trans (hmajorant.trans hsmallT)
  have htarget : ‖T ^ ε * |T|‖ = T ^ (1 + ε) := by
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (Real.rpow_nonneg hT0.le _) (abs_nonneg T)), abs_of_pos hT0]
    calc
      T ^ ε * T = T ^ ε * T ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = T ^ (ε + 1) := (Real.rpow_add hT0 _ _).symm
      _ = T ^ (1 + ε) := by ring_nf
  rw [Real.norm_eq_abs, abs_abs,
    abs_of_nonneg (norm_nonneg
      (hughesYoungActiveWholeSmoothedMoment T
          (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T) -
        hughesYoungActiveFiniteSmoothedMoment T (T / 8)
          (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T))), htarget]
  have hone : 1 ≤ 1 * T ^ (1 + ε) := by
    simpa using Real.one_le_rpow hT1 (show 0 ≤ 1 + ε by linarith)
  exact hbound.trans hone

/-- The whole active smoothed moment inherits the finite native estimate
after the Gaussian vertical tail is restored. -/
theorem hughesYoungConductorActiveWholeSmoothedMoment_epsilonPowerBound_native :
    EpsilonPowerBound
      (fun T => ‖hughesYoungActiveWholeSmoothedMoment T
        (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)‖)
      (fun T => T) := by
  intro ε hε
  have hsum :=
    (hughesYoungConductorActiveVerticalTail_epsilonPowerBound_native.add
      hughesYoungConductorActiveFiniteSmoothedMoment_epsilonPowerBound_native) ε hε
  obtain ⟨C, hC, hbound⟩ := hsum.exists_nonneg
  apply IsBigO.of_bound C
  filter_upwards [hbound.bound] with T hsumT
  have htri :
      ‖hughesYoungActiveWholeSmoothedMoment T
          (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)‖ ≤
        ‖hughesYoungActiveWholeSmoothedMoment T
            (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T) -
          hughesYoungActiveFiniteSmoothedMoment T (T / 8)
            (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)‖ +
        ‖hughesYoungActiveFiniteSmoothedMoment T (T / 8)
          (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)‖ := by
    have hident : hughesYoungActiveWholeSmoothedMoment T
          (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T) =
        (hughesYoungActiveWholeSmoothedMoment T
            (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T) -
          hughesYoungActiveFiniteSmoothedMoment T (T / 8)
            (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)) +
        hughesYoungActiveFiniteSmoothedMoment T (T / 8)
          (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T) := by ring
    calc
      _ = ‖(hughesYoungActiveWholeSmoothedMoment T
              (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T) -
            hughesYoungActiveFiniteSmoothedMoment T (T / 8)
              (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)) +
          hughesYoungActiveFiniteSmoothedMoment T (T / 8)
            (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)‖ :=
        congrArg norm hident
      _ ≤ _ := norm_add_le _ _
  have hfinal := htri.trans <| by
    simpa only [Real.norm_eq_abs, abs_of_nonneg
      (add_nonneg (norm_nonneg _) (norm_nonneg _))] using hsumT
  simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hfinal

/-- The exact Hughes--Young smooth fourth moment satisfies the native
`T^(1+epsilon)` estimate after the active source and its opening-line
remainder are reassembled. -/
theorem hughesYoungSmoothedMoment_epsilonPowerBound_native :
    EpsilonPowerBound hughesYoungSmoothedMoment (fun T => T) := by
  intro ε hε
  have hsum :=
    (hughesYoungConductorActiveWholeSmoothedMoment_epsilonPowerBound_native.add
      hughesYoungConductorOpeningRemainder_epsilonPowerBound) ε hε
  obtain ⟨C, hC, hbound⟩ := hsum.exists_nonneg
  apply IsBigO.of_bound C
  filter_upwards [hbound.bound, eventually_ge_atTop (Real.exp 1)] with T hsumT hT
  have hT1 : 1 ≤ T := by linarith [Real.exp_one_gt_d9]
  have hT2 : 2 ≤ T := by linarith [Real.exp_one_gt_two]
  have hR : 0 < hughesYoungConductorRadius T :=
    hughesYoungConductorRadius_pos hT1
  have hcover : ∀ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∀ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        (((hughesYoungReducedLeft h k) *
          (hughesYoungReducedRight h k) * hughesYoungConductorRadius T : ℕ) : ℝ) ≤
            hughesYoungDyadicRatio ^ (hughesYoungGlobalDepth T + 1) := by
    intro h hh k hk
    exact hughesYoungConductor_cover hT2 hh hk
  have heq := ofReal_hughesYoungSmoothedMoment_eq_active_add_remainder
    (q := 1000) (R := hughesYoungConductorRadius T)
    (K := hughesYoungGlobalDepth T) (by norm_num)
    hR (1 / 2 : ℝ) (by norm_num) (by norm_num) hT hcover
  have htri :
      |hughesYoungSmoothedMoment T| ≤
        ‖hughesYoungActiveWholeSmoothedMoment T
          (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)‖ +
        ‖hughesYoungActiveWholeSmoothedRemainder 1000 T
          (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)‖ := by
    calc
      _ = ‖(hughesYoungSmoothedMoment T : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs]
      _ = ‖hughesYoungActiveWholeSmoothedMoment T
            (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T) +
          hughesYoungActiveWholeSmoothedRemainder 1000 T
            (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)‖ :=
        congrArg norm heq
      _ ≤ _ := norm_add_le _ _
  have hfinal := htri.trans <| by
    simpa only [Real.norm_eq_abs, abs_of_nonneg
      (add_nonneg (norm_nonneg _) (norm_nonneg _))] using hsumT
  simpa only [Real.norm_eq_abs, abs_abs] using hfinal

/-- The native Hughes--Young twisted fourth-moment theorem.  Its proof
starts from the exact sharp moment, uses the source smooth majorant, and
then consumes the complete DFI/Hughes--Young assembly above. -/
theorem twistedZetaFourthMoment_native : TwistedZetaFourthMomentProp := by
  intro ε hε
  have hsmooth := hughesYoungSmoothedMoment_epsilonPowerBound_native ε hε
  obtain ⟨C, hC, hbound⟩ := hsmooth.exists_nonneg
  apply IsBigO.of_bound C
  filter_upwards [hbound.bound, eventually_ge_atTop (Real.exp 1)] with T hboundT hT
  have hT0 : 0 < T := (Real.exp_pos 1).trans_le hT
  have hmomentNonneg : 0 ≤ twistedZetaFourthMoment T := by
    rw [twistedZetaFourthMoment, intervalIntegral.integral_of_le (by linarith)]
    apply MeasureTheory.integral_nonneg
    intro t
    dsimp [twistedZetaMomentIntegrand]
    positivity
  have hsmoothNonneg := hughesYoungSmoothedMoment_nonneg T
  have hmajor := twistedZetaFourthMoment_le_hughesYoungSmoothedMoment hT0
  rw [Real.norm_eq_abs, abs_abs, abs_of_nonneg hmomentNonneg]
  exact hmajor.trans <| by
    simpa only [Real.norm_eq_abs, abs_abs, abs_of_nonneg hsmoothNonneg] using hboundT

end RiemannZeta.GuthMaynard

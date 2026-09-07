import PrimeShell.KernelSymmetry

namespace PrimeShell

noncomputable section

open Set MeasureTheory Real
open Zeta23 Zeta23.PrimeSide

/-- The sine quotient occurring in the exact symmetrized difference kernel. -/
def sineQuotient (q d : ℝ) : ℝ := Real.sin (q * d / 2) / q

/-- A Lipschitz estimate for the exact sine quotient, with no extension through
`q = 0`.  The deliberately asymmetric denominator is useful when the first
frequency has the explicit lower bound furnished by a dyadic block. -/
theorem abs_sineQuotient_sub_sineQuotient_le
    {q q' d : ℝ} (hq : 0 < q) (hq' : 0 < q') (hd : 0 ≤ d) :
    |sineQuotient q d - sineQuotient q' d| ≤
      d * |q - q'| / q := by
  unfold sineQuotient
  rw [show Real.sin (q * d / 2) / q - Real.sin (q' * d / 2) / q' =
      (Real.sin (q * d / 2) - Real.sin (q' * d / 2)) / q +
        Real.sin (q' * d / 2) * (1 / q - 1 / q') by
    field_simp [hq.ne', hq'.ne']
    ring]
  calc
    |(Real.sin (q * d / 2) - Real.sin (q' * d / 2)) / q +
        Real.sin (q' * d / 2) * (1 / q - 1 / q')| ≤
        |Real.sin (q * d / 2) - Real.sin (q' * d / 2)| / q +
          |Real.sin (q' * d / 2)| * |1 / q - 1 / q'| := by
      calc
        |(Real.sin (q * d / 2) - Real.sin (q' * d / 2)) / q +
            Real.sin (q' * d / 2) * (1 / q - 1 / q')| ≤
            |(Real.sin (q * d / 2) - Real.sin (q' * d / 2)) / q| +
              |Real.sin (q' * d / 2) * (1 / q - 1 / q')| :=
          abs_add_le _ _
        _ = |Real.sin (q * d / 2) - Real.sin (q' * d / 2)| / q +
              |Real.sin (q' * d / 2)| * |1 / q - 1 / q'| := by
          rw [abs_div, abs_of_pos hq, abs_mul]
    _ ≤ (|q - q'| * d / 2) / q +
          (q' * d / 2) * (|q - q'| / (q * q')) := by
      gcongr
      · calc
          |Real.sin (q * d / 2) - Real.sin (q' * d / 2)| ≤
              |q * d / 2 - q' * d / 2| :=
            Real.abs_sin_sub_sin_le _ _
          _ = |q - q'| * d / 2 := by
            rw [show q * d / 2 - q' * d / 2 = (q - q') * d / 2 by ring,
              abs_div, abs_mul, abs_of_nonneg hd]
            norm_num
      · calc
          |Real.sin (q' * d / 2)| ≤ |q' * d / 2| := Real.abs_sin_le_abs
          _ = q' * d / 2 := by
            rw [abs_of_nonneg]
            positivity
      · rw [show 1 / q - 1 / q' = (q' - q) / (q * q') by
          field_simp [hq.ne', hq'.ne']]
        rw [abs_div, abs_mul, abs_of_pos hq, abs_of_pos hq', abs_sub_comm]
    _ = d * |q - q'| / q := by
      field_simp [hq.ne', hq'.ne']
      ring

/-- The literal oscillatory integral in the exact symmetrized kernel after
the positive log-gap `q` and log-midpoint `c` have been exposed. -/
def localizedKernelIntegral
    (Phi : ℝ → ℝ) (T q c : ℝ) : ℝ :=
  ∫ x in Set.Icc (-T) T,
    Phi x ^ 2 * Real.cos (x * c) * sineQuotient q (T - |x|)

/-- Uniform size of the literal oscillatory integral. -/
theorem abs_localizedKernelIntegral_le
    {Phi : ℝ → ℝ} {T q c : ℝ}
    (hT : 0 ≤ T) (hq : 0 < q)
    (hPhi : Continuous Phi) (hPhi2 : Integrable fun x => Phi x ^ 2) :
    |localizedKernelIntegral Phi T q c| ≤
      T / 2 * ∫ x, Phi x ^ 2 := by
  unfold localizedKernelIntegral
  have hint : IntegrableOn
      (fun x => Phi x ^ 2 * Real.cos (x * c) *
        sineQuotient q (T - |x|)) (Set.Icc (-T) T) := by
    apply Continuous.integrableOn_Icc
    simp only [sineQuotient]
    fun_prop
  calc
    |∫ x in Set.Icc (-T) T,
        Phi x ^ 2 * Real.cos (x * c) * sineQuotient q (T - |x|)| ≤
        ∫ x in Set.Icc (-T) T,
          |Phi x ^ 2 * Real.cos (x * c) * sineQuotient q (T - |x|)| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ x in Set.Icc (-T) T, Phi x ^ 2 * (T / 2) := by
      apply setIntegral_mono_on hint.abs
        (hPhi2.integrableOn.mul_const _) measurableSet_Icc
      intro x hx
      have hdx : 0 ≤ T - |x| := by
        have habs : |x| ≤ T := (abs_le).2 ⟨by linarith [hx.1], hx.2⟩
        linarith
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg _)]
      calc
        Phi x ^ 2 * |Real.cos (x * c)| *
            |sineQuotient q (T - |x|)| ≤
            Phi x ^ 2 * 1 * ((T - |x|) / 2) := by
          gcongr
          · exact Real.abs_cos_le_one _
          · unfold sineQuotient
            rw [abs_div, abs_of_pos hq]
            calc
              |Real.sin (q * (T - |x|) / 2)| / q ≤
                  |q * (T - |x|) / 2| / q :=
                div_le_div_of_nonneg_right Real.abs_sin_le_abs hq.le
              _ = (T - |x|) / 2 := by
                rw [abs_div, abs_mul, abs_of_pos hq, abs_of_nonneg hdx]
                norm_num
                field_simp [hq.ne']
        _ ≤ Phi x ^ 2 * (T / 2) := by
          have habs : 0 ≤ |x| := abs_nonneg x
          nlinarith [sq_nonneg (Phi x)]
    _ = T / 2 * ∫ x in Set.Icc (-T) T, Phi x ^ 2 := by
      rw [integral_mul_const]
      ring
    _ ≤ T / 2 * ∫ x, Phi x ^ 2 := by
      exact mul_le_mul_of_nonneg_left
        (setIntegral_le_integral hPhi2
          (Filter.Eventually.of_forall fun x => sq_nonneg _)) (by positivity)

/-- Exact two-parameter localization estimate for the oscillatory integral.
The first term records motion of the logarithmic midpoint and the second
records motion of the logarithmic gap.  Both use actual moments of `Phi`. -/
theorem abs_localizedKernelIntegral_sub_le
    {Phi : ℝ → ℝ} {T q q' c c' : ℝ}
    (hT : 0 ≤ T) (hq : 0 < q) (hq' : 0 < q')
    (hPhi : Continuous Phi)
    (hPhi2 : Integrable fun x => Phi x ^ 2)
    (hPhiAbs : Integrable fun x => Phi x ^ 2 * |x|) :
    |localizedKernelIntegral Phi T q c -
        localizedKernelIntegral Phi T q' c'| ≤
      T / 2 * |c - c'| * (∫ x, Phi x ^ 2 * |x|) +
        T * |q - q'| / q * (∫ x, Phi x ^ 2) := by
  unfold localizedKernelIntegral
  let f : ℝ → ℝ := fun x =>
    Phi x ^ 2 * Real.cos (x * c) * sineQuotient q (T - |x|)
  let g : ℝ → ℝ := fun x =>
    Phi x ^ 2 * Real.cos (x * c') * sineQuotient q' (T - |x|)
  have hf : IntegrableOn f (Set.Icc (-T) T) := by
    apply Continuous.integrableOn_Icc
    dsimp [f, sineQuotient]
    fun_prop
  have hg : IntegrableOn g (Set.Icc (-T) T) := by
    apply Continuous.integrableOn_Icc
    dsimp [g, sineQuotient]
    fun_prop
  rw [← integral_sub hf hg]
  calc
    |∫ x in Set.Icc (-T) T, f x - g x| ≤
        ∫ x in Set.Icc (-T) T, |f x - g x| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ x in Set.Icc (-T) T,
        (T / 2 * |c - c'|) * (Phi x ^ 2 * |x|) +
          (T * |q - q'| / q) * Phi x ^ 2 := by
      apply setIntegral_mono_on (hf.sub hg).abs
        ((hPhiAbs.const_mul _).add (hPhi2.const_mul _)).integrableOn
        measurableSet_Icc
      intro x hx
      have hdx : 0 ≤ T - |x| := by
        have habs : |x| ≤ T := (abs_le).2 ⟨by linarith [hx.1], hx.2⟩
        linarith
      change |Phi x ^ 2 * Real.cos (x * c) * sineQuotient q (T - |x|) -
          Phi x ^ 2 * Real.cos (x * c') * sineQuotient q' (T - |x|)| ≤ _
      rw [show Phi x ^ 2 * Real.cos (x * c) * sineQuotient q (T - |x|) -
          Phi x ^ 2 * Real.cos (x * c') * sineQuotient q' (T - |x|) =
          Phi x ^ 2 *
            ((Real.cos (x * c) - Real.cos (x * c')) *
                sineQuotient q (T - |x|) +
              Real.cos (x * c') *
                (sineQuotient q (T - |x|) -
                  sineQuotient q' (T - |x|))) by ring]
      rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
      calc
        Phi x ^ 2 *
            |(Real.cos (x * c) - Real.cos (x * c')) *
                sineQuotient q (T - |x|) +
              Real.cos (x * c') *
                (sineQuotient q (T - |x|) -
                  sineQuotient q' (T - |x|))| ≤
            Phi x ^ 2 *
              (|x| * |c - c'| * (T / 2) +
                1 * ((T - |x|) * |q - q'| / q)) := by
          gcongr
          calc
            |(Real.cos (x * c) - Real.cos (x * c')) *
                  sineQuotient q (T - |x|) +
                Real.cos (x * c') *
                  (sineQuotient q (T - |x|) -
                    sineQuotient q' (T - |x|))| ≤
                |Real.cos (x * c) - Real.cos (x * c')| *
                    |sineQuotient q (T - |x|)| +
                  |Real.cos (x * c')| *
                    |sineQuotient q (T - |x|) -
                      sineQuotient q' (T - |x|)| := by
              calc
                |(Real.cos (x * c) - Real.cos (x * c')) *
                      sineQuotient q (T - |x|) +
                    Real.cos (x * c') *
                      (sineQuotient q (T - |x|) -
                        sineQuotient q' (T - |x|))| ≤
                    |(Real.cos (x * c) - Real.cos (x * c')) *
                      sineQuotient q (T - |x|)| +
                    |Real.cos (x * c') *
                      (sineQuotient q (T - |x|) -
                        sineQuotient q' (T - |x|))| := abs_add_le _ _
                _ = |Real.cos (x * c) - Real.cos (x * c')| *
                      |sineQuotient q (T - |x|)| +
                    |Real.cos (x * c')| *
                      |sineQuotient q (T - |x|) -
                        sineQuotient q' (T - |x|)| := by rw [abs_mul, abs_mul]
            _ ≤ |x| * |c - c'| * (T / 2) +
                  1 * ((T - |x|) * |q - q'| / q) := by
              gcongr
              · calc
                  |Real.cos (x * c) - Real.cos (x * c')| ≤
                      |x * c - x * c'| := Real.abs_cos_sub_cos_le _ _
                  _ = |x| * |c - c'| := by
                    rw [show x * c - x * c' = x * (c - c') by ring, abs_mul]
              · unfold sineQuotient
                rw [abs_div, abs_of_pos hq]
                calc
                  |Real.sin (q * (T - |x|) / 2)| / q ≤
                      |q * (T - |x|) / 2| / q :=
                    div_le_div_of_nonneg_right Real.abs_sin_le_abs hq.le
                  _ = (T - |x|) / 2 := by
                    rw [abs_div, abs_mul, abs_of_pos hq, abs_of_nonneg hdx]
                    norm_num
                    field_simp [hq.ne']
                  _ ≤ T / 2 := by linarith [abs_nonneg x]
              · exact Real.abs_cos_le_one _
              · exact abs_sineQuotient_sub_sineQuotient_le hq hq' hdx
        _ ≤ (T / 2 * |c - c'|) * (Phi x ^ 2 * |x|) +
              (T * |q - q'| / q) * Phi x ^ 2 := by
          rw [mul_add]
          apply add_le_add
          · ring_nf
            exact le_rfl
          · have hdle : T - |x| ≤ T := by linarith [abs_nonneg x]
            have hratio : 0 ≤ |q - q'| / q := div_nonneg (abs_nonneg _) hq.le
            calc
              Phi x ^ 2 * (1 * ((T - |x|) * |q - q'| / q)) ≤
                  Phi x ^ 2 * (T * |q - q'| / q) := by
                apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
                rw [show (T - |x|) * |q - q'| / q =
                    (T - |x|) * (|q - q'| / q) by ring,
                  show T * |q - q'| / q = T * (|q - q'| / q) by ring]
                simpa only [one_mul] using mul_le_mul_of_nonneg_right hdle hratio
              _ = (T * |q - q'| / q) * Phi x ^ 2 := by ring
    _ = T / 2 * |c - c'| * (∫ x in Set.Icc (-T) T, Phi x ^ 2 * |x|) +
          T * |q - q'| / q * (∫ x in Set.Icc (-T) T, Phi x ^ 2) := by
      rw [integral_add (hPhiAbs.integrableOn.const_mul _)
          (hPhi2.integrableOn.const_mul _),
        integral_const_mul, integral_const_mul]
    _ ≤ T / 2 * |c - c'| * (∫ x, Phi x ^ 2 * |x|) +
          T * |q - q'| / q * (∫ x, Phi x ^ 2) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left
          (setIntegral_le_integral hPhiAbs
            (Filter.Eventually.of_forall fun x => by positivity)) (by positivity)
      · exact mul_le_mul_of_nonneg_left
          (setIntegral_le_integral hPhi2
            (Filter.Eventually.of_forall fun x => sq_nonneg _)) (by positivity)

/-- The exact symmetrized kernel expressed only in its positive log-gap and
log-midpoint coordinates. -/
def localizedSymmetricKernel
    (Phi : ℝ → ℝ) (T q c : ℝ) : ℝ :=
  4 * Real.cos (3 * q * T / 2) * localizedKernelIntegral Phi T q c

/-- The complete literal-kernel localization ledger.  The three terms are,
respectively, the outer resonant phase, the Fourier midpoint, and the sine
quotient. -/
theorem abs_localizedSymmetricKernel_sub_le
    {Phi : ℝ → ℝ} {T q q' c c' : ℝ}
    (hT : 0 ≤ T) (hq : 0 < q) (hq' : 0 < q')
    (hPhi : Continuous Phi)
    (hPhi2 : Integrable fun x => Phi x ^ 2)
    (hPhiAbs : Integrable fun x => Phi x ^ 2 * |x|) :
    |localizedSymmetricKernel Phi T q c -
        localizedSymmetricKernel Phi T q' c'| ≤
      3 * T ^ 2 * |q - q'| * (∫ x, Phi x ^ 2) +
        2 * T * |c - c'| * (∫ x, Phi x ^ 2 * |x|) +
        4 * T * |q - q'| / q * (∫ x, Phi x ^ 2) := by
  unfold localizedSymmetricKernel
  rw [show 4 * Real.cos (3 * q * T / 2) * localizedKernelIntegral Phi T q c -
      4 * Real.cos (3 * q' * T / 2) * localizedKernelIntegral Phi T q' c' =
      4 * ((Real.cos (3 * q * T / 2) - Real.cos (3 * q' * T / 2)) *
          localizedKernelIntegral Phi T q c +
        Real.cos (3 * q' * T / 2) *
          (localizedKernelIntegral Phi T q c -
            localizedKernelIntegral Phi T q' c')) by ring]
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
  calc
    4 * |(Real.cos (3 * q * T / 2) - Real.cos (3 * q' * T / 2)) *
          localizedKernelIntegral Phi T q c +
        Real.cos (3 * q' * T / 2) *
          (localizedKernelIntegral Phi T q c -
            localizedKernelIntegral Phi T q' c')| ≤
        4 * ((3 * T / 2 * |q - q'|) *
            (T / 2 * ∫ x, Phi x ^ 2) +
          1 * (T / 2 * |c - c'| * (∫ x, Phi x ^ 2 * |x|) +
            T * |q - q'| / q * (∫ x, Phi x ^ 2))) := by
      gcongr
      calc
        |(Real.cos (3 * q * T / 2) - Real.cos (3 * q' * T / 2)) *
              localizedKernelIntegral Phi T q c +
            Real.cos (3 * q' * T / 2) *
              (localizedKernelIntegral Phi T q c -
                localizedKernelIntegral Phi T q' c')| ≤
            |Real.cos (3 * q * T / 2) - Real.cos (3 * q' * T / 2)| *
                |localizedKernelIntegral Phi T q c| +
              |Real.cos (3 * q' * T / 2)| *
                |localizedKernelIntegral Phi T q c -
                  localizedKernelIntegral Phi T q' c'| := by
          calc
            |(Real.cos (3 * q * T / 2) - Real.cos (3 * q' * T / 2)) *
                  localizedKernelIntegral Phi T q c +
                Real.cos (3 * q' * T / 2) *
                  (localizedKernelIntegral Phi T q c -
                    localizedKernelIntegral Phi T q' c')| ≤
                |(Real.cos (3 * q * T / 2) - Real.cos (3 * q' * T / 2)) *
                  localizedKernelIntegral Phi T q c| +
                |Real.cos (3 * q' * T / 2) *
                  (localizedKernelIntegral Phi T q c -
                    localizedKernelIntegral Phi T q' c')| := abs_add_le _ _
            _ = |Real.cos (3 * q * T / 2) - Real.cos (3 * q' * T / 2)| *
                  |localizedKernelIntegral Phi T q c| +
                |Real.cos (3 * q' * T / 2)| *
                  |localizedKernelIntegral Phi T q c -
                    localizedKernelIntegral Phi T q' c'| := by rw [abs_mul, abs_mul]
        _ ≤ (3 * T / 2 * |q - q'|) *
              (T / 2 * ∫ x, Phi x ^ 2) +
            1 * (T / 2 * |c - c'| * (∫ x, Phi x ^ 2 * |x|) +
              T * |q - q'| / q * (∫ x, Phi x ^ 2)) := by
          gcongr
          · calc
              |Real.cos (3 * q * T / 2) - Real.cos (3 * q' * T / 2)| ≤
                  |3 * q * T / 2 - 3 * q' * T / 2| :=
                Real.abs_cos_sub_cos_le _ _
              _ = 3 * T / 2 * |q - q'| := by
                rw [show 3 * q * T / 2 - 3 * q' * T / 2 =
                  (3 * T / 2) * (q - q') by ring,
                  abs_mul, abs_of_nonneg (by positivity : 0 ≤ 3 * T / 2)]
          · exact abs_localizedKernelIntegral_le hT hq hPhi hPhi2
          · exact Real.abs_cos_le_one _
          · exact abs_localizedKernelIntegral_sub_le hT hq hq'
              hPhi hPhi2 hPhiAbs
    _ = 3 * T ^ 2 * |q - q'| * (∫ x, Phi x ^ 2) +
          2 * T * |c - c'| * (∫ x, Phi x ^ 2 * |x|) +
          4 * T * |q - q'| / q * (∫ x, Phi x ^ 2) := by
      ring

/-- The literal dyadic shift kernel is exactly the localized symmetric
kernel at its positive logarithmic gap and logarithmic midpoint. -/
theorem dyadicShiftKernel_eq_localizedSymmetricKernel
    {Phi : ℝ → ℝ} {T : ℝ} {n h : ℕ}
    (hn : 1 ≤ n) (hh : 1 ≤ h) (hPhi : Continuous Phi) :
    dyadicShiftKernel Phi T n h =
      localizedSymmetricKernel Phi T
        (Real.log (n + h) - Real.log n)
        ((Real.log n + Real.log (n + h)) / 2) := by
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hsumpos : (0 : ℝ) < n + h := by positivity
  have hcast : (n : ℝ) < n + h := by
    exact_mod_cast Nat.lt_add_of_pos_right hh
  have hlog : Real.log n < Real.log (n + h) :=
    Real.strictMonoOn_log (Set.mem_Ioi.mpr hnpos)
      (Set.mem_Ioi.mpr hsumpos) hcast
  have hne : Real.log n - Real.log (n + h) ≠ 0 :=
    sub_ne_zero.mpr hlog.ne
  unfold dyadicShiftKernel localizedSymmetricKernel localizedKernelIntegral
  rw [Aminus_add_swap_eq hne Phi hPhi]
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
  intro x hx
  unfold sineQuotient
  rw [show Real.log n - Real.log (n + h) =
      -(Real.log (n + h) - Real.log n) by ring]
  rw [show 3 * -(Real.log (n + h) - Real.log n) * T / 2 =
      -(3 * (Real.log (n + h) - Real.log n) * T / 2) by ring,
    Real.cos_neg]
  simp only [neg_mul, neg_div, Real.sin_neg]
  field_simp [sub_ne_zero.mpr hlog.ne']

/-- Uniform resonant-size bound for the literal two-orientation kernel.  In
contrast with the nonresonant `1/|log n-log(n+h)|` estimate, this remains
finite at the resonant scale and is the correct tool for boundary and
exceptional-row ledgers. -/
theorem abs_dyadicShiftKernel_le_two_mul_T
    {Phi : ℝ → ℝ} {T : ℝ} {n h : ℕ}
    (hT : 0 ≤ T) (hn : 1 ≤ n) (hh : 1 ≤ h)
    (hPhi : Continuous Phi)
    (hPhi2 : Integrable fun x => Phi x ^ 2) :
    |dyadicShiftKernel Phi T n h| ≤
      2 * T * ∫ x, Phi x ^ 2 := by
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hsumpos : (0 : ℝ) < n + h := by positivity
  have hcast : (n : ℝ) < n + h := by
    exact_mod_cast Nat.lt_add_of_pos_right hh
  have hq : 0 < Real.log (n + h) - Real.log n := sub_pos.mpr <|
    Real.strictMonoOn_log (Set.mem_Ioi.mpr hnpos)
      (Set.mem_Ioi.mpr hsumpos) hcast
  rw [dyadicShiftKernel_eq_localizedSymmetricKernel hn hh hPhi]
  unfold localizedSymmetricKernel
  rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
  calc
    4 * |Real.cos (3 * (Real.log (n + h) - Real.log n) * T / 2)| *
        |localizedKernelIntegral Phi T
          (Real.log (n + h) - Real.log n)
          ((Real.log n + Real.log (n + h)) / 2)| ≤
      4 * 1 * (T / 2 * ∫ x, Phi x ^ 2) := by
        gcongr
        · exact Real.abs_cos_le_one _
        · exact abs_localizedKernelIntegral_le hT hq hPhi hPhi2
    _ = 2 * T * ∫ x, Phi x ^ 2 := by ring

/-- Direct localization estimate for two literal source-kernel rows.  It
retains the exact logarithmic coordinates; the next arithmetic-geometric
layer is responsible for bounding their motion inside a short `n`-box. -/
theorem abs_dyadicShiftKernel_sub_le_logCoordinates
    {Phi : ℝ → ℝ} {T : ℝ} {n m h : ℕ}
    (hT : 0 ≤ T) (hn : 1 ≤ n) (hm : 1 ≤ m) (hh : 1 ≤ h)
    (hPhi : Continuous Phi)
    (hPhi2 : Integrable fun x => Phi x ^ 2)
    (hPhiAbs : Integrable fun x => Phi x ^ 2 * |x|) :
    |dyadicShiftKernel Phi T n h - dyadicShiftKernel Phi T m h| ≤
      3 * T ^ 2 *
          |(Real.log (n + h) - Real.log n) -
            (Real.log (m + h) - Real.log m)| *
          (∫ x, Phi x ^ 2) +
        2 * T *
          |(Real.log n + Real.log (n + h)) / 2 -
            (Real.log m + Real.log (m + h)) / 2| *
          (∫ x, Phi x ^ 2 * |x|) +
        4 * T *
          |(Real.log (n + h) - Real.log n) -
            (Real.log (m + h) - Real.log m)| /
          (Real.log (n + h) - Real.log n) *
          (∫ x, Phi x ^ 2) := by
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hmpos : (0 : ℝ) < m := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hnhpos : (0 : ℝ) < n + h := by positivity
  have hmhpos : (0 : ℝ) < m + h := by positivity
  have hnlt : (n : ℝ) < n + h := by
    exact_mod_cast Nat.lt_add_of_pos_right hh
  have hmlt : (m : ℝ) < m + h := by
    exact_mod_cast Nat.lt_add_of_pos_right hh
  have hqn : 0 < Real.log (n + h) - Real.log n := sub_pos.mpr <|
    Real.strictMonoOn_log (Set.mem_Ioi.mpr hnpos)
      (Set.mem_Ioi.mpr hnhpos) hnlt
  have hqm : 0 < Real.log (m + h) - Real.log m := sub_pos.mpr <|
    Real.strictMonoOn_log (Set.mem_Ioi.mpr hmpos)
      (Set.mem_Ioi.mpr hmhpos) hmlt
  rw [dyadicShiftKernel_eq_localizedSymmetricKernel hn hh hPhi,
    dyadicShiftKernel_eq_localizedSymmetricKernel hm hh hPhi]
  exact abs_localizedSymmetricKernel_sub_le hT hqn hqm
    hPhi hPhi2 hPhiAbs

/-! ### Motion of the logarithmic coordinates inside a short box -/

private theorem log_sub_log_le_of_le_local
    {t u : ℝ} (hu : 0 < u) (hut : u ≤ t) :
    Real.log t - Real.log u ≤ (t - u) / u := by
  have ht : 0 < t := lt_of_lt_of_le hu hut
  rw [← Real.log_div ht.ne' hu.ne']
  have hlog := Real.log_le_sub_one_of_pos (show 0 < t / u by positivity)
  have heq : t / u - 1 = (t - u) / u := by field_simp
  linarith

/-- Elementary logarithmic Lipschitz estimate, included locally so the
Prime Shell extension does not import an unrelated pinned Xi-prime module. -/
theorem abs_log_sub_log_le_min
    {t u : ℝ} (ht : 0 < t) (hu : 0 < u) :
    |Real.log t - Real.log u| ≤ |t - u| / min t u := by
  rcases le_total u t with hut | htu
  · have hlog : Real.log u ≤ Real.log t := Real.log_le_log hu hut
    rw [min_eq_right hut, abs_of_nonneg (by linarith),
      abs_of_nonneg (by linarith)]
    exact log_sub_log_le_of_le_local hu hut
  · have hlog : Real.log t ≤ Real.log u := Real.log_le_log ht htu
    rw [min_eq_left htu, abs_of_nonpos (by linarith),
      abs_of_nonpos (by linarith), neg_sub, neg_sub]
    exact log_sub_log_le_of_le_local ht htu

/-- Cancellation in `log (n+h) - log n` gives the decisive factor `h/N`:
the gap coordinate moves by at most `h |n-m| / N²` on a box above `N`.
This is the exact analytic reason polylogarithmically short `n`-boxes can
freeze the resonant phase. -/
theorem abs_logGap_sub_logGap_le
    {N n m h : ℝ} (hN : 0 < N) (hn : N ≤ n) (hm : N ≤ m)
    (hh : 0 ≤ h) :
    |(Real.log (n + h) - Real.log n) -
        (Real.log (m + h) - Real.log m)| ≤
      h * |n - m| / N ^ 2 := by
  have hn0 : 0 < n := hN.trans_le hn
  have hm0 : 0 < m := hN.trans_le hm
  have hnh0 : 0 < n + h := by linarith
  have hmh0 : 0 < m + h := by linarith
  let u : ℝ := (n + h) / n
  let v : ℝ := (m + h) / m
  have hu1 : 1 ≤ u := by
    dsimp [u]
    rw [le_div_iff₀ hn0]
    linarith
  have hv1 : 1 ≤ v := by
    dsimp [v]
    rw [le_div_iff₀ hm0]
    linarith
  have hu0 : 0 < u := zero_lt_one.trans_le hu1
  have hv0 : 0 < v := zero_lt_one.trans_le hv1
  have hqn : Real.log (n + h) - Real.log n = Real.log u := by
    dsimp [u]
    rw [Real.log_div hnh0.ne' hn0.ne']
  have hqm : Real.log (m + h) - Real.log m = Real.log v := by
    dsimp [v]
    rw [Real.log_div hmh0.ne' hm0.ne']
  rw [hqn, hqm]
  have hlog := abs_log_sub_log_le_min hu0 hv0
  have hmin : 1 ≤ min u v := le_min hu1 hv1
  have hmin0 : 0 < min u v := zero_lt_one.trans_le hmin
  have hdrop : |u - v| / min u v ≤ |u - v| := by
    rw [div_le_iff₀ hmin0]
    nlinarith [abs_nonneg (u - v)]
  calc
    |Real.log u - Real.log v| ≤ |u - v| := hlog.trans hdrop
    _ = h * |n - m| / (n * m) := by
      have huv : u - v = h * (m - n) / (n * m) := by
        dsimp [u, v]
        field_simp [hn0.ne', hm0.ne']
        ring
      rw [huv, abs_div, abs_mul, abs_of_nonneg hh,
        abs_mul, abs_of_pos hn0, abs_of_pos hm0, abs_sub_comm]
    _ ≤ h * |n - m| / N ^ 2 := by
      have hnum : 0 ≤ h * |n - m| := mul_nonneg hh (abs_nonneg _)
      have hden : N ^ 2 ≤ n * m := by nlinarith
      have hN2 : 0 < N ^ 2 := sq_pos_of_pos hN
      have hnm0 : 0 < n * m := mul_pos hn0 hm0
      exact div_le_div_of_nonneg_left hnum hN2 hden

/-- The logarithmic midpoint has ordinary `1/N` Lipschitz motion. -/
theorem abs_logMidpoint_sub_logMidpoint_le
    {N n m h : ℝ} (hN : 0 < N) (hn : N ≤ n) (hm : N ≤ m)
    (hh : 0 ≤ h) :
    |(Real.log n + Real.log (n + h)) / 2 -
        (Real.log m + Real.log (m + h)) / 2| ≤
      |n - m| / N := by
  have hn0 : 0 < n := hN.trans_le hn
  have hm0 : 0 < m := hN.trans_le hm
  have hnh0 : 0 < n + h := by linarith
  have hmh0 : 0 < m + h := by linarith
  have hlog1 := abs_log_sub_log_le_min hn0 hm0
  have hlog2 := abs_log_sub_log_le_min hnh0 hmh0
  have hmin1 : N ≤ min n m := le_min hn hm
  have hmin2 : N ≤ min (n + h) (m + h) :=
    le_min (by linarith) (by linarith)
  have hb1 : |Real.log n - Real.log m| ≤ |n - m| / N := by
    refine hlog1.trans ?_
    exact div_le_div_of_nonneg_left (abs_nonneg _) hN hmin1
  have hb2 : |Real.log (n + h) - Real.log (m + h)| ≤ |n - m| / N := by
    refine hlog2.trans ?_
    rw [show (n + h) - (m + h) = n - m by ring]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hN hmin2
  rw [show (Real.log n + Real.log (n + h)) / 2 -
      (Real.log m + Real.log (m + h)) / 2 =
      ((Real.log n - Real.log m) +
        (Real.log (n + h) - Real.log (m + h))) / 2 by ring,
    abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    |(Real.log n - Real.log m) +
        (Real.log (n + h) - Real.log (m + h))| / 2 ≤
        (|Real.log n - Real.log m| +
          |Real.log (n + h) - Real.log (m + h)|) / 2 :=
      div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num)
    _ ≤ |n - m| / N := by linarith

/-- Lower bound for the positive logarithmic gap.  It is the elementary
inequality `log (1+x) ≥ x/(1+x)` in the source variables. -/
theorem div_add_le_logGap
    {n h : ℝ} (hn : 0 < n) (hh : 0 ≤ h) :
    h / (n + h) ≤ Real.log (n + h) - Real.log n := by
  have hnh : 0 < n + h := by linarith
  have hratio : 0 < n / (n + h) := by positivity
  have hlog := Real.log_le_sub_one_of_pos hratio
  rw [Real.log_div hn.ne' hnh.ne'] at hlog
  have heq : n / (n + h) - 1 = -(h / (n + h)) := by
    field_simp [hnh.ne']
    ring
  rw [heq] at hlog
  linarith

/-- In a dyadic box, division by the positive log gap preserves the same
`|n-m|/N` localization scale.  The constant `3` comes only from
`n+h ≤ 3N`; no asymptotic notation is hidden here. -/
theorem abs_logGap_sub_logGap_div_logGap_le
    {N n m h : ℝ} (hN : 0 < N) (hn : N ≤ n) (hn2 : n ≤ 2 * N)
    (hm : N ≤ m) (hh : 0 < h) (hhN : h ≤ N) :
    |(Real.log (n + h) - Real.log n) -
        (Real.log (m + h) - Real.log m)| /
        (Real.log (n + h) - Real.log n) ≤
      3 * |n - m| / N := by
  have hn0 : 0 < n := hN.trans_le hn
  have hnh0 : 0 < n + h := by linarith
  have hqn : 0 < Real.log (n + h) - Real.log n := sub_pos.mpr <|
    Real.strictMonoOn_log (Set.mem_Ioi.mpr hn0)
      (Set.mem_Ioi.mpr hnh0) (by linarith)
  have hmove := abs_logGap_sub_logGap_le hN hn hm hh.le
  have hlower0 := div_add_le_logGap hn0 hh.le
  have hnh3 : n + h ≤ 3 * N := by linarith
  have hlower : h / (3 * N) ≤ Real.log (n + h) - Real.log n := by
    exact (div_le_div_of_nonneg_left hh.le (by positivity) hnh3).trans hlower0
  rw [div_le_iff₀ hqn]
  calc
    |(Real.log (n + h) - Real.log n) -
        (Real.log (m + h) - Real.log m)| ≤
        h * |n - m| / N ^ 2 := hmove
    _ = (3 * |n - m| / N) * (h / (3 * N)) := by
      field_simp [hN.ne']
    _ ≤ (3 * |n - m| / N) *
        (Real.log (n + h) - Real.log n) := by
      exact mul_le_mul_of_nonneg_left hlower (by positivity)

/-- Fully explicit localization of two literal Zeta23 kernel rows inside one
dyadic `n`-block.  This is the analytic bridge needed before any arithmetic
correlation theorem may be used on short multiplicative boxes. -/
theorem abs_dyadicShiftKernel_sub_le_dyadicBox
    {Phi : ℝ → ℝ} {T : ℝ} {N n m h : ℕ}
    (hT : 0 ≤ T) (hN : 1 ≤ N)
    (hn : n ∈ Finset.Ioc N (2 * N))
    (hm : m ∈ Finset.Ioc N (2 * N))
    (hh : 1 ≤ h) (hhN : h ≤ N)
    (hPhi : Continuous Phi)
    (hPhi2 : Integrable fun x => Phi x ^ 2)
    (hPhiAbs : Integrable fun x => Phi x ^ 2 * |x|) :
    |dyadicShiftKernel Phi T n h - dyadicShiftKernel Phi T m h| ≤
      3 * T ^ 2 *
          ((h : ℝ) * |(n : ℝ) - m| / (N : ℝ) ^ 2) *
          (∫ x, Phi x ^ 2) +
        2 * T * (|(n : ℝ) - m| / (N : ℝ)) *
          (∫ x, Phi x ^ 2 * |x|) +
        12 * T * (|(n : ℝ) - m| / (N : ℝ)) *
          (∫ x, Phi x ^ 2) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hn' := Finset.mem_Ioc.mp hn
  have hm' := Finset.mem_Ioc.mp hm
  have hn1 : 1 ≤ n := by omega
  have hm1 : 1 ≤ m := by omega
  have hnN : (N : ℝ) ≤ n := by exact_mod_cast (Nat.le_of_lt hn'.1)
  have hmN : (N : ℝ) ≤ m := by exact_mod_cast (Nat.le_of_lt hm'.1)
  have hn2 : (n : ℝ) ≤ 2 * N := by exact_mod_cast hn'.2
  have hh0 : (0 : ℝ) < h := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hh)
  have hhNr : (h : ℝ) ≤ N := by exact_mod_cast hhN
  have hgap := abs_logGap_sub_logGap_le hN0 hnN hmN hh0.le
  have hmid := abs_logMidpoint_sub_logMidpoint_le hN0 hnN hmN hh0.le
  have hquot := abs_logGap_sub_logGap_div_logGap_le
    hN0 hnN hn2 hmN hh0 hhNr
  have hI0 : 0 ≤ ∫ x, Phi x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hI1 : 0 ≤ ∫ x, Phi x ^ 2 * |x| :=
    integral_nonneg fun x => mul_nonneg (sq_nonneg _) (abs_nonneg _)
  refine (abs_dyadicShiftKernel_sub_le_logCoordinates hT hn1 hm1 hh
    hPhi hPhi2 hPhiAbs).trans ?_
  apply add_le_add
  · exact add_le_add
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hgap (by positivity)) hI0)
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hmid (by positivity)) hI1)
  · have hscaled := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hquot
        (show 0 ≤ 4 * T by positivity)) hI0
    convert hscaled using 1 <;> ring

/-- Motion of the logarithmic gap when the starting point is fixed and the
positive shift varies. -/
theorem abs_logGap_sub_logGap_shift_le
    {N n h j : ℝ} (hN : 0 < N) (hn : N ≤ n)
    (hh : 0 ≤ h) (hj : 0 ≤ j) :
    |(Real.log (n + h) - Real.log n) -
        (Real.log (n + j) - Real.log n)| ≤ |h - j| / N := by
  rw [show (Real.log (n + h) - Real.log n) -
      (Real.log (n + j) - Real.log n) =
      Real.log (n + h) - Real.log (n + j) by ring]
  have hnh : N ≤ n + h := by linarith
  have hnj : N ≤ n + j := by linarith
  have hbase := abs_log_sub_log_le_min
    (hN.trans_le hnh) (hN.trans_le hnj)
  calc
    |Real.log (n + h) - Real.log (n + j)| ≤
        |(n + h) - (n + j)| / min (n + h) (n + j) := hbase
    _ ≤ |(n + h) - (n + j)| / N :=
      div_le_div_of_nonneg_left (abs_nonneg _) hN (le_min hnh hnj)
    _ = |h - j| / N := by
      rw [show (n + h) - (n + j) = h - j by ring]

/-- Motion of the logarithmic midpoint when the starting point is fixed. -/
theorem abs_logMidpoint_sub_logMidpoint_shift_le
    {N n h j : ℝ} (hN : 0 < N) (hn : N ≤ n)
    (hh : 0 ≤ h) (hj : 0 ≤ j) :
    |(Real.log n + Real.log (n + h)) / 2 -
        (Real.log n + Real.log (n + j)) / 2| ≤ |h - j| / (2 * N) := by
  rw [show (Real.log n + Real.log (n + h)) / 2 -
      (Real.log n + Real.log (n + j)) / 2 =
      (Real.log (n + h) - Real.log (n + j)) / 2 by ring,
    abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlog := abs_logGap_sub_logGap_shift_le hN hn hh hj
  rw [show (Real.log (n + h) - Real.log n) -
      (Real.log (n + j) - Real.log n) =
      Real.log (n + h) - Real.log (n + j) by ring] at hlog
  calc
    |Real.log (n + h) - Real.log (n + j)| / 2 ≤
        (|h - j| / N) / 2 :=
      div_le_div_of_nonneg_right hlog (by norm_num)
    _ = |h - j| / (2 * N) := by ring

/-- Relative logarithmic-gap motion in a dyadic box.  The denominator is
the first shift `h`, which is the exact orientation needed by the asymmetric
sine-quotient estimate. -/
theorem abs_logGap_sub_logGap_shift_div_logGap_le
    {N n h j : ℝ} (hN : 0 < N) (hnN : N ≤ n) (hn2 : n ≤ 2 * N)
    (hh : 0 < h) (hhN : h ≤ N) (hj : 0 ≤ j) :
    |(Real.log (n + h) - Real.log n) -
        (Real.log (n + j) - Real.log n)| /
        (Real.log (n + h) - Real.log n) ≤
      3 * |h - j| / h := by
  have hn0 : 0 < n := hN.trans_le hnN
  have hnh0 : 0 < n + h := by positivity
  have hq : 0 < Real.log (n + h) - Real.log n := sub_pos.mpr <|
    Real.strictMonoOn_log (Set.mem_Ioi.mpr hn0)
      (Set.mem_Ioi.mpr hnh0) (by linarith)
  have hmove := abs_logGap_sub_logGap_shift_le hN hnN hh.le hj
  have hlower0 := div_add_le_logGap hn0 hh.le
  have hnh3 : n + h ≤ 3 * N := by linarith
  have hlower : h / (3 * N) ≤ Real.log (n + h) - Real.log n := by
    exact (div_le_div_of_nonneg_left hh.le (by positivity) hnh3).trans hlower0
  rw [div_le_iff₀ hq]
  calc
    |(Real.log (n + h) - Real.log n) -
        (Real.log (n + j) - Real.log n)| ≤ |h - j| / N := hmove
    _ = (3 * |h - j| / h) * (h / (3 * N)) := by
      field_simp [hN.ne', hh.ne']
    _ ≤ (3 * |h - j| / h) *
        (Real.log (n + h) - Real.log n) := by
      exact mul_le_mul_of_nonneg_left hlower (by positivity)

/-- Fully explicit variation of the literal kernel in the shift coordinate
inside one dyadic `n`-block.  This is the analytic input for a geometric
shift-block consumer of almost-all short-interval estimates. -/
theorem abs_dyadicShiftKernel_sub_le_shiftBox
    {Phi : ℝ → ℝ} {T : ℝ} {N n h j : ℕ}
    (hT : 0 ≤ T) (hN : 1 ≤ N)
    (hn : n ∈ Finset.Ioc N (2 * N))
    (hh : 1 ≤ h) (hhN : h ≤ N)
    (hj : 1 ≤ j)
    (hPhi : Continuous Phi)
    (hPhi2 : Integrable fun x => Phi x ^ 2)
    (hPhiAbs : Integrable fun x => Phi x ^ 2 * |x|) :
    |dyadicShiftKernel Phi T n h - dyadicShiftKernel Phi T n j| ≤
      3 * T ^ 2 * (|(h : ℝ) - j| / (N : ℝ)) *
          (∫ x, Phi x ^ 2) +
        T * (|(h : ℝ) - j| / (N : ℝ)) *
          (∫ x, Phi x ^ 2 * |x|) +
        12 * T * (|(h : ℝ) - j| / (h : ℝ)) *
          (∫ x, Phi x ^ 2) := by
  have hn' := Finset.mem_Ioc.mp hn
  have hN0 : (0 : ℝ) < N := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hnN : (N : ℝ) ≤ n := by exact_mod_cast (Nat.le_of_lt hn'.1)
  have hn2 : (n : ℝ) ≤ 2 * N := by exact_mod_cast hn'.2
  have hh0 : (0 : ℝ) < h := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hh)
  have hj0 : (0 : ℝ) < j := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hj)
  have hhNr : (h : ℝ) ≤ N := by exact_mod_cast hhN
  have hgap := abs_logGap_sub_logGap_shift_le hN0 hnN hh0.le hj0.le
  have hmid := abs_logMidpoint_sub_logMidpoint_shift_le hN0 hnN hh0.le hj0.le
  have hquot := abs_logGap_sub_logGap_shift_div_logGap_le
    hN0 hnN hn2 hh0 hhNr hj0.le
  have hI0 : 0 ≤ ∫ x, Phi x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hI1 : 0 ≤ ∫ x, Phi x ^ 2 * |x| :=
    integral_nonneg fun x => mul_nonneg (sq_nonneg _) (abs_nonneg _)
  have hn1 : 1 ≤ n := by omega
  have hnh0 : (0 : ℝ) < n + h := by positivity
  have hnj0 : (0 : ℝ) < n + j := by positivity
  have hn0 : (0 : ℝ) < n := by positivity
  have hqh : 0 < Real.log (n + h) - Real.log n := sub_pos.mpr <|
    Real.strictMonoOn_log (Set.mem_Ioi.mpr hn0)
      (Set.mem_Ioi.mpr hnh0) (by exact_mod_cast Nat.lt_add_of_pos_right hh)
  have hqj : 0 < Real.log (n + j) - Real.log n := sub_pos.mpr <|
    Real.strictMonoOn_log (Set.mem_Ioi.mpr hn0)
      (Set.mem_Ioi.mpr hnj0) (by exact_mod_cast Nat.lt_add_of_pos_right hj)
  rw [dyadicShiftKernel_eq_localizedSymmetricKernel hn1 hh hPhi,
    dyadicShiftKernel_eq_localizedSymmetricKernel hn1 hj hPhi]
  refine (abs_localizedSymmetricKernel_sub_le hT hqh hqj
    hPhi hPhi2 hPhiAbs).trans ?_
  apply add_le_add
  · apply add_le_add
    · exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hgap (by positivity)) hI0
    · have hscaled := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hmid (show 0 ≤ 2 * T by positivity)) hI1
      convert hscaled using 1
      all_goals ring_nf
  · have hscaled := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hquot (show 0 ≤ 4 * T by positivity)) hI0
    convert hscaled using 1
    all_goals ring_nf

end

end PrimeShell

import RiemannZeta.GuthMaynard.ZetaBounds

open Complex Set MeasureTheory

namespace RiemannZeta.GuthMaynard

/-- The fractional-part tail in the first-order Euler--Maclaurin formula for zeta,
with a variable positive lower limit. -/
noncomputable def abelZetaTail (b : ℝ) (s : ℂ) : ℂ :=
  ∫ t in Ioi b, ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))

theorem integrableOn_abelZetaTail_integrand {b : ℝ} (hb : 1 ≤ b) {s : ℂ}
    (hs : 0 < s.re) :
    IntegrableOn
      (fun t : ℝ => ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)))
      (Ioi b) :=
  (integrableOn_abelZetaRemainder_integrand hs).mono_set (Ioi_subset_Ioi hb)

theorem abelZetaRemainder_eq_finite_add_tail {b : ℝ} (hb : 1 ≤ b) {s : ℂ}
    (hs : 0 < s.re) :
    abelZetaRemainder s =
      (∫ t in Ioc (1 : ℝ) b,
        ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) + abelZetaTail b s := by
  have hAll := integrableOn_abelZetaRemainder_integrand hs
  have hLeft : IntegrableOn
      (fun t : ℝ => ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)))
      (Ioc (1 : ℝ) b) :=
    hAll.mono_set Ioc_subset_Ioi_self
  have hRight := integrableOn_abelZetaTail_integrand hb hs
  rw [abelZetaRemainder_eq_integral hs, ← Ioc_union_Ioi_eq_Ioi hb,
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hLeft hRight,
    abelZetaTail]

theorem sum_cpow_neg_eq_boundary_add_floor_integral {b : ℕ} (hb : 1 ≤ b) {s : ℂ}
    (hs : 0 < s.re) :
    ∑ n ∈ Finset.Icc 1 b, (n : ℂ) ^ (-s) =
      (b : ℂ) ^ (1 - s) + s * ∫ t in Ioc (1 : ℝ) b,
        (⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  let c : ℕ → ℂ := fun n => if n = 0 then 0 else 1
  have hs0 : s ≠ 0 := ne_zero_of_re_pos hs
  have hDiff : ∀ t ∈ Set.Icc ((1 : ℕ) : ℝ) (b : ℝ),
      DifferentiableAt ℝ (fun x : ℝ => (x : ℂ) ^ (-s)) t := by
    intro t ht
    have ht1 : (1 : ℝ) ≤ t := by simpa using ht.1
    exact differentiableAt_id.ofReal_cpow_const (zero_lt_one.trans_le ht1).ne'
      (neg_ne_zero.mpr hs0)
  have hInt : IntegrableOn (deriv (fun x : ℝ => (x : ℂ) ^ (-s)))
      (Set.Icc ((1 : ℕ) : ℝ) (b : ℝ)) := by
    exact (Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi
      (integrableOn_Ioi_deriv_ofReal_cpow (s := -s) zero_lt_one (by simp [hs]))).mono_set
        (by
          intro t ht
          change (1 : ℝ) ≤ t
          simpa using ht.1)
  have hAbel := sum_mul_eq_sub_sub_integral_mul' (f := fun x : ℝ => (x : ℂ) ^ (-s))
    c hb hDiff hInt
  have hSumC (m : ℕ) : ∑ n ∈ Finset.Icc 0 m, c n = (m : ℂ) := by
    rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le m), Finset.sum_cons]
    simp only [c, if_pos, zero_add]
    calc
      (∑ n ∈ Finset.Ioc 0 m, if n = 0 then (0 : ℂ) else 1) =
          ∑ _n ∈ Finset.Ioc 0 m, (1 : ℂ) := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [if_neg (ne_of_gt (Finset.mem_Ioc.mp hn).1)]
      _ = (m : ℂ) := by simp
  have hLhs :
      (∑ n ∈ Finset.Ioc 1 b, (n : ℂ) ^ (-s) * c n) =
        ∑ n ∈ Finset.Ioc 1 b, (n : ℂ) ^ (-s) := by
    apply Finset.sum_congr rfl
    intro n hn
    simp only [c]
    rw [if_neg (ne_of_gt (zero_lt_one.trans (Finset.mem_Ioc.mp hn).1)), mul_one]
  have hDerivIntegral :
      (∫ t in Ioc (1 : ℝ) b,
        deriv (fun x : ℝ => (x : ℂ) ^ (-s)) t * (⌊t⌋₊ : ℂ)) =
        -s * ∫ t in Ioc (1 : ℝ) b,
          (⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
    calc
      (∫ t in Ioc (1 : ℝ) b,
          deriv (fun x : ℝ => (x : ℂ) ^ (-s)) t * (⌊t⌋₊ : ℂ)) =
          ∫ t in Ioc (1 : ℝ) b,
            (-s) * ((⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1))) := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro t ht
        change deriv (fun x : ℝ => (x : ℂ) ^ (-s)) t * (⌊t⌋₊ : ℂ) =
          (-s) * ((⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1)))
        rw [Complex.deriv_ofReal_cpow_const (by linarith [ht.1]) (neg_ne_zero.mpr hs0)]
        rw [show -s - 1 = -(s + 1) by ring]
        ring
      _ = -s * ∫ t in Ioc (1 : ℝ) b,
          (⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
        exact integral_const_mul (μ := volume.restrict (Ioc (1 : ℝ) b)) (-s) _
  simp only [Complex.ofReal_natCast] at hAbel
  rw [hLhs] at hAbel
  simp only [hSumC] at hAbel
  have hAbel' :
      (∑ n ∈ Finset.Ioc 1 b, (n : ℂ) ^ (-s)) =
        (b : ℂ) ^ (-s) * b - 1 -
          ∫ t in Ioc (1 : ℝ) b,
            deriv (fun x : ℝ => (x : ℂ) ^ (-s)) t * (⌊t⌋₊ : ℂ) := by
    simpa using hAbel
  rw [Finset.Icc_eq_cons_Ioc hb, Finset.sum_cons]
  simp only [Nat.cast_one, one_cpow]
  rw [hAbel', hDerivIntegral]
  have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt (zero_lt_one.trans_le hb))
  rw [show (b : ℂ) ^ (1 - s) = (b : ℂ) * (b : ℂ) ^ (-s) by
    rw [sub_eq_add_neg, cpow_add _ _ hb0, cpow_one]]
  ring

theorem integral_Ioc_cpow_neg {b : ℝ} (hb : 1 ≤ b) {s : ℂ} (hs1 : s ≠ 1) :
    (∫ t in Ioc (1 : ℝ) b, (t : ℂ) ^ (-s)) =
      ((b : ℂ) ^ (1 - s) - 1) / (1 - s) := by
  have hnotmem : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) b := by
    apply Set.notMem_uIcc_of_lt <;> positivity
  rw [← intervalIntegral.integral_of_le hb]
  rw [integral_cpow (Or.inr ⟨by grind, hnotmem⟩)]
  simp only [ofReal_one, one_cpow]
  congr 2 <;> ring_nf

theorem floor_cpow_integral_eq_sub_fract {b : ℕ} (hb : 1 ≤ b) {s : ℂ}
    (hs : 0 < s.re) :
    (∫ t in Ioc (1 : ℝ) b, (⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1))) =
      (∫ t in Ioc (1 : ℝ) b, (t : ℂ) ^ (-s)) -
        ∫ t in Ioc (1 : ℝ) b,
          ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  have hnotmem : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) (b : ℝ) := by
    apply Set.notMem_uIcc_of_lt <;> positivity
  have hPower : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s)) (Ioc (1 : ℝ) b) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by exact_mod_cast hb)).mp
      (intervalIntegral.intervalIntegrable_cpow (Or.inr hnotmem))
  have hFract : IntegrableOn
      (fun t : ℝ => ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)))
      (Ioc (1 : ℝ) b) :=
    (integrableOn_abelZetaRemainder_integrand hs).mono_set Ioc_subset_Ioi_self
  calc
    (∫ t in Ioc (1 : ℝ) b, (⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1))) =
        ∫ t in Ioc (1 : ℝ) b,
          ((t : ℂ) ^ (-s) -
            ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro t ht
      change (⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1)) =
        (t : ℂ) ^ (-s) - ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))
      rw [natFloor_cast_complex t ht.1, sub_mul]
      congr 1
      have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt (zero_lt_one.trans ht.1))
      calc
        (t : ℂ) * (t : ℂ) ^ (-(s + 1)) =
            (t : ℂ) ^ (1 : ℂ) * (t : ℂ) ^ (-(s + 1)) := by rw [cpow_one]
        _ = (t : ℂ) ^ ((1 : ℂ) + (-(s + 1))) := (cpow_add _ _ ht0).symm
        _ = (t : ℂ) ^ (-s) := by
          congr 1
          ring
    _ = (∫ t in Ioc (1 : ℝ) b, (t : ℂ) ^ (-s)) -
        ∫ t in Ioc (1 : ℝ) b,
          ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
      rw [integral_sub hPower hFract]

/-- Uniform first-order Euler--Maclaurin truncation of the analytically continued
Riemann zeta function on `Re(s) > 0`, away from its pole. -/
theorem riemannZeta_truncation {b : ℕ} (hb : 1 ≤ b) {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) :
    ∑ n ∈ Finset.Icc 1 b, (n : ℂ) ^ (-s) =
      riemannZeta s + (b : ℂ) ^ (1 - s) / (1 - s) + s * abelZetaTail b s := by
  rw [sum_cpow_neg_eq_boundary_add_floor_integral hb hs,
    floor_cpow_integral_eq_sub_fract hb hs,
    integral_Ioc_cpow_neg (by exact_mod_cast hb) hs1,
    riemannZeta_eq_abel hs hs1,
    abelZetaRemainder_eq_finite_add_tail
      (show (1 : ℝ) ≤ (b : ℝ) by exact_mod_cast hb) hs,
    abelZetaTail]
  simp only [Complex.ofReal_natCast]
  have hden : (1 - s) ≠ 0 := sub_ne_zero.mpr hs1.symm
  have hden' : (s - 1) ≠ 0 := sub_ne_zero.mpr hs1
  field_simp [hden, hden']
  ring_nf

/-- Euler--Maclaurin specialized at a zeta zero away from the real axis. -/
theorem zeta_zero_truncation {b : ℕ} (hb : 1 ≤ b) {ρ : ℂ}
    (hρre : 0 < ρ.re) (hρim : ρ.im ≠ 0) (hρzero : riemannZeta ρ = 0) :
    ∑ n ∈ Finset.Icc 1 b, (n : ℂ) ^ (-ρ) =
      (b : ℂ) ^ (1 - ρ) / (1 - ρ) + ρ * abelZetaTail b ρ := by
  have hρ1 : ρ ≠ 1 := ne_of_apply_ne im (by simpa using hρim)
  rw [riemannZeta_truncation hb hρre hρ1, hρzero, zero_add]

/-- Uniform Euler--Maclaurin tail bound.  The factor `1/2` available after centering
the fractional part is deliberately not used here; this form matches the project's
existing Abel continuation and is sufficient for epsilon-power estimates. -/
theorem norm_abelZetaTail_le {b : ℝ} (hb : 1 ≤ b) {s : ℂ} (hs : 0 < s.re) :
    ‖abelZetaTail b s‖ ≤ b ^ (-s.re) / s.re := by
  have hbPos : 0 < b := zero_lt_one.trans_le hb
  have hInt := integrableOn_abelZetaTail_integrand hb hs
  have hPower : IntegrableOn (fun t : ℝ => t ^ (-s.re - 1)) (Ioi b) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hbPos
  rw [abelZetaTail]
  calc
    ‖∫ t in Ioi b, ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))‖ ≤
        ∫ t in Ioi b, ‖((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi b, t ^ (-s.re - 1) := by
      apply setIntegral_mono_on hInt.norm hPower measurableSet_Ioi
      intro t ht
      rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg t),
        norm_cpow_eq_rpow_re_of_pos (hbPos.trans ht)]
      change Int.fract t * t ^ (-(s.re + 1)) ≤ t ^ (-s.re - 1)
      rw [show -(s.re + 1) = -s.re - 1 by ring]
      have hpow : 0 ≤ t ^ (-s.re - 1) := Real.rpow_nonneg (hbPos.trans ht).le _
      exact mul_le_of_le_one_left hpow (Int.fract_lt_one t).le
    _ = b ^ (-s.re) / s.re := by
      rw [integral_Ioi_rpow_of_lt (by linarith) hbPos]
      rw [show -s.re - 1 + 1 = -s.re by ring, neg_div_neg_eq]

/-- Quantitative zero-specialized truncation error, uniform in the truncation point. -/
theorem norm_zeta_zero_truncation_error_le {b : ℕ} (hb : 1 ≤ b) {ρ : ℂ}
    (hρre : 0 < ρ.re) (hρim : ρ.im ≠ 0) (hρzero : riemannZeta ρ = 0) :
    ‖(∑ n ∈ Finset.Icc 1 b, (n : ℂ) ^ (-ρ)) -
        (b : ℂ) ^ (1 - ρ) / (1 - ρ)‖ ≤
      ‖ρ‖ * (b : ℝ) ^ (-ρ.re) / ρ.re := by
  rw [zeta_zero_truncation hb hρre hρim hρzero]
  ring_nf
  rw [norm_mul]
  calc
    ‖ρ‖ * ‖abelZetaTail (b : ℝ) ρ‖ ≤ ‖ρ‖ * ((b : ℝ) ^ (-ρ.re) / ρ.re) :=
      mul_le_mul_of_nonneg_left
        (norm_abelZetaTail_le (show (1 : ℝ) ≤ (b : ℝ) by exact_mod_cast hb) hρre)
        (norm_nonneg ρ)
    _ = ‖ρ‖ * (b : ℝ) ^ (-ρ.re) / ρ.re := by ring

end RiemannZeta.GuthMaynard

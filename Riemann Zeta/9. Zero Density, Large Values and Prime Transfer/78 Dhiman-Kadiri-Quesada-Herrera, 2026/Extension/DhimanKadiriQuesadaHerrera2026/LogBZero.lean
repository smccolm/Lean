import DhimanKadiriQuesadaHerrera2026.LogBOne
import GuthMaynard.VanDerCorput

namespace DhimanKadiriQuesadaHerrera2026

/-- Two-sided bounds for a unit logarithmic increment. -/
theorem log_unit_increment {x : ℝ} (hx : 0 < x) :
    1 / (x + 1) ≤ Real.log (x + 1) - Real.log x ∧
      Real.log (x + 1) - Real.log x ≤ 1 / x := by
  have hx1 : 0 < x + 1 := by positivity
  have hu := Real.log_le_sub_one_of_pos (div_pos hx1 hx)
  have hl := Real.log_le_sub_one_of_pos (div_pos hx hx1)
  rw [Real.log_div hx1.ne' hx.ne'] at hu
  rw [Real.log_div hx.ne' hx1.ne'] at hl
  constructor
  · have he : x / (x + 1) - 1 = -(1 / (x + 1)) := by field_simp [hx.ne', hx1.ne']; ring_nf
    rw [he] at hl
    linarith
  · have he : (x + 1) / x - 1 = 1 / x := by field_simp [hx.ne', hx1.ne']; ring_nf
    rwa [he] at hu

/-- Logarithmic unit increments decrease with the base point. -/
theorem log_unit_increment_antitone {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    Real.log (y + 1) - Real.log y ≤ Real.log (x + 1) - Real.log x := by
  have hy := hx.trans_le hxy
  rw [← Real.log_div (by positivity : y + 1 ≠ 0) hy.ne',
    ← Real.log_div (by positivity : x + 1 ≠ 0) hx.ne']
  apply Real.log_le_log (div_pos (by positivity) hy)
  have h := one_div_le_one_div_of_le hx hxy
  have he (z : ℝ) (hz : z ≠ 0) : (z + 1) / z = 1 + 1 / z := by field_simp
  rw [he x hx.ne', he y hy.ne']
  linarith

/-- Existing Kusmin--Landau cancellation applied to actual logarithmic samples. -/
theorem logarithmic_range_cancellation {c A b : ℝ} {N : ℕ}
    (hc : 0 < c) (hA : 0 < A) (hN : 0 < N) (hAN : A + N ≤ 2 * b)
    (hcA : c / A ≤ 1 / 2) :
    ‖∑ n ∈ Finset.range N,
      Complex.exp (2 * Real.pi * Complex.I * ((c * Real.log (A + n) : ℝ) : ℂ))‖ ≤ 2 * b / c := by
  have hb : 0 < b := by have h := Nat.cast_nonneg (α := ℝ) N; linarith
  have hcAb : c ≤ A / 2 := by have h := (div_le_iff₀ hA).mp hcA; linarith
  have hcb : c ≤ b := by have h := Nat.cast_nonneg (α := ℝ) N; linarith
  let θ : ℕ → ℝ := fun n => 2 * Real.pi * c * Real.log (A + n)
  let δ : ℝ := Real.pi * c / b
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδπ : δ ≤ Real.pi := by
    dsimp [δ]
    apply (div_le_iff₀ hb).mpr
    exact mul_le_mul_of_nonneg_left hcb Real.pi_pos.le
  have hdiff (n : ℕ) : θ (n + 1) - θ n =
      (2 * Real.pi * c) * (Real.log (A + n + 1) - Real.log (A + n)) := by
    dsimp [θ]
    push_cast
    ring_nf
  have hlow (n : ℕ) (hn : n ≤ N - 1) : δ ≤ θ (n + 1) - θ n := by
    rw [hdiff]
    have hx : 0 < A + n := by positivity
    have hxB : A + n + 1 ≤ 2 * b := by
      have hn' : (n : ℝ) + 1 ≤ N := by exact_mod_cast (show n + 1 ≤ N by omega)
      linarith
    have h := (log_unit_increment hx).1
    have hi := one_div_le_one_div_of_le (by positivity : 0 < A + n + 1) hxB
    have hm := mul_le_mul_of_nonneg_left (hi.trans h) (by positivity : 0 ≤ 2 * Real.pi * c)
    have he : 2 * Real.pi * c * (1 / (2 * b)) = δ := by dsimp [δ]; ring_nf
    rwa [he] at hm
  have hhigh (n : ℕ) : θ (n + 1) - θ n ≤ 2 * Real.pi - δ := by
    rw [hdiff]
    have hx : 0 < A + n := by positivity
    have h := (log_unit_increment hx).2
    have hi := one_div_le_one_div_of_le hA (by have h := Nat.cast_nonneg (α := ℝ) n; linarith : A ≤ A + n)
    have hm := mul_le_mul_of_nonneg_left (h.trans hi) (by positivity : 0 ≤ 2 * Real.pi * c)
    have hc' := mul_le_mul_of_nonneg_left hcA (by positivity : 0 ≤ 2 * Real.pi)
    have he : 2 * Real.pi * c * (1 / A) = 2 * Real.pi * (c / A) := by ring
    rw [he] at hm
    linarith
  have hmono (n : ℕ) : θ (n + 2) - θ (n + 1) ≤ θ (n + 1) - θ n := by
    have he : n + 2 = (n + 1) + 1 := by omega
    rw [he, hdiff, hdiff]
    push_cast
    exact mul_le_mul_of_nonneg_left
      (log_unit_increment_antitone (by positivity : 0 < A + n) (by linarith : A + n ≤ A + (n + 1)))
      (by positivity)
  have h := RiemannZeta.GuthMaynard.kusminLandau_one_period_decreasing θ (N - 1) δ
    hδ hlow (fun n _ => hhigh n) (fun n _ => hmono n)
  have heN : N - 1 + 1 = N := by omega
  rw [heN] at h
  have hphase (n : ℕ) : RiemannZeta.GuthMaynard.unitaryPhase (θ n) =
      Complex.exp (2 * Real.pi * Complex.I * ((c * Real.log (A + n) : ℝ) : ℂ)) := by
    unfold RiemannZeta.GuthMaynard.unitaryPhase θ
    congr 1
    push_cast
    ring_nf
  simp_rw [hphase] at h
  have he : 2 * Real.pi / δ = 2 * b / c := by dsimp [δ]; field_simp
  rwa [he] at h

/-- Reindex a genuine integer interval by a finite natural range. -/
theorem sum_int_Ioc_eq_range {k l : ℤ} (hkl : k ≤ l) (F : ℤ → ℂ) :
    ∑ n ∈ Finset.Ioc k l, F n =
      ∑ m ∈ Finset.range (l - k).toNat, F (k + 1 + (m : ℤ)) := by
  symm
  apply Finset.sum_bij (fun (m : ℕ) _ => k + 1 + (m : ℤ))
  · intro m hm
    have hm' := Finset.mem_range.mp hm
    have hlen : ((l - k).toNat : ℤ) = l - k := Int.toNat_of_nonneg (by omega)
    have hmz : (m : ℤ) < ((l - k).toNat : ℤ) := by exact_mod_cast hm'
    rw [hlen] at hmz
    exact Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
  · intro m hm n hn he
    omega
  · intro n hn
    obtain ⟨hkn, hnl⟩ := Finset.mem_Ioc.mp hn
    refine ⟨(n - (k + 1)).toNat, ?_, ?_⟩
    · apply Finset.mem_range.mpr
      omega
    · omega
  · intro m hm
    rfl

/-- A logarithmic sum with derivative at most one half has the needed curvature scale. -/
theorem logarithmic_zero_norm {c a b : ℝ} (hc : 0 < c) (ha : 0 < a) (hab : a < b)
    (hβ : c / a ≤ 1 / 2)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2) :
    ‖∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋,
      Complex.exp (2 * Real.pi * Complex.I * ((c * Real.log (n : ℝ) : ℝ) : ℂ))‖ ≤
      2 / Real.sqrt (c / b ^ 2) := by
  obtain ⟨k, hk⟩ := hah
  obtain ⟨l, hl⟩ := hbh
  have hfa : ⌊a⌋ = k := Int.floor_eq_iff.mpr ⟨by linarith, by linarith⟩
  have hfb : ⌊b⌋ = l := Int.floor_eq_iff.mpr ⟨by linarith, by linarith⟩
  have hkl : k < l := by exact_mod_cast (show (k : ℝ) < l by linarith)
  have hb := ha.trans hab
  let N := (l - k).toNat
  have hNi : (N : ℤ) = l - k := Int.toNat_of_nonneg (by omega)
  have hNr : (N : ℝ) = (l : ℝ) - k := by exact_mod_cast hNi
  have hN : 0 < N := by dsimp [N]; omega
  have hNrpos : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hA : 0 < (k : ℝ) + 1 := by linarith
  have hAb : (k : ℝ) + 1 + N ≤ 2 * b := by rw [hNr]; linarith
  have hcA : c / ((k : ℝ) + 1) ≤ 1 / 2 :=
    (div_le_div_of_nonneg_left hc.le ha (by linarith)).trans hβ
  have hcan := logarithmic_range_cancellation hc hA hN hAb hcA
  rw [hfa, hfb, sum_int_Ioc_eq_range hkl.le]
  simp only [Int.cast_add, Int.cast_one, Int.cast_natCast]
  change ‖∑ n ∈ Finset.range N,
    Complex.exp (2 * Real.pi * Complex.I * ((c * Real.log ((k : ℝ) + 1 + n) : ℝ) : ℂ))‖ ≤ _
  have htriv : ‖∑ n ∈ Finset.range N,
    Complex.exp (2 * Real.pi * Complex.I * ((c * Real.log ((k : ℝ) + 1 + n) : ℝ) : ℂ))‖ ≤ b := by
    apply (norm_sum_le _ _).trans
    have hn (n : ℕ) : ‖Complex.exp (2 * Real.pi * Complex.I *
        ((c * Real.log ((k : ℝ) + 1 + n) : ℝ) : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]
      simp
    simp_rw [hn]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    rw [hNr]
    linarith
  have he : 2 / Real.sqrt (c / b ^ 2) = 2 * b / Real.sqrt c := by
    rw [Real.sqrt_div hc.le, Real.sqrt_sq_eq_abs, abs_of_pos hb]
    field_simp
  rw [he]
  by_cases hc1 : c ≤ 1
  · apply htriv.trans
    have hs : Real.sqrt c ≤ 1 := (Real.sqrt_le_one).mpr hc1
    apply (le_div_iff₀ (Real.sqrt_pos.mpr hc)).mpr
    nlinarith
  · apply hcan.trans
    have hsc : Real.sqrt c ≤ c := by
      have hs := Real.sq_sqrt hc.le
      have hn := Real.sqrt_nonneg c
      nlinarith
    exact div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.mpr hc) hsc

/-- The combined printed E₁/E₂ coefficient is nonnegative below derivative one half. -/
theorem printed_zero_coefficients_nonneg {β : ℝ} (hβ : 0 < β) (hh : β ≤ 1 / 2) :
    0 ≤ printedPartIIE1 β / β + partIICubeCoefficient β := by
  have hf : ⌊β⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
  have hd : 0 < 1 - β := by linarith
  have he : printedPartIIE1 β / β + partIICubeCoefficient β =
      1 / (1 - β) ^ 3 + 1 / (2 - β) ^ 3 + 1 / (2 * (2 - β) ^ 2) +
        1 / (β * (2 - β) ^ 2) + 1 / (2 * β ^ 2) - 1 / (2 * (1 + β) ^ 2) := by
    unfold printedPartIIE1 partIICubeCoefficient
    simp only [hf, Nat.cast_zero, sub_zero, zero_add]
    have h1 : 1 + β ≠ 0 := by positivity
    have h2 : 2 - β ≠ 0 := by linarith
    have h3 : 1 - β + 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [he]
  have hsq : 2 * β ^ 2 ≤ 2 * (1 + β) ^ 2 := by nlinarith
  have hi := one_div_le_one_div_of_le (by positivity : 0 < 2 * β ^ 2) hsq
  have hp : 0 ≤ 1 / (1 - β) ^ 3 + 1 / (2 - β) ^ 3 +
      1 / (2 * (2 - β) ^ 2) + 1 / (β * (2 - β) ^ 2) := by
    have h2 : 0 < 2 - β := by linarith
    positivity
  linarith

/-- The printed stationary error alone dominates twice the inverse square-root curvature. -/
theorem stationary_zero_budget {ℓ w : ℝ} (hℓ : 0 < ℓ) (hw : ℓ ≤ w) :
    2 / Real.sqrt ℓ ≤ 2.686 / Real.sqrt ℓ + 2 / Real.pi * Real.log w := by
  have hlog := neg_inv_sqrt_le_log (hℓ.trans_le hw)
  have hs := one_div_le_one_div_of_le (Real.sqrt_pos.mpr hℓ) (Real.sqrt_le_sqrt hw)
  have hlow : -(1 / Real.sqrt ℓ) ≤ Real.log w := by linarith
  have hp : 2 / Real.pi ≤ (2 / 3 : ℝ) := by
    apply (div_le_iff₀ Real.pi_pos).mpr
    linarith [Real.pi_gt_three]
  have hmul := mul_le_mul_of_nonneg_left hlow (by positivity : 0 ≤ 2 / Real.pi)
  have hmul' := mul_le_mul_of_nonneg_right hp (by positivity : 0 ≤ 1 / Real.sqrt ℓ)
  have hi : 0 ≤ 1 / Real.sqrt ℓ := by positivity
  norm_num only [div_eq_mul_inv] at hmul hmul' hi ⊢
  nlinarith only [hmul, hmul', hi]

/-- The literal source remainder holds in the zero-frequency logarithmic case when δ≥1/2. -/
theorem logarithmic_b_process_printed_zero {c a b : ℝ} (hc : 0 < c) (ha : 0 < a) (hab : a < b)
    (hzero : ⌊c / a⌋₊ = 0)
    (hδ : 1 / 2 ≤ (⌊c / a⌋₊ : ℝ) + 1 - c / a)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2) :
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * ((c * Real.log (n : ℝ) : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊c / a⌋₊, ((Real.sqrt c / (ν : ℝ) : ℝ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * ((c * Real.log (c / (ν : ℝ)) - c - 1 / 8 : ℝ) : ℂ))‖ ≤
      2.686 / Real.sqrt (c / b ^ 2) +
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * (b ^ 2 / a ^ 2) *
          (2 * c / a ^ 3) ^ (1 / 3 : ℝ) * (b - a) +
        2 / Real.pi * Real.log (c / a - c / b) +
      (((c / b) * halfSecondEndpointBound ⌊c / a⌋₊ (c / b) +
          (c / a) * halfSecondEndpointBound ⌊c / a⌋₊ (c / a)) / (2 * Real.pi) +
        (c / a ^ 2) * printedPartIIE1 (c / a) / (2 * Real.pi ^ 2 * (c / a)) +
        (c / a ^ 2) * partIICubeCoefficient (c / a) / (2 * Real.pi ^ 2) +
        1 / (2 * Real.pi * (c / a)) + 1.251 + Real.log 2 / (2 * Real.pi)) := by
  have hβ : c / a ≤ 1 / 2 := by
    have hd := hδ
    simp only [hzero, Nat.cast_zero, zero_add] at hd
    linarith
  have hβp : 0 < c / a := div_pos hc ha
  have hb := ha.trans hab
  have hαp : 0 < c / b := div_pos hc hb
  have hℓ : 0 < c / b ^ 2 := by positivity
  have hlen := half_integer_length_ge_one hab hah hbh
  have hr := afePhase_constant_secondOrderRegularity hc ha hab
  have hscl := afePhase_b_process_scales hc ha hab.le
  have hanti := (afePhase_strictAnti hc).mono (fun u (hu : u ∈ Set.Icc a b) => ha.trans_le hu.1)
  have hcurv := stationary_curvature_of_antitone hab hr.f_deriv_differentiable hanti.antitoneOn hscl.1
  have hw0 := stationary_derivative_drop hr.f_deriv_differentiable hcurv
    (Set.left_mem_Icc.mpr hab.le) (Set.right_mem_Icc.mpr hab.le) hab.le
  rw [(afePhase_hasDerivAt c ha).deriv, (afePhase_hasDerivAt c hb).deriv] at hw0
  have hw : c / b ^ 2 ≤ c / a - c / b := by nlinarith
  have hstat := stationary_zero_budget hℓ hw
  have hnorm := logarithmic_zero_norm hc ha hab hβ hah hbh
  have hdual : (∑ ν ∈ Finset.Icc 1 ⌊c / a⌋₊, ((Real.sqrt c / (ν : ℝ) : ℝ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * ((c * Real.log (c / (ν : ℝ)) - c - 1 / 8 : ℝ) : ℂ))) = 0 := by
    simp [hzero]
  rw [hdual, sub_zero]
  have hcoef := mul_nonneg (by positivity : 0 ≤ (c / a ^ 2) / (2 * Real.pi ^ 2))
    (printed_zero_coefficients_nonneg hβp hβ)
  have he : (c / a ^ 2) / (2 * Real.pi ^ 2) *
      (printedPartIIE1 (c / a) / (c / a) + partIICubeCoefficient (c / a)) =
      (c / a ^ 2) * printedPartIIE1 (c / a) / (2 * Real.pi ^ 2 * (c / a)) +
        (c / a ^ 2) * partIICubeCoefficient (c / a) / (2 * Real.pi ^ 2) := by ring
  rw [he] at hcoef
  have hB (y : ℝ) (hy : 0 < y) : 0 ≤ y * halfSecondEndpointBound ⌊c / a⌋₊ y := by
    unfold halfSecondEndpointBound
    positivity
  have hend : 0 ≤ ((c / b) * halfSecondEndpointBound ⌊c / a⌋₊ (c / b) +
      (c / a) * halfSecondEndpointBound ⌊c / a⌋₊ (c / a)) / (2 * Real.pi) :=
    div_nonneg (add_nonneg (hB _ hαp) (hB _ hβp)) (by positivity)
  have hnonlin : 0 ≤ (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) *
      (b ^ 2 / a ^ 2) * (2 * c / a ^ 3) ^ (1 / 3 : ℝ) * (b - a) := by positivity
  have hhead : 0 ≤ 1 / (2 * Real.pi * (c / a)) + 1.251 + Real.log 2 / (2 * Real.pi) := by positivity
  linarith

/-- The literal logarithmic B-process for every frequency count, on the proved δ≥1/2 range. -/
theorem logarithmic_b_process_printed_half {c a b : ℝ} (hc : 0 < c) (ha : 0 < a) (hab : a < b)
    (hα : c / b < 1)
    (hδ : 1 / 2 ≤ (⌊c / a⌋₊ : ℝ) + 1 - c / a)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2) :
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * ((c * Real.log (n : ℝ) : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊c / a⌋₊, ((Real.sqrt c / (ν : ℝ) : ℝ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * ((c * Real.log (c / (ν : ℝ)) - c - 1 / 8 : ℝ) : ℂ))‖ ≤
      2.686 / Real.sqrt (c / b ^ 2) +
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * (b ^ 2 / a ^ 2) *
          (2 * c / a ^ 3) ^ (1 / 3 : ℝ) * (b - a) +
        2 / Real.pi * Real.log (c / a - c / b) +
      (((c / b) * halfSecondEndpointBound ⌊c / a⌋₊ (c / b) +
          (c / a) * halfSecondEndpointBound ⌊c / a⌋₊ (c / a)) / (2 * Real.pi) +
        (c / a ^ 2) * printedPartIIE1 (c / a) / (2 * Real.pi ^ 2 * (c / a)) +
        (c / a ^ 2) * partIICubeCoefficient (c / a) / (2 * Real.pi ^ 2) +
        1 / (2 * Real.pi * (c / a)) + 1.251 + Real.log 2 / (2 * Real.pi)) := by
  by_cases hz : ⌊c / a⌋₊ = 0
  · exact logarithmic_b_process_printed_zero hc ha hab hz hδ hah hbh
  by_cases ho : ⌊c / a⌋₊ = 1
  · exact logarithmic_b_process_printed_one hc ha hab hα ho hδ hah hbh
  have hm : 2 ≤ ⌊c / a⌋₊ := by omega
  have hmR : (2 : ℝ) ≤ ⌊c / a⌋₊ := by exact_mod_cast hm
  have hfloor := Nat.floor_le (div_nonneg hc.le ha.le)
  exact logarithmic_b_process_printed hc ha hab hα (by linarith) hδ hah hbh

end DhimanKadiriQuesadaHerrera2026

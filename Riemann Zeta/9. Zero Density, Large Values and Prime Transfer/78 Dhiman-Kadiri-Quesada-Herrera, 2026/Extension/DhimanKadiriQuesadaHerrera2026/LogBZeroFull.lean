import DhimanKadiriQuesadaHerrera2026.LogBZero

namespace DhimanKadiriQuesadaHerrera2026

/-- The curvature term and cubic endpoint term absorb a reciprocal endpoint gap. -/
theorem cubic_gap_absorb {x δ : ℝ} (hx : 0 < x) (hd : 0 < δ) :
    1 / δ ≤ 2 * x + 1 / (2 * Real.pi ^ 2 * x ^ 2 * δ ^ 3) := by
  have hp : Real.pi ^ 2 ≤ 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hpoly : 0 ≤ 40 * (x * δ) ^ 3 - 20 * (x * δ) ^ 2 + 1 := by
    have h := mul_nonneg (sq_nonneg (x * δ - 1 / 3))
      (by positivity : 0 ≤ x * δ + 1 / 6)
    nlinarith
  have hr : 1 / δ ≤ 2 * x + 1 / (20 * x ^ 2 * δ ^ 3) := by
    have hstep : 1 / δ - 2 * x ≤ 1 / (20 * x ^ 2 * δ ^ 3) := by
      apply (le_div_iff₀ (by positivity : 0 < 20 * x ^ 2 * δ ^ 3)).mpr
      have he : (1 / δ - 2 * x) * (20 * x ^ 2 * δ ^ 3) =
          20 * (x * δ) ^ 2 - 40 * (x * δ) ^ 3 := by field_simp; ring
      rw [he]
      linarith
    linarith
  apply hr.trans
  apply add_le_add le_rfl
  exact one_div_le_one_div_of_le (by positivity)
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith : 2 * Real.pi ^ 2 ≤ 20)
      (sq_nonneg x)) (by positivity))

/-- Kusmin--Landau with an explicit gap from both neighboring integer frequencies. -/
theorem logarithmic_range_gap {c A b η : ℝ} {N : ℕ}
    (hc : 0 < c) (hA : 0 < A) (hN : 0 < N) (hAN : A + N ≤ 2 * b)
    (hη : 0 < η) (hηb : η ≤ c / (2 * b)) (hηA : η + c / A ≤ 1) :
    ‖∑ n ∈ Finset.range N,
      Complex.exp (2 * Real.pi * Complex.I * ((c * Real.log (A + n) : ℝ) : ℂ))‖ ≤ 1 / η := by
  have hb : 0 < b := by have h := Nat.cast_nonneg (α := ℝ) N; linarith
  let θ : ℕ → ℝ := fun n => 2 * Real.pi * c * Real.log (A + n)
  let δ : ℝ := 2 * Real.pi * η
  have hδ : 0 < δ := by dsimp [δ]; positivity
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
    have hh := mul_le_mul_of_nonneg_left hηb (by positivity : 0 ≤ 2 * Real.pi)
    have he : 2 * Real.pi * c * (1 / (2 * b)) = 2 * Real.pi * (c / (2 * b)) := by ring
    rw [he] at hm
    exact hh.trans hm
  have hhigh (n : ℕ) : θ (n + 1) - θ n ≤ 2 * Real.pi - δ := by
    rw [hdiff]
    have hx : 0 < A + n := by positivity
    have h := (log_unit_increment hx).2
    have hi := one_div_le_one_div_of_le hA (by have h := Nat.cast_nonneg (α := ℝ) n; linarith : A ≤ A + n)
    have hm := mul_le_mul_of_nonneg_left (h.trans hi) (by positivity : 0 ≤ 2 * Real.pi * c)
    have hc' := mul_le_mul_of_nonneg_left hηA (by positivity : 0 ≤ 2 * Real.pi)
    have he : 2 * Real.pi * c * (1 / A) = 2 * Real.pi * (c / A) := by ring
    rw [he] at hm
    dsimp [δ]
    nlinarith
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
  have he : 2 * Real.pi / δ = 1 / η := by dsimp [δ]; field_simp
  rwa [he] at h

/-- The actual integer logarithmic sum with no stationary frequencies and an arbitrary positive gap. -/
theorem logarithmic_zero_gap_norm {c a b : ℝ} (hc : 0 < c) (ha : 0 < a) (hab : a < b)
    (hβ : c / a < 1)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2) :
    ‖∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋,
      Complex.exp (2 * Real.pi * Complex.I * ((c * Real.log (n : ℝ) : ℝ) : ℂ))‖ ≤
      max (2 * b / c) (1 / (1 - c / a)) := by
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
  have hcA : c / ((k : ℝ) + 1) ≤ c / a := div_le_div_of_nonneg_left hc.le ha (by linarith)
  let η := min (c / (2 * b)) (1 - c / a)
  have hη : 0 < η := lt_min (by positivity) (by linarith)
  have hηb : η ≤ c / (2 * b) := min_le_left _ _
  have hηA : η + c / ((k : ℝ) + 1) ≤ 1 := by
    have h := min_le_right (c / (2 * b)) (1 - c / a)
    dsimp [η]
    linarith
  have hcan := logarithmic_range_gap hc hA hN hAb hη hηb hηA
  rw [hfa, hfb, sum_int_Ioc_eq_range hkl.le]
  simp only [Int.cast_add, Int.cast_one, Int.cast_natCast]
  change ‖∑ n ∈ Finset.range N,
    Complex.exp (2 * Real.pi * Complex.I * ((c * Real.log ((k : ℝ) + 1 + n) : ℝ) : ℂ))‖ ≤ _
  apply hcan.trans
  dsimp [η]
  by_cases hle : c / (2 * b) ≤ 1 - c / a
  · rw [min_eq_left hle]
    have he : 1 / (c / (2 * b)) = 2 * b / c := by field_simp
    rw [he]
    exact le_max_left _ _
  · rw [min_eq_right (le_of_not_ge hle)]
    exact le_max_right _ _

/-- In the zero-frequency case the printed combined coefficient supplies its full cubic singularity. -/
theorem printed_zero_coefficients_lower {β : ℝ} (hβ : 0 < β) (hh : β < 1) :
    1 / (1 - β) ^ 3 ≤ printedPartIIE1 β / β + partIICubeCoefficient β := by
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
  have hp : 0 ≤ 1 / (2 - β) ^ 3 +
      1 / (2 * (2 - β) ^ 2) + 1 / (β * (2 - β) ^ 2) := by
    have h2 : 0 < 2 - β := by linarith
    positivity
  linarith

/-- The unit-norm bound on the actual half-integer logarithmic sum. -/
theorem logarithmic_half_sum_trivial {c a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2) :
    ‖∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋,
      Complex.exp (2 * Real.pi * Complex.I * ((c * Real.log (n : ℝ) : ℝ) : ℂ))‖ ≤
      b := by
  obtain ⟨k, hk⟩ := hah
  obtain ⟨l, hl⟩ := hbh
  have hfa : ⌊a⌋ = k := Int.floor_eq_iff.mpr ⟨by linarith, by linarith⟩
  have hfb : ⌊b⌋ = l := Int.floor_eq_iff.mpr ⟨by linarith, by linarith⟩
  have hkl : k < l := by exact_mod_cast (show (k : ℝ) < l by linarith)
  let N := (l - k).toNat
  have hNi : (N : ℤ) = l - k := Int.toNat_of_nonneg (by omega)
  have hNr : (N : ℝ) = (l : ℝ) - k := by exact_mod_cast hNi
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
  exact htriv

/-- A no-stationary-frequency logarithmic sum is controlled by curvature plus the printed cubic singularity. -/
theorem logarithmic_zero_cubic_bound {c a b : ℝ} (hc : 0 < c) (ha : 0 < a) (hab : a < b)
    (hβ : c / a < 1)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2) :
    ‖∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋,
      Complex.exp (2 * Real.pi * Complex.I * ((c * Real.log (n : ℝ) : ℝ) : ℂ))‖ ≤
      2 / Real.sqrt (c / b ^ 2) + (c / a ^ 2) / (2 * Real.pi ^ 2 * (1 - c / a) ^ 3) := by
  have hb := ha.trans hab
  have hd : 0 < 1 - c / a := by linarith
  have hsq : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have he : 2 / Real.sqrt (c / b ^ 2) = 2 * b / Real.sqrt c := by
    rw [Real.sqrt_div hc.le, Real.sqrt_sq_eq_abs, abs_of_pos hb]
    field_simp
  rw [he]
  have htail : 0 ≤ (c / a ^ 2) / (2 * Real.pi ^ 2 * (1 - c / a) ^ 3) := by positivity
  by_cases hc1 : c ≤ 1
  · have htriv := logarithmic_half_sum_trivial (c := c) ha hab hah hbh
    have hs : Real.sqrt c ≤ 1 := Real.sqrt_le_one.mpr hc1
    have hle : b ≤ 2 * b / Real.sqrt c := (le_div_iff₀ hsq).mpr (by nlinarith)
    linarith
  · have hcan := logarithmic_zero_gap_norm hc ha hab hβ hah hbh
    apply hcan.trans
    apply max_le
    · have hsc : Real.sqrt c ≤ c := by
        have hs := Real.sq_sqrt hc.le
        have hn := Real.sqrt_nonneg c
        nlinarith
      have hle := div_le_div_of_nonneg_left (by positivity : 0 ≤ 2 * b) hsq hsc
      linarith
    · have hg := cubic_gap_absorb (div_pos ha hsq) hd
      have hgTail : 1 / (2 * Real.pi ^ 2 * (a / Real.sqrt c) ^ 2 * (1 - c / a) ^ 3) =
          (c / a ^ 2) / (2 * Real.pi ^ 2 * (1 - c / a) ^ 3) := by
        field_simp
        rw [Real.sq_sqrt hc.le]
      rw [hgTail] at hg
      have habd := div_le_div_of_nonneg_right hab.le hsq.le
      have he2 : 2 * (a / Real.sqrt c) = (2 * a) / Real.sqrt c := by ring
      rw [he2] at hg
      norm_num only [div_eq_mul_inv] at hg habd ⊢
      linarith

/-- The printed logarithmic B-process is valid for zero stationary frequencies on the entire positive δ range. -/
theorem logarithmic_b_process_printed_zero_full {c a b : ℝ} (hc : 0 < c) (ha : 0 < a) (hab : a < b)
    (hzero : ⌊c / a⌋₊ = 0)
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
  have hβ : c / a < 1 := Nat.floor_eq_zero.mp hzero
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
  have hnorm := logarithmic_zero_cubic_bound hc ha hab hβ hah hbh
  have hdual : (∑ ν ∈ Finset.Icc 1 ⌊c / a⌋₊, ((Real.sqrt c / (ν : ℝ) : ℝ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * ((c * Real.log (c / (ν : ℝ)) - c - 1 / 8 : ℝ) : ℂ))) = 0 := by
    simp [hzero]
  rw [hdual, sub_zero]
  have hcoef := mul_le_mul_of_nonneg_left (printed_zero_coefficients_lower hβp hβ)
    (by positivity : 0 ≤ (c / a ^ 2) / (2 * Real.pi ^ 2))
  have he : (c / a ^ 2) / (2 * Real.pi ^ 2) *
      (printedPartIIE1 (c / a) / (c / a) + partIICubeCoefficient (c / a)) =
      (c / a ^ 2) * printedPartIIE1 (c / a) / (2 * Real.pi ^ 2 * (c / a)) +
        (c / a ^ 2) * partIICubeCoefficient (c / a) / (2 * Real.pi ^ 2) := by ring
  rw [he] at hcoef
  have htailEq : (c / a ^ 2) / (2 * Real.pi ^ 2) * (1 / (1 - c / a) ^ 3) =
      (c / a ^ 2) / (2 * Real.pi ^ 2 * (1 - c / a) ^ 3) := by field_simp
  rw [htailEq] at hcoef
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

end DhimanKadiriQuesadaHerrera2026

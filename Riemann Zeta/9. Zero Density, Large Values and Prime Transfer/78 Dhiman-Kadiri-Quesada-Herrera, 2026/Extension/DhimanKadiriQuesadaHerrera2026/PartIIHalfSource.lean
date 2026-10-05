import DhimanKadiriQuesadaHerrera2026.PartIIShiftInputs
import DhimanKadiriQuesadaHerrera2026.SecondHalfErrors

namespace DhimanKadiriQuesadaHerrera2026

/-- The exact half-offset square assembly also covers y=1/2 and the zero frequency cutoff. -/
theorem squareBounds_exact_half_offset {M : ℕ} {y : ℝ} (hy : 0 < y)
    (hM : (M : ℝ) + 1 = y + 1 / 2) :
    minusSquareBound M y + plusSquareBound y = (46 / 9) / y +
      (Real.log (y + 1) - Real.log (y + 1 / 2) + 1 / (y + 1 / 2) -
        2 * Real.log 2 - (1 + 2 * y) / (2 * (y + 1))) / y ^ 2 := by
  dsimp only [minusSquareBound, plusSquareBound]
  rw [hM, show y + 1 / 2 - y = 1 / 2 by ring]
  norm_num [real_digamma_half]
  have h1 : y + 1 ≠ 0 := by positivity
  have hh : y + 1 / 2 ≠ 0 := by positivity
  field_simp
  ring_nf

/-- The unchanged half-offset cube assembly includes the smallest positive half-integer parameter. -/
theorem cubeBounds_exact_half_offset {M : ℕ} {y : ℝ} (hy : 0 < y)
    (hM : (M : ℝ) + 1 = y + 1 / 2) :
    minusCubeBound M y + plusCubeBound y = (230 / 27) / y - (14 / 3) / y ^ 2 +
      (Real.log (y + 1 / 2) + Real.log (y + 1) + 2 * Real.log 2 +
        2 * Real.eulerMascheroniConstant - 1 / (2 * (y + 1 / 2)) -
        (1 + 3 * y + 3 * y ^ 2) / (2 * (y + 1) ^ 2)) / y ^ 3 := by
  dsimp only [minusCubeBound, plusCubeBound]
  rw [hM, show y + 1 / 2 - y = 1 / 2 by ring]
  norm_num [real_digamma_half]
  have h1 : y + 1 ≠ 0 := by positivity
  have hh : y + 1 / 2 ≠ 0 := by positivity
  field_simp
  ring_nf

/-- The proposed E₁ coefficient has its exact half-offset expression on the whole positive domain. -/
theorem partIISquareTailEnvelope_half_offset {y : ℝ} (hy : 0 < y)
    (hδ : (⌊y⌋₊ : ℝ) + 1 - y = 1 / 2) :
    partIISquareTailEnvelope y = 46 / 9 +
      (Real.log (y + 1) - Real.log (y + 1 / 2) + 1 / (y + 1 / 2) -
        2 * Real.log 2 - (1 + 2 * y) / (2 * (y + 1))) / y := by
  have he := squareBounds_exact_half_offset hy (show (⌊y⌋₊ : ℝ) + 1 = y + 1 / 2 by linarith)
  rw [squareBounds_eq_proposed_envelope hy] at he
  have hid : (46 / 9) / y +
      (Real.log (y + 1) - Real.log (y + 1 / 2) + 1 / (y + 1 / 2) -
        2 * Real.log 2 - (1 + 2 * y) / (2 * (y + 1))) / y ^ 2 =
      (46 / 9 + (Real.log (y + 1) - Real.log (y + 1 / 2) + 1 / (y + 1 / 2) -
        2 * Real.log 2 - (1 + 2 * y) / (2 * (y + 1))) / y) / y := by
    field_simp
  rw [hid] at he
  exact (div_left_inj' hy.ne').mp he

/-- The unchanged E₂ coefficient has the exact literal half-offset simplification. -/
theorem partIICubeCoefficient_half_offset {y : ℝ} (hy : 0 < y)
    (hδ : (⌊y⌋₊ : ℝ) + 1 - y = 1 / 2) :
    partIICubeCoefficient y = 230 / 27 - (14 / 3) / y +
      (Real.log (y + 1 / 2) + Real.log (y + 1) + 2 * Real.log 2 +
        2 * Real.eulerMascheroniConstant - 1 / (2 * (y + 1 / 2)) -
        (1 + 3 * y + 3 * y ^ 2) / (2 * (y + 1) ^ 2)) / y ^ 2 := by
  have he := cubeBounds_exact_half_offset hy (show (⌊y⌋₊ : ℝ) + 1 = y + 1 / 2 by linarith)
  rw [cubeBounds_eq_source_coefficient hy] at he
  have hid : (230 / 27) / y - (14 / 3) / y ^ 2 +
      (Real.log (y + 1 / 2) + Real.log (y + 1) + 2 * Real.log 2 +
        2 * Real.eulerMascheroniConstant - 1 / (2 * (y + 1 / 2)) -
        (1 + 3 * y + 3 * y ^ 2) / (2 * (y + 1) ^ 2)) / y ^ 3 =
      (230 / 27 - (14 / 3) / y +
      (Real.log (y + 1 / 2) + Real.log (y + 1) + 2 * Real.log 2 +
        2 * Real.eulerMascheroniConstant - 1 / (2 * (y + 1 / 2)) -
        (1 + 3 * y + 3 * y ^ 2) / (2 * (y + 1) ^ 2)) / y ^ 2) / y := by
    field_simp
  rw [hid] at he
  exact (div_left_inj' hy.ne').mp he

/-- The full weighted inequality has literal half-offset coefficients, including the zero-cutoff case. -/
theorem SecondOrderRegularity.exact_half_offset_bound {f g : ℝ → ℝ} {a b : ℝ}
    (r : SecondOrderRegularity f g a b)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2)
    (hδ : (⌊deriv f a⌋₊ : ℝ) + 1 - deriv f a = 1 / 2) :
    let y := deriv f a
    let z := deriv f b
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, weightedWave f g (n : ℝ)) - poissonMain f g a b ⌊y⌋₊‖ ≤
      ((g a + g b) / (2 * Real.pi)) * (Real.log 2 + 1 / y) +
      secondH f g b / (4 * Real.pi ^ 2) *
        ((1 / z) * (Real.pi / 2 + 1 / (y + 1 / 2) + Real.log 2 + 3 / (2 * (z + 1)))) +
      secondH f g a / (4 * Real.pi ^ 2) *
        ((1 / y) * (Real.pi / 2 + 1 / (y + 1 / 2) + Real.log 2 + 3 / (2 * (y + 1)))) +
      secondH1 f g a / (4 * Real.pi ^ 3) *
        ((46 / 9) / y + (Real.log (y + 1) - Real.log (y + 1 / 2) + 1 / (y + 1 / 2) -
          2 * Real.log 2 - (1 + 2 * y) / (2 * (y + 1))) / y ^ 2) +
      (secondH f g a * |deriv (deriv f) a| / (4 * Real.pi ^ 3)) *
        ((230 / 27) / y - (14 / 3) / y ^ 2 +
          (Real.log (y + 1 / 2) + Real.log (y + 1) + 2 * Real.log 2 +
            2 * Real.eulerMascheroniConstant - 1 / (2 * (y + 1 / 2)) -
            (1 + 3 * y + 3 * y ^ 2) / (2 * (y + 1) ^ 2)) / y ^ 3) := by
  dsimp only
  have hy := r.f_deriv_pos a (Set.left_mem_Icc.mpr r.lt.le)
  have hM : (⌊deriv f a⌋₊ : ℝ) + 1 = deriv f a + 1 / 2 := by linarith
  have ht := r.half_integer_bound hah hbh hδ.ge
  dsimp only at ht
  rw [squareBounds_exact_half_offset hy hM, cubeBounds_exact_half_offset hy hM] at ht
  simpa only [halfSecondEndpointBound, hM] using ht

/-- The exact half-offset inequality restores every integer frequency and retains the shifted endpoint weights. -/
theorem second_poisson_shifted_exact_half {f g : ℝ → ℝ} {a b : ℝ} {N : ℕ}
    (h : PartIRegularityAt f g a b N)
    (r : SecondOrderRegularity (phaseShift f N) g a b)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2)
    (hδ : 1 - Int.fract (deriv f a) = 1 / 2) :
    let F := phaseShift f N
    let y := deriv f a - N
    let z := deriv f b - N
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, weightedWave f g (n : ℝ)) -
      ∑ ν ∈ Finset.Icc N ⌊deriv f a⌋₊,
        ∫ u in a..b, (g u : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))‖ ≤
      ((g a + g b) / (2 * Real.pi)) * (Real.log 2 + 1 / y) +
      secondH F g b / (4 * Real.pi ^ 2) *
        ((1 / z) * (Real.pi / 2 + 1 / (y + 1 / 2) + Real.log 2 + 3 / (2 * (z + 1)))) +
      secondH F g a / (4 * Real.pi ^ 2) *
        ((1 / y) * (Real.pi / 2 + 1 / (y + 1 / 2) + Real.log 2 + 3 / (2 * (y + 1)))) +
      secondH1 F g a / (4 * Real.pi ^ 3) *
        ((46 / 9) / y + (Real.log (y + 1) - Real.log (y + 1 / 2) + 1 / (y + 1 / 2) -
          2 * Real.log 2 - (1 + 2 * y) / (2 * (y + 1))) / y ^ 2) +
      (secondH F g a * |deriv (deriv F) a| / (4 * Real.pi ^ 3)) *
        ((230 / 27) / y - (14 / 3) / y ^ 2 +
          (Real.log (y + 1 / 2) + Real.log (y + 1) + 2 * Real.log 2 +
            2 * Real.eulerMascheroniConstant - 1 / (2 * (y + 1 / 2)) -
            (1 + 3 * y + 3 * y ^ 2) / (2 * (y + 1) ^ 2)) / y ^ 3) := by
  have ha := Set.left_mem_Icc.mpr h.lt.le
  have hb := Set.right_mem_Icc.mpr h.lt.le
  have hd := deriv_phaseShift N (h.f_differentiable a ha)
  have hdb := deriv_phaseShift N (h.f_differentiable b hb)
  have hδ' : (⌊deriv (phaseShift f N) a⌋₊ : ℝ) + 1 - deriv (phaseShift f N) a = 1 / 2 := by
    rw [hd, Nat.floor_sub_natCast, shifted_floor_delta (h.deriv_gt ha).le]
    exact hδ
  have ht := r.exact_half_offset_bound hah hbh hδ'
  dsimp only at ht ⊢
  rw [weighted_sum_phaseShift, poissonMain_phaseShift h] at ht
  simpa only [hd, hdb] using ht

/-- The full half-offset source inequality follows from explicit shifted analytic inputs. -/
theorem second_poisson_half_offset_from_inputs {f g : ℝ → ℝ} {a b : ℝ} {N : ℕ}
    (r : PartIRegularityAt f g a b N)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hfc : ContinuousOn (deriv (deriv f)) (Set.Icc a b))
    (hg : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv g) u)
    (hgc : ContinuousOn (deriv (deriv g)) (Set.Icc a b))
    (hfa : AntitoneOn (fun u => |deriv (deriv f) u|) (Set.Icc a b))
    (hgn : ∀ u ∈ Set.Icc a b, 0 ≤ deriv (deriv g) u)
    (hga : AntitoneOn (deriv (deriv g)) (Set.Icc a b))
    (hq : ∀ h : ℝ → ℝ, (h = deriv g ∨ h = fun u => g u * (deriv f u - N)) →
      ∀ n : ℕ, AntitoneOn (fun u => |deriv h u| / (((n : ℝ) + 1) + deriv f u - N) ^ 2) (Set.Icc a b))
    (hc : ∀ h : ℝ → ℝ, (h = deriv g ∨ h = fun u => g u * (deriv f u - N)) →
      ∀ n : ℕ, AntitoneOn (fun u => |h u * deriv (deriv f) u| /
        (((n : ℝ) + 1) + deriv f u - N) ^ 3) (Set.Icc a b))
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2)
    (hδ : 1 - Int.fract (deriv f a) = 1 / 2) :
    let F := phaseShift f N
    let y := deriv f a - N
    let z := deriv f b - N
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, weightedWave f g (n : ℝ)) -
      ∑ ν ∈ Finset.Icc N ⌊deriv f a⌋₊,
        ∫ u in a..b, (g u : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))‖ ≤
      ((g a + g b) / (2 * Real.pi)) * (Real.log 2 + 1 / y) +
      secondH F g b / (4 * Real.pi ^ 2) *
        ((1 / z) * (Real.pi / 2 + 1 / (y + 1 / 2) + Real.log 2 + 3 / (2 * (z + 1)))) +
      secondH F g a / (4 * Real.pi ^ 2) *
        ((1 / y) * (Real.pi / 2 + 1 / (y + 1 / 2) + Real.log 2 + 3 / (2 * (y + 1)))) +
      secondH1 F g a / (4 * Real.pi ^ 3) *
        ((46 / 9) / y + (Real.log (y + 1) - Real.log (y + 1 / 2) + 1 / (y + 1 / 2) -
          2 * Real.log 2 - (1 + 2 * y) / (2 * (y + 1))) / y ^ 2) +
      (secondH F g a * |deriv (deriv F) a| / (4 * Real.pi ^ 3)) *
        ((230 / 27) / y - (14 / 3) / y ^ 2 +
          (Real.log (y + 1 / 2) + Real.log (y + 1) + 2 * Real.log 2 +
            2 * Real.eulerMascheroniConstant - 1 / (2 * (y + 1 / 2)) -
            (1 + 3 * y + 3 * y ^ 2) / (2 * (y + 1) ^ 2)) / y ^ 3) := by
  exact second_poisson_shifted_exact_half r
    (secondOrderRegularity_shift_of_inputs r hf hfc hg hgc hfa hgn hga hq hc) hah hbh hδ

end DhimanKadiriQuesadaHerrera2026

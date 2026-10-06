import DhimanKadiriQuesadaHerrera2026.PartIIInputs
import DhimanKadiriQuesadaHerrera2026.SecondEndpoints
import DhimanKadiriQuesadaHerrera2026.PoissonShift

namespace DhimanKadiriQuesadaHerrera2026

/-- The exact sum of the absolute reciprocal tails, valid also at integer endpoints. -/
noncomputable def secondTailAbsolute (M : ℕ) (y : ℝ) : ℝ :=
  ((Complex.digamma ((M : ℝ) + 1 : ℝ)).re -
    (Complex.digamma ((M : ℝ) + 1 - y : ℝ)).re +
      (Complex.digamma (y + 1 : ℝ)).re + Real.eulerMascheroniConstant) / y

/-- The literal sum Z₀+Z₁ away from integer endpoints. -/
noncomputable def secondTailSource (M : ℕ) (x y : ℝ) : ℝ :=
  (1 / (y * |Real.sin (Real.pi * x)|)) *
    (1 / ((M : ℝ) + 1 - y) + 1 / ((M : ℝ) + 1) + 1 + 1 / (1 + y))

/-- The source endpoint convention is completed by the absolute-tail value at integers. -/
noncomputable def secondTailMajorant (M : ℕ) (x y : ℝ) : ℝ := by
  classical
  exact if ∃ k : ℤ, x = (k : ℝ) then secondTailAbsolute M y else secondTailSource M x y

/-- The complete pair of actual endpoint tails is bounded by its absolute reciprocal sums. -/
theorem second_tail_absolute_bound {M : ℕ} {y : ℝ} (hy : 0 < y)
    (hM : y < (M : ℝ) + 1) (x : ℝ) :
    ‖negativeTail M x y‖ + ‖positiveTail (-x) y‖ ≤ secondTailAbsolute M y := by
  have hn : ‖negativeTail M x y‖ ≤
      ((Complex.digamma ((M : ℝ) + 1 : ℝ)).re -
        (Complex.digamma ((M : ℝ) + 1 - y : ℝ)).re) / y := by
    rw [negativeTail_eq_shift hy hM]
    apply tsum_of_norm_bounded (hasSum_harmonic_tail hy hM)
    intro n
    have hd : 0 < (n : ℝ) + M + 1 - y := by linarith [Nat.cast_nonneg (α := ℝ) n]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / (((n : ℝ) + M + 1) * ((n : ℝ) + M + 1 - y))), norm_expMode, mul_one]
  have hp : ‖positiveTail (-x) y‖ ≤
      ((Complex.digamma (y + 1 : ℝ)).re + Real.eulerMascheroniConstant) / y := by
    rw [positiveTail_eq_shift hy]
    apply tsum_of_norm_bounded (hasSum_harmonic_plus hy)
    intro n
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / (((n : ℝ) + 1) * ((n : ℝ) + 1 + y))), norm_expMode, mul_one]
  unfold secondTailAbsolute
  convert add_le_add hn hp using 1
  ring

/-- Away from integers the actual endpoint tails satisfy the literal source Z₀+Z₁ estimate. -/
theorem second_tail_source_bound {M : ℕ} {x y : ℝ} (hy : 0 < y)
    (hM : y < (M : ℝ) + 1) (hx : ∀ k : ℤ, x ≠ (k : ℝ)) :
    ‖negativeTail M x y‖ + ‖positiveTail (-x) y‖ ≤ secondTailSource M x y := by
  rw [norm_positiveTail_neg]
  have h := add_le_add (norm_negativeTail_le_source hy hM hx) (norm_positiveTail_le_source hy hx)
  apply h.trans_eq
  unfold secondTailSource
  ring

/-- The completed explicit endpoint majorant covers every real endpoint. -/
theorem second_tail_majorant_bound {M : ℕ} {y : ℝ} (hy : 0 < y)
    (hM : y < (M : ℝ) + 1) (x : ℝ) :
    ‖negativeTail M x y‖ + ‖positiveTail (-x) y‖ ≤ secondTailMajorant M x y := by
  classical
  unfold secondTailMajorant
  split_ifs with hx
  · exact second_tail_absolute_bound hy hM x
  · exact second_tail_source_bound hy hM (not_exists.mp hx)

/-- The explicit second-order bound keeps the separately proved square coefficients visible. -/
noncomputable def secondPoissonError (f g : ℝ → ℝ) (a b : ℝ) : ℝ :=
  let M := ⌊deriv f a⌋₊
  (g b * poissonEndpointMajorant b (deriv f a) + g a * poissonEndpointMajorant a (deriv f a)) /
    (2 * Real.pi) + ‖poissonBoundary f g a b‖ +
  (secondH f g b * secondTailMajorant M b (deriv f b) +
    secondH f g a * secondTailMajorant M a (deriv f a)) / (4 * Real.pi ^ 2) +
  secondH1 f g a / (4 * Real.pi ^ 3) * (minusSquareBound M (deriv f a) + plusSquareBound (deriv f a)) +
  (secondH f g a * |deriv (deriv f) a| / (4 * Real.pi ^ 3)) *
    (minusCubeBound M (deriv f a) + plusCubeBound (deriv f a))

/-- The repaired general analytic inputs yield the full explicit bound at all real endpoints. -/
theorem SecondOrderRegularity.explicit_poisson_bound {f g : ℝ → ℝ} {a b : ℝ}
    (r : SecondOrderRegularity f g a b) :
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, weightedWave f g (n : ℝ)) -
      poissonMain f g a b ⌊deriv f a⌋₊‖ ≤ secondPoissonError f g a b := by
  have ha := Set.left_mem_Icc.mpr r.lt.le
  have hb := Set.right_mem_Icc.mpr r.lt.le
  have hM := Nat.lt_floor_add_one (deriv f a)
  have hea := mul_le_mul_of_nonneg_left (second_tail_majorant_bound (r.f_deriv_pos a ha) hM a)
    (div_nonneg (secondH_nonneg f g a) (by positivity : 0 ≤ 4 * Real.pi ^ 2))
  have heb := mul_le_mul_of_nonneg_left (second_tail_majorant_bound (r.f_deriv_pos b hb)
    ((r.f_deriv_antitone ha hb r.lt.le).trans_lt hM) b)
    (div_nonneg (secondH_nonneg f g b) (by positivity : 0 ≤ 4 * Real.pi ^ 2))
  have hha := norm_poissonHeadBoundary_le (f := f) (y := deriv f a) (r.g_nonneg a ha)
  have hhb := norm_poissonHeadBoundary_le (f := f) (y := deriv f a) (r.g_nonneg b hb)
  have ht := r.finite_poisson_bound
  dsimp only [secondPoissonError] at ht ⊢
  simp only [div_eq_mul_inv] at ht hea heb hha hhb ⊢
  nlinarith only [ht, hea, heb, hha, hhb]


/-- Every permitted lower frequency is restored in the actual sum and Fourier integrals. -/
theorem second_poisson_shifted_bound {f g : ℝ → ℝ} {a b : ℝ} {N : ℕ}
    (h : PartIRegularityAt f g a b N)
    (r : SecondOrderRegularity (phaseShift f N) g a b) :
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, weightedWave f g (n : ℝ)) -
      ∑ ν ∈ Finset.Icc N ⌊deriv f a⌋₊,
        ∫ u in a..b, (g u : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))‖ ≤
      secondPoissonError (phaseShift f N) g a b := by
  have ht := r.explicit_poisson_bound
  rw [weighted_sum_phaseShift, poissonMain_phaseShift h] at ht
  exact ht

/-- The explicit general bound packages the separately derived square terms into the proposed coefficient; scope adoption remains separate. -/
theorem secondPoissonError_eq_envelope {f g : ℝ → ℝ} {a b : ℝ} (hy : 0 < deriv f a) :
    secondPoissonError f g a b =
      (g b * poissonEndpointMajorant b (deriv f a) + g a * poissonEndpointMajorant a (deriv f a)) /
        (2 * Real.pi) + ‖poissonBoundary f g a b‖ +
      (secondH f g b * secondTailMajorant ⌊deriv f a⌋₊ b (deriv f b) +
        secondH f g a * secondTailMajorant ⌊deriv f a⌋₊ a (deriv f a)) / (4 * Real.pi ^ 2) +
      (secondH1 f g a * partIISquareTailEnvelope (deriv f a) +
        secondH f g a * |deriv (deriv f) a| * partIICubeCoefficient (deriv f a)) /
          (4 * Real.pi ^ 3 * deriv f a) := by
  dsimp only [secondPoissonError]
  rw [squareBounds_eq_proposed_envelope hy, cubeBounds_eq_source_coefficient hy]
  ring

/-- The general second-order argument has the literal half-integer endpoint simplification for δ≥1/2. -/
theorem SecondOrderRegularity.half_integer_bound {f g : ℝ → ℝ} {a b : ℝ}
    (r : SecondOrderRegularity f g a b)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2)
    (hδ : 1 / 2 ≤ (⌊deriv f a⌋₊ : ℝ) + 1 - deriv f a) :
    let M : ℕ := ⌊deriv f a⌋₊
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, weightedWave f g (n : ℝ)) - poissonMain f g a b M‖ ≤
      ((g a + g b) / (2 * Real.pi)) * (Real.log 2 + 1 / deriv f a) +
      secondH f g b / (4 * Real.pi ^ 2) * halfSecondEndpointBound M (deriv f b) +
      secondH f g a / (4 * Real.pi ^ 2) * halfSecondEndpointBound M (deriv f a) +
      secondH1 f g a / (4 * Real.pi ^ 3) *
        (minusSquareBound M (deriv f a) + plusSquareBound (deriv f a)) +
      (secondH f g a * |deriv (deriv f) a| / (4 * Real.pi ^ 3)) *
        (minusCubeBound M (deriv f a) + plusCubeBound (deriv f a)) := by
  dsimp only
  have ha := Set.left_mem_Icc.mpr r.lt.le
  have hb := Set.right_mem_Icc.mpr r.lt.le
  have hya := r.f_deriv_pos a ha
  have hyb := r.f_deriv_pos b hb
  have hba := r.f_deriv_antitone ha hb r.lt.le
  have hδb : 1 / 2 ≤ (⌊deriv f a⌋₊ : ℝ) + 1 - deriv f b := by linarith
  have heb := mul_le_mul_of_nonneg_left (second_endpoint_half_integer_bound hbh hyb hδb)
    (div_nonneg (secondH_nonneg f g b) (by positivity : 0 ≤ 4 * Real.pi ^ 2))
  have hea := mul_le_mul_of_nonneg_left (second_endpoint_half_integer_bound hah hya hδ)
    (div_nonneg (secondH_nonneg f g a) (by positivity : 0 ≤ 4 * Real.pi ^ 2))
  have hha := norm_poissonHeadBoundary_half_integer_le (f := f) hah (r.g_nonneg a ha) hya
  have hhb := norm_poissonHeadBoundary_half_integer_le (f := f) hbh (r.g_nonneg b hb) hya
  have hg : poissonBoundary f g a b = 0 := by
    obtain ⟨k, rfl⟩ := hah
    obtain ⟨l, rfl⟩ := hbh
    exact poissonBoundary_half_integer _ _ k l
  have ht := r.finite_poisson_bound
  dsimp only at ht
  rw [hg, norm_zero, add_zero] at ht
  simp only [div_eq_mul_inv] at ht hea heb hha hhb ⊢
  nlinarith only [ht, hea, heb, hha, hhb]

/-- The half-integer second-order estimate transports the actual main sum to every allowed lower frequency. -/
theorem second_poisson_shifted_half {f g : ℝ → ℝ} {a b : ℝ} {N : ℕ}
    (h : PartIRegularityAt f g a b N)
    (r : SecondOrderRegularity (phaseShift f N) g a b)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2)
    (hδ : 1 / 2 ≤ 1 - Int.fract (deriv f a)) :
    let F := phaseShift f N
    let y := deriv f a - N
    let M := ⌊deriv f a⌋₊ - N
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, weightedWave f g (n : ℝ)) -
      ∑ ν ∈ Finset.Icc N ⌊deriv f a⌋₊,
        ∫ u in a..b, (g u : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))‖ ≤
      ((g a + g b) / (2 * Real.pi)) * (Real.log 2 + 1 / y) +
      secondH F g b / (4 * Real.pi ^ 2) * halfSecondEndpointBound M (deriv f b - N) +
      secondH F g a / (4 * Real.pi ^ 2) * halfSecondEndpointBound M y +
      secondH1 F g a / (4 * Real.pi ^ 3) * (minusSquareBound M y + plusSquareBound y) +
      (secondH F g a * |deriv (deriv F) a| / (4 * Real.pi ^ 3)) *
        (minusCubeBound M y + plusCubeBound y) := by
  have ha := Set.left_mem_Icc.mpr h.lt.le
  have hb := Set.right_mem_Icc.mpr h.lt.le
  have hd := deriv_phaseShift N (h.f_differentiable a ha)
  have hdb := deriv_phaseShift N (h.f_differentiable b hb)
  have hδ' : 1 / 2 ≤ (⌊deriv (phaseShift f N) a⌋₊ : ℝ) + 1 - deriv (phaseShift f N) a := by
    rw [hd, Nat.floor_sub_natCast, shifted_floor_delta (h.deriv_gt ha).le]
    exact hδ
  have ht := r.half_integer_bound hah hbh hδ'
  dsimp only at ht ⊢
  rw [weighted_sum_phaseShift, poissonMain_phaseShift h] at ht
  simpa only [hd, hdb, Nat.floor_sub_natCast] using ht

end DhimanKadiriQuesadaHerrera2026

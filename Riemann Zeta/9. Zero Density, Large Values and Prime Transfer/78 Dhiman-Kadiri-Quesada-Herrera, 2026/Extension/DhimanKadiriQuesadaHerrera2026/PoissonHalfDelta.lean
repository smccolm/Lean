import DhimanKadiriQuesadaHerrera2026.BProcessPoisson

namespace DhimanKadiriQuesadaHerrera2026

/-- The exact digamma endpoint replacement for the half-integer bound at every positive frequency gap. -/
noncomputable def halfSecondEndpointDelta (M : ℕ) (y : ℝ) : ℝ :=
  let δ := (M : ℝ) + 1 - y
  (1 / y) * (|(Complex.digamma (δ : ℂ)).re -
    (Complex.digamma (((δ + 1) / 2 : ℝ) : ℂ)).re - Real.log 2| +
      1 / ((M : ℝ) + 1) + Real.log 2 + 3 / (2 * (y + 1)))

/-- The complete endpoint-tail pair retains its δ dependence instead of assuming δ≥1/2. -/
theorem second_endpoint_half_integer_delta {M : ℕ} {x y : ℝ}
    (hx : ∃ k : ℤ, x = (k : ℝ) + 1 / 2) (hy : 0 < y) (hM : y < (M : ℝ) + 1) :
    ‖negativeTail M x y‖ + ‖positiveTail (-x) y‖ ≤ halfSecondEndpointDelta M y := by
  rw [norm_positiveTail_neg]
  obtain ⟨k, rfl⟩ := hx
  have h := add_le_add (norm_negativeTail_half_integer_le k hy hM)
    (norm_positiveTail_half_integer_le k hy)
  apply h.trans_eq
  unfold halfSecondEndpointDelta
  dsimp only
  have hy1 : y + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- The source pi/2 expression is recovered on the domain where its digamma bound applies. -/
theorem halfSecondEndpointDelta_le_pi {M : ℕ} {y : ℝ} (hy : 0 < y)
    (hδ : 1 / 2 ≤ (M : ℝ) + 1 - y) :
    halfSecondEndpointDelta M y ≤ halfSecondEndpointBound M y := by
  unfold halfSecondEndpointDelta halfSecondEndpointBound
  dsimp only
  exact mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add (add_le_add (digamma_half_integer_tail_bound hδ) le_rfl) le_rfl) le_rfl)
    (by positivity)

/-- The actual weighted second-order Poisson bound at half-integer endpoints retains the full positive δ domain. -/
theorem SecondOrderRegularity.half_integer_delta_bound {f g : ℝ → ℝ} {a b : ℝ}
    (r : SecondOrderRegularity f g a b)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2)
    :
    let M : ℕ := ⌊deriv f a⌋₊
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, weightedWave f g (n : ℝ)) - poissonMain f g a b M‖ ≤
      ((g a + g b) / (2 * Real.pi)) * (Real.log 2 + 1 / deriv f a) +
      secondH f g b / (4 * Real.pi ^ 2) * halfSecondEndpointDelta M (deriv f b) +
      secondH f g a / (4 * Real.pi ^ 2) * halfSecondEndpointDelta M (deriv f a) +
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
  have hM := Nat.lt_floor_add_one (deriv f a)
  have hMb := hba.trans_lt hM
  have heb := mul_le_mul_of_nonneg_left (second_endpoint_half_integer_delta hbh hyb hMb)
    (div_nonneg (secondH_nonneg f g b) (by positivity : 0 ≤ 4 * Real.pi ^ 2))
  have hea := mul_le_mul_of_nonneg_left (second_endpoint_half_integer_delta hah hya hM)
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
theorem second_poisson_shifted_delta {f g : ℝ → ℝ} {a b : ℝ} {N : ℕ}
    (h : PartIRegularityAt f g a b N)
    (r : SecondOrderRegularity (phaseShift f N) g a b)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2)
    :
    let F := phaseShift f N
    let y := deriv f a - N
    let M := ⌊deriv f a⌋₊ - N
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, weightedWave f g (n : ℝ)) -
      ∑ ν ∈ Finset.Icc N ⌊deriv f a⌋₊,
        ∫ u in a..b, (g u : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))‖ ≤
      ((g a + g b) / (2 * Real.pi)) * (Real.log 2 + 1 / y) +
      secondH F g b / (4 * Real.pi ^ 2) * halfSecondEndpointDelta M (deriv f b - N) +
      secondH F g a / (4 * Real.pi ^ 2) * halfSecondEndpointDelta M y +
      secondH1 F g a / (4 * Real.pi ^ 3) * (minusSquareBound M y + plusSquareBound y) +
      (secondH F g a * |deriv (deriv F) a| / (4 * Real.pi ^ 3)) *
        (minusCubeBound M y + plusCubeBound y) := by
  have ha := Set.left_mem_Icc.mpr h.lt.le
  have hb := Set.right_mem_Icc.mpr h.lt.le
  have hd := deriv_phaseShift N (h.f_differentiable a ha)
  have hdb := deriv_phaseShift N (h.f_differentiable b hb)
  have ht := r.half_integer_delta_bound hah hbh
  dsimp only at ht ⊢
  rw [weighted_sum_phaseShift, poissonMain_phaseShift h] at ht
  simpa only [hd, hdb, Nat.floor_sub_natCast] using ht

/-- The constant-weight specialization retains the complete separately proved square and cube terms. -/
theorem constant_second_poisson_delta {f : ℝ → ℝ} {a b : ℝ}
    (r : SecondOrderRegularity f (fun _ => 1) a b)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2)
    :
    let y := deriv f a
    let M := ⌊y⌋₊
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 0 M, ∫ u in a..b,
        Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))‖ ≤
      (Real.log 2 + 1 / y) / Real.pi +
      (deriv f b * halfSecondEndpointDelta M (deriv f b) + y * halfSecondEndpointDelta M y) /
        (2 * Real.pi) +
      |deriv (deriv f) a| / (2 * Real.pi ^ 2) * (minusSquareBound M y + plusSquareBound y) +
      (y * |deriv (deriv f) a| / (2 * Real.pi ^ 2)) * (minusCubeBound M y + plusCubeBound y) := by
  have h := r.half_integer_delta_bound hah hbh
  dsimp only at h ⊢
  rw [secondH_constant (r.f_deriv_pos a (Set.left_mem_Icc.mpr r.lt.le)).le,
    secondH_constant (r.f_deriv_pos b (Set.right_mem_Icc.mpr r.lt.le)).le,
    secondH1_constant] at h
  simp only [weightedWave, poissonMain_eq_source, Complex.ofReal_one, one_mul] at h
  apply h.trans_eq
  field_simp
  ring


/-- The actual discrete B-process with the proved second-order coefficients, conditional on the explicit repaired analytic regularity, with all positive frequency gaps. -/
theorem exists_b_process_delta {f : ℝ → ℝ} {a b ℓ₂ ℓ₃ h₂ h₃ : ℝ}
    (r : SecondOrderRegularity f (fun _ => 1) a b)
    (hℓ₂ : 0 < ℓ₂) (hℓ₃ : 0 ≤ ℓ₃) (hh₃ : 0 ≤ h₃) (hα : deriv f b < 1)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b))
    (hlower : ∀ u ∈ Set.Icc a b, ℓ₂ ≤ |deriv (deriv f) u|)
    (hupper : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ h₂ * ℓ₂)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ h₃ * ℓ₃) :
    ∃ ξ : ℕ → ℝ, (∀ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
      ξ ν ∈ Set.Icc a b ∧ deriv f (ξ ν) = (ν : ℝ)) ∧
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
        Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ ≤
      2.686 / Real.sqrt ℓ₂ +
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * h₃ ^ (1 / 3 : ℝ) * (b - a) * ℓ₃ ^ (1 / 3 : ℝ) +
        2 / Real.pi * Real.log (deriv f a - deriv f b) + 1.251 +
      ((Real.log 2 + 1 / (deriv f a)) / Real.pi +
      (deriv f b * halfSecondEndpointDelta ⌊deriv f a⌋₊ (deriv f b) + (deriv f a) * halfSecondEndpointDelta ⌊deriv f a⌋₊ (deriv f a)) /
        (2 * Real.pi) +
      |deriv (deriv f) a| / (2 * Real.pi ^ 2) * (minusSquareBound ⌊deriv f a⌋₊ (deriv f a) + plusSquareBound (deriv f a)) +
      (deriv f a * |deriv (deriv f) a| / (2 * Real.pi ^ 2)) * (minusCubeBound ⌊deriv f a⌋₊ (deriv f a) + plusCubeBound (deriv f a))) := by
  have hab := r.lt
  have hf := r.f_differentiable
  have hf' := r.f_deriv_differentiable
  have hαpos := r.f_deriv_pos b (Set.right_mem_Icc.mpr hab.le)
  obtain ⟨ξ, hξ, hs⟩ := exists_source_stationary_transform hab hℓ₂ hℓ₃ hh₃ hαpos hα hah hbh
    hf hf' hf'' hanti hlower hupper hD
  have hp := constant_second_poisson_delta r hah hbh
  dsimp only at hp
  refine ⟨ξ, hξ, ?_⟩
  have ht := (norm_add_le _ _).trans (add_le_add hp hs)
  simpa only [sub_add_sub_cancel, add_comm] using ht


end DhimanKadiriQuesadaHerrera2026

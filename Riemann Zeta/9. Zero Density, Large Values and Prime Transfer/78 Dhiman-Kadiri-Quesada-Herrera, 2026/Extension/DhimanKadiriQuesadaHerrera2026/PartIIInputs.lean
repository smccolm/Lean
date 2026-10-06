import DhimanKadiriQuesadaHerrera2026.SecondCoeffBounds

namespace DhimanKadiriQuesadaHerrera2026

/-- Explicit analytic inputs for the general second-order Poisson argument; the explicit adopted source adapter is in CorrectedPartII. -/
structure SecondOrderRegularity (f g : ℝ → ℝ) (a b : ℝ) : Prop extends PartIRegularity f g a b where
  f_deriv_differentiable : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u
  f_second_continuous : ContinuousOn (deriv (deriv f)) (Set.Icc a b)
  g_deriv_differentiable : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv g) u
  g_second_continuous : ContinuousOn (deriv (deriv g)) (Set.Icc a b)
  f_second_abs_antitone : AntitoneOn (fun u => |deriv (deriv f) u|) (Set.Icc a b)
  g_second_abs_antitone : AntitoneOn (fun u => |deriv (deriv g) u|) (Set.Icc a b)
  product_deriv_abs_antitone : AntitoneOn (fun u => |deriv g u * deriv f u + g u * deriv (deriv f) u|) (Set.Icc a b)
  positive_deriv_quotient : ∀ h : ℝ → ℝ, (h = deriv g ∨ h = fun u => g u * deriv f u) →
    ∀ n : ℕ, AntitoneOn (fun u => |deriv h u| / (((n : ℝ) + 1) + deriv f u) ^ 2) (Set.Icc a b)
  positive_curvature_quotient : ∀ h : ℝ → ℝ, (h = deriv g ∨ h = fun u => g u * deriv f u) →
    ∀ n : ℕ, AntitoneOn (fun u => |h u * deriv (deriv f) u| /
      (((n : ℝ) + 1) + deriv f u) ^ 3) (Set.Icc a b)

/-- The two actual amplitudes have the differentiability and continuous derivatives required for integration by parts. -/
theorem SecondOrderRegularity.amplitude_regular {f g : ℝ → ℝ} {a b : ℝ}
    (r : SecondOrderRegularity f g a b) (h : ℝ → ℝ)
    (hh : h = deriv g ∨ h = fun u => g u * deriv f u) :
    (∀ u ∈ Set.Icc a b, DifferentiableAt ℝ h u) ∧ ContinuousOn (deriv h) (Set.Icc a b) := by
  rcases hh with rfl | rfl
  · exact ⟨r.g_deriv_differentiable, r.g_second_continuous⟩
  · refine ⟨fun u hu => (r.g_differentiable u hu).mul (r.f_deriv_differentiable u hu), ?_⟩
    have hc : ContinuousOn g (Set.Icc a b) := fun u hu => (r.g_differentiable u hu).continuousAt.continuousWithinAt
    have hd := (r.g_deriv_continuous.mul r.f_deriv_continuous).add (hc.mul r.f_second_continuous)
    apply hd.congr
    intro u hu
    exact ((r.g_differentiable u hu).hasDerivAt.mul (r.f_deriv_differentiable u hu).hasDerivAt).deriv

/-- The absolute values of both actual amplitudes are nonincreasing. -/
theorem SecondOrderRegularity.amplitude_abs_antitone {f g : ℝ → ℝ} {a b : ℝ}
    (r : SecondOrderRegularity f g a b) (h : ℝ → ℝ)
    (hh : h = deriv g ∨ h = fun u => g u * deriv f u) : AntitoneOn (fun u => |h u|) (Set.Icc a b) := by
  rcases hh with rfl | rfl
  · exact r.g_abs_deriv_antitone
  · intro u hu v hv huv
    dsimp only
    rw [abs_of_nonneg (mul_nonneg (r.g_nonneg u hu) (r.f_deriv_pos u hu).le),
      abs_of_nonneg (mul_nonneg (r.g_nonneg v hv) (r.f_deriv_pos v hv).le)]
    exact mul_le_mul (r.g_antitone hu hv huv) (r.f_deriv_antitone hu hv huv)
      (r.f_deriv_pos v hv).le (r.g_nonneg u hu)

/-- The absolute derivatives of both amplitudes have the required monotonicity. -/
theorem SecondOrderRegularity.amplitude_deriv_abs_antitone {f g : ℝ → ℝ} {a b : ℝ}
    (r : SecondOrderRegularity f g a b) (h : ℝ → ℝ)
    (hh : h = deriv g ∨ h = fun u => g u * deriv f u) : AntitoneOn (fun u => |deriv h u|) (Set.Icc a b) := by
  rcases hh with rfl | rfl
  · exact r.g_second_abs_antitone
  · intro u hu v hv huv
    change |deriv (g * deriv f) v| ≤ |deriv (g * deriv f) u|
    rw [((r.g_differentiable u hu).hasDerivAt.mul (r.f_deriv_differentiable u hu).hasDerivAt).deriv,
      ((r.g_differentiable v hv).hasDerivAt.mul (r.f_deriv_differentiable v hv).hasDerivAt).deriv]
    exact r.product_deriv_abs_antitone hu hv huv

/-- Explicit general analytic inputs prove convergence and the complete positive-mode estimate for each actual amplitude. -/
theorem SecondOrderRegularity.positive_tail {f g : ℝ → ℝ} {a b : ℝ}
    (r : SecondOrderRegularity f g a b) (h : ℝ → ℝ)
    (hh : h = deriv g ∨ h = fun u => g u * deriv f u) :
    Summable (secondModeTerm f h a b) ∧
      ‖∑' n : ℕ, secondModeTerm f h a b n‖ ≤ positiveModeError (deriv f) (deriv (deriv f)) h (deriv h) a b := by
  have hr := r.amplitude_regular h hh
  have hf u hu := (r.f_differentiable u hu).hasDerivAt
  have hp u hu := (r.f_deriv_differentiable u hu).hasDerivAt
  have hd u hu := (hr.1 u hu).hasDerivAt
  refine ⟨(secondModeTail_bound r.lt hf hp hd r.f_deriv_continuous r.f_second_continuous hr.2
    r.f_deriv_pos (r.positive_deriv_quotient h hh) (r.positive_curvature_quotient h hh)).1, ?_⟩
  exact secondModeTail_source_bound r.lt hf hp hd r.f_deriv_continuous r.f_second_continuous hr.2
    r.f_deriv_pos (r.positive_deriv_quotient h hh) (r.positive_curvature_quotient h hh)

/-- Explicit general analytic inputs prove convergence and the complete upper-mode estimate for each actual amplitude. -/
theorem SecondOrderRegularity.upper_tail {f g : ℝ → ℝ} {a b : ℝ}
    (r : SecondOrderRegularity f g a b) (h : ℝ → ℝ)
    (hh : h = deriv g ∨ h = fun u => g u * deriv f u) {M : ℕ} (hM : deriv f a < (M : ℝ) + 1) :
    Summable (upperModeTerm f h a b M) ∧
      ‖∑' n : ℕ, upperModeTerm f h a b M n‖ ≤ negativeModeError (deriv f) (deriv (deriv f)) h (deriv h) a b M := by
  have hr := r.amplitude_regular h hh
  have hf u hu := (r.f_differentiable u hu).hasDerivAt
  have hp u hu := (r.f_deriv_differentiable u hu).hasDerivAt
  have hd u hu := (hr.1 u hu).hasDerivAt
  refine ⟨(upperModeTail_bound r.lt hf hp hd r.f_deriv_continuous r.f_second_continuous hr.2
    r.f_deriv_antitone (r.amplitude_abs_antitone h hh) (r.amplitude_deriv_abs_antitone h hh)
      r.f_second_abs_antitone r.f_deriv_pos hM).1, ?_⟩
  exact upperModeTail_source_bound r.lt hf hp hd r.f_deriv_continuous r.f_second_continuous hr.2
    r.f_deriv_antitone (r.amplitude_abs_antitone h hh) (r.amplitude_deriv_abs_antitone h hh)
      r.f_second_abs_antitone r.f_deriv_pos hM

/-- The general analytic inputs imply the complete positive coefficient estimate. -/
theorem SecondOrderRegularity.positive_coefficient_bound {f g : ℝ → ℝ} {a b : ℝ}
    (r : SecondOrderRegularity f g a b) :
    ‖∑' n : ℕ, positiveCoefficient f g a b n‖ ≤
      secondH f g b / (4 * Real.pi ^ 2) * ‖positiveTail (-b) (deriv f b)‖ +
      secondH f g a / (4 * Real.pi ^ 2) * ‖positiveTail (-a) (deriv f a)‖ +
      secondH1 f g a / (4 * Real.pi ^ 3) * plusSquareBound (deriv f a) +
      (secondH f g a * |deriv (deriv f) a| / (4 * Real.pi ^ 3)) * plusCubeBound (deriv f a) := by
  have hg := r.positive_tail (deriv g) (Or.inl rfl)
  have hgf := r.positive_tail (fun u => g u * deriv f u) (Or.inr rfl)
  exact norm_positiveCoefficient_le_mode_errors r.toPartIRegularity hg.1 hgf.1 hg.2 hgf.2
    (r.f_deriv_differentiable a (Set.left_mem_Icc.mpr r.lt.le))


/-- The general analytic inputs imply the complete negative coefficient estimate. -/
theorem SecondOrderRegularity.negative_coefficient_bound {f g : ℝ → ℝ} {a b : ℝ}
    (r : SecondOrderRegularity f g a b) (M : ℕ) (hM : deriv f a < (M : ℝ) + 1) :
    ‖∑' n : ℕ, negativeCoefficient f g a b (n + M + 1)‖ ≤
      secondH f g b / (4 * Real.pi ^ 2) * ‖negativeTail M b (deriv f b)‖ +
      secondH f g a / (4 * Real.pi ^ 2) * ‖negativeTail M a (deriv f a)‖ +
      secondH1 f g a / (4 * Real.pi ^ 3) * minusSquareBound M (deriv f a) +
      (secondH f g a * |deriv (deriv f) a| / (4 * Real.pi ^ 3)) * minusCubeBound M (deriv f a) := by
  have hg := r.upper_tail (deriv g) (Or.inl rfl) hM
  have hgf := r.upper_tail (fun u => g u * deriv f u) (Or.inr rfl) hM
  exact norm_negativeCoefficient_le_mode_errors r.toPartIRegularity M hM hg.1 hgf.1 hg.2 hgf.2
    (r.f_deriv_differentiable a (Set.left_mem_Icc.mpr r.lt.le))


/-- The actual general finite Poisson remainder has the complete second-order bound, with the two square coefficients kept separate. -/
theorem SecondOrderRegularity.finite_poisson_bound {f g : ℝ → ℝ} {a b : ℝ}
    (r : SecondOrderRegularity f g a b) :
    let M : ℕ := ⌊deriv f a⌋₊
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, weightedWave f g (n : ℝ)) - poissonMain f g a b M‖ ≤
      ‖poissonHeadBoundary f g b M‖ + ‖poissonHeadBoundary f g a M‖ + ‖poissonBoundary f g a b‖ +
      secondH f g b / (4 * Real.pi ^ 2) *
        (‖negativeTail M b (deriv f b)‖ + ‖positiveTail (-b) (deriv f b)‖) +
      secondH f g a / (4 * Real.pi ^ 2) *
        (‖negativeTail M a (deriv f a)‖ + ‖positiveTail (-a) (deriv f a)‖) +
      secondH1 f g a / (4 * Real.pi ^ 3) *
        (minusSquareBound M (deriv f a) + plusSquareBound (deriv f a)) +
      (secondH f g a * (|deriv (deriv f) a|) / (4 * Real.pi ^ 3)) *
        (minusCubeBound M (deriv f a) + plusCubeBound (deriv f a)) := by
  dsimp only
  have hp := r.positive_coefficient_bound
  have hn := r.negative_coefficient_bound ⌊deriv f a⌋₊ (Nat.lt_floor_add_one (deriv f a))
  have hs (A B N P G : ℂ) : ‖A - B + N - P + G‖ ≤ ‖A‖ + ‖B‖ + ‖N‖ + ‖P‖ + ‖G‖ := by
    have h1 := norm_sub_le A B
    have h2 := norm_add_le (A - B) N
    have h3 := norm_sub_le (A - B + N) P
    have h4 := norm_add_le (A - B + N - P) G
    linarith
  rw [weighted_sum_eq_poissonMain_add_remainder r.toPartIRegularity]
  apply (hs _ _ _ _ _).trans
  simp only [div_eq_mul_inv] at hp hn ⊢
  nlinarith only [hp, hn]


/-- The actual AFE phase and weight satisfy every general second-order analytic input, including σ=0. -/
theorem afe_secondOrderRegularity {σ c a b : ℝ} (hσ : 0 ≤ σ) (hc : 0 < c)
    (ha : 0 < a) (hab : a < b) : SecondOrderRegularity (afePhase c) (afeWeight σ) a b := by
  have hpos (u : ℝ) (hu : u ∈ Set.Icc a b) : 0 < u := ha.trans_le hu.1
  have hsub : Set.Icc a b ⊆ Set.Ioi 0 := fun u hu => hpos u hu
  have hw := afe_second_amplitude_regular σ c (deriv (afeWeight σ)) (Or.inl rfl)
  have hd := afe_second_derivatives_antitone hσ hc.le
  refine { toPartIRegularity := afe_partIRegularity hσ hc ha hab
           f_deriv_differentiable := fun u hu => (afePhase_deriv_hasDerivAt c (hpos u hu)).differentiableAt
           f_second_continuous := ?_
           g_deriv_differentiable := fun u hu => hw.1 u (hpos u hu)
           g_second_continuous := hw.2.mono hsub
           f_second_abs_antitone := hd.2.1.mono hsub
           g_second_abs_antitone := (afe_second_amplitudes_antitone hσ hc.le
             (deriv (afeWeight σ)) (Or.inl rfl)).2.mono hsub
           product_deriv_abs_antitone := ?_
           positive_deriv_quotient := ?_
           positive_curvature_quotient := ?_ }
  · have hcont : ContinuousOn (fun u : ℝ => -c / u ^ 2) (Set.Icc a b) :=
      continuousOn_const.div (continuousOn_id.pow 2) (fun u hu => pow_ne_zero _ (hpos u hu).ne')
    exact hcont.congr (fun u hu => (afePhase_deriv_hasDerivAt c (hpos u hu)).deriv)
  · intro u hu v hv huv
    have he (w : ℝ) (hw : 0 < w) :
        deriv (fun z => afeWeight σ z * deriv (afePhase c) z) w =
          deriv (afeWeight σ) w * deriv (afePhase c) w +
            afeWeight σ w * deriv (deriv (afePhase c)) w :=
      ((afeWeight_hasDerivAt σ hw).differentiableAt.hasDerivAt.mul
        (afePhase_deriv_hasDerivAt c hw).differentiableAt.hasDerivAt).deriv
    have h := hd.2.2 (hpos u hu) (hpos v hv) huv
    simpa only [he u (hpos u hu), he v (hpos v hv)] using h
  · intro h hh n
    have hq := afe_second_quotients_antitone hσ hc.le (show 0 < (n : ℝ) + 1 by positivity)
    rcases hh with rfl | rfl
    · exact hq.1.mono hsub
    · exact hq.2.2.1.mono hsub
  · intro h hh n
    have hq := afe_second_quotients_antitone hσ hc.le (show 0 < (n : ℝ) + 1 by positivity)
    rcases hh with rfl | rfl
    · exact hq.2.1.mono hsub
    · exact hq.2.2.2.mono hsub

end DhimanKadiriQuesadaHerrera2026

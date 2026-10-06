import DhimanKadiriQuesadaHerrera2026.PartIIBounds

namespace DhimanKadiriQuesadaHerrera2026
open Filter
open scoped Topology

/-- Nonzero first derivative supplies the local differentiability needed to differentiate the shifted derivative. -/
theorem hasDerivAt_deriv_phaseShift {f : ℝ → ℝ} {x : ℝ} (N : ℕ)
    (hf : DifferentiableAt ℝ (deriv f) x) (hfn : deriv f x ≠ 0) :
    HasDerivAt (deriv (phaseShift f N)) (deriv (deriv f) x) x := by
  have he : ∀ᶠ u in 𝓝 x, deriv f u ≠ 0 := hf.continuousAt.eventually_ne hfn
  apply (hf.hasDerivAt.sub_const (N : ℝ)).congr_of_eventuallyEq
  filter_upwards [he] with u hu
  exact deriv_phaseShift N (differentiableAt_of_deriv_ne_zero hu)

/-- The curvature is unchanged by the actual integer-frequency shift, including interval endpoints. -/
theorem deriv_deriv_phaseShift {f : ℝ → ℝ} {x : ℝ} (N : ℕ)
    (hf : DifferentiableAt ℝ (deriv f) x) (hfn : deriv f x ≠ 0) :
    deriv (deriv (phaseShift f N)) x = deriv (deriv f) x :=
  (hasDerivAt_deriv_phaseShift N hf hfn).deriv

/-- A nonincreasing differentiable function has nonpositive derivative even at closed-interval endpoints. -/
theorem deriv_nonpos_of_antitone_Icc {F : ℝ → ℝ} {a b x : ℝ} (hab : a < b)
    (hm : AntitoneOn F (Set.Icc a b)) (hx : x ∈ Set.Icc a b) (hd : DifferentiableAt ℝ F x) :
    deriv F x ≤ 0 := by
  have h := hm.derivWithin_nonpos (x := x)
  rw [hd.derivWithin ((uniqueDiffOn_Icc hab).uniqueDiffWithinAt hx)] at h
  exact h

/-- The product-derivative absolute value is nonincreasing after every allowed frequency shift. -/
theorem PartIRegularityAt.shifted_product_antitone {f g : ℝ → ℝ} {a b : ℝ} {N : ℕ}
    (r : PartIRegularityAt f g a b N)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hc : AntitoneOn (fun u => |deriv (deriv f) u|) (Set.Icc a b)) :
    AntitoneOn (fun u => |deriv g u * (deriv f u - N) + g u * deriv (deriv f) u|) (Set.Icc a b) := by
  have hg (u : ℝ) (hu : u ∈ Set.Icc a b) : deriv g u ≤ 0 :=
    deriv_nonpos_of_antitone_Icc r.lt r.g_antitone hu (r.g_differentiable u hu)
  have hff (u : ℝ) (hu : u ∈ Set.Icc a b) : deriv (deriv f) u ≤ 0 :=
    deriv_nonpos_of_antitone_Icc r.lt r.f_deriv_antitone hu (hf u hu)
  have he (u : ℝ) (hu : u ∈ Set.Icc a b) :
      |deriv g u * (deriv f u - N) + g u * deriv (deriv f) u| =
        |deriv g u| * (deriv f u - N) + g u * |deriv (deriv f) u| := by
    have hh := add_nonpos (mul_nonpos_of_nonpos_of_nonneg (hg u hu) (sub_pos.mpr (r.deriv_gt hu)).le)
      (mul_nonpos_of_nonneg_of_nonpos (r.g_nonneg u hu) (hff u hu))
    rw [abs_of_nonpos hh, abs_of_nonpos (hg u hu), abs_of_nonpos (hff u hu)]
    ring
  intro u hu v hv huv
  dsimp only
  rw [he u hu, he v hv]
  apply add_le_add
  · exact mul_le_mul (r.g_abs_deriv_antitone hu hv huv)
      (sub_le_sub_right (r.f_deriv_antitone hu hv huv) _) (sub_pos.mpr (r.deriv_gt hv)).le (abs_nonneg _)
  · exact mul_le_mul (r.g_antitone hu hv huv) (hc hu hv huv) (abs_nonneg _) (r.g_nonneg u hu)

/-- The derivative of the shifted product amplitude agrees with its explicit source formula. -/
theorem deriv_shifted_product_eq {f g : ℝ → ℝ} {x : ℝ} (N : ℕ)
    (hf : DifferentiableAt ℝ (deriv f) x) (hfn : deriv f x ≠ 0) (hg : DifferentiableAt ℝ g x) :
    deriv (fun u => g u * deriv (phaseShift f N) u) x =
      deriv (fun u => g u * (deriv f u - N)) x := by
  change deriv (g * deriv (phaseShift f N)) x = deriv (g * fun u => deriv f u - (N : ℝ)) x
  rw [(hg.hasDerivAt.mul (hasDerivAt_deriv_phaseShift N hf hfn)).deriv,
    (hg.hasDerivAt.mul (hf.hasDerivAt.sub_const (N : ℝ))).deriv,
    deriv_phaseShift N (differentiableAt_of_deriv_ne_zero hfn)]


/-- Explicit shifted analytic hypotheses construct the repaired Part-II interface; no remainder estimate is supplied. -/
theorem secondOrderRegularity_shift_of_inputs {f g : ℝ → ℝ} {a b : ℝ} {N : ℕ}
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
        (((n : ℝ) + 1) + deriv f u - N) ^ 3) (Set.Icc a b)) :
    SecondOrderRegularity (phaseShift f N) g a b := by
  have hfn (u : ℝ) (hu : u ∈ Set.Icc a b) : deriv f u ≠ 0 := by
    have hh := r.deriv_gt hu
    have hn := Nat.cast_nonneg (α := ℝ) N
    linarith
  have hd (u : ℝ) (hu : u ∈ Set.Icc a b) := deriv_phaseShift N (r.f_differentiable u hu)
  have hdd (u : ℝ) (hu : u ∈ Set.Icc a b) := deriv_deriv_phaseShift N (hf u hu) (hfn u hu)
  have hamp (u : ℝ) (hu : u ∈ Set.Icc a b) := deriv_shifted_product_eq N (hf u hu) (hfn u hu) (r.g_differentiable u hu)
  refine { toPartIRegularity := r.shift
           f_deriv_differentiable := fun u hu => (hasDerivAt_deriv_phaseShift N (hf u hu) (hfn u hu)).differentiableAt
           f_second_continuous := hfc.congr (fun u hu => hdd u hu)
           g_deriv_differentiable := hg
           g_second_continuous := hgc
           f_second_abs_antitone := ?_
           g_second_abs_antitone := ?_
           product_deriv_abs_antitone := ?_
           positive_deriv_quotient := ?_
           positive_curvature_quotient := ?_ }
  · intro u hu v hv huv
    dsimp only
    rw [hdd u hu, hdd v hv]
    exact hfa hu hv huv
  · intro u hu v hv huv
    dsimp only
    rw [abs_of_nonneg (hgn u hu), abs_of_nonneg (hgn v hv)]
    exact hga hu hv huv
  · intro u hu v hv huv
    dsimp only
    rw [hd u hu, hd v hv, hdd u hu, hdd v hv]
    exact r.shifted_product_antitone hf hfa hu hv huv
  · intro h hh n
    rcases hh with rfl | rfl
    · intro u hu v hv huv
      dsimp only
      rw [hd u hu, hd v hv]
      simpa only [← add_sub_assoc] using hq (deriv g) (Or.inl rfl) n hu hv huv
    · intro u hu v hv huv
      dsimp only
      rw [hd u hu, hd v hv, hamp u hu, hamp v hv]
      simpa only [← add_sub_assoc] using hq (fun u => g u * (deriv f u - N)) (Or.inr rfl) n hu hv huv
  · intro h hh n
    rcases hh with rfl | rfl
    · intro u hu v hv huv
      dsimp only
      rw [hd u hu, hd v hv, hdd u hu, hdd v hv]
      simpa only [← add_sub_assoc] using hc (deriv g) (Or.inl rfl) n hu hv huv
    · intro u hu v hv huv
      dsimp only
      rw [hd u hu, hd v hv, hdd u hu, hdd v hv]
      simpa only [← add_sub_assoc] using hc (fun u => g u * (deriv f u - N)) (Or.inr rfl) n hu hv huv


/-- H retains the frequency shift in every endpoint weight. -/
theorem secondH_phaseShift {f g : ℝ → ℝ} {x : ℝ} (N : ℕ) (hf : DifferentiableAt ℝ f x) :
    secondH (phaseShift f N) g x = |deriv g x| + 2 * Real.pi * |g x * (deriv f x - N)| := by
  rw [secondH, deriv_phaseShift N hf]

/-- H₁ keeps both shifted first-derivative and unchanged curvature terms. -/
theorem secondH1_phaseShift {f g : ℝ → ℝ} {x : ℝ} (N : ℕ)
    (hf : DifferentiableAt ℝ (deriv f) x) (hfn : deriv f x ≠ 0) :
    secondH1 (phaseShift f N) g x = |deriv (deriv g) x| +
      2 * Real.pi * (|g x * deriv (deriv f) x| + |deriv g x * (deriv f x - N)|) := by
  rw [secondH1, deriv_deriv_phaseShift N hf hfn,
    deriv_phaseShift N (differentiableAt_of_deriv_ne_zero hfn)]

/-- The full general-N weighted Poisson inequality follows from explicit shifted analytic inputs. -/
theorem second_poisson_from_shift_inputs {f g : ℝ → ℝ} {a b : ℝ} {N : ℕ}
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
        (((n : ℝ) + 1) + deriv f u - N) ^ 3) (Set.Icc a b)) :
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, weightedWave f g (n : ℝ)) -
      ∑ ν ∈ Finset.Icc N ⌊deriv f a⌋₊,
        ∫ u in a..b, (g u : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))‖ ≤
      secondPoissonError (phaseShift f N) g a b := by
  exact second_poisson_shifted_bound r
    (secondOrderRegularity_shift_of_inputs r hf hfc hg hgc hfa hgn hga hq hc)

/-- The complete half-integer general-N inequality consumes the explicit shifted inputs, retaining every source term. -/
theorem second_poisson_half_from_shift_inputs {f g : ℝ → ℝ} {a b : ℝ} {N : ℕ}
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
  exact second_poisson_shifted_half r
    (secondOrderRegularity_shift_of_inputs r hf hfc hg hgc hfa hgn hga hq hc) hah hbh hδ

end DhimanKadiriQuesadaHerrera2026

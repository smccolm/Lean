import DhimanKadiriQuesadaHerrera2026.PartIIBounds
import DhimanKadiriQuesadaHerrera2026.PoissonCorollary

namespace DhimanKadiriQuesadaHerrera2026

/-- Constant weight satisfies the provisional second-order interface from two explicit phase quotients. -/
theorem constant_secondOrderRegularity {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hfd : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hfc : ContinuousOn (deriv f) (Set.Icc a b)) (hpos : 0 < deriv f b)
    (hfa : AntitoneOn (deriv f) (Set.Icc a b))
    (hfdd : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hfcc : ContinuousOn (deriv (deriv f)) (Set.Icc a b))
    (hanti : AntitoneOn (fun u => |deriv (deriv f) u|) (Set.Icc a b))
    (hq : ∀ n : ℕ, AntitoneOn (fun u => |deriv (deriv f) u| /
      (((n : ℝ) + 1) + deriv f u) ^ 2) (Set.Icc a b))
    (hr : ∀ n : ℕ, AntitoneOn (fun u => |deriv f u * deriv (deriv f) u| /
      (((n : ℝ) + 1) + deriv f u) ^ 3) (Set.Icc a b)) :
    SecondOrderRegularity f (fun _ => 1) a b := by
  have hp := partIRegularityAt_constant (N := 0) hab hfd hfc (by simpa only [Nat.cast_zero] using hpos) hfa
  have hfp (u : ℝ) (hu : u ∈ Set.Icc a b) : 0 < deriv f u := by
    simpa only [Nat.cast_zero] using hp.deriv_gt hu
  refine { toPartIRegularity := constant_weight_partIRegularity hab hfd hfc hfp hfa
           f_deriv_differentiable := hfdd
           f_second_continuous := hfcc
           g_deriv_differentiable := ?_
           g_second_continuous := ?_
           f_second_abs_antitone := hanti
           g_second_abs_antitone := ?_
           product_deriv_abs_antitone := ?_
           positive_deriv_quotient := ?_
           positive_curvature_quotient := ?_ }
  · simp only [deriv_const']
    intro u _
    exact differentiableAt_const 0
  · simp only [deriv_const']
    exact continuousOn_const
  · simp only [deriv_const', abs_zero]
    exact antitoneOn_const
  · simpa only [deriv_const, zero_mul, one_mul, zero_add] using hanti
  · intro h hh n
    rcases hh with rfl | rfl
    · simp only [deriv_const', abs_zero, zero_div]
      exact antitoneOn_const
    · simpa only [one_mul] using hq n
  · intro h hh n
    rcases hh with rfl | rfl
    · simp only [deriv_const, zero_mul, abs_zero, zero_div]
      exact antitoneOn_const
    · simpa only [one_mul] using hr n

/-- The H numerator for constant weight is exactly twice pi times the positive phase derivative. -/
theorem secondH_constant {f : ℝ → ℝ} {u : ℝ} (hf : 0 ≤ deriv f u) :
    secondH f (fun _ => 1) u = 2 * Real.pi * deriv f u := by
  simp only [secondH, deriv_const, abs_zero, zero_add, one_mul, abs_of_nonneg hf]

/-- The H₁ numerator for constant weight contains only the actual curvature. -/
theorem secondH1_constant (f : ℝ → ℝ) (u : ℝ) :
    secondH1 f (fun _ => 1) u = 2 * Real.pi * |deriv (deriv f) u| := by
  simp only [secondH1, deriv_const', abs_zero, zero_add, one_mul, zero_mul, add_zero]

/-- The constant-weight specialization retains the complete separately proved square and cube terms. -/
theorem constant_second_poisson_half {f : ℝ → ℝ} {a b : ℝ}
    (r : SecondOrderRegularity f (fun _ => 1) a b)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2)
    (hδ : 1 / 2 ≤ (⌊deriv f a⌋₊ : ℝ) + 1 - deriv f a) :
    let y := deriv f a
    let M := ⌊y⌋₊
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 0 M, ∫ u in a..b,
        Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))‖ ≤
      (Real.log 2 + 1 / y) / Real.pi +
      (deriv f b * halfSecondEndpointBound M (deriv f b) + y * halfSecondEndpointBound M y) /
        (2 * Real.pi) +
      |deriv (deriv f) a| / (2 * Real.pi ^ 2) * (minusSquareBound M y + plusSquareBound y) +
      (y * |deriv (deriv f) a| / (2 * Real.pi ^ 2)) * (minusCubeBound M y + plusCubeBound y) := by
  have h := r.half_integer_bound hah hbh hδ
  dsimp only at h ⊢
  rw [secondH_constant (r.f_deriv_pos a (Set.left_mem_Icc.mpr r.lt.le)).le,
    secondH_constant (r.f_deriv_pos b (Set.right_mem_Icc.mpr r.lt.le)).le,
    secondH1_constant] at h
  simp only [weightedWave, poissonMain_eq_source, Complex.ofReal_one, one_mul] at h
  apply h.trans_eq
  field_simp
  ring

/-- The unweighted second-order estimate consumes explicit phase conditions, with every constant-weight field discharged. -/
theorem constant_second_poisson_from_phase {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hfd : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hfc : ContinuousOn (deriv f) (Set.Icc a b)) (hpos : 0 < deriv f b)
    (hfa : AntitoneOn (deriv f) (Set.Icc a b))
    (hfdd : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hfcc : ContinuousOn (deriv (deriv f)) (Set.Icc a b))
    (hanti : AntitoneOn (fun u => |deriv (deriv f) u|) (Set.Icc a b))
    (hq : ∀ n : ℕ, AntitoneOn (fun u => |deriv (deriv f) u| /
      (((n : ℝ) + 1) + deriv f u) ^ 2) (Set.Icc a b))
    (hr : ∀ n : ℕ, AntitoneOn (fun u => |deriv f u * deriv (deriv f) u| /
      (((n : ℝ) + 1) + deriv f u) ^ 3) (Set.Icc a b))
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2)
    (hδ : 1 / 2 ≤ (⌊deriv f a⌋₊ : ℝ) + 1 - deriv f a) :
    let y := deriv f a
    let M := ⌊y⌋₊
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 0 M, ∫ u in a..b,
        Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))‖ ≤
      (Real.log 2 + 1 / y) / Real.pi +
      (deriv f b * halfSecondEndpointBound M (deriv f b) + y * halfSecondEndpointBound M y) /
        (2 * Real.pi) +
      |deriv (deriv f) a| / (2 * Real.pi ^ 2) * (minusSquareBound M y + plusSquareBound y) +
      (y * |deriv (deriv f) a| / (2 * Real.pi ^ 2)) * (minusCubeBound M y + plusCubeBound y) := by
  exact constant_second_poisson_half
    (constant_secondOrderRegularity hab hfd hfc hpos hfa hfdd hfcc hanti hq hr) hah hbh hδ

end DhimanKadiriQuesadaHerrera2026

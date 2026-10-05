import DhimanKadiriQuesadaHerrera2026.PoissonShift

namespace DhimanKadiriQuesadaHerrera2026

/-- Constant weight satisfies every accepted Part-I amplitude condition, without positive derivative assumptions. -/
theorem partIRegularityAt_constant {f : ℝ → ℝ} {a b : ℝ} {N : ℕ}
    (hab : a < b) (hfd : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ f x)
    (hfc : ContinuousOn (deriv f) (Set.Icc a b)) (hN : (N : ℝ) < deriv f b)
    (hfa : AntitoneOn (deriv f) (Set.Icc a b)) : PartIRegularityAt f (fun _ => 1) a b N := by
  refine ⟨hab, hfd, hfc, hN, hfa, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x _
    exact differentiableAt_const 1
  · simp only [deriv_const']
    exact continuousOn_const
  · intro x _
    norm_num
  · intro x _ y _ _
    exact le_refl 1
  · simp only [deriv_const, abs_zero]
    exact antitoneOn_const
  · simp only [deriv_const, abs_zero, zero_div]
    exact antitoneOn_const

/-- Substitution of the actual constant weight gives the exact fully shifted analytic coefficient. -/
theorem partIShiftAnalyticError_constant {f : ℝ → ℝ} {a : ℝ} {N : ℕ}
    (hN : (N : ℝ) < deriv f a) :
    partIShiftAnalyticError f (fun _ => 1) a N =
      (1 / Real.pi) *
        (Real.log (1 + (deriv f a - N)) + Real.eulerMascheroniConstant +
          Real.log (((⌊deriv f a⌋₊ - N : ℕ) : ℝ) + 1) -
            (Complex.digamma ((1 - Int.fract (deriv f a) : ℝ) : ℂ)).re -
          1 / (2 * (((⌊deriv f a⌋₊ - N : ℕ) : ℝ) + 1)) -
            1 / (2 * (1 + (deriv f a - N)))) := by
  dsimp only [partIShiftAnalyticError]
  simp only [deriv_const, abs_zero, zero_add, mul_one]
  have hy : deriv f a - N ≠ 0 := (sub_pos.mpr hN).ne'
  field_simp

/-- The constant-weight Poisson bound retains every logarithmic and digamma term at arbitrary allowed N. -/
theorem poisson_constant_partI_half_integer {f : ℝ → ℝ} {a b : ℝ} {N : ℕ}
    (hab : a < b) (hfd : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ f x)
    (hfc : ContinuousOn (deriv f) (Set.Icc a b)) (hN : (N : ℝ) < deriv f b)
    (hfa : AntitoneOn (deriv f) (Set.Icc a b))
    (ha : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hb : ∃ k : ℤ, b = (k : ℝ) + 1 / 2) :
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc N ⌊deriv f a⌋₊,
        ∫ x in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f x - (ν : ℝ) * x : ℝ) : ℂ))‖ ≤
      (1 / Real.pi) *
        (Real.log (1 + (deriv f a - N)) + Real.eulerMascheroniConstant +
          Real.log (((⌊deriv f a⌋₊ - N : ℕ) : ℝ) + 1) -
            (Complex.digamma ((1 - Int.fract (deriv f a) : ℝ) : ℂ)).re -
          1 / (2 * (((⌊deriv f a⌋₊ - N : ℕ) : ℝ) + 1)) -
            1 / (2 * (1 + (deriv f a - N))) + Real.log 2 + 1 / (deriv f a - N)) := by
  have hreg := partIRegularityAt_constant hab hfd hfc hN hfa
  have h := corrected_poisson_partI_half_integer hreg ha hb
  rw [partIShiftAnalyticError_constant (hreg.deriv_gt (Set.left_mem_Icc.mpr hab.le))] at h
  simp only [weightedWave, Complex.ofReal_one, one_mul] at h
  apply h.trans_eq
  field_simp
  ring_nf

/-- Corollary 0.1 Part I has the literal printed constant, with all zero-amplitude hypotheses discharged. -/
theorem corollary_zero_one_partI {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hfd : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ f x)
    (hfc : ContinuousOn (deriv f) (Set.Icc a b)) (hpos : 0 < deriv f b)
    (hfa : StrictAntiOn (deriv f) (Set.Icc a b))
    (ha : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hb : ∃ k : ℤ, b = (k : ℝ) + 1 / 2) :
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 0 ⌊deriv f a⌋₊,
        ∫ x in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f x - (ν : ℝ) * x : ℝ) : ℂ))‖ ≤
      (1 / Real.pi) *
        (Real.log (1 + deriv f a) + Real.log (1 + (⌊deriv f a⌋₊ : ℝ)) +
          Real.eulerMascheroniConstant - 1 / (2 * (1 + (⌊deriv f a⌋₊ : ℝ))) -
            1 / (2 * (1 + deriv f a)) -
              (Complex.digamma ((1 - Int.fract (deriv f a) : ℝ) : ℂ)).re +
                Real.log 2 + 1 / deriv f a) := by
  have h := poisson_constant_partI_half_integer (N := 0) hab hfd hfc (by simpa only [Nat.cast_zero] using hpos) hfa.antitoneOn ha hb
  simp only [Nat.cast_zero, sub_zero, Nat.sub_zero] at h
  apply h.trans_eq
  congr 1
  rw [add_comm (1 : ℝ) (⌊deriv f a⌋₊ : ℝ)]
  ring

end DhimanKadiriQuesadaHerrera2026

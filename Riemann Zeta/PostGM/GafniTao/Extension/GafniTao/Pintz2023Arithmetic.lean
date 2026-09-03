import GafniTao.PintzPublishedCutoff

/-!
# Exact parameter arithmetic in Pintz (2023), Sections 2--4

This file isolates the real-variable arithmetic which surrounds the powered
Dirichlet-polynomial argument.  In particular, it keeps the `-6 r ε`
perturbations appearing in Pintz equations (3.1), (4.15), and (4.24), rather
than silently replacing them by their limiting values.
-/

open Filter Set Topology

namespace GafniTao

noncomputable section

/-- The perturbed `k` denominator in Pintz equation (4.24). -/
noncomputable def pintzKDenominator
    (eta epsilon : ℝ) (k : ℕ) : ℝ :=
  (k : ℝ) * (1 - ((k : ℝ) - 1) * eta - 6 * (k : ℝ) * epsilon)

/-- The perturbed `ell` denominator in Pintz equation (4.24). -/
noncomputable def pintzEllDenominator
    (eta epsilon : ℝ) (ell : ℕ) : ℝ :=
  (ell : ℝ) *
    (1 - 2 * eta * ((ell : ℝ) - 1) - 6 * (ell : ℝ) * epsilon)

/-- The literal maximum in the exponent on the right of Pintz (4.24). -/
noncomputable def pintzPerturbedCoefficient
    (eta epsilon : ℝ) (k ell : ℕ) : ℝ :=
  max (3 / pintzEllDenominator eta epsilon ell)
    (4 / pintzKDenominator eta epsilon k)

theorem pintzCell_eta_pos
    {eta : ℝ} {k ell : ℕ} (hcell : PintzCell eta k ell) :
    0 < eta := by
  rcases hcell with ⟨_hkFour, hellThree, _hkUpper, _hkLower,
    _hellUpper, hellLower⟩
  have hellPos : (0 : ℝ) < ell := by
    exact_mod_cast (lt_of_lt_of_le (by omega) hellThree)
  have hfactor : 0 < (2 : ℝ) * (ell + 1) * ell := by positivity
  nlinarith

theorem pintzCell_k_base_denominator_pos
    {eta : ℝ} {k ell : ℕ} (hcell : PintzCell eta k ell) :
    0 < pintzKDenominator eta 0 k := by
  have heta : 0 < eta := pintzCell_eta_pos hcell
  rcases hcell with ⟨hkFour, _hellThree, hkUpper, _hkLower,
    _hellUpper, _hellLower⟩
  have hkOne : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hterm : 0 ≤ eta * ((k : ℝ) - 1) := by positivity
  have hcompare : eta * ((k : ℝ) - 1) ≤
      (eta * ((k : ℝ) - 1)) * (k : ℝ) :=
    by simpa only [mul_one] using mul_le_mul_of_nonneg_left hkOne hterm
  unfold pintzKDenominator
  have hparen : 0 < 1 - ((k : ℝ) - 1) * eta := by
    nlinarith [hcompare]
  simpa using mul_pos (zero_lt_one.trans_le hkOne) hparen

theorem pintzCell_ell_base_denominator_pos
    {eta : ℝ} {k ell : ℕ} (hcell : PintzCell eta k ell) :
    0 < pintzEllDenominator eta 0 ell := by
  have heta : 0 < eta := pintzCell_eta_pos hcell
  rcases hcell with ⟨_hkFour, hellThree, _hkUpper, _hkLower,
    hellUpper, _hellLower⟩
  have hellOne : (1 : ℝ) ≤ ell := by exact_mod_cast (show 1 ≤ ell by omega)
  have hterm : 0 ≤ 2 * eta * ((ell : ℝ) - 1) := by positivity
  have hcompare : 2 * eta * ((ell : ℝ) - 1) ≤
      (2 * eta * ((ell : ℝ) - 1)) * (ell : ℝ) :=
    by simpa only [mul_one] using mul_le_mul_of_nonneg_left hellOne hterm
  unfold pintzEllDenominator
  have hparen : 0 < 1 - 2 * eta * ((ell : ℝ) - 1) := by
    nlinarith [hcompare]
  simpa using mul_pos (zero_lt_one.trans_le hellOne) hparen

theorem pintzKDenominator_pos
    {eta epsilon : ℝ} {k : ℕ}
    (hk : 0 < k)
    (hmargin : 6 * (k : ℝ) * epsilon <
      1 - ((k : ℝ) - 1) * eta) :
    0 < pintzKDenominator eta epsilon k := by
  have hkReal : (0 : ℝ) < k := by exact_mod_cast hk
  unfold pintzKDenominator
  positivity

theorem pintzEllDenominator_pos
    {eta epsilon : ℝ} {ell : ℕ}
    (hell : 0 < ell)
    (hmargin : 6 * (ell : ℝ) * epsilon <
      1 - 2 * eta * ((ell : ℝ) - 1)) :
    0 < pintzEllDenominator eta epsilon ell := by
  have hellReal : (0 : ℝ) < ell := by exact_mod_cast hell
  unfold pintzEllDenominator
  positivity

theorem pintzPerturbedCoefficient_zero
    (eta : ℝ) (k ell : ℕ) :
    pintzPerturbedCoefficient eta 0 k ell =
      pintzTheoremOneCoefficient eta k ell := by
  unfold pintzPerturbedCoefficient pintzTheoremOneCoefficient
    pintzKDenominator pintzEllDenominator
  ring_nf

theorem continuousAt_pintzPerturbedCoefficient
    {eta : ℝ} {k ell : ℕ} (hcell : PintzCell eta k ell) :
    ContinuousAt (fun epsilon : ℝ =>
      pintzPerturbedCoefficient eta epsilon k ell) 0 := by
  have hkNe : pintzKDenominator eta 0 k ≠ 0 :=
    (pintzCell_k_base_denominator_pos hcell).ne'
  have hellNe : pintzEllDenominator eta 0 ell ≠ 0 :=
    (pintzCell_ell_base_denominator_pos hcell).ne'
  unfold pintzPerturbedCoefficient
  have hEll : ContinuousAt (fun epsilon : ℝ =>
      3 / pintzEllDenominator eta epsilon ell) 0 := by
    apply ContinuousAt.div continuousAt_const
      (show ContinuousAt (fun epsilon : ℝ =>
        pintzEllDenominator eta epsilon ell) 0 by
          unfold pintzEllDenominator
          fun_prop)
    exact hellNe
  have hK : ContinuousAt (fun epsilon : ℝ =>
      4 / pintzKDenominator eta epsilon k) 0 := by
    apply ContinuousAt.div continuousAt_const
      (show ContinuousAt (fun epsilon : ℝ =>
        pintzKDenominator eta epsilon k) 0 by
          unfold pintzKDenominator
          fun_prop)
    exact hkNe
  exact hEll.max hK

/-- The perturbed coefficient in (4.24) approaches the exact coefficient in
Pintz Theorem 1 as the auxiliary epsilon tends to zero. -/
theorem tendsto_pintzPerturbedCoefficient_zero
    {eta : ℝ} {k ell : ℕ} (hcell : PintzCell eta k ell) :
    Tendsto (fun epsilon : ℝ =>
      pintzPerturbedCoefficient eta epsilon k ell)
      (𝓝 0) (𝓝 (pintzTheoremOneCoefficient eta k ell)) := by
  rw [← pintzPerturbedCoefficient_zero eta k ell]
  exact continuousAt_pintzPerturbedCoefficient hcell

/-- A source-sized positive perturbation can be chosen while losing less
than any prescribed amount in the final exponent. -/
theorem exists_pintz_perturbation
    {eta target : ℝ} {k ell : ℕ}
    (hcell : PintzCell eta k ell) (htarget : 0 < target) :
    ∃ epsilon : ℝ,
      0 < epsilon ∧
      6 * (k : ℝ) * epsilon < 1 - ((k : ℝ) - 1) * eta ∧
      6 * (ell : ℝ) * epsilon <
        1 - 2 * eta * ((ell : ℝ) - 1) ∧
      eta * pintzPerturbedCoefficient eta epsilon k ell <
        eta * pintzTheoremOneCoefficient eta k ell + target := by
  have heta : 0 < eta := pintzCell_eta_pos hcell
  have hkBase := pintzCell_k_base_denominator_pos hcell
  have hellBase := pintzCell_ell_base_denominator_pos hcell
  have hkNat : 0 < k := by
    exact lt_of_lt_of_le (by omega) hcell.1
  have hellNat : 0 < ell := by
    exact lt_of_lt_of_le (by omega) hcell.2.1
  have hkReal : (0 : ℝ) < k := by exact_mod_cast hkNat
  have hellReal : (0 : ℝ) < ell := by exact_mod_cast hellNat
  have hkParen : 0 < 1 - ((k : ℝ) - 1) * eta := by
    unfold pintzKDenominator at hkBase
    nlinarith
  have hellParen : 0 < 1 - 2 * eta * ((ell : ℝ) - 1) := by
    unfold pintzEllDenominator at hellBase
    nlinarith
  obtain ⟨radius, hradius, hclose⟩ :=
    Metric.continuousAt_iff.mp
      (continuousAt_pintzPerturbedCoefficient hcell)
      (target / eta) (by positivity)
  let marginK : ℝ := (1 - ((k : ℝ) - 1) * eta) / (12 * (k : ℝ))
  let marginEll : ℝ :=
    (1 - 2 * eta * ((ell : ℝ) - 1)) / (12 * (ell : ℝ))
  have hmarginK : 0 < marginK := by
    dsimp only [marginK]
    positivity
  have hmarginEll : 0 < marginEll := by
    dsimp only [marginEll]
    positivity
  let epsilon : ℝ := min radius (min marginK marginEll) / 2
  have hepsilon : 0 < epsilon := by
    dsimp only [epsilon]
    positivity
  have hepsilonRadius : epsilon < radius := by
    dsimp only [epsilon]
    have := min_le_left radius (min marginK marginEll)
    nlinarith
  have hepsilonK : epsilon ≤ marginK := by
    dsimp only [epsilon]
    have hmin := min_le_right radius (min marginK marginEll)
    have := min_le_left marginK marginEll
    nlinarith
  have hepsilonEll : epsilon ≤ marginEll := by
    dsimp only [epsilon]
    have hmin := min_le_right radius (min marginK marginEll)
    have := min_le_right marginK marginEll
    nlinarith
  have hK : 6 * (k : ℝ) * epsilon <
      1 - ((k : ℝ) - 1) * eta := by
    dsimp only [marginK] at hepsilonK
    have hkTwelve : 0 < 12 * (k : ℝ) := by positivity
    have hscaled := (le_div_iff₀ hkTwelve).mp hepsilonK
    nlinarith
  have hEll : 6 * (ell : ℝ) * epsilon <
      1 - 2 * eta * ((ell : ℝ) - 1) := by
    dsimp only [marginEll] at hepsilonEll
    have hellTwelve : 0 < 12 * (ell : ℝ) := by positivity
    have hscaled := (le_div_iff₀ hellTwelve).mp hepsilonEll
    nlinarith
  have hdist : dist epsilon 0 < radius := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hepsilon]
    exact hepsilonRadius
  have hCoeffDist := hclose hdist
  rw [Real.dist_eq,
    pintzPerturbedCoefficient_zero eta k ell] at hCoeffDist
  have hCoeff : pintzPerturbedCoefficient eta epsilon k ell <
      pintzTheoremOneCoefficient eta k ell + target / eta := by
    linarith [le_abs_self
      (pintzPerturbedCoefficient eta epsilon k ell -
        pintzTheoremOneCoefficient eta k ell)]
  refine ⟨epsilon, hepsilon, hK, hEll, ?_⟩
  have hmul := mul_lt_mul_of_pos_left hCoeff heta
  field_simp [heta.ne'] at hmul
  exact hmul

/-- Elementary Archimedean power selection used in the non-squaring branch
of Pintz (4.15)--(4.16). -/
theorem exists_positive_nat_power_in_window
    {lower u width : ℝ}
    (hlower : 0 ≤ lower) (hu : 0 < u) (hwidth : u < width) :
    ∃ h : ℕ, 1 ≤ h ∧ lower < (h : ℝ) * u ∧
      (h : ℝ) * u < lower + width := by
  let h : ℕ := ⌊lower / u⌋₊ + 1
  have hquot : 0 ≤ lower / u := div_nonneg hlower hu.le
  have hfloorLower : ((⌊lower / u⌋₊ : ℕ) : ℝ) ≤ lower / u :=
    Nat.floor_le hquot
  have hfloorUpper : lower / u < ((⌊lower / u⌋₊ : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  refine ⟨h, by dsimp only [h]; omega, ?_, ?_⟩
  · dsimp only [h]
    have := mul_lt_mul_of_pos_right hfloorUpper hu
    rw [div_mul_cancel₀ lower hu.ne'] at this
    norm_num at this ⊢
    linarith
  · dsimp only [h]
    have := mul_le_mul_of_nonneg_right hfloorLower hu.le
    rw [div_mul_cancel₀ lower hu.ne'] at this
    norm_num at this ⊢
    nlinarith

#print axioms pintzCell_threshold_order
#print axioms pintzKDenominator_pos
#print axioms pintzEllDenominator_pos
#print axioms tendsto_pintzPerturbedCoefficient_zero
#print axioms exists_pintz_perturbation
#print axioms exists_positive_nat_power_in_window

end

end GafniTao

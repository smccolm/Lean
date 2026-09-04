import GafniTao.WooleySection9Admissible

/-!
# The analytic two-step composition in Wooley Lemma 9.3

The arithmetic properties of the selected scales and weights are proved in
`WooleySection9Arithmetic`.  Here we prove the exact nonlinear substitution
of the two Lemma-9.2 bounds, with both formerly implicit constants retained.
-/

namespace GafniTao

noncomputable section

/-- Substitution of one monograde estimate into another. -/
theorem wooley_monograde_two_step_compose
    {P Q R C₁ C₂ tail₁ tail₂ rho₁ rho₂ : ℝ}
    (hQ : 0 ≤ Q) (hR : 0 ≤ R) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (htail₁ : 0 ≤ tail₁) (htail₂ : 0 ≤ tail₂) (hrho₁ : 0 ≤ rho₁)
    (hfirst : P ≤ C₁ * Q ^ rho₁ * tail₁)
    (hsecond : Q ≤ C₂ * R ^ rho₂ * tail₂) :
    P ≤ C₁ * C₂ ^ rho₁ * R ^ (rho₁ * rho₂) *
      tail₂ ^ rho₁ * tail₁ := by
  have hsecondPow := Real.rpow_le_rpow hQ hsecond hrho₁
  have hRpow : 0 ≤ R ^ rho₂ := Real.rpow_nonneg hR _
  have hmiddle : 0 ≤ C₁ * tail₁ := mul_nonneg hC₁ htail₁
  calc
    P ≤ C₁ * Q ^ rho₁ * tail₁ := hfirst
    _ ≤ C₁ * (C₂ * R ^ rho₂ * tail₂) ^ rho₁ * tail₁ := by
      have := mul_le_mul_of_nonneg_left hsecondPow hC₁
      exact mul_le_mul_of_nonneg_right this htail₁
    _ = C₁ * C₂ ^ rho₁ * R ^ (rho₁ * rho₂) *
        tail₂ ^ rho₁ * tail₁ := by
      rw [Real.mul_rpow (mul_nonneg hC₂ hRpow) htail₂,
        Real.mul_rpow hC₂ hRpow, ← Real.rpow_mul hR]
      ring_nf

/-- The extra decay produced by the second step is at most one, so the source
may retain only its first `p^{-b Lambda/(2k)}` factor in (9.6). -/
theorem wooley_second_decay_rpow_le_one
    {p k b : ℕ} {Lambda rho : ℝ}
    (hp : 2 ≤ p) (hk : 1 ≤ k) (hLambda : 0 ≤ Lambda)
    (hrho : 0 ≤ rho) :
    ((p : ℝ) ^ (-(b : ℝ) * Lambda / (2 * (k : ℝ)))) ^ rho ≤ 1 := by
  have hpOne : (1 : ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hexp : -(b : ℝ) * Lambda / (2 * (k : ℝ)) ≤ 0 := by
    have hnum : -(b : ℝ) * Lambda ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) hLambda
    exact div_nonpos_of_nonpos_of_nonneg hnum (by positivity)
  have hbase : (p : ℝ) ^ (-(b : ℝ) * Lambda / (2 * (k : ℝ))) ≤ 1 := by
    rw [← Real.rpow_zero (p : ℝ)]
    exact Real.rpow_le_rpow_of_exponent_le hpOne hexp
  have hbase0 : 0 ≤ (p : ℝ) ^ (-(b : ℝ) * Lambda / (2 * (k : ℝ))) :=
    Real.rpow_nonneg (by positivity) _
  simpa only [Real.one_rpow] using Real.rpow_le_rpow hbase0 hbase hrho

/-- Source-shaped two-step composition.  The output retains the first decay
factor and exposes the exact product weight `rho_{r1} rho_{r2}`. -/
theorem wooley_source_two_step_compose
    {p k b b₁ : ℕ} {Lambda P Q R C₁ C₂ : ℝ}
    {r₁ r₂ : ℕ}
    (hp : 2 ≤ p) (hk : 2 ≤ k) (hLambda : 0 ≤ Lambda)
    (hQ : 0 ≤ Q) (hR : 0 ≤ R) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hr₁ : 1 ≤ r₁)
    (hfirst : P ≤ C₁ * Q ^ wooleyRho k r₁ *
      (p : ℝ) ^ (-(b : ℝ) * Lambda / (2 * (k : ℝ))))
    (hsecond : Q ≤ C₂ * R ^ wooleyRho k r₂ *
      (p : ℝ) ^ (-(b₁ : ℝ) * Lambda / (2 * (k : ℝ)))) :
    P ≤ C₁ * C₂ ^ wooleyRho k r₁ *
      R ^ wooleyTwoStepWeight k r₁ r₂ *
      (p : ℝ) ^ (-(b : ℝ) * Lambda / (2 * (k : ℝ))) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hrho₁ : 0 ≤ wooleyRho k r₁ := (wooleyRho_pos hr₁).le
  have hfull := wooley_monograde_two_step_compose
    hQ hR hC₁ hC₂ (Real.rpow_nonneg hpR.le _) (Real.rpow_nonneg hpR.le _)
      hrho₁ hfirst hsecond
  have hdrop := wooley_second_decay_rpow_le_one
    (p := p) (k := k) (b := b₁) (Lambda := Lambda)
      (rho := wooleyRho k r₁) hp (by omega) hLambda hrho₁
  have hnonneg : 0 ≤ C₁ * C₂ ^ wooleyRho k r₁ *
      R ^ (wooleyRho k r₁ * wooleyRho k r₂) := by positivity
  calc
    P ≤ C₁ * C₂ ^ wooleyRho k r₁ *
        R ^ (wooleyRho k r₁ * wooleyRho k r₂) *
        ((p : ℝ) ^ (-(b₁ : ℝ) * Lambda / (2 * (k : ℝ)))) ^
          wooleyRho k r₁ *
        (p : ℝ) ^ (-(b : ℝ) * Lambda / (2 * (k : ℝ))) := hfull
    _ ≤ C₁ * C₂ ^ wooleyRho k r₁ *
        R ^ (wooleyRho k r₁ * wooleyRho k r₂) * 1 *
        (p : ℝ) ^ (-(b : ℝ) * Lambda / (2 * (k : ℝ))) := by
      gcongr
    _ = C₁ * C₂ ^ wooleyRho k r₁ *
        R ^ wooleyTwoStepWeight k r₁ r₂ *
        (p : ℝ) ^ (-(b : ℝ) * Lambda / (2 * (k : ℝ))) := by
      simp only [wooleyTwoStepWeight, mul_one]

#print axioms wooley_monograde_two_step_compose
#print axioms wooley_second_decay_rpow_le_one
#print axioms wooley_source_two_step_compose

end

end GafniTao

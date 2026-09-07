import GafniTao.ZeroEnergy

/-!
# Near-one zero inputs and the Lemma 2.1 exponent optimizer

This module states the two source inputs used at the right edge in their
literal quantitative form.  They are predicates, not project axioms.  The
public theorems below prove the algebraic optimization that converts the
logarithmic density exponent into decay on the physical `X` scale.
-/

namespace GafniTao

/-- The logarithmic near-one density estimate used in the proof of Lemma 2.1.
The exponent is literally `C * eta^(3/2)`; no `T^epsilon` loss is inserted. -/
def NearOneLogDensityBound (C B T₀ : ℝ) : Prop :=
  ∀ ⦃eta T : ℝ⦄, 0 < eta → eta ≤ 1 / 2 → T₀ ≤ T →
    (zeroCount (1 - eta) T : ℝ) ≤
      T ^ (C * eta ^ (3 / 2 : ℝ)) * Real.log T ^ B

/-- Count-level Vinogradov--Korobov zero-free input.  The weak inequality at
the boundary is recorded explicitly rather than hidden in asymptotic
notation. -/
def VinogradovKorobovCountVanishing (c T₀ : ℝ) : Prop :=
  ∀ ⦃eta T : ℝ⦄, 0 < eta → T₀ ≤ T →
    eta ≤ c /
      (Real.log T ^ (2 / 3 : ℝ) *
        Real.log (Real.log T) ^ (1 / 3 : ℝ)) →
    zeroCount (1 - eta) T = 0

/-- The elementary `eta^(3/2)` identity used to choose the fixed right-edge
width. -/
theorem eta_three_halves_eq_mul_sqrt {eta : ℝ} (heta : 0 ≤ eta) :
    eta ^ (3 / 2 : ℝ) = eta * eta ^ (1 / 2 : ℝ) := by
  by_cases hzero : eta = 0
  · simp [hzero]
  have hetaPos : 0 < eta := lt_of_le_of_ne heta (Ne.symm hzero)
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
    Real.rpow_add hetaPos, Real.rpow_one]

/-- A concrete fixed right-edge width makes the logarithmic-density exponent
at most half the saving `eta`. -/
theorem nearOne_density_exponent_le_half
    {C q eta : ℝ} (hC : 0 < C) (hq : 0 < q) (heta : 0 ≤ eta)
    (hetaSmall : eta ≤ (1 / (2 * q * C)) ^ (2 : ℕ)) :
    q * (C * eta ^ (3 / 2 : ℝ)) ≤ eta / 2 := by
  rw [eta_three_halves_eq_mul_sqrt heta]
  by_cases hetaZero : eta = 0
  · simp [hetaZero]
  have hetaPos : 0 < eta := lt_of_le_of_ne heta (Ne.symm hetaZero)
  have hden : 0 < 2 * q * C := by positivity
  have hdenne : 2 * q * C ≠ 0 := ne_of_gt hden
  have hfraction : q * C / (2 * q * C) = (1 / 2 : ℝ) := by
    apply (div_eq_iff hdenne).2
    ring
  have hsqrt : eta ^ (1 / 2 : ℝ) ≤ 1 / (2 * q * C) := by
    have hsquareNonneg : 0 ≤ 1 / (2 * q * C) := le_of_lt (one_div_pos.mpr hden)
    rw [← Real.sqrt_eq_rpow]
    calc
      √eta ≤ √((1 / (2 * q * C)) ^ (2 : ℕ)) :=
        Real.sqrt_le_sqrt hetaSmall
      _ = |1 / (2 * q * C)| := Real.sqrt_sq_eq_abs _
      _ = 1 / (2 * q * C) := abs_of_nonneg hsquareNonneg
  calc
    q * (C * (eta * eta ^ (1 / 2 : ℝ))) =
        eta * (q * C * eta ^ (1 / 2 : ℝ)) := by ring
    _ ≤ eta * (q * C * (1 / (2 * q * C))) := by gcongr
    _ = eta * (q * C / (2 * q * C)) := by simp [div_eq_mul_inv]
    _ = eta * (1 / 2) := by rw [hfraction]
    _ = eta / 2 := by ring

/-- The exact algebraic heart of the near-one argument.  A source density
bound at height `T`, together with `T ≤ X^q` and the explicit exponent margin,
produces the required half-saving after multiplication by `X^{-eta}`. -/
theorem nearOne_count_mul_rpow_neg_le
    {C B T₀ q eta T X : ℝ}
    (hDensity : NearOneLogDensityBound C B T₀)
    (hetaPos : 0 < eta) (hetaUpper : eta ≤ 1 / 2)
    (hT₀ : T₀ ≤ T) (hTone : 1 ≤ T)
    (hX : 1 ≤ X) (hTscale : T ≤ X ^ q)
    (hExponent : q * (C * eta ^ (3 / 2 : ℝ)) ≤ eta / 2)
    (hExponentNonneg : 0 ≤ C * eta ^ (3 / 2 : ℝ)) :
    (zeroCount (1 - eta) T : ℝ) * X ^ (-eta) ≤
      Real.log T ^ B * X ^ (-eta / 2) := by
  have hDensityT := hDensity hetaPos hetaUpper hT₀
  have hTnonneg : 0 ≤ T := zero_le_one.trans hTone
  have hXnonneg : 0 ≤ X := zero_le_one.trans hX
  have hTpow :
      T ^ (C * eta ^ (3 / 2 : ℝ)) ≤
        (X ^ q) ^ (C * eta ^ (3 / 2 : ℝ)) :=
    Real.rpow_le_rpow hTnonneg hTscale hExponentNonneg
  have hpowCollapse :
      (X ^ q) ^ (C * eta ^ (3 / 2 : ℝ)) =
        X ^ (q * (C * eta ^ (3 / 2 : ℝ))) := by
    rw [Real.rpow_mul hXnonneg]
  have hXpow :
      X ^ (q * (C * eta ^ (3 / 2 : ℝ))) ≤ X ^ (eta / 2) :=
    Real.rpow_le_rpow_of_exponent_le hX hExponent
  have hlogNonneg : 0 ≤ Real.log T ^ B :=
    Real.rpow_nonneg (Real.log_nonneg hTone) B
  calc
    (zeroCount (1 - eta) T : ℝ) * X ^ (-eta) ≤
        (T ^ (C * eta ^ (3 / 2 : ℝ)) * Real.log T ^ B) *
          X ^ (-eta) := by
            gcongr
    _ ≤ (X ^ (eta / 2) * Real.log T ^ B) * X ^ (-eta) := by
          gcongr
          exact hTpow.trans_eq hpowCollapse |>.trans hXpow
    _ = Real.log T ^ B * (X ^ (eta / 2) * X ^ (-eta)) := by ring
    _ = Real.log T ^ B * X ^ (-eta / 2) := by
      rw [← Real.rpow_add (zero_lt_one.trans_le hX)]
      rw [show eta / 2 + -eta = -eta / 2 by ring]

/-- The same decay with the exponent margin discharged by the concrete fixed
right-edge width. -/
theorem nearOne_count_mul_rpow_neg_le_of_eta_small
    {C B T₀ q eta T X : ℝ}
    (hDensity : NearOneLogDensityBound C B T₀)
    (hC : 0 < C) (hq : 0 < q)
    (hetaPos : 0 < eta) (hetaUpper : eta ≤ 1 / 2)
    (hetaSmall : eta ≤ (1 / (2 * q * C)) ^ (2 : ℕ))
    (hT₀ : T₀ ≤ T) (hTone : 1 ≤ T)
    (hX : 1 ≤ X) (hTscale : T ≤ X ^ q) :
    (zeroCount (1 - eta) T : ℝ) * X ^ (-eta) ≤
      Real.log T ^ B * X ^ (-eta / 2) := by
  apply nearOne_count_mul_rpow_neg_le hDensity hetaPos hetaUpper hT₀ hTone
    hX hTscale
  · exact nearOne_density_exponent_le_half hC hq hetaPos.le hetaSmall
  · positivity

/-- The source near-one inputs now meet in one theorem: below the
Vinogradov--Korobov threshold the actual multiplicity-weighted count vanishes;
above it the logarithmic density theorem supplies the optimized half-saving.
This is the precise pointwise dichotomy used before summing/integrating in
Lemma 2.1. -/
theorem nearOne_count_zero_or_half_decay
    {C B T₀ c T₁ q eta T X : ℝ}
    (hDensity : NearOneLogDensityBound C B T₀)
    (hZeroFree : VinogradovKorobovCountVanishing c T₁)
    (hC : 0 < C) (hq : 0 < q)
    (hetaPos : 0 < eta) (hetaUpper : eta ≤ 1 / 2)
    (hetaSmall : eta ≤ (1 / (2 * q * C)) ^ (2 : ℕ))
    (hT₀ : T₀ ≤ T) (hT₁ : T₁ ≤ T) (hTone : 1 ≤ T)
    (hX : 1 ≤ X) (hTscale : T ≤ X ^ q) :
    zeroCount (1 - eta) T = 0 ∨
      (zeroCount (1 - eta) T : ℝ) * X ^ (-eta) ≤
        Real.log T ^ B * X ^ (-eta / 2) := by
  by_cases hetaVK :
      eta ≤ c /
        (Real.log T ^ (2 / 3 : ℝ) *
          Real.log (Real.log T) ^ (1 / 3 : ℝ))
  · exact Or.inl (hZeroFree hetaPos hT₁ hetaVK)
  · exact Or.inr (nearOne_count_mul_rpow_neg_le_of_eta_small
      hDensity hC hq hetaPos hetaUpper hetaSmall hT₀ hTone hX hTscale)

end GafniTao

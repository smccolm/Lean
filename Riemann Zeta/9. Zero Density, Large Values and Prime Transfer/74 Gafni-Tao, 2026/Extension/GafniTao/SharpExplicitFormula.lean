import GafniTao.StripAssembly

/-!
# The sharp truncated explicit-formula contract and its physical error ledger

The predicate in this file is the exact upstream analytic theorem still to be
proved from Perron inversion and contour shifting.  It is intentionally much
narrower than any exceptional-set conclusion: it is a pointwise identity
error for the actual Chebyshev increment and the actual multiplicity-weighted
zero sum.  The subsequent lemmas consume its constant explicitly at the
Gafni--Tao height `J log(X)^2 tau`.
-/

open Filter

namespace GafniTao

/-- The standard sharp explicit-formula remainder: the literal short
Chebyshev discrepancy plus the truncated, multiplicity-weighted nontrivial
zero sum.  Davenport's contour shift gives the zero sum with a minus sign in
the discrepancy.  The displayed sign in Gafni--Tao (2.3) is immaterial to its
absolute-value consumer, but the formal remainder uses the analytic sign. -/
noncomputable def sharpExplicitFormulaError (T tau x : ℝ) : ℂ :=
  ((mangoldtIntervalSum x (x / tau) - x / tau : ℝ) : ℂ) +
    fullZeroIncrementSum T tau x

/-- Source-faithful pointwise form of the sharp truncated explicit formula in
the standard application range `2 ≤ T ≤ x`.  The upper restriction is
essential: it is what absorbs the nearest-integer/endpoint term into
`x log^2(x) / T`.  The parameter called `X` elsewhere is irrelevant here;
`tau`, `T`, and `x` are the actual analytic variables. -/
def SharpTruncatedExplicitFormulaBound : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ {T tau x : ℝ}, 1 ≤ tau → 2 ≤ T → T ≤ x → 2 ≤ x →
      ‖sharpExplicitFormulaError T tau x‖ ≤
        C * x * (Real.log x) ^ 2 / T

/-- The harmless first two arguments of `localMangoldtSum` only supply
`tau = localTau X theta`; unfolding exposes the literal Mangoldt interval. -/
theorem sharpExplicitFormulaError_physical_eq
    (J theta X x : ℝ) :
    sharpExplicitFormulaError (explicitFormulaHeight J theta X)
        (localTau X theta) x =
      (((localMangoldtSum X theta x - x / localTau X theta : ℝ) : ℂ) +
        fullZeroIncrementSum (explicitFormulaHeight J theta X)
          (localTau X theta) x) := by
  rw [sharpExplicitFormulaError, localMangoldtSum]

/-- At the source height, the explicit-formula error is at most
`8 C / J * X^theta`, uniformly on `[X,2X]`.  The factor eight records the
literal `x ≤ 2X` and `log x ≤ 2 log X` losses. -/
theorem eventually_sharpExplicitFormulaError_physical_le
    (hFormula : SharpTruncatedExplicitFormulaBound) :
    ∃ C : ℝ, 0 < C ∧ ∀ {J : ℕ}, 0 < J →
      ∀ {theta : ℝ}, 0 < theta → theta < 1 →
      ∀ᶠ X in atTop, ∀ x : ℝ, X ≤ x → x ≤ 2 * X →
        ‖sharpExplicitFormulaError (explicitFormulaHeight J theta X)
            (localTau X theta) x‖ ≤
          (8 * C / J) * X ^ theta := by
  rcases hFormula with ⟨C, hC, hFormula⟩
  refine ⟨C, hC, ?_⟩
  intro J hJ theta hthetaPos htheta
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  filter_upwards [eventually_ge_atTop (Real.exp 2),
      tendsto_explicitFormulaHeight_atTop hJr htheta |>.eventually
        (eventually_ge_atTop 2),
      eventually_explicitFormulaHeight_le_rpow
        (J := (J : ℝ)) (theta := theta) (q := theta / 2)
          (half_pos hthetaPos)] with X hX hT hHeightPow x hxLower hxUpper
  have hXPos : 0 < X := (Real.exp_pos 2).trans_le hX
  have hxTwo : 2 ≤ x := by
    have hexpTwo : 2 < Real.exp 2 := by
      linarith [Real.add_one_lt_exp (show (2 : ℝ) ≠ 0 by norm_num)]
    linarith
  have htau : 0 < localTau X theta := localTau_pos hXPos
  have htauOne : 1 ≤ localTau X theta := by
    rw [localTau]
    exact Real.one_le_rpow
      (by
        have : 1 < Real.exp 2 := Real.one_lt_exp_iff.mpr (by norm_num)
        exact this.le.trans hX)
      (by linarith)
  have hHeightLeX : explicitFormulaHeight J theta X ≤ X := by
    calc
      explicitFormulaHeight J theta X ≤ X ^ (1 - theta + theta / 2) :=
        hHeightPow
      _ ≤ X ^ (1 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le
        · exact (by
            have : 1 < Real.exp 2 := Real.one_lt_exp_iff.mpr (by norm_num)
            exact this.le.trans hX)
        · linarith
      _ = X := Real.rpow_one X
  have hraw := hFormula htauOne hT (hHeightLeX.trans hxLower) hxTwo
  have hlogX : 0 < Real.log X := Real.log_pos (by
    have : 1 < Real.exp 2 := Real.one_lt_exp_iff.mpr (by norm_num)
    exact this.trans_le hX)
  have hlogTwo : Real.log 2 ≤ Real.log X := by
    apply Real.strictMonoOn_log.monotoneOn (by norm_num) hXPos
    have hexpTwo : 2 < Real.exp 2 := by
      linarith [Real.add_one_lt_exp (show (2 : ℝ) ≠ 0 by norm_num)]
    linarith
  have hxPos : 0 < x := by linarith
  have hlogxNonneg : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hlogx : Real.log x ≤ 2 * Real.log X := by
    calc
      Real.log x ≤ Real.log (2 * X) :=
        Real.strictMonoOn_log.monotoneOn hxPos (mul_pos (by norm_num) hXPos)
          hxUpper
      _ = Real.log 2 + Real.log X := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hXPos.ne']
      _ ≤ 2 * Real.log X := by linarith
  have hlogSq : (Real.log x) ^ 2 ≤ 4 * (Real.log X) ^ 2 := by nlinarith
  have hlogXSqPos : 0 < (Real.log X) ^ 2 := sq_pos_of_pos hlogX
  have hnumerator :
      C * x * (Real.log x) ^ 2 ≤ C * (2 * X) * (4 * (Real.log X) ^ 2) := by
    gcongr
  have hheight : explicitFormulaHeight (J : ℝ) theta X =
      J * (Real.log X) ^ 2 * localTau X theta := rfl
  calc
    ‖sharpExplicitFormulaError (explicitFormulaHeight J theta X)
        (localTau X theta) x‖
        ≤ C * x * (Real.log x) ^ 2 /
            explicitFormulaHeight J theta X := hraw
    _ ≤ C * (2 * X) * (4 * (Real.log X) ^ 2) /
          explicitFormulaHeight J theta X := by
            exact div_le_div_of_nonneg_right hnumerator
              (explicitFormulaHeight_pos hJr (by
                have : 1 < Real.exp 2 :=
                  Real.one_lt_exp_iff.mpr (by norm_num)
                exact this.trans_le hX)).le
    _ = (8 * C / J) * (X / localTau X theta) := by
      rw [hheight]
      field_simp [hJr.ne', hlogXSqPos.ne', (localTau_pos hXPos).ne']
      ring
    _ = (8 * C / J) * X ^ theta := by
      rw [div_localTau_self_eq_rpow hXPos]

/-- Once `J` exceeds the explicit-formula constant budget, its physical
remainder is at most `delta/3 * X^theta`. -/
theorem eventually_sharpExplicitFormulaError_physical_le_third
    (hFormula : SharpTruncatedExplicitFormulaBound) :
    ∃ C : ℝ, 0 < C ∧ ∀ {J : ℕ}, 0 < J →
      ∀ {theta delta : ℝ}, 0 < theta → theta < 1 → 0 < delta →
      24 * C ≤ delta * J →
      ∀ᶠ X in atTop, ∀ x : ℝ, X ≤ x → x ≤ 2 * X →
        ‖sharpExplicitFormulaError (explicitFormulaHeight J theta X)
            (localTau X theta) x‖ ≤
          (delta / 3) * X ^ theta := by
  obtain ⟨C, hC, hBound⟩ :=
    eventually_sharpExplicitFormulaError_physical_le hFormula
  refine ⟨C, hC, ?_⟩
  intro J hJ theta delta hthetaPos htheta hdelta hJlarge
  filter_upwards [hBound hJ hthetaPos htheta] with X hX x hxLower hxUpper
  refine (hX x hxLower hxUpper).trans ?_
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have hcoeff : 8 * C / J ≤ delta / 3 := by
    rw [div_le_iff₀ hJr]
    linarith
  exact mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg (by
    have hxNonneg : 0 ≤ x := by linarith [hxLower, hxUpper]
    linarith) theta)

end GafniTao

import Tao2026.TypeIIKernel

/-!
# Type II logarithmic exponent arithmetic

This module records the exact real-power bookkeeping behind the source's
high-frequency condition `F > log^(C A) P`.  It contains no exponential-sum
estimate: it converts a proved lower bound for `F` into the logarithmic saving
required after the Type II distance-kernel summation.
-/

namespace Tao2026

/-- The largest derivative order required by the source form of Vinogradov's
exponential-sum estimate. -/
noncomputable def vinogradovDerivativeCutoff (X F : ℝ) : ℕ :=
  10 * ⌈Real.log F / Real.log X⌉₊ + 1

/-- The ceiling in the source derivative cutoff costs strictly less than one.
This is the real-valued form used in the asymptotic range comparison. -/
theorem vinogradovDerivativeCutoff_cast_lt
    {X F : ℝ} (hX : 1 < X) (hF : 1 ≤ F) :
    (vinogradovDerivativeCutoff X F : ℝ) <
      10 * (Real.log F / Real.log X + 1) + 1 := by
  have hlogX : 0 < Real.log X := Real.log_pos hX
  have hlogF : 0 ≤ Real.log F := Real.log_nonneg hF
  have hratio : 0 ≤ Real.log F / Real.log X := div_nonneg hlogF hlogX.le
  have hceil := Nat.ceil_lt_add_one hratio
  unfold vinogradovDerivativeCutoff
  push_cast
  nlinarith

/-- Add a phase degree to the cutoff once the corresponding real ceiling
majorant fits inside the available derivative budget. -/
theorem vinogradovDerivativeCutoff_add_degree_cast_le
    {X F ℓ : ℝ} {j : ℕ} (hX : 1 < X) (hF : 1 ≤ F)
    (hbudget : 10 * (Real.log F / Real.log X + 1) + 1 + j ≤ ℓ) :
    (((vinogradovDerivativeCutoff X F + j : ℕ) : ℝ)) ≤ ℓ := by
  have hcut := vinogradovDerivativeCutoff_cast_lt hX hF
  push_cast
  linarith

/-- The source bounds for `log F` and `log X` give the precise power bound on
their ratio that controls the derivative cutoff. -/
theorem vinogradov_log_ratio_le
    {ℓ x u C c ε : ℝ} (hℓ : 1 ≤ ℓ) (hC : 0 ≤ C) (hc : 0 < c)
    (hxLower : c * ℓ ≤ x) (huUpper : u ≤ C * ℓ ^ (3 / 2 - ε)) :
    u / x ≤ (C / c) * ℓ ^ (1 / 2 - ε) := by
  have hℓpos : 0 < ℓ := zero_lt_one.trans_le hℓ
  have hcell : 0 < c * ℓ := mul_pos hc hℓpos
  have hx : 0 < x := hcell.trans_le hxLower
  have hcoef : 0 ≤ (C / c) * ℓ ^ (1 / 2 - ε) := by positivity
  have hpower : ℓ ^ (1 / 2 - ε) * ℓ = ℓ ^ (3 / 2 - ε) := by
    calc
      ℓ ^ (1 / 2 - ε) * ℓ =
          ℓ ^ (1 / 2 - ε) * ℓ ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = ℓ ^ ((1 / 2 - ε) + 1) := (Real.rpow_add hℓpos _ _).symm
      _ = ℓ ^ (3 / 2 - ε) := by congr 1; ring_nf
  rw [div_le_iff₀ hx]
  calc
    u ≤ C * ℓ ^ (3 / 2 - ε) := huUpper
    _ = ((C / c) * ℓ ^ (1 / 2 - ε)) * (c * ℓ) := by
      rw [← hpower]
      field_simp [ne_of_gt hc]
    _ ≤ ((C / c) * ℓ ^ (1 / 2 - ε)) * x :=
      mul_le_mul_of_nonneg_left hxLower hcoef

/-- The source cutoff contribution and the allowed phase degree together fit
below one full logarithmic derivative budget.  Constants are uniform in the
varying phase parameters. -/
theorem eventually_vinogradov_cutoff_real_budget
    {D ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ ℓ : ℝ in Filter.atTop,
      10 * (D * ℓ ^ (1 / 2 - ε) + 1) + 1 + ℓ ^ (1 / 2 : ℝ) ≤ ℓ := by
  have hhalfEps : 0 < 1 / 2 + ε := by linarith
  have hhalf : 0 < (1 / 2 : ℝ) := by norm_num
  filter_upwards [
    (tendsto_rpow_atTop hhalfEps).eventually
      (Filter.eventually_ge_atTop (30 * D)),
    (tendsto_rpow_atTop hhalf).eventually
      (Filter.eventually_ge_atTop 3),
    Filter.eventually_ge_atTop (33 : ℝ)] with ℓ hlarge hsqrt hℓ
  have hℓpos : 0 < ℓ := by linarith
  have hfirstProduct := mul_le_mul_of_nonneg_right hlarge
    (Real.rpow_nonneg hℓpos.le (1 / 2 - ε))
  have hfirstIdentity :
      ℓ ^ (1 / 2 + ε) * ℓ ^ (1 / 2 - ε) = ℓ := by
    rw [← Real.rpow_add hℓpos]
    rw [show 1 / 2 + ε + (1 / 2 - ε) = (1 : ℝ) by ring,
      Real.rpow_one]
  rw [hfirstIdentity] at hfirstProduct
  have hfirst : 10 * (D * ℓ ^ (1 / 2 - ε)) ≤ ℓ / 3 := by
    linarith
  have hsqrtProduct := mul_le_mul_of_nonneg_right hsqrt
    (Real.rpow_nonneg hℓpos.le (1 / 2 : ℝ))
  have hsqrtIdentity : ℓ ^ (1 / 2 : ℝ) * ℓ ^ (1 / 2 : ℝ) = ℓ := by
    rw [← Real.rpow_add hℓpos]
    norm_num
  rw [hsqrtIdentity] at hsqrtProduct
  have hsqrtThird : ℓ ^ (1 / 2 : ℝ) ≤ ℓ / 3 := by linarith
  have hconstant : (11 : ℝ) ≤ ℓ / 3 := by linarith
  linarith

/-- Pointwise source cutoff bound after inserting the scale-ratio estimate and
the allowed square-root logarithmic phase degree. -/
theorem vinogradovDerivativeCutoff_add_degree_le_log
    {P X F C c ε : ℝ} {j : ℕ}
    (hlog : 1 ≤ Real.log P) (hX : 1 < X) (hF : 1 ≤ F)
    (hC : 0 ≤ C) (hc : 0 < c)
    (hXlower : c * Real.log P ≤ Real.log X)
    (hFupper : Real.log F ≤ C * (Real.log P) ^ (3 / 2 - ε))
    (hj : (j : ℝ) ≤ (Real.log P) ^ (1 / 2 : ℝ))
    (hbudget : 10 * ((C / c) * (Real.log P) ^ (1 / 2 - ε) + 1) + 1 +
      (Real.log P) ^ (1 / 2 : ℝ) ≤ Real.log P) :
    (((vinogradovDerivativeCutoff X F + j : ℕ) : ℝ)) ≤ Real.log P := by
  have hratio : Real.log F / Real.log X ≤
      (C / c) * (Real.log P) ^ (1 / 2 - ε) :=
    vinogradov_log_ratio_le hlog hC hc hXlower hFupper
  have hmajorant : 10 * (Real.log F / Real.log X + 1) + 1 + (j : ℝ) ≤
      10 * ((C / c) * (Real.log P) ^ (1 / 2 - ε) + 1) + 1 +
        (Real.log P) ^ (1 / 2 : ℝ) := by
    gcongr
  exact vinogradovDerivativeCutoff_add_degree_cast_le hX hF
    (hmajorant.trans hbudget)

/-- Uniform eventual source cutoff bound.  It is simultaneous in `X`, `F`,
and `j`, so it can be applied to every transformed Type II correlation pair. -/
theorem eventually_vinogradovDerivativeCutoff_add_degree_le_log
    {C c ε : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hε : 0 < ε) :
    ∀ᶠ P : ℝ in Filter.atTop, ∀ X F : ℝ, ∀ j : ℕ,
      1 < X → 1 ≤ F →
      c * Real.log P ≤ Real.log X →
      Real.log F ≤ C * (Real.log P) ^ (3 / 2 - ε) →
      (j : ℝ) ≤ (Real.log P) ^ (1 / 2 : ℝ) →
      (((vinogradovDerivativeCutoff X F + j : ℕ) : ℝ)) ≤ Real.log P := by
  have hbudget := eventually_vinogradov_cutoff_real_budget
    (D := C / c) hε
  filter_upwards [Real.tendsto_log_atTop.eventually hbudget,
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (1 : ℝ))]
      with P hbudgetP hlog
  intro X F j hX hF hXlower hFupper hj
  exact vinogradovDerivativeCutoff_add_degree_le_log hlog hX hF hC hc
    hXlower hFupper hj hbudgetP

/-- A power lower bound for the frequency absorbs a positive logarithmic
factor against `F⁻ᶜ`, with every exponent displayed explicitly. -/
theorem rpow_mul_frequencyDecay_le
    {ℓ F b c d t : ℝ} (hℓ : 1 ≤ ℓ) (hFd : ℓ ^ d ≤ F)
    (hc : 0 ≤ c) (hexponent : b + t ≤ d * c) :
    ℓ ^ b * F ^ (-c) ≤ ℓ ^ (-t) := by
  have hℓpos : 0 < ℓ := zero_lt_one.trans_le hℓ
  have hbasepos : 0 < ℓ ^ d := Real.rpow_pos_of_pos hℓpos d
  have hdecay : F ^ (-c) ≤ (ℓ ^ d) ^ (-c) :=
    Real.rpow_le_rpow_of_nonpos hbasepos hFd (neg_nonpos.mpr hc)
  calc
    ℓ ^ b * F ^ (-c) ≤ ℓ ^ b * (ℓ ^ d) ^ (-c) :=
      mul_le_mul_of_nonneg_left hdecay
        (Real.rpow_nonneg (zero_le_one.trans hℓ) _)
    _ = ℓ ^ (b - d * c) := by
      rw [← Real.rpow_mul (zero_le_one.trans hℓ) d (-c),
        ← Real.rpow_add hℓpos]
      congr 1
      ring
    _ ≤ ℓ ^ (-t) :=
      Real.rpow_le_rpow_of_exponent_le hℓ (by linarith)

/-- Direct exponent subtraction for two powers of the same logarithmic base. -/
theorem rpow_mul_rpow_neg_le
    {ℓ b d t : ℝ} (hℓ : 1 ≤ ℓ) (hexponent : b + t ≤ d) :
    ℓ ^ b * ℓ ^ (-d) ≤ ℓ ^ (-t) := by
  have hℓpos : 0 < ℓ := zero_lt_one.trans_le hℓ
  rw [← Real.rpow_add hℓpos]
  exact Real.rpow_le_rpow_of_exponent_le hℓ (by linarith)

/-- The strict high-frequency inequality used in the source supplies the weak
power lower bound needed by `rpow_mul_frequencyDecay_le`. -/
theorem rpow_mul_frequencyDecay_le_of_lt
    {ℓ F b c d t : ℝ} (hℓ : 1 ≤ ℓ) (hFd : ℓ ^ d < F)
    (hc : 0 ≤ c) (hexponent : b + t ≤ d * c) :
    ℓ ^ b * F ^ (-c) ≤ ℓ ^ (-t) :=
  rpow_mul_frequencyDecay_le hℓ hFd.le hc hexponent

/-- Source-facing specialization with the logarithmic base `log P`.  The
explicit threshold `exp 1 ≤ P` is exactly what guarantees `1 ≤ log P`. -/
theorem log_rpow_mul_frequencyDecay_le
    {P F b c d t : ℝ} (hP : Real.exp 1 ≤ P)
    (hFd : (Real.log P) ^ d ≤ F) (hc : 0 ≤ c)
    (hexponent : b + t ≤ d * c) :
    (Real.log P) ^ b * F ^ (-c) ≤ (Real.log P) ^ (-t) := by
  have hPpos : 0 < P := (Real.exp_pos 1).trans_le hP
  have hlog : 1 ≤ Real.log P :=
    (Real.le_log_iff_exp_le hPpos).2 hP
  exact rpow_mul_frequencyDecay_le hlog hFd hc hexponent

/-- Strict source high-frequency version of
`log_rpow_mul_frequencyDecay_le`. -/
theorem log_rpow_mul_frequencyDecay_le_of_lt
    {P F b c d t : ℝ} (hP : Real.exp 1 ≤ P)
    (hFd : (Real.log P) ^ d < F) (hc : 0 ≤ c)
    (hexponent : b + t ≤ d * c) :
    (Real.log P) ^ b * F ^ (-c) ≤ (Real.log P) ^ (-t) :=
  log_rpow_mul_frequencyDecay_le hP hFd.le hc hexponent

/-- The stretched-exponential factor produced by the high-scale Vinogradov
estimate beats every prescribed logarithmic power.  This isolates the exact
asymptotic conversion used after its `exp (-c (log P)^ρ)` conclusion. -/
theorem eventually_exp_neg_log_rpow_le_log_rpow_neg
    {c ρ A : ℝ} (hc : 0 < c) (hρ : 0 < ρ) :
    ∀ᶠ P : ℝ in Filter.atTop,
      Real.exp (-c * (Real.log P) ^ ρ) ≤ (Real.log P) ^ (-A) := by
  have hsmall :
      (fun x : ℝ => Real.exp (-c * x ^ ρ)) =o[Filter.atTop]
        (fun x : ℝ => (x ^ ρ) ^ (-A / ρ)) := by
    simpa only [Function.comp_apply] using
      (isLittleO_exp_neg_mul_rpow_atTop hc (-A / ρ)).comp_tendsto
        (tendsto_rpow_atTop hρ)
  have hxevent : ∀ᶠ x : ℝ in Filter.atTop,
      Real.exp (-c * x ^ ρ) ≤ x ^ (-A) := by
    filter_upwards [hsmall.eventuallyLE, Filter.eventually_ge_atTop (1 : ℝ)] with x hx hxone
    have hxpos : 0 < x := zero_lt_one.trans_le hxone
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hxpos ρ) _)] at hx
    have hpower : (x ^ ρ) ^ (-A / ρ) = x ^ (-A) := by
      rw [← Real.rpow_mul hxpos.le]
      congr 1
      field_simp
    simpa only [hpower] using hx
  exact Real.tendsto_log_atTop.eventually hxevent

/-- Polynomial logarithmic losses are absorbed by the same stretched-
exponential Vinogradov factor. -/
theorem eventually_log_rpow_mul_exp_neg_log_rpow_le_log_rpow_neg
    {c ρ A b : ℝ} (hc : 0 < c) (hρ : 0 < ρ) :
    ∀ᶠ P : ℝ in Filter.atTop,
      (Real.log P) ^ b * Real.exp (-c * (Real.log P) ^ ρ) ≤
        (Real.log P) ^ (-A) := by
  filter_upwards [eventually_exp_neg_log_rpow_le_log_rpow_neg
      (A := A + b) hc hρ,
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (1 : ℝ))]
      with P hdecay hlog
  have hlognonneg : 0 ≤ Real.log P := zero_le_one.trans hlog
  calc
    (Real.log P) ^ b * Real.exp (-c * (Real.log P) ^ ρ) ≤
        (Real.log P) ^ b * (Real.log P) ^ (-(A + b)) :=
      mul_le_mul_of_nonneg_left hdecay (Real.rpow_nonneg hlognonneg _)
    _ = (Real.log P) ^ (-A) := by
      rw [← Real.rpow_add (zero_lt_one.trans_le hlog)]
      congr 1
      ring

/-- A fixed multiple of `log ℓ`, divided by any positive real power of `ℓ`,
tends below the numerical threshold in Vinogradov's side condition. -/
theorem eventually_const_mul_log_div_rpow_lt_one_div_thousand
    {D ρ : ℝ} (hD : 0 ≤ D) (hρ : 0 < ρ) :
    ∀ᶠ ℓ : ℝ in Filter.atTop,
      D * Real.log ℓ / ℓ ^ ρ < 1 / 1000 := by
  have hsmall :=
    (isLittleO_log_rpow_atTop hρ).const_mul_left (1000 * D)
  have hpositive : ∀ᶠ ℓ : ℝ in Filter.atTop,
      0 < ‖ℓ ^ ρ‖ := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with ℓ hℓ
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hℓ ρ)]
    exact Real.rpow_pos_of_pos hℓ ρ
  filter_upwards [hsmall.eventuallyLT_norm_of_eventually_pos hpositive,
    Filter.eventually_ge_atTop (1 : ℝ)] with ℓ hlt hℓ
  have hℓpos : 0 < ℓ := zero_lt_one.trans_le hℓ
  have hlog0 : 0 ≤ Real.log ℓ := Real.log_nonneg hℓ
  have hleft0 : 0 ≤ 1000 * D * Real.log ℓ := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hleft0,
    Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hℓpos ρ)] at hlt
  rw [div_lt_iff₀ (Real.rpow_pos_of_pos hℓpos ρ)]
  calc
    D * Real.log ℓ = (1 / 1000 : ℝ) * (1000 * D * Real.log ℓ) := by ring
    _ < (1 / 1000 : ℝ) * ℓ ^ ρ :=
      mul_lt_mul_of_pos_left hlt (by norm_num)

/-- Pointwise reduction of Vinogradov's numerical side condition to the
standard asymptotic ratio `log ℓ / ℓ^(2ε)`.  Here `x=log X` and `u=log F`;
all constants remain explicit. -/
theorem vinogradov_alpha_condition_of_log_bounds
    {ℓ x u A C c ε : ℝ} (hℓ : 1 ≤ ℓ) (hu : 0 ≤ u)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hc : 0 < c)
    (hxLower : c * ℓ ≤ x)
    (huUpper : u ≤ C * ℓ ^ (3 / 2 - ε))
    (hsmall : (4 * A * C ^ 2 / c ^ 3) * Real.log ℓ /
      ℓ ^ (2 * ε) < 1 / 1000) :
    Real.log (ℓ ^ (4 * A)) * u ^ 2 / x ^ 3 < 1 / 1000 := by
  have hℓpos : 0 < ℓ := zero_lt_one.trans_le hℓ
  have hlog0 : 0 ≤ Real.log ℓ := Real.log_nonneg hℓ
  have hmajorant0 : 0 ≤ C * ℓ ^ (3 / 2 - ε) := by positivity
  have huSq : u ^ 2 ≤ C ^ 2 * ℓ ^ (3 - 2 * ε) := by
    have hsquare := (sq_le_sq₀ hu hmajorant0).2 huUpper
    calc
      u ^ 2 ≤ (C * ℓ ^ (3 / 2 - ε)) ^ 2 := hsquare
      _ = C ^ 2 * ℓ ^ (3 - 2 * ε) := by
        rw [mul_pow,
          show (ℓ ^ (3 / 2 - ε)) ^ 2 =
            (ℓ ^ (3 / 2 - ε)) ^ (2 : ℝ) from
              (Real.rpow_natCast _ 2).symm,
          ← Real.rpow_mul hℓpos.le]
        congr 1
        ring_nf
  have hlogAlpha : Real.log (ℓ ^ (4 * A)) = 4 * A * Real.log ℓ :=
    Real.log_rpow hℓpos (4 * A)
  have hnum : Real.log (ℓ ^ (4 * A)) * u ^ 2 ≤
      (4 * A * Real.log ℓ) * (C ^ 2 * ℓ ^ (3 - 2 * ε)) := by
    rw [hlogAlpha]
    exact mul_le_mul_of_nonneg_left huSq (by positivity)
  have hcell : 0 < c * ℓ := mul_pos hc hℓpos
  have hden : (c * ℓ) ^ 3 ≤ x ^ 3 :=
    pow_le_pow_left₀ hcell.le hxLower 3
  have hfrac : Real.log (ℓ ^ (4 * A)) * u ^ 2 / x ^ 3 ≤
      (4 * A * Real.log ℓ) * (C ^ 2 * ℓ ^ (3 - 2 * ε)) /
        (c * ℓ) ^ 3 := by
    exact div_le_div₀ (by positivity) hnum (pow_pos hcell 3) hden
  have hidentity :
      (4 * A * Real.log ℓ) * (C ^ 2 * ℓ ^ (3 - 2 * ε)) /
          (c * ℓ) ^ 3 =
        (4 * A * C ^ 2 / c ^ 3) * Real.log ℓ / ℓ ^ (2 * ε) := by
    rw [mul_pow, Real.rpow_sub hℓpos]
    field_simp [ne_of_gt hc, ne_of_gt hℓpos,
      ne_of_gt (Real.rpow_pos_of_pos hℓpos (2 * ε))]
    exact congrArg (fun z : ℝ => A * Real.log ℓ * C ^ 2 * z)
      (Real.rpow_natCast ℓ 3)
  exact hfrac.trans_lt (by simpa only [hidentity] using hsmall)

/-- The numerical smallness condition in Vinogradov's estimate is automatic
under the source growth bound for `F` and a fixed positive-power lower bound
for `X`.  The source choice `α=(log P)^(4A)` is substituted literally. -/
theorem eventually_vinogradov_alpha_condition_of_log_bounds
    {A C c ε : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hc : 0 < c)
    (hε : 0 < ε) :
    ∀ᶠ P : ℝ in Filter.atTop, ∀ X F : ℝ,
      0 ≤ Real.log F →
      c * Real.log P ≤ Real.log X →
      Real.log F ≤ C * (Real.log P) ^ (3 / 2 - ε) →
      Real.log ((Real.log P) ^ (4 * A)) * (Real.log F) ^ 2 /
          (Real.log X) ^ 3 < 1 / 1000 := by
  have hD : 0 ≤ 4 * A * C ^ 2 / c ^ 3 := by positivity
  have hρ : 0 < 2 * ε := by positivity
  have hratio := eventually_const_mul_log_div_rpow_lt_one_div_thousand hD hρ
  filter_upwards [Real.tendsto_log_atTop.eventually hratio,
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (1 : ℝ))]
      with P hsmall hlog
  intro X F hFlog hXlower hFupper
  exact vinogradov_alpha_condition_of_log_bounds hlog hFlog hA hC hc
    hXlower hFupper hsmall

/-- Parameter arithmetic behind the source's high-scale Vinogradov exponent.
If `log F` is at most `C ℓ^(3/2-ε)`, then the exponent
`ℓ^3/(log F)^2` retains the stretched-log power `ℓ^(2ε)/C^2`. -/
theorem vinogradovExponent_lower_of_logScale
    {ℓ u C ε : ℝ} (hℓ : 1 ≤ ℓ) (hu : 0 < u) (hC : 0 < C)
    (hupper : u ≤ C * ℓ ^ (3 / 2 - ε)) :
    (1 / C ^ 2) * ℓ ^ (2 * ε) ≤ ℓ ^ (3 : ℝ) / u ^ 2 := by
  have hℓpos : 0 < ℓ := zero_lt_one.trans_le hℓ
  have hmajorantPos : 0 < C * ℓ ^ (3 / 2 - ε) :=
    mul_pos hC (Real.rpow_pos_of_pos hℓpos _)
  have hsquare : u ^ 2 ≤ (C * ℓ ^ (3 / 2 - ε)) ^ 2 :=
    (sq_le_sq₀ hu.le hmajorantPos.le).2 hupper
  rw [le_div_iff₀ (sq_pos_of_pos hu)]
  calc
    (1 / C ^ 2) * ℓ ^ (2 * ε) * u ^ 2 ≤
        (1 / C ^ 2) * ℓ ^ (2 * ε) *
          (C * ℓ ^ (3 / 2 - ε)) ^ 2 :=
      mul_le_mul_of_nonneg_left hsquare
        (mul_nonneg (by positivity) (Real.rpow_nonneg hℓpos.le _))
    _ = ℓ ^ (3 : ℝ) := by
      rw [mul_pow]
      field_simp
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul hℓpos.le, ← Real.rpow_add hℓpos]
      congr 1
      ring

/-- Exponential form of `vinogradovExponent_lower_of_logScale`: the source's
Vinogradov decay is bounded by an explicit stretched-log exponential. -/
theorem vinogradovExp_le_stretchedLog_of_logScale
    {ℓ u C ε c : ℝ} (hℓ : 1 ≤ ℓ) (hu : 0 < u) (hC : 0 < C)
    (hc : 0 ≤ c) (hupper : u ≤ C * ℓ ^ (3 / 2 - ε)) :
    Real.exp (-c * (ℓ ^ (3 : ℝ) / u ^ 2)) ≤
      Real.exp (-(c / C ^ 2) * ℓ ^ (2 * ε)) := by
  have hscale := vinogradovExponent_lower_of_logScale hℓ hu hC hupper
  apply Real.exp_le_exp.mpr
  have hmul := mul_le_mul_of_nonpos_left hscale (neg_nonpos.mpr hc)
  calc
    -c * (ℓ ^ (3 : ℝ) / u ^ 2) ≤
        -c * ((1 / C ^ 2) * ℓ ^ (2 * ε)) := hmul
    _ = -(c / C ^ 2) * ℓ ^ (2 * ε) := by ring

/-- Uniform source-facing logarithmic absorption for the Vinogradov factor.
The auxiliary quantity `u` represents `log F` and may vary with `P`; its
source growth bound is consumed pointwise. -/
theorem eventually_log_rpow_mul_vinogradovExp_le_log_rpow_neg
    {C ε c A b : ℝ} (hC : 0 < C) (hε : 0 < ε) (hc : 0 < c) :
    ∀ᶠ P : ℝ in Filter.atTop, ∀ u : ℝ, 0 < u →
      u ≤ C * (Real.log P) ^ (3 / 2 - ε) →
      (Real.log P) ^ b *
          Real.exp (-c * ((Real.log P) ^ (3 : ℝ) / u ^ 2)) ≤
        (Real.log P) ^ (-A) := by
  have hcC : 0 < c / C ^ 2 := div_pos hc (sq_pos_of_pos hC)
  have htwoε : 0 < 2 * ε := by positivity
  filter_upwards [eventually_log_rpow_mul_exp_neg_log_rpow_le_log_rpow_neg
      (A := A) (b := b) hcC htwoε,
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (1 : ℝ))]
      with P hdecay hlog
  intro u hu hupper
  have hvin := vinogradovExp_le_stretchedLog_of_logScale
    hlog hu hC hc.le hupper
  calc
    (Real.log P) ^ b *
        Real.exp (-c * ((Real.log P) ^ (3 : ℝ) / u ^ 2)) ≤
      (Real.log P) ^ b *
        Real.exp (-(c / C ^ 2) * (Real.log P) ^ (2 * ε)) :=
      mul_le_mul_of_nonneg_left hvin
        (Real.rpow_nonneg (zero_le_one.trans hlog) _)
    _ ≤ (Real.log P) ^ (-A) := hdecay

/-- Turn a source-sized exponential parameter into the logarithmic upper
bound consumed by the Vinogradov exponent arithmetic.  The multiplier hidden
by big-O notation is retained explicitly as `|log C|+1`. -/
theorem log_le_absLog_add_one_mul_rpow_of_le_mul_exp_rpow
    {F C ℓ a : ℝ} (hF : 0 < F) (hC : 0 < C) (hℓ : 1 ≤ ℓ)
    (ha : 0 ≤ a) (hupper : F ≤ C * Real.exp (ℓ ^ a)) :
    Real.log F ≤ (|Real.log C| + 1) * ℓ ^ a := by
  have hmajorantPos : 0 < C * Real.exp (ℓ ^ a) :=
    mul_pos hC (Real.exp_pos _)
  have hlogUpper : Real.log F ≤ Real.log (C * Real.exp (ℓ ^ a)) :=
    Real.strictMonoOn_log.monotoneOn hF hmajorantPos hupper
  rw [Real.log_mul hC.ne' (Real.exp_ne_zero _), Real.log_exp] at hlogUpper
  have hpowOne : (1 : ℝ) ≤ ℓ ^ a := Real.one_le_rpow hℓ ha
  have habsMul : |Real.log C| ≤ |Real.log C| * ℓ ^ a := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hpowOne (abs_nonneg (Real.log C))
  calc
    Real.log F ≤ Real.log C + ℓ ^ a := hlogUpper
    _ ≤ |Real.log C| + ℓ ^ a :=
      add_le_add (le_abs_self (Real.log C)) le_rfl
    _ ≤ (|Real.log C| + 1) * ℓ ^ a := by
      nlinarith

/-- Primitive source-parameter form of the Vinogradov smallness condition.
The bound `F ≤ C exp((log P)^(3/2-ε))` is converted internally to the required
logarithmic estimate, with multiplier `|log C|+1`. -/
theorem eventually_vinogradov_alpha_condition_of_parameterBound
    {A C c ε : ℝ} (hA : 0 ≤ A) (hC : 0 < C) (hc : 0 < c)
    (hε : 0 < ε) (ha : 0 ≤ 3 / 2 - ε) :
    ∀ᶠ P : ℝ in Filter.atTop, ∀ X F : ℝ, 1 < F →
      F ≤ C * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
      c * Real.log P ≤ Real.log X →
      Real.log ((Real.log P) ^ (4 * A)) * (Real.log F) ^ 2 /
          (Real.log X) ^ 3 < 1 / 1000 := by
  have hC' : 0 ≤ |Real.log C| + 1 := by positivity
  have hvin := eventually_vinogradov_alpha_condition_of_log_bounds
    hA hC' hc hε
  filter_upwards [hvin,
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (1 : ℝ))]
      with P hvinP hlog
  intro X F hF hFupper hXlower
  apply hvinP X F (Real.log_nonneg hF.le) hXlower
  exact log_le_absLog_add_one_mul_rpow_of_le_mul_exp_rpow
    (zero_lt_one.trans hF) hC hlog ha hFupper

/-- Primitive source-parameter form of the full derivative-cutoff budget.
This combines the exact ceiling cutoff with the exponential bound on `F` and
the source degree restriction `j≤(log P)^(1/2)`. -/
theorem eventually_vinogradovDerivativeCutoff_add_degree_le_log_of_parameterBound
    {C c ε : ℝ} (hC : 0 < C) (hc : 0 < c) (hε : 0 < ε)
    (ha : 0 ≤ 3 / 2 - ε) :
    ∀ᶠ P : ℝ in Filter.atTop, ∀ X F : ℝ, ∀ j : ℕ,
      1 < X → 1 < F →
      F ≤ C * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
      c * Real.log P ≤ Real.log X →
      (j : ℝ) ≤ (Real.log P) ^ (1 / 2 : ℝ) →
      (((vinogradovDerivativeCutoff X F + j : ℕ) : ℝ)) ≤ Real.log P := by
  have hC' : 0 ≤ |Real.log C| + 1 := by positivity
  have hcutoff := eventually_vinogradovDerivativeCutoff_add_degree_le_log
    hC' hc hε
  filter_upwards [hcutoff,
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (1 : ℝ))]
      with P hcutoffP hlog
  intro X F j hX hF hFupper hXlower hj
  apply hcutoffP X F j hX hF.le hXlower
  · exact log_le_absLog_add_one_mul_rpow_of_le_mul_exp_rpow
      (zero_lt_one.trans hF) hC hlog ha hFupper
  · exact hj

/-- Complete parameter-to-saving bridge for the source's high-scale branch.
An explicit `O(exp(log^(3/2-ε) P))` bound for `F`, together with `F>1`, is
converted into arbitrary logarithmic saving for the Vinogradov exponential. -/
theorem eventually_log_rpow_mul_vinogradovExp_of_parameterBound
    {C ε c A b : ℝ} (hC : 0 < C) (hε : 0 < ε) (hc : 0 < c)
    (ha : 0 ≤ 3 / 2 - ε) :
    ∀ᶠ P : ℝ in Filter.atTop, ∀ F : ℝ, 1 < F →
      F ≤ C * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
      (Real.log P) ^ b *
          Real.exp (-c * ((Real.log P) ^ (3 : ℝ) / (Real.log F) ^ 2)) ≤
        (Real.log P) ^ (-A) := by
  have hC' : 0 < |Real.log C| + 1 := by positivity
  filter_upwards [eventually_log_rpow_mul_vinogradovExp_le_log_rpow_neg
      (C := |Real.log C| + 1) (ε := ε) (c := c) (A := A) (b := b)
        hC' hε hc,
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (1 : ℝ))]
      with P hvin hlog
  intro F hF hupper
  apply hvin (Real.log F) (Real.log_pos hF)
  exact log_le_absLog_add_one_mul_rpow_of_le_mul_exp_rpow
    (zero_lt_one.trans hF) hC hlog ha hupper

/-- The source choices `α=ℓ^(4A)` and `q=ℓ^(-3A)` automatically satisfy all
elementary coefficient conditions for derivative orders bounded by `ℓ`, once
`ℓ^A≥10`. -/
theorem vinogradov_log_power_parameters
    {ℓ A : ℝ} {R j : ℕ} (hℓ : 1 ≤ ℓ) (hA : 1 / 4 ≤ A)
    (hRj : (((R + j : ℕ) : ℝ)) ≤ ℓ) (hten : 10 ≤ ℓ ^ A) :
    let α := ℓ ^ (4 * A)
    let q := ℓ ^ (-3 * A)
    0 < q ∧ q ≤ 1 ∧ 1 ≤ α ∧ (((R + j : ℕ) : ℝ)) ≤ α ∧
      10 ≤ α * q := by
  dsimp only
  have hℓpos : 0 < ℓ := zero_lt_one.trans_le hℓ
  have hApos : 0 < A := by linarith
  have hfourA : 1 ≤ 4 * A := by linarith
  have hneg : -3 * A ≤ 0 := by linarith
  have hqpos : 0 < ℓ ^ (-3 * A) := Real.rpow_pos_of_pos hℓpos _
  have hqOne : ℓ ^ (-3 * A) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hℓ hneg
  have hαOne : 1 ≤ ℓ ^ (4 * A) :=
    Real.one_le_rpow hℓ (by positivity)
  have hℓα : ℓ ≤ ℓ ^ (4 * A) := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hℓ hfourA)
  have hproduct : ℓ ^ (4 * A) * ℓ ^ (-3 * A) = ℓ ^ A := by
    rw [← Real.rpow_add hℓpos]
    congr 1
    ring
  exact ⟨hqpos, hqOne, hαOne, hRj.trans hℓα, by simpa only [hproduct] using hten⟩

/-- Eventual source-facing form of `vinogradov_log_power_parameters`.  The
order inequality remains explicit because its cutoff depends on the varying
phase scale, while every purely logarithmic side condition is discharged. -/
theorem eventually_vinogradov_log_power_parameters
    {A : ℝ} (hA : 1 / 4 ≤ A) :
    ∀ᶠ P : ℝ in Filter.atTop, ∀ R j : ℕ,
      (((R + j : ℕ) : ℝ)) ≤ Real.log P →
      let α := (Real.log P) ^ (4 * A)
      let q := (Real.log P) ^ (-3 * A)
      0 < q ∧ q ≤ 1 ∧ 1 ≤ α ∧ (((R + j : ℕ) : ℝ)) ≤ α ∧
        10 ≤ α * q := by
  have hApos : 0 < A := by linarith
  have hten : ∀ᶠ P : ℝ in Filter.atTop, 10 ≤ (Real.log P) ^ A :=
    ((tendsto_rpow_atTop hApos).comp Real.tendsto_log_atTop).eventually
      (Filter.eventually_ge_atTop 10)
  filter_upwards [hten,
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (1 : ℝ))]
      with P htenP hlog
  intro R j hRj
  exact vinogradov_log_power_parameters hlog hA hRj htenP

/-- Uniform source-facing package for the high-scale Vinogradov branch.  Under
the primitive parameter bound for the transformed phase scale, all conditions
which only require taking `P` large are available simultaneously: the base
logarithm is at least one, the source amplitude has reached ten, the exact
ceiling cutoff (including the polynomial degree) fits below `log P`, and the
source's `10⁻³` smallness condition holds. -/
theorem eventually_sourceVinogradov_parameterConditions_of_parameterBound
    {A C c ε : ℝ} (hA : 1 / 4 ≤ A) (hC : 0 < C) (hc : 0 < c)
    (hε : 0 < ε) (ha : 0 ≤ 3 / 2 - ε) :
    ∀ᶠ P : ℝ in Filter.atTop,
      1 ≤ Real.log P ∧ 10 ≤ (Real.log P) ^ A ∧
        ∀ X F : ℝ, ∀ j : ℕ,
          1 < X → 1 < F →
          F ≤ C * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
          c * Real.log P ≤ Real.log X →
          (j : ℝ) ≤ (Real.log P) ^ (1 / 2 : ℝ) →
          (((vinogradovDerivativeCutoff X F + j : ℕ) : ℝ)) ≤ Real.log P ∧
            Real.log ((Real.log P) ^ (4 * A)) * (Real.log F) ^ 2 /
                (Real.log X) ^ 3 < 1 / 1000 := by
  have hA0 : 0 ≤ A := by linarith
  have hApos : 0 < A := by linarith
  have hcutoff :=
    eventually_vinogradovDerivativeCutoff_add_degree_le_log_of_parameterBound
      hC hc hε ha
  have hsmall := eventually_vinogradov_alpha_condition_of_parameterBound
    hA0 hC hc hε ha
  have hten : ∀ᶠ P : ℝ in Filter.atTop, 10 ≤ (Real.log P) ^ A :=
    ((tendsto_rpow_atTop hApos).comp Real.tendsto_log_atTop).eventually
      (Filter.eventually_ge_atTop 10)
  filter_upwards [hcutoff, hsmall, hten,
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (1 : ℝ))]
      with P hcutoffP hsmallP htenP hlogP
  refine ⟨hlogP, htenP, ?_⟩
  intro X F j hX hF hFupper hXlower hj
  exact ⟨hcutoffP X F j hX hF hFupper hXlower hj,
    hsmallP X F hF hFupper hXlower⟩

/-- Quadratic high-scale specialization of the uniform source parameter
package.  The condition `X⁴ ≤ F` supplies `F>1`, and the fixed degree two is
eventually below `(log P)^(1/2)`, so the conclusion is exactly the collection
of asymptotic hypotheses consumed by the Type II Vinogradov estimate. -/
theorem eventually_sourceVinogradov_quadraticParameterConditions_of_parameterBound
    {A C c ε : ℝ} (hA : 1 / 4 ≤ A) (hC : 0 < C) (hc : 0 < c)
    (hε : 0 < ε) (ha : 0 ≤ 3 / 2 - ε) :
    ∀ᶠ P : ℝ in Filter.atTop, ∀ X F : ℝ,
      2 ≤ X → X ^ 4 ≤ F →
      F ≤ C * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
      c * Real.log P ≤ Real.log X →
      1 ≤ Real.log P ∧ 10 ≤ (Real.log P) ^ A ∧
        (((vinogradovDerivativeCutoff X F + 2 : ℕ) : ℝ)) ≤ Real.log P ∧
          Real.log ((Real.log P) ^ (4 * A)) * (Real.log F) ^ 2 /
              (Real.log X) ^ 3 < 1 / 1000 := by
  have hparameters :=
    eventually_sourceVinogradov_parameterConditions_of_parameterBound
      hA hC hc hε ha
  have htwo : ∀ᶠ P : ℝ in Filter.atTop,
      (2 : ℝ) ≤ (Real.log P) ^ (1 / 2 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
      Real.tendsto_log_atTop).eventually (Filter.eventually_ge_atTop 2)
  filter_upwards [hparameters, htwo] with P hparametersP htwoP
  intro X F hX hFhigh hFupper hXlower
  have hF : 1 < F := by
    calc
      (1 : ℝ) < 2 ^ 4 := by norm_num
      _ ≤ X ^ 4 := pow_le_pow_left₀ (by norm_num) hX 4
      _ ≤ F := hFhigh
  obtain ⟨hlogP, htenP, hparametersP⟩ := hparametersP
  obtain ⟨hcutoff, hsmall⟩ :=
    hparametersP X F 2 (by linarith) hF hFupper hXlower htwoP
  exact ⟨hlogP, htenP, hcutoff, hsmall⟩

/-- The complete logarithmic Vinogradov component envelope, normalized by its
interval scale, has arbitrary logarithmic saving.  Besides the principal
stretched-exponential term this absorbs both critical-deletion contributions.
The inequality `T+2≤3A` is the exact budget used here for the deletion width
`(log P)^(-3A)`. -/
theorem eventually_sourceVinogradov_logEnvelope_le
    {C₀ C₁ c ε A T : ℝ} (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hc : 0 < c) (hε : 0 < ε) (ha : 0 ≤ 3 / 2 - ε)
    (hAT : T + 2 ≤ 3 * A) :
    ∀ᶠ P : ℝ in Filter.atTop, ∀ X F : ℝ,
      2 ≤ X → X ^ 4 ≤ F →
      F ≤ C₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
      c * Real.log P ≤ Real.log X →
      (2 * Real.log P + 1) *
          (C₁ * (Real.log P) ^ (4 * A) * X * Real.exp
            (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
              (Real.log F) ^ 2)) +
        Real.log P *
          (16 * X * (Real.log P) ^ (-3 * A) + Real.log P + 1) ≤
        3 * X * (Real.log P) ^ (-T) := by
  have hdecayConstant : 0 < (2 : ℝ) ^ (-18 : ℝ) * c ^ 3 := by positivity
  have hprincipal :=
    eventually_log_rpow_mul_vinogradovExp_of_parameterBound
      (C := C₀) (ε := ε) (c := (2 : ℝ) ^ (-18 : ℝ) * c ^ 3)
        (A := T + 1) (b := 4 * A + 1) hC₀ hε hdecayConstant ha
  have hendpoint :=
    eventually_log_rpow_mul_exp_neg_log_rpow_le_log_rpow_neg
      (c := c) (ρ := 1) (A := T) (b := 3) hc (by norm_num)
  filter_upwards [hprincipal, hendpoint,
    Real.tendsto_log_atTop.eventually
      (Filter.eventually_ge_atTop (max (max (3 * C₁) 16) 2))]
      with P hprincipalP hendpointP hlogLarge
  intro X F hX hFhigh hFupper hXlower
  have hlog : 2 ≤ Real.log P := le_trans (le_max_right _ _) hlogLarge
  have hlogOne : 1 ≤ Real.log P := by linarith
  have hlogPos : 0 < Real.log P := by linarith
  have hcoef : 3 * C₁ ≤ Real.log P :=
    le_trans (le_max_left _ 16) (le_trans (le_max_left _ 2) hlogLarge)
  have hsixteen : (16 : ℝ) ≤ Real.log P :=
    le_trans (le_max_right (3 * C₁) 16) (le_trans (le_max_left _ 2) hlogLarge)
  have hXpos : 0 < X := by linarith
  have hF : 1 < F := by
    calc
      (1 : ℝ) < 2 ^ 4 := by norm_num
      _ ≤ X ^ 4 := pow_le_pow_left₀ (by norm_num) hX 4
      _ ≤ F := hFhigh
  have hlogFpos : 0 < Real.log F := Real.log_pos hF
  have hlogXpos : 0 < Real.log X := by
    have : 0 < c * Real.log P := mul_pos hc hlogPos
    linarith
  have hcube : c ^ 3 * (Real.log P) ^ 3 ≤ (Real.log X) ^ 3 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (mul_nonneg hc.le hlogPos.le) hXlower 3
  have hratio : c ^ 3 * ((Real.log P) ^ 3 / (Real.log F) ^ 2) ≤
      (Real.log X) ^ 3 / (Real.log F) ^ 2 := by
    calc
      c ^ 3 * ((Real.log P) ^ 3 / (Real.log F) ^ 2) =
          (c ^ 3 * (Real.log P) ^ 3) / (Real.log F) ^ 2 := by ring
      _ ≤ (Real.log X) ^ 3 / (Real.log F) ^ 2 :=
        div_le_div_of_nonneg_right hcube (sq_nonneg (Real.log F))
  have hratioRpow : c ^ 3 *
        ((Real.log P) ^ (3 : ℝ) / (Real.log F) ^ 2) ≤
      (Real.log X) ^ 3 / (Real.log F) ^ 2 := by
    have hpowEq : (Real.log P) ^ (3 : ℝ) = (Real.log P) ^ (3 : ℕ) :=
      Real.rpow_natCast (Real.log P) 3
    calc
      c ^ 3 * ((Real.log P) ^ (3 : ℝ) / (Real.log F) ^ 2) =
          c ^ 3 * ((Real.log P) ^ (3 : ℕ) / (Real.log F) ^ 2) := by
            rw [hpowEq]
      _ ≤ (Real.log X) ^ 3 / (Real.log F) ^ 2 := hratio
  have hexp : Real.exp
        (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
          (Real.log F) ^ 2) ≤
      Real.exp (-((2 : ℝ) ^ (-18 : ℝ) * c ^ 3) *
        ((Real.log P) ^ (3 : ℝ) / (Real.log F) ^ 2)) := by
    apply Real.exp_le_exp.mpr
    have hmul := mul_le_mul_of_nonneg_left hratioRpow
      (show 0 ≤ (2 : ℝ) ^ (-18 : ℝ) by positivity)
    calc
      -((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
          (Real.log F) ^ 2 =
          -((2 : ℝ) ^ (-18 : ℝ) *
            ((Real.log X) ^ 3 / (Real.log F) ^ 2)) := by ring
      _ ≤ -((2 : ℝ) ^ (-18 : ℝ) *
          (c ^ 3 * ((Real.log P) ^ (3 : ℝ) / (Real.log F) ^ 2))) :=
        neg_le_neg hmul
      _ = -((2 : ℝ) ^ (-18 : ℝ) * c ^ 3) *
          ((Real.log P) ^ (3 : ℝ) / (Real.log F) ^ 2) := by ring
  have hprincipalDecay := hprincipalP F hF hFupper
  have hshift : Real.log P * (Real.log P) ^ (-(T + 1)) =
      (Real.log P) ^ (-T) := by
    calc
      Real.log P * (Real.log P) ^ (-(T + 1)) =
          (Real.log P) ^ (1 : ℝ) * (Real.log P) ^ (-(T + 1)) := by
            rw [Real.rpow_one]
      _ = (Real.log P) ^ ((1 : ℝ) + -(T + 1)) :=
        (Real.rpow_add hlogPos 1 (-(T + 1))).symm
      _ = (Real.log P) ^ (-T) := by
        congr 1
        ring
  have hprincipalScalar :
      (2 * Real.log P + 1) * C₁ * (Real.log P) ^ (4 * A) *
          Real.exp (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
            (Real.log F) ^ 2) ≤
        (Real.log P) ^ (-T) := by
    have hprefactor : 2 * Real.log P + 1 ≤ 3 * Real.log P := by linarith
    calc
      (2 * Real.log P + 1) * C₁ * (Real.log P) ^ (4 * A) *
          Real.exp (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
            (Real.log F) ^ 2) ≤
        (3 * Real.log P) * C₁ * (Real.log P) ^ (4 * A) *
          Real.exp (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
            (Real.log F) ^ 2) := by
              gcongr
      _ = 3 * C₁ * ((Real.log P) ^ (4 * A + 1) *
          Real.exp (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
            (Real.log F) ^ 2)) := by
              rw [Real.rpow_add hlogPos]
              norm_num
              ring
      _ ≤ 3 * C₁ * ((Real.log P) ^ (4 * A + 1) *
          Real.exp (-((2 : ℝ) ^ (-18 : ℝ) * c ^ 3) *
            ((Real.log P) ^ (3 : ℝ) / (Real.log F) ^ 2))) := by
              gcongr
      _ ≤ 3 * C₁ * (Real.log P) ^ (-(T + 1)) := by
              exact mul_le_mul_of_nonneg_left hprincipalDecay (by positivity)
      _ ≤ Real.log P * (Real.log P) ^ (-(T + 1)) := by
              gcongr
      _ = (Real.log P) ^ (-T) := hshift
  have hcritical :
      16 * Real.log P * (Real.log P) ^ (-3 * A) ≤
        (Real.log P) ^ (-T) := by
    have hexponent : 1 - 3 * A ≤ -(T + 1) := by linarith
    have hrpow : (Real.log P) ^ (1 - 3 * A) ≤
        (Real.log P) ^ (-(T + 1)) :=
      Real.rpow_le_rpow_of_exponent_le hlogOne hexponent
    calc
      16 * Real.log P * (Real.log P) ^ (-3 * A) =
          16 * ((Real.log P) ^ (1 : ℝ) *
            (Real.log P) ^ (-3 * A)) := by
              rw [Real.rpow_one]
              ring
      _ = 16 * (Real.log P) ^ (1 - 3 * A) := by
            rw [← Real.rpow_add hlogPos 1 (-3 * A)]
            ring_nf
      _ ≤ 16 * (Real.log P) ^ (-(T + 1)) := by gcongr
      _ ≤ Real.log P * (Real.log P) ^ (-(T + 1)) := by gcongr
      _ = (Real.log P) ^ (-T) := hshift
  have hexpX : Real.exp (c * Real.log P) ≤ X := by
    have := Real.exp_le_exp.mpr hXlower
    rwa [Real.exp_log hXpos] at this
  have hinvX : 1 / X ≤ Real.exp (-c * Real.log P) := by
    calc
      1 / X ≤ 1 / Real.exp (c * Real.log P) :=
        one_div_le_one_div_of_le (Real.exp_pos _) hexpX
      _ = (Real.exp (c * Real.log P))⁻¹ := by rw [one_div]
      _ = Real.exp (-(c * Real.log P)) := (Real.exp_neg _).symm
      _ = Real.exp (-c * Real.log P) := by ring_nf
  have hendpointDecay := hendpointP
  have hendpointTerm : Real.log P * (Real.log P + 1) ≤
      X * (Real.log P) ^ (-T) := by
    have hpolyNat : Real.log P * (Real.log P + 1) ≤ (Real.log P) ^ 3 := by
      nlinarith [sq_nonneg (Real.log P),
        mul_nonneg (sq_nonneg (Real.log P)) hlogPos.le]
    have hpoly := hpolyNat
    rw [← Real.rpow_natCast] at hpoly
    have hnormalized :
        (Real.log P * (Real.log P + 1)) * (1 / X) ≤
          (Real.log P) ^ (-T) := by
      calc
        (Real.log P * (Real.log P + 1)) * (1 / X) ≤
            (Real.log P) ^ (3 : ℝ) * Real.exp (-c * Real.log P) := by
              exact mul_le_mul hpoly hinvX (by positivity) (by positivity)
        _ = (Real.log P) ^ (3 : ℝ) *
            Real.exp (-c * (Real.log P) ^ (1 : ℝ)) := by
              rw [Real.rpow_one]
        _ ≤ (Real.log P) ^ (-T) := hendpointDecay
    calc
      Real.log P * (Real.log P + 1) =
          X * ((Real.log P * (Real.log P + 1)) * (1 / X)) := by
            field_simp
      _ ≤ X * (Real.log P) ^ (-T) := by gcongr
  have hsaving : 0 ≤ (Real.log P) ^ (-T) := Real.rpow_nonneg hlogPos.le _
  calc
    (2 * Real.log P + 1) *
          (C₁ * (Real.log P) ^ (4 * A) * X * Real.exp
            (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
              (Real.log F) ^ 2)) +
        Real.log P *
          (16 * X * (Real.log P) ^ (-3 * A) + Real.log P + 1) =
      X * ((2 * Real.log P + 1) * C₁ *
          (Real.log P) ^ (4 * A) * Real.exp
            (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
              (Real.log F) ^ 2)) +
        X * (16 * Real.log P * (Real.log P) ^ (-3 * A)) +
        Real.log P * (Real.log P + 1) := by ring
    _ ≤ X * (Real.log P) ^ (-T) + X * (Real.log P) ^ (-T) +
        X * (Real.log P) ^ (-T) := by
          gcongr
    _ = 3 * X * (Real.log P) ^ (-T) := by ring

end Tao2026

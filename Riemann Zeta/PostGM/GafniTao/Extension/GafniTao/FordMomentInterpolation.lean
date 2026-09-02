import GafniTao.FordLemma36Moment
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Ford Theorem 3: interpolation between adjacent `k`-multiple moments

Ford writes an arbitrary permissible moment index as `s = n k + u`, with
`0 \le u \le k`, and applies Hölder between `J_{nk,k}` and
`J_{(n+1)k,k}`.  This file proves that exact interpolation for the literal
Vinogradov moment already defined in `FordVinogradovIntegral`.
-/

open MeasureTheory

namespace GafniTao

noncomputable section

/-- The complete Vinogradov Weyl sum is continuous on the normalized torus. -/
theorem continuous_fordVinogradovWeylSum (k Q : ℕ) :
    Continuous (fordVinogradovWeylSum k Q) := by
  unfold fordVinogradovWeylSum fordVinogradovMonomial
  exact continuous_finsetSum _ fun n _ =>
    (UnitAddTorus.mFourier (fordVinogradovExponent n)).continuous

/-- The nonnegative torus integral of a power of the complete Weyl sum is
the corresponding literal finite solution count. -/
theorem ford_vinogradov_lintegral_mean_eq (s k Q : ℕ) :
    (∫⁻ α : UnitAddTorus (Fin k),
        (ENNReal.ofReal ‖fordVinogradovWeylSum k Q α‖) ^ (2 * s)
        ∂Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)) =
      (fordVinogradovMomentNat s k Q : ENNReal) := by
  have hint : Integrable (fun α : UnitAddTorus (Fin k) =>
      ‖fordVinogradovWeylSum k Q α‖ ^ (2 * s))
      (Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)) := by
    rw [← integrableOn_univ]
    apply ContinuousOn.integrableOn_compact isCompact_univ
    exact ((continuous_fordVinogradovWeylSum k Q).norm.pow (2 * s)).continuousOn
  calc
    (∫⁻ α : UnitAddTorus (Fin k),
        (ENNReal.ofReal ‖fordVinogradovWeylSum k Q α‖) ^ (2 * s)
        ∂Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)) =
        ∫⁻ α : UnitAddTorus (Fin k), ENNReal.ofReal
          (‖fordVinogradovWeylSum k Q α‖ ^ (2 * s))
          ∂Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle) := by
      apply lintegral_congr
      intro α
      rw [ENNReal.ofReal_pow (norm_nonneg _)]
    _ = ENNReal.ofReal (∫ α : UnitAddTorus (Fin k),
          ‖fordVinogradovWeylSum k Q α‖ ^ (2 * s)
          ∂Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)) :=
      (ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall fun _ => by positivity)).symm
    _ = (fordVinogradovMomentNat s k Q : ENNReal) := by
      rw [ford_vinogradov_torus_real_mean_eq]
      norm_num

/-- The pointwise exponent identity behind Ford's Hölder interpolation. -/
theorem ford_moment_interpolation_point
    {n k u : ℕ} (hk : 1 ≤ k) (hu : u ≤ k) (x : ENNReal) :
    (x ^ (2 * (n * k))) ^ (((k : ℝ) - u) / (k : ℝ)) *
        (x ^ (2 * ((n + 1) * k))) ^ ((u : ℝ) / (k : ℝ)) =
      x ^ (2 * (n * k + u)) := by
  let p : ℝ := ((k : ℝ) - u) / (k : ℝ)
  let q : ℝ := (u : ℝ) / (k : ℝ)
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hp : 0 ≤ p := by
    dsimp [p]
    exact div_nonneg (sub_nonneg.mpr (by exact_mod_cast hu)) hkR.le
  have hq : 0 ≤ q := by
    dsimp [q]
    positivity
  have hexponent :
      ((2 * (n * k) : ℕ) : ℝ) * p +
          ((2 * ((n + 1) * k) : ℕ) : ℝ) * q =
        ((2 * (n * k + u) : ℕ) : ℝ) := by
    dsimp [p, q]
    push_cast
    field_simp
    ring
  calc
    (x ^ (2 * (n * k))) ^ p *
        (x ^ (2 * ((n + 1) * k))) ^ q =
        x ^ (((2 * (n * k) : ℕ) : ℝ) * p) *
          x ^ (((2 * ((n + 1) * k) : ℕ) : ℝ) * q) := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
        ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    _ = x ^ ((((2 * (n * k) : ℕ) : ℝ) * p) +
        (((2 * ((n + 1) * k) : ℕ) : ℝ) * q)) := by
      rw [ENNReal.rpow_add_of_nonneg _ _
        (mul_nonneg (by positivity) hp) (mul_nonneg (by positivity) hq)]
    _ = x ^ (((2 * (n * k + u) : ℕ) : ℝ)) := by rw [hexponent]
    _ = x ^ (2 * (n * k + u)) := ENNReal.rpow_natCast _ _

/-- Ford's exact Hölder interpolation
`J_{nk+u,k} ≤ J_{nk,k}^{1-u/k} J_{(n+1)k,k}^{u/k}`. -/
theorem ford_vinogradov_moment_interpolation
    {n k u Q : ℕ} (hk : 1 ≤ k) (hu : u ≤ k) :
    (fordVinogradovMomentNat (n * k + u) k Q : ENNReal) ≤
      (fordVinogradovMomentNat (n * k) k Q : ENNReal) ^
          (((k : ℝ) - u) / (k : ℝ)) *
        (fordVinogradovMomentNat ((n + 1) * k) k Q : ENNReal) ^
          ((u : ℝ) / (k : ℝ)) := by
  let B : UnitAddTorus (Fin k) → ENNReal := fun α =>
    ENNReal.ofReal ‖fordVinogradovWeylSum k Q α‖
  let p : ℝ := ((k : ℝ) - u) / (k : ℝ)
  let q : ℝ := (u : ℝ) / (k : ℝ)
  have hp : 0 ≤ p := by
    dsimp [p]
    have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    exact div_nonneg (sub_nonneg.mpr (by exact_mod_cast hu)) hkR.le
  have hq : 0 ≤ q := by
    dsimp [q]
    positivity
  have hpq : p + q = 1 := by
    dsimp [p, q]
    have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    field_simp
    ring
  have hB : AEMeasurable B
      (Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)) := by
    exact (ENNReal.continuous_ofReal.comp
      (continuous_fordVinogradovWeylSum k Q).norm).aemeasurable
  have hholder := ENNReal.lintegral_mul_norm_pow_le
    (hB.pow_const (2 * (n * k)))
    (hB.pow_const (2 * ((n + 1) * k))) hp hq hpq
  have hpoint (α : UnitAddTorus (Fin k)) :
      (B α ^ (2 * (n * k))) ^ p *
          (B α ^ (2 * ((n + 1) * k))) ^ q =
        B α ^ (2 * (n * k + u)) :=
    ford_moment_interpolation_point hk hu (B α)
  rw [show (∫⁻ α, (B α ^ (2 * (n * k))) ^ p *
          (B α ^ (2 * ((n + 1) * k))) ^ q
          ∂Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)) =
        ∫⁻ α, B α ^ (2 * (n * k + u))
          ∂Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle) by
      apply lintegral_congr
      exact hpoint] at hholder
  change (∫⁻ α : UnitAddTorus (Fin k),
      (ENNReal.ofReal ‖fordVinogradovWeylSum k Q α‖) ^
        (2 * (n * k + u))
      ∂Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)) ≤
    (∫⁻ α : UnitAddTorus (Fin k),
      (ENNReal.ofReal ‖fordVinogradovWeylSum k Q α‖) ^
        (2 * (n * k))
      ∂Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)) ^ p *
    (∫⁻ α : UnitAddTorus (Fin k),
      (ENNReal.ofReal ‖fordVinogradovWeylSum k Q α‖) ^
        (2 * ((n + 1) * k))
      ∂Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)) ^ q at hholder
  rw [ford_vinogradov_lintegral_mean_eq,
    ford_vinogradov_lintegral_mean_eq,
    ford_vinogradov_lintegral_mean_eq] at hholder
  exact hholder

/-- Real-valued form of the exact Hölder interpolation. -/
theorem ford_vinogradov_moment_interpolation_real
    {n k u Q : ℕ} (hk : 1 ≤ k) (hu : u ≤ k) :
    (fordVinogradovMomentNat (n * k + u) k Q : ℝ) ≤
      (fordVinogradovMomentNat (n * k) k Q : ℝ) ^
          (((k : ℝ) - u) / (k : ℝ)) *
        (fordVinogradovMomentNat ((n + 1) * k) k Q : ℝ) ^
          ((u : ℝ) / (k : ℝ)) := by
  have h := ford_vinogradov_moment_interpolation
    (n := n) (k := k) (u := u) (Q := Q) hk hu
  have hfinite :
      (fordVinogradovMomentNat (n * k) k Q : ENNReal) ^
          (((k : ℝ) - u) / (k : ℝ)) *
        (fordVinogradovMomentNat ((n + 1) * k) k Q : ENNReal) ^
          ((u : ℝ) / (k : ℝ)) ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · apply ENNReal.rpow_ne_top_of_nonneg
      · have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
        exact div_nonneg (sub_nonneg.mpr (by exact_mod_cast hu)) hkR.le
      · exact ENNReal.coe_ne_top
    · apply ENNReal.rpow_ne_top_of_nonneg (by positivity)
      exact ENNReal.coe_ne_top
  have ht := ENNReal.toReal_mono hfinite h
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ← ENNReal.toReal_rpow] at ht
  simpa using ht

/-- The weighted adjacent exponents combine into Ford's exponent at the
intermediate moment index. -/
theorem fordLambda34_interpolation
    {n k u : ℕ} (hk : 1 ≤ k) (delta₀ delta₁ : ℝ) :
    (((k : ℝ) - u) / (k : ℝ)) *
        fordLambda34 (n * k) k delta₀ +
      ((u : ℝ) / (k : ℝ)) *
        fordLambda34 ((n + 1) * k) k delta₁ =
      fordLambda34 (n * k + u) k
        ((((k : ℝ) - u) / (k : ℝ)) * delta₀ +
          ((u : ℝ) / (k : ℝ)) * delta₁) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  unfold fordLambda34
  push_cast
  field_simp [hk0]
  ring

/-- Interpolation preserves a literal global Vinogradov moment bound, with
the weighted exponent and the expected Hölder coefficient. -/
theorem FordVinogradovMomentBound.interpolate
    {n k u : ℕ} {C₀ C₁ delta₀ delta₁ : ℝ}
    (hk : 1 ≤ k) (hu : u ≤ k)
    (h₀ : FordVinogradovMomentBound (n * k) k C₀ delta₀)
    (h₁ : FordVinogradovMomentBound ((n + 1) * k) k C₁ delta₁) :
    FordVinogradovMomentBound (n * k + u) k
      (C₀ ^ (((k : ℝ) - u) / (k : ℝ)) *
        C₁ ^ ((u : ℝ) / (k : ℝ)))
      ((((k : ℝ) - u) / (k : ℝ)) * delta₀ +
        ((u : ℝ) / (k : ℝ)) * delta₁) := by
  intro Q hQ
  let p : ℝ := ((k : ℝ) - u) / (k : ℝ)
  let q : ℝ := (u : ℝ) / (k : ℝ)
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hp : 0 ≤ p := by
    dsimp [p]
    exact div_nonneg (sub_nonneg.mpr (by exact_mod_cast hu)) hkR.le
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hC₀ : 0 ≤ C₀ := (h₀.one_le_coefficient).trans' zero_le_one
  have hC₁ : 0 ≤ C₁ := (h₁.one_le_coefficient).trans' zero_le_one
  have hQ0 : (0 : ℝ) ≤ Q := by positivity
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hbound₀ := h₀ Q hQ
  have hbound₁ := h₁ Q hQ
  have hinterp := ford_vinogradov_moment_interpolation_real
    (n := n) (k := k) (u := u) (Q := Q) hk hu
  calc
    (fordVinogradovMomentNat (n * k + u) k Q : ℝ) ≤
        (fordVinogradovMomentNat (n * k) k Q : ℝ) ^ p *
          (fordVinogradovMomentNat ((n + 1) * k) k Q : ℝ) ^ q := hinterp
    _ ≤ (C₀ * (Q : ℝ) ^ fordLambda34 (n * k) k delta₀) ^ p *
          (C₁ * (Q : ℝ) ^ fordLambda34 ((n + 1) * k) k delta₁) ^ q := by
      gcongr
    _ = (C₀ ^ p * C₁ ^ q) *
          (Q : ℝ) ^ (p * fordLambda34 (n * k) k delta₀ +
            q * fordLambda34 ((n + 1) * k) k delta₁) := by
      rw [Real.mul_rpow hC₀ (Real.rpow_nonneg hQ0 _),
        Real.mul_rpow hC₁ (Real.rpow_nonneg hQ0 _),
        ← Real.rpow_mul hQ0, ← Real.rpow_mul hQ0]
      have hcomm₀ : fordLambda34 (n * k) k delta₀ * p =
          p * fordLambda34 (n * k) k delta₀ := by ring
      have hcomm₁ : fordLambda34 ((n + 1) * k) k delta₁ * q =
          q * fordLambda34 ((n + 1) * k) k delta₁ := by ring
      rw [hcomm₀, hcomm₁]
      calc
        C₀ ^ p * (Q : ℝ) ^ (p * fordLambda34 (n * k) k delta₀) *
            (C₁ ^ q * (Q : ℝ) ^
              (q * fordLambda34 ((n + 1) * k) k delta₁)) =
            (C₀ ^ p * C₁ ^ q) *
              ((Q : ℝ) ^ (p * fordLambda34 (n * k) k delta₀) *
                (Q : ℝ) ^
                  (q * fordLambda34 ((n + 1) * k) k delta₁)) := by ring
        _ = _ := by rw [← Real.rpow_add hQpos]
    _ = (C₀ ^ p * C₁ ^ q) *
          (Q : ℝ) ^ fordLambda34 (n * k + u) k
            (p * delta₀ + q * delta₁) := by
      rw [fordLambda34_interpolation hk]

#print axioms continuous_fordVinogradovWeylSum
#print axioms ford_vinogradov_lintegral_mean_eq
#print axioms ford_moment_interpolation_point
#print axioms ford_vinogradov_moment_interpolation
#print axioms ford_vinogradov_moment_interpolation_real
#print axioms fordLambda34_interpolation
#print axioms FordVinogradovMomentBound.interpolate

end

end GafniTao

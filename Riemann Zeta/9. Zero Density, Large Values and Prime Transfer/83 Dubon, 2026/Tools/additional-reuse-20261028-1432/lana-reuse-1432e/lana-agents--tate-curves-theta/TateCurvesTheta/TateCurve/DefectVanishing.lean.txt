/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TateCurvesTheta.TateCurve.EisensteinKernels
import TateCurvesTheta.TateCurve.WeierstrassIdentity
import TateCurvesTheta.Theta.ThetaProdGlobalLaurent
import TateCurvesTheta.Theta.Uniqueness

/-!
# Vanishing of the Weierstrass defect: the Eisenstein pair-identity computation

This file proves the **Tate Weierstrass identity** pointwise: for a Tate parameter `q` over
a complete nonarchimedean field `K` with `12 ≠ 0` and every point `u : Kˣ` off the
`q`-orbit, the Weierstrass defect vanishes,
```
tateDefect u = Y(u)² + X(u)·Y(u) - (X(u)³ + a₄·X(u) + a₆) = 0,
```
by running the classical elementary Eisenstein computation (Silverman, *Advanced Topics*,
Ch. V, Thm 3.1; Weil, *Elliptic Functions According to Eisenstein and Kronecker*) directly
on the orbit series — **uniformly in `u`**, with no annulus restriction, no boundary-sphere
case split, and no base change.

## The computation

Write `wₙ = qⁿu` and `p, r, z` for the Eisenstein kernels of
`TateCurve/EisensteinKernels.lean`, so `p(wₙ) = Xterm u n` and `r(wₙ) = 2·Yterm u n +
Xterm u n`. With `S = ∑ₙ p(wₙ)` and `R = ∑ₙ r(wₙ) = 2Y + X` one has `X = S - 2s₁` and
```
4·tateDefect u = R² - X² - 4X³ - 4a₄X - 4a₆.
```
The three squares/cubes expand through the ℤ²-shear `(n, m) = (m + d, m)` and the
Eisenstein pair identities; the shifted `z`-differences **telescope**,
`∑ₘ (z(w_{m+d}) - z(wₘ)) = 2d` (`tsum_eisZ_orbit_shift_sub`), which is where the
`d`-weighted Eisenstein series enter. The `d`-sums fold by the kernels' inversion parities
into the constant series `pSum`, `rSum`, `phiSum`, `psiSum`, `pSqSum`, `prSum` of
`TateCurve/EisensteinSeries.lean`, yielding
```
S²   = S₂ + 4·pSum·S + 2·rSum,
R²   = 4S₃ + S₂ - 8·phiSum·S - 2·psiSum,
S₂·S = S₃ + 2·pSum·S₂ + (phiSum + 2·pSqSum)·S + 4·prSum,
```
with `S₂ = ∑ₙ p(wₙ)²`, `S₃ = ∑ₙ p(wₙ)³` (the diagonal terms collapse through the
nodal-cubic relation `r² = 4p³ + p²`). Substituting into the defect and using the two
bracket identities of `EisensteinSeries.lean` — ultimately the Besge and `σ₁∗σ₃`
convolution identities of `Arithmetic/DivisorConvolution.lean` — every term cancels.

## Main results

* `TateParameter.tsum_eisZ_orbit_shift_sub`: the orbit telescope `∑ₘ (z(w_{m+d}) - z(wₘ)) = 2d`.
* `TateParameter.tateDefect_eq_zero`: `tateDefect u = 0` for every off-orbit `u` (char `∤ 12`).

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Ch. V, Thm 3.1.
* A. Weil, *Elliptic Functions According to Eisenstein and Kronecker*.
* J. Tate, *A review of non-Archimedean elliptic functions*.
-/

open Filter Topology

noncomputable section

namespace TateCurvesTheta

namespace TateParameter

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable (t : TateParameter K)

/-! ### Orbit terms and the Eisenstein kernels -/

section OrbitBasics

variable (u : Kˣ)

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- The orbit term `qⁿu` is nonzero. -/
lemma qzpow_mul_ne_zero' (n : ℤ) : (t.q : K) ^ n * (u : K) ≠ 0 :=
  mul_ne_zero (zpow_ne_zero n t.q.ne_zero) u.ne_zero

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- The Eisenstein kernel `p` at an orbit point is the `X`-coordinate term. -/
lemma eisP_orbit (n : ℤ) : eisP ((t.q : K) ^ n * (u : K)) = t.Xterm u n := rfl

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- The Eisenstein kernel `r` at an orbit point is the `2Yterm + Xterm` combination. -/
lemma eisR_orbit {u : Kˣ} (hu : ∀ n : ℤ, (t.q : K) ^ n * (u : K) ≠ 1) (n : ℤ) :
    eisR ((t.q : K) ^ n * (u : K)) = 2 * t.Yterm u n + t.Xterm u n := by
  have h1 : (1 : K) - (t.q : K) ^ n * (u : K) ≠ 0 := t.one_sub_qzpow_mul_ne_zero hu n
  rw [eisR, Yterm_apply, Xterm_apply]
  field_simp
  ring

/-- Summability transfers through pointwise products over the same index type: in a
complete nonarchimedean field a family is summable iff it tends to zero along `cofinite`,
and null families are closed under pointwise products. -/
lemma summable_mul_pointwise {ι : Type*} {f g : ι → K} (hf : Summable f) (hg : Summable g) :
    Summable fun i => f i * g i :=
  NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    (by simpa using hf.tendsto_cofinite_zero.mul hg.tendsto_cofinite_zero)

/-- The squared `X`-terms are summable. -/
lemma Xterm_sq_summable : Summable fun n : ℤ => t.Xterm u n ^ 2 := by
  simpa [pow_two] using summable_mul_pointwise (t.Xterm_summable u) (t.Xterm_summable u)

/-- The cubed `X`-terms are summable. -/
lemma Xterm_cube_summable : Summable fun n : ℤ => t.Xterm u n ^ 3 := by
  have h := summable_mul_pointwise (t.Xterm_summable u)
    (summable_mul_pointwise (t.Xterm_summable u) (t.Xterm_summable u))
  refine h.congr fun n => ?_
  ring

/-- The Eisenstein `r`-kernels along the orbit are summable. -/
lemma eisR_orbit_summable {u : Kˣ} (hu : ∀ n : ℤ, (t.q : K) ^ n * (u : K) ≠ 1) :
    Summable fun n : ℤ => eisR ((t.q : K) ^ n * (u : K)) := by
  refine (((t.Yterm_summable u).mul_left 2).add (t.Xterm_summable u)).congr fun n => ?_
  rw [eisR_orbit t hu n]

end OrbitBasics

/-! ### The orbit telescope -/

section Telescope

variable {u : Kˣ}

/-- The `±1` step function against which the orbit values of the `z`-kernel are corrected:
`z(qᵐu) → 1` as `m → +∞` (where `qᵐu → 0`) and `→ -1` as `m → -∞`. -/
private def stepZ (m : ℤ) : K := if 0 ≤ m then 1 else -1

omit [CompleteSpace K] [IsUltrametricDist K] in
private lemma tendsto_qzpow_atTop : Tendsto (fun m : ℤ => (t.q : K) ^ m) atTop (𝓝 0) := by
  have hnat : Tendsto (fun k : ℕ => (t.q : K) ^ (k : ℤ)) atTop (𝓝 0) := by
    have := t.tendsto_pow_atTop_zero
    refine this.congr fun k => ?_
    rw [zpow_natCast]
  have htoNat : Tendsto Int.toNat atTop atTop :=
    tendsto_atTop_atTop_of_monotone (fun a b h => Int.toNat_le_toNat h)
      fun b => ⟨(b : ℤ), by simp⟩
  have hcomp := hnat.comp htoNat
  refine hcomp.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℤ)] with m hm
  simp only [Function.comp_apply, Int.toNat_of_nonneg hm]

omit [CompleteSpace K] [IsUltrametricDist K] in
private lemma tendsto_orbit_atTop (u : Kˣ) :
    Tendsto (fun m : ℤ => (t.q : K) ^ m * (u : K)) atTop (𝓝 0) := by
  simpa using t.tendsto_qzpow_atTop.mul_const (u : K)

omit [CompleteSpace K] [IsUltrametricDist K] in
private lemma tendsto_orbit_inv_atBot (u : Kˣ) :
    Tendsto (fun m : ℤ => ((t.q : K) ^ m * (u : K))⁻¹) atBot (𝓝 0) := by
  have h : Tendsto (fun m : ℤ => (t.q : K) ^ (-m)) atBot (𝓝 0) :=
    t.tendsto_qzpow_atTop.comp tendsto_neg_atBot_atTop
  have h' := h.mul_const ((u : K)⁻¹)
  simp only [zero_mul] at h'
  refine h'.congr fun m => ?_
  rw [mul_inv, zpow_neg]

omit [CompleteSpace K] [IsUltrametricDist K] in
private lemma eisZ_zero : eisZ (0 : K) = 1 := by
  rw [eisZ]
  simp

omit [CompleteSpace K] in
private lemma continuousAt_eisZ_zero : ContinuousAt (eisZ : K → K) 0 := by
  have heq : (eisZ : K → K) = fun x => (1 + x) / (1 - x) := funext fun x => rfl
  rw [heq]
  exact ContinuousAt.div (by fun_prop) (by fun_prop) (by simp)

/-- The corrected `z`-values `z(qᵐu) - stepZ m` are summable: they tend to zero at both
ends of `ℤ`. -/
private lemma summable_zeta (hu : ∀ n : ℤ, (t.q : K) ^ n * (u : K) ≠ 1) :
    Summable fun m : ℤ => eisZ ((t.q : K) ^ m * (u : K)) - stepZ m := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [Int.cofinite_eq, tendsto_sup]
  constructor
  · -- `atBot`: `z(w) = -z(w⁻¹) → -z(0) = -1`, and `stepZ = -1` eventually.
    have hz : Tendsto (fun m : ℤ => eisZ (((t.q : K) ^ m * (u : K))⁻¹)) atBot (𝓝 1) := by
      have h := continuousAt_eisZ_zero.tendsto.comp (t.tendsto_orbit_inv_atBot u)
      rw [eisZ_zero] at h
      exact h.congr fun m => rfl
    have hz' : Tendsto (fun m : ℤ => eisZ ((t.q : K) ^ m * (u : K))) atBot (𝓝 (-1)) := by
      have hneg := hz.neg
      refine hneg.congr fun m => ?_
      rw [eisZ_inv (t.qzpow_mul_ne_zero' u m) (hu m), neg_neg]
    have h0 : Tendsto (fun m : ℤ => eisZ ((t.q : K) ^ m * (u : K)) - -1) atBot (𝓝 0) := by
      simpa using hz'.sub_const (-1)
    refine h0.congr' ?_
    filter_upwards [eventually_lt_atBot (0 : ℤ)] with m hm
    simp [stepZ, not_le.mpr hm]
  · -- `atTop`: `z(w) → z(0) = 1`, and `stepZ = 1` eventually.
    have hz : Tendsto (fun m : ℤ => eisZ ((t.q : K) ^ m * (u : K))) atTop (𝓝 1) := by
      have h := continuousAt_eisZ_zero.tendsto.comp (t.tendsto_orbit_atTop u)
      rw [eisZ_zero] at h
      exact h.congr fun m => rfl
    have h1 : Tendsto (fun m : ℤ => eisZ ((t.q : K) ^ m * (u : K)) - 1) atTop (𝓝 0) := by
      simpa using hz.sub_const 1
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℤ)] with m hm
    simp [stepZ, hm]

omit [IsUltrametricDist K] in
private lemma summable_shift {f : ℤ → K} (hf : Summable f) (d : ℤ) :
    Summable fun m : ℤ => f (m + d) :=
  hf.comp_injective (add_left_injective d)

omit [CompleteSpace K] [IsUltrametricDist K] in
private lemma tsum_shift (f : ℤ → K) (d : ℤ) : ∑' m : ℤ, f (m + d) = ∑' m : ℤ, f m := by
  rw [← (Equiv.addRight d).tsum_eq f]
  exact tsum_congr fun m => rfl

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- The window where the step function changes, together with the change values: the
shifted step-difference is supported on a window of length `|d|` where it equals `±2`. -/
private lemma hasSum_stepZ_sub (d : ℤ) :
    HasSum (fun m : ℤ => stepZ (K := K) (m + d) - stepZ m) (2 * (d : K)) := by
  classical
  rcases le_total 0 d with hd | hd
  · have hvanish : ∀ m ∉ Finset.Ico (-d) (0 : ℤ), stepZ (K := K) (m + d) - stepZ m = 0 := by
      intro m hm
      rw [Finset.mem_Ico, not_and_or, not_le, not_lt] at hm
      rcases hm with hm | hm
      · have h1 : ¬(0 ≤ m) := by omega
        have h2 : ¬(0 ≤ m + d) := by omega
        simp [stepZ, h1, h2]
      · have h1 : 0 ≤ m := hm
        have h2 : 0 ≤ m + d := by omega
        simp [stepZ, h1, h2]
    have h : HasSum (fun m : ℤ => stepZ (K := K) (m + d) - stepZ m)
        (∑ m ∈ Finset.Ico (-d) (0 : ℤ), (stepZ (K := K) (m + d) - stepZ m)) :=
      hasSum_sum_of_ne_finset_zero hvanish
    have hval : (∑ m ∈ Finset.Ico (-d) (0 : ℤ), (stepZ (K := K) (m + d) - stepZ m))
        = 2 * (d : K) := by
      have hterm : ∀ m ∈ Finset.Ico (-d) (0 : ℤ),
          stepZ (K := K) (m + d) - stepZ m = 2 := by
        intro m hm
        rw [Finset.mem_Ico] at hm
        have h1 : ¬(0 ≤ m) := by omega
        have h2 : 0 ≤ m + d := by omega
        rw [stepZ, stepZ, if_pos h2, if_neg h1]
        ring
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, Int.card_Ico, nsmul_eq_mul]
      have hnat : ((0 - -d).toNat : ℤ) = d := by omega
      have : (((0 - -d).toNat : ℕ) : K) = (d : K) := by rw [← Int.cast_natCast, hnat]
      rw [this]
      ring
    rwa [hval] at h
  · have hvanish : ∀ m ∉ Finset.Ico (0 : ℤ) (-d), stepZ (K := K) (m + d) - stepZ m = 0 := by
      intro m hm
      rw [Finset.mem_Ico, not_and_or, not_le, not_lt] at hm
      rcases hm with hm | hm
      · have h1 : ¬(0 ≤ m) := by omega
        have h2 : ¬(0 ≤ m + d) := by omega
        simp [stepZ, h1, h2]
      · have h1 : 0 ≤ m := by omega
        have h2 : 0 ≤ m + d := by omega
        simp [stepZ, h1, h2]
    have h : HasSum (fun m : ℤ => stepZ (K := K) (m + d) - stepZ m)
        (∑ m ∈ Finset.Ico (0 : ℤ) (-d), (stepZ (K := K) (m + d) - stepZ m)) :=
      hasSum_sum_of_ne_finset_zero hvanish
    have hval : (∑ m ∈ Finset.Ico (0 : ℤ) (-d), (stepZ (K := K) (m + d) - stepZ m))
        = 2 * (d : K) := by
      have hterm : ∀ m ∈ Finset.Ico (0 : ℤ) (-d),
          stepZ (K := K) (m + d) - stepZ m = -2 := by
        intro m hm
        rw [Finset.mem_Ico] at hm
        have h1 : 0 ≤ m := hm.1
        have h2 : ¬(0 ≤ m + d) := by omega
        rw [stepZ, stepZ, if_neg h2, if_pos h1]
        ring
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, Int.card_Ico, nsmul_eq_mul]
      have hnat : ((-d - 0).toNat : ℤ) = -d := by omega
      have : (((-d - 0).toNat : ℕ) : K) = ((-d : ℤ) : K) := by rw [← Int.cast_natCast, hnat]
      rw [this]
      push_cast
      ring
    rwa [hval] at h

/-- The shifted-difference family of orbit `z`-values is summable. -/
lemma summable_eisZ_orbit_shift_sub (hu : ∀ n : ℤ, (t.q : K) ^ n * (u : K) ≠ 1) (d : ℤ) :
    Summable fun m : ℤ =>
      eisZ ((t.q : K) ^ (m + d) * (u : K)) - eisZ ((t.q : K) ^ m * (u : K)) := by
  have hζ := t.summable_zeta hu
  have hζs := summable_shift hζ d
  refine (((hζs.sub hζ).add (hasSum_stepZ_sub (K := K) d).summable).congr fun m => ?_)
  simp only [stepZ]
  ring

/-- **The orbit telescope**: for every `d`, the shifted differences of the `z`-kernel over
the orbit `qᶻu` sum to `2d`. The boundary values `z(0) = 1` and `z(∞) = -1` of the odd
kernel produce the `d`-weight; this is where the weighted Eisenstein series of the final
assembly originate. -/
theorem tsum_eisZ_orbit_shift_sub (hu : ∀ n : ℤ, (t.q : K) ^ n * (u : K) ≠ 1) (d : ℤ) :
    (∑' m : ℤ, (eisZ ((t.q : K) ^ (m + d) * (u : K)) - eisZ ((t.q : K) ^ m * (u : K))))
      = 2 * (d : K) := by
  have hζ := t.summable_zeta hu
  have hζs := summable_shift hζ d
  have hdecomp : (fun m : ℤ =>
      eisZ ((t.q : K) ^ (m + d) * (u : K)) - eisZ ((t.q : K) ^ m * (u : K)))
      = fun m => ((eisZ ((t.q : K) ^ (m + d) * (u : K)) - stepZ (m + d))
          - (eisZ ((t.q : K) ^ m * (u : K)) - stepZ m))
          + (stepZ (m + d) - stepZ m) := by
    funext m
    ring
  rw [hdecomp, (hζs.sub hζ).tsum_add (hasSum_stepZ_sub (K := K) d).summable,
    Summable.tsum_sub hζs hζ,
    tsum_shift (fun m => eisZ ((t.q : K) ^ m * (u : K)) - stepZ m) d, sub_self, zero_add,
    (hasSum_stepZ_sub (K := K) d).tsum_eq]

end Telescope

/-! ### The constant Eisenstein series: summability -/

section ConstantSeries

omit [CompleteSpace K] in
private lemma norm_one_sub_eq_one {x : K} (hx : ‖x‖ < 1) : ‖(1 : K) - x‖ = 1 := by
  rw [norm_one_sub_of_norm_ne_one hx.ne, max_eq_left hx.le]

omit [CompleteSpace K] in
private lemma norm_add_le_one {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a + b‖ ≤ 1 :=
  (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)

omit [CompleteSpace K] in
omit [IsUltrametricDist K] in
private lemma norm_mul_le_one {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a * b‖ ≤ 1 := by
  rw [norm_mul]
  exact mul_le_one₀ ha (norm_nonneg _) hb


omit [CompleteSpace K] in
private lemma norm_eisP_le {x : K} (hx : ‖x‖ < 1) : ‖eisP x‖ ≤ ‖x‖ := by
  rw [eisP, norm_div, norm_pow, norm_one_sub_eq_one hx, one_pow, div_one]

omit [CompleteSpace K] in
private lemma norm_eisR_le {x : K} (hx : ‖x‖ < 1) : ‖eisR x‖ ≤ ‖x‖ := by
  rw [eisR, norm_div, norm_pow, norm_one_sub_eq_one hx, one_pow, div_one, norm_mul]
  have h1 : ‖(1 : K) + x‖ ≤ 1 := norm_add_le_one (by simp) hx.le
  calc ‖x‖ * ‖1 + x‖ ≤ ‖x‖ * 1 := by gcongr
    _ = ‖x‖ := mul_one _

omit [CompleteSpace K] in
private lemma norm_eisPhi_le {x : K} (hx : ‖x‖ < 1) : ‖eisPhi x‖ ≤ ‖x‖ := by
  rw [eisPhi, norm_div, norm_pow, norm_one_sub_eq_one hx, one_pow, div_one, norm_mul]
  have h4 : ‖(4 : K)‖ ≤ 1 := by exact_mod_cast IsUltrametricDist.norm_natCast_le_one K 4
  have h1 : ‖(1 : K) + 4 * x + x ^ 2‖ ≤ 1 :=
    norm_add_le_one (norm_add_le_one (by simp) (norm_mul_le_one h4 hx.le))
      (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx.le)
  calc ‖x‖ * ‖1 + 4 * x + x ^ 2‖ ≤ ‖x‖ * 1 := by gcongr
    _ = ‖x‖ := mul_one _

omit [CompleteSpace K] in
private lemma norm_eisPsi_le {x : K} (hx : ‖x‖ < 1) : ‖eisPsi x‖ ≤ ‖x‖ := by
  rw [eisPsi, norm_div, norm_pow, norm_one_sub_eq_one hx, one_pow, div_one, norm_mul]
  have hx1 : ‖x‖ ≤ 1 := hx.le
  have hpow : ∀ j : ℕ, ‖x ^ j‖ ≤ 1 := fun j => by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx1
  have h11 : ‖(11 : K)‖ ≤ 1 := by exact_mod_cast IsUltrametricDist.norm_natCast_le_one K 11
  have h1 : ‖(1 : K) + 11 * x + 11 * x ^ 2 + x ^ 3‖ ≤ 1 :=
    norm_add_le_one (norm_add_le_one (norm_add_le_one (by simp)
      (norm_mul_le_one h11 hx1))
      (norm_mul_le_one h11 (hpow 2))) (hpow 3)
  calc ‖x‖ * ‖1 + 11 * x + 11 * x ^ 2 + x ^ 3‖ ≤ ‖x‖ * 1 := by gcongr
    _ = ‖x‖ := mul_one _

omit [CompleteSpace K] in
private lemma norm_eisPsi3_le {x : K} (hx : ‖x‖ < 1) : ‖eisPsi3 x‖ ≤ ‖x‖ := by
  rw [eisPsi3, norm_div, norm_pow, norm_one_sub_eq_one hx, one_pow, div_one, norm_mul]
  have h2 : ‖(2 : K)‖ ≤ 1 := by exact_mod_cast IsUltrametricDist.norm_natCast_le_one K 2
  have h1 : ‖2 * x + 1‖ ≤ 1 :=
    norm_add_le_one (norm_mul_le_one h2 hx.le) (by simp)
  calc ‖x‖ * ‖2 * x + 1‖ ≤ ‖x‖ * 1 := by gcongr
    _ = ‖x‖ := mul_one _

omit [CompleteSpace K] [IsUltrametricDist K] in
private lemma norm_qpow_lt_one (k : ℕ) : ‖(t.q : K) ^ (k + 1)‖ < 1 := by
  rw [norm_pow]
  exact pow_lt_one₀ (norm_nonneg _) t.norm_lt_one (Nat.succ_ne_zero k)

omit [IsUltrametricDist K] in
/-- Summability of any `q`-power-dominated family. -/
private lemma summable_of_qpow_bound {G : ℕ → K}
    (hG : ∀ k : ℕ, ‖G k‖ ≤ ‖(t.q : K)‖ ^ (k + 1)) : Summable G := by
  have hgeom : Summable fun k : ℕ => ‖(t.q : K)‖ ^ (k + 1) := by
    simpa only [pow_succ] using
      (summable_geometric_of_lt_one (norm_nonneg _) t.norm_lt_one).mul_right ‖(t.q : K)‖
  exact hgeom.of_norm_bounded hG

omit [CompleteSpace K] [IsUltrametricDist K] in
private lemma norm_weight_kernel_le {F : K → K}
    (hF : ∀ {x : K}, ‖x‖ < 1 → ‖F x‖ ≤ ‖x‖) (c : ℕ → K) (hc : ∀ k, ‖c k‖ ≤ 1) (k : ℕ) :
    ‖c k * F ((t.q : K) ^ (k + 1))‖ ≤ ‖(t.q : K)‖ ^ (k + 1) := by
  rw [norm_mul]
  calc ‖c k‖ * ‖F ((t.q : K) ^ (k + 1))‖
      ≤ 1 * ‖(t.q : K) ^ (k + 1)‖ := by
        gcongr
        · exact hc k
        · exact hF (t.norm_qpow_lt_one k)
    _ = ‖(t.q : K)‖ ^ (k + 1) := by rw [one_mul, norm_pow]

private lemma summable_eisP_qpow : Summable fun k : ℕ => eisP ((t.q : K) ^ (k + 1)) := by
  refine t.summable_of_qpow_bound fun k => ?_
  have := t.norm_weight_kernel_le (fun {_} hx => norm_eisP_le hx) (fun _ => 1)
    (fun _ => by simp) k
  simpa using this

private lemma summable_eisR_qpow : Summable fun k : ℕ => eisR ((t.q : K) ^ (k + 1)) := by
  refine t.summable_of_qpow_bound fun k => ?_
  have := t.norm_weight_kernel_le (fun {_} hx => norm_eisR_le hx) (fun _ => 1)
    (fun _ => by simp) k
  simpa using this

private lemma summable_eisPsi3_qpow : Summable fun k : ℕ => eisPsi3 ((t.q : K) ^ (k + 1)) := by
  refine t.summable_of_qpow_bound fun k => ?_
  have := t.norm_weight_kernel_le (fun {_} hx => norm_eisPsi3_le hx) (fun _ => 1)
    (fun _ => by simp) k
  simpa using this

private lemma summable_phi_qpow : Summable fun k : ℕ => eisPhi ((t.q : K) ^ (k + 1)) := by
  refine t.summable_of_qpow_bound fun k => ?_
  have := t.norm_weight_kernel_le (fun {_} hx => norm_eisPhi_le hx) (fun _ => 1)
    (fun _ => by simp) k
  simpa using this

private lemma summable_weight_eisR_qpow :
    Summable fun k : ℕ => ((k + 1 : ℕ) : K) * eisR ((t.q : K) ^ (k + 1)) :=
  t.summable_of_qpow_bound fun k =>
    t.norm_weight_kernel_le (fun {_} hx => norm_eisR_le hx)
      (fun k => ((k + 1 : ℕ) : K)) (fun k => IsUltrametricDist.norm_natCast_le_one K (k + 1)) k

private lemma summable_weight_eisPsi_qpow :
    Summable fun k : ℕ => ((k + 1 : ℕ) : K) * eisPsi ((t.q : K) ^ (k + 1)) :=
  t.summable_of_qpow_bound fun k =>
    t.norm_weight_kernel_le (fun {_} hx => norm_eisPsi_le hx)
      (fun k => ((k + 1 : ℕ) : K)) (fun k => IsUltrametricDist.norm_natCast_le_one K (k + 1)) k

private lemma summable_eisP_sq_qpow :
    Summable fun k : ℕ => eisP ((t.q : K) ^ (k + 1)) ^ 2 := by
  have h := summable_mul_pointwise t.summable_eisP_qpow t.summable_eisP_qpow
  refine h.congr fun k => ?_
  rw [pow_two]

private lemma summable_weight_eisP_mul_eisR_qpow :
    Summable fun k : ℕ =>
      ((k + 1 : ℕ) : K) * (eisP ((t.q : K) ^ (k + 1)) * eisR ((t.q : K) ^ (k + 1))) := by
  have h := summable_mul_pointwise t.summable_eisP_qpow t.summable_weight_eisR_qpow
  refine h.congr fun k => ?_
  ring

end ConstantSeries

/-! ### Per-`d` evaluation of the sheared cross sums -/

section PerD

variable {u : Kˣ}

omit [CompleteSpace K] [IsUltrametricDist K] in
private lemma w_shift (u : Kˣ) (m d : ℤ) :
    (t.q : K) ^ (m + d) * (u : K) = (t.q : K) ^ d * ((t.q : K) ^ m * (u : K)) := by
  rw [zpow_add₀ t.q.ne_zero]
  ring

/-- Per-`d` evaluation of the sheared `X·X` cross sum: for `d ≠ 0`,
`∑ₘ p(w_{m+d})p(wₘ) = 2p(qᵈ)·S + d·r(qᵈ)`. -/
private lemma tsum_shift_mul_Xterm (h2 : (2 : K) ≠ 0)
    (hu : ∀ n : ℤ, (t.q : K) ^ n * (u : K) ≠ 1) {d : ℤ} (hd : d ≠ 0) :
    ∑' m : ℤ, t.Xterm u (m + d) * t.Xterm u m
      = 2 * eisP ((t.q : K) ^ d) * (∑' n : ℤ, t.Xterm u n)
        + (d : K) * eisR ((t.q : K) ^ d) := by
  have htd1 : (t.q : K) ^ d ≠ 1 := t.zpow_ne_one hd
  have hX := t.Xterm_summable u
  have hXs := summable_shift hX d
  have hZ := t.summable_eisZ_orbit_shift_sub hu d
  have hpair : ∀ m : ℤ, 2 * (t.Xterm u (m + d) * t.Xterm u m)
      = 2 * eisP ((t.q : K) ^ d) * (t.Xterm u m + t.Xterm u (m + d))
        - eisR ((t.q : K) ^ d)
            * (-(eisZ ((t.q : K) ^ (m + d) * (u : K)) - eisZ ((t.q : K) ^ m * (u : K)))) := by
    intro m
    have h := eisP_mul_eisP (t := (t.q : K) ^ d) (v := (t.q : K) ^ m * (u : K)) htd1 (hu m)
      (by rw [← t.w_shift u m d]; exact hu (m + d))
    rw [← t.w_shift u m d] at h
    rw [eisP_orbit, eisP_orbit] at h
    have hmul : t.Xterm u (m + d) * t.Xterm u m = t.Xterm u m * t.Xterm u (m + d) := mul_comm _ _
    rw [neg_sub]
    calc 2 * (t.Xterm u (m + d) * t.Xterm u m)
        = 2 * (t.Xterm u (m + d) * t.Xterm u m) := rfl
      _ = 2 * eisP ((t.q : K) ^ d) * (t.Xterm u m + t.Xterm u (m + d))
            - eisR ((t.q : K) ^ d)
              * (eisZ ((t.q : K) ^ m * (u : K)) - eisZ ((t.q : K) ^ (m + d) * (u : K))) := h
  have hs1 : Summable fun m : ℤ => t.Xterm u m + t.Xterm u (m + d) := hX.add hXs
  have hkey : (∑' m : ℤ, 2 * (t.Xterm u (m + d) * t.Xterm u m))
      = 2 * eisP ((t.q : K) ^ d) * ((∑' n : ℤ, t.Xterm u n) + (∑' n : ℤ, t.Xterm u n))
        - eisR ((t.q : K) ^ d) * (-(2 * (d : K))) := by
    rw [tsum_congr hpair,
      Summable.tsum_sub (hs1.mul_left _) (hZ.neg.mul_left _), tsum_mul_left, tsum_mul_left,
      hX.tsum_add hXs, tsum_shift (t.Xterm u) d, tsum_neg, t.tsum_eisZ_orbit_shift_sub hu d]
  rw [tsum_mul_left] at hkey
  apply mul_left_cancel₀ h2
  rw [hkey]
  ring

/-- Per-`d` evaluation of the sheared `r·r` cross sum: for `d ≠ 0`,
`∑ₘ r(w_{m+d})r(wₘ) = -4φ(qᵈ)·S - d·ψ(qᵈ)`. -/
private lemma tsum_shift_mul_eisR (h2 : (2 : K) ≠ 0)
    (hu : ∀ n : ℤ, (t.q : K) ^ n * (u : K) ≠ 1) {d : ℤ} (hd : d ≠ 0) :
    ∑' m : ℤ, eisR ((t.q : K) ^ (m + d) * (u : K)) * eisR ((t.q : K) ^ m * (u : K))
      = -(4 * eisPhi ((t.q : K) ^ d) * (∑' n : ℤ, t.Xterm u n))
        - (d : K) * eisPsi ((t.q : K) ^ d) := by
  have htd1 : (t.q : K) ^ d ≠ 1 := t.zpow_ne_one hd
  have hX := t.Xterm_summable u
  have hXs := summable_shift hX d
  have hR := t.eisR_orbit_summable hu
  have hRs := summable_shift hR d
  have hZ := t.summable_eisZ_orbit_shift_sub hu d
  have hpair : ∀ m : ℤ, 2 * (eisR ((t.q : K) ^ (m + d) * (u : K))
        * eisR ((t.q : K) ^ m * (u : K)))
      = 2 * eisR ((t.q : K) ^ d)
          * (eisR ((t.q : K) ^ m * (u : K)) - eisR ((t.q : K) ^ (m + d) * (u : K)))
        - 4 * eisPhi ((t.q : K) ^ d) * (t.Xterm u m + t.Xterm u (m + d))
        - eisPsi ((t.q : K) ^ d)
            * (eisZ ((t.q : K) ^ (m + d) * (u : K)) - eisZ ((t.q : K) ^ m * (u : K))) := by
    intro m
    have h := eisR_mul_eisR (t := (t.q : K) ^ d) (v := (t.q : K) ^ m * (u : K)) htd1 (hu m)
      (by rw [← t.w_shift u m d]; exact hu (m + d))
    rw [← t.w_shift u m d] at h
    rw [eisP_orbit, eisP_orbit] at h
    rw [h]
    ring
  have hsR : Summable fun m : ℤ =>
      eisR ((t.q : K) ^ m * (u : K)) - eisR ((t.q : K) ^ (m + d) * (u : K)) := hR.sub hRs
  have hsX : Summable fun m : ℤ => t.Xterm u m + t.Xterm u (m + d) := hX.add hXs
  have hkey : (∑' m : ℤ, 2 * (eisR ((t.q : K) ^ (m + d) * (u : K))
        * eisR ((t.q : K) ^ m * (u : K))))
      = 2 * eisR ((t.q : K) ^ d) * 0
        - 4 * eisPhi ((t.q : K) ^ d)
            * ((∑' n : ℤ, t.Xterm u n) + (∑' n : ℤ, t.Xterm u n))
        - eisPsi ((t.q : K) ^ d) * (2 * (d : K)) := by
    rw [tsum_congr hpair,
      Summable.tsum_sub ((hsR.mul_left _).sub (hsX.mul_left _)) (hZ.mul_left _),
      Summable.tsum_sub (hsR.mul_left _) (hsX.mul_left _),
      tsum_mul_left, tsum_mul_left, tsum_mul_left,
      Summable.tsum_sub hR hRs,
      tsum_shift (fun n => eisR ((t.q : K) ^ n * (u : K))) d, sub_self,
      hX.tsum_add hXs, tsum_shift (t.Xterm u) d, t.tsum_eisZ_orbit_shift_sub hu d]
  rw [tsum_mul_left] at hkey
  apply mul_left_cancel₀ h2
  rw [hkey]
  ring

/-- Per-`d` evaluation of the sheared `p²·p` cross sum (doubled form): for `d ≠ 0`,
`2·∑ₘ p(w_{m+d})²p(wₘ) = 2p(qᵈ)·S₂ + r(qᵈ)·R + (2ψ₃(qᵈ) - r(qᵈ))·S + 2p(qᵈ)²·S + 4d·p(qᵈ)r(qᵈ)`. -/
private lemma tsum_shift_sq_mul_Xterm
    (hu : ∀ n : ℤ, (t.q : K) ^ n * (u : K) ≠ 1) {d : ℤ} (hd : d ≠ 0) :
    2 * ∑' m : ℤ, t.Xterm u (m + d) ^ 2 * t.Xterm u m
      = 2 * eisP ((t.q : K) ^ d) * (∑' n : ℤ, t.Xterm u n ^ 2)
        + eisR ((t.q : K) ^ d) * (∑' n : ℤ, eisR ((t.q : K) ^ n * (u : K)))
        + (2 * eisPsi3 ((t.q : K) ^ d) - eisR ((t.q : K) ^ d)) * (∑' n : ℤ, t.Xterm u n)
        + 2 * eisP ((t.q : K) ^ d) ^ 2 * (∑' n : ℤ, t.Xterm u n)
        + 4 * (d : K) * (eisP ((t.q : K) ^ d) * eisR ((t.q : K) ^ d)) := by
  have htd1 : (t.q : K) ^ d ≠ 1 := t.zpow_ne_one hd
  have hX := t.Xterm_summable u
  have hXs := summable_shift hX d
  have hX2 := t.Xterm_sq_summable u
  have hX2s := summable_shift hX2 d
  have hR := t.eisR_orbit_summable hu
  have hRs := summable_shift hR d
  have hZ := t.summable_eisZ_orbit_shift_sub hu d
  have hpair : ∀ m : ℤ, 2 * (t.Xterm u (m + d) ^ 2 * t.Xterm u m)
      = (2 * eisP ((t.q : K) ^ d) * t.Xterm u (m + d) ^ 2
          + eisR ((t.q : K) ^ d) * eisR ((t.q : K) ^ (m + d) * (u : K))
          + (2 * eisPsi3 ((t.q : K) ^ d) - eisR ((t.q : K) ^ d)) * t.Xterm u (m + d)
          + 2 * eisP ((t.q : K) ^ d) ^ 2 * t.Xterm u m)
        + 2 * (eisP ((t.q : K) ^ d) * eisR ((t.q : K) ^ d))
            * (eisZ ((t.q : K) ^ (m + d) * (u : K)) - eisZ ((t.q : K) ^ m * (u : K))) := by
    intro m
    have h := eisP_sq_mul_eisP (t := (t.q : K) ^ d) (v := (t.q : K) ^ m * (u : K)) htd1 (hu m)
      (by rw [← t.w_shift u m d]; exact hu (m + d))
    rw [← t.w_shift u m d] at h
    rw [eisP_orbit, eisP_orbit] at h
    calc 2 * (t.Xterm u (m + d) ^ 2 * t.Xterm u m)
        = 2 * (t.Xterm u (m + d) ^ 2 * t.Xterm u m) := rfl
      _ = _ := by rw [h]; ring
  have hmain : Summable fun m : ℤ =>
      2 * eisP ((t.q : K) ^ d) * t.Xterm u (m + d) ^ 2
        + eisR ((t.q : K) ^ d) * eisR ((t.q : K) ^ (m + d) * (u : K))
        + (2 * eisPsi3 ((t.q : K) ^ d) - eisR ((t.q : K) ^ d)) * t.Xterm u (m + d)
        + 2 * eisP ((t.q : K) ^ d) ^ 2 * t.Xterm u m :=
    (((hX2s.mul_left _).add (hRs.mul_left _)).add (hXs.mul_left _)).add (hX.mul_left _)
  have hkey : (∑' m : ℤ, 2 * (t.Xterm u (m + d) ^ 2 * t.Xterm u m))
      = (2 * eisP ((t.q : K) ^ d) * (∑' n : ℤ, t.Xterm u n ^ 2)
          + eisR ((t.q : K) ^ d) * (∑' n : ℤ, eisR ((t.q : K) ^ n * (u : K)))
          + (2 * eisPsi3 ((t.q : K) ^ d) - eisR ((t.q : K) ^ d)) * (∑' n : ℤ, t.Xterm u n)
          + 2 * eisP ((t.q : K) ^ d) ^ 2 * (∑' n : ℤ, t.Xterm u n))
        + 2 * (eisP ((t.q : K) ^ d) * eisR ((t.q : K) ^ d)) * (2 * (d : K)) := by
    rw [tsum_congr hpair, (hmain).tsum_add (hZ.mul_left _)]
    congr 1
    · rw [(((hX2s.mul_left _).add (hRs.mul_left _)).add (hXs.mul_left _)).tsum_add
          (hX.mul_left _),
        ((hX2s.mul_left _).add (hRs.mul_left _)).tsum_add (hXs.mul_left _),
        (hX2s.mul_left _).tsum_add (hRs.mul_left _),
        tsum_mul_left, tsum_mul_left, tsum_mul_left, tsum_mul_left,
        tsum_shift (fun n => t.Xterm u n ^ 2) d,
        tsum_shift (fun n => eisR ((t.q : K) ^ n * (u : K))) d,
        tsum_shift (t.Xterm u) d]
    · rw [tsum_mul_left, t.tsum_eisZ_orbit_shift_sub hu d]
  rw [tsum_mul_left] at hkey
  rw [hkey]
  ring

end PerD

/-! ### Folding the `d`-sums -/

section Fold

variable {u : Kˣ}

omit [CompleteSpace K] [IsUltrametricDist K] in
private lemma zpow_succ_natCast (k : ℕ) :
    (t.q : K) ^ ((k : ℤ) + 1) = (t.q : K) ^ (k + 1) := by
  rw [(by push_cast; ring : ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ)), zpow_natCast]

omit [CompleteSpace K] [IsUltrametricDist K] in
private lemma zpow_neg_succ_natCast (k : ℕ) :
    (t.q : K) ^ (-((k : ℤ) + 1)) = ((t.q : K) ^ (k + 1))⁻¹ := by
  rw [zpow_neg, t.zpow_succ_natCast k]

omit [CompleteSpace K] [IsUltrametricDist K] in
private lemma qpow_succ_ne_zero (k : ℕ) : (t.q : K) ^ (k + 1) ≠ 0 :=
  pow_ne_zero _ t.q.ne_zero

omit [CompleteSpace K] [IsUltrametricDist K] in
private lemma qpow_succ_ne_one (k : ℕ) : (t.q : K) ^ (k + 1) ≠ 1 :=
  t.pow_ne_one (Nat.succ_pos k)

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- Fold a `ℤ ∖ {0}`-indexed family into its two `ℕ`-indexed halves. -/
private lemma hasSum_int_ite {v : ℤ → K} {cp cn : K}
    (hp : HasSum (fun k : ℕ => v ((k : ℤ) + 1)) cp)
    (hn : HasSum (fun k : ℕ => v (-((k : ℤ) + 1))) cn) :
    HasSum (fun d : ℤ => if d = 0 then 0 else v d) (cp + cn) := by
  classical
  have hinjp : Function.Injective (fun k : ℕ => (k : ℤ) + 1) := fun a b h => by
    simpa using h
  have hinjn : Function.Injective (fun k : ℕ => -((k : ℤ) + 1)) := fun a b h => by
    simpa using h
  have hpos : HasSum (fun d : ℤ => if 0 < d then v d else 0) cp := by
    apply (hinjp.hasSum_iff ?_).mp
    · have hcomp : ((fun d : ℤ => if 0 < d then v d else 0) ∘ fun k : ℕ => (k : ℤ) + 1)
          = fun k : ℕ => v ((k : ℤ) + 1) := by
        funext k
        simp only [Function.comp_apply]
        rw [if_pos (by omega)]
      rw [hcomp]
      exact hp
    · intro d hd
      have hnpos : ¬(0 : ℤ) < d := by
        intro h0
        exact hd ⟨(d - 1).toNat, by simp only []; omega⟩
      exact if_neg hnpos
  have hneg : HasSum (fun d : ℤ => if d < 0 then v d else 0) cn := by
    apply (hinjn.hasSum_iff ?_).mp
    · have hcomp : ((fun d : ℤ => if d < 0 then v d else 0) ∘ fun k : ℕ => -((k : ℤ) + 1))
          = fun k : ℕ => v (-((k : ℤ) + 1)) := by
        funext k
        simp only [Function.comp_apply]
        rw [if_pos (by omega)]
      rw [hcomp]
      exact hn
    · intro d hd
      have hnneg : ¬d < (0 : ℤ) := by
        intro h0
        exact hd ⟨(-d - 1).toNat, by simp only []; omega⟩
      exact if_neg hnneg
  have hcomb := hpos.add hneg
  have hfe : (fun d : ℤ => (if 0 < d then v d else 0) + (if d < 0 then v d else 0))
      = fun d : ℤ => if d = 0 then 0 else v d := by
    funext d
    rcases lt_trichotomy d 0 with h | h | h
    · rw [if_neg (by omega), if_pos h, if_neg (by omega), zero_add]
    · subst h
      norm_num
    · rw [if_pos h, if_neg (by omega), if_neg (by omega), add_zero]
  rwa [hfe] at hcomb

/-- The shear `(d, m) ↦ (m + d, m)` on `ℤ²`. -/
private def shearEquiv : ℤ × ℤ ≃ ℤ × ℤ where
  toFun p := (p.2 + p.1, p.2)
  invFun p := (p.1 - p.2, p.2)
  left_inv p := by
    obtain ⟨a, b⟩ := p
    simp
  right_inv p := by
    obtain ⟨a, b⟩ := p
    simp

/-- **Expansion of `S²`**: `S² = S₂ + 4·𝔭·S + 2·ρ̂` where `𝔭 = ∑ p(qᵏ⁺¹)` and
`ρ̂ = ∑ (k+1)·r(qᵏ⁺¹)`. -/
theorem tsum_Xterm_sq_expansion (h2 : (2 : K) ≠ 0)
    (hu : ∀ n : ℤ, (t.q : K) ^ n * (u : K) ≠ 1) :
    (∑' n : ℤ, t.Xterm u n) * (∑' n : ℤ, t.Xterm u n)
      = (∑' n : ℤ, t.Xterm u n ^ 2)
        + 4 * (∑' k : ℕ, eisP ((t.q : K) ^ (k + 1))) * (∑' n : ℤ, t.Xterm u n)
        + 2 * (∑' k : ℕ, ((k + 1 : ℕ) : K) * eisR ((t.q : K) ^ (k + 1))) := by
  classical
  have hX := t.Xterm_summable u
  set S := ∑' n : ℤ, t.Xterm u n with hS
  set g : ℤ → K := fun d => ∑' m : ℤ, t.Xterm u (m + d) * t.Xterm u m with hg
  -- the sheared double sum collapses fiberwise onto `g`
  have hSS : HasSum (fun p : ℤ × ℤ => t.Xterm u p.1 * t.Xterm u p.2) (S * S) :=
    hX.hasSum.mul_of_nonarchimedean hX.hasSum
  have hshear : HasSum (fun p : ℤ × ℤ => t.Xterm u (p.2 + p.1) * t.Xterm u p.2) (S * S) := by
    have h := (shearEquiv.hasSum_iff
      (f := fun p : ℤ × ℤ => t.Xterm u p.1 * t.Xterm u p.2)).mpr hSS
    exact h
  have hfib : ∀ d : ℤ, HasSum (fun m : ℤ => t.Xterm u (m + d) * t.Xterm u m) (g d) :=
    fun d => (summable_mul_pointwise (summable_shift hX d) hX).hasSum
  have hG : HasSum g (S * S) := by
    refine hshear.prod_fiberwise fun d => ?_
    exact hfib d
  -- the positive and negative halves of the `d ≠ 0` part
  have hpS : HasSum (fun k : ℕ => eisP ((t.q : K) ^ (k + 1)))
      (∑' k : ℕ, eisP ((t.q : K) ^ (k + 1))) := t.summable_eisP_qpow.hasSum
  have hrS : HasSum (fun k : ℕ => ((k + 1 : ℕ) : K) * eisR ((t.q : K) ^ (k + 1)))
      (∑' k : ℕ, ((k + 1 : ℕ) : K) * eisR ((t.q : K) ^ (k + 1))) :=
    t.summable_weight_eisR_qpow.hasSum
  set pS := ∑' k : ℕ, eisP ((t.q : K) ^ (k + 1)) with hpSdef
  set rS := ∑' k : ℕ, ((k + 1 : ℕ) : K) * eisR ((t.q : K) ^ (k + 1)) with hrSdef
  have hval : HasSum (fun k : ℕ =>
      2 * eisP ((t.q : K) ^ (k + 1)) * S + ((k + 1 : ℕ) : K) * eisR ((t.q : K) ^ (k + 1)))
      (2 * pS * S + rS) := by
    have h1 : HasSum (fun k : ℕ => 2 * eisP ((t.q : K) ^ (k + 1)) * S) (2 * pS * S) := by
      have := (hpS.mul_left 2).mul_right S
      exact this
    exact h1.add hrS
  have hgpos : HasSum (fun k : ℕ => g ((k : ℤ) + 1)) (2 * pS * S + rS) := by
    have hfe : (fun k : ℕ =>
        2 * eisP ((t.q : K) ^ (k + 1)) * S + ((k + 1 : ℕ) : K) * eisR ((t.q : K) ^ (k + 1)))
        = fun k : ℕ => g ((k : ℤ) + 1) := by
      funext k
      simp only [hg]
      rw [t.tsum_shift_mul_Xterm h2 hu (show ((k : ℤ) + 1) ≠ 0 by omega), ← hS,
        t.zpow_succ_natCast k]
      push_cast
      ring
    exact hfe ▸ hval
  have hgneg : HasSum (fun k : ℕ => g (-((k : ℤ) + 1))) (2 * pS * S + rS) := by
    have hfe : (fun k : ℕ =>
        2 * eisP ((t.q : K) ^ (k + 1)) * S + ((k + 1 : ℕ) : K) * eisR ((t.q : K) ^ (k + 1)))
        = fun k : ℕ => g (-((k : ℤ) + 1)) := by
      funext k
      simp only [hg]
      rw [t.tsum_shift_mul_Xterm h2 hu (show -((k : ℤ) + 1) ≠ 0 by omega), ← hS,
        t.zpow_neg_succ_natCast k,
        eisP_inv (t.qpow_succ_ne_zero k) (t.qpow_succ_ne_one k),
        eisR_inv (t.qpow_succ_ne_zero k) (t.qpow_succ_ne_one k)]
      push_cast
      ring
    exact hfe ▸ hval
  have hIte : HasSum (fun d : ℤ => if d = 0 then 0 else g d)
      ((2 * pS * S + rS) + (2 * pS * S + rS)) := hasSum_int_ite hgpos hgneg
  have hdelta : HasSum (fun d : ℤ => if d = 0 then g 0 else 0) (g 0) :=
    hasSum_ite_eq 0 (g 0)
  have hsplit : (fun d : ℤ => (if d = 0 then 0 else g d) + (if d = 0 then g 0 else 0))
      = g := by
    funext d
    by_cases hd : d = 0
    · subst hd
      simp
    · simp [hd]
  have htot : HasSum g ((2 * pS * S + rS) + (2 * pS * S + rS) + g 0) := by
    have h := hIte.add hdelta
    rwa [hsplit] at h
  have hg0 : g 0 = ∑' n : ℤ, t.Xterm u n ^ 2 := by
    simp only [hg]
    exact tsum_congr fun m => by rw [add_zero, pow_two]
  have hfinal := hG.unique htot
  rw [hfinal, hg0]
  ring

set_option maxHeartbeats 1000000 in
-- the ℤ²-shear, fiberwise collapse and parity folding make this elaboration heavy
/-- **Expansion of `R²`**: `R² = 4S₃ + S₂ - 8·Φ̂·S - 2·Ψ̂` where `Φ̂ = ∑ φ(qᵏ⁺¹)` and
`Ψ̂ = ∑ (k+1)·ψ(qᵏ⁺¹)`; the diagonal collapses through the nodal relation `r² = 4p³ + p²`. -/
theorem tsum_eisR_sq_expansion (h2 : (2 : K) ≠ 0)
    (hu : ∀ n : ℤ, (t.q : K) ^ n * (u : K) ≠ 1) :
    (∑' n : ℤ, eisR ((t.q : K) ^ n * (u : K)))
        * (∑' n : ℤ, eisR ((t.q : K) ^ n * (u : K)))
      = 4 * (∑' n : ℤ, t.Xterm u n ^ 3) + (∑' n : ℤ, t.Xterm u n ^ 2)
        - 8 * (∑' k : ℕ, eisPhi ((t.q : K) ^ (k + 1))) * (∑' n : ℤ, t.Xterm u n)
        - 2 * (∑' k : ℕ, ((k + 1 : ℕ) : K) * eisPsi ((t.q : K) ^ (k + 1))) := by
  classical
  have hX := t.Xterm_summable u
  have hX2 := t.Xterm_sq_summable u
  have hX3 := t.Xterm_cube_summable u
  have hR := t.eisR_orbit_summable hu
  set S := ∑' n : ℤ, t.Xterm u n with hS
  set R := ∑' n : ℤ, eisR ((t.q : K) ^ n * (u : K)) with hRdef
  set g : ℤ → K := fun d =>
    ∑' m : ℤ, eisR ((t.q : K) ^ (m + d) * (u : K)) * eisR ((t.q : K) ^ m * (u : K)) with hg
  have hRR : HasSum (fun p : ℤ × ℤ =>
      eisR ((t.q : K) ^ p.1 * (u : K)) * eisR ((t.q : K) ^ p.2 * (u : K))) (R * R) :=
    hR.hasSum.mul_of_nonarchimedean hR.hasSum
  have hshear : HasSum (fun p : ℤ × ℤ =>
      eisR ((t.q : K) ^ (p.2 + p.1) * (u : K)) * eisR ((t.q : K) ^ p.2 * (u : K))) (R * R) :=
    (shearEquiv.hasSum_iff (f := fun p : ℤ × ℤ =>
      eisR ((t.q : K) ^ p.1 * (u : K)) * eisR ((t.q : K) ^ p.2 * (u : K)))).mpr hRR
  have hfib : ∀ d : ℤ, HasSum (fun m : ℤ =>
      eisR ((t.q : K) ^ (m + d) * (u : K)) * eisR ((t.q : K) ^ m * (u : K))) (g d) :=
    fun d => (summable_mul_pointwise (summable_shift hR d) hR).hasSum
  have hG : HasSum g (R * R) := hshear.prod_fiberwise fun d => hfib d
  have hphi : HasSum (fun k : ℕ => eisPhi ((t.q : K) ^ (k + 1)))
      (∑' k : ℕ, eisPhi ((t.q : K) ^ (k + 1))) := t.summable_phi_qpow.hasSum
  have hpsi : HasSum (fun k : ℕ => ((k + 1 : ℕ) : K) * eisPsi ((t.q : K) ^ (k + 1)))
      (∑' k : ℕ, ((k + 1 : ℕ) : K) * eisPsi ((t.q : K) ^ (k + 1))) :=
    t.summable_weight_eisPsi_qpow.hasSum
  set phS := ∑' k : ℕ, eisPhi ((t.q : K) ^ (k + 1)) with hphSdef
  set psS := ∑' k : ℕ, ((k + 1 : ℕ) : K) * eisPsi ((t.q : K) ^ (k + 1)) with hpsSdef
  have hval : HasSum (fun k : ℕ =>
      -(4 * eisPhi ((t.q : K) ^ (k + 1)) * S)
        - ((k + 1 : ℕ) : K) * eisPsi ((t.q : K) ^ (k + 1)))
      (-(4 * phS * S) - psS) :=
    (((hphi.mul_left 4).mul_right S).neg).sub hpsi
  have hgpos : HasSum (fun k : ℕ => g ((k : ℤ) + 1)) (-(4 * phS * S) - psS) := by
    have hfe : (fun k : ℕ =>
        -(4 * eisPhi ((t.q : K) ^ (k + 1)) * S)
          - ((k + 1 : ℕ) : K) * eisPsi ((t.q : K) ^ (k + 1)))
        = fun k : ℕ => g ((k : ℤ) + 1) := by
      funext k
      simp only [hg]
      rw [t.tsum_shift_mul_eisR h2 hu (show ((k : ℤ) + 1) ≠ 0 by omega), ← hS,
        t.zpow_succ_natCast k]
      push_cast
      ring
    exact hfe ▸ hval
  have hgneg : HasSum (fun k : ℕ => g (-((k : ℤ) + 1))) (-(4 * phS * S) - psS) := by
    have hfe : (fun k : ℕ =>
        -(4 * eisPhi ((t.q : K) ^ (k + 1)) * S)
          - ((k + 1 : ℕ) : K) * eisPsi ((t.q : K) ^ (k + 1)))
        = fun k : ℕ => g (-((k : ℤ) + 1)) := by
      funext k
      simp only [hg]
      rw [t.tsum_shift_mul_eisR h2 hu (show -((k : ℤ) + 1) ≠ 0 by omega), ← hS,
        t.zpow_neg_succ_natCast k,
        eisPhi_inv (t.qpow_succ_ne_zero k) (t.qpow_succ_ne_one k),
        eisPsi_inv (t.qpow_succ_ne_zero k) (t.qpow_succ_ne_one k)]
      push_cast
      ring
    exact hfe ▸ hval
  have hIte : HasSum (fun d : ℤ => if d = 0 then 0 else g d)
      ((-(4 * phS * S) - psS) + (-(4 * phS * S) - psS)) := hasSum_int_ite hgpos hgneg
  have hdelta : HasSum (fun d : ℤ => if d = 0 then g 0 else 0) (g 0) :=
    hasSum_ite_eq 0 (g 0)
  have hsplit : (fun d : ℤ => (if d = 0 then 0 else g d) + (if d = 0 then g 0 else 0))
      = g := by
    funext d
    by_cases hd : d = 0
    · subst hd
      simp
    · simp [hd]
  have htot : HasSum g ((-(4 * phS * S) - psS) + (-(4 * phS * S) - psS) + g 0) := by
    have h := hIte.add hdelta
    rwa [hsplit] at h
  have hg0 : g 0 = 4 * (∑' n : ℤ, t.Xterm u n ^ 3) + (∑' n : ℤ, t.Xterm u n ^ 2) := by
    simp only [hg]
    have hfe : ∀ m : ℤ,
        eisR ((t.q : K) ^ (m + 0) * (u : K)) * eisR ((t.q : K) ^ m * (u : K))
          = 4 * t.Xterm u m ^ 3 + t.Xterm u m ^ 2 := by
      intro m
      rw [add_zero, ← pow_two, eisR_sq (hu m), eisP_orbit]
    rw [tsum_congr hfe, (hX3.mul_left 4).tsum_add hX2, tsum_mul_left]
  have hfinal := hG.unique htot
  rw [hfinal, hg0]
  ring

set_option maxHeartbeats 1600000 in
-- the ℤ²-shear, fiberwise collapse and six-term parity folding make this elaboration heavy
/-- **Expansion of `S₂·S`**: `S₂·S = S₃ + 2·𝔭·S₂ + (Φ̂ + 2·Π̂₂)·S + 4·Λ̂`, where
`Π̂₂ = ∑ p(qᵏ⁺¹)²` and `Λ̂ = ∑ (k+1)·p(qᵏ⁺¹)r(qᵏ⁺¹)`. -/
theorem tsum_Xterm_sq_mul_expansion (h2 : (2 : K) ≠ 0)
    (hu : ∀ n : ℤ, (t.q : K) ^ n * (u : K) ≠ 1) :
    (∑' n : ℤ, t.Xterm u n ^ 2) * (∑' n : ℤ, t.Xterm u n)
      = (∑' n : ℤ, t.Xterm u n ^ 3)
        + 2 * (∑' k : ℕ, eisP ((t.q : K) ^ (k + 1))) * (∑' n : ℤ, t.Xterm u n ^ 2)
        + ((∑' k : ℕ, eisPhi ((t.q : K) ^ (k + 1)))
            + 2 * (∑' k : ℕ, eisP ((t.q : K) ^ (k + 1)) ^ 2)) * (∑' n : ℤ, t.Xterm u n)
        + 4 * (∑' k : ℕ, ((k + 1 : ℕ) : K)
            * (eisP ((t.q : K) ^ (k + 1)) * eisR ((t.q : K) ^ (k + 1)))) := by
  classical
  have hX := t.Xterm_summable u
  have hX2 := t.Xterm_sq_summable u
  have hX3 := t.Xterm_cube_summable u
  have hR := t.eisR_orbit_summable hu
  set S := ∑' n : ℤ, t.Xterm u n with hS
  set S2 := ∑' n : ℤ, t.Xterm u n ^ 2 with hS2
  set R := ∑' n : ℤ, eisR ((t.q : K) ^ n * (u : K)) with hRdef
  set g : ℤ → K := fun d => ∑' m : ℤ, t.Xterm u (m + d) ^ 2 * t.Xterm u m with hg
  have hSS : HasSum (fun p : ℤ × ℤ => t.Xterm u p.1 ^ 2 * t.Xterm u p.2) (S2 * S) :=
    hX2.hasSum.mul_of_nonarchimedean hX.hasSum
  have hshear : HasSum (fun p : ℤ × ℤ => t.Xterm u (p.2 + p.1) ^ 2 * t.Xterm u p.2)
      (S2 * S) :=
    (shearEquiv.hasSum_iff
      (f := fun p : ℤ × ℤ => t.Xterm u p.1 ^ 2 * t.Xterm u p.2)).mpr hSS
  have hfib : ∀ d : ℤ, HasSum (fun m : ℤ => t.Xterm u (m + d) ^ 2 * t.Xterm u m) (g d) :=
    fun d => (summable_mul_pointwise (summable_shift hX2 d) hX).hasSum
  have hG : HasSum g (S2 * S) := hshear.prod_fiberwise fun d => hfib d
  -- work with the doubled family to keep integral coefficients
  have hG2 : HasSum (fun d : ℤ => 2 * g d) (2 * (S2 * S)) := hG.mul_left 2
  have hp : HasSum (fun k : ℕ => eisP ((t.q : K) ^ (k + 1)))
      (∑' k : ℕ, eisP ((t.q : K) ^ (k + 1))) := t.summable_eisP_qpow.hasSum
  have hrk : HasSum (fun k : ℕ => eisR ((t.q : K) ^ (k + 1)))
      (∑' k : ℕ, eisR ((t.q : K) ^ (k + 1))) := t.summable_eisR_qpow.hasSum
  have hpsi3 : HasSum (fun k : ℕ => eisPsi3 ((t.q : K) ^ (k + 1)))
      (∑' k : ℕ, eisPsi3 ((t.q : K) ^ (k + 1))) := t.summable_eisPsi3_qpow.hasSum
  have hphi : HasSum (fun k : ℕ => eisPhi ((t.q : K) ^ (k + 1)))
      (∑' k : ℕ, eisPhi ((t.q : K) ^ (k + 1))) := t.summable_phi_qpow.hasSum
  have hpsq : HasSum (fun k : ℕ => eisP ((t.q : K) ^ (k + 1)) ^ 2)
      (∑' k : ℕ, eisP ((t.q : K) ^ (k + 1)) ^ 2) := t.summable_eisP_sq_qpow.hasSum
  have hpr : HasSum (fun k : ℕ => ((k + 1 : ℕ) : K)
      * (eisP ((t.q : K) ^ (k + 1)) * eisR ((t.q : K) ^ (k + 1))))
      (∑' k : ℕ, ((k + 1 : ℕ) : K)
        * (eisP ((t.q : K) ^ (k + 1)) * eisR ((t.q : K) ^ (k + 1)))) :=
    t.summable_weight_eisP_mul_eisR_qpow.hasSum
  set pS := ∑' k : ℕ, eisP ((t.q : K) ^ (k + 1)) with hpSdef
  set rkS := ∑' k : ℕ, eisR ((t.q : K) ^ (k + 1)) with hrkSdef
  set p3S := ∑' k : ℕ, eisPsi3 ((t.q : K) ^ (k + 1)) with hp3Sdef
  set phS := ∑' k : ℕ, eisPhi ((t.q : K) ^ (k + 1)) with hphSdef
  set pqS := ∑' k : ℕ, eisP ((t.q : K) ^ (k + 1)) ^ 2 with hpqSdef
  set prS := ∑' k : ℕ, ((k + 1 : ℕ) : K)
      * (eisP ((t.q : K) ^ (k + 1)) * eisR ((t.q : K) ^ (k + 1))) with hprSdef
  -- positive half
  have hvalp : HasSum (fun k : ℕ =>
      2 * eisP ((t.q : K) ^ (k + 1)) * S2
        + eisR ((t.q : K) ^ (k + 1)) * R
        + (2 * eisPsi3 ((t.q : K) ^ (k + 1)) - eisR ((t.q : K) ^ (k + 1))) * S
        + 2 * eisP ((t.q : K) ^ (k + 1)) ^ 2 * S
        + 4 * (((k + 1 : ℕ) : K)
            * (eisP ((t.q : K) ^ (k + 1)) * eisR ((t.q : K) ^ (k + 1)))))
      (2 * pS * S2 + rkS * R + (2 * p3S - rkS) * S + 2 * pqS * S + 4 * prS) := by
    refine ((((((hp.mul_left 2).mul_right S2).add (hrk.mul_right R)).add
      (((hpsi3.mul_left 2).sub hrk).mul_right S)).add
      (((hpsq.mul_left 2)).mul_right S)).add (hpr.mul_left 4))
  have hgpos : HasSum (fun k : ℕ => 2 * g ((k : ℤ) + 1))
      (2 * pS * S2 + rkS * R + (2 * p3S - rkS) * S + 2 * pqS * S + 4 * prS) := by
    have hfe : (fun k : ℕ =>
        2 * eisP ((t.q : K) ^ (k + 1)) * S2
          + eisR ((t.q : K) ^ (k + 1)) * R
          + (2 * eisPsi3 ((t.q : K) ^ (k + 1)) - eisR ((t.q : K) ^ (k + 1))) * S
          + 2 * eisP ((t.q : K) ^ (k + 1)) ^ 2 * S
          + 4 * (((k + 1 : ℕ) : K)
              * (eisP ((t.q : K) ^ (k + 1)) * eisR ((t.q : K) ^ (k + 1)))))
        = fun k : ℕ => 2 * g ((k : ℤ) + 1) := by
      funext k
      simp only [hg]
      rw [t.tsum_shift_sq_mul_Xterm hu (show ((k : ℤ) + 1) ≠ 0 by omega), ← hS, ← hS2,
        ← hRdef, t.zpow_succ_natCast k]
      push_cast
      ring
    exact hfe ▸ hvalp
  -- negative half
  have hvaln : HasSum (fun k : ℕ =>
      2 * eisP ((t.q : K) ^ (k + 1)) * S2
        - eisR ((t.q : K) ^ (k + 1)) * R
        + (2 * (eisPhi ((t.q : K) ^ (k + 1)) - eisPsi3 ((t.q : K) ^ (k + 1)))
            + eisR ((t.q : K) ^ (k + 1))) * S
        + 2 * eisP ((t.q : K) ^ (k + 1)) ^ 2 * S
        + 4 * (((k + 1 : ℕ) : K)
            * (eisP ((t.q : K) ^ (k + 1)) * eisR ((t.q : K) ^ (k + 1)))))
      (2 * pS * S2 - rkS * R + (2 * (phS - p3S) + rkS) * S + 2 * pqS * S + 4 * prS) := by
    refine ((((((hp.mul_left 2).mul_right S2).sub (hrk.mul_right R)).add
      ((((hphi.sub hpsi3).mul_left 2).add hrk).mul_right S)).add
      (((hpsq.mul_left 2)).mul_right S)).add (hpr.mul_left 4))
  have hgneg : HasSum (fun k : ℕ => 2 * g (-((k : ℤ) + 1)))
      (2 * pS * S2 - rkS * R + (2 * (phS - p3S) + rkS) * S + 2 * pqS * S + 4 * prS) := by
    have hfe : (fun k : ℕ =>
        2 * eisP ((t.q : K) ^ (k + 1)) * S2
          - eisR ((t.q : K) ^ (k + 1)) * R
          + (2 * (eisPhi ((t.q : K) ^ (k + 1)) - eisPsi3 ((t.q : K) ^ (k + 1)))
              + eisR ((t.q : K) ^ (k + 1))) * S
          + 2 * eisP ((t.q : K) ^ (k + 1)) ^ 2 * S
          + 4 * (((k + 1 : ℕ) : K)
              * (eisP ((t.q : K) ^ (k + 1)) * eisR ((t.q : K) ^ (k + 1)))))
        = fun k : ℕ => 2 * g (-((k : ℤ) + 1)) := by
      funext k
      have hpsi3inv : eisPsi3 (((t.q : K) ^ (k + 1))⁻¹)
          = eisPhi ((t.q : K) ^ (k + 1)) - eisPsi3 ((t.q : K) ^ (k + 1)) := by
        linear_combination eisPsi3_add_inv (t.qpow_succ_ne_zero k) (t.qpow_succ_ne_one k)
      simp only [hg]
      rw [t.tsum_shift_sq_mul_Xterm hu (show -((k : ℤ) + 1) ≠ 0 by omega), ← hS, ← hS2,
        ← hRdef, t.zpow_neg_succ_natCast k,
        eisP_inv (t.qpow_succ_ne_zero k) (t.qpow_succ_ne_one k),
        eisR_inv (t.qpow_succ_ne_zero k) (t.qpow_succ_ne_one k), hpsi3inv]
      push_cast
      ring
    exact hfe ▸ hvaln
  have hIte : HasSum (fun d : ℤ => if d = 0 then 0 else 2 * g d)
      ((2 * pS * S2 + rkS * R + (2 * p3S - rkS) * S + 2 * pqS * S + 4 * prS)
        + (2 * pS * S2 - rkS * R + (2 * (phS - p3S) + rkS) * S + 2 * pqS * S + 4 * prS)) :=
    hasSum_int_ite hgpos hgneg
  have hdelta : HasSum (fun d : ℤ => if d = 0 then 2 * g 0 else 0) (2 * g 0) :=
    hasSum_ite_eq 0 (2 * g 0)
  have hsplit : (fun d : ℤ =>
      (if d = 0 then 0 else 2 * g d) + (if d = 0 then 2 * g 0 else 0))
      = fun d : ℤ => 2 * g d := by
    funext d
    by_cases hd : d = 0
    · subst hd
      simp
    · simp [hd]
  have htot : HasSum (fun d : ℤ => 2 * g d)
      ((2 * pS * S2 + rkS * R + (2 * p3S - rkS) * S + 2 * pqS * S + 4 * prS)
        + (2 * pS * S2 - rkS * R + (2 * (phS - p3S) + rkS) * S + 2 * pqS * S + 4 * prS)
        + 2 * g 0) := by
    have h := hIte.add hdelta
    rwa [hsplit] at h
  have hg0 : g 0 = ∑' n : ℤ, t.Xterm u n ^ 3 := by
    simp only [hg]
    exact tsum_congr fun m => by rw [add_zero]; ring
  have hfinal := hG2.unique htot
  apply mul_left_cancel₀ h2
  rw [hfinal, hg0]
  ring

end Fold

/-! ### Assembly: vanishing of the defect modulo the two bracket identities -/

section Assembly

variable {u : Kˣ}

/-- The orbit sum of the `r`-kernel is the coordinate combination `2Y + X`. -/
lemma tsum_eisR_orbit_eq (hu : ∀ n : ℤ, (t.q : K) ^ n * (u : K) ≠ 1) :
    (∑' n : ℤ, eisR ((t.q : K) ^ n * (u : K))) = 2 * t.Y u + t.X u := by
  have h1 : (∑' n : ℤ, eisR ((t.q : K) ^ n * (u : K)))
      = ∑' n : ℤ, (2 * t.Yterm u n + t.Xterm u n) :=
    tsum_congr fun n => t.eisR_orbit hu n
  rw [h1, ((t.Yterm_summable u).mul_left 2).tsum_add (t.Xterm_summable u), tsum_mul_left,
    X_apply, Y_apply]
  ring

/-- **Vanishing of the Weierstrass defect, modulo the two Eisenstein bracket identities.**
Given the weight-4 bracket (the Besge identity in series form) and the weight-6 bracket
(the `σ₁∗σ₃` convolution identity in series form), together with `𝔭 = s₁`, the Eisenstein
pair-identity computation collapses the defect to zero at every off-orbit point. -/
theorem tateDefect_eq_zero_of_brackets (h2 : (2 : K) ≠ 0) (h4 : (4 : K) ≠ 0)
    (hu : ∀ n : ℤ, (t.q : K) ^ n * (u : K) ≠ 1)
    (hpe : (∑' k : ℕ, eisP ((t.q : K) ^ (k + 1))) = t.eisenstein 1)
    (hbrA : 12 * (∑' k : ℕ, eisPhi ((t.q : K) ^ (k + 1)))
        + 8 * (∑' k : ℕ, eisP ((t.q : K) ^ (k + 1)) ^ 2)
        + 8 * (∑' k : ℕ, ((k + 1 : ℕ) : K) * eisR ((t.q : K) ^ (k + 1)))
        + 16 * t.eisenstein 1 ^ 2 + 4 * t.a₄ = 0)
    (hbrB : 2 * (∑' k : ℕ, ((k + 1 : ℕ) : K) * eisPsi ((t.q : K) ^ (k + 1)))
        + 16 * (∑' k : ℕ, ((k + 1 : ℕ) : K)
            * (eisP ((t.q : K) ^ (k + 1)) * eisR ((t.q : K) ^ (k + 1))))
        + 2 * (∑' k : ℕ, ((k + 1 : ℕ) : K) * eisR ((t.q : K) ^ (k + 1)))
        + 4 * t.eisenstein 1 ^ 2 + 4 * t.a₆
      = 16 * t.eisenstein 1 * (∑' k : ℕ, ((k + 1 : ℕ) : K) * eisR ((t.q : K) ^ (k + 1)))
        + 32 * t.eisenstein 1 ^ 3 + 8 * t.a₄ * t.eisenstein 1) :
    t.tateDefect u = 0 := by
  have hE1 := t.tsum_Xterm_sq_expansion h2 hu
  have hE2 := t.tsum_eisR_sq_expansion h2 hu
  have hE3 := t.tsum_Xterm_sq_mul_expansion h2 hu
  rw [hpe] at hE1 hE3
  have hR2 := t.tsum_eisR_orbit_eq hu
  set S := ∑' n : ℤ, t.Xterm u n with hS
  set S2 := ∑' n : ℤ, t.Xterm u n ^ 2 with hS2
  set S3 := ∑' n : ℤ, t.Xterm u n ^ 3 with hS3
  set R := ∑' n : ℤ, eisR ((t.q : K) ^ n * (u : K)) with hRdef
  set e := t.eisenstein 1 with he
  set phS := ∑' k : ℕ, eisPhi ((t.q : K) ^ (k + 1)) with hphS
  set psS := ∑' k : ℕ, ((k + 1 : ℕ) : K) * eisPsi ((t.q : K) ^ (k + 1)) with hpsS
  set rS := ∑' k : ℕ, ((k + 1 : ℕ) : K) * eisR ((t.q : K) ^ (k + 1)) with hrS
  set pqS := ∑' k : ℕ, eisP ((t.q : K) ^ (k + 1)) ^ 2 with hpqS
  set prS := ∑' k : ℕ, ((k + 1 : ℕ) : K)
      * (eisP ((t.q : K) ^ (k + 1)) * eisR ((t.q : K) ^ (k + 1))) with hprS
  have hX : t.X u = S - 2 * e := by
    rw [X_apply, hS, he]
  -- the doubled defect in terms of `R` and `S`
  have hkey : 4 * t.tateDefect u
      = R * R - (S - 2 * e) * (S - 2 * e)
        - 4 * ((S - 2 * e) * (S - 2 * e) * (S - 2 * e))
        - 4 * t.a₄ * (S - 2 * e) - 4 * t.a₆ := by
    rw [tateDefect_apply, ← hX]
    linear_combination (-(R + 2 * t.Y u + t.X u)) * hR2
  -- assemble: the coefficient of `S` is the A-bracket, the constant is the B-bracket
  have h4D : 4 * t.tateDefect u = 0 := by
    rw [hkey]
    linear_combination hE2 + (-1 - 4 * S + 8 * e) * hE1 + (-4) * hE3
      + (-S) * hbrA + (-1) * hbrB
  calc t.tateDefect u = 4⁻¹ * (4 * t.tateDefect u) := by
        field_simp
    _ = 0 := by rw [h4D, mul_zero]

end Assembly

end TateParameter

end TateCurvesTheta

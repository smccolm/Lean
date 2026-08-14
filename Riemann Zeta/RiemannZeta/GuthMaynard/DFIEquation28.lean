import Mathlib.Analysis.PSeries
import RiemannZeta.GuthMaynard.DFIEquation24
import RiemannZeta.GuthMaynard.DFIPointwise

/-!
# DFI equation (28): derivatives of the localized delta weight

This module develops the quantitative derivative input used for the Bessel
integration by parts in DFI equation (28).  The first results are exact:
they differentiate an individual delta-kernel summand and then the locally
finite delta series.  The uniform bounds are assembled from the explicit
derivative profile of equations (2) and (13).
-/

open Complex Finset Set Filter Topology
open scoped BigOperators ContDiff Topology
open Classical

namespace RiemannZeta.GuthMaynard

/-- Exact positive-order derivative of one summand of the DFI delta kernel. -/
theorem iteratedDeriv_dfiDeltaSummand
    {Q : ℝ} (w : DFIDeltaWeight Q) (q r k : ℕ) (hk : 0 < k) (u : ℝ) :
    iteratedDeriv k (dfiDeltaSummand w q r) u =
      -(((q * r : ℕ) : ℝ)⁻¹ ^ (k + 1) *
        iteratedDeriv k w.toFun (u / (q * r : ℕ))) := by
  unfold dfiDeltaSummand
  rw [iteratedDeriv_div_const]
  rw [iteratedDeriv_const_sub hk]
  rw [iteratedDeriv_neg]
  have hcomp := iteratedDeriv_comp_const_mul
    (n := k) (w.smooth.of_le (by exact_mod_cast le_top))
    (((q * r : ℕ) : ℝ)⁻¹)
  have hfun : (fun z : ℝ => w (z / (q * r : ℕ))) =
      fun z : ℝ => w ((((q * r : ℕ) : ℝ)⁻¹) * z) := by
    funext z
    rw [div_eq_mul_inv, mul_comm]
  rw [hfun, hcomp]
  rw [div_eq_mul_inv]
  ring

/-- Around each point, one fixed finite sum represents the delta kernel. -/
theorem dfiDeltaKernel_eventuallyEq_fixedSum
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ) (hq : 0 < q) (u₀ : ℝ) :
    dfiDeltaKernel w q =ᶠ[nhds u₀]
      fun u => ∑ r ∈ Finset.Icc 1 (⌈2 * Q + (|u₀| + 1) / Q⌉₊ + 1),
        dfiDeltaSummand w q r u := by
  filter_upwards [dfiDeltaSummand_eq_zero_eventually_outside w q hq u₀] with u hu
  rw [dfiDeltaKernel_eq_tsum w q hq u]
  rw [tsum_eq_sum
    (s := Finset.Icc 1 (⌈2 * Q + (|u₀| + 1) / Q⌉₊ + 1))
    (fun r hr => by simpa [dfiDeltaSummand] using hu r hr)]
  rfl

/-- Exact termwise positive-order derivative of the locally finite DFI
delta kernel. -/
theorem iteratedDeriv_dfiDeltaKernel
    {Q : ℝ} (w : DFIDeltaWeight Q) (q k : ℕ)
    (hq : 0 < q) (u : ℝ) :
    iteratedDeriv k (dfiDeltaKernel w q) u =
      ∑ r ∈ Finset.Icc 1 (⌈2 * Q + (|u| + 1) / Q⌉₊ + 1),
        iteratedDeriv k (dfiDeltaSummand w q r) u := by
  let R := ⌈2 * Q + (|u| + 1) / Q⌉₊ + 1
  let fixed : ℝ → ℝ := fun z =>
    ∑ r ∈ Finset.Icc 1 R, dfiDeltaSummand w q r z
  have heq : dfiDeltaKernel w q =ᶠ[nhds u] fixed := by
    simpa [fixed, R] using dfiDeltaKernel_eventuallyEq_fixedSum w q hq u
  rw [Filter.EventuallyEq.iteratedDeriv_eq k heq]
  have hsum := iteratedDeriv_fun_sum
    (I := Finset.Icc 1 R) (f := fun r => dfiDeltaSummand w q r)
    (x := u) (n := k) (fun r hr =>
      (contDiff_dfiDeltaSummand w q r).contDiffAt.of_le
        (by exact_mod_cast le_top))
  simpa [fixed, R] using hsum

/-- Uniform positive-order derivative bound for the DFI delta kernel.  The
constant depends only on the derivative order and the normalized cutoff,
while the complete `q`- and `Q`-dependence is explicit. -/
theorem norm_iteratedDeriv_dfiDeltaKernel_le
    {Q : ℝ} (w : DFIDeltaWeight Q) (k : ℕ) (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ), 0 < q → ∀ u : ℝ,
      ‖iteratedDeriv k (dfiDeltaKernel w q) u‖ ≤
        C * (Q ^ (k + 1))⁻¹ * (((q : ℝ) ^ (k + 1))⁻¹) := by
  obtain ⟨Cw, hCw, hw⟩ := w.derivativeBound k
  let pseries : ℕ → ℝ := fun r => (((r : ℝ) ^ (k + 1))⁻¹)
  have hkpow : 1 < k + 1 := by omega
  have hpseries : Summable pseries := by
    simpa [pseries, one_div] using
      (Real.summable_nat_pow_inv.mpr hkpow)
  let S : ℝ := ∑' r : ℕ, pseries r
  have hS : 0 ≤ S := by
    dsimp [S]
    exact tsum_nonneg (fun r => by
      dsimp [pseries]
      positivity)
  let C : ℝ := Cw * max 1 S
  have hC : 0 < C := mul_pos hCw (lt_of_lt_of_le zero_lt_one (le_max_left 1 S))
  refine ⟨C, hC, ?_⟩
  intro q hq u
  let R := ⌈2 * Q + (|u| + 1) / Q⌉₊ + 1
  have hterm : ∀ r ∈ Finset.Icc 1 R,
      ‖iteratedDeriv k (dfiDeltaSummand w q r) u‖ ≤
        Cw * (Q ^ (k + 1))⁻¹ * (((q : ℝ) ^ (k + 1))⁻¹) *
          pseries r := by
    intro r hr
    have hrpos : 0 < r := (Finset.mem_Icc.mp hr).1
    rw [iteratedDeriv_dfiDeltaSummand w q r k hk u]
    rw [norm_neg, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) _)]
    have hwbound := hw (u / (q * r : ℕ))
    rw [Real.norm_eq_abs] at hwbound
    calc
      (((q * r : ℕ) : ℝ)⁻¹ ^ (k + 1)) *
          |iteratedDeriv k w.toFun (u / (q * r : ℕ))| ≤
        (((q * r : ℕ) : ℝ)⁻¹ ^ (k + 1)) *
          (Cw * (Q ^ (k + 1))⁻¹) :=
        mul_le_mul_of_nonneg_left hwbound
          (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) _)
      _ = Cw * (Q ^ (k + 1))⁻¹ * (((q : ℝ) ^ (k + 1))⁻¹) *
          pseries r := by
        simp only [pseries]
        push_cast
        rw [mul_inv_rev, mul_pow]
        ring
  rw [iteratedDeriv_dfiDeltaKernel w q k hq u]
  change ‖∑ r ∈ Finset.Icc 1 R,
      iteratedDeriv k (dfiDeltaSummand w q r) u‖ ≤ _
  calc
    ‖∑ r ∈ Finset.Icc 1 R,
        iteratedDeriv k (dfiDeltaSummand w q r) u‖ ≤
      ∑ r ∈ Finset.Icc 1 R,
        ‖iteratedDeriv k (dfiDeltaSummand w q r) u‖ := norm_sum_le _ _
    _ ≤ ∑ r ∈ Finset.Icc 1 R,
        Cw * (Q ^ (k + 1))⁻¹ * (((q : ℝ) ^ (k + 1))⁻¹) *
          pseries r := Finset.sum_le_sum hterm
    _ = (Cw * (Q ^ (k + 1))⁻¹ * (((q : ℝ) ^ (k + 1))⁻¹)) *
        ∑ r ∈ Finset.Icc 1 R, pseries r := by
      rw [Finset.mul_sum]
    _ ≤ (Cw * (Q ^ (k + 1))⁻¹ * (((q : ℝ) ^ (k + 1))⁻¹)) * S := by
      apply mul_le_mul_of_nonneg_left
      · exact hpseries.sum_le_tsum _ (fun r hr => by
          dsimp [pseries]
          positivity)
      · have hQ : 0 < Q := w.Q_pos
        positivity
    _ ≤ (Cw * (Q ^ (k + 1))⁻¹ * (((q : ℝ) ^ (k + 1))⁻¹)) *
        max 1 S := by
      apply mul_le_mul_of_nonneg_left (le_max_right 1 S)
      have hQ : 0 < Q := w.Q_pos
      positivity
    _ = C * (Q ^ (k + 1))⁻¹ * (((q : ℝ) ^ (k + 1))⁻¹) := by
      dsimp [C]
      ring

/-- Uniform form of the delta-kernel derivative estimate at every order,
including order zero.  This is the one-variable input to DFI equation (28):
each derivative costs one further factor `(qQ)⁻¹`. -/
theorem norm_iteratedDeriv_dfiDeltaKernel_le_product
    {Q : ℝ} (w : DFIDeltaWeight Q) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ), 0 < q → ∀ u : ℝ,
      ‖iteratedDeriv k (dfiDeltaKernel w q) u‖ ≤
        C * ((((q : ℝ) * Q) ^ (k + 1))⁻¹) := by
  by_cases hk : k = 0
  · subst k
    obtain ⟨K, hK, hbound⟩ := dfiEquation19 w
    refine ⟨2 * K, by positivity, ?_⟩
    intro q hq u
    have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
    have hqQ : 0 < (q : ℝ) * Q := mul_pos hqR w.Q_pos
    have hfirst :
        (((q : ℝ) * Q + Q ^ 2)⁻¹) ≤ (((q : ℝ) * Q)⁻¹) := by
      exact inv_anti₀ hqQ (le_add_of_nonneg_right (sq_nonneg Q))
    have hsecond :
        (((q : ℝ) * Q + |u|)⁻¹) ≤ (((q : ℝ) * Q)⁻¹) := by
      exact inv_anti₀ hqQ (le_add_of_nonneg_right (abs_nonneg u))
    rw [iteratedDeriv_zero]
    rw [Real.norm_eq_abs]
    calc
      |dfiDeltaKernel w q u| ≤
          K * ((((q : ℝ) * Q + Q ^ 2)⁻¹) +
            (((q : ℝ) * Q + |u|)⁻¹)) := hbound q hq u
      _ ≤ K * ((((q : ℝ) * Q)⁻¹) + (((q : ℝ) * Q)⁻¹)) := by
        gcongr
      _ = (2 * K) * ((((q : ℝ) * Q) ^ (0 + 1))⁻¹) := by ring
  · obtain ⟨C, hC, hbound⟩ :=
      norm_iteratedDeriv_dfiDeltaKernel_le w k (Nat.pos_of_ne_zero hk)
    refine ⟨C, hC, ?_⟩
    intro q hq u
    calc
      ‖iteratedDeriv k (dfiDeltaKernel w q) u‖ ≤
          C * (Q ^ (k + 1))⁻¹ * (((q : ℝ) ^ (k + 1))⁻¹) :=
        hbound q hq u
      _ = C * ((((q : ℝ) * Q) ^ (k + 1))⁻¹) := by
        rw [mul_pow, mul_inv_rev]
        ring

/-- One positive constant controls every delta-kernel derivative through a
fixed order. -/
theorem exists_uniform_norm_iteratedDeriv_dfiDeltaKernel_le_product
    {Q : ℝ} (w : DFIDeltaWeight Q) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ k ≤ n, ∀ (q : ℕ), 0 < q → ∀ u : ℝ,
      ‖iteratedDeriv k (dfiDeltaKernel w q) u‖ ≤
        C * ((((q : ℝ) * Q) ^ (k + 1))⁻¹) := by
  choose C hC hbound using fun k =>
    norm_iteratedDeriv_dfiDeltaKernel_le_product w k
  let Cmax := ∑ k ∈ Finset.range (n + 1), C k
  have hCmax : 0 < Cmax := by
    dsimp [Cmax]
    exact Finset.sum_pos (fun k _ => hC k) ⟨0, by simp⟩
  refine ⟨Cmax, hCmax, ?_⟩
  intro k hk q hq u
  have hkmem : k ∈ Finset.range (n + 1) := by simp [hk]
  have hCle : C k ≤ Cmax := by
    dsimp [Cmax]
    exact Finset.single_le_sum (fun r _ => (hC r).le) hkmem
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hqQ : 0 < (q : ℝ) * Q := mul_pos hqR w.Q_pos
  exact (hbound k q hq u).trans
    (mul_le_mul_of_nonneg_right hCle (by positivity))

/-- Exact mixed-derivative scaling under the affine change
`(x,y) ↦ (a*x,b*y)`. -/
theorem dfiMixedDeriv_affine_scale
    {F : ℝ → ℝ → ℂ}
    (hF : ContDiff ℝ ∞ (Function.uncurry F))
    (a b : ℝ) (i j : ℕ) (x y : ℝ) :
    dfiMixedDeriv i j (fun x' y' => F (a * x') (b * y')) x y =
      (a ^ i * b ^ j) • dfiMixedDeriv i j F (a * x) (b * y) := by
  unfold dfiMixedDeriv
  have hyfun :
      (fun x' => iteratedDeriv j (fun y' => F (a * x') (b * y')) y) =
        fun x' => b ^ j • iteratedDeriv j (F (a * x')) (b * y) := by
    funext x'
    have hslice : ContDiff ℝ j (F (a * x')) :=
      (contDiff_slice_right hF (a * x')).of_le (by exact_mod_cast le_top)
    simpa using congrFun (iteratedDeriv_comp_const_smul hslice b) y
  rw [hyfun]
  rw [iteratedDeriv_fun_const_smul_field]
  have hxbase : ContDiff ℝ i (fun z => iteratedDeriv j (F z) (b * y)) :=
    (contDiff_iteratedDeriv_slice_right hF j (b * y)).of_le
      (by exact_mod_cast le_top)
  rw [show iteratedDeriv i
      (fun x' => iteratedDeriv j (F (a * x')) (b * y)) x =
        a ^ i • iteratedDeriv i
          (fun z => iteratedDeriv j (F z) (b * y)) (a * x) by
    simpa using congrFun (iteratedDeriv_comp_const_smul hxbase a) x]
  rw [smul_smul]
  rw [mul_comm]

/-- The equation-(21) derivative profile after the arithmetic scaling
`(x,y) ↦ (a*x,b*y)`, uniformly through a fixed mixed order. -/
theorem exists_uniform_norm_dfiMixedDeriv_affine_localized_le
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (hscale : U ≤ P⁻¹ * min X Y) (h : ℝ)
    (a b i j : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ r ≤ i, ∀ s ≤ j, ∀ x y : ℝ,
        ‖dfiMixedDeriv r s
          (fun x' y' => dfiLocalizedWeight f φ h
            ((a : ℝ) * x') ((b : ℝ) * y')) x y‖ ≤
          C * ((a : ℝ) / U) ^ r * ((b : ℝ) / U) ^ s := by
  choose C hC hbound using fun r s =>
    dfiEquation21 hf hbox hφ hscale h r s
  let Cmax := ∑ r ∈ Finset.range (i + 1),
    ∑ s ∈ Finset.range (j + 1), C r s
  have hCmax : 0 < Cmax := by
    dsimp [Cmax]
    have hinner : ∀ r ∈ Finset.range (i + 1),
        0 < ∑ s ∈ Finset.range (j + 1), C r s := by
      intro r _hr
      exact Finset.sum_pos (fun s _ => hC r s) ⟨0, by simp⟩
    exact Finset.sum_pos hinner ⟨0, by simp⟩
  refine ⟨Cmax, hCmax, ?_⟩
  intro r hr s hs x y
  have hrmem : r ∈ Finset.range (i + 1) := by simp [hr]
  have hsmem : s ∈ Finset.range (j + 1) := by simp [hs]
  have hCle : C r s ≤ Cmax := by
    dsimp [Cmax]
    exact (Finset.single_le_sum (fun t _ => (hC r t).le) hsmem).trans
      (Finset.single_le_sum
        (fun t _ => Finset.sum_nonneg (fun u _ => (hC t u).le)) hrmem)
  have hU : 0 < U := hφ.U_pos
  have ha0 : 0 ≤ (a : ℝ) := Nat.cast_nonneg a
  have hb0 : 0 ≤ (b : ℝ) := Nat.cast_nonneg b
  have hfactor : 0 ≤ ((a : ℝ) ^ r * (b : ℝ) ^ s) := by positivity
  rw [dfiMixedDeriv_affine_scale
    (contDiff_uncurry_dfiLocalizedWeight hf hφ)
    (a : ℝ) (b : ℝ) r s x y]
  rw [norm_smul, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (pow_nonneg ha0 r), abs_of_nonneg (pow_nonneg hb0 s)]
  calc
    (a : ℝ) ^ r * (b : ℝ) ^ s *
        ‖dfiMixedDeriv r s (dfiLocalizedWeight f φ h)
          ((a : ℝ) * x) ((b : ℝ) * y)‖ ≤
      (a : ℝ) ^ r * (b : ℝ) ^ s *
        (C r s * U⁻¹ ^ (r + s)) :=
      mul_le_mul_of_nonneg_left
        ((hbound r s ((a : ℝ) * x) ((b : ℝ) * y)).2) hfactor
    _ = C r s * ((a : ℝ) / U) ^ r * ((b : ℝ) / U) ^ s := by
      simp only [pow_add, div_eq_mul_inv, mul_pow]
      ring
    _ ≤ Cmax * ((a : ℝ) / U) ^ r * ((b : ℝ) / U) ^ s := by
      gcongr

/-- Arithmetic-uniform version of the equation-(21) affine derivative
profile.  The constant is selected before the shift and both dilation
parameters, which is the quantifier order required by DFI's final error
term. -/
theorem exists_uniform_norm_dfiMixedDeriv_affine_localized_all
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (hscale : U ≤ P⁻¹ * min X Y) (i j : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (h : ℝ) (a b : ℕ), ∀ r ≤ i, ∀ s ≤ j, ∀ x y : ℝ,
        ‖dfiMixedDeriv r s
          (fun x' y' => dfiLocalizedWeight f φ h
            ((a : ℝ) * x') ((b : ℝ) * y')) x y‖ ≤
          C * ((a : ℝ) / U) ^ r * ((b : ℝ) / U) ^ s := by
  choose C hC hbound using fun r s =>
    dfiEquation21_uniform_in_shift hf hbox hφ hscale r s
  let Cmax := ∑ r ∈ Finset.range (i + 1),
    ∑ s ∈ Finset.range (j + 1), C r s
  have hCmax : 0 < Cmax := by
    dsimp [Cmax]
    have hinner : ∀ r ∈ Finset.range (i + 1),
        0 < ∑ s ∈ Finset.range (j + 1), C r s := by
      intro r _hr
      exact Finset.sum_pos (fun s _ => hC r s) ⟨0, by simp⟩
    exact Finset.sum_pos hinner ⟨0, by simp⟩
  refine ⟨Cmax, hCmax, ?_⟩
  intro h a b r hr s hs x y
  have hrmem : r ∈ Finset.range (i + 1) := by simp [hr]
  have hsmem : s ∈ Finset.range (j + 1) := by simp [hs]
  have hCle : C r s ≤ Cmax := by
    dsimp [Cmax]
    exact (Finset.single_le_sum (fun t _ => (hC r t).le) hsmem).trans
      (Finset.single_le_sum
        (fun t _ => Finset.sum_nonneg (fun u _ => (hC t u).le)) hrmem)
  have hU : 0 < U := hφ.U_pos
  have ha0 : 0 ≤ (a : ℝ) := Nat.cast_nonneg a
  have hb0 : 0 ≤ (b : ℝ) := Nat.cast_nonneg b
  have hfactor : 0 ≤ ((a : ℝ) ^ r * (b : ℝ) ^ s) := by positivity
  rw [dfiMixedDeriv_affine_scale
    (contDiff_uncurry_dfiLocalizedWeight hf hφ)
    (a : ℝ) (b : ℝ) r s x y]
  rw [norm_smul, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (pow_nonneg ha0 r), abs_of_nonneg (pow_nonneg hb0 s)]
  calc
    (a : ℝ) ^ r * (b : ℝ) ^ s *
        ‖dfiMixedDeriv r s (dfiLocalizedWeight f φ h)
          ((a : ℝ) * x) ((b : ℝ) * y)‖ ≤
      (a : ℝ) ^ r * (b : ℝ) ^ s *
        (C r s * U⁻¹ ^ (r + s)) :=
      mul_le_mul_of_nonneg_left
        ((hbound r s h ((a : ℝ) * x) ((b : ℝ) * y)).2) hfactor
    _ = C r s * ((a : ℝ) / U) ^ r * ((b : ℝ) / U) ^ s := by
      simp only [pow_add, div_eq_mul_inv, mul_pow]
      ring
    _ ≤ Cmax * ((a : ℝ) / U) ^ r * ((b : ℝ) / U) ^ s := by
      gcongr

/-- DFI equation (28).  Under the source choice `U = Q²` and the active
modulus range `q ≤ 2Q`, the complete equation-(23) weight has one factor
`(qQ)⁻¹` and each mixed derivative costs at most `ab/(qQ)`. -/
theorem dfiEquation28
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2)
    (a b q : ℕ) (ha : 0 < a) (hb : 0 < b) (hq : 0 < q)
    (hqQ : (q : ℝ) ≤ 2 * Q) (h : ℤ) (i j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : ℝ,
      ‖dfiMixedDeriv i j
        (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q) x y‖ ≤
        C * ((q : ℝ) * Q)⁻¹ *
          (((a : ℝ) * (b : ℝ)) / ((q : ℝ) * Q)) ^ (i + j) := by
  obtain ⟨CF, hCF, hFbound⟩ :=
    exists_uniform_norm_dfiMixedDeriv_affine_localized_le
      hf hbox hφ hscale (h : ℝ) 1 1 i j
  obtain ⟨Cδ, hCδ, hδbound⟩ :=
    exists_uniform_norm_iteratedDeriv_dfiDeltaKernel_le_product w (i + j)
  let A : ℝ := (a : ℝ) * (b : ℝ)
  let qQ : ℝ := (q : ℝ) * Q
  let C : ℝ := CF * Cδ * 3 ^ (i + j)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro x y
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hbR : 0 < (b : ℝ) := by exact_mod_cast hb
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hQ : 0 < Q := w.Q_pos
  have hU : 0 < U := hφ.U_pos
  have hqQpos : 0 < qQ := by
    dsimp [qQ]
    positivity
  have hA : 1 ≤ A := by
    dsimp [A]
    have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
    have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
    simpa [A] using mul_le_mul ha1 hb1 zero_le_one haR.le
  have hbaseSmooth : ContDiff ℝ ∞
      (Function.uncurry (dfiLocalizedWeight f φ h)) :=
    contDiff_uncurry_dfiLocalizedWeight hf hφ
  have hdeltaSmooth : ContDiff ℝ ∞
      (fun u : ℝ => (dfiDeltaKernel w q u : ℂ)) := by
    exact Complex.ofRealCLM.contDiff.comp (contDiff_dfiDeltaKernel w q hq)
  have hFcoarse : ∀ r ∈ Finset.range (i + 1),
      ∀ s ∈ Finset.range (j + 1), ∀ x y : ℝ,
      ‖dfiMixedDeriv r s (dfiLocalizedWeight f φ h) x y‖ ≤
        CF * ((1 : ℝ) / U) ^ r * ((1 : ℝ) / U) ^ s := by
    intro r hr s hs x' y'
    have hrle : r ≤ i := by simpa using hr
    have hsle : s ≤ j := by simpa using hs
    simpa using hFbound r hrle s hsle x' y'
  have hδcoarse : ∀ k ≤ i + j, ∀ u : ℝ,
      ‖iteratedDeriv k (fun z : ℝ => (dfiDeltaKernel w q z : ℂ)) u‖ ≤
        (Cδ * qQ⁻¹) * qQ⁻¹ ^ k := by
    intro k hk u
    rw [iteratedDeriv_ofReal_comp (dfiDeltaKernel w q)
      (contDiff_dfiDeltaKernel w q hq) k]
    rw [Complex.norm_real]
    calc
      |iteratedDeriv k (dfiDeltaKernel w q) u| =
          ‖iteratedDeriv k (dfiDeltaKernel w q) u‖ := by
            rw [Real.norm_eq_abs]
      _ ≤ Cδ * ((((q : ℝ) * Q) ^ (k + 1))⁻¹) :=
        hδbound k hk q hq u
      _ = (Cδ * qQ⁻¹) * qQ⁻¹ ^ k := by
        dsimp [qQ]
        rw [pow_succ, mul_inv_rev]
        ring
  have hphysicalSmooth : ContDiff ℝ ∞
      (Function.uncurry
        (dfiLocalizedWeight (dfiLocalizedWeight f φ h)
          (fun z : ℝ => (dfiDeltaKernel w q z : ℂ)) h)) := by
    unfold dfiLocalizedWeight Function.uncurry
    exact hbaseSmooth.mul (hdeltaSmooth.comp
      ((contDiff_fst.sub contDiff_snd).sub contDiff_const))
  have hraw : ∀ x' y' : ℝ,
      ‖dfiMixedDeriv i j
        (dfiLocalizedWeight (dfiLocalizedWeight f φ h)
          (fun z : ℝ => (dfiDeltaKernel w q z : ℂ)) h) x' y'‖ ≤
        CF * (Cδ * qQ⁻¹) * (((1 : ℝ) / U) + qQ⁻¹) ^ i *
          (((1 : ℝ) / U) + qQ⁻¹) ^ j := by
    intro x' y'
    exact norm_dfiMixedDeriv_localized_le
      hbaseSmooth hdeltaSmooth
      (P := (1 : ℝ)) (X := U) (Y := U) (U := qQ)
      (Cf := CF) (Cφ := Cδ * qQ⁻¹)
      zero_le_one hU hU hCF.le i j hFcoarse hδcoarse (h : ℝ) x' y'
  have hqQ_le_twoU : qQ ≤ 2 * U := by
    dsimp [qQ]
    rw [hUQ]
    nlinarith [mul_le_mul_of_nonneg_right hqQ hQ.le]
  have hinvU : U⁻¹ ≤ 2 * qQ⁻¹ := by
    have hhalf : 0 < qQ / 2 := by positivity
    have hhalf_le : qQ / 2 ≤ U := by linarith
    calc
      U⁻¹ ≤ (qQ / 2)⁻¹ := inv_anti₀ hhalf hhalf_le
      _ = 2 * qQ⁻¹ := by field_simp [hqQpos.ne']
  have hsum : (1 : ℝ) / U + qQ⁻¹ ≤ 3 * qQ⁻¹ := by
    rw [one_div]
    linarith
  have haA : (a : ℝ) ≤ A := by
    dsimp [A]
    nlinarith [mul_le_mul_of_nonneg_left
      (show (1 : ℝ) ≤ b by exact_mod_cast hb) haR.le]
  have hbA : (b : ℝ) ≤ A := by
    dsimp [A]
    nlinarith [mul_le_mul_of_nonneg_right
      (show (1 : ℝ) ≤ a by exact_mod_cast ha) hbR.le]
  have heq :
      dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q =
        fun x' y' =>
          dfiLocalizedWeight (dfiLocalizedWeight f φ h)
            (fun z : ℝ => (dfiDeltaKernel w q z : ℂ)) h
            ((a : ℝ) * x') ((b : ℝ) * y') := by
    rfl
  rw [heq, dfiMixedDeriv_affine_scale hphysicalSmooth
    (a : ℝ) (b : ℝ) i j x y]
  rw [norm_smul, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (pow_nonneg haR.le i), abs_of_nonneg (pow_nonneg hbR.le j)]
  calc
    (a : ℝ) ^ i * (b : ℝ) ^ j *
        ‖dfiMixedDeriv i j
          (dfiLocalizedWeight (dfiLocalizedWeight f φ h)
            (fun z : ℝ => (dfiDeltaKernel w q z : ℂ)) h)
          ((a : ℝ) * x) ((b : ℝ) * y)‖ ≤
      (a : ℝ) ^ i * (b : ℝ) ^ j *
        (CF * (Cδ * qQ⁻¹) * (((1 : ℝ) / U) + qQ⁻¹) ^ i *
          (((1 : ℝ) / U) + qQ⁻¹) ^ j) := by
      gcongr
      exact hraw _ _
    _ ≤ (a : ℝ) ^ i * (b : ℝ) ^ j *
        (CF * (Cδ * qQ⁻¹) * (3 * qQ⁻¹) ^ i *
          (3 * qQ⁻¹) ^ j) := by gcongr
    _ = C * qQ⁻¹ * ((a : ℝ) / qQ) ^ i * ((b : ℝ) / qQ) ^ j := by
      dsimp [C]
      simp only [div_eq_mul_inv, mul_pow, pow_add]
      ring
    _ ≤ C * qQ⁻¹ * (A / qQ) ^ i * (A / qQ) ^ j := by
      gcongr
    _ = C * qQ⁻¹ * (A / qQ) ^ (i + j) := by
      rw [pow_add]
      ring
    _ = C * ((q : ℝ) * Q)⁻¹ *
        (((a : ℝ) * (b : ℝ)) / ((q : ℝ) * Q)) ^ (i + j) := by
      rfl

/-- Fully arithmetic-uniform equation (28).  Its constant is chosen before
`a`, `b`, the shift, and the active modulus; this is the source-level
quantifier order needed when summing equation (24). -/
theorem dfiEquation28_uniform
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2) (i j : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b → 0 < q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (x y : ℝ),
        ‖dfiMixedDeriv i j
          (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q) x y‖ ≤
          C * ((q : ℝ) * Q)⁻¹ *
            (((a : ℝ) * (b : ℝ)) / ((q : ℝ) * Q)) ^ (i + j) := by
  obtain ⟨CF, hCF, hFbound⟩ :=
    exists_uniform_norm_dfiMixedDeriv_affine_localized_all
      hf hbox hφ hscale i j
  obtain ⟨Cδ, hCδ, hδbound⟩ :=
    exists_uniform_norm_iteratedDeriv_dfiDeltaKernel_le_product w (i + j)
  let C : ℝ := CF * Cδ * 3 ^ (i + j)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro a b q ha hb hq hqQ h x y
  let A : ℝ := (a : ℝ) * (b : ℝ)
  let qQ : ℝ := (q : ℝ) * Q
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hbR : 0 < (b : ℝ) := by exact_mod_cast hb
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hQ : 0 < Q := w.Q_pos
  have hU : 0 < U := hφ.U_pos
  have hqQpos : 0 < qQ := by
    dsimp [qQ]
    positivity
  have hA : 1 ≤ A := by
    dsimp [A]
    have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
    have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
    simpa [A] using mul_le_mul ha1 hb1 zero_le_one haR.le
  have hbaseSmooth : ContDiff ℝ ∞
      (Function.uncurry (dfiLocalizedWeight f φ h)) :=
    contDiff_uncurry_dfiLocalizedWeight hf hφ
  have hdeltaSmooth : ContDiff ℝ ∞
      (fun u : ℝ => (dfiDeltaKernel w q u : ℂ)) := by
    exact Complex.ofRealCLM.contDiff.comp (contDiff_dfiDeltaKernel w q hq)
  have hFcoarse : ∀ r ∈ Finset.range (i + 1),
      ∀ s ∈ Finset.range (j + 1), ∀ x y : ℝ,
      ‖dfiMixedDeriv r s (dfiLocalizedWeight f φ h) x y‖ ≤
        CF * ((1 : ℝ) / U) ^ r * ((1 : ℝ) / U) ^ s := by
    intro r hr s hs x' y'
    have hrle : r ≤ i := by simpa using hr
    have hsle : s ≤ j := by simpa using hs
    simpa using hFbound h 1 1 r hrle s hsle x' y'
  have hδcoarse : ∀ k ≤ i + j, ∀ u : ℝ,
      ‖iteratedDeriv k (fun z : ℝ => (dfiDeltaKernel w q z : ℂ)) u‖ ≤
        (Cδ * qQ⁻¹) * qQ⁻¹ ^ k := by
    intro k hk u
    rw [iteratedDeriv_ofReal_comp (dfiDeltaKernel w q)
      (contDiff_dfiDeltaKernel w q hq) k]
    rw [Complex.norm_real]
    calc
      |iteratedDeriv k (dfiDeltaKernel w q) u| =
          ‖iteratedDeriv k (dfiDeltaKernel w q) u‖ := by
            rw [Real.norm_eq_abs]
      _ ≤ Cδ * ((((q : ℝ) * Q) ^ (k + 1))⁻¹) :=
        hδbound k hk q hq u
      _ = (Cδ * qQ⁻¹) * qQ⁻¹ ^ k := by
        dsimp [qQ]
        rw [pow_succ, mul_inv_rev]
        ring
  have hphysicalSmooth : ContDiff ℝ ∞
      (Function.uncurry
        (dfiLocalizedWeight (dfiLocalizedWeight f φ h)
          (fun z : ℝ => (dfiDeltaKernel w q z : ℂ)) h)) := by
    unfold dfiLocalizedWeight Function.uncurry
    exact hbaseSmooth.mul (hdeltaSmooth.comp
      ((contDiff_fst.sub contDiff_snd).sub contDiff_const))
  have hraw : ∀ x' y' : ℝ,
      ‖dfiMixedDeriv i j
        (dfiLocalizedWeight (dfiLocalizedWeight f φ h)
          (fun z : ℝ => (dfiDeltaKernel w q z : ℂ)) h) x' y'‖ ≤
        CF * (Cδ * qQ⁻¹) * (((1 : ℝ) / U) + qQ⁻¹) ^ i *
          (((1 : ℝ) / U) + qQ⁻¹) ^ j := by
    intro x' y'
    exact norm_dfiMixedDeriv_localized_le
      hbaseSmooth hdeltaSmooth
      (P := (1 : ℝ)) (X := U) (Y := U) (U := qQ)
      (Cf := CF) (Cφ := Cδ * qQ⁻¹)
      zero_le_one hU hU hCF.le i j hFcoarse hδcoarse (h : ℝ) x' y'
  have hqQ_le_twoU : qQ ≤ 2 * U := by
    dsimp [qQ]
    rw [hUQ]
    nlinarith [mul_le_mul_of_nonneg_right hqQ hQ.le]
  have hinvU : U⁻¹ ≤ 2 * qQ⁻¹ := by
    have hhalf : 0 < qQ / 2 := by positivity
    have hhalf_le : qQ / 2 ≤ U := by linarith
    calc
      U⁻¹ ≤ (qQ / 2)⁻¹ := inv_anti₀ hhalf hhalf_le
      _ = 2 * qQ⁻¹ := by field_simp [hqQpos.ne']
  have hsum : (1 : ℝ) / U + qQ⁻¹ ≤ 3 * qQ⁻¹ := by
    rw [one_div]
    linarith
  have haA : (a : ℝ) ≤ A := by
    dsimp [A]
    nlinarith [mul_le_mul_of_nonneg_left
      (show (1 : ℝ) ≤ b by exact_mod_cast hb) haR.le]
  have hbA : (b : ℝ) ≤ A := by
    dsimp [A]
    nlinarith [mul_le_mul_of_nonneg_right
      (show (1 : ℝ) ≤ a by exact_mod_cast ha) hbR.le]
  have heq :
      dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q =
        fun x' y' =>
          dfiLocalizedWeight (dfiLocalizedWeight f φ h)
            (fun z : ℝ => (dfiDeltaKernel w q z : ℂ)) h
            ((a : ℝ) * x') ((b : ℝ) * y') := by
    rfl
  rw [heq, dfiMixedDeriv_affine_scale hphysicalSmooth
    (a : ℝ) (b : ℝ) i j x y]
  rw [norm_smul, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (pow_nonneg haR.le i), abs_of_nonneg (pow_nonneg hbR.le j)]
  calc
    (a : ℝ) ^ i * (b : ℝ) ^ j *
        ‖dfiMixedDeriv i j
          (dfiLocalizedWeight (dfiLocalizedWeight f φ h)
            (fun z : ℝ => (dfiDeltaKernel w q z : ℂ)) h)
          ((a : ℝ) * x) ((b : ℝ) * y)‖ ≤
      (a : ℝ) ^ i * (b : ℝ) ^ j *
        (CF * (Cδ * qQ⁻¹) * (((1 : ℝ) / U) + qQ⁻¹) ^ i *
          (((1 : ℝ) / U) + qQ⁻¹) ^ j) := by
      gcongr
      exact hraw _ _
    _ ≤ (a : ℝ) ^ i * (b : ℝ) ^ j *
        (CF * (Cδ * qQ⁻¹) * (3 * qQ⁻¹) ^ i *
          (3 * qQ⁻¹) ^ j) := by gcongr
    _ = C * qQ⁻¹ * ((a : ℝ) / qQ) ^ i * ((b : ℝ) / qQ) ^ j := by
      dsimp [C]
      simp only [div_eq_mul_inv, mul_pow, pow_add]
      ring
    _ ≤ C * qQ⁻¹ * (A / qQ) ^ i * (A / qQ) ^ j := by
      gcongr
    _ = C * qQ⁻¹ * (A / qQ) ^ (i + j) := by
      rw [pow_add]
      ring
    _ = C * ((q : ℝ) * Q)⁻¹ *
        (((a : ℝ) * (b : ℝ)) / ((q : ℝ) * Q)) ^ (i + j) := by
      rfl

end RiemannZeta.GuthMaynard

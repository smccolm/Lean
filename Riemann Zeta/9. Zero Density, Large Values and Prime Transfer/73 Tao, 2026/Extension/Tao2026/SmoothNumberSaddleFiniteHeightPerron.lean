import Tao2026.SmoothNumberSaddleHTMinorArcIntegralQuarter
import Tao2026.SmoothNumberSaddlePerronCutoff
import Tao2026.SmoothNumberSaddleMainTermGrowth
import Tao2026.SmoothNumberSaddleHTPerronArithmeticSharp

/-!
# Finite-height sharp Perron inversion at the HT ceiling

This module bounds the coefficient-free smooth-number sharp-Perron error at
a finite HT source height.  The near-diagonal terms retain their harmonic
distance, while the far terms are summed by the smooth Dirichlet series.
The quarter-epsilon ceiling is then large enough to make the full error
negligible uniformly in every fixed positive critical parameter.
-/

open Filter Topology MeasureTheory Set Complex Finset
open scoped BigOperators Interval

namespace Tao2026

noncomputable section

/-- The coefficient-free endpoint allowance in finite-height sharp Perron. -/
noncomputable def smoothSaddlePerronEndpointWeight
    (X n : ℕ) : ℝ :=
  if n = X then 3 / 2 else 0

theorem smoothSaddlePerronEndpointWeight_nonneg (X n : ℕ) :
    0 ≤ smoothSaddlePerronEndpointWeight X n := by
  unfold smoothSaddlePerronEndpointWeight
  split_ifs <;> norm_num

theorem summable_smoothSaddlePerronEndpointWeight (X : ℕ) :
    Summable (smoothSaddlePerronEndpointWeight X) := by
  apply summable_of_ne_finset_zero (s := {X})
  intro n hn
  have hne : n ≠ X := by simpa using hn
  simp [smoothSaddlePerronEndpointWeight, hne]

theorem tsum_smoothSaddlePerronEndpointWeight (X : ℕ) :
    ∑' n : ℕ, smoothSaddlePerronEndpointWeight X n = 3 / 2 := by
  rw [tsum_eq_sum (s := {X})]
  · simp [smoothSaddlePerronEndpointWeight]
  · intro n hn
    have hne : n ≠ X := by simpa using hn
    simp [smoothSaddlePerronEndpointWeight, hne]

/-- Replace the logarithmic sharp-Perron denominator by additive distance. -/
theorem norm_smoothSharpPerronKernel_sub_cutoff_le_additive
    {X y : ℕ} {sigma T : ℝ} (hsigma : 0 < sigma) (hT : 0 < T)
    (hX : 1 ≤ X) (n : Nat.smoothNumbers (y + 1)) (hne : n.1 ≠ X) :
    ‖GafniTao.sharpPerronKernel sigma T X n.1 -
        smoothSharpPerronCutoff X y n‖ ≤
      (((X : ℝ) / n.1) ^ sigma / (Real.pi * T)) *
        (max (X : ℝ) (n.1 : ℝ) / |(X : ℝ) - n.1|) := by
  have hn : 1 ≤ n.1 := Nat.one_le_iff_ne_zero.mpr
    (Nat.ne_zero_of_mem_smoothNumbers n.2)
  have hXpos : 0 < (X : ℝ) := by positivity
  have hnpos : 0 < (n.1 : ℝ) := by positivity
  have hpiT : 0 < Real.pi * T := mul_pos Real.pi_pos hT
  have hbase : 0 ≤ ((X : ℝ) / n.1) ^ sigma / (Real.pi * T) :=
    div_nonneg (Real.rpow_nonneg (div_pos hXpos hnpos).le _) hpiT.le
  rcases lt_or_gt_of_ne hne with hnX | hXn
  · have hnXreal : (n.1 : ℝ) < X := by exact_mod_cast hnX
    have hInv := GafniTao.one_div_log_div_le_div_sub_of_pos_of_lt
      hnpos hnXreal
    refine (norm_smoothSharpPerronKernel_sub_cutoff_le_of_lt
      hsigma hT hX n hnX).trans ?_
    rw [max_eq_left hnXreal.le,
      abs_of_nonneg (sub_nonneg.mpr hnXreal.le)]
    calc
      ((X : ℝ) / n.1) ^ sigma /
          (Real.pi * T * Real.log ((X : ℝ) / n.1)) =
        (((X : ℝ) / n.1) ^ sigma / (Real.pi * T)) *
          (1 / Real.log ((X : ℝ) / n.1)) := by ring
      _ ≤ (((X : ℝ) / n.1) ^ sigma / (Real.pi * T)) *
          ((X : ℝ) / ((X : ℝ) - n.1)) :=
        mul_le_mul_of_nonneg_left hInv hbase
  · have hXnreal : (X : ℝ) < n.1 := by exact_mod_cast hXn
    have hInv := GafniTao.one_div_neg_log_div_le_div_sub_of_pos_of_lt
      hXpos hXnreal
    refine (norm_smoothSharpPerronKernel_sub_cutoff_le_of_gt
      hsigma hT hX n hXn).trans ?_
    rw [max_eq_right hXnreal.le,
      abs_of_nonpos (sub_nonpos.mpr hXnreal.le), neg_sub]
    calc
      ((X : ℝ) / n.1) ^ sigma /
          (Real.pi * T * (-Real.log ((X : ℝ) / n.1))) =
        (((X : ℝ) / n.1) ^ sigma / (Real.pi * T)) *
          (1 / (-Real.log ((X : ℝ) / n.1))) := by ring
      _ ≤ (((X : ℝ) / n.1) ^ sigma / (Real.pi * T)) *
          ((n.1 : ℝ) / ((n.1 : ℝ) - X)) :=
        mul_le_mul_of_nonneg_left hInv hbase

/-- In the multiplicative near range, a coefficient-free Perron error is a
fixed multiple of the harmonic distance weight. -/
theorem norm_smoothSharpPerronKernel_sub_cutoff_le_near
    {X y : ℕ} {sigma T : ℝ} (hsigma : 0 < sigma) (hsigmaOne : sigma ≤ 1)
    (hT : 0 < T) (hX : 2 ≤ X) (n : Nat.smoothNumbers (y + 1))
    (hne : n.1 ≠ X) (hnLower : (X : ℝ) / 2 < n.1)
    (hnUpper : (n.1 : ℝ) < 2 * X) :
    ‖GafniTao.sharpPerronKernel sigma T X n.1 -
        smoothSharpPerronCutoff X y n‖ ≤
      (4 * X / (Real.pi * T)) *
        smoothSaddleHTPerronHarmonicWeight X n.1 := by
  have hn : 1 ≤ n.1 := Nat.one_le_iff_ne_zero.mpr
    (Nat.ne_zero_of_mem_smoothNumbers n.2)
  have hXpos : 0 < (X : ℝ) := by positivity
  have hnpos : 0 < (n.1 : ℝ) := by positivity
  have hratio0 : 0 ≤ (X : ℝ) / n.1 := (div_pos hXpos hnpos).le
  have hratio2 : (X : ℝ) / n.1 ≤ 2 := by
    rw [div_le_iff₀ hnpos]
    linarith
  have hpow : ((X : ℝ) / n.1) ^ sigma ≤ 2 := by
    calc
      ((X : ℝ) / n.1) ^ sigma ≤ (2 : ℝ) ^ sigma :=
        Real.rpow_le_rpow hratio0 hratio2 hsigma.le
      _ ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hsigmaOne
      _ = 2 := by norm_num
  have hmax : max (X : ℝ) (n.1 : ℝ) ≤ 2 * X :=
    max_le (by linarith) hnUpper.le
  have hdist : 0 < |(X : ℝ) - (n.1 : ℝ)| := by
    rw [abs_pos, sub_ne_zero]
    exact_mod_cast Ne.symm hne
  have hpiT : 0 < Real.pi * T := mul_pos Real.pi_pos hT
  have hweight := smoothSaddleHTPerronHarmonicWeight_eq_of_near hne
    (by exact_mod_cast hnUpper)
  refine (norm_smoothSharpPerronKernel_sub_cutoff_le_additive
    hsigma hT (show 1 ≤ X by omega) n hne).trans ?_
  rw [hweight]
  calc
    (((X : ℝ) / n.1) ^ sigma / (Real.pi * T)) *
        (max (X : ℝ) (n.1 : ℝ) / |(X : ℝ) - n.1|) ≤
      (2 / (Real.pi * T)) *
        ((2 * X) / |(X : ℝ) - n.1|) := by
      exact mul_le_mul
        (div_le_div_of_nonneg_right hpow hpiT.le)
        (div_le_div_of_nonneg_right hmax hdist.le)
        (div_nonneg (by positivity) hdist.le)
        (div_nonneg (by norm_num) hpiT.le)
    _ = (4 * X / (Real.pi * T)) *
        (1 / |(X : ℝ) - n.1|) := by ring

/-- Outside the multiplicative near range, the coefficient-free Perron error
is controlled by the positive smooth Dirichlet-series term. -/
theorem norm_smoothSharpPerronKernel_sub_cutoff_le_far
    {X y : ℕ} {sigma T : ℝ} (hsigma : 0 < sigma) (hT : 0 < T)
    (hX : 2 ≤ X) (n : Nat.smoothNumbers (y + 1))
    (hfar : (n.1 : ℝ) ≤ (X : ℝ) / 2 ∨ 2 * (X : ℝ) ≤ n.1) :
    ‖GafniTao.sharpPerronKernel sigma T X n.1 -
        smoothSharpPerronCutoff X y n‖ ≤
      (2 * (X : ℝ) ^ sigma / (Real.pi * T)) *
        (n.1 : ℝ) ^ (-sigma) := by
  have hn : 1 ≤ n.1 := Nat.one_le_iff_ne_zero.mpr
    (Nat.ne_zero_of_mem_smoothNumbers n.2)
  have hXpos : 0 < (X : ℝ) := by positivity
  have hnpos : 0 < (n.1 : ℝ) := by positivity
  have hne : n.1 ≠ X := by
    intro heq
    subst X
    rcases hfar with h | h <;> nlinarith
  have hfactor := GafniTao.max_div_abs_sub_le_two_of_far
    hXpos hnpos hfar
  have hbase : 0 ≤ ((X : ℝ) / n.1) ^ sigma / (Real.pi * T) :=
    div_nonneg (Real.rpow_nonneg (div_pos hXpos hnpos).le _)
      (mul_nonneg Real.pi_pos.le hT.le)
  refine (norm_smoothSharpPerronKernel_sub_cutoff_le_additive
    hsigma hT (show 1 ≤ X by omega) n hne).trans ?_
  calc
    (((X : ℝ) / n.1) ^ sigma / (Real.pi * T)) *
        (max (X : ℝ) (n.1 : ℝ) / |(X : ℝ) - n.1|) ≤
      (((X : ℝ) / n.1) ^ sigma / (Real.pi * T)) * 2 :=
        mul_le_mul_of_nonneg_left hfactor hbase
    _ = (2 * (X : ℝ) ^ sigma / (Real.pi * T)) *
        (n.1 : ℝ) ^ (-sigma) := by
      rw [Real.div_rpow hXpos.le hnpos.le, Real.rpow_neg hnpos.le]
      ring

/-- A summable endpoint/near/far majorant for the coefficient-free smooth
sharp-Perron error. -/
noncomputable def smoothSaddleFiniteHeightPerronMajorant
    (X y : ℕ) (T : ℝ) (n : Nat.smoothNumbers (y + 1)) : ℝ :=
  smoothSaddlePerronEndpointWeight X n.1 +
    (4 * X / (Real.pi * T)) *
      smoothSaddleHTPerronHarmonicWeight X n.1 +
    (2 * (X : ℝ) ^ smoothSaddlePoint X y / (Real.pi * T)) *
      (n.1 : ℝ) ^ (-smoothSaddlePoint X y)

theorem smoothSaddleFiniteHeightPerronMajorant_nonneg
    {X y : ℕ} (hX : 2 ≤ X) {T : ℝ} (hT : 0 < T)
    (n : Nat.smoothNumbers (y + 1)) :
    0 ≤ smoothSaddleFiniteHeightPerronMajorant X y T n := by
  unfold smoothSaddleFiniteHeightPerronMajorant
  exact add_nonneg
    (add_nonneg (smoothSaddlePerronEndpointWeight_nonneg X n.1)
      (mul_nonneg (div_nonneg (by positivity)
        (mul_nonneg Real.pi_pos.le hT.le))
        (smoothSaddleHTPerronHarmonicWeight_nonneg X n.1)))
    (mul_nonneg (div_nonneg
      (mul_nonneg (by norm_num) (Real.rpow_nonneg (by positivity) _))
      (mul_nonneg Real.pi_pos.le hT.le))
      (Real.rpow_nonneg (by positivity) _))

theorem norm_smoothSharpPerronKernel_sub_cutoff_le_finiteHeightMajorant
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) {T : ℝ} (hT : 0 < T)
    (hsigmaOne : smoothSaddlePoint X y ≤ 1)
    (n : Nat.smoothNumbers (y + 1)) :
    ‖GafniTao.sharpPerronKernel (smoothSaddlePoint X y) T X n.1 -
        smoothSharpPerronCutoff X y n‖ ≤
      smoothSaddleFiniteHeightPerronMajorant X y T n := by
  let sigma := smoothSaddlePoint X y
  have hsigma : 0 < sigma := smoothSaddlePoint_pos hX hy
  by_cases hne : n.1 = X
  · have hendpoint := norm_smoothSharpPerronKernel_sub_cutoff_le_three_halves_of_eq
      (T := T) hsigma (show 1 ≤ X by omega) n hne
    unfold smoothSaddleFiniteHeightPerronMajorant
    rw [smoothSaddlePerronEndpointWeight, if_pos hne]
    have hrest : 0 ≤
        (4 * (X : ℝ) / (Real.pi * T)) *
            smoothSaddleHTPerronHarmonicWeight X n.1 +
          (2 * (X : ℝ) ^ smoothSaddlePoint X y / (Real.pi * T)) *
            (n.1 : ℝ) ^ (-smoothSaddlePoint X y) := by
      exact add_nonneg
        (mul_nonneg (by positivity)
          (smoothSaddleHTPerronHarmonicWeight_nonneg X n.1))
        (mul_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _))
    apply hendpoint.trans
    linarith
  · have hendpoint : smoothSaddlePerronEndpointWeight X n.1 = 0 := by
      simp [smoothSaddlePerronEndpointWeight, hne]
    by_cases hnear : (X : ℝ) / 2 < n.1 ∧ (n.1 : ℝ) < 2 * X
    · have hbound := norm_smoothSharpPerronKernel_sub_cutoff_le_near
        hsigma hsigmaOne hT hX n hne hnear.1 hnear.2
      unfold smoothSaddleFiniteHeightPerronMajorant
      rw [hendpoint, zero_add]
      exact hbound.trans (le_add_of_nonneg_right (mul_nonneg
        (div_nonneg
          (mul_nonneg (by norm_num) (Real.rpow_nonneg (by positivity) _))
          (mul_nonneg Real.pi_pos.le hT.le))
        (Real.rpow_nonneg (by positivity) _)))
    · have hfar : (n.1 : ℝ) ≤ (X : ℝ) / 2 ∨
          2 * (X : ℝ) ≤ n.1 := by
        by_cases hlow : (n.1 : ℝ) ≤ (X : ℝ) / 2
        · exact Or.inl hlow
        · exact Or.inr (le_of_not_gt (fun hupper => hnear
            ⟨lt_of_not_ge hlow, hupper⟩))
      have hbound := norm_smoothSharpPerronKernel_sub_cutoff_le_far
        hsigma hT hX n hfar
      unfold smoothSaddleFiniteHeightPerronMajorant
      rw [hendpoint, zero_add]
      exact hbound.trans (le_add_of_nonneg_left (mul_nonneg
        (div_nonneg (by positivity) (mul_nonneg Real.pi_pos.le hT.le))
        (smoothSaddleHTPerronHarmonicWeight_nonneg X n.1)))

theorem summable_smoothSaddleFiniteHeightPerronMajorant
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) (T : ℝ) :
    Summable (smoothSaddleFiniteHeightPerronMajorant X y T) := by
  let sigma := smoothSaddlePoint X y
  have hsigma : 0 < sigma := smoothSaddlePoint_pos hX hy
  have he : Summable (fun n : Nat.smoothNumbers (y + 1) =>
      smoothSaddlePerronEndpointWeight X n.1) :=
    (summable_smoothSaddlePerronEndpointWeight X).comp_injective
      Subtype.val_injective
  have hh : Summable (fun n : Nat.smoothNumbers (y + 1) =>
      smoothSaddleHTPerronHarmonicWeight X n.1) :=
    (summable_smoothSaddleHTPerronHarmonicWeight X).comp_injective
      Subtype.val_injective
  have hd : Summable (fun n : Nat.smoothNumbers (y + 1) =>
      (n.1 : ℝ) ^ (-sigma)) :=
    (summable_smoothDirichletSeries_and_eq_eulerProduct
      (y + 1) hsigma).1
  exact (he.add (hh.mul_left (4 * X / (Real.pi * T)))).add
    (hd.mul_left (2 * (X : ℝ) ^ sigma / (Real.pi * T)))

/-- Arithmetic summation of the coefficient-free finite-height majorant. -/
theorem tsum_smoothSaddleFiniteHeightPerronMajorant_le
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) {T : ℝ} (hT : 0 < T) :
    (∑' n : Nat.smoothNumbers (y + 1),
        smoothSaddleFiniteHeightPerronMajorant X y T n) ≤
      3 / 2 +
        (4 * X / (Real.pi * T)) * (8 * (harmonic (X + 1) : ℝ)) +
        (2 * (X : ℝ) ^ smoothSaddlePoint X y / (Real.pi * T)) *
          smoothDirichletSeries (y + 1) (smoothSaddlePoint X y) := by
  let sigma := smoothSaddlePoint X y
  have hsigma : 0 < sigma := smoothSaddlePoint_pos hX hy
  have he : Summable (fun n : Nat.smoothNumbers (y + 1) =>
      smoothSaddlePerronEndpointWeight X n.1) :=
    (summable_smoothSaddlePerronEndpointWeight X).comp_injective
      Subtype.val_injective
  have hh : Summable (fun n : Nat.smoothNumbers (y + 1) =>
      smoothSaddleHTPerronHarmonicWeight X n.1) :=
    (summable_smoothSaddleHTPerronHarmonicWeight X).comp_injective
      Subtype.val_injective
  have hd : Summable (fun n : Nat.smoothNumbers (y + 1) =>
      (n.1 : ℝ) ^ (-sigma)) :=
    (summable_smoothDirichletSeries_and_eq_eulerProduct
      (y + 1) hsigma).1
  have he_le : (∑' n : Nat.smoothNumbers (y + 1),
      smoothSaddlePerronEndpointWeight X n.1) ≤ 3 / 2 := by
    calc
      _ ≤ ∑' n : ℕ, smoothSaddlePerronEndpointWeight X n := by
        exact Summable.tsum_subtype_le _ _
          (smoothSaddlePerronEndpointWeight_nonneg X)
          (summable_smoothSaddlePerronEndpointWeight X)
      _ = 3 / 2 := tsum_smoothSaddlePerronEndpointWeight X
  have hh_le : (∑' n : Nat.smoothNumbers (y + 1),
      smoothSaddleHTPerronHarmonicWeight X n.1) ≤
        8 * (harmonic (X + 1) : ℝ) := by
    calc
      _ ≤ ∑' n : ℕ, smoothSaddleHTPerronHarmonicWeight X n := by
        exact Summable.tsum_subtype_le _ _
          (smoothSaddleHTPerronHarmonicWeight_nonneg X)
          (summable_smoothSaddleHTPerronHarmonicWeight X)
      _ ≤ 8 * (harmonic (X + 1) : ℝ) :=
        tsum_smoothSaddleHTPerronHarmonicWeight_le X
  unfold smoothSaddleFiniteHeightPerronMajorant
  rw [Summable.tsum_add
      (he.add (hh.mul_left (4 * X / (Real.pi * T))))
      (hd.mul_left (2 * (X : ℝ) ^ sigma / (Real.pi * T))),
    Summable.tsum_add he (hh.mul_left (4 * X / (Real.pi * T))),
    tsum_mul_left, tsum_mul_left, show
      (∑' n : Nat.smoothNumbers (y + 1), (n.1 : ℝ) ^ (-sigma)) =
        smoothDirichletSeries (y + 1) sigma from rfl]
  have hA : 0 ≤ 4 * (X : ℝ) / (Real.pi * T) := by positivity
  have hB : 0 ≤ 2 * (X : ℝ) ^ sigma / (Real.pi * T) := by positivity
  exact add_le_add (add_le_add he_le
    (mul_le_mul_of_nonneg_left hh_le hA)) le_rfl

/-- The literal finite-height smooth Perron line differs from the inclusive
smooth cutoff by at most the explicit endpoint/near/far arithmetic bound. -/
theorem norm_smoothSharpPerron_tsum_sub_psiNat_le
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) {T : ℝ} (hT : 0 < T)
    (hsigmaOne : smoothSaddlePoint X y ≤ 1) :
    ‖(∑' n : Nat.smoothNumbers (y + 1),
        GafniTao.sharpPerronKernel (smoothSaddlePoint X y) T X n.1) -
        (psiNat X y : ℂ)‖ ≤
      3 / 2 +
        (4 * X / (Real.pi * T)) * (8 * (harmonic (X + 1) : ℝ)) +
        (2 * (X : ℝ) ^ smoothSaddlePoint X y / (Real.pi * T)) *
          smoothDirichletSeries (y + 1) (smoothSaddlePoint X y) := by
  let e : Nat.smoothNumbers (y + 1) → ℂ := fun n =>
    GafniTao.sharpPerronKernel (smoothSaddlePoint X y) T X n.1 -
      smoothSharpPerronCutoff X y n
  let M := smoothSaddleFiniteHeightPerronMajorant X y T
  have hM := summable_smoothSaddleFiniteHeightPerronMajorant hX hy T
  have hpoint : ∀ n, ‖e n‖ ≤ M n := fun n =>
    norm_smoothSharpPerronKernel_sub_cutoff_le_finiteHeightMajorant
      hX hy hT hsigmaOne n
  have henorm : Summable (fun n => ‖e n‖) := by
    apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) hpoint hM
  rw [smoothSharpPerron_tsum_sub_psiNat_eq_tsum_cutoffError
    (smoothSaddlePoint_pos hX hy) (show 1 ≤ X by omega)]
  change ‖∑' n, e n‖ ≤ _
  calc
    ‖∑' n, e n‖ ≤ ∑' n, ‖e n‖ := norm_tsum_le_tsum_norm henorm
    _ ≤ ∑' n, M n := henorm.tsum_le_tsum hpoint hM
    _ ≤ _ := tsum_smoothSaddleFiniteHeightPerronMajorant_le hX hy hT

/-- The elementary main-term lower bound retains the actual saddle exponent.
This sharper numerator is what makes finite height `T = y` sufficient. -/
theorem smoothSaddleMainTerm_lower_bound_at_saddleExponent
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) (hyX : y ≤ X)
    (hsigmaLower : (1 / 2 : ℝ) ≤ smoothSaddlePoint X y)
    (hsigmaUpper : smoothSaddlePoint X y ≤ 1) :
    (X : ℝ) ^ smoothSaddlePoint X y /
        (Real.sqrt (14 * Real.pi) * Real.log X) ≤
      smoothSaddleMainTerm X y := by
  have hsigma := smoothSaddlePoint_pos hX hy
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hlogy : 0 ≤ Real.log (y : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ y by omega))
  have hlogyX : Real.log (y : ℝ) ≤ Real.log (X : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast hyX)
  have hphi := smoothSaddlePhiTwo_saddle_le_seven_log_mul_log
    hX hy hsigmaLower
  have hphiBound : smoothSaddlePhiTwo y (smoothSaddlePoint X y) ≤
      7 * (Real.log X) ^ 2 := by
    calc
      smoothSaddlePhiTwo y (smoothSaddlePoint X y) ≤
          7 * Real.log y * Real.log X := hphi
      _ ≤ 7 * (Real.log X) ^ 2 := by nlinarith
  have hinside :
      2 * Real.pi * smoothSaddlePhiTwo y (smoothSaddlePoint X y) ≤
        14 * Real.pi * (Real.log X) ^ 2 := by
    have := mul_le_mul_of_nonneg_left hphiBound
      (by positivity : 0 ≤ 2 * Real.pi)
    nlinarith
  have hsqrt :
      Real.sqrt (2 * Real.pi *
          smoothSaddlePhiTwo y (smoothSaddlePoint X y)) ≤
        Real.sqrt (14 * Real.pi) * Real.log X := by
    calc
      Real.sqrt (2 * Real.pi *
          smoothSaddlePhiTwo y (smoothSaddlePoint X y)) ≤
          Real.sqrt (14 * Real.pi * (Real.log X) ^ 2) :=
        Real.sqrt_le_sqrt hinside
      _ = Real.sqrt (14 * Real.pi) * Real.log X :=
        sqrt_fourteen_pi_mul_log_sq hlogX.le
  have hden : smoothSaddlePoint X y *
        Real.sqrt (2 * Real.pi *
          smoothSaddlePhiTwo y (smoothSaddlePoint X y)) ≤
      Real.sqrt (14 * Real.pi) * Real.log X := by
    calc
      smoothSaddlePoint X y * Real.sqrt (2 * Real.pi *
          smoothSaddlePhiTwo y (smoothSaddlePoint X y)) ≤
          1 * Real.sqrt (2 * Real.pi *
            smoothSaddlePhiTwo y (smoothSaddlePoint X y)) := by
        gcongr
      _ ≤ Real.sqrt (14 * Real.pi) * Real.log X := by simpa using hsqrt
  have hnum : (X : ℝ) ^ smoothSaddlePoint X y ≤
      Real.exp (smoothSaddlePhase X y (smoothSaddlePoint X y)) :=
    rpow_le_exp_smoothSaddlePhase (show 1 ≤ X by omega) hsigma
  have hdenPos : 0 < smoothSaddlePoint X y *
      Real.sqrt (2 * Real.pi *
        smoothSaddlePhiTwo y (smoothSaddlePoint X y)) := by
    exact mul_pos hsigma (Real.sqrt_pos.2 (mul_pos
      (mul_pos (by norm_num) Real.pi_pos)
      (smoothSaddlePhiTwo_pos hy hsigma)))
  have hupperDenPos : 0 < Real.sqrt (14 * Real.pi) * Real.log X :=
    mul_pos (Real.sqrt_pos.2 (by positivity)) hlogX
  unfold smoothSaddleMainTerm
  rw [div_le_div_iff₀ hupperDenPos hdenPos]
  exact mul_le_mul hnum hden hdenPos.le (Real.exp_pos _).le

/-- Exact cancellation of the Rankin exponential against the saddle main
term in the far part of finite-height Perron. -/
theorem smoothSaddle_rpow_mul_dirichlet_div_mainTerm
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) :
    ((X : ℝ) ^ smoothSaddlePoint X y *
        smoothDirichletSeries (y + 1) (smoothSaddlePoint X y)) /
        smoothSaddleMainTerm X y =
      smoothSaddlePoint X y *
        Real.sqrt (2 * Real.pi *
          smoothSaddlePhiTwo y (smoothSaddlePoint X y)) := by
  have hsigma := smoothSaddlePoint_pos hX hy
  have hphase : (X : ℝ) ^ smoothSaddlePoint X y *
        smoothDirichletSeries (y + 1) (smoothSaddlePoint X y) =
      Real.exp (smoothSaddlePhase X y (smoothSaddlePoint X y)) := by
    rw [smoothDirichletSeries_source_eq_eulerProduct y hsigma]
    exact rpow_mul_sourceEulerProduct_eq_exp_smoothSaddlePhase
      (show 1 ≤ X by omega) hsigma
  rw [hphase]
  unfold smoothSaddleMainTerm
  have hroot : 0 < Real.sqrt (2 * Real.pi *
      smoothSaddlePhiTwo y (smoothSaddlePoint X y)) := by
    exact Real.sqrt_pos.2 (mul_pos (mul_pos (by norm_num) Real.pi_pos)
      (smoothSaddlePhiTwo_pos hy hsigma))
  field_simp [hsigma.ne', hroot.ne', Real.exp_ne_zero]

/-- Every fixed logarithmic power is negligible compared with its argument. -/
theorem tendsto_log_pow_div_self_zero (k : ℕ) :
    Tendsto (fun x : ℝ => Real.log x ^ k / x) atTop (𝓝 0) := by
  have hlog : Tendsto (fun x : ℝ => Real.log x) atTop atTop :=
    Real.tendsto_log_atTop
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    (k : ℝ) 1 (by norm_num)).comp hlog
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  change (Real.log x) ^ (k : ℝ) * Real.exp (-1 * Real.log x) =
    Real.log x ^ k / x
  rw [Real.rpow_natCast, neg_mul, one_mul, Real.exp_neg, Real.exp_log hx]
  ring

/-- In a critical regime, `u log u` has the finite scale
`(1/alpha^2) log y`. -/
theorem IsTaoCriticalSmoothRegime.tendsto_rankinRatio_mul_log_div_log_y
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun n =>
      smoothRankinRatio (X n) (y n) *
          Real.log (smoothRankinRatio (X n) (y n)) /
        Real.log (y n : ℝ)) atTop (𝓝 (1 / α ^ 2)) := by
  have hquot :=
    (hregime.tendsto_rankinRatio_mul_log_div_log_taoZ hα).div
      hregime.2 hα.ne'
  have hquot' : Tendsto (fun n =>
      (smoothRankinRatio (X n) (y n) *
          Real.log (smoothRankinRatio (X n) (y n)) /
            Real.log (taoZ n)) /
        (Real.log (y n : ℝ) / Real.log (taoZ n)))
      atTop (𝓝 ((1 / α) / α)) := by
    simpa using hquot
  have hcongr : ∀ᶠ n in atTop,
      (smoothRankinRatio (X n) (y n) *
          Real.log (smoothRankinRatio (X n) (y n)) /
            Real.log (taoZ n)) /
        (Real.log (y n : ℝ) / Real.log (taoZ n)) =
      smoothRankinRatio (X n) (y n) *
          Real.log (smoothRankinRatio (X n) (y n)) /
        Real.log (y n : ℝ) := by
    filter_upwards [tendsto_taoZ_atTop.eventually (eventually_gt_atTop 1),
      (hregime.tendsto_log_y_atTop hα).eventually
        (eventually_gt_atTop (0 : ℝ))] with n hz hy
    field_simp [(Real.log_pos hz).ne', hy.ne']
  have h := hquot'.congr' hcongr
  have hlimit : (1 / α) / α = 1 / α ^ 2 := by
    field_simp [hα.ne']
  simpa only [hlimit] using h

/-- The fixed endpoint allowance is negligible relative to the saddle main
term. -/
theorem IsTaoCriticalSmoothRegime.tendsto_finiteHeightPerronEndpoint_div_mainTerm_zero
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun n => (3 / 2 : ℝ) /
      smoothSaddleMainTerm (X n) (y n)) atTop (𝓝 0) := by
  exact tendsto_const_nhds.div_atTop
    (hregime.tendsto_smoothSaddleMainTerm_atTop hα)

/-- The Dirichlet-series far part of finite-height Perron vanishes at the
quarter-epsilon HT ceiling after saddle normalization. -/
theorem IsTaoCriticalSmoothRegime.tendsto_finiteHeightPerronFarQuarter_div_mainTerm_zero
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun n =>
      ((2 * (X n : ℝ) ^ smoothSaddlePoint (X n) (y n) /
          (Real.pi * smoothSaddleHTFrequencyCeiling (y n) (1 / 4))) *
        smoothDirichletSeries (y n + 1)
          (smoothSaddlePoint (X n) (y n))) /
        smoothSaddleMainTerm (X n) (y n)) atTop (𝓝 0) := by
  let C := 2 * Real.sqrt (2 * Real.pi) * Real.sqrt 7 / Real.pi
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hmodel := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    (2 : ℝ) 1 (by norm_num)).comp (hregime.tendsto_log_y_atTop hα)
  have hmodel' : Tendsto (fun n => C *
      (Real.log (y n : ℝ) ^ (2 : ℕ) *
        Real.exp (-Real.log (y n : ℝ)))) atTop (𝓝 0) := by
    simpa [Real.rpow_natCast] using hmodel.const_mul C
  refine squeeze_zero' ?_ ?_ hmodel'
  · filter_upwards [hregime.eventually_two_le_X,
      hregime.eventually_two_le_y hα] with n hX hy
    have hmain : 0 < smoothSaddleMainTerm (X n) (y n) :=
      smoothSaddleMainTerm_pos hX hy
    have hT : 0 < smoothSaddleHTFrequencyCeiling (y n) (1 / 4) :=
      smoothSaddleHTFrequencyCeiling_pos _ _
    have hsigma := smoothSaddlePoint_pos hX hy
    have hseries := smoothDirichletSeries_source_pos (y n) hsigma
    exact div_nonneg
      (mul_nonneg (div_nonneg (mul_nonneg (by norm_num)
        (Real.rpow_nonneg (by positivity) _))
        (mul_nonneg Real.pi_pos.le hT.le)) hseries.le) hmain.le
  · filter_upwards [hregime.eventually_two_le_X,
      hregime.eventually_two_le_y hα,
      (hregime.tendsto_log_y_atTop hα).eventually
        (eventually_ge_atTop (1 : ℝ)),
      (hregime.tendsto_smoothSaddlePoint_one hα).eventually
        (Ici_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)),
      hregime.eventually_smoothSaddlePoint_lt_one hα,
      hregime.eventually_rankinRatio_le_log_y hα] with
      n hX hy hLone hsigmaHalf hsigmaOne huL
    let u := smoothRankinRatio (X n) (y n)
    let L := Real.log (y n : ℝ)
    let sigma := smoothSaddlePoint (X n) (y n)
    have hu : 0 < u := by dsimp [u]; exact smoothRankinRatio_pos hX hy
    have hL : 0 < L := by dsimp [L]; linarith
    have hsdDiv := smoothSaddleStandardDeviation_div_log_le_sqrt_rankinRatio
      hX hy hsigmaHalf
    have hsdPos := smoothSaddleStandardDeviation_pos hX hy
    have hsd : smoothSaddleStandardDeviation (X n) (y n) ≤
        L * Real.sqrt (7 * u) := by
      have hsd' := (div_le_iff₀ hL).mp
        (by simpa only [L, u] using hsdDiv)
      nlinarith
    have hsqrtMono : Real.sqrt u ≤ Real.sqrt L :=
      Real.sqrt_le_sqrt (by simpa only [u, L] using huL)
    have hsqrtL : Real.sqrt L ≤ L := by
      nlinarith [Real.sq_sqrt hL.le, Real.sqrt_nonneg L]
    have hsqrtMul : Real.sqrt (7 * u) = Real.sqrt 7 * Real.sqrt u := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 7)]
    have hsdBound : smoothSaddleStandardDeviation (X n) (y n) ≤
        Real.sqrt 7 * L ^ (2 : ℕ) := by
      rw [hsqrtMul] at hsd
      calc
        smoothSaddleStandardDeviation (X n) (y n) ≤
            L * (Real.sqrt 7 * Real.sqrt u) := hsd
        _ ≤ L * (Real.sqrt 7 * L) := by
          gcongr
          exact hsqrtMono.trans hsqrtL
        _ = Real.sqrt 7 * L ^ (2 : ℕ) := by ring
    have hroot : Real.sqrt (2 * Real.pi *
          smoothSaddlePhiTwo (y n) sigma) =
        Real.sqrt (2 * Real.pi) *
          smoothSaddleStandardDeviation (X n) (y n) := by
      unfold smoothSaddleStandardDeviation
      rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi)]
    have hpow : L ≤ L ^ (5 / 4 : ℝ) := by
      calc
        L = L ^ (1 : ℝ) := by simp
        _ ≤ L ^ (5 / 4 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hLone (by norm_num)
    have hexp : Real.exp (-L ^ (5 / 4 : ℝ)) ≤ Real.exp (-L) := by
      exact Real.exp_le_exp.mpr (neg_le_neg hpow)
    have hexact := smoothSaddle_rpow_mul_dirichlet_div_mainTerm hX hy
    rw [show
      ((2 * (X n : ℝ) ^ sigma /
          (Real.pi * smoothSaddleHTFrequencyCeiling (y n) (1 / 4))) *
        smoothDirichletSeries (y n + 1) sigma) /
          smoothSaddleMainTerm (X n) (y n) =
        (2 / (Real.pi * smoothSaddleHTFrequencyCeiling (y n) (1 / 4))) *
          (((X n : ℝ) ^ sigma *
            smoothDirichletSeries (y n + 1) sigma) /
              smoothSaddleMainTerm (X n) (y n)) by ring,
      hexact, smoothSaddleHTFrequencyCeiling_quarter, hroot]
    rw [show 2 / (Real.pi * Real.exp (L ^ (5 / 4 : ℝ))) *
        (sigma * (Real.sqrt (2 * Real.pi) *
          smoothSaddleStandardDeviation (X n) (y n))) =
      (2 * Real.sqrt (2 * Real.pi) / Real.pi) * sigma *
        smoothSaddleStandardDeviation (X n) (y n) *
          Real.exp (-L ^ (5 / 4 : ℝ)) by
        rw [Real.exp_neg]
        field_simp]
    calc
      (2 * Real.sqrt (2 * Real.pi) / Real.pi) * sigma *
          smoothSaddleStandardDeviation (X n) (y n) *
            Real.exp (-L ^ (5 / 4 : ℝ)) ≤
        (2 * Real.sqrt (2 * Real.pi) / Real.pi) * 1 *
          (Real.sqrt 7 * L ^ (2 : ℕ)) *
            Real.exp (-L ^ (5 / 4 : ℝ)) := by
          gcongr
      _ ≤ C * (L ^ (2 : ℕ) * Real.exp (-L)) := by
        rw [show (2 * Real.sqrt (2 * Real.pi) / Real.pi) * 1 *
            (Real.sqrt 7 * L ^ (2 : ℕ)) *
              Real.exp (-L ^ (5 / 4 : ℝ)) =
          C * (L ^ (2 : ℕ) * Real.exp (-L ^ (5 / 4 : ℝ))) by
            dsimp [C]
            ring]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hexp (pow_nonneg hL.le _)) hC

noncomputable def smoothSaddleFiniteHeightNearConstant : ℝ :=
  96 * Real.sqrt (14 * Real.pi) / Real.pi

theorem smoothSaddleFiniteHeightNearConstant_pos :
    0 < smoothSaddleFiniteHeightNearConstant := by
  unfold smoothSaddleFiniteHeightNearConstant
  positivity

/-- The quarter-epsilon ceiling absorbs the Rankin displacement and all
fixed logarithmic losses in the near-diagonal Perron error. -/
theorem IsTaoCriticalSmoothRegime.eventually_finiteHeightPerronNearScaleQuarter_le
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    ∀ᶠ n in atTop,
      smoothSaddleFiniteHeightNearConstant * Real.log (X n : ℝ) ^ (2 : ℕ) *
          (X n : ℝ) ^ (1 - smoothSaddlePoint (X n) (y n)) /
            smoothSaddleHTFrequencyCeiling (y n) (1 / 4) ≤
        1 / Real.log (y n : ℝ) := by
  let D := 1 + 1 / α ^ 2
  let C := smoothSaddleFiniteHeightNearConstant
  have hC : 0 ≤ C := by
    dsimp [C]
    exact smoothSaddleFiniteHeightNearConstant_pos.le
  have hD : 0 < D := by
    dsimp [D]
    have hsq : 0 < α ^ 2 := sq_pos_of_pos hα
    positivity
  have hratio :=
    (hregime.tendsto_rankinRatio_mul_log_div_log_y hα).eventually
      (Iio_mem_nhds (show 1 / α ^ 2 < D by dsimp [D]; linarith))
  have hrootTop : Tendsto (fun n =>
      Real.log (y n : ℝ) ^ (1 / 8 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)).comp
      (hregime.tendsto_log_y_atTop hα)
  have hrootLarge := hrootTop.eventually (eventually_ge_atTop (8 * D))
  have habsorbNat :=
    eventually_const_mul_log_rpow_mul_exp_log_rpow_le_exp_log_rpow_of_lt
      (C := C) (α := (9 / 8 : ℝ)) (β := (5 / 4 : ℝ))
      (by norm_num) (by norm_num) 5
  have habsorb := (hregime.tendsto_y_atTop hα).eventually habsorbNat
  filter_upwards [hregime.eventually_two_le_X,
    hregime.eventually_two_le_y hα,
    (hregime.tendsto_log_y_atTop hα).eventually
      (eventually_ge_atTop (1 : ℝ)),
    hregime.eventually_one_sub_saddle_lt_eight_log_ratio hα,
    hregime.eventually_rankinRatio_le_log_y hα,
    hratio, hrootLarge, habsorb] with
      n hX hy hLone hdisp huL hratio hrootLarge habsorb
  let u := smoothRankinRatio (X n) (y n)
  let L := Real.log (y n : ℝ)
  let beta := 1 - smoothSaddlePoint (X n) (y n)
  have hu : 0 < u := by dsimp [u]; exact smoothRankinRatio_pos hX hy
  have hL : 0 < L := by dsimp [L]; linarith
  have hcritical : u * Real.log u ≤ D * L := by
    have hratio' : u * Real.log u / L < D := by
      simpa only [u, L] using hratio
    exact ((div_lt_iff₀ hL).mp hratio').le
  have hlinear : 8 * D * L ≤ L ^ (9 / 8 : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hrootLarge hL.le
    calc
      8 * D * L ≤ L ^ (1 / 8 : ℝ) * L := by
        simpa only [mul_assoc] using hmul
      _ = L ^ (9 / 8 : ℝ) := by
        calc
          L ^ (1 / 8 : ℝ) * L =
              L ^ (1 / 8 : ℝ) * L ^ (1 : ℝ) := by simp
          _ = L ^ ((1 / 8 : ℝ) + 1) := (Real.rpow_add hL _ _).symm
        norm_num
  have hlogX : Real.log (X n : ℝ) = u * L := by
    dsimp [u, L, smoothRankinRatio]
    field_simp [hL.ne']
  have hbetaL : beta * L ≤ 8 * Real.log u := by
    apply (le_div_iff₀ hL).mp
    simpa only [beta, L, u] using hdisp.le
  have hbetaLogX : beta * Real.log (X n : ℝ) ≤ 8 * u * Real.log u := by
    rw [hlogX]
    have hmul := mul_le_mul_of_nonneg_left hbetaL hu.le
    nlinarith
  have hbetaBound : (X n : ℝ) ^ beta ≤
      Real.exp (L ^ (9 / 8 : ℝ)) := by
    rw [Real.rpow_def_of_pos (by positivity : 0 < (X n : ℝ))]
    apply Real.exp_le_exp.mpr
    calc
      Real.log (X n : ℝ) * beta = beta * Real.log (X n : ℝ) := by ring
      _ ≤ 8 * u * Real.log u := hbetaLogX
      _ ≤ 8 * (D * L) := by nlinarith
      _ ≤ L ^ (9 / 8 : ℝ) := by nlinarith
  have hlogXBound : Real.log (X n : ℝ) ^ (2 : ℕ) ≤ L ^ (4 : ℕ) := by
    have hlogXLe : Real.log (X n : ℝ) ≤ L ^ (2 : ℕ) := by
      rw [hlogX]
      have := mul_le_mul_of_nonneg_right huL hL.le
      nlinarith
    have hlogXNonneg : 0 ≤ Real.log (X n : ℝ) := by
      exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ X n by omega))
    nlinarith [sq_nonneg (L ^ (2 : ℕ) - Real.log (X n : ℝ))]
  have habsorb' : C * L ^ (5 : ℕ) * Real.exp (L ^ (9 / 8 : ℝ)) ≤
      Real.exp (L ^ (5 / 4 : ℝ)) := by
    simpa only [C, L, Real.rpow_natCast] using habsorb
  rw [smoothSaddleHTFrequencyCeiling_quarter]
  change C * Real.log (X n : ℝ) ^ (2 : ℕ) * (X n : ℝ) ^ beta /
      Real.exp (L ^ (5 / 4 : ℝ)) ≤ 1 / L
  have hnumer : C * Real.log (X n : ℝ) ^ (2 : ℕ) * (X n : ℝ) ^ beta ≤
      C * L ^ (4 : ℕ) * Real.exp (L ^ (9 / 8 : ℝ)) := by
    gcongr
  calc
    C * Real.log (X n : ℝ) ^ (2 : ℕ) * (X n : ℝ) ^ beta /
        Real.exp (L ^ (5 / 4 : ℝ)) ≤
      (C * L ^ (4 : ℕ) * Real.exp (L ^ (9 / 8 : ℝ))) /
        Real.exp (L ^ (5 / 4 : ℝ)) :=
      div_le_div_of_nonneg_right hnumer (Real.exp_pos _).le
    _ ≤ 1 / L := by
      apply (le_div_iff₀ hL).2
      rw [show (C * L ^ (4 : ℕ) * Real.exp (L ^ (9 / 8 : ℝ)) /
          Real.exp (L ^ (5 / 4 : ℝ))) * L =
        (C * L ^ (5 : ℕ) * Real.exp (L ^ (9 / 8 : ℝ))) /
          Real.exp (L ^ (5 / 4 : ℝ)) by ring]
      exact (div_le_one (Real.exp_pos _)).2 habsorb'

/-- The harmonic near-diagonal part of finite-height Perron vanishes after
normalization by the saddle main term. -/
theorem IsTaoCriticalSmoothRegime.tendsto_finiteHeightPerronNearQuarter_div_mainTerm_zero
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun n =>
      ((4 * (X n : ℝ) /
          (Real.pi * smoothSaddleHTFrequencyCeiling (y n) (1 / 4))) *
        (8 * (harmonic (X n + 1) : ℝ))) /
          smoothSaddleMainTerm (X n) (y n)) atTop (𝓝 0) := by
  have hrecip : Tendsto (fun n => 1 / Real.log (y n : ℝ))
      atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (hregime.tendsto_log_y_atTop hα)
  have hyX : ∀ᶠ n in atTop, y n ≤ X n := by
    have hratio := (hregime.tendsto_log_y_div_log_X_zero hα).eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [hratio, hregime.eventually_two_le_X,
      hregime.eventually_two_le_y hα] with n hratio hX hy
    have hlogX : 0 < Real.log (X n : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < X n by omega))
    have hlogyX : Real.log (y n : ℝ) < Real.log (X n : ℝ) := by
      rw [div_lt_one hlogX] at hratio
      exact hratio
    have hypos : (0 : ℝ) < y n := by positivity
    have hXpos : (0 : ℝ) < X n := by positivity
    have hreal : (y n : ℝ) ≤ X n :=
      (Real.strictMonoOn_log.le_iff_le
        (show (y n : ℝ) ∈ Set.Ioi 0 from hypos)
        (show (X n : ℝ) ∈ Set.Ioi 0 from hXpos)).mp hlogyX.le
    exact_mod_cast hreal
  refine squeeze_zero' ?_ ?_ hrecip
  · filter_upwards [hregime.eventually_two_le_X,
      hregime.eventually_two_le_y hα] with n hX hy
    have hharm : 0 ≤ (harmonic (X n + 1) : ℝ) := by
      exact_mod_cast (show (0 : ℚ) ≤ harmonic (X n + 1) by
        unfold harmonic
        positivity)
    have hT : 0 < smoothSaddleHTFrequencyCeiling (y n) (1 / 4) :=
      smoothSaddleHTFrequencyCeiling_pos _ _
    have hmain : 0 < smoothSaddleMainTerm (X n) (y n) :=
      smoothSaddleMainTerm_pos hX hy
    positivity
  · filter_upwards [hregime.eventually_two_le_X,
      hregime.eventually_two_le_y hα,
      (hregime.tendsto_log_X_atTop).eventually
        (eventually_ge_atTop (1 : ℝ)),
      (hregime.tendsto_smoothSaddlePoint_one hα).eventually
        (Ici_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)),
      hregime.eventually_smoothSaddlePoint_lt_one hα,
      hyX,
      hregime.eventually_finiteHeightPerronNearScaleQuarter_le hα] with
      n hX hy hlogXone hsigmaHalf hsigmaOne hyX hscale
    let sigma := smoothSaddlePoint (X n) (y n)
    let beta := 1 - sigma
    let T := smoothSaddleHTFrequencyCeiling (y n) (1 / 4)
    let K := Real.sqrt (14 * Real.pi)
    let C := smoothSaddleFiniteHeightNearConstant
    have hXreal : 0 < (X n : ℝ) := by positivity
    have hlogX : 0 < Real.log (X n : ℝ) := by linarith
    have hT : 0 < T := by
      dsimp [T]
      exact smoothSaddleHTFrequencyCeiling_pos _ _
    have hK : 0 < K := by dsimp [K]; positivity
    have hmainPos : 0 < smoothSaddleMainTerm (X n) (y n) :=
      smoothSaddleMainTerm_pos hX hy
    have hlowerPos : 0 < (X n : ℝ) ^ sigma /
        (K * Real.log (X n : ℝ)) := by positivity
    have hmainLower := smoothSaddleMainTerm_lower_bound_at_saddleExponent
      hX hy hyX hsigmaHalf hsigmaOne.le
    have hharm : (harmonic (X n + 1) : ℝ) ≤
        3 * Real.log (X n : ℝ) := by
      calc
        (harmonic (X n + 1) : ℝ) ≤
            1 + Real.log (X n + 1 : ℝ) := by
          simpa [Nat.cast_add] using (harmonic_le_one_add_log (X n + 1))
        _ ≤ 1 + 2 * Real.log (X n : ℝ) := by
          gcongr
          exact log_natCast_add_one_le_two_log hX
        _ ≤ 3 * Real.log (X n : ℝ) := by linarith
    have hA : 0 ≤ (4 * (X n : ℝ) / (Real.pi * T)) *
        (8 * (harmonic (X n + 1) : ℝ)) := by
      have hharm0 : 0 ≤ (harmonic (X n + 1) : ℝ) := by
        exact_mod_cast (show (0 : ℚ) ≤ harmonic (X n + 1) by
          unfold harmonic
          positivity)
      positivity
    have hdivide :
        ((4 * (X n : ℝ) / (Real.pi * T)) *
            (8 * (harmonic (X n + 1) : ℝ))) /
              smoothSaddleMainTerm (X n) (y n) ≤
          ((4 * (X n : ℝ) / (Real.pi * T)) *
            (8 * (harmonic (X n + 1) : ℝ))) /
              ((X n : ℝ) ^ sigma / (K * Real.log (X n : ℝ))) :=
      div_le_div_of_nonneg_left hA hlowerPos hmainLower
    have hrpow : (X n : ℝ) / (X n : ℝ) ^ sigma =
        (X n : ℝ) ^ beta := by
      dsimp [beta]
      rw [Real.rpow_sub hXreal, Real.rpow_one]
    calc
      ((4 * (X n : ℝ) / (Real.pi * T)) *
          (8 * (harmonic (X n + 1) : ℝ))) /
            smoothSaddleMainTerm (X n) (y n) ≤
        ((4 * (X n : ℝ) / (Real.pi * T)) *
          (8 * (harmonic (X n + 1) : ℝ))) /
            ((X n : ℝ) ^ sigma / (K * Real.log (X n : ℝ))) := hdivide
      _ ≤ C * Real.log (X n : ℝ) ^ (2 : ℕ) *
          (X n : ℝ) ^ beta / T := by
        rw [show
          ((4 * (X n : ℝ) / (Real.pi * T)) *
            (8 * (harmonic (X n + 1) : ℝ))) /
              ((X n : ℝ) ^ sigma / (K * Real.log (X n : ℝ))) =
            (32 * K / Real.pi) *
              (harmonic (X n + 1) : ℝ) * Real.log (X n : ℝ) *
                ((X n : ℝ) / (X n : ℝ) ^ sigma) / T by
                  field_simp [hK.ne', hlogX.ne', hT.ne', Real.pi_ne_zero,
                    (Real.rpow_pos_of_pos hXreal sigma).ne']
                  ring,
          hrpow]
        unfold C smoothSaddleFiniteHeightNearConstant
        have hfactor : 0 ≤ (32 * K / Real.pi) * Real.log (X n : ℝ) *
            (X n : ℝ) ^ beta / T := by positivity
        calc
          (32 * K / Real.pi) * (harmonic (X n + 1) : ℝ) *
              Real.log (X n : ℝ) * (X n : ℝ) ^ beta / T =
            (harmonic (X n + 1) : ℝ) *
              ((32 * K / Real.pi) * Real.log (X n : ℝ) *
                (X n : ℝ) ^ beta / T) := by ring
          _ ≤ (3 * Real.log (X n : ℝ)) *
              ((32 * K / Real.pi) * Real.log (X n : ℝ) *
                (X n : ℝ) ^ beta / T) :=
            mul_le_mul_of_nonneg_right hharm hfactor
          _ = (96 * Real.sqrt (14 * Real.pi) / Real.pi) *
              Real.log (X n : ℝ) ^ (2 : ℕ) *
                (X n : ℝ) ^ beta / T := by
            dsimp [K]
            ring
      _ ≤ 1 / Real.log (y n : ℝ) := by
        simpa only [C, beta, T] using hscale

/-- At the quarter-epsilon HT height, the literal coefficient-free sharp
Perron sum converges to the inclusive smooth-number cutoff on the saddle
main-term scale. -/
theorem IsTaoCriticalSmoothRegime.tendsto_smoothSharpPerronQuarter_sub_psiNat_div_mainTerm_zero
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun n =>
      ((∑' m : Nat.smoothNumbers (y n + 1),
          GafniTao.sharpPerronKernel
            (smoothSaddlePoint (X n) (y n))
            (smoothSaddleHTFrequencyCeiling (y n) (1 / 4))
            (X n) m.1) - (psiNat (X n) (y n) : ℂ)) /
        (smoothSaddleMainTerm (X n) (y n) : ℂ)) atTop (𝓝 0) := by
  have hendpoint :=
    hregime.tendsto_finiteHeightPerronEndpoint_div_mainTerm_zero hα
  have hnear :=
    hregime.tendsto_finiteHeightPerronNearQuarter_div_mainTerm_zero hα
  have hfar :=
    hregime.tendsto_finiteHeightPerronFarQuarter_div_mainTerm_zero hα
  have hupper : Tendsto (fun n =>
      (3 / 2 +
        (4 * (X n : ℝ) /
            (Real.pi * smoothSaddleHTFrequencyCeiling (y n) (1 / 4))) *
          (8 * (harmonic (X n + 1) : ℝ)) +
        (2 * (X n : ℝ) ^ smoothSaddlePoint (X n) (y n) /
            (Real.pi * smoothSaddleHTFrequencyCeiling (y n) (1 / 4))) *
          smoothDirichletSeries (y n + 1)
            (smoothSaddlePoint (X n) (y n))) /
        smoothSaddleMainTerm (X n) (y n)) atTop (𝓝 0) := by
    have hsum := hendpoint.add hnear |>.add hfar
    have hsum' : Tendsto (fun n =>
        (3 / 2 : ℝ) / smoothSaddleMainTerm (X n) (y n) +
          ((4 * (X n : ℝ) /
              (Real.pi * smoothSaddleHTFrequencyCeiling (y n) (1 / 4))) *
            (8 * (harmonic (X n + 1) : ℝ))) /
              smoothSaddleMainTerm (X n) (y n) +
          ((2 * (X n : ℝ) ^ smoothSaddlePoint (X n) (y n) /
              (Real.pi * smoothSaddleHTFrequencyCeiling (y n) (1 / 4))) *
            smoothDirichletSeries (y n + 1)
              (smoothSaddlePoint (X n) (y n))) /
              smoothSaddleMainTerm (X n) (y n)) atTop (𝓝 0) := by
      simpa using hsum
    apply hsum'.congr'
    filter_upwards with n
    ring
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hupper
  filter_upwards [hregime.eventually_two_le_X,
    hregime.eventually_two_le_y hα,
    hregime.eventually_smoothSaddlePoint_lt_one hα] with
      n hX hy hsigmaOne
  let T := smoothSaddleHTFrequencyCeiling (y n) (1 / 4)
  have hT : 0 < T := by
    dsimp [T]
    exact smoothSaddleHTFrequencyCeiling_pos _ _
  have hmain : 0 < smoothSaddleMainTerm (X n) (y n) :=
    smoothSaddleMainTerm_pos hX hy
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hmain.le]
  apply div_le_div_of_nonneg_right _ hmain.le
  simpa only [T] using norm_smoothSharpPerron_tsum_sub_psiNat_le
    hX hy hT hsigmaOne.le

end

end Tao2026

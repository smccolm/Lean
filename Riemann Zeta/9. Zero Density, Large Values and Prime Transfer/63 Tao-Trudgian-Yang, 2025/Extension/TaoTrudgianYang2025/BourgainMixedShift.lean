import TaoTrudgianYang2025.BourgainSeparatedSelf
import TaoTrudgianYang2025.BourgainLocalMean
import TaoTrudgianYang2025.BourgainSliceGeometry

/-!
# The actual shifted polynomial and full slice enter mixed Cauchy--Schwarz

A unit-norm twist absorbs the integration variable without changing support
or coefficients' bounds. The integer-to-real bridge preserves every summand.
-/

open Complex Finset MeasureTheory RiemannZeta.GuthMaynard
open scoped Interval Classical

noncomputable section

namespace TaoTrudgianYang2025

theorem LargeValuePattern.dirichletPhase_add (P : LargeValuePattern)
    {n : ℕ} (hn : n ∈ P.indices) (t v : ℝ) :
    dirichletPhase n (t+v) = dirichletPhase n t*dirichletPhase n v := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (P.index_pos hn).ne'
  change (n : ℂ)^(-(Complex.I*((t+v : ℝ) : ℂ))) =
    (n : ℂ)^(-(Complex.I*(t : ℂ)))*(n : ℂ)^(-(Complex.I*(v : ℂ)))
  rw [← Complex.cpow_add _ _ hn0]
  congr 1
  push_cast
  ring

theorem bourgain_shifted_polynomial (P : LargeValuePattern) (t u v : ℝ) :
    (∑ n ∈ P.indices, P.coeff n*dirichletPhase n (t-u+v)) =
      ∑ n ∈ P.indices, (P.coeff n*dirichletPhase n v)*dirichletPhase n (t-u) := by
  apply Finset.sum_congr rfl
  intro n hn
  rw [P.dirichletPhase_add hn]
  ring

theorem bourgain_shifted_mixed_cauchySchwarz (P : LargeValuePattern)
    (W U : Finset ℝ) (v : ℝ) :
    (∑ t ∈ W, ∑ u ∈ U,
      ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n (t-u+v)‖^2) ≤
      Real.sqrt (bourgainSelfMoment P W)*Real.sqrt (bourgainSelfMoment P U) := by
  simp_rw [bourgain_shifted_polynomial]
  apply mixed_doubleZeta_cauchySchwarz P.indices W U
    (fun n => P.coeff n*dirichletPhase n v) (fun _ hn => P.index_pos hn)
  intro n hn
  rw [norm_mul, P.norm_dirichletPhase hn, mul_one]
  exact P.coeff_one_bounded n hn

/-- No multiplicity is lost in replacing integer ordinates by their real image. -/
theorem bourgain_integerSlice_sum {H T V u : ℝ} (f : ℝ → ℝ) :
    (∑ ℓ ∈ bourgainIntegerSlice H T V u, f (ℓ : ℝ)) =
      ∑ x ∈ bourgainRealSlice H T V u, f x := by
  unfold bourgainRealSlice
  rw [Finset.sum_image (fun x _ y _ h => Int.cast_injective h)]

theorem bourgain_slice_mixed_cauchySchwarz (P : LargeValuePattern)
    (W : Finset ℝ) (H T V u v : ℝ) :
    (∑ t ∈ W, ∑ ℓ ∈ bourgainIntegerSlice H T V u,
      ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n (t-(ℓ : ℝ)+v)‖^2) ≤
      Real.sqrt (bourgainSelfMoment P W)*
        Real.sqrt (bourgainSelfMoment P (bourgainRealSlice H T V u)) := by
  calc
    _ = ∑ t ∈ W, ∑ x ∈ bourgainRealSlice H T V u,
        ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n (t-x+v)‖^2 :=
      Finset.sum_congr rfl (fun t _ => bourgain_integerSlice_sum
        (fun x => ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n (t-x+v)‖^2))
    _ ≤ _ := bourgain_shifted_mixed_cauchySchwarz P W _ v

theorem bourgain_mixed_slice_continuous (P : LargeValuePattern)
    (W : Finset ℝ) (H T V u : ℝ) :
    Continuous (fun v : ℝ => ∑ t ∈ W, ∑ ℓ ∈ bourgainIntegerSlice H T V u,
      ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n (t-(ℓ : ℝ)+v)‖^2) := by
  apply continuous_finsetSum
  intro t ht
  apply continuous_finsetSum
  intro ℓ hℓ
  exact (P.polynomial_norm_continuous.comp (continuous_const.add continuous_id)).pow 2

/-- The original mixed local moment is bounded by the two actual self moments.
The only integration loss is the literal window length. -/
theorem bourgain_slice_mixed_integral_cauchySchwarz (P : LargeValuePattern)
    (W : Finset ℝ) (H T V u r : ℝ) (hr : 0 ≤ r) :
    (∫ v in -r..r, ∑ t ∈ W, ∑ ℓ ∈ bourgainIntegerSlice H T V u,
      ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n (t-(ℓ : ℝ)+v)‖^2) ≤
      2*r*(Real.sqrt (bourgainSelfMoment P W)*
        Real.sqrt (bourgainSelfMoment P (bourgainRealSlice H T V u))) := by
  have h := intervalIntegral.integral_mono_on (μ := volume) (by linarith : -r ≤ r)
    ((bourgain_mixed_slice_continuous P W H T V u).intervalIntegrable (-r) r)
    intervalIntegrable_const
    (fun v _ => bourgain_slice_mixed_cauchySchwarz P W H T V u v)
  simpa only [intervalIntegral.integral_const, sub_neg_eq_add, smul_eq_mul,
    show r+r = 2*r by ring] using h

end TaoTrudgianYang2025

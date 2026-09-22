import TaoTrudgianYang2025.ZetaFourthMoment
import TaoTrudgianYang2025.BourgainZetaDifferenceMoments

/-!
# The global fourth moment and Bourgain's weighted-moment bound

The dyadic fourth-moment theorem is extended to a symmetric interval by
a proved dyadic induction, the compact initial interval, and zeta
conjugation. The resulting bound consumes the actual difference moment.
-/

open MeasureTheory
open scoped Interval
open RiemannZeta.GuthMaynard

noncomputable section

namespace TaoTrudgianYang2025

/-- A nonnegative continuous function with a dyadic power bound has the
corresponding bound from zero. The compact initial interval is retained. -/
theorem integral_zero_le_of_dyadic (f : ℝ → ℝ) (hf : Continuous f)
    (hf0 : ∀ t, 0 ≤ f t) {p B C : ℝ} (hp : 1 ≤ p) (hB : 1 ≤ B) (hC : 0 ≤ C)
    (hdyad : ∀ H : ℝ, B ≤ H → (∫ t in H..2*H, f t) ≤ C*H^p) :
    ∃ K : ℝ, 0 < K ∧ ∀ H : ℝ, B ≤ H →
      (∫ t in 0..H, f t) ≤ K*H^p := by
  let A : ℝ := |∫ t in 0..B, f t| + C + 1
  have hA : 0 < A := by dsimp [A]; positivity
  have hCA : C ≤ A := by dsimp [A]; linarith [abs_nonneg (∫ t in 0..B, f t)]
  have hBp : 0 < B := by linarith
  have htwo : (2 : ℝ) ≤ (2 : ℝ)^p := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hp
  have hstep : ∀ m : ℕ, (∫ t in 0..(2 : ℝ)^m*B, f t) ≤ A*((2 : ℝ)^m*B)^p := by
    intro m
    induction m with
    | zero =>
      simp only [pow_zero, one_mul]
      have hbpower := Real.one_le_rpow hB (by linarith : 0 ≤ p)
      calc
        _ ≤ |∫ t in 0..B, f t| := le_abs_self _
        _ ≤ A := by dsimp [A]; linarith
        _ ≤ A*B^p := by nlinarith
    | succ m ih =>
      have hm : B ≤ (2 : ℝ)^m*B := by
        have hpow : 1 ≤ (2 : ℝ)^m := one_le_pow₀ (by norm_num)
        nlinarith
      have hX : 0 ≤ (2 : ℝ)^m*B := by positivity
      have heq : (2 : ℝ)^(m+1)*B = 2*((2 : ℝ)^m*B) := by rw [pow_succ']; ring
      rw [heq, ← intervalIntegral.integral_add_adjacent_intervals
        (hf.intervalIntegrable 0 ((2 : ℝ)^m*B))
        (hf.intervalIntegrable ((2 : ℝ)^m*B) (2*((2 : ℝ)^m*B)))]
      calc
        _ ≤ A*((2 : ℝ)^m*B)^p + C*((2 : ℝ)^m*B)^p :=
          add_le_add ih (hdyad _ hm)
        _ ≤ A*((2 : ℝ)^m*B)^p + A*((2 : ℝ)^m*B)^p :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_right hCA (Real.rpow_nonneg hX _))
        _ = A*2*((2 : ℝ)^m*B)^p := by ring
        _ ≤ A*(2 : ℝ)^p*((2 : ℝ)^m*B)^p :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htwo hA.le)
            (Real.rpow_nonneg hX _)
        _ = _ := by rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hX]; ring
  refine ⟨A*(2 : ℝ)^p, by positivity, ?_⟩
  intro H hH
  have hHp : 0 < H := hBp.trans_le hH
  obtain ⟨m, hlo, hhi⟩ := exists_dyadic_cutoff
    ((le_div_iff₀ hBp).mpr (by simpa using hH))
  have hlo' : H ≤ (2 : ℝ)^m*B := (div_le_iff₀ hBp).mp hlo
  have hhi' : (2 : ℝ)^m*B ≤ 2*H := by
    have := (mul_le_mul_iff_left₀ hBp).mpr hhi
    field_simp at this
    nlinarith
  calc
    _ ≤ ∫ t in 0..(2 : ℝ)^m*B, f t := by
      apply intervalIntegral.integral_mono_interval le_rfl hHp.le hlo'
      · exact Filter.Eventually.of_forall hf0
      · exact hf.intervalIntegrable _ _
    _ ≤ A*((2 : ℝ)^m*B)^p := hstep m
    _ ≤ A*(2*H)^p :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hhi' (by linarith)) hA.le
    _ = _ := by rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hHp.le]; ring

/-- The actual critical-line zeta norm is even, by conjugation. -/
theorem zetaMomentCriticalNorm_neg (t : ℝ) :
    zetaMomentCriticalNorm (-t) = zetaMomentCriticalNorm t := by
  have h := congrArg norm (riemannZeta_afeCriticalPoint_neg_eq_star t)
  simpa only [zetaMomentCriticalNorm, afeCriticalPoint, norm_star,
    Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using h

/-- The genuine unweighted fourth moment on a full symmetric height interval. -/
theorem zeta_fourth_symmetric {η : ℝ} (hη : 0 < η) :
    ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧
      ∀ T : ℝ, T₀ ≤ T →
        (∫ t in -T..T, zetaMomentCriticalNorm t^4) ≤ C*T^(1+η) := by
  obtain ⟨D, H₀, hD, hd⟩ := zeta_fourth_dyadic η hη
  let B : ℝ := max H₀ 1
  have hB : 1 ≤ B := le_max_right _ _
  obtain ⟨K, hK, hglobal⟩ := integral_zero_le_of_dyadic
    (fun t => zetaMomentCriticalNorm t^4) (continuous_zetaMomentCriticalNorm.pow 4)
    (fun _ => by positivity) (by linarith : 1 ≤ 1+η) hB hD
    (fun H hH => hd H ((le_max_left _ _).trans hH) (by linarith))
  refine ⟨2*K, B, by positivity, hB, ?_⟩
  intro T hT
  have hi (a b : ℝ) : IntervalIntegrable (fun t => zetaMomentCriticalNorm t^4) volume a b :=
    (continuous_zetaMomentCriticalNorm.pow 4).intervalIntegrable a b
  have heven : (∫ t in -T..0, zetaMomentCriticalNorm t^4) =
      ∫ t in 0..T, zetaMomentCriticalNorm t^4 := by
    have hs := intervalIntegral.integral_comp_neg (fun t => zetaMomentCriticalNorm t^4)
      (a := (0 : ℝ)) (b := T)
    simpa only [zetaMomentCriticalNorm_neg, neg_zero] using hs.symm
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi (-T) 0) (hi 0 T), heven]
  have h := hglobal T hT
  nlinarith

/-- Bourgain's actual weighted local zeta-square moment is now bounded
using the proved fourth moment. The constant is uniform in the set and
both physical height parameters; the window loss is fully explicit. -/
theorem bourgainZetaDifferenceMoment_fourth_bound {η : ℝ} (hη : 0 < η) :
    ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧
      ∀ (W : Finset ℝ) (T H : ℝ), T₀ ≤ T → 0 ≤ H →
        IsSeparated 2 W → InBaseInterval T W →
        bourgainZetaDifferenceMoment W H ^ 2 ≤
          C * H * (2 * Nat.ceil H + 1 : ℕ) * (W.card : ℝ)^3 *
            (T+H+1)^(1+η) := by
  obtain ⟨D, T₀, hD, hT₀, hmoment⟩ := zeta_fourth_symmetric hη
  refine ⟨4*D, T₀, by positivity, hT₀, ?_⟩
  intro W T H hT hH hsep hbase
  have hb := bourgainZetaDifferenceMoment_sq_le hsep hbase (by linarith) hH
  have hm := hmoment (T+H+1) (by linarith)
  have h := hb.trans (mul_le_mul_of_nonneg_left hm
    (by positivity : 0 ≤ 4*H*(2*Nat.ceil H+1 : ℕ)*(W.card : ℝ)^3))
  convert h using 1
  ring

end TaoTrudgianYang2025

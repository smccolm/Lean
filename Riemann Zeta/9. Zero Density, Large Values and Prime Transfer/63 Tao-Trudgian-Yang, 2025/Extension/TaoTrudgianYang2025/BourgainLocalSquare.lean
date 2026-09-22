import TaoTrudgianYang2025.BourgainPowerMean

/-!
# Squared local means and the strict difference-bin displacement

The local L1 theorem yields a genuine local second-moment lower bound.
Moving the centre by at most one enlarges the window by exactly one;
this is the displacement required by the strict integer difference counts.
-/

open MeasureTheory RiemannZeta.GuthMaynard Set
open scoped Interval Classical

noncomputable section

namespace TaoTrudgianYang2025

/-- Finite-interval Cauchy--Schwarz, with explicit integrability rather than
a continuity assumption or an unproved local mean. -/
theorem bourgain_interval_integral_sq_le {f : ℝ → ℝ} {H : ℝ}
    (hH : 0 < H) (hf : IntervalIntegrable f volume (-H) H)
    (hf₂ : IntervalIntegrable (fun u => (f u)^2) volume (-H) H) :
    (∫ u in -H..H, f u)^2 ≤ 2*H*(∫ u in -H..H, (f u)^2) := by
  let M := ∫ u in -H..H, f u
  let Q := ∫ u in -H..H, (f u)^2
  let c := M/(2*H)
  have hc : 2*H*c = M := by
    dsimp only [c]
    exact mul_div_cancel₀ M (by positivity : (2*H : ℝ) ≠ 0)
  have hn : 0 ≤ ∫ u in -H..H, (f u)^2-2*c*f u+c^2 := by
    apply intervalIntegral.integral_nonneg (by linarith)
    intro u hu
    nlinarith [sq_nonneg (f u-c)]
  rw [intervalIntegral.integral_add (hf₂.sub (hf.const_mul (2*c))) intervalIntegrable_const,
    intervalIntegral.integral_sub hf₂ (hf.const_mul (2*c)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul] at hn
  change 0 ≤ Q-2*c*M+(H- -H)*c^2 at hn
  have hp := mul_nonneg (show 0 ≤ 2*H by positivity) hn
  change M^2 ≤ 2*H*Q
  nlinarith [sq_nonneg (2*H*c-M)]

/-- A source-linked local second moment on an arbitrarily small positive
power window, using the unchanged coefficient polynomial. -/
theorem bourgain_power_window_local_square {η : ℝ} (hη : 0 < η) :
    ∃ C N₀ : ℝ, 0 < C ∧ 2 ≤ N₀ ∧ ∀ P : LargeValuePattern,
      N₀ ≤ P.N → ∀ σ δ : ℝ, 0 ≤ σ → δ ≤ 1 → P.N^(σ-δ) ≤ P.V →
      ∀ t ∈ P.ordinates,
        P.V^2 ≤ C*P.N^η*
          (∫ u in -(2*Real.pi*P.N^η)..(2*Real.pi*P.N^η),
            ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n (t+u)‖^2) := by
  obtain ⟨D, N₀, hD, hN₀, hm⟩ := bourgain_power_window_local_mean_in_source_range hη
  refine ⟨4*Real.pi*D^2, N₀, by positivity, hN₀, ?_⟩
  intro P hN σ δ hσ hδ hV t ht
  let R := 2*Real.pi*P.N^η
  let f := fun u => ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n (t+u)‖
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hR : 0 < R := by dsimp only [R]; positivity
  have hfc : Continuous f := P.polynomial_norm_continuous.comp (by fun_prop)
  have hCS := bourgain_interval_integral_sq_le hR
    (hfc.intervalIntegrable _ _) ((hfc.pow 2).intervalIntegrable _ _)
  have hpoint : P.V ≤ D*(∫ u in -R..R, f u) := hm P hN σ δ hσ hδ hV t ht
  have hsq : P.V^2 ≤ (D*(∫ u in -R..R, f u))^2 :=
    pow_le_pow_left₀ P.V_pos.le hpoint 2
  have hprod := mul_le_mul_of_nonneg_left hCS (sq_nonneg D)
  calc
    _ ≤ D^2*(∫ u in -R..R, f u)^2 := by simpa only [mul_pow] using hsq
    _ ≤ D^2*(2*R*(∫ u in -R..R, (f u)^2)) := hprod
    _ = _ := by dsimp only [R, f]; ring

/-- Translate the actual local second moment to any centre within one
unit, exactly matching the displacement in the strict integer bins. -/
theorem bourgain_power_window_displaced_square {η : ℝ} (hη : 0 < η) :
    ∃ C N₀ : ℝ, 0 < C ∧ 2 ≤ N₀ ∧ ∀ P : LargeValuePattern,
      N₀ ≤ P.N → ∀ σ δ : ℝ, 0 ≤ σ → δ ≤ 1 → P.N^(σ-δ) ≤ P.V →
      ∀ t ∈ P.ordinates, ∀ x : ℝ, |x-t| ≤ 1 →
        P.V^2 ≤ C*P.N^η*
          (∫ u in -(1+2*Real.pi*P.N^η)..(1+2*Real.pi*P.N^η),
            ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n (x+u)‖^2) := by
  obtain ⟨C, N₀, hC, hN₀, hm⟩ := bourgain_power_window_local_square hη
  refine ⟨C, N₀, hC, hN₀, ?_⟩
  intro P hN σ δ hσ hδ hV t ht x hx
  let R := 2*Real.pi*P.N^η
  let f := fun y => ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n y‖^2
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hR : 0 < R := by dsimp only [R]; positivity
  have hfc : Continuous f := P.polynomial_norm_continuous.pow 2
  have hpoint := hm P hN σ δ hσ hδ hV t ht
  have hmono : (∫ u in -R..R, f (t+u)) ≤
      ∫ u in -(1+R)..(1+R), f (x+u) := by
    rw [intervalIntegral.integral_comp_add_left (f := f) t,
      intervalIntegral.integral_comp_add_left (f := f) x]
    apply intervalIntegral.integral_mono_interval
    · linarith [(abs_le.mp hx).2]
    · linarith
    · linarith [(abs_le.mp hx).1]
    · exact Filter.Eventually.of_forall (fun _ => sq_nonneg _)
    · exact hfc.intervalIntegrable _ _
  exact hpoint.trans (mul_le_mul_of_nonneg_left hmono (by positivity))

end TaoTrudgianYang2025


import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Asymptotics Filter Topology

namespace RiemannZeta.GuthMaynard

/--
`EpsilonPowerBound f g` represents the Guth-Maynard asymptotic convention $f(T) \lessapprox g(T)$.
It means that for any $\varepsilon > 0$, we have $|f(T)| \ll_{\varepsilon} T^{\varepsilon} |g(T)|$ as $T \to \infty$.
The implicit constant may depend on $\varepsilon$.
-/
def EpsilonPowerBound (f g : ℝ → ℝ) : Prop :=
  ∀ (ε : ℝ), ε > 0 → (fun T => |f T|) =O[atTop] (fun T => T ^ ε * |g T|)

theorem EpsilonPowerBound.refl (f : ℝ → ℝ) : EpsilonPowerBound f f := by
  intro ε hε
  apply IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop 1] with T hT
  have hT_pos : 0 < T := by linarith
  have hε_nonneg : 0 ≤ ε := by linarith
  have h_pow : 1 ≤ T ^ ε := Real.one_le_rpow (by linarith) hε_nonneg
  rw [Real.norm_eq_abs (|f T|), abs_abs]
  have H2 : ‖T ^ ε * |f T|‖ = T ^ ε * |f T| := by
    rw [Real.norm_eq_abs]
    exact abs_of_nonneg (by positivity)
  rw [H2]
  calc |f T| = 1 * |f T| := by ring
    _ ≤ T ^ ε * |f T| := mul_le_mul_of_nonneg_right h_pow (abs_nonneg (f T))
    _ = 1 * (T ^ ε * |f T|) := by ring

theorem EpsilonPowerBound.trans {f g h : ℝ → ℝ}
    (h1 : EpsilonPowerBound f g) (h2 : EpsilonPowerBound g h) :
    EpsilonPowerBound f h := by
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  have H1 : (fun T => |f T|) =O[atTop] (fun T => T ^ (ε / 2) * |g T|) := h1 (ε / 2) hε2
  have H2 : (fun T => |g T|) =O[atTop] (fun T => T ^ (ε / 2) * |h T|) := h2 (ε / 2) hε2
  have H3 : (fun T => T ^ (ε / 2) * |g T|) =O[atTop] (fun T => T ^ (ε / 2) * (T ^ (ε / 2) * |h T|)) :=
    IsBigO.mul (isBigO_refl (fun T => T ^ (ε / 2)) atTop) H2
  have H4 := H1.trans H3
  have Heq : (fun T => T ^ (ε / 2) * (T ^ (ε / 2) * |h T|)) =ᶠ[atTop] (fun T => T ^ ε * |h T|) := by
    filter_upwards [eventually_ge_atTop 1] with T hT
    have hT_pos : 0 < T := by linarith
    have h_pow_add : T ^ (ε / 2) * T ^ (ε / 2) = T ^ (ε / 2 + ε / 2) := by
      exact (Real.rpow_add hT_pos _ _).symm
    calc T ^ (ε / 2) * (T ^ (ε / 2) * |h T|)
      _ = (T ^ (ε / 2) * T ^ (ε / 2)) * |h T| := mul_assoc .. |>.symm
      _ = T ^ (ε / 2 + ε / 2) * |h T| := by rw [h_pow_add]
      _ = T ^ ε * |h T| := by ring_nf
  exact H4.trans_eventuallyEq Heq

end RiemannZeta.GuthMaynard

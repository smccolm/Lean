import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! # Exact smooth jets under genuine continuous linear maps -/

namespace Dubon2026

noncomputable section
open scoped ContDiff

/-- A genuine continuous real linear map carries an actual curve derivative to the derivative of its image. -/
theorem deriv_continuousLinearMap {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (L : V →L[ℝ] W) (C : ℝ → V) (t : ℝ) (hC : DifferentiableAt ℝ C t) :
    deriv (fun u => L (C u)) t = L (deriv C t) :=
  (L.hasFDerivAt.comp_hasDerivAt t hC.hasDerivAt).deriv

/-- A bounded operator that shifts an actual differentiable orbit carries its initial derivative to the shifted derivative. -/
theorem continuousLinearMap_orbit_deriv {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] (L : V →L[ℝ] V) (C : ℝ → V) (s : ℝ)
    (hshift : ∀ t, L (C t) = C (s + t)) (hd : DifferentiableAt ℝ C 0) :
    L (deriv C 0) = deriv C s := by
  have he := deriv_continuousLinearMap L C 0 hd
  rw [funext hshift, deriv_comp_const_add, add_zero] at he
  exact he.symm

/-- A genuine continuous real linear map commutes with every derivative of an actual smooth vector curve. -/
theorem iteratedDeriv_continuousLinearMap {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (L : V →L[ℝ] W) (C : ℝ → V) (hC : ContDiff ℝ ∞ C) (n : ℕ) :
    iteratedDeriv n (fun t => L (C t)) = fun t => L (iteratedDeriv n C t) := by
  induction n with
  | zero => simp only [iteratedDeriv_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]
    funext t
    have hCn : ContDiff ℝ (n + 1) C := by
      simpa only [Nat.cast_add, Nat.cast_one] using contDiff_infty.mp hC (n + 1)
    have hd := (hCn.differentiable_iteratedDeriv' n t).hasDerivAt
    exact (L.hasFDerivAt.comp_hasDerivAt t hd).deriv

end
end Dubon2026

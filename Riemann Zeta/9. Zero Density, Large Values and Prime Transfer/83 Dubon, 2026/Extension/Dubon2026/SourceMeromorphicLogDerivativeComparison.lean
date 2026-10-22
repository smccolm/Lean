import Dubon2026.SourceComplexPuncturedBallPaths
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Meromorphic.Order

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi converse ->
meromorphic gluing. Native equality of logarithmic derivatives makes the
global exponential a nonzero scalar multiple of its local model on the
punctured disk. Meromorphicity and the exact order therefore transfer.
-/
namespace Dubon2026.SourceFunctionField.OriginalExpTopology
noncomputable section
open Filter Set Metric
open scoped Topology

theorem meromorphicAt_of_same_logarithmic_derivative {r : ℝ} (hr : 0 < r)
    (f M R : ℂ → ℂ) (hM0 : MeromorphicAt M 0)
    (hf : ∀ z ∈ ball (0 : ℂ) r, z ≠ 0 → f z ≠ 0 ∧ HasDerivAt f (R z * f z) z)
    (hM : ∀ z ∈ ball (0 : ℂ) r, z ≠ 0 → M z ≠ 0 ∧ HasDerivAt M (R z * M z) z) :
    MeromorphicAt f 0 ∧ meromorphicOrderAt f 0 = meromorphicOrderAt M 0 := by
  let U : Set ℂ := ball 0 r \ {0}
  have hU : IsOpen U := isOpen_ball.sdiff isClosed_singleton
  have hconn : IsPreconnected U :=
    (isPathConnected_ball_diff_singleton 0 hr).isConnected.isPreconnected
  have hfd : DifferentiableOn ℂ f U := fun z hz => (hf z hz.1 hz.2).2.differentiableAt.differentiableWithinAt
  have hMd : DifferentiableOn ℂ M U := fun z hz => (hM z hz.1 hz.2).2.differentiableAt.differentiableWithinAt
  obtain ⟨C, hC, he⟩ := (logDeriv_eqOn_iff hfd hMd hU hconn
    (fun z hz => (hM z hz.1 hz.2).1) (fun z hz => (hf z hz.1 hz.2).1)).mp (by
      intro z hz
      rw [logDeriv_apply, logDeriv_apply, (hf z hz.1 hz.2).2.deriv, (hM z hz.1 hz.2).2.deriv]
      rw [mul_div_cancel_right₀ _ (hf z hz.1 hz.2).1, mul_div_cancel_right₀ _ (hM z hz.1 hz.2).1])
  have heq : f =ᶠ[𝓝[≠] (0 : ℂ)] fun z => C * M z := by
    rw [Filter.EventuallyEq, eventually_nhdsWithin_iff]
    filter_upwards [ball_mem_nhds (0 : ℂ) hr] with z hz hn
    exact he ⟨hz, hn⟩
  refine ⟨((MeromorphicAt.const C 0).mul hM0).congr heq.symm, ?_⟩
  rw [meromorphicOrderAt_congr heq]
  change meromorphicOrderAt ((fun _ => C) * M) 0 = meromorphicOrderAt M 0
  rw [meromorphicOrderAt_mul (MeromorphicAt.const C 0) hM0, meromorphicOrderAt_const]
  simp only [if_neg hC, zero_add]

end
end Dubon2026.SourceFunctionField.OriginalExpTopology

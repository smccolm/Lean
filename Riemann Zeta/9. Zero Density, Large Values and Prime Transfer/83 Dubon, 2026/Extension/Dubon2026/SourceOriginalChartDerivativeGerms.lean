import Dubon2026.SourceOriginalChartGermHom

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi -> differential
coordinate compatibility. Differentiate the proved original chart germ
homomorphism using native punctured-germ derivative congruence and local
meromorphic analyticity. These are the exact additivity, scalar and Leibniz
identities needed to apply the existing Kaehler differential universal map.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Filter Metric
open scoped Topology
variable (N : ℕ) [NeZero N]

theorem eventually_differentiableAt_chartRead (v : Place ℂ (modularFunctionFieldOver N ℂ))
    (f : modularFunctionFieldOver N ℂ) :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ), DifferentiableAt ℂ (chartRead N v f) z :=
  (meromorphicAt_chartRead N v f (mem_ball_self (place_spec N v).1)).eventually_analyticAt.mono
    fun _ h => h.differentiableAt

theorem deriv_chartRead_add (v : Place ℂ (modularFunctionFieldOver N ℂ))
    (f g : modularFunctionFieldOver N ℂ) :
    deriv (chartRead N v (f + g)) =ᶠ[𝓝[≠] (0 : ℂ)]
      deriv (chartRead N v f) + deriv (chartRead N v g) := by
  filter_upwards [(chartRead_add N v f g).nhdsNE_deriv,
    eventually_differentiableAt_chartRead N v f,
    eventually_differentiableAt_chartRead N v g] with z he hf hg
  rw [he, Pi.add_apply]
  exact deriv_add hf hg

theorem deriv_chartRead_mul (v : Place ℂ (modularFunctionFieldOver N ℂ))
    (f g : modularFunctionFieldOver N ℂ) :
    deriv (chartRead N v (f * g)) =ᶠ[𝓝[≠] (0 : ℂ)]
      deriv (chartRead N v f) * chartRead N v g + chartRead N v f * deriv (chartRead N v g) := by
  filter_upwards [(chartRead_mul N v f g).nhdsNE_deriv,
    eventually_differentiableAt_chartRead N v f,
    eventually_differentiableAt_chartRead N v g] with z he hf hg
  rw [he, Pi.add_apply, Pi.mul_apply, Pi.mul_apply]
  exact deriv_mul hf hg

theorem deriv_chartRead_smul (v : Place ℂ (modularFunctionFieldOver N ℂ))
    (c : ℂ) (f : modularFunctionFieldOver N ℂ) :
    deriv (chartRead N v (c • f)) =ᶠ[𝓝[≠] (0 : ℂ)] c • deriv (chartRead N v f) := by
  rw [Algebra.smul_def]
  filter_upwards [deriv_chartRead_mul N v (algebraMap ℂ (modularFunctionFieldOver N ℂ) c) f] with z hz
  rw [hz, chartRead_algebraMap]
  simp

theorem deriv_chartRead_one (v : Place ℂ (modularFunctionFieldOver N ℂ)) :
    deriv (chartRead N v 1) = 0 := by
  rw [chartRead_one]
  funext z
  exact deriv_const z 1

end
end Dubon2026.SourceFunctionField.OriginalChart

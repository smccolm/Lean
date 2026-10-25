import Dubon2026.SourceOriginalWeilCoverChartGermHom

/-! DUB-17/18 -> auxiliary Abel comparison -> actual differential readings.
Adapt the existing original-curve residue-germ derivation argument to the
literal Kummer splitting field and its constructed uniformizer charts.
The local spanning and field-reading inputs are proved for this actual cover.
The original derivation proof was adapted from anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_exists_isPrimitiveAlong_of_mem_regularDifferentials.
-/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Filter Metric
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (r : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C r : Polynomial FF)
variable (A : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hr : r ≠ 0)
variable (hrA : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord r = (n : ℤ) * A v)
include A hr hrA

theorem eventually_differentiableAt_chartRead (v : Place ℂ (EE))
    (f : EE) :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ), DifferentiableAt ℂ (chartRead N n r A hr hrA v f) z :=
  (meromorphicAt_chartRead N n r A hr hrA v f (mem_ball_self (place_spec N n r A hr hrA v).1)).eventually_analyticAt.mono
    fun _ h => h.differentiableAt

theorem deriv_chartRead_add (v : Place ℂ (EE))
    (f g : EE) :
    deriv (chartRead N n r A hr hrA v (f + g)) =ᶠ[𝓝[≠] (0 : ℂ)]
      deriv (chartRead N n r A hr hrA v f) + deriv (chartRead N n r A hr hrA v g) := by
  filter_upwards [(chartRead_add N n r A hr hrA v f g).nhdsNE_deriv,
    eventually_differentiableAt_chartRead N n r A hr hrA v f,
    eventually_differentiableAt_chartRead N n r A hr hrA v g] with z he hf hg
  rw [he, Pi.add_apply]
  exact deriv_add hf hg

theorem deriv_chartRead_mul (v : Place ℂ (EE))
    (f g : EE) :
    deriv (chartRead N n r A hr hrA v (f * g)) =ᶠ[𝓝[≠] (0 : ℂ)]
      deriv (chartRead N n r A hr hrA v f) * chartRead N n r A hr hrA v g + chartRead N n r A hr hrA v f * deriv (chartRead N n r A hr hrA v g) := by
  filter_upwards [(chartRead_mul N n r A hr hrA v f g).nhdsNE_deriv,
    eventually_differentiableAt_chartRead N n r A hr hrA v f,
    eventually_differentiableAt_chartRead N n r A hr hrA v g] with z he hf hg
  rw [he, Pi.add_apply, Pi.mul_apply, Pi.mul_apply]
  exact deriv_mul hf hg

theorem deriv_chartRead_smul (v : Place ℂ (EE))
    (c : ℂ) (f : EE) :
    deriv (chartRead N n r A hr hrA v (c • f)) =ᶠ[𝓝[≠] (0 : ℂ)] c • deriv (chartRead N n r A hr hrA v f) := by
  rw [Algebra.smul_def]
  filter_upwards [deriv_chartRead_mul N n r A hr hrA v (algebraMap ℂ (EE) c) f] with z hz
  rw [hz, chartRead_algebraMap]
  simp

theorem deriv_chartRead_one (v : Place ℂ (EE)) :
    deriv (chartRead N n r A hr hrA v 1) = 0 := by
  rw [chartRead_one]
  funext z
  exact deriv_const z 1

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart

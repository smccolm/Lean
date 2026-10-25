import Dubon2026.SourceCuspDiscGermUniqueness

/-! DUB-17/18 -> auxiliary cover analytic charts -> actual field laws on a disk.
Connected meromorphic uniqueness extends the common Laurent representation
at the center to punctured germs at each disk point. This is the existing
original cusp argument with its field parameter exposed for the torsion cover. -/
namespace Dubon2026.SourceCurve.AnalyticDisc
noncomputable section
open SourceFunctionField.CuspTaylor Filter Metric
open scoped Topology
variable {E : Type*} [Field E] [Algebra ℂ E]
variable (e : E →ₐ[ℂ] realizedField) {R : ℝ} (hR : 0 < R) (G : E → ℂ → ℂ)
variable (hm : ∀ a, MeromorphicOn (G a) (ball 0 R))
variable (hr : ∀ a, Represents (e a).val (G a))

include hR hm hr

theorem realize_const (c : ℂ) {z : ℂ} (hz : z ∈ ball 0 R) :
    G (algebraMap ℂ E c) =ᶠ[𝓝[≠] z] (fun _ => c) := by
  have hc := represents_const c
  rw [← (realizedField.val.comp e).commutes] at hc
  exact (hr _).eventuallyEq_on_disc hR (hm _) (MeromorphicOn.const c) hc hz

theorem realize_add (a b : E) {z : ℂ} (hz : z ∈ ball 0 R) :
    G (a + b) =ᶠ[𝓝[≠] z] G a + G b := by
  have hab := (hr a).add (hr b)
  change Represents ((realizedField.val.comp e) a + (realizedField.val.comp e) b) _ at hab
  rw [← map_add] at hab
  exact (hr _).eventuallyEq_on_disc hR (hm _) ((hm a).add (hm b)) hab hz

theorem realize_mul (a b : E) {z : ℂ} (hz : z ∈ ball 0 R) :
    G (a * b) =ᶠ[𝓝[≠] z] G a * G b := by
  have hab := (hr a).mul (hr b)
  change Represents ((realizedField.val.comp e) a * (realizedField.val.comp e) b) _ at hab
  rw [← map_mul] at hab
  exact (hr _).eventuallyEq_on_disc hR (hm _) ((hm a).mul (hm b)) hab hz

theorem realize_sub_const (a : E) (c : ℂ) {z : ℂ} (hz : z ∈ ball 0 R) :
    G (a - algebraMap ℂ E c) =ᶠ[𝓝[≠] z] (fun u => G a u - c) := by
  have ha := realize_add e hR G hm hr a (algebraMap ℂ E (-c)) hz
  have hc := realize_const e hR G hm hr (-c) hz
  filter_upwards [ha, hc] with u hu hv
  rw [map_neg] at hv
  simpa only [map_neg, sub_eq_add_neg, Pi.add_apply, hv] using hu

end
end Dubon2026.SourceCurve.AnalyticDisc

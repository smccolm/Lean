import Dubon2026.SourceCurveConvergentDiscOrders
import Dubon2026.SourceCurveLocalDifferentials
import Mathlib.Analysis.Meromorphic.NormalForm

/-! DUB-17/18 -> auxiliary cover place charts -> an actual local coordinate.
The native meromorphic normal form of a genuine place uniformizer has
order one, so it is analytic with nonzero derivative. Nearby differences
therefore have order one and normalize the forthcoming place family. -/
namespace Dubon2026.SourceCurve.AnalyticDisc
noncomputable section
open SourceFunctionField.CuspTaylor Filter Metric
open scoped Topology
variable {E : Type*}

/-- Meromorphic normal form of the specified disk realization. -/
def normal (R : ℝ) (G : E → ℂ → ℂ) (a : E) : ℂ → ℂ :=
  toMeromorphicNFOn (G a) (ball 0 R)

theorem normal_germ {R : ℝ} {G : E → ℂ → ℂ}
    (hm : ∀ a, MeromorphicOn (G a) (ball 0 R)) (a : E)
    {z : ℂ} (hz : z ∈ ball 0 R) :
    normal R G a =ᶠ[𝓝[≠] z] G a :=
  (hm a).toMeromorphicNFOn_eq_self_on_nhdsNE hz

theorem normal_form {R : ℝ} (G : E → ℂ → ℂ) (a : E)
    {z : ℂ} (hz : z ∈ ball 0 R) : MeromorphicNFAt (normal R G a) z :=
  meromorphicNFOn_toMeromorphicNFOn _ _ hz

variable [Field E] [Algebra ℂ E]

theorem normal_uniformizer {R : ℝ} (hR : 0 < R) (G : E → ℂ → ℂ)
    (hm : ∀ a, MeromorphicOn (G a) (ball 0 R)) (w : Place ℂ E)
    (ho : meromorphicOrderAt (G w.uniformizer) 0 = (1 : ℤ)) :
    AnalyticAt ℂ (normal R G w.uniformizer) 0 ∧
      normal R G w.uniformizer 0 = 0 ∧ deriv (normal R G w.uniformizer) 0 ≠ 0 := by
  have hnf := normal_form G w.uniformizer (mem_ball_self hR)
  have horder : meromorphicOrderAt (normal R G w.uniformizer) 0 = (1 : ℤ) :=
    (meromorphicOrderAt_congr (normal_germ hm _ (mem_ball_self hR))).trans ho
  have ha : AnalyticAt ℂ (normal R G w.uniformizer) 0 :=
    hnf.meromorphicOrderAt_nonneg_iff_analyticAt.mp (by rw [horder]; norm_num)
  refine ⟨ha, ?_, ?_⟩
  · by_contra hne
    have hz := hnf.meromorphicOrderAt_eq_zero_iff.mpr hne
    rw [horder] at hz
    norm_num at hz
  · have hao : analyticOrderAt (normal R G w.uniformizer) 0 = (1 : ℕ∞) := by
      apply WithTop.map_injective (Nat.cast_injective (R := ℤ))
      change (analyticOrderAt (normal R G w.uniformizer) 0).map (Nat.cast : ℕ → ℤ) =
        (1 : ℕ∞).map (Nat.cast : ℕ → ℤ)
      rw [← ha.meromorphicOrderAt_eq, horder]
      rfl
    exact ha.deriv.analyticOrderAt_eq_zero.mp
      (analyticOrderAt_deriv_of_pos ha (n := 0) (by simpa only [Nat.cast_zero, zero_add] using hao))

theorem order_sub_uniformizer_one (e : E →ₐ[ℂ] realizedField) {R : ℝ}
    (hR : 0 < R) (G : E → ℂ → ℂ)
    (hm : ∀ a, MeromorphicOn (G a) (ball 0 R))
    (hr : ∀ a, Represents (e a).val (G a)) (w : Place ℂ E)
    {z : ℂ} (hz : z ∈ ball 0 R)
    (ha : AnalyticAt ℂ (normal R G w.uniformizer) z)
    (hd : deriv (normal R G w.uniformizer) z ≠ 0) :
    meromorphicOrderAt (G (w.uniformizer - algebraMap ℂ E (normal R G w.uniformizer z))) z =
      (1 : ℤ) := by
  rw [meromorphicOrderAt_congr (realize_sub_const e hR G hm hr _ _ hz)]
  have he := (normal_germ hm w.uniformizer hz).sub
    (Filter.EventuallyEq.rfl (f := fun _ : ℂ => normal R G w.uniformizer z))
  change meromorphicOrderAt (G w.uniformizer - fun _ => normal R G w.uniformizer z) z = _
  rw [← meromorphicOrderAt_congr he, (ha.sub analyticAt_const).meromorphicOrderAt_eq]
  have ho := ha.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hd
  change analyticOrderAt (normal R G w.uniformizer - fun _ => normal R G w.uniformizer z) z = 1 at ho
  rw [ho]
  rfl

end
end Dubon2026.SourceCurve.AnalyticDisc

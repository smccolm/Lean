import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Tactic.Ring

/-! DUB-17/18 -> cover Abel converse -> meromorphic loop generation.
Fill the residue-subtracted coefficient by its removable limit. The existing
source proof already knows an analytic remainder, so direct neighborhood
equality is shorter than deriving boundedness for a new removable-singularity
application. These are exactly the scalar steps needed by the actual cells. -/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open Set Filter
open scoped Topology

/-- The literal residue subtraction, filled at the pole by its punctured limit. -/
def residueSubtractedCoefficient (q r : ℂ) (f : ℂ → ℂ) : ℂ → ℂ := by
  classical
  exact Function.update (fun w => f w - r / (w - q)) q
    (limUnder (𝓝[≠] q) (fun w => f w - r / (w - q)))

theorem residueSubtractedCoefficient_of_ne (q r : ℂ) (f : ℂ → ℂ) {w : ℂ}
    (hw : w ≠ q) : residueSubtractedCoefficient q r f w = f w - r / (w - q) := by
  classical
  simp [residueSubtractedCoefficient, hw]

theorem analyticAt_residueSubtractedCoefficient_center (q r : ℂ) (f G : ℂ → ℂ)
    (hGa : AnalyticAt ℂ G q)
    (hG : ∀ᶠ w in 𝓝[≠] q, f w = r / (w - q) + G w) :
    AnalyticAt ℂ (residueSubtractedCoefficient q r f) q := by
  have ht : Tendsto (fun w => f w - r / (w - q)) (𝓝[≠] q) (𝓝 (G q)) := by
    refine (hGa.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [hG] with w hw
    rw [hw]
    ring
  have hlim := ht.limUnder_eq
  have heq : residueSubtractedCoefficient q r f =ᶠ[𝓝 q] G := by
    rw [eventually_nhdsWithin_iff] at hG
    filter_upwards [hG] with w hw
    by_cases hwq : w = q
    · subst w
      simp only [residueSubtractedCoefficient, Function.update_self, hlim]
    · rw [residueSubtractedCoefficient_of_ne q r f hwq, hw hwq]
      ring
  exact hGa.congr heq.symm

theorem analyticAt_residueSubtractedCoefficient_of_ne (q r : ℂ) (f : ℂ → ℂ)
    {w : ℂ} (hw : w ≠ q) (hf : AnalyticAt ℂ f w) :
    AnalyticAt ℂ (residueSubtractedCoefficient q r f) w := by
  have ha : AnalyticAt ℂ (fun w => f w - r / (w - q)) w :=
    hf.sub (analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.2 hw))
  apply ha.congr
  filter_upwards [isOpen_ne.mem_nhds hw] with z hz
  exact (residueSubtractedCoefficient_of_ne q r f hz).symm

end
end Dubon2026.SourceFunctionField.CellGeometry

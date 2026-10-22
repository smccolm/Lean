import Dubon2026.SourceOriginalMeromorphicFunctionComparison
import Dubon2026.SourceCurvePicardGroup

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi converse.
An analytic meromorphic function with prescribed original chart orders gives
an actual principal divisor in the original function field. The function-field
comparison is proved here, so only the meromorphic function and its orders
remain to be supplied by the forthcoming exponential construction.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Filter
open scoped Topology
variable (N : ℕ) [NeZero N]

theorem original_isPrincipal_of_meromorphic_orders
    (D : Divisor ℂ (modularFunctionFieldOver N ℂ))
    (g : Place ℂ (modularFunctionFieldOver N ℂ) → ℂ)
    (hg : ∀ v, MeromorphicAt (fun z => g (placeFamily N v z)) 0)
    (hord : ∀ v, meromorphicOrderAt (fun z => g (placeFamily N v z)) 0 = (D v : WithTop ℤ)) :
    Divisor.IsPrincipal D := by
  obtain ⟨f, hf⟩ := exists_original_function_of_meromorphicAt N g hg
  have hf0 : f ≠ 0 := by
    intro hz
    let v := originalAnalyticPlace N UpperHalfPlane.I
    have h := meromorphicOrderAt_congr (hf v)
    rw [hord v, hz, chartRead_zero] at h
    have htop : meromorphicOrderAt (0 : ℂ → ℂ) (0 : ℂ) = ⊤ :=
      meromorphicOrderAt_eq_top_iff.mpr (Eventually.of_forall fun _ => rfl)
    exact WithTop.coe_ne_top (h.trans htop)
  refine ⟨f, hf0, fun v => ?_⟩
  have h := meromorphicOrderAt_congr (hf v)
  rw [hord v, meromorphicOrderAt_chartRead N v hf0] at h
  exact WithTop.coe_injective h

end
end Dubon2026.SourceFunctionField.OriginalChart

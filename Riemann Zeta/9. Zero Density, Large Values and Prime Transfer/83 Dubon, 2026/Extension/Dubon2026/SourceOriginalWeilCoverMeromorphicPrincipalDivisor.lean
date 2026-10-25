import Dubon2026.SourceOriginalWeilCoverMeromorphicFunctionComparison
import Dubon2026.SourceCurvePicardGroup
import Dubon2026.SourceOriginalWeilCoverOnePole

/-! DUB-17/18 -> auxiliary point division -> cover Abel converse -> integral-period exponential and principality. Adapt the native original-curve deduction to the literal cover, using proved chart, residue and meromorphic comparison inputs. No global regularity or completed Abel converse is assumed. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n] (radicand : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C radicand : Polynomial FF)
variable (A : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hRadicand : radicand ≠ 0)
variable (hOrders : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord radicand = (n : ℤ) * A v)
include A hRadicand hOrders
local notation "CoverPath" => @Path (Place ℂ EE) (placeTopology N n radicand A hRadicand hOrders)

theorem cover_isPrincipal_of_meromorphic_orders
    (D : Divisor ℂ (EE))
    (g : Place ℂ (EE) → ℂ)
    (hg : ∀ v, MeromorphicAt (fun z => g (placeFamily N n radicand A hRadicand hOrders v z)) 0)
    (hord : ∀ v, meromorphicOrderAt (fun z => g (placeFamily N n radicand A hRadicand hOrders v z)) 0 = (D v : WithTop ℤ)) :
    Divisor.IsPrincipal D := by
  letI := placeTopology N n radicand A hRadicand hOrders
  obtain ⟨f, hf⟩ := exists_cover_function_of_meromorphicAt N n radicand A hRadicand hOrders g hg
  have hf0 : f ≠ 0 := by
    intro hz
    let v := Classical.choice (nonempty_cover_place N n radicand)
    have h := meromorphicOrderAt_congr (hf v)
    rw [hord v, hz, chartRead_zero] at h
    have htop : meromorphicOrderAt (0 : ℂ → ℂ) (0 : ℂ) = ⊤ :=
      meromorphicOrderAt_eq_top_iff.mpr (Eventually.of_forall fun _ => rfl)
    exact WithTop.coe_ne_top (h.trans htop)
  refine ⟨f, hf0, fun v => ?_⟩
  have h := meromorphicOrderAt_congr (hf v)
  rw [hord v, meromorphicOrderAt_chartRead N n radicand A hRadicand hOrders v hf0] at h
  exact WithTop.coe_injective h


end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart

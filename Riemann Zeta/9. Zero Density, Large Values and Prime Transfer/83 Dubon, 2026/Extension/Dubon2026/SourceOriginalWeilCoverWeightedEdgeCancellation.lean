import Dubon2026.SourceOriginalWeilCoverWeightedArcReversal

/-! DUB-17/18 -> cover Abel converse -> weighted residue reciprocity.
Use the existing C1 reversed-arc substitution on the actual coefficient.
The actual dissection supplies the overlap and geometry; its constructed
primitive derivatives and constant jumps give the weighted cancellation. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Set Filter KaehlerDifferential CellGeometry
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (radicand : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C radicand : Polynomial FF)
variable (baseDivisor : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hRadicand : radicand ≠ 0)
variable (hOrders : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord radicand = (n : ℤ) * baseDivisor v)
include baseDivisor hRadicand hOrders
local notation "PC" => placeChart N n radicand baseDivisor hRadicand hOrders
local notation "PF" => placeFamily N n radicand baseDivisor hRadicand hOrders
local notation "RD" => readDifferential N n radicand baseDivisor hRadicand hOrders
local notation "CF" => coverCoeffIn N n radicand baseDivisor hRadicand hOrders

local notation "BI" => coverBoundaryIntegrand N n radicand baseDivisor hRadicand hOrders

open MeasureTheory

open intervalIntegral
open scoped Interval

theorem cover_weighted_edge_cancellation :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (C C' : RadialCell (Place ℂ EE)),
      (∀ P ∈ C.ζ.source, AnalyticAt ℂ (C.ζ ∘ PF P) 0 ∧ deriv (C.ζ ∘ PF P) 0 ≠ 0) →
      (∀ P ∈ C'.ζ.source, AnalyticAt ℂ (C'.ζ ∘ PF P) 0 ∧ deriv (C'.ζ ∘ PF P) 0 ≠ 0) →
      ∀ (k : Fin C.R.N) (k' : Fin C'.R.N) (ψ : ℝ → ℝ),
      StrictAntiOn ψ (C'.R.arcIcc k') → ContDiffOn ℝ 1 ψ (C'.R.arcIcc k') →
      ψ (C'.R.φs k'.castSucc) = C.R.φs k.succ →
      ψ (C'.R.φs k'.succ) = C.R.φs k.castSucc →
      (∀ u ∈ C'.R.arcIcc k', C'.bdry u = C.bdry (ψ u)) →
      (∀ s ∈ C.R.arcIcc k, C.bdry s ∈ C'.ζ.source ∧ C'.ζ (C.bdry s) ∈ C'.R.K) →
      ∀ (θ : Ω[EE⁄ℂ]), (∀ s ∈ C.R.arcIcc k, 0 ≤ (C.bdry s).ordDifferential θ) →
      ∀ (Ψ Ψ' : ℂ → ℂ), (∀ w ∈ C.R.K, ContinuousAt Ψ w) →
      (∀ w ∈ C'.R.K, ContinuousAt Ψ' w) → ∀ J : ℂ,
      (∀ s ∈ C.R.arcIcc k, Ψ (C.R.loop s) - Ψ' (C'.ζ (C.bdry s)) = J) →
      (∫ s in (C.R.φs k.castSucc)..(C.R.φs k.succ), Ψ (C.R.loop s) * BI C θ s) +
        (∫ t in (C'.R.φs k'.castSucc)..(C'.R.φs k'.succ), Ψ' (C'.R.loop t) * BI C' θ t) =
          J * ∫ s in (C.R.φs k.castSucc)..(C.R.φs k.succ), BI C θ s := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro C C' hC hC' k k' ψ hanti hc ha hb hbd hover θ hθ Ψ Ψ' hΨ hΨ' J hJ
  have hab : C.R.φs k.castSucc < C.R.φs k.succ := C.R.hmono Fin.castSucc_lt_succ
  have hP : ContinuousOn (fun s => Ψ (C.R.loop s)) (C.R.arcIcc k) := by
    intro s _
    exact ((hΨ _ (C.R.loop_mem_K s)).comp C.R.continuous_loop.continuousAt).continuousWithinAt
  have hW : ContinuousOn (fun s => Ψ' (C'.ζ (C.bdry s))) (C.R.arcIcc k) := by
    intro s hs
    exact (((hΨ' _ (hover s hs).2).comp (C'.ζ.continuousAt (hover s hs).1)).comp
      C.continuous_bdry.continuousAt).continuousWithinAt
  have hI1 := (cover_weighted_arc_integral_extension N n radicand baseDivisor hRadicand hOrders C hC k θ hθ _ hP).1
  have hI2 := (cover_weighted_arc_integral_extension N n radicand baseDivisor hRadicand hOrders C hC k θ hθ _ hW).1
  rw [cover_weighted_reversed_arc_integral N n radicand baseDivisor hRadicand hOrders C C' hC hC' k k' ψ hanti hc ha hb hbd hover θ hθ Ψ' hΨ',
    ← sub_eq_add_neg, ← integral_sub hI1 hI2, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  rw [uIcc_of_le hab.le]
  intro s hs
  dsimp only
  rw [← sub_mul, hJ s hs]

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart

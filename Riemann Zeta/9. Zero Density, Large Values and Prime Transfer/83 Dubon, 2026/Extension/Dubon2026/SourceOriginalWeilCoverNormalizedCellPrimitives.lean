import Dubon2026.SourceOriginalWeilCoverDissectionPrimitiveJumps
import Dubon2026.SourceRadialDualTreeNormalization
import Dubon2026.SourceRadialDissectionArcPaths

/-! DUB-17/18 -> cover reciprocity -> actual cell primitives.
The constructed regular cell primitives and proved actual paired overlaps
give constant jumps on every edge of the same cover dissection. The primitives
and jumps are both constructed from the actual regular differentials. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Set KaehlerDifferential CellGeometry
open CellGeometry.IntegerEdgeChains CellGeometry.RadialDissectionTrees
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (radicand : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C radicand : Polynomial FF)
variable (baseDivisor : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hRadicand : radicand ≠ 0)
variable (hOrders : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord radicand = (n : ℤ) * baseDivisor v)
include baseDivisor hRadicand hOrders

theorem cover_exists_normalized_primitives_and_jumps {κ : Type*} :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (D : RadialCellDissection (Place ℂ EE)),
      (∀ C P, P ∈ (D.cell C).ζ.source →
        AnalyticAt ℂ ((D.cell C).ζ ∘ placeFamily N n radicand baseDivisor hRadicand hOrders P) 0 ∧
        deriv ((D.cell C).ζ ∘ placeFamily N n radicand baseDivisor hRadicand hOrders P) 0 ≠ 0) →
      ∀ (η : κ → Ω[EE⁄ℂ]), (∀ i, η i ∈ regularDifferentials ℂ EE) →
      ∀ (Ts : Finset D.ιE),
      IsTree (fun e => Cside D e true) (fun e => Cside D e false) Ts →
      ∀ (C₀ : D.ιC) (w₀ : ℂ),
    ∃ (V : D.ιC → Set ℂ) (Ψ : κ → D.ιC → ℂ → ℂ) (J : D.ιE → κ → ℂ),
      (∀ C, IsOpen (V C) ∧ (D.cell C).R.q ∈ V C ∧
        StarConvex ℝ (D.cell C).R.q (V C) ∧ (D.cell C).R.K ⊆ V C ∧ V C ⊆ (D.cell C).ζ.target) ∧
      (∀ i C, ∀ w ∈ V C, HasDerivAt (Ψ i C) (coverCoeffIn N n radicand baseDivisor hRadicand hOrders (D.cell C).ζ (η i) w) w) ∧
      (∀ e i,
        let p := D.arcOf (e, true)
        let n := D.arcOf (e, false)
        ∀ s ∈ (D.cell p.1).R.arcIcc p.2,
          Ψ i p.1 ((D.cell p.1).R.loop s) -
            Ψ i n.1 ((D.cell n.1).ζ ((D.cell p.1).bdry s)) = J e i) ∧
      (∀ e ∈ Ts, J e = 0) ∧ ∀ i, Ψ i C₀ w₀ = 0 := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro D hD η hη Ts hTs C₀ w₀
  obtain ⟨V, Ψ, J, hV, hΨ, hJ⟩ := cover_exists_regular_primitives_and_jumps N n radicand baseDivisor hRadicand hOrders D hD η hη
  obtain ⟨c, hc, hce⟩ := D.exists_normalising_constants Ts hTs J C₀ (fun i => Ψ i C₀ w₀)
  refine ⟨V, (fun i C w => Ψ i C w + c C i),
    (fun e => J e + c (Cside D e true) - c (Cside D e false)), hV, ?_, ?_, hce, ?_⟩
  · intro i C w hw
    exact ((hΨ i C).2 w hw).add_const _
  · intro e i
    dsimp only
    intro s hs
    have hj := hJ e i s hs
    change Ψ i (D.arcOf (e, true)).1 ((D.cell (D.arcOf (e, true)).1).R.loop s) +
        c (D.arcOf (e, true)).1 i -
        (Ψ i (D.arcOf (e, false)).1 ((D.cell (D.arcOf (e, false)).1).ζ
          ((D.cell (D.arcOf (e, true)).1).bdry s)) + c (D.arcOf (e, false)).1 i) =
      J e i + c (D.arcOf (e, true)).1 i - c (D.arcOf (e, false)).1 i
    linear_combination hj
  · intro i
    simp only [hc, Pi.neg_apply]
    exact add_neg_cancel _

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart

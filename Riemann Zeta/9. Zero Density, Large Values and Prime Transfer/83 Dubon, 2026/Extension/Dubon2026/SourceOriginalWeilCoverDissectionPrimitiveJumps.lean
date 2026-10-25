import Dubon2026.SourceOriginalWeilCoverCellPrimitiveFamily
import Dubon2026.SourceOriginalWeilCoverCellPrimitiveJumps
import Dubon2026.SourceRadialPairedArcOverlap

/-! DUB-17/18 -> cover reciprocity -> actual cell primitives.
The constructed regular cell primitives and proved actual paired overlaps
give constant jumps on every edge of the same cover dissection. The primitives
and jumps are both constructed from the actual regular differentials. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Set KaehlerDifferential CellGeometry
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (radicand : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C radicand : Polynomial FF)
variable (baseDivisor : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hRadicand : radicand ≠ 0)
variable (hOrders : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord radicand = (n : ℤ) * baseDivisor v)
include baseDivisor hRadicand hOrders

theorem cover_exists_regular_primitives_and_jumps {κ : Type*} :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (D : RadialCellDissection (Place ℂ EE)),
      (∀ C P, P ∈ (D.cell C).ζ.source →
        AnalyticAt ℂ ((D.cell C).ζ ∘ placeFamily N n radicand baseDivisor hRadicand hOrders P) 0 ∧
        deriv ((D.cell C).ζ ∘ placeFamily N n radicand baseDivisor hRadicand hOrders P) 0 ≠ 0) →
      ∀ (η : κ → Ω[EE⁄ℂ]), (∀ i, η i ∈ regularDifferentials ℂ EE) →
    ∃ (V : D.ιC → Set ℂ) (Ψ : κ → D.ιC → ℂ → ℂ) (J : D.ιE → κ → ℂ),
      (∀ C, IsOpen (V C) ∧ (D.cell C).R.q ∈ V C ∧
        StarConvex ℝ (D.cell C).R.q (V C) ∧ (D.cell C).R.K ⊆ V C ∧ V C ⊆ (D.cell C).ζ.target) ∧
      (∀ i C, Ψ i C (D.cell C).R.q = 0 ∧ ∀ w ∈ V C,
        HasDerivAt (Ψ i C) (coverCoeffIn N n radicand baseDivisor hRadicand hOrders (D.cell C).ζ (η i) w) w) ∧
      ∀ e i,
        let p := D.arcOf (e, true)
        let q := D.arcOf (e, false)
        ∀ s ∈ (D.cell p.1).R.arcIcc p.2,
          Ψ i p.1 ((D.cell p.1).R.loop s) -
            Ψ i q.1 ((D.cell q.1).ζ ((D.cell p.1).bdry s)) = J e i := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro D hD η hη
  obtain ⟨V, Ψ, hV, hΨ⟩ := cover_cell_primitives_of_coordinates N n radicand baseDivisor hRadicand hOrders D hD η hη
  have hj : ∀ e : D.ιE, ∀ i : κ, ∃ J : ℂ,
      let p := D.arcOf (e, true)
      let q := D.arcOf (e, false)
      ∀ s ∈ (D.cell p.1).R.arcIcc p.2,
        Ψ i p.1 ((D.cell p.1).R.loop s) -
          Ψ i q.1 ((D.cell q.1).ζ ((D.cell p.1).bdry s)) = J := by
    intro e i
    let p := D.arcOf (e, true)
    let q := D.arcOf (e, false)
    exact cover_primitive_jump_on_arc N n radicand baseDivisor hRadicand hOrders
      (D.cell p.1) (D.cell q.1) (hD _) (hD _) p.2 (D.paired_arc_overlap e)
      (η i) (Ψ i p.1) (Ψ i q.1)
      (fun w hw => (hΨ i p.1).2 w ((hV p.1).2.2.2.1 hw))
      (fun w hw => (hΨ i q.1).2 w ((hV q.1).2.2.2.1 hw))
  choose J hJ using hj
  exact ⟨V, Ψ, J, hV, hΨ, hJ⟩

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart

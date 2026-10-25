import Dubon2026.SourceOriginalWeilCoverEulerDissectionData

/-! DUB-17/18 -> actual cover reciprocity -> complete marked Euler dissection.
The proved centered original global cover supplies the projected marked data.
The actual lifted-dissection construction discharges every remaining geometric
and Euler premise, with exact actual regular-differential genus. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Set Topology CellGeometry
attribute [local instance] OriginalChart.placeTopology restrictionIntegral
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (radicand : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C radicand : Polynomial FF)
variable (baseDivisor : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hRadicand : radicand ≠ 0)
variable (hOrders : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord radicand = (n : ℤ) * baseDivisor v)
include baseDivisor hRadicand hOrders



theorem exists_cover_euler_cell_dissection (P₀ : Place ℂ EE) (S : Finset (Place ℂ EE)) :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∃ D : RadialCellDissection (Place ℂ EE),
      (∀ P ∈ insert P₀ (S : Set (Place ℂ EE)), ∃ i : D.ιC,
        P ∈ (D.cell i).interior' ∧ (D.cell i).ζ P = (D.cell i).R.q) ∧
      (∀ i : D.ιC, ((D.cell i).carrier ∩ (S : Set (Place ℂ EE))).Subsingleton) ∧
      ((Fintype.card D.ιV : ℤ) - (Fintype.card D.ιE : ℤ) + (Fintype.card D.ιC : ℤ) =
        2 - 2 * (Module.finrank ℂ (regularDifferentials ℂ EE) : ℤ)) ∧
      Function.Injective D.vert ∧
      (∀ v : D.ιV, ∃ e : D.ιE, (D.ends e).1 = v ∨ (D.ends e).2 = v) ∧
      ∀ i P, P ∈ (D.cell i).ζ.source →
        AnalyticAt ℂ ((D.cell i).ζ ∘ placeFamily N n radicand baseDivisor hRadicand hOrders P) 0 ∧
          deriv ((D.cell i).ζ ∘ placeFamily N n radicand baseDivisor hRadicand hOrders P) 0 ≠ 0 := by
  classical
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  let p : Place ℂ EE → Place ℂ FF := fun w => w.restrict FF
  let S₀ := S.image p
  obtain ⟨Marked, A, _, hcent, hsep⟩ := exists_original_centered_global_cover N (p P₀) S₀
  apply cover_euler_dissection_of_centered_base N n radicand baseDivisor hRadicand hOrders Marked A P₀ S
  · intro w hw
    apply hcent (p w)
    rcases hw with hw | hw
    · exact Or.inl (congrArg p hw)
    · exact Or.inr (Finset.mem_image.mpr ⟨w, hw, rfl⟩)
  · intro i
    simpa only [S₀, Finset.coe_image] using hsep i

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart

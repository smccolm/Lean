import Dubon2026.SourceOriginalWeilCoverCellPrimitives

/-! DUB-17/18 -> cover reciprocity -> actual cell primitives.
The native radial neighborhood and primitive theorems apply to the actual
cover coefficient. This constructs the domain and normalized primitives for
every family of actual regular differentials; neither is assumed. -/
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

/-- Normalized actual cell primitives and their constructed open domains.
Existence is proved below from the already proved forward cell coordinates. -/
def CoverCellPrimitives {ι : Type*} :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    (D : RadialCellDissection (Place ℂ EE)) → (ι → Ω[EE⁄ℂ]) → Prop := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  exact fun D η => ∃ (V : D.ιC → Set ℂ) (Ψ : ι → D.ιC → ℂ → ℂ),
    (∀ C, IsOpen (V C) ∧ (D.cell C).R.q ∈ V C ∧ StarConvex ℝ (D.cell C).R.q (V C) ∧
      (D.cell C).R.K ⊆ V C ∧ V C ⊆ (D.cell C).ζ.target) ∧
    ∀ i C, Ψ i C (D.cell C).R.q = 0 ∧ ∀ w ∈ V C,
      HasDerivAt (Ψ i C) (coverCoeffIn N n radicand baseDivisor hRadicand hOrders (D.cell C).ζ (η i) w) w

theorem cover_cell_primitives_of_coordinates {ι : Type*} :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (D : RadialCellDissection (Place ℂ EE)),
      (∀ C P, P ∈ (D.cell C).ζ.source →
        AnalyticAt ℂ ((D.cell C).ζ ∘ placeFamily N n radicand baseDivisor hRadicand hOrders P) 0 ∧
        deriv ((D.cell C).ζ ∘ placeFamily N n radicand baseDivisor hRadicand hOrders P) 0 ≠ 0) →
      ∀ (η : ι → Ω[EE⁄ℂ]), (∀ i, η i ∈ regularDifferentials ℂ EE) →
      CoverCellPrimitives N n radicand baseDivisor hRadicand hOrders D η := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro D hD η hη
  have h := fun C => cover_cell_exists_regular_primitives N n radicand baseDivisor hRadicand hOrders
    (D.cell C) (hD C) η hη
  choose V Ψ hVo hVq hVs hKV hVt hΨ using h
  exact ⟨V, fun i C => Ψ C i, fun C => ⟨hVo C, hVq C, hVs C, hKV C, hVt C⟩,
    fun i C => hΨ C i⟩

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart

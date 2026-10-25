import Dubon2026.SourceOriginalWeilCoverCellCoefficientPullback
import Dubon2026.SourceRadialCellDissection
import Dubon2026.SourceCellRadialPrimitive

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

theorem cover_cell_exists_regular_primitives {ι : Type*} :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (C : RadialCell (Place ℂ EE)),
      (∀ P ∈ C.ζ.source,
        AnalyticAt ℂ (C.ζ ∘ placeFamily N n radicand baseDivisor hRadicand hOrders P) 0 ∧
        deriv (C.ζ ∘ placeFamily N n radicand baseDivisor hRadicand hOrders P) 0 ≠ 0) →
      ∀ (η : ι → Ω[EE⁄ℂ]), (∀ i, η i ∈ regularDifferentials ℂ EE) →
      ∃ (V : Set ℂ) (Ψ : ι → ℂ → ℂ), IsOpen V ∧ C.R.q ∈ V ∧
        StarConvex ℝ C.R.q V ∧ C.R.K ⊆ V ∧ V ⊆ C.ζ.target ∧
        ∀ i, Ψ i C.R.q = 0 ∧ ∀ w ∈ V,
          HasDerivAt (Ψ i) (coverCoeffIn N n radicand baseDivisor hRadicand hOrders C.ζ (η i) w) w := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro C hC η hη
  obtain ⟨V, hVo, hVq, hVs, hKV, hVt⟩ :=
    C.R.exists_open_starConvex_neighborhood C.ζ.target C.ζ.open_target C.hKt
  have hprim : ∀ i, ∃ Ψ : ℂ → ℂ, Ψ C.R.q = 0 ∧ ∀ w ∈ V,
      HasDerivAt Ψ (coverCoeffIn N n radicand baseDivisor hRadicand hOrders C.ζ (η i) w) w := by
    intro i
    apply exists_radial_primitive hVo hVs
    intro w hw
    have hQ := C.ζ.map_target (hVt hw)
    have hθ := (mem_cover_regularDifferentials_iff N n radicand (η i)).mp (hη i) (C.ζ.symm w)
    have h := (cover_coeff_eq_near N n radicand baseDivisor hRadicand hOrders C.ζ hQ
      (hC _ hQ).1 (hC _ hQ).2 (η i) hθ).2
    rw [C.ζ.right_inv (hVt hw)] at h
    exact h.differentiableAt.differentiableWithinAt
  choose Ψ hΨ0 hΨ using hprim
  exact ⟨V, Ψ, hVo, hVq, hVs, hKV, hVt, fun i => ⟨hΨ0 i, hΨ i⟩⟩

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart

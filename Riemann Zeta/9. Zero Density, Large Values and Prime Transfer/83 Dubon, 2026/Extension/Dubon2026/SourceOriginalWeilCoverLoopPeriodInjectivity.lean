import Dubon2026.SourceOriginalWeilCoverPeriodAnnihilator
import Dubon2026.SourceOriginalWeilCoverFinitePeriodGeneration
import Dubon2026.SourcePeriodMatrixInjectivity

/-! DUB-17/18 -> cover Abel converse -> raw reciprocity period correction.
A kernel functional of the actual period matrix annihilates all periods by
integer generation. Its real and imaginary parts vanish by the proved compact
maximum principle. This proves the necessary injectivity directly, without
constructing a real period basis, lattice discreteness or freeness. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential Matrix
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n] (radicand : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C radicand : Polynomial FF)
variable (baseDivisor : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hRadicand : radicand ≠ 0)
variable (hOrders : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord radicand = (n : ℤ) * baseDivisor v)
include baseDivisor hRadicand hOrders
local notation "CoverPath" => @Path (Place ℂ EE) (placeTopology N n radicand baseDivisor hRadicand hOrders)


theorem cover_loop_period_matrix_injective {kDim : ℕ}
    (b : Module.Basis (Fin kDim) ℂ (regularDifferentials ℂ EE))
    (Pz : Fin kDim ⊕ Fin kDim → Place ℂ EE) (Z : ∀ k, CoverPath (Pz k) (Pz k))
    (hgen : ∀ (P : Place ℂ EE) (γ : CoverPath P P), ∃ κ : Fin kDim ⊕ Fin kDim → ℤ,
      ∀ i, pathIntegral N n radicand baseDivisor hRadicand hOrders (b i : Ω[EE⁄ℂ]) γ =
        ∑ k, (κ k : ℂ) * pathIntegral N n radicand baseDivisor hRadicand hOrders (b i : Ω[EE⁄ℂ]) (Z k)) :
    Function.Injective (Matrix.mulVecLin
      (fun k i => pathIntegral N n radicand baseDivisor hRadicand hOrders (b i : Ω[EE⁄ℂ]) (Z k))) := by
  apply PeriodCorrection.matrix_mulVecLin_injective_of_period_annihilator
    (Λ := pathPeriodLattice N n radicand baseDivisor hRadicand hOrders (fun i => (b i : Ω[EE⁄ℂ])))
  · intro u hu
    exact exists_cover_period_coordinates N n radicand baseDivisor hRadicand hOrders
      (fun i => (b i : Ω[EE⁄ℂ])) Pz Z hgen hu
  · intro ℓ hℓ
    apply eq_zero_of_annihilates_periods N n radicand baseDivisor hRadicand hOrders
      (fun i => (b i : Ω[EE⁄ℂ])) (fun i => (b i).2) _ ℓ hℓ
    exact b.linearIndependent.map' (regularDifferentials ℂ EE).subtype (Submodule.ker_subtype _)

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart

import Dubon2026.SourceReductionPoleSpace
import Dubon2026.SourceModularReductionDimension
import Dubon2026.SourceModularCoefficientDivisorSupport
import Dubon2026.SourceCurvePoleDivisor

/-! DUB-17/18 -> original Frobenius/inertia -> actual good reduction ->
genus comparison. Literal coefficient reduction preserves every multiple of
the actual j pole divisor on the modular function fields. All coordinate,
degree, finite-support and chart-integrality inputs are derived. Original
constants have characteristic zero; all residue characteristics away from
the level remain included. Genus preservation and place comparison are still
separate obligations. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open SourceCurve

/-- The actual j pole divisor on the modular coefficient field. -/
def modularJPole (N : ℕ) [NeZero N] (K : Type*) [Field K] [PerfectField K] :
    Divisor K (modularFunctionFieldCoeff N K) :=
  poleDivisor (jCoeff N K) (finite_coeff_divisor_support N K (jCoeff N K))

theorem modularJPole_apply (N : ℕ) [NeZero N] (K : Type*) [Field K] [PerfectField K]
    (v : Place K (modularFunctionFieldCoeff N K)) :
    modularJPole N K v = max 0 (-v.ord (jCoeff N K)) := max_comm _ _

variable {L : Type*} [Field L] [CharZero L] [IsAlgClosed L]
variable (A : ValuationSubring L) (N : ℕ) [NeZero N]
local notation "FF" => modularFunctionFieldCoeff N L
local notation "kk" => IsLocalRing.ResidueField A
attribute [local instance] residueModularAlgebra

/-- The actual valuation residue constants are closed by the proved monic-lifting theorem. -/
local instance residueConstantsClosed : IsAlgClosed kk := valuation_residue_isAlgClosed A

theorem modularResidueHom_mem_j_pole_space (hNL : (N : L) ≠ 0) (hNk : (N : kk) ≠ 0)
    (m : ℕ) {f : gaussRing A N}
    (hf : (f : FF) ∈ LSpace (m • modularJPole N L)) :
    modularResidueHom A N hNL hNk f ∈ LSpace (m • modularJPole N kk) := by
  let R := modularRegularProlongation A N hNL hNk
  let x : R.integers := ⟨jCoeff N L, jCoeff_mem_gaussRing A N⟩
  have hres : R.residue x = jCoeff N kk := modularResidueHom_jCoeff A N hNL hNk
  apply RegularProlongation.residue_mem_pole_space R x _ _ _
    (D := modularJPole N L) (Db := modularJPole N kk) _ _ m hf
  · rw [hres]
    exact transcendental_jCoeff N kk
  · rw [hres]
    exact (reduction_coordinate_degree A N hNL hNk).2
  · rw [hres]
    exact (reduction_coordinate_degree A N hNL hNk).1
  · exact modularJPole_apply N L
  · intro w
    rw [hres]
    exact modularJPole_apply N kk w

end
end Dubon2026.SourceFunctionField.GaussReduction

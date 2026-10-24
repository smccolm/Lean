import Dubon2026.SourceModularKummerCurve
import Dubon2026.SourceCurveFiniteCoordinateCanonicalDegree

/-! DUB-17/18 -> Picard torsion injectivity -> original-field power
lifting -> unramified Kummer-cover genus. The actual canonical divisor
on every finite arithmetic modular extension has degree twice its
source H1 genus minus two. Curve structure, canonical support, global
residue vanishing and residue duality are all discharged upstream. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve IntermediateField KaehlerDifferential
local notation "Qbar" => AlgebraicClosure ℚ
variable (N : ℕ) [NeZero N]
local notation "FF" => modularFunctionFieldCoeff N Qbar

theorem modular_extension_canonical_degree_eq_genusFF
    (E : Type*) [Field E] [Algebra FF E] [Algebra Qbar E]
    [IsScalarTower Qbar FF E] [FiniteDimensional FF E] :
    letI := (modular_extension_curve_and_canonical N E).2
    ∀ {ω : Ω[E⁄Qbar]} (hω : ω ≠ 0),
      Divisor.degree (canonicalDivisorOf hω) = 2 * (genusFF Qbar E : ℤ) - 2 := by
  letI := (modular_extension_curve_and_canonical N E).2
  letI hdim : FiniteDimensional Qbar⟮algebraMap FF E (jCoeff N Qbar)⟯ E :=
    modular_extension_finite_coordinate N E
  have ht : Transcendental Qbar (algebraMap FF E (jCoeff N Qbar)) :=
    (transcendental_algebraMap_iff (algebraMap FF E).injective).mpr (transcendental_jCoeff N Qbar)
  intro ω hω
  exact finite_coordinate_canonical_degree_eq_genusFF _ ht (modular_extension_D_j_ne_zero N E) hω

end
end Dubon2026.SourceFunctionField

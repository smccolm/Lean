import Dubon2026.SourceCurveWeilRankOne
import Dubon2026.SourceOriginalGlobalIndex
import Dubon2026.SourceOriginalAdelicQuotients

/-! DUB-17/18 -> actual regular differential dimension -> Riemann--Roch
-> residue duality. The literal original function field satisfies the
rank-one theorem for bounded global-annihilating functionals. All global
index, maximum, principal-divisor, residue and nonempty-place inputs are
derived. The remaining residue-duality obligation is to construct a
nonzero functional whose maximal bound is the actual canonical divisor.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]

theorem original_weil_differentials_rank_one :
    letI := hasPrincipalDivisors_original N L
    WeilDifferentialRankOne (K := L) (F := modularFunctionFieldOver N L) := by
  letI := hasPrincipalDivisors_original N L
  haveI : ∀ v : Place L (modularFunctionFieldOver N L), Module.Finite L v.ResidueField :=
    finite_original_place_residue N L
  haveI := finite_original_lSpace N L (0 : Divisor L (modularFunctionFieldOver N L))
  haveI := nonempty_original_places N L
  obtain ⟨γ, D₀, h⟩ := original_degree_dimension_maximum N L
  intro φ hφ hφ0 μ hμ
  exact weilDifferentialRankOne_of_genusReached h hφ hφ0 hμ

end
end Dubon2026.SourceFunctionField

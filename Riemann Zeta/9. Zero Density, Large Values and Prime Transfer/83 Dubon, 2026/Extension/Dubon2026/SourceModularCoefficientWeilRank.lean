import Dubon2026.SourceCurveWeilRankOne
import Dubon2026.SourceModularCoefficientGenusMaximum

/-! DUB-17/18 -> good reduction -> reverse genus inequality -> canonical
degree and residue duality. Reuse the existing local-residue and Weil-rank
proofs on the actual modular coefficient field. The residue constants,
canonical support and finite divisor-space maxima are proved in every
characteristic. Global residue vanishing remains a separate obligation;
no such vanishing is assumed or claimed here. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve KaehlerDifferential

variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [IsAlgClosed L]

theorem coeff_weil_differentials_rank_one :
    letI := hasPrincipalDivisors_coeff_field N L
    WeilDifferentialRankOne (K := L) (F := modularFunctionFieldCoeff N L) := by
  letI := hasPrincipalDivisors_coeff_field N L
  haveI : ∀ v : Place L (modularFunctionFieldCoeff N L), Module.Finite L v.ResidueField :=
    finite_coeff_place_residue N L
  haveI := finite_coeff_lSpace N L (0 : Divisor L (modularFunctionFieldCoeff N L))
  haveI := nonempty_coeff_place N L
  obtain ⟨γ, D₀, h⟩ := coeff_degree_dimension_maximum N L
  intro φ hφ hφ0 μ hμ
  exact weilDifferentialRankOne_of_genusReached h hφ hφ0 hμ

end
end Dubon2026.SourceFunctionField

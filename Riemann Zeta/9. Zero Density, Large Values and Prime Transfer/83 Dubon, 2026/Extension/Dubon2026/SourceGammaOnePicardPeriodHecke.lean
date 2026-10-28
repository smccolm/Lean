import Dubon2026.SourceGammaOnePicardHeckeDivisors
import Dubon2026.SourceGammaOneEndpointHecke
import Dubon2026.SourceGammaOnePicardPeriodEquiv

/-! DUB17/18 -> actual Gamma1 arithmetic realization -> Picard/H1
comparison. The proved original Picard-period equivalence intertwines
the literal algebraic prime Hecke correspondence and the dual native cusp
trace on the original integral-period quotient. Both compatibilities are
derived on actual analytic divisor representatives and descend by the
proved surjective presentation. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane SourceCurve CongruenceSubgroup SourceWeightTwoJacobi
open scoped MatrixGroups
variable (M p : ℕ) [NeZero M] [Fact p.Prime]
  (hT : ModularGroup.T ∈ Gamma1 M)

theorem picardPeriodEquiv_hecke
    (x : Pic0 ℂ (functionFieldOver (Gamma1 M) ℂ)) :
    picardPeriodEquiv M hT (heckePicard ℂ M p x) =
      periodQuotientHecke M p (picardPeriodEquiv M hT x) := by
  have hH : ModularGroup.T ∈ Gamma1 M ⊓ Gamma0 (p * M) :=
    ⟨hT, by simp [Gamma0_mem, ModularGroup.T]⟩
  have he (c : analyticDegree.ker) :
      picardPeriodEquiv M hT (analyticPicardHom M hT c) = analyticPeriodHom M c :=
    picardPeriodEquiv_analytic_divisor M hT c
  obtain ⟨c, rfl⟩ := analyticPicardHom_surjective M hT x
  rw [← analyticPicardHom_hecke M p hT hH, he, he, analyticPeriodHom_hecke]

end
end Dubon2026.SourceFunctionField.GammaOne

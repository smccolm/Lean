import Dubon2026.SourceGammaOneHeckeGammaZeroMap

/-! DUB17/18 -> actual Gamma1 Picard/Hecke comparison -> exact geometric
fibers. Equality of actual intersection-field places forces equality of
their original Gamma0 places, using the literal field inclusion and its
proved analytic germs. No global intersection-orbit identification is assumed. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane SourceCurve CongruenceSubgroup
open scoped MatrixGroups
variable (M d : ℕ) [NeZero M] [NeZero d]
  (hH : ModularGroup.T ∈ Gamma1 M ⊓ Gamma0 (d * M))
include hH

theorem analyticOrder_heckeGammaZero (τ : ℍ)
    (x : modularFunctionFieldOver (d * M) ℂ) :
    analyticOrder (Gamma1 M ⊓ Gamma0 (d * M)) τ (heckeGammaZeroMap M d x) =
      originalAnalyticOrder (d * M) τ x :=
  meromorphicOrderAt_congr (realize_heckeGammaZero_eventuallyEq M d hH x τ)

theorem mem_heckeGammaZero_analyticPlace (τ : ℍ)
    (x : modularFunctionFieldOver (d * M) ℂ) :
    heckeGammaZeroMap M d x ∈ (analyticPlace hH τ).toValuationSubring ↔
      x ∈ (originalAnalyticPlace (d * M) τ).toValuationSubring := by
  have ho : 0 ≤ analyticOrder (Gamma1 M ⊓ Gamma0 (d * M)) τ (heckeGammaZeroMap M d x) ↔
      0 ≤ originalAnalyticOrder (d * M) τ x := by
    rw [analyticOrder_heckeGammaZero M d hH]
  exact (analyticPlace_mem_iff hH τ _).trans
    (ho.trans (originalAnalyticPlace_mem_iff (d * M) τ x).symm)

theorem originalGammaZeroPlace_eq_of_heckePlace_eq (τ τ' : ℍ)
    (he : analyticPlace hH τ = analyticPlace hH τ') :
    originalAnalyticPlace (d * M) τ = originalAnalyticPlace (d * M) τ' := by
  apply Place.ext
  ext x
  exact (mem_heckeGammaZero_analyticPlace M d hH τ x).symm.trans
    ((Iff.of_eq (congrArg (fun P : Place ℂ (functionFieldOver (Gamma1 M ⊓ Gamma0 (d * M)) ℂ) =>
      heckeGammaZeroMap M d x ∈ P.toValuationSubring) he)).trans
        (mem_heckeGammaZero_analyticPlace M d hH τ' x))

end
end Dubon2026.SourceFunctionField.GammaOne

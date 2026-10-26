import Dubon2026.OriginalAdicIntegerNormComparison
import Dubon2026.OriginalIntegerLocalValuationMap

/-! DUB-17/18 -> prescribed coefficient reduction -> identify the actual
completion residue map on every original algebraic integer. Reuse the
proved completion-residue quotient equivalence and the identity-on-values
comparison between its original integer ring and norm valuation ring. -/
namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField ValuativeRel
variable (F : Type) [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F))
private local instance : ValuativeRel (w.adicCompletion F) :=
  ValuativeRel.ofValuation (NormedField.valuation (K := w.adicCompletion F))

/-- The original integer quotient identified with the norm-valuation residue field of its completion. -/
def sourceAdicCoefficientResidueEquiv :
    (𝓞 F ⧸ w.asIdeal) ≃+* 𝓀[w.adicCompletion F] :=
  (originalRingOfIntegersQuotientEquivAdicResidueField F w).trans
    (IsLocalRing.ResidueField.mapEquiv (originalAdicIntegerNormEquiv F w))

theorem sourceAdicCoefficientResidueEquiv_mk (x : 𝓞 F) :
    sourceAdicCoefficientResidueEquiv F w (Ideal.Quotient.mk w.asIdeal x) =
      IsLocalRing.residue 𝒪[w.adicCompletion F]
        (originalIntegerToValuationIntegerMap F (w.adicCompletion F) x) := by
  rfl

end
end Dubon2026

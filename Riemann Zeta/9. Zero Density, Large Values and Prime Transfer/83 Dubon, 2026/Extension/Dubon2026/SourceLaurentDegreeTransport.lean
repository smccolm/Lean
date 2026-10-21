import Dubon2026.SourceLaurentDegreeTransportSpan
import Dubon2026.SourceLaurentDegreeTransportIndependence

/-! DUB-17/18 -> numerical modular genus -> exact all-level j-map degree
-> transport from the rational original field to its geometric coefficient
extension. Literal Laurent coefficients preserve linear independence.
Polynomial denominator clearing and the existing finite original extension
then preserve the coordinate degree, allowing rational prime-power proofs
to serve the actual algebraically closed coefficient field.
Selected from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
Definitions/Def_ModularCurve_GeometricBaseChange.lean and
P2M/Sol/S_ModularCurve_relfinrank_laurentBaseChange.lean.
Only the finite degree-transport chain is selected; external global instance
changes, proof options and the infinite-dimensional generalization are omitted.
-/
namespace Dubon2026.SourceFunctionField.DegreeTransport
noncomputable section
open IntermediateField Polynomial

variable (L : Type*) [Field L] [Algebra ℚ L]
variable {F₀ : IntermediateField ℚ (LaurentSeries ℚ)} {t : LaurentSeries ℚ}

theorem relfinrank_eq_of_finite (ht : t ∈ F₀) (htr : Transcendental ℚ t)
    [FiniteDimensional (K₀ t) (E₀ F₀ t ht)] :
    relfinrank (K L t) (laurentBaseChange L F₀) = relfinrank (K₀ t) F₀ := by
  classical
  rw [relfinrank_eq_finrank_of_le (K_le L ht), relfinrank_eq_finrank_of_le (K₀_le ht)]
  change Module.finrank (K L t) (E L F₀ t ht) = Module.finrank (K₀ t) (E₀ F₀ t ht)
  obtain ⟨hfinE, hle⟩ := finite_and_finrank_le L ht
  haveI := hfinE
  refine le_antisymm hle ?_
  let b := Module.Free.chooseBasis (K₀ t) (E₀ F₀ t ht)
  have hind := linearIndependent_ψ L ht htr b.linearIndependent
  rw [Module.finrank_eq_card_chooseBasisIndex]
  exact hind.fintype_card_le_finrank

end
end Dubon2026.SourceFunctionField.DegreeTransport

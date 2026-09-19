import Tao2026.BadOneTermRegularVariation
import Tao2026.SmoothNumberSaddleFiniteHeightAssembly
import Tao2026.BurgessPolyaVinogradov
import Tao2026.BurgessWeilPrimeKummerLegendreLiteralWeil

/-!
# Theorem 1.7 reduced to the single Burgess input

The critical smooth-number saddle asymptotic is now unconditional.  This
file composes it with the previously conditional public endpoint, proving
that an explicit cubefree Burgess estimate alone implies Tao's Theorem 1.7.

It also carries the fixed seventh-moment complete Weil input, the full Kummer
Frobenius system, and the final pair of intrinsic spectral sources through
the entire Burgess argument to a concrete coefficient together with the
public theorem.  Thus the smooth-number input has disappeared from the
remaining Theorem 1.7 boundary.
-/

namespace Tao2026

/-- A concrete explicit Burgess coefficient together with the public
Theorem 1.7 conclusion it proves. -/
def TaoTheorem17BurgessCertificate : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    TaoExplicitCubefreeBurgessBound C 1 ∧ TaoTheorem17Conclusion

/-- The unconditional critical saddle theorem removes the last
smooth-number hypothesis from the Theorem 1.7 endpoint. -/
theorem taoTheorem17_unconditional_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀) :
    TaoTheorem17Conclusion :=
  taoTheorem17_of_criticalSmoothSaddleAsymptotic_explicitBurgess
    hC hburgess taoCriticalSmoothSaddleAsymptoticConclusion

/-- The fixed-moment complete Weil estimate yields both a nonnegative
explicit Burgess coefficient and Tao's Theorem 1.7. -/
theorem exists_explicitBurgess_and_taoTheorem17_of_completeWeil
    (hweil : TaoPrimitiveCubefreeBurgessCompleteWeilBoundRSeven) :
    TaoTheorem17BurgessCertificate := by
  have hη : 0 < taoBurgessRSevenEpsilon / 2 := by
    norm_num [taoBurgessRSevenEpsilon]
  obtain ⟨A, hA, hburgess⟩ :=
    exists_taoPrimitiveCubefreeBurgessRSevenBound_of_completeWeil hweil hη
  let C := RiemannZeta.GuthMaynard.divisorEpsilonConstant
    (taoBurgessRSevenEpsilon / 2) * A
  have hC : 0 ≤ C := mul_nonneg
    (RiemannZeta.GuthMaynard.divisorEpsilonConstant_pos _).le
    (zero_le_one.trans hA)
  have hexplicit : TaoExplicitCubefreeBurgessBound C 1 :=
    hburgess.toExplicit (zero_le_one.trans hA)
  exact ⟨C, hC, hexplicit,
    taoTheorem17_unconditional_of_explicitBurgess hC hexplicit⟩

/-- The full Kummer Frobenius system reaches the public Theorem 1.7
endpoint, while retaining its explicit Burgess witness. -/
theorem TaoPrimeKummerIsotypicFrobeniusSystem.toTheorem17BurgessCertificate
    (h : TaoPrimeKummerIsotypicFrobeniusSystem) :
    TaoTheorem17BurgessCertificate :=
  exists_explicitBurgess_and_taoTheorem17_of_completeWeil
    h.toCompositeRSeven

/-- The two final intrinsic spectral sources imply Tao's Theorem 1.7 and
produce the explicit Burgess certificate consumed by the proof. -/
theorem TaoPrimeExplicitLegendreAndRootMultisetSpectra.toTheorem17BurgessCertificate
    (h : TaoPrimeExplicitLegendreAndRootMultisetSpectra) :
    TaoTheorem17BurgessCertificate :=
  h.toFull.toTheorem17BurgessCertificate

/-- In particular, the two final intrinsic spectral sources imply the public
Theorem 1.7 conclusion directly. -/
theorem TaoPrimeExplicitLegendreAndRootMultisetSpectra.toTheorem17
    (h : TaoPrimeExplicitLegendreAndRootMultisetSpectra) :
    TaoTheorem17Conclusion := by
  obtain ⟨_C, _hC, _hburgess, h17⟩ := h.toTheorem17BurgessCertificate
  exact h17

/-- The fully concrete residual source—canonical Legendre roots with their
recurrence, together with the higher-root Kummer spectra—produces the
explicit Burgess certificate consumed by Theorem 1.7. -/
theorem TaoPrimeCanonicalLegendreAndRootMultisetSpectra.toTheorem17BurgessCertificate
    (h : TaoPrimeCanonicalLegendreAndRootMultisetSpectra) :
    TaoTheorem17BurgessCertificate :=
  h.toFull.toTheorem17BurgessCertificate

/-- In particular, the canonical-root formulation of the residual source
implies the public Theorem 1.7 conclusion directly. -/
theorem TaoPrimeCanonicalLegendreAndRootMultisetSpectra.toTheorem17
    (h : TaoPrimeCanonicalLegendreAndRootMultisetSpectra) :
    TaoTheorem17Conclusion := by
  obtain ⟨_C, _hC, _hburgess, h17⟩ := h.toTheorem17BurgessCertificate
  exact h17

/-- The determinant-only canonical Legendre formulation, together with the
higher-root spectra, produces the explicit Burgess certificate. -/
theorem TaoPrimeCanonicalDeterminantLegendreAndRootMultisetSpectra.toTheorem17BurgessCertificate
    (h : TaoPrimeCanonicalDeterminantLegendreAndRootMultisetSpectra) :
    TaoTheorem17BurgessCertificate :=
  h.toFull.toTheorem17BurgessCertificate

/-- The determinant-only canonical residual implies the public Theorem 1.7
conclusion directly. -/
theorem TaoPrimeCanonicalDeterminantLegendreAndRootMultisetSpectra.toTheorem17
    (h : TaoPrimeCanonicalDeterminantLegendreAndRootMultisetSpectra) :
    TaoTheorem17Conclusion := by
  obtain ⟨_C, _hC, _hburgess, h17⟩ := h.toTheorem17BurgessCertificate
  exact h17

/-- Once determinant integrality is discharged, canonical-root weight and
recurrence data together with the higher-root spectra still produce the
explicit Burgess certificate. -/
theorem TaoPrimeCanonicalWeightRecurrenceLegendreAndRootMultisetSpectra.toTheorem17BurgessCertificate
    (h : TaoPrimeCanonicalWeightRecurrenceLegendreAndRootMultisetSpectra) :
    TaoTheorem17BurgessCertificate :=
  h.toFull.toTheorem17BurgessCertificate

/-- The weight-and-recurrence residual implies the public Theorem 1.7
conclusion directly. -/
theorem TaoPrimeCanonicalWeightRecurrenceLegendreAndRootMultisetSpectra.toTheorem17
    (h : TaoPrimeCanonicalWeightRecurrenceLegendreAndRootMultisetSpectra) :
    TaoTheorem17Conclusion := by
  obtain ⟨_C, _hC, _hburgess, h17⟩ := h.toTheorem17BurgessCertificate
  exact h17

/-- The completely literal Legendre Weil-bound/recurrence source together
with the higher-root spectra produces the explicit Burgess certificate. -/
theorem TaoPrimeLiteralWeilRecurrenceLegendreAndRootMultisetSpectra.toTheorem17BurgessCertificate
    (h : TaoPrimeLiteralWeilRecurrenceLegendreAndRootMultisetSpectra) :
    TaoTheorem17BurgessCertificate :=
  h.toFull.toTheorem17BurgessCertificate

/-- The completely literal residual source implies the public Theorem 1.7
conclusion directly. -/
theorem TaoPrimeLiteralWeilRecurrenceLegendreAndRootMultisetSpectra.toTheorem17
    (h : TaoPrimeLiteralWeilRecurrenceLegendreAndRootMultisetSpectra) :
    TaoTheorem17Conclusion := by
  obtain ⟨_C, _hC, _hburgess, h17⟩ := h.toTheorem17BurgessCertificate
  exact h17

/-- The canonical unique-existence form of the higher-root source produces
the same explicit Burgess certificate. -/
theorem TaoPrimeLiteralWeilRecurrenceLegendreAndUniqueRootMultisetSpectrum.toTheorem17BurgessCertificate
    (h : TaoPrimeLiteralWeilRecurrenceLegendreAndUniqueRootMultisetSpectrum) :
    TaoTheorem17BurgessCertificate :=
  h.toFull.toTheorem17BurgessCertificate

/-- The literal Legendre conditions and uniquely determined higher-root
spectrum imply the public Theorem 1.7 conclusion directly. -/
theorem TaoPrimeLiteralWeilRecurrenceLegendreAndUniqueRootMultisetSpectrum.toTheorem17
    (h : TaoPrimeLiteralWeilRecurrenceLegendreAndUniqueRootMultisetSpectrum) :
    TaoTheorem17Conclusion := by
  obtain ⟨_C, _hC, _hburgess, h17⟩ := h.toTheorem17BurgessCertificate
  exact h17

/-- The fully canonical Newton-polynomial formulation of the residual
produces the explicit Burgess certificate. -/
theorem TaoPrimeLiteralWeilRecurrenceLegendreAndNewtonRootMultisetConditions.toTheorem17BurgessCertificate
    (h : TaoPrimeLiteralWeilRecurrenceLegendreAndNewtonRootMultisetConditions) :
    TaoTheorem17BurgessCertificate :=
  h.toFull.toTheorem17BurgessCertificate

/-- The literal Legendre conditions and fixed higher-root Newton-polynomial
conditions imply the public Theorem 1.7 conclusion directly. -/
theorem TaoPrimeLiteralWeilRecurrenceLegendreAndNewtonRootMultisetConditions.toTheorem17
    (h : TaoPrimeLiteralWeilRecurrenceLegendreAndNewtonRootMultisetConditions) :
    TaoTheorem17Conclusion := by
  obtain ⟨_C, _hC, _hburgess, h17⟩ := h.toTheorem17BurgessCertificate
  exact h17

/-- The finite-recurrence form of the Newton residual produces the explicit
Burgess certificate. -/
theorem TaoPrimeLiteralWeilRecurrenceLegendreAndNewtonRootMultisetRecurrenceConditions.toTheorem17BurgessCertificate
    (h : TaoPrimeLiteralWeilRecurrenceLegendreAndNewtonRootMultisetRecurrenceConditions) :
    TaoTheorem17BurgessCertificate :=
  h.toFull.toTheorem17BurgessCertificate

/-- The literal Legendre conditions and finite higher-root characteristic
recurrence imply the public Theorem 1.7 conclusion directly. -/
theorem TaoPrimeLiteralWeilRecurrenceLegendreAndNewtonRootMultisetRecurrenceConditions.toTheorem17
    (h : TaoPrimeLiteralWeilRecurrenceLegendreAndNewtonRootMultisetRecurrenceConditions) :
    TaoTheorem17Conclusion := by
  obtain ⟨_C, _hC, _hburgess, h17⟩ := h.toTheorem17BurgessCertificate
  exact h17

/-- The sharpened Newton-characteristic residual produces the explicit
Burgess certificate. -/
theorem TaoPrimeLiteralWeilRecurrenceLegendreAndNewtonCharacteristicConditions.toTheorem17BurgessCertificate
    (h : TaoPrimeLiteralWeilRecurrenceLegendreAndNewtonCharacteristicConditions) :
    TaoTheorem17BurgessCertificate :=
  h.toFull.toTheorem17BurgessCertificate

/-- The literal Legendre conditions and the sole higher-root characteristic
recurrence, together with fixed-root integrality and weight, imply Theorem
1.7 directly. -/
theorem TaoPrimeLiteralWeilRecurrenceLegendreAndNewtonCharacteristicConditions.toTheorem17
    (h : TaoPrimeLiteralWeilRecurrenceLegendreAndNewtonCharacteristicConditions) :
    TaoTheorem17Conclusion := by
  obtain ⟨_C, _hC, _hburgess, h17⟩ := h.toTheorem17BurgessCertificate
  exact h17

/-- The finite Newton-coefficient residual produces the explicit Burgess
certificate. -/
theorem TaoPrimeLiteralWeilRecurrenceLegendreAndNewtonCoefficientConditions.toTheorem17BurgessCertificate
    (h : TaoPrimeLiteralWeilRecurrenceLegendreAndNewtonCoefficientConditions) :
    TaoTheorem17BurgessCertificate :=
  h.toFull.toTheorem17BurgessCertificate

/-- The literal Legendre conditions and finite Newton-coefficient form of the
higher-root source imply Theorem 1.7 directly. -/
theorem TaoPrimeLiteralWeilRecurrenceLegendreAndNewtonCoefficientConditions.toTheorem17
    (h : TaoPrimeLiteralWeilRecurrenceLegendreAndNewtonCoefficientConditions) :
    TaoTheorem17Conclusion := by
  obtain ⟨_C, _hC, _hburgess, h17⟩ := h.toTheorem17BurgessCertificate
  exact h17

/-- The completely literal weight formulation of both Kummer branches
produces the explicit Burgess certificate. -/
theorem TaoPrimeLiteralWeilRecurrenceLegendreAndNewtonLiteralConditions.toTheorem17BurgessCertificate
    (h : TaoPrimeLiteralWeilRecurrenceLegendreAndNewtonLiteralConditions) :
    TaoTheorem17BurgessCertificate :=
  h.toFull.toTheorem17BurgessCertificate

/-- The fully literal Weil/recurrence residual, with finite higher-root
Newton-coefficient integrality, implies Theorem 1.7 directly. -/
theorem TaoPrimeLiteralWeilRecurrenceLegendreAndNewtonLiteralConditions.toTheorem17
    (h : TaoPrimeLiteralWeilRecurrenceLegendreAndNewtonLiteralConditions) :
    TaoTheorem17Conclusion := by
  obtain ⟨_C, _hC, _hburgess, h17⟩ := h.toTheorem17BurgessCertificate
  exact h17

end Tao2026

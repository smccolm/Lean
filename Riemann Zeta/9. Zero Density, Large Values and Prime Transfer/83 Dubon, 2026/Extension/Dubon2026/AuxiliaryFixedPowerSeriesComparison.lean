import Dubon2026.AuxiliaryPowerSeriesFixedParameters
import Mathlib.Data.Fintype.EquivFin

/-! An exact-size selected family uses a fixed power-series algebra and
variable ideal. The record retains the actual arithmetic comparison,
so its quotient and universal matrices come from that same family. -/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing

/-- Original arithmetic comparison with its genuine character directions
indexed by a fixed type. Both fields are constructed in the arithmetic
application; the maps below are derived from them. -/
structure AuxiliaryFixedPowerSeriesComparison
    (O : Type*) [CommRing O] {R A ι n G : Type*}
    [CommRing R] [IsLocalRing R] [Algebra O R] [CommRing A] [Algebra O A]
    [Fintype ι] [Fintype n] [DecidableEq n]
    (Q : Finset Nat.Primes) (q : ℕ)
    (τ : G → GeneralLinearGroup n R) (τ₀ : G → GeneralLinearGroup n A)
    (η : Type*) where
  /-- The actual original tame characters, parameters and coefficient comparison. -/
  comparison : AuxiliaryPowerSeriesAugmentationComparison O (ι := ι) Q q τ τ₀
  /-- Every fixed direction corresponds to exactly one genuine original direction. -/
  index : η ≃ Q × ι

variable (O : Type*) [CommRing O] {R A ι n G η : Type*}
  [CommRing R] [IsLocalRing R] [Algebra O R] [CommRing A] [Algebra O A]
  [Fintype ι] [Fintype n] [DecidableEq n]
  (Q : Finset Nat.Primes) (q : ℕ)
  (τ : G → GeneralLinearGroup n R) (τ₀ : G → GeneralLinearGroup n A)

/-- Exact cardinality constructs the fixed prime and character index. -/
def auxiliaryFixedPowerSeriesComparisonOfCard
    (degree g : ℕ)
    (d : AuxiliaryPowerSeriesAugmentationComparison O (ι := Fin degree) Q q τ τ₀)
    (hcard : Q.card = g) :
    AuxiliaryFixedPowerSeriesComparison O (ι := Fin degree) Q q τ τ₀ (Fin g × Fin degree) where
  comparison := d
  index := Equiv.prodCongr (Finset.equivFinOfCardEq hcard).symm (Equiv.refl _)

/-- Action of the fixed power-series algebra on the original coefficient ring. -/
def auxiliaryFixedPowerSeriesParameterMap
    (d : AuxiliaryFixedPowerSeriesComparison O (ι := ι) Q q τ τ₀ η) :
    MvPowerSeries η O →ₐ[O] R :=
  auxiliaryPowerSeriesFixedParameterMap O Q q τ τ₀ d.comparison d.index

/-- The same fixed variable ideal recovers the original base ring. -/
def auxiliaryFixedPowerSeriesQuotientEquiv
    (d : AuxiliaryFixedPowerSeriesComparison O (ι := ι) Q q τ τ₀ η) :
    (R ⧸ Ideal.map (auxiliaryFixedPowerSeriesParameterMap O Q q τ τ₀ d).toRingHom
      (Ideal.span (Set.range (MvPowerSeries.X (R := O) (σ := η))))) ≃ₐ[O] A :=
  auxiliaryPowerSeriesFixedQuotientEquiv O Q q τ τ₀ d.comparison d.index

/-- Reindexing retains the exact universal representation in the base quotient. -/
theorem auxiliaryFixedPowerSeriesQuotientEquiv_matrix
    (d : AuxiliaryFixedPowerSeriesComparison O (ι := ι) Q q τ τ₀ η) (g : G) :
    GeneralLinearGroup.map
      (auxiliaryFixedPowerSeriesQuotientEquiv O Q q τ τ₀ d).toAlgHom.toRingHom
      (GeneralLinearGroup.map
        (Ideal.Quotient.mk (Ideal.map
          (auxiliaryFixedPowerSeriesParameterMap O Q q τ τ₀ d).toRingHom
          (Ideal.span (Set.range (MvPowerSeries.X (R := O) (σ := η)))))) (τ g)) = τ₀ g :=
  auxiliaryPowerSeriesFixedQuotientEquiv_matrix O Q q τ τ₀ d.comparison d.index g

end
end Dubon2026

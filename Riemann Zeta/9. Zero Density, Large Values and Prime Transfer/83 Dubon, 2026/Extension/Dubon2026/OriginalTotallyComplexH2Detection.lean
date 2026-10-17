import Dubon2026.OriginalGlobalOddH2Detection
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

/-! # Finite-place detection over the actual totally complex base

The cyclic two-power subfield has no real places. Its upper infinite
decomposition groups therefore have order one, so actual infinite-place
H2 vanishes without an odd-torsion restriction. Existing original idele
local detection then gives the global zero test needed for DUB-17's
two-primary splitting and full-order class construction.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField

/-- The actual original infinite unit H2 vanishes over a totally complex
base, since the original prime stabilizer has order one. -/
theorem originalInfiniteUnitH2_zero_of_totallyComplex
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsTotallyComplex K]
    (w : InfinitePlace L) (x : groupCohomology (originalInfiniteUnitRep K L w) 2) : x = 0 := by
  have hu : w.IsUnramified K := InfinitePlace.isUnramified_iff.mpr
    (Or.inr (IsTotallyComplex.isComplex (w.comap (algebraMap K L))))
  have hc : Nat.card (OriginalInfiniteDecompositionGroup K L w) = 1 :=
    InfinitePlace.isUnramified_iff_card_stabilizer_eq_one.mp hu
  letI : Fintype (OriginalInfiniteDecompositionGroup K L w) := Fintype.ofFinite _
  have hx := finiteSecondCohomology_card_nsmul_eq_zero (originalInfiniteUnitRep K L w) x
  rw [← Nat.card_eq_fintype_card, hc, one_smul] at hx
  exact hx

/-- Every actual global unit H2 class over a totally complex number field
is detected by its literal finite-prime localizations. -/
theorem originalGlobalUnitH2_zero_of_finite_over_totallyComplex
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsTotallyComplex K]
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2)
    (hx : ∀ w : HeightOneSpectrum (𝓞 L), originalGlobalAdicH2 K L w x = 0) : x = 0 := by
  apply originalGlobalUnitH2_zero_of_points K L x
  intro S hS p
  cases p with
  | inl w =>
    exact originalIdelePointH2Map_principal_infinite_zero K L S hS w x
      (originalInfiniteUnitH2_zero_of_totallyComplex K L w (originalGlobalInfiniteH2 K L w x))
  | inr w =>
    exact originalIdelePointH2Map_principal_finite_zero K L S hS w x (hx w.val)

end
end Dubon2026

import Dubon2026.OriginalSupportedAdicH2Comparison
import Dubon2026.OriginalSupportedInfiniteH2Comparison
import Dubon2026.OriginalInfiniteOddH2

/-! # Actual finite-prime detection of odd-torsion original global H2

The proved original class-H1 vanishing and idele local detection are
consumed with the literal finite and infinite completion maps. Infinite
places vanish for odd-prime torsion by their proved two-annihilation.
Thus only actual finite-prime localizations remain to be killed by the
constructed cyclotomic stage in DUB-17's invariant sum-zero chain.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- An actual odd-prime-torsion original global unit H2 class is zero if all its literal finite-prime localizations vanish; no archimedean premise remains. -/
theorem originalGlobalUnitH2_zero_of_finite_at_odd_prime
    (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2)
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) (hxq : q • x = 0)
    (hx : ∀ w : HeightOneSpectrum (𝓞 L), originalGlobalAdicH2 K L w x = 0) : x = 0 := by
  apply originalGlobalUnitH2_zero_of_points K L x
  intro S hS p
  cases p with
  | inl w =>
    exact originalIdelePointH2Map_principal_infinite_zero K L S hS w x
      (originalGlobalInfiniteH2_eq_zero_of_odd_torsion K L w q hq hq2 x hxq)
  | inr w =>
    exact originalIdelePointH2Map_principal_finite_zero K L S hS w x (hx w.val)

end
end Dubon2026

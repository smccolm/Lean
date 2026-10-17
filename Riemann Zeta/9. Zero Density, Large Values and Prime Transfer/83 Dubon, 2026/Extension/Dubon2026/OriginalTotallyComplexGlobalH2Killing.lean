import Dubon2026.OriginalTotallyComplexH2Detection
import Dubon2026.OriginalGlobalH2FiniteDegreeKilling
import Dubon2026.OriginalPrimeTowerSelection

/-! # Actual global killing over a totally complex field

Original finite-place base-change comparisons and global detection give
zero in the actual compositum once local degrees kill the class. Total
complexity discharges every infinite-place condition. This removes the
odd-prime restriction from the killing step needed by DUB-17's constructed
two-primary cyclic stage; the degree and support inputs remain explicit
until the arithmetic stage assembly consumes them.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
attribute [-instance] UniformSpace.Completion.instSMul

/-- Divisible actual completion degrees on the original finite localization support kill the actual globally base-changed class over the totally complex field. -/
theorem originalGlobalUnitH2_baseChange_zero_of_totallyComplex_degrees
    (K E L M : Type) [Field K] [NumberField K] [Field E] [NumberField E]
    [Field L] [NumberField L] [Field M] [NumberField M]
    [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
    [IsScalarTower K E M] [IsScalarTower K L M]
    [FiniteDimensional K E] [FiniteDimensional K L] [FiniteDimensional E M]
    [IsGalois K E] [IsGalois K L] [IsGalois E M]
    [IsTotallyComplex E] (n : ℕ)
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) (hx : n • x = 0)
    (S : Finset (HeightOneSpectrum (𝓞 L)))
    (hS : ∀ w : HeightOneSpectrum (𝓞 L), w ∉ S → originalGlobalAdicH2 K L w x = 0)
    (hdegree : ∀ t : HeightOneSpectrum (𝓞 M), originalFinitePrimeBelow L M t ∈ S →
      let u := originalFinitePrimeBelow E M t
      let v := originalFinitePrimeBelow K E u
      letI := originalFinitePrimeBelow_liesOver K E u
      letI : Algebra (v.adicCompletion K) (u.adicCompletion E) :=
        (originalAdicBaseChangeMap K E v u).toAlgebra
      n ∣ Module.finrank (v.adicCompletion K) (u.adicCompletion E)) :
    groupCohomology.map (galoisBaseChangeRestriction K E L M)
      (galoisUnitBaseChangeInclusion K E L M) 2 x = 0 := by
  apply originalGlobalUnitH2_zero_of_finite_over_totallyComplex E M
  intro t
  let u := originalFinitePrimeBelow E M t
  let w := originalFinitePrimeBelow L M t
  let v := originalFinitePrimeBelow K E u
  have hv : v = originalFinitePrimeBelow K M t := originalFinitePrimeBelow_tower K E M t
  have hw : originalFinitePrimeBelow K L w = v :=
    (originalFinitePrimeBelow_tower K L M t).trans hv.symm
  letI : u.asIdeal.LiesOver v.asIdeal := originalFinitePrimeBelow_liesOver K E u
  letI : w.asIdeal.LiesOver v.asIdeal := by
    rw [← hw]
    exact originalFinitePrimeBelow_liesOver K L w
  letI : t.asIdeal.LiesOver v.asIdeal := by
    rw [hv]
    exact originalFinitePrimeBelow_liesOver K M t
  letI : t.asIdeal.LiesOver u.asIdeal := originalFinitePrimeBelow_liesOver E M t
  letI : t.asIdeal.LiesOver w.asIdeal := originalFinitePrimeBelow_liesOver L M t
  by_cases ht : w ∈ S
  · exact originalGlobalAdicH2_baseChange_zero_of_degree_dvd K E L M v u w t (n) x hx (hdegree t ht)
  · exact originalGlobalAdicH2_baseChange_zero_of_local_zero K E L M v u w t x (hS w ht)

end
end Dubon2026

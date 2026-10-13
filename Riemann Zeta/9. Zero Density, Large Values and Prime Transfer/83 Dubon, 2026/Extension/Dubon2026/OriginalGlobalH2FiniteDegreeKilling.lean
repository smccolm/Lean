import Dubon2026.OriginalGlobalAdicH2BaseChangeKilling
import Dubon2026.OriginalGlobalAdicH2BaseChangeZero
import Dubon2026.OriginalGlobalOddH2Detection
import Dubon2026.OriginalGlobalAdicH2FiniteSupport

/-! # Finite local degrees kill the actual original odd-primary global class

Outside the actual finite localization support, the proved base-change
square preserves zero. On that support the proved local degree theorem
kills the class. Original finite-prime detection derives the global zero,
including the already proved real-place odd-torsion vanishing. This is
the cohomological assembly consumed by DUB-17's cyclotomic stage.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
attribute [-instance] UniformSpace.Completion.instSMul

/-- Divisible actual completion degrees on the original finite localization support kill the actual globally base-changed odd-primary class. -/
theorem originalGlobalUnitH2_baseChange_zero_of_finite_degrees
    (K E L M : Type) [Field K] [NumberField K] [Field E] [NumberField E]
    [Field L] [NumberField L] [Field M] [NumberField M]
    [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
    [IsScalarTower K E M] [IsScalarTower K L M]
    [FiniteDimensional K E] [FiniteDimensional K L] [FiniteDimensional E M]
    [IsGalois K E] [IsGalois K L] [IsGalois E M]
    (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2)
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) (hx : q • x = 0)
    (S : Finset (HeightOneSpectrum (𝓞 L)))
    (hS : ∀ w : HeightOneSpectrum (𝓞 L), w ∉ S → originalGlobalAdicH2 K L w x = 0)
    (hdegree : ∀ t : HeightOneSpectrum (𝓞 M), originalFinitePrimeBelow L M t ∈ S →
      let u := originalFinitePrimeBelow E M t
      let v := originalFinitePrimeBelow K E u
      letI := originalFinitePrimeBelow_liesOver K E u
      letI : Algebra (v.adicCompletion K) (u.adicCompletion E) :=
        (originalAdicBaseChangeMap K E v u).toAlgebra
      q ∣ Module.finrank (v.adicCompletion K) (u.adicCompletion E)) :
    groupCohomology.map (galoisBaseChangeRestriction K E L M)
      (galoisUnitBaseChangeInclusion K E L M) 2 x = 0 := by
  let y := groupCohomology.map (galoisBaseChangeRestriction K E L M)
    (galoisUnitBaseChangeInclusion K E L M) 2 x
  have hy : q • y = 0 := by
    change q • groupCohomology.map _ _ 2 x = 0
    rw [← map_nsmul, hx]
    exact map_zero (groupCohomology.map (galoisBaseChangeRestriction K E L M)
      (galoisUnitBaseChangeInclusion K E L M) 2).hom
  apply originalGlobalUnitH2_zero_of_finite_at_odd_prime E M q hq hq2 y hy
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
  · exact originalGlobalAdicH2_baseChange_zero_of_degree_dvd K E L M v u w t q x hx (hdegree t ht)
  · exact originalGlobalAdicH2_baseChange_zero_of_local_zero K E L M v u w t x (hS w ht)

end
end Dubon2026

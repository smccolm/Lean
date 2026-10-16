import Dubon2026.OriginalGlobalOddPrimaryH2Detection
import Dubon2026.CyclotomicHigherLocalDegreeStage
import Dubon2026.OriginalGlobalH2FiniteDegreeKilling
import Dubon2026.OriginalIntegerPrimeTower

/-! # Constructed splitting of actual odd-primary global unit cohomology

The finite support of the original class and the constructed higher-degree
cyclotomic stage discharge every completion-degree premise. Finite-place
detection then proves zero in the actual compositum. This removes the
prime-torsion restriction on the cyclic splitting step used for DUB-17's
rational reciprocity and full-order idele-class invariant construction.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
attribute [-instance] UniformSpace.Completion.instSMul

/-- Divisible actual completion degrees on the original finite localization support kill the actual globally base-changed odd-primary class. -/
theorem originalGlobalUnitH2_baseChange_zero_of_prime_power_degrees
    (K E L M : Type) [Field K] [NumberField K] [Field E] [NumberField E]
    [Field L] [NumberField L] [Field M] [NumberField M]
    [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
    [IsScalarTower K E M] [IsScalarTower K L M]
    [FiniteDimensional K E] [FiniteDimensional K L] [FiniteDimensional E M]
    [IsGalois K E] [IsGalois K L] [IsGalois E M]
    (q r : ℕ) (hq : q.Prime) (hq2 : q ≠ 2)
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) (hx : q ^ r • x = 0)
    (S : Finset (HeightOneSpectrum (𝓞 L)))
    (hS : ∀ w : HeightOneSpectrum (𝓞 L), w ∉ S → originalGlobalAdicH2 K L w x = 0)
    (hdegree : ∀ t : HeightOneSpectrum (𝓞 M), originalFinitePrimeBelow L M t ∈ S →
      let u := originalFinitePrimeBelow E M t
      let v := originalFinitePrimeBelow K E u
      letI := originalFinitePrimeBelow_liesOver K E u
      letI : Algebra (v.adicCompletion K) (u.adicCompletion E) :=
        (originalAdicBaseChangeMap K E v u).toAlgebra
      q ^ r ∣ Module.finrank (v.adicCompletion K) (u.adicCompletion E)) :
    groupCohomology.map (galoisBaseChangeRestriction K E L M)
      (galoisUnitBaseChangeInclusion K E L M) 2 x = 0 := by
  let y := groupCohomology.map (galoisBaseChangeRestriction K E L M)
    (galoisUnitBaseChangeInclusion K E L M) 2 x
  have hy : q ^ r • y = 0 := by
    change q ^ r • groupCohomology.map _ _ 2 x = 0
    rw [← map_nsmul, hx]
    exact map_zero (groupCohomology.map (galoisBaseChangeRestriction K E L M)
      (galoisUnitBaseChangeInclusion K E L M) 2).hom
  apply originalGlobalUnitH2_zero_of_finite_at_odd_prime_power E M q hq hq2 r y hy
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
  · exact originalGlobalAdicH2_baseChange_zero_of_degree_dvd K E L M v u w t (q ^ r) x hx (hdegree t ht)
  · exact originalGlobalAdicH2_baseChange_zero_of_local_zero K E L M v u w t x (hS w ht)


attribute [-instance] DivisionRing.toRatAlgebra SubfieldClass.instSMulRat

/-- An actual odd-primary global class is killed in its actual compositum with a constructed cyclic cyclotomic stage inside the original unramified union. -/
theorem originalCyclotomic_exists_odd_primary_globalH2_killing_stage
    {Ω : Type} [Field Ω] [CharZero Ω] [Algebra ℚ Ω] [IsSepClosed Ω]
    (L : FiniteGaloisIntermediateField ℚ Ω)
    (a : 𝓞 ℚ) (q r : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits ℚ L) 2) (hx : q ^ (r + 1) • x = 0) :
    ∃ (k : ℕ) (F : FiniteGaloisIntermediateField ℚ Ω),
      r + 1 ≤ k ∧ IsCyclotomicExtension {q ^ (k + 1)} ℚ F ∧ IsCyclic Gal(F/ℚ) ∧
      F.toIntermediateField ≤ originalUnramifiedGaloisUnion (Ω := Ω) a ∧
      let M := L.toIntermediateField ⊔ F.toIntermediateField
      let iL : L →ₐ[ℚ] M := IntermediateField.inclusion (show L.toIntermediateField ≤ M from le_sup_left)
      let iF : F →ₐ[ℚ] M := IntermediateField.inclusion (show F.toIntermediateField ≤ M from le_sup_right)
      letI : Algebra L M := iL.toAlgebra
      letI : Algebra F M := iF.toAlgebra
      letI : IsScalarTower ℚ L M := IsScalarTower.of_algHom iL
      letI : IsScalarTower ℚ F M := IsScalarTower.of_algHom iF
      groupCohomology.map (galoisBaseChangeRestriction ℚ F L M)
        (galoisUnitBaseChangeInclusion ℚ F L M) 2 x = 0 := by
  letI : NumberField L := NumberField.of_module_finite ℚ L
  obtain ⟨S, hS⟩ := originalGlobalAdicH2_exists_finite_support ℚ L x
  choose p hp hwp using originalIntegerPrimeBelow_exists_prime L
  let T := S.image p
  have hT : ∀ r ∈ T, r.Prime := by
    intro r hr
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hr
    exact hp w
  obtain ⟨k, F, hk, hcyc, hCyclic, hUnion, hDegree⟩ :=
    originalCyclotomic_exists_higher_localDegree_stage (Ω := Ω) a q r hq hq2 hqa T hT
  have hrat : (DivisionRing.toRatAlgebra : Algebra ℚ F) = F.algebra' := Subsingleton.elim _ _
  rw [hrat] at hcyc hCyclic
  refine ⟨k, F, hk, hcyc, hCyclic, hUnion, ?_⟩
  let M := L.toIntermediateField ⊔ F.toIntermediateField
  let iL : L →ₐ[ℚ] M := IntermediateField.inclusion (show L.toIntermediateField ≤ M from le_sup_left)
  let iF : F →ₐ[ℚ] M := IntermediateField.inclusion (show F.toIntermediateField ≤ M from le_sup_right)
  letI : Algebra L M := iL.toAlgebra
  letI : Algebra F M := iF.toAlgebra
  letI : IsScalarTower ℚ L M := IsScalarTower.of_algHom iL
  letI : IsScalarTower ℚ F M := IsScalarTower.of_algHom iF
  letI : NumberField F := NumberField.of_module_finite ℚ F
  letI : NumberField M := NumberField.of_module_finite ℚ M
  letI : FiniteDimensional F M := FiniteDimensional.right ℚ F M
  letI : IsGalois F M := IsGalois.tower_top_of_isGalois ℚ F M
  apply originalGlobalUnitH2_baseChange_zero_of_prime_power_degrees ℚ F L M q (r + 1) hq hq2 x hx S hS
  intro t ht
  let w := originalFinitePrimeBelow L M t
  let u := originalFinitePrimeBelow F M t
  have hPrime : u.asIdeal.LiesOver (Ideal.span {(p w : ℤ)}) := by
    letI := hwp w
    refine ⟨?_⟩
    calc
      Ideal.span {(p w : ℤ)} = w.asIdeal.under ℤ := Ideal.over_def w.asIdeal _
      _ = t.asIdeal.under ℤ := congrArg HeightOneSpectrum.asIdeal (originalIntegerPrimeBelow_tower L M t)
      _ = u.asIdeal.under ℤ := (congrArg HeightOneSpectrum.asIdeal (originalIntegerPrimeBelow_tower F M t)).symm
  have hd : letI : Algebra ℚ F := DivisionRing.toRatAlgebra
      let v := originalFinitePrimeBelow ℚ F u
      letI := originalFinitePrimeBelow_liesOver ℚ F u
      letI : Algebra (v.adicCompletion ℚ) (u.adicCompletion F) :=
        (originalAdicBaseChangeMap ℚ F v u).toAlgebra
      q ^ (r + 1) ∣ Module.finrank (v.adicCompletion ℚ) (u.adicCompletion F) :=
    hDegree (p w) (Finset.mem_image.mpr ⟨w, ht, rfl⟩) u hPrime
  rw [hrat] at hd
  exact hd


end
end Dubon2026

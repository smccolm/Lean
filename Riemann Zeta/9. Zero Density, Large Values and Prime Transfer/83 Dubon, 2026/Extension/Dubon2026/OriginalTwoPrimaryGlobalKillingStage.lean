import Dubon2026.OriginalTwoPrimaryStageComparison
import Dubon2026.OriginalTotallyComplexGlobalH2Killing
import Dubon2026.OriginalIntegerPrimeTower

/-! # Constructed global killing of actual two-primary classes

The actual finite localization support determines one cyclotomic stage
inside the unchanged original arithmetic union. Its totally complex cyclic
subfield kills the original class in the common finite extension. All
support, completion-degree and infinite-place conditions are derived.
This supplies the missing two-primary splitting input on DUB-17's route
through cyclic descent and sum-zero to the full-order idele-class element.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
attribute [-instance] UniformSpace.Completion.instSMul DivisionRing.toRatAlgebra SubfieldClass.instSMulRat

/-- An actual two-primary global unit class becomes zero over a constructed
totally complex cyclic subfield in the original arithmetic union. -/
theorem originalUnramifiedUnion_exists_two_primary_globalH2_killing
    {Ω : Type} [Field Ω] [CharZero Ω] [Algebra ℚ Ω] [IsSepClosed Ω]
    (L : FiniteGaloisIntermediateField ℚ Ω) (a : 𝓞 ℚ) (r : ℕ)
    (h2a : (2 : 𝓞 ℚ) ∣ a)
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits ℚ L) 2) (hx : 2 ^ (r + 1) • x = 0) :
    ∃ (k : ℕ) (F : FiniteGaloisIntermediateField ℚ Ω),
      r + 2 ≤ k ∧ IsCyclotomicExtension {2 ^ (k + 1)} ℚ F ∧
      F.toIntermediateField ≤ originalUnramifiedGaloisUnion (Ω := Ω) a ∧
      ∃ E : IntermediateField ℚ F,
        IsGalois ℚ E ∧ IsCyclic Gal(E/ℚ) ∧ IsTotallyComplex E ∧
        let M := L.toIntermediateField ⊔ F.toIntermediateField
        let iL : L →ₐ[ℚ] M := IntermediateField.inclusion (show L.toIntermediateField ≤ M from le_sup_left)
        let iF : F →ₐ[ℚ] M := IntermediateField.inclusion (show F.toIntermediateField ≤ M from le_sup_right)
        let iE : E →ₐ[ℚ] M := iF.comp E.val
        letI : Algebra L M := iL.toAlgebra
        letI : Algebra E M := iE.toAlgebra
        letI : IsScalarTower ℚ L M := IsScalarTower.of_algHom iL
        letI : IsScalarTower ℚ E M := IsScalarTower.of_algHom iE
        groupCohomology.map (galoisBaseChangeRestriction ℚ E L M)
          (galoisUnitBaseChangeInclusion ℚ E L M) 2 x = 0 := by
  letI : NumberField L := NumberField.of_module_finite ℚ L
  obtain ⟨S, hS⟩ := originalGlobalAdicH2_exists_finite_support ℚ L x
  choose p hp hwp using originalIntegerPrimeBelow_exists_prime L
  let T := S.image p
  have hT : ∀ s ∈ T, s.Prime := by
    intro s hs
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hs
    exact hp w
  obtain ⟨k, F, hk, hcyclo, hUnion, E, hgal, hcyclic, hcomplex, hDegree⟩ :=
    originalUnramifiedUnion_exists_two_primary_original_stage (Ω := Ω) a r h2a T hT
  letI : NumberField F := NumberField.of_module_finite ℚ F
  letI := hgal
  letI := hcomplex
  letI : NumberField E := NumberField.of_module_finite ℚ E
  refine ⟨k, F, hk, hcyclo, hUnion, E, hgal, hcyclic, hcomplex, ?_⟩
  let M := L.toIntermediateField ⊔ F.toIntermediateField
  let iL : L →ₐ[ℚ] M := IntermediateField.inclusion (show L.toIntermediateField ≤ M from le_sup_left)
  let iF : F →ₐ[ℚ] M := IntermediateField.inclusion (show F.toIntermediateField ≤ M from le_sup_right)
  let iE : E →ₐ[ℚ] M := iF.comp E.val
  letI : Algebra L M := iL.toAlgebra
  letI : Algebra E M := iE.toAlgebra
  letI : Module E M := Algebra.toModule
  letI : SMul E M := iE.toAlgebra.toSMul
  letI : IsScalarTower ℚ L M := IsScalarTower.of_algHom iL
  letI : IsScalarTower ℚ E M := IsScalarTower.of_algHom iE
  letI : NumberField M := NumberField.of_module_finite ℚ M
  letI : FiniteDimensional E M := FiniteDimensional.right ℚ E M
  letI : IsGalois E M := IsGalois.tower_top_of_isGalois ℚ E M
  apply originalGlobalUnitH2_baseChange_zero_of_totallyComplex_degrees ℚ E L M (2 ^ (r + 1)) x hx S hS
  intro t ht
  let w := originalFinitePrimeBelow L M t
  let u := originalFinitePrimeBelow E M t
  have hPrime : u.asIdeal.LiesOver (Ideal.span {(p w : ℤ)}) := by
    letI := hwp w
    refine ⟨?_⟩
    calc
      Ideal.span {(p w : ℤ)} = w.asIdeal.under ℤ := Ideal.over_def w.asIdeal _
      _ = t.asIdeal.under ℤ := congrArg HeightOneSpectrum.asIdeal (originalIntegerPrimeBelow_tower L M t)
      _ = u.asIdeal.under ℤ := (congrArg HeightOneSpectrum.asIdeal (originalIntegerPrimeBelow_tower E M t)).symm
  exact hDegree (p w) (Finset.mem_image.mpr ⟨w, ht, rfl⟩) u hPrime

end
end Dubon2026

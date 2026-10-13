import Dubon2026.OriginalGlobalH2FiniteDegreeKilling
import Dubon2026.OriginalCyclotomicLocalDegreeStage
import Dubon2026.OriginalIntegerPrimeTower

/-! # A constructed cyclic cyclotomic extension kills the original global class

Finite support is derived from the actual original global H2 class.
The existing primitive-root construction supplies a cyclic stage in the
original unramified union with divisible original completion degrees at
the actual support primes. Their literal contractions in the compositum
discharge the degree premises of global killing. This is the cyclic
splitting step preceding principal-product and carry/cup comparison on
DUB-17's arithmetic invariant sum-zero dependency.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
attribute [-instance] UniformSpace.Completion.instSMul DivisionRing.toRatAlgebra SubfieldClass.instSMulRat

/-- An actual odd-primary global class is killed in its actual compositum with a constructed cyclic cyclotomic stage inside the original unramified union. -/
theorem originalCyclotomic_exists_globalH2_killing_stage
    {Ω : Type} [Field Ω] [CharZero Ω] [Algebra ℚ Ω] [IsSepClosed Ω]
    (L : FiniteGaloisIntermediateField ℚ Ω)
    (a : 𝓞 ℚ) (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits ℚ L) 2) (hx : q • x = 0) :
    ∃ (k : ℕ) (F : FiniteGaloisIntermediateField ℚ Ω),
      1 ≤ k ∧ IsCyclotomicExtension {q ^ (k + 1)} ℚ F ∧ IsCyclic Gal(F/ℚ) ∧
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
    originalCyclotomic_exists_localDegree_stage (Ω := Ω) a q hq hq2 hqa T hT
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
  apply originalGlobalUnitH2_baseChange_zero_of_finite_degrees ℚ F L M q hq hq2 x hx S hS
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
      q ∣ Module.finrank (v.adicCompletion ℚ) (u.adicCompletion F) :=
    hDegree (p w) (Finset.mem_image.mpr ⟨w, ht, rfl⟩) u hPrime
  rw [hrat] at hd
  exact hd

end
end Dubon2026

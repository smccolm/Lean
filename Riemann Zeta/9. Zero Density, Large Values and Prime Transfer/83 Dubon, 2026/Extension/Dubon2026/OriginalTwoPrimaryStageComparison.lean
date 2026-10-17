import Dubon2026.OriginalTwoPrimaryLocalDegreeStage

/-! # The constructed two-primary stage with its original rational algebras

Rational scalar structures are unique, but Lean's literal original stage
inclusions must retain their actual algebra instances. This comparison
keeps the same subfield carrier and transports the cyclicity and completed
degree statements. It enables the actual cohomology base-change assembly
on DUB-17's two-primary splitting route.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
attribute [-instance] UniformSpace.Completion.instSMul DivisionRing.toRatAlgebra SubfieldClass.instSMulRat

/-- The constructed local-degree field uses the actual original-stage
rational algebras and the literal original completed embeddings. -/
theorem originalUnramifiedUnion_exists_two_primary_original_stage
    {Ω : Type} [Field Ω] [CharZero Ω] [Algebra ℚ Ω] [IsSepClosed Ω]
    (a : 𝓞 ℚ) (r : ℕ) (h2a : (2 : 𝓞 ℚ) ∣ a)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∃ (k : ℕ) (F : FiniteGaloisIntermediateField ℚ Ω),
      r + 2 ≤ k ∧ IsCyclotomicExtension {2 ^ (k + 1)} ℚ F ∧
      F.toIntermediateField ≤ originalUnramifiedGaloisUnion (Ω := Ω) a ∧
      ∃ E : IntermediateField ℚ F,
        IsGalois ℚ E ∧ IsCyclic Gal(E/ℚ) ∧ IsTotallyComplex E ∧
        ∀ p ∈ S, ∀ w : HeightOneSpectrum (𝓞 E),
          w.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) →
          let v := originalFinitePrimeBelow ℚ E w
          letI := originalFinitePrimeBelow_liesOver ℚ E w
          letI : Algebra (v.adicCompletion ℚ) (w.adicCompletion E) :=
            (originalAdicBaseChangeMap ℚ E v w).toAlgebra
          2 ^ (r + 1) ∣ Module.finrank (v.adicCompletion ℚ) (w.adicCompletion E) := by
  obtain ⟨k, F, hF⟩ :=
    originalUnramifiedUnion_exists_two_primary_localDegree_subfield (Ω := Ω) a r h2a S hS
  dsimp only at hF
  obtain ⟨hk, hcyc₀, hUnion, E₀, hgal₀, hcyclic₀, hcomplex, _, hDegree⟩ := hF
  let S₀ : Subfield F := @IntermediateField.toSubfield ℚ F _ _ DivisionRing.toRatAlgebra E₀
  let E : IntermediateField ℚ F := {
    __ := S₀
    algebraMap_mem' := fun q => by
      have hrat : (DivisionRing.toRatAlgebra : Algebra ℚ F) = F.algebra' := Subsingleton.elim _ _
      have hm := @IntermediateField.algebraMap_mem ℚ F _ _ DivisionRing.toRatAlgebra E₀ q
      exact hrat ▸ hm }
  have hratF : (DivisionRing.toRatAlgebra : Algebra ℚ F) = F.algebra' := Subsingleton.elim _ _
  have hcyc : IsCyclotomicExtension {2 ^ (k + 1)} ℚ F := hratF ▸ hcyc₀
  have hratE : (DivisionRing.toRatAlgebra : Algebra ℚ E) = E.algebra' := Subsingleton.elim _ _
  have hgal : IsGalois ℚ E := hratE ▸ hgal₀
  have hcyclic : IsCyclic Gal(E/ℚ) := hratE ▸ hcyclic₀
  refine ⟨k, F, hk, hcyc, hUnion, E, hgal, hcyclic, hcomplex, ?_⟩
  intro p hp w hw
  have hd := hDegree p hp w hw
  rw [hratE] at hd
  exact hd

end
end Dubon2026

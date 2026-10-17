import Dubon2026.TwoPowerCyclotomicComplexSubfield
import Dubon2026.OriginalIndexTwoDecompositionDegree
import Dubon2026.CyclotomicHigherLocalDegreeStage

/-! # Completion degrees in the actual cyclic two-power subfield

The original cyclotomic local-degree theorem works at the prime two.
Applying it with one extra power and restricting actual prime stabilizers
supplies the required completion degrees in the totally complex cyclic
subfield. This discharges the local-degree loss in DUB-17's two-primary
splitting route without a new theory of completed scalar towers.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField
attribute [-instance] UniformSpace.Completion.instSMul

/-- A sufficiently large actual two-power cyclotomic extension has a
totally complex cyclic subfield retaining the prescribed local degrees. -/
theorem originalTwoPowerCyclotomic_exists_cyclic_localDegree_subfield
    (k r : ℕ) (hk : r + 2 ≤ k)
    (L : Type) [Field L] [NumberField L]
    [IsCyclotomicExtension {2 ^ (k + 1)} ℚ L] :
    ∃ E : IntermediateField ℚ L,
      IsGalois ℚ E ∧ IsCyclic Gal(E/ℚ) ∧ IsTotallyComplex E ∧
      Module.finrank E L ≤ 2 ∧
      ∀ (p : ℕ) [Fact p.Prime],
        (p ≠ 2 → p ^ (2 ^ (r + 1) * (2 - 1)) - 1 < 2 ^ (k + 1)) →
        ∀ (w : HeightOneSpectrum (𝓞 E)),
          w.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) →
          let v := originalFinitePrimeBelow ℚ E w
          letI := originalFinitePrimeBelow_liesOver ℚ E w
          letI : Algebra (v.adicCompletion ℚ) (w.adicCompletion E) :=
            (originalAdicBaseChangeMap ℚ E v w).toAlgebra
          2 ^ (r + 1) ∣ Module.finrank (v.adicCompletion ℚ) (w.adicCompletion E) := by
  letI : IsGalois ℚ L := IsCyclotomicExtension.isGalois {2 ^ (k + 1)} ℚ L
  have he : k + 1 = (k - 2) + 3 := by omega
  have hc : IsCyclotomicExtension {2 ^ ((k - 2) + 3)} ℚ L := by
    rw [← he]
    infer_instance
  letI := hc
  obtain ⟨E, hgal, hcyclic, hdegree, hcomplex⟩ :=
    originalTwoPowerCyclotomic_exists_complex_cyclic_subfield ℚ L (k - 2)
  letI := hgal
  letI : NumberField E := NumberField.of_module_finite ℚ E
  have hrat : (E.algebra' : Algebra ℚ E) = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  letI : @IsGalois ℚ _ E _ DivisionRing.toRatAlgebra := hrat ▸ hgal
  refine ⟨E, hgal, hcyclic, hcomplex, hdegree, ?_⟩
  intro p hp hlarge w hw
  obtain ⟨t, ht⟩ := originalFinitePrimeBelow_surjective E L w
  letI : t.asIdeal.LiesOver w.asIdeal := by
    rw [← ht]
    exact originalFinitePrimeBelow_liesOver E L t
  letI : w.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := hw
  letI : t.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) :=
    Ideal.LiesOver.trans t.asIdeal w.asIdeal (Ideal.span {(p : ℤ)})
  let v := originalFinitePrimeBelow ℚ E w
  letI := originalFinitePrimeBelow_liesOver ℚ E w
  letI : Algebra (v.adicCompletion ℚ) (w.adicCompletion E) :=
    (originalAdicBaseChangeMap ℚ E v w).toAlgebra
  change 2 ^ (r + 1) ∣ Module.finrank (v.adicCompletion ℚ) (w.adicCompletion E)
  rw [originalAdicBaseChange_finrank_eq_decomposition_card ℚ E v w]
  rw [← ht]
  apply originalFiniteDecomposition_two_power_divisibility ℚ L E hdegree t (r + 1)
  have htop := cyclotomicPrimePower_higher_completion_degree_dvd 2 k (r + 1) L hk p hlarge t
  let u := originalFinitePrimeBelow ℚ L t
  letI := originalFinitePrimeBelow_liesOver ℚ L t
  letI : Algebra (u.adicCompletion ℚ) (t.adicCompletion L) :=
    (originalAdicBaseChangeMap ℚ L u t).toAlgebra
  change 2 ^ ((r + 1) + 1) ∣ Module.finrank (u.adicCompletion ℚ) (t.adicCompletion L) at htop
  rwa [originalAdicBaseChange_finrank_eq_decomposition_card ℚ L u t] at htop

end
end Dubon2026

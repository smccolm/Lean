import Dubon2026.ChebotarevFiniteFactorPrime
import Dubon2026.NumberFieldLargeResiduePrime
import Dubon2026.OriginalIntegerPrimeTower

/-! # Prescribed Frobenius with a large original residue characteristic

The source auxiliary prime in BLGG 3.6.1 must satisfy both Frobenius
conditions and the size restriction used for unitary smallness. Excluding
the finitely many original primes above bounded rational primes lets the
already proved Chebotarev theorem supply these conditions simultaneously.
This serves DUB-17's source unitary auxiliary module construction.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField

/-- The original finite places of bounded rational residue characteristic form a finite set. -/
theorem numberField_finite_small_residue_primes
    (K : Type*) [Field K] [NumberField K] (B : ℕ) :
    {v : HeightOneSpectrum (𝓞 K) | ∃ p : ℕ, p.Prime ∧ p ≤ B ∧
      v.asIdeal.LiesOver (Ideal.span {(p : ℤ)})}.Finite := by
  classical
  let P := (Finset.range (B + 1)).filter Nat.Prime
  let S : Finset (HeightOneSpectrum ℤ) := P.attach.image fun p =>
    rationalPrimePlace p.val (Finset.mem_filter.mp p.property).2
  apply (heightOneUnder_preimage_finite (A := ℤ) (B := 𝓞 K)
    (S : Set (HeightOneSpectrum ℤ)) S.finite_toSet).subset
  rintro v ⟨p, hp, hpB, hlie⟩
  have hpP : p ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp⟩
  have hv : v.under ℤ = rationalPrimePlace p hp := by
    by_contra h
    apply rationalPrimePlace_prime_not_mem p hp (v.under ℤ) h
    change (p : ℤ) ∈ v.asIdeal.under ℤ
    rw [← hlie.over]
    exact Ideal.subset_span (Set.mem_singleton _)
  change v.under ℤ ∈ S
  rw [hv]
  exact Finset.mem_image.mpr ⟨⟨p, hpP⟩, Finset.mem_attach _ _, rfl⟩

/-- The actual finite Galois factor has every prescribed Frobenius class at arbitrarily large original residue primes, avoiding any specified finite set of places. -/
theorem continuous_galois_exists_large_frobenius_prime
    {K : Type} {Ω T : Type*} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    [IsGalois K Ω] [Group T] [TopologicalSpace T] [DiscreteTopology T]
    (χ : Gal(Ω/K) →ₜ* T) :
    ∃ F : FiniteGaloisIntermediateField K Ω, ∃ ψ : Gal(F/K) →* T,
      (∀ g : Gal(Ω/K), ψ (AlgEquiv.restrictNormalHom F g) = χ g) ∧
      (letI : NumberField F := NumberField.of_module_finite K F
       ∀ (g : Gal(Ω/K)) (S : Finset (Ideal (𝓞 K))) (B : ℕ),
         ∃ (v : HeightOneSpectrum (𝓞 K)) (p : ℕ),
           v.asIdeal ∉ S ∧ p.Prime ∧ B < p - 1 ∧
           CharP (Valued.ResidueField (v.adicCompletion K)) p ∧
           Chebotarev.UnramifiedIn K F v.asIdeal ∧
           Chebotarev.frobeniusClass K F v.asIdeal =
             ConjClasses.mk (AlgEquiv.restrictNormalHom F g) ∧
           IsConj (ψ (Chebotarev.frobeniusClass K F v.asIdeal).out) (χ g)) := by
  classical
  obtain ⟨F, ψ, hψ, hF⟩ := continuous_galois_exists_frobenius_prime χ
  refine ⟨F, ψ, hψ, ?_⟩
  letI : NumberField F := NumberField.of_module_finite K F
  intro g S B
  let bad := numberField_finite_small_residue_primes K (B + 1)
  obtain ⟨a, haS, ha, hur, hc, hconj⟩ := hF g
    (S ∪ bad.toFinset.image HeightOneSpectrum.asIdeal)
  let v : HeightOneSpectrum (𝓞 K) := ⟨a, ha, hur.1⟩
  obtain ⟨p, hp, hlie⟩ := originalIntegerPrimeBelow_exists_prime K v
  have hlarge : B < p - 1 := by
    by_contra h
    have hv : v ∈ bad.toFinset := bad.mem_toFinset.mpr ⟨p, hp, by omega, hlie⟩
    exact haS (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨v, hv, rfl⟩))
  have hmem : (p : 𝓞 K) ∈ a := by
    haveI := hlie
    simpa only [map_natCast] using (Ideal.mem_of_liesOver a (Ideal.span {(p : ℤ)}) (p : ℤ)).mp
      (Ideal.subset_span (Set.mem_singleton _))
  exact ⟨v, p, fun h => haS (Finset.mem_union_left _ h), hp, hlarge,
    originalAdicResidue_charP_of_prime_mem K v p hp hmem, hur, hc, hconj⟩

end
end Dubon2026

import Dubon2026.NumberFieldLargeFrobeniusPrime
import Dubon2026.NumberFieldCyclotomicDegreeLowerBound
import Mathlib.NumberTheory.Cyclotomic.Basic

/-! # Simultaneous source conditions on the unitary smallness prime

BLGG 3.6.1 chooses a prime where the residual adjoint Frobenius is trivial
and the cyclotomic Frobenius is nontrivial. Their kernel noncontainment
supplies the required Galois element. Existing Chebotarev, finite absolute
ramification, and the cyclotomic degree bound then supply all the prime
conditions simultaneously. The actual residual modular representation
and its source kernel noncontainment remain separate DUB-17 obligations.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField

/-- Kernel noncontainment gives source auxiliary Frobenius primes with trivial first image, nontrivial second image, absolute unramifiedness and the required cyclotomic degree. -/
theorem continuous_galois_exists_smallness_frobenius_prime
    {K : Type} {Ω A C : Type*} [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsGalois K Ω]
    [Group A] [TopologicalSpace A] [DiscreteTopology A]
    [Group C] [TopologicalSpace C] [DiscreteTopology C]
    (ρ : Gal(Ω/K) →ₜ* A) (χ : Gal(Ω/K) →ₜ* C)
    (hker : ¬ ρ.toMonoidHom.ker ≤ χ.toMonoidHom.ker) :
    ∃ F : FiniteGaloisIntermediateField K Ω, ∃ ψ : Gal(F/K) →* A × C,
      (∀ g : Gal(Ω/K), ψ (AlgEquiv.restrictNormalHom F g) = (ρ g, χ g)) ∧
      (letI : NumberField F := NumberField.of_module_finite K F
       ∀ (S : Finset (Ideal (𝓞 K))) (n : ℕ),
         ∃ (v : HeightOneSpectrum (𝓞 K)) (p : ℕ),
           v.asIdeal ∉ S ∧ p.Prime ∧ n * Module.finrank ℚ K < p - 1 ∧
           CharP (Valued.ResidueField (v.adicCompletion K)) p ∧
           Algebra.IsUnramifiedAt ℤ v.asIdeal ∧
           Chebotarev.UnramifiedIn K F v.asIdeal ∧
           (ψ (Chebotarev.frobeniusClass K F v.asIdeal).out).1 = 1 ∧
           (ψ (Chebotarev.frobeniusClass K F v.asIdeal).out).2 ≠ 1 ∧
           n < Module.finrank K (CyclotomicField p K)) := by
  classical
  obtain ⟨g, hg, hc⟩ : ∃ g : Gal(Ω/K), ρ g = 1 ∧ χ g ≠ 1 := by
    by_contra h
    apply hker
    intro g hg
    exact not_not.mp fun hc => h ⟨g, hg, hc⟩
  obtain ⟨F, ψ, hψ, hF⟩ := continuous_galois_exists_large_frobenius_prime (ρ.prod χ)
  refine ⟨F, ψ, hψ, ?_⟩
  letI : NumberField F := NumberField.of_module_finite K F
  intro S n
  let bad := original_finite_absolutely_ramified_places K
  obtain ⟨v, p, hv, hp, hlarge, hchar, hur, _, hconj⟩ :=
    hF g (S ∪ bad.toFinset.image HeightOneSpectrum.asIdeal) (n * Module.finrank ℚ K)
  have hvabs : Algebra.IsUnramifiedAt ℤ v.asIdeal := by
    by_contra h
    exact hv (Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨v, bad.mem_toFinset.mpr h, rfl⟩))
  have hfst := (MonoidHom.fst A C).map_isConj hconj
  have hsnd := (MonoidHom.snd A C).map_isConj hconj
  change IsConj _ (ρ g) at hfst
  change IsConj (ψ (Chebotarev.frobeniusClass K F v.asIdeal).out).2 (χ g) at hsnd
  rw [hg] at hfst
  have hsndne : (ψ (Chebotarev.frobeniusClass K F v.asIdeal).out).2 ≠ 1 := by
    intro he
    rw [he] at hsnd
    exact hc (isConj_one_right.mp hsnd)
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI := IsCyclotomicExtension.finiteDimensional {p} K (CyclotomicField p K)
  letI : NumberField (CyclotomicField p K) := NumberField.of_module_finite K _
  exact ⟨v, p, fun h => hv (Finset.mem_union_left _ h), hp, hlarge, hchar, hvabs,
    hur, isConj_one_left.mp hfst, hsndne,
    numberField_cyclotomic_degree_gt K (CyclotomicField p K) p n hp hlarge
      (IsCyclotomicExtension.zeta p K (CyclotomicField p K))
      (IsCyclotomicExtension.zeta_spec p K (CyclotomicField p K))⟩

end
end Dubon2026

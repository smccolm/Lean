import Dubon2026.ChebotarevCyclotomicPrimes
import Dubon2026.ContinuousCyclotomicFiniteFactor

/-! Actual continuous-representation auxiliary primes with the required
cyclotomic congruence. The finite factor and its primitive root are constructed
using native proofs. Residual regularity and dual-class detection are the next
conditions in the DUB-17 arithmetic patching dependency. -/

namespace Dubon2026
noncomputable section
open scoped NumberField

/-- Use the original finite intermediate field algebra over the rationals. -/
local instance cyclotomicPrimeFiniteFieldAlgebra
    {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    (F : FiniteGaloisIntermediateField ℚ Ω) : Algebra ℚ F := F.algebra'

/-- The actual continuous representation factors through a constructed finite
field containing the specified root. Every original Galois element fixing that
root is realized by the image of Frobenius at a new prime congruent to one
modulo the root order. -/
theorem continuous_rational_galois_exists_cyclotomic_frobenius_prime
    {Ω T : Type} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω]
    [Group T] [TopologicalSpace T] [DiscreteTopology T]
    (χ : Gal(Ω/ℚ) →ₜ* T) {m : ℕ} [NeZero m]
    {ζ : Ω} (hζ : IsPrimitiveRoot ζ m) :
    ∃ F : FiniteGaloisIntermediateField ℚ Ω, ζ ∈ F.toIntermediateField ∧
      ∃ ψ : Gal(F/ℚ) →* T,
        (∀ g : Gal(Ω/ℚ), ψ (AlgEquiv.restrictNormalHom F g) = χ g) ∧
        (letI : NumberField F := NumberField.of_module_finite ℚ F
         ∀ (g : Gal(Ω/ℚ)), g ζ = ζ → ∀ S : Finset ℕ,
           ∃ p : ℕ, p.Prime ∧ p ∉ S ∧ p ≡ 1 [MOD m] ∧
             Chebotarev.UnramifiedIn ℚ F (Ideal.span {(p : 𝓞 ℚ)}) ∧
             Chebotarev.frobeniusClass ℚ F (Ideal.span {(p : 𝓞 ℚ)}) =
               ConjClasses.mk (AlgEquiv.restrictNormalHom F g) ∧
             IsConj (ψ (Chebotarev.frobeniusClass ℚ F
               (Ideal.span {(p : 𝓞 ℚ)})).out) (χ g)) := by
  obtain ⟨F, hmem, ψ, hψ⟩ := continuous_galois_finite_factor_with_root χ hζ
  refine ⟨F, hmem, ψ, hψ, ?_⟩
  letI : NumberField F := NumberField.of_module_finite ℚ F
  let μ : F := ⟨ζ, hmem⟩
  have hμ : IsPrimitiveRoot μ m :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap F Ω) hζ
      (FaithfulSMul.algebraMap_injective F Ω)
  intro g hg S
  have hfix : AlgEquiv.restrictNormalHom F g μ = μ := by
    apply Subtype.ext
    rw [AlgEquiv.restrictNormalHom_apply]
    exact hg
  obtain ⟨p, hp, hpS, hmod, hur, hclass⟩ :=
    finiteGalois_exists_prime_congruent_one_of_fixed_root F hμ
      (AlgEquiv.restrictNormalHom F g) hfix S
  refine ⟨p, hp, hpS, hmod, hur, hclass, ?_⟩
  have hconj : IsConj
      (Chebotarev.frobeniusClass ℚ F (Ideal.span {(p : 𝓞 ℚ)})).out
      (AlgEquiv.restrictNormalHom F g) := by
    apply ConjClasses.mk_eq_mk_iff_isConj.mp
    exact (Quotient.out_eq _).trans hclass
  simpa only [hψ] using ψ.map_isConj hconj

end
end Dubon2026

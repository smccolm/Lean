import Dubon2026.ChebotarevFiniteFactorPrime
import Dubon2026.OriginalIntegerPrimeTower
import Mathlib.NumberTheory.Padics.HeightOneSpectrum

/-! Prescribed Frobenius at genuine rational primes for DUB-17's auxiliary-prime
construction. The native classification of original places supplies the prime
integer; the original continuous representation supplies its finite factor.
No residual image or dual Selmer detection condition is asserted. -/

namespace Dubon2026
noncomputable section
open scoped NumberField

/-- Keep the literal finite intermediate-field algebra when specializing to the rationals. -/
local instance rationalChebotarevFiniteFieldAlgebra
    {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    (F : FiniteGaloisIntermediateField ℚ Ω) : Algebra ℚ F := F.algebra'

/-- The native integer-prime classification identifies a nonzero prime ideal
of the actual ring of integers of the rationals with its rational generator. -/
theorem rationalNonzeroPrime_eq_span (v : Ideal (𝓞 ℚ))
    (hv : v.IsPrime) (hne : v ≠ ⊥) :
    ∃ p : ℕ, p.Prime ∧ v = Ideal.span {(p : 𝓞 ℚ)} := by
  obtain ⟨p, hp, hwp⟩ := originalIntegerPrimeBelow_exists_prime ℚ ⟨v, hv, hne⟩
  refine ⟨p, hp, ?_⟩
  have he : v = (v.under ℤ).map (algebraMap ℤ (𝓞 ℚ)) :=
    (Ideal.map_comap_of_surjective _ (Rat.int_algebraMap_surjective (𝓞 ℚ)) _).symm
  rw [he, ← hwp.over, Ideal.map_span, Set.image_singleton, map_natCast]

/-- Outside every specified finite set of integers, a genuine rational prime
has the prescribed Frobenius conjugacy class in the finite field constructed
from the original continuous Galois representation. -/
theorem continuous_rational_galois_exists_frobenius_prime
    {Ω T : Type*} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω]
    [Group T] [TopologicalSpace T] [DiscreteTopology T]
    (χ : Gal(Ω/ℚ) →ₜ* T) :
    ∃ F : FiniteGaloisIntermediateField ℚ Ω,
      ∃ ψ : Gal(F/ℚ) →* T,
        (∀ g : Gal(Ω/ℚ), ψ (AlgEquiv.restrictNormalHom F g) = χ g) ∧
        (letI : NumberField F := NumberField.of_module_finite ℚ F
         ∀ (g : Gal(Ω/ℚ)) (S : Finset ℕ),
           ∃ p : ℕ, p.Prime ∧ p ∉ S ∧
             Chebotarev.UnramifiedIn ℚ F (Ideal.span {(p : 𝓞 ℚ)}) ∧
             Chebotarev.frobeniusClass ℚ F (Ideal.span {(p : 𝓞 ℚ)}) =
               ConjClasses.mk (AlgEquiv.restrictNormalHom F g) ∧
             IsConj (ψ (Chebotarev.frobeniusClass ℚ F
               (Ideal.span {(p : 𝓞 ℚ)})).out) (χ g)) := by
  classical
  obtain ⟨F, ψ, hψ, hF⟩ := continuous_galois_exists_frobenius_prime χ
  refine ⟨F, ψ, hψ, ?_⟩
  letI : NumberField F := NumberField.of_module_finite ℚ F
  intro g S
  obtain ⟨v, hvS, hv, hur, hclass, hconj⟩ :=
    hF g (S.image fun p : ℕ => Ideal.span {(p : 𝓞 ℚ)})
  obtain ⟨p, hp, rfl⟩ := rationalNonzeroPrime_eq_span v hv hur.1
  exact ⟨p, hp, fun hpS => hvS (Finset.mem_image.mpr ⟨p, hpS, rfl⟩),
    hur, hclass, hconj⟩

end
end Dubon2026

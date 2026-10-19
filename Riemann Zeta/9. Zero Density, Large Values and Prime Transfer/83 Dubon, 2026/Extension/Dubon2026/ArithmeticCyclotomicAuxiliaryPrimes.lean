import Dubon2026.ContinuousCyclotomicFrobeniusPrimes
import Dubon2026.RationalArithmeticGaloisGroup
import Dubon2026.OriginalUnramifiedCyclotomicPowerRoots
import Dubon2026.RationalExceptionalPrimeFinite

/-! Prescribed auxiliary primes for the same arithmetic Galois group used by
the proved trace Selmer comparison. Native power-root existence and exceptional
prime finiteness discharge the root and bad-prime witnesses for every level.
This is the prime-selection branch of DUB-17 arithmetic patching; a suitable
residual-regular, dual-class-detecting Galois element is still required. -/

namespace Dubon2026
noncomputable section
open scoped NumberField

/-- Retain the literal rational algebra on a finite intermediate field. -/
local instance arithmeticAuxiliaryFiniteFieldAlgebra
    {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    (F : FiniteGaloisIntermediateField ℚ Ω) : Algebra ℚ F := F.algebra'

/-- For every power conductor supported on the original exceptional integer,
construct the actual primitive root, the finite representation factor, and
primes outside both the original exceptional support and an arbitrary finite
set. They have the required congruence and realize the prescribed image of
every original Galois element fixing that root. -/
theorem rationalArithmetic_exists_cyclotomic_auxiliary_prime
    (a : 𝓞 ℚ) (ha : a ≠ 0) (q n : ℕ) [NeZero q]
    (hqa : (q : 𝓞 ℚ) ∣ a)
    {T : Type} [Group T] [TopologicalSpace T] [DiscreteTopology T]
    (χ : rationalArithmeticGaloisGroup a →ₜ* T) :
    let U := rationalUnramifiedExtension a
    letI : Algebra ℚ U := U.algebra'
    letI : IsGalois ℚ U := originalUnramifiedGaloisUnion_isGalois a
    ∃ ζ : U, IsPrimitiveRoot ζ (q ^ n) ∧
      ∃ F : FiniteGaloisIntermediateField ℚ U, ζ ∈ F.toIntermediateField ∧
        ∃ ψ : Gal(F/ℚ) →* T,
          (∀ g : Gal(U/ℚ), ψ (AlgEquiv.restrictNormalHom F g) = χ g) ∧
          (letI : NumberField F := NumberField.of_module_finite ℚ F
           ∀ g : Gal(U/ℚ), g ζ = ζ → ∀ S : Finset ℕ,
             ∃ p : ℕ, p.Prime ∧ p ∉ S ∧ ¬ (p : 𝓞 ℚ) ∣ a ∧
               p ≡ 1 [MOD q ^ n] ∧
               Chebotarev.UnramifiedIn ℚ F (Ideal.span {(p : 𝓞 ℚ)}) ∧
               Chebotarev.frobeniusClass ℚ F (Ideal.span {(p : 𝓞 ℚ)}) =
                 ConjClasses.mk (AlgEquiv.restrictNormalHom F g) ∧
               IsConj (ψ (Chebotarev.frobeniusClass ℚ F
                 (Ideal.span {(p : 𝓞 ℚ)})).out) (χ g)) := by
  classical
  let U := rationalUnramifiedExtension a
  letI : Algebra ℚ U := U.algebra'
  letI : IsGalois ℚ U := originalUnramifiedGaloisUnion_isGalois a
  obtain ⟨ζ, hζ⟩ := originalQUnramifiedUnion_exists_powerRoot
    (Ω := AlgebraicClosure ℚ) a q n hqa
  obtain ⟨F, hmem, ψ, hψ, hF⟩ :=
    continuous_rational_galois_exists_cyclotomic_frobenius_prime
      (show Gal(U/ℚ) →ₜ* T from χ) hζ
  refine ⟨ζ, hζ, F, hmem, ψ, hψ, ?_⟩
  letI : NumberField F := NumberField.of_module_finite ℚ F
  intro g hg S
  let bad := (rationalExceptionalPrimeSet_finite a ha).toFinset
  obtain ⟨p, hp, hpS, hmod, hur, hclass, hconj⟩ :=
    hF g hg (S ∪ bad.image Subtype.val)
  refine ⟨p, hp, fun h => hpS (Finset.mem_union_left _ h), ?_,
    hmod, hur, hclass, hconj⟩
  intro hpa
  have hb : (⟨p, hp⟩ : Nat.Primes) ∈ bad :=
    (rationalExceptionalPrimeSet_finite a ha).mem_toFinset.mpr hpa
  exact hpS (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨⟨p, hp⟩, hb, rfl⟩))

end
end Dubon2026

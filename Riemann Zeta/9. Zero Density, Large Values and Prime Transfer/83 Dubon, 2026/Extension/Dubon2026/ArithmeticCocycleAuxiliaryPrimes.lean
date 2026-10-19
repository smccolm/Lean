import Dubon2026.ArithmeticCyclotomicAuxiliaryPrimes
import Dubon2026.ContinuousCocycleAffinePermutation
import Dubon2026.CocycleAffineH1Detection

/-! Select a single actual arithmetic prime retaining both the original
representation image and a non-coboundary cocycle test. The finite affine
permutation encoding avoids a second cohomology development on the DUB-17
dual Selmer detection chain. The detecting original element remains an input. -/

namespace Dubon2026
noncomputable section
open scoped NumberField

/-- The finite factor uses its literal rational algebra. -/
local instance cocycleAuxiliaryFiniteFieldAlgebra
    {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    (F : FiniteGaloisIntermediateField ℚ Ω) : Algebra ℚ F := F.algebra'

/-- The same chosen arithmetic prime retains a prescribed representation image,
the prime-power cyclotomic congruence, and the affine non-fixed-point test of
the original continuous cocycle. All finite fields, primitive roots and
excluded bad-prime sets are constructed from the original data. -/
theorem rationalArithmetic_exists_cocycle_auxiliary_prime
    (a : 𝓞 ℚ) (ha : a ≠ 0) (q n : ℕ) [NeZero q]
    (hqa : (q : 𝓞 ℚ) ∣ a)
    {R T : Type} [CommRing R] [TopologicalSpace R]
    [Group T] [TopologicalSpace T] [DiscreteTopology T]
    (A : Rep.{0} R (rationalArithmeticGaloisGroup a))
    [Finite A] [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul R A]
    (hA : Continuous (fun z : rationalArithmeticGaloisGroup a × A => A.ρ z.1 z.2))
    (χ : rationalArithmeticGaloisGroup a →ₜ* T)
    (c : continuousRepresentationCocyclesOne A) :
    let U := rationalUnramifiedExtension a
    letI : Algebra ℚ U := U.algebra'
    letI : IsGalois ℚ U := originalUnramifiedGaloisUnion_isGalois a
    ∃ ζ : U, IsPrimitiveRoot ζ (q ^ n) ∧
      ∃ F : FiniteGaloisIntermediateField ℚ U, ζ ∈ F.toIntermediateField ∧
        ∃ ψ : Gal(F/ℚ) →* T × Equiv.Perm A,
          (∀ g : Gal(U/ℚ), ψ (AlgEquiv.restrictNormalHom F g) =
            (χ g, cocycleAffinePermutation A c.val g)) ∧
          (letI : NumberField F := NumberField.of_module_finite ℚ F
           ∀ g : Gal(U/ℚ), g ζ = ζ →
             c.val g ∉ LinearMap.range (A.ρ g - 1) → ∀ S : Finset ℕ,
             ∃ p : ℕ, p.Prime ∧ p ∉ S ∧ ¬ (p : 𝓞 ℚ) ∣ a ∧
               p ≡ 1 [MOD q ^ n] ∧
               Chebotarev.UnramifiedIn ℚ F (Ideal.span {(p : 𝓞 ℚ)}) ∧
               Chebotarev.frobeniusClass ℚ F (Ideal.span {(p : 𝓞 ℚ)}) =
                 ConjClasses.mk (AlgEquiv.restrictNormalHom F g) ∧
               IsConj (ψ (Chebotarev.frobeniusClass ℚ F
                 (Ideal.span {(p : 𝓞 ℚ)})).out).1 (χ g) ∧
               ¬ ∃ x : A, (ψ (Chebotarev.frobeniusClass ℚ F
                 (Ideal.span {(p : 𝓞 ℚ)})).out).2 x = x) := by
  letI : TopologicalSpace (Equiv.Perm A) := ⊥
  letI : DiscreteTopology (Equiv.Perm A) := ⟨rfl⟩
  let α : rationalArithmeticGaloisGroup a →ₜ* Equiv.Perm A :=
    ⟨cocycleAffinePermutation A c.val, continuousCocycleAffinePermutation_continuous A hA c⟩
  obtain ⟨ζ, hζ, F, hmem, ψ, hψ, hF⟩ :=
    rationalArithmetic_exists_cyclotomic_auxiliary_prime a ha q n hqa (χ.prod α)
  let U := rationalUnramifiedExtension a
  letI : Algebra ℚ U := U.algebra'
  letI : IsGalois ℚ U := originalUnramifiedGaloisUnion_isGalois a
  refine ⟨ζ, hζ, F, hmem, ψ, hψ, ?_⟩
  letI : NumberField F := NumberField.of_module_finite ℚ F
  intro g hg hc S
  obtain ⟨p, hp, hpS, hpa, hmod, hur, hclass, hconj⟩ := hF g hg S
  refine ⟨p, hp, hpS, hpa, hmod, hur, hclass,
    (MonoidHom.fst T (Equiv.Perm A)).map_isConj hconj, ?_⟩
  intro hfixed
  have hsecond := (MonoidHom.snd T (Equiv.Perm A)).map_isConj hconj
  have hfixed' : ∃ x : A, cocycleAffinePermutation A c.val g x = x :=
    (permutation_isConj_exists_fixed_iff hsecond).mp hfixed
  exact hc ((cocycleAffinePermutation_exists_fixed_iff A c.val g).mp hfixed')

end
end Dubon2026

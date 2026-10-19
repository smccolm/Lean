import Dubon2026.ArithmeticCocycleLocalDetection
import Dubon2026.CocycleKernelTranslateDetection

/-! Actual auxiliary primes from the kernel-functional step of dual Selmer
detection. The native prime consumer is applied to the constructed detecting
element, retaining the exact two possible original representation images.
The residual-image theory must still produce the kernel value and functional;
this file does not assert their existence or arbitrary-rank adequacy. -/

namespace Dubon2026
noncomputable section
open scoped NumberField

/-- The original invariant functional and nonzero kernel-cocycle pairing
produce a good congruence prime detecting the same original H1 class.
The final image is conjugate to the specified original element or its
literal kernel translate, allowing the residual regularity check to use
those two concrete alternatives. -/
theorem rationalArithmetic_exists_prime_detecting_kernel_functional
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
      ∀ g τ : Gal(U/ℚ), g ζ = ζ → τ ζ = ζ → A.ρ τ = 1 →
        ∀ ℓ : A →ₗ[R] R, (∀ x : A, ℓ (A.ρ g x) = ℓ x) → ℓ (c.val τ) ≠ 0 →
          ∀ S : Finset ℕ, ∃ p : ℕ, ∃ hp : p.Prime,
            p ∉ S ∧ ¬ (p : 𝓞 ℚ) ∣ a ∧ p ≡ 1 [MOD q ^ n] ∧
            (∃ γ : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp),
              IsConj (χ (rationalPrimeArithmeticRestriction a p hp γ)) (χ g) ∨
              IsConj (χ (rationalPrimeArithmeticRestriction a p hp γ)) (χ (τ * g))) ∧
            rationalArithmeticH1PrimeRestriction a A hA p hp (Submodule.Quotient.mk c) ≠ 0 := by
  let U := rationalUnramifiedExtension a
  letI : Algebra ℚ U := U.algebra'
  letI : IsGalois ℚ U := originalUnramifiedGaloisUnion_isGalois a
  have hprimes := rationalArithmetic_exists_prime_detecting_cocycle a ha q n hqa A hA χ c
  obtain ⟨ζ, hζ, hF⟩ := hprimes
  refine ⟨ζ, hζ, ?_⟩
  intro g τ hg hτ hρτ ℓ hℓ hc S
  let H : Subgroup (rationalArithmeticGaloisGroup a) := MulAction.stabilizer Gal(U/ℚ) ζ
  have hgH : g ∈ H := MulAction.mem_stabilizer_iff.mpr hg
  have hτH : τ ∈ H := MulAction.mem_stabilizer_iff.mpr hτ
  have hdetect := cocycle_exists_detecting_of_kernel_functional A c.val H g τ hgH hτH hρτ
  have hdetect' := hdetect ℓ hℓ hc
  obtain ⟨σ, hσH, hσ, hcσ⟩ := hdetect'
  have hσζ : (show Gal(U/ℚ) from σ) ζ = ζ := by
    change (show Gal(U/ℚ) from σ) ∈ MulAction.stabilizer Gal(U/ℚ) ζ at hσH
    exact MulAction.mem_stabilizer_iff.mp hσH
  have hselected := hF σ hσζ hcσ S
  obtain ⟨p, hp, hpS, hpa, hmod, ⟨γ, hγ⟩, hne⟩ := hselected
  refine ⟨p, hp, hpS, hpa, hmod, ⟨γ, ?_⟩, hne⟩
  rcases hσ with hσ | hσ
  · exact Or.inl (hσ ▸ hγ)
  · exact Or.inr (hσ ▸ hγ)

end
end Dubon2026

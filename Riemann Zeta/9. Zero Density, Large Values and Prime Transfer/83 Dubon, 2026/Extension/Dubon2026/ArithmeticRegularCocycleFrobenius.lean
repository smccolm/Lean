import Dubon2026.ArithmeticSymmetricRegularPrimes
import Dubon2026.ArithmeticCocycleLocalDetection

/-! Preserve the literal finite Frobenius class when combining regular
residual images with detection of the original continuous cohomology class.
This serves DUB-17 auxiliary-prime selection before arithmetic patching. -/

namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance] rationalArithmeticOriginalFiniteGalois

/-- The finite affine factor detects native local H1, while the same
original completion Frobenius has a separable residual characteristic
polynomial. Its finite Frobenius equality is part of the conclusion. -/
theorem rationalArithmetic_local_regular_detection_of_finite_factor
    (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)
    {K ι : Type} [Field K] [TopologicalSpace K] [Fintype ι] [DecidableEq ι]
    (A : Rep.{0} K (rationalArithmeticGaloisGroup a))
    [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul K A]
    (hA : Continuous (fun z : rationalArithmeticGaloisGroup a × A => A.ρ z.1 z.2))
    (ρ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup ι K)
    (c : continuousRepresentationCocyclesOne A)
    (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    (ψ : Gal(F/ℚ) →* Matrix.GeneralLinearGroup ι K × Equiv.Perm A)
    (hψ : ∀ g : rationalArithmeticGaloisGroup a,
      ψ (AlgEquiv.restrictNormalHom F g) = (ρ g, cocycleAffinePermutation A c.val g))
    (hunr : letI : NumberField F := NumberField.of_module_finite ℚ F
      Chebotarev.UnramifiedIn ℚ F (Ideal.span {(p : 𝓞 ℚ)}))
    (hfixed : letI : NumberField F := NumberField.of_module_finite ℚ F
      ¬ ∃ x : A, (ψ (Chebotarev.frobeniusClass ℚ F (Ideal.span {(p : 𝓞 ℚ)})).out).2 x = x)
    (hregular : letI : NumberField F := NumberField.of_module_finite ℚ F
      (ψ (Chebotarev.frobeniusClass ℚ F (Ideal.span {(p : 𝓞 ℚ)})).out).1.val.charpoly.Separable) :
    letI : NumberField F := NumberField.of_module_finite ℚ F
    (∃ γ : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp),
      Chebotarev.frobeniusClass ℚ F (Ideal.span {(p : 𝓞 ℚ)}) =
        ConjClasses.mk (AlgEquiv.restrictNormalHom F (rationalPrimeArithmeticRestriction a p hp γ)) ∧
      (ρ (rationalPrimeArithmeticRestriction a p hp γ)).val.charpoly.Separable) ∧
    rationalArithmeticH1PrimeRestriction a A hA p hp (Submodule.Quotient.mk c) ≠ 0 := by
  letI : NumberField F := NumberField.of_module_finite ℚ F
  have hd := rationalArithmetic_local_detection_of_finite_factor a p hp A hA ρ c F
  have hd' := hd ψ hψ hunr hfixed
  have hlift := rationalArithmetic_exists_local_frobenius a p hp F
  have hlift' := hlift hunr
  obtain ⟨γ, hγ⟩ := hlift'
  have hc : IsConj (Chebotarev.frobeniusClass ℚ F (Ideal.span {(p : 𝓞 ℚ)})).out
      (AlgEquiv.restrictNormalHom F (rationalPrimeArithmeticRestriction a p hp γ)) := by
    apply ConjClasses.mk_eq_mk_iff_isConj.mp
    exact (Quotient.out_eq _).trans hγ
  have hpair := ψ.map_isConj hc
  rw [hψ] at hpair
  have hfirst := (MonoidHom.fst (Matrix.GeneralLinearGroup ι K) (Equiv.Perm A)).map_isConj hpair
  change IsConj (ψ (Chebotarev.frobeniusClass ℚ F
    (Ideal.span {(p : 𝓞 ℚ)})).out).1 (ρ (rationalPrimeArithmeticRestriction a p hp γ)) at hfirst
  refine ⟨⟨γ, hγ, ?_⟩, hd'.2⟩
  rw [← generalLinearGroup_charpoly_eq_of_isConj hfirst]
  exact hregular

/-- A regular original residual element that detects the cocycle yields
good congruence primes with regular actual Frobenius and nonzero native
H1 localization. The constructed common finite factor is retained. -/
theorem rationalArithmetic_exists_regular_detecting_cocycle
    (a : 𝓞 ℚ) (ha : a ≠ 0) (q n : ℕ) [NeZero q]
    (hqa : (q : 𝓞 ℚ) ∣ a)
    {K ι : Type} [Field K] [TopologicalSpace K] [DiscreteTopology K]
    [Fintype ι] [DecidableEq ι]
    (A : Rep.{0} K (rationalArithmeticGaloisGroup a))
    [Finite A] [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul K A]
    (hA : Continuous (fun z : rationalArithmeticGaloisGroup a × A => A.ρ z.1 z.2))
    (ρ : rationalArithmeticGaloisGroup a →ₜ* Matrix.GeneralLinearGroup ι K)
    (c : continuousRepresentationCocyclesOne A) :
    let U := rationalUnramifiedExtension a
    letI : Algebra ℚ U := U.algebra'
    letI : IsGalois ℚ U := originalUnramifiedGaloisUnion_isGalois a
    ∃ ζ : U, IsPrimitiveRoot ζ (q ^ n) ∧
      ∃ F : FiniteGaloisIntermediateField ℚ U,
        ∃ ψ : Gal(F/ℚ) →* Matrix.GeneralLinearGroup ι K × Equiv.Perm A,
          (∀ g : Gal(U/ℚ), ψ (AlgEquiv.restrictNormalHom F g) =
            (ρ g, cocycleAffinePermutation A c.val g)) ∧
          (letI : NumberField F := NumberField.of_module_finite ℚ F
           ∀ g : Gal(U/ℚ), g ζ = ζ →
             c.val g ∉ LinearMap.range (A.ρ g - 1) → (ρ g).val.charpoly.Separable →
             ∀ S : Finset ℕ, ∃ p : ℕ, ∃ hp : p.Prime,
               p ∉ S ∧ ¬ (p : 𝓞 ℚ) ∣ a ∧ p ≡ 1 [MOD q ^ n] ∧
               Chebotarev.UnramifiedIn ℚ F (Ideal.span {(p : 𝓞 ℚ)}) ∧
               (∃ γ : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp),
                 Chebotarev.frobeniusClass ℚ F (Ideal.span {(p : 𝓞 ℚ)}) =
                   ConjClasses.mk (AlgEquiv.restrictNormalHom F
                     (rationalPrimeArithmeticRestriction a p hp γ)) ∧
                 (ρ (rationalPrimeArithmeticRestriction a p hp γ)).val.charpoly.Separable) ∧
               rationalArithmeticH1PrimeRestriction a A hA p hp (Submodule.Quotient.mk c) ≠ 0) := by
  let U := rationalUnramifiedExtension a
  letI : Algebra ℚ U := U.algebra'
  letI : IsGalois ℚ U := originalUnramifiedGaloisUnion_isGalois a
  have hprimes := rationalArithmetic_exists_cocycle_auxiliary_prime a ha q n hqa A hA ρ c
  obtain ⟨ζ, hζ, F, _, ψ, hψ, hF⟩ := hprimes
  letI : Algebra ℚ F := F.algebra'
  letI : NumberField F := NumberField.of_module_finite ℚ F
  refine ⟨ζ, hζ, F, ψ, hψ, ?_⟩
  intro g hg hc hregular S
  have hselected := hF g hg hc S
  obtain ⟨p, hp, hpS, hpa, hmod, hunr, _, hconj, hfixed⟩ := hselected
  have hr : (ψ (Chebotarev.frobeniusClass ℚ F
      (Ideal.span {(p : 𝓞 ℚ)})).out).1.val.charpoly.Separable := by
    rw [generalLinearGroup_charpoly_eq_of_isConj hconj]
    exact hregular
  have hd := rationalArithmetic_local_regular_detection_of_finite_factor a p hp A hA
    ρ.toMonoidHom c F
  have hd' := hd ψ hψ hunr hfixed hr
  exact ⟨p, hp, hpS, hpa, hmod, hunr, hd'.1, hd'.2⟩

end
end Dubon2026

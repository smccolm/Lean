import Dubon2026.ArithmeticCocycleAuxiliaryPrimes
import Dubon2026.RationalArithmeticFrobeniusLift

/-! The prescribed actual prime detects the original continuous H1 class
through its original prime-local arithmetic restriction. This is the
DUB-17 detection step preceding finite dual-Selmer prime selection; an
original element with the non-coboundary test is still required. -/

namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance] rationalArithmeticOriginalFiniteGalois

/-- The actual continuous H1 localization at the original rational prime,
using the already constructed arithmetic restriction and coefficient module. -/
def rationalArithmeticH1PrimeRestriction
    (a : 𝓞 ℚ) {R : Type} [CommRing R] [TopologicalSpace R]
    (A : Rep.{0} R (rationalArithmeticGaloisGroup a))
    [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul R A]
    (hA : Continuous (fun z : rationalArithmeticGaloisGroup a × A => A.ρ z.1 z.2))
    (p : ℕ) (hp : p.Prime) :=
  continuousRepresentationH1Restriction A hA
    (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
    (rationalPrimeArithmeticRestriction a p hp).continuous

/-- The finite affine factor and the actual unramified Frobenius class
detect the original continuous local H1 restriction. The literal local
representative is constructed by the native completion comparison. -/
theorem rationalArithmetic_local_detection_of_finite_factor
    (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)
    {R T : Type} [CommRing R] [TopologicalSpace R] [Group T]
    (A : Rep.{0} R (rationalArithmeticGaloisGroup a))
    [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul R A]
    (hA : Continuous (fun z : rationalArithmeticGaloisGroup a × A => A.ρ z.1 z.2))
    (χ : rationalArithmeticGaloisGroup a →* T)
    (c : continuousRepresentationCocyclesOne A)
    (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    (ψ : Gal(F/ℚ) →* T × Equiv.Perm A)
    (hψ : ∀ g : rationalArithmeticGaloisGroup a,
      ψ (AlgEquiv.restrictNormalHom F g) = (χ g, cocycleAffinePermutation A c.val g))
    (hunr : letI : NumberField F := NumberField.of_module_finite ℚ F
      Chebotarev.UnramifiedIn ℚ F (Ideal.span {(p : 𝓞 ℚ)}))
    (hfixed : letI : NumberField F := NumberField.of_module_finite ℚ F
      ¬ ∃ x : A, (ψ (Chebotarev.frobeniusClass ℚ F (Ideal.span {(p : 𝓞 ℚ)})).out).2 x = x) :
    letI : NumberField F := NumberField.of_module_finite ℚ F
    (∃ τ : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp),
      IsConj (χ (rationalPrimeArithmeticRestriction a p hp τ))
        (ψ (Chebotarev.frobeniusClass ℚ F (Ideal.span {(p : 𝓞 ℚ)})).out).1) ∧
    rationalArithmeticH1PrimeRestriction a A hA p hp (Submodule.Quotient.mk c) ≠ 0 := by
  letI : NumberField F := NumberField.of_module_finite ℚ F
  have hlift := rationalArithmetic_exists_local_frobenius a p hp F
  have hlift' := hlift hunr
  obtain ⟨τ, hτ⟩ := hlift'
  have hconj : IsConj (Chebotarev.frobeniusClass ℚ F
      (Ideal.span {(p : 𝓞 ℚ)})).out
      (AlgEquiv.restrictNormalHom F (rationalPrimeArithmeticRestriction a p hp τ)) := by
    apply ConjClasses.mk_eq_mk_iff_isConj.mp
    exact (Quotient.out_eq _).trans hτ
  have hpair := ψ.map_isConj hconj
  rw [hψ] at hpair
  have hfirst := (MonoidHom.fst T (Equiv.Perm A)).map_isConj hpair
  have hsecond := (MonoidHom.snd T (Equiv.Perm A)).map_isConj hpair
  refine ⟨⟨τ, hfirst.symm⟩, ?_⟩
  apply continuousH1Restriction_ne_zero_of_affine_no_fixed A hA
    (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
    (rationalPrimeArithmeticRestriction a p hp).continuous c τ
  intro hx
  exact hfixed ((permutation_isConj_exists_fixed_iff hsecond).mpr hx)

/-- A detecting original Galois element fixing the constructed power root
produces an actual good prime with the required congruence and nonzero
restriction of the same continuous H1 class. Its original representation
image is retained up to conjugacy. -/
theorem rationalArithmetic_exists_prime_detecting_cocycle
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
      ∀ g : Gal(U/ℚ), g ζ = ζ → c.val g ∉ LinearMap.range (A.ρ g - 1) →
        ∀ S : Finset ℕ, ∃ p : ℕ, ∃ hp : p.Prime,
          p ∉ S ∧ ¬ (p : 𝓞 ℚ) ∣ a ∧ p ≡ 1 [MOD q ^ n] ∧
          (∃ τ : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp),
            IsConj (χ (rationalPrimeArithmeticRestriction a p hp τ)) (χ g)) ∧
          rationalArithmeticH1PrimeRestriction a A hA p hp (Submodule.Quotient.mk c) ≠ 0 := by
  let U := rationalUnramifiedExtension a
  letI : Algebra ℚ U := U.algebra'
  letI : IsGalois ℚ U := originalUnramifiedGaloisUnion_isGalois a
  have hprimes := rationalArithmetic_exists_cocycle_auxiliary_prime a ha q n hqa A hA χ c
  obtain ⟨ζ, hζ, F, _, ψ, hψ, hF⟩ := hprimes
  letI : Algebra ℚ F := F.algebra'
  letI : NumberField F := NumberField.of_module_finite ℚ F
  refine ⟨ζ, hζ, ?_⟩
  intro g hg hc S
  have hselected := hF g hg hc S
  obtain ⟨p, hp, hpS, hpa, hmod, hur, _, himage, hfixed⟩ := hselected
  have hdetect := rationalArithmetic_local_detection_of_finite_factor a p hp A hA χ.toMonoidHom c F
  have hdetect' := hdetect ψ hψ
  have hdetect'' := hdetect' hur hfixed
  obtain ⟨⟨τ, hτ⟩, hne⟩ := hdetect''
  exact ⟨p, hp, hpS, hpa, hmod, ⟨τ, hτ.trans himage⟩, hne⟩

end
end Dubon2026

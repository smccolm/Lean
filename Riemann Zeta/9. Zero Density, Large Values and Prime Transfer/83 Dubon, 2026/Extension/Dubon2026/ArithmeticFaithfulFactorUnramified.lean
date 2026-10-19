import Dubon2026.RationalArithmeticFiniteInertiaLift
import Dubon2026.NumberFieldUnramifiedOfTrivialInertia
import Dubon2026.ContinuousGaloisFaithfulFiniteFactor

/-! Trivial original local norm inertia in an actual discrete arithmetic
representation implies genuine unramifiedness of its faithful finite
Galois field. This combines the constructed inertia lifts with native
ramification theory, removing the finite-field unramifiedness premise
needed to identify Dubon Theorem 2.6's auxiliary augmentation quotient
with deformations on the original support. -/

namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField

attribute [local instance] rationalArithmeticOriginalFiniteGalois rationalPrimeLocalField_charZero
  rationalPrimeOriginalNorm rationalPrimeOriginalNorm_ultrametric
  rationalPrimeOriginalClosureNorm rationalPrimeOriginalClosureNormedAlgebra
  rationalPrimeOriginalClosureNorm_ultrametric
attribute [local instance 1100] rationalPrimeOriginalNormedField

/-- A faithful factor field of the original arithmetic representation
is genuinely unramified when that representation kills original local
norm inertia. No field ramification condition is supplied. -/
theorem rationalArithmetic_faithful_factor_unramified
    {T : Type} [Group T] (a : 𝓞 ℚ)
    (χ : rationalArithmeticGaloisGroup a →* T)
    (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    (ψ : Gal(F/ℚ) →* T) (hψinj : Function.Injective ψ)
    (hψ : ∀ g, ψ (AlgEquiv.restrictNormalHom F g) = χ g)
    (p : ℕ) (hp : p.Prime)
    (hI : ∀ g ∈ rationalPrimeNormInertia p hp,
      χ (rationalPrimeArithmeticRestriction a p hp g) = 1) :
    Chebotarev.UnramifiedIn ℚ F (Ideal.span {(p : 𝓞 ℚ)}) := by
  letI : NumberField F := NumberField.of_module_finite ℚ F
  letI (α : Algebra ℚ F) : @IsGalois ℚ _ F _ α := by
    have he : F.algebra' = α := Subsingleton.elim _ _
    exact Eq.mp (congrArg (fun β : Algebra ℚ F => @IsGalois ℚ _ F _ β) he) F.isGalois
  obtain ⟨w, hw, hs⟩ := rationalArithmetic_finite_inertia_exists_norm_lift a F p hp
  letI := hw
  have hbot : w.asIdeal.inertia Gal(F/ℚ) = ⊥ := by
    apply le_antisymm _ bot_le
    intro σ hσ
    change σ = 1
    obtain ⟨g, hg, hr⟩ := hs σ hσ
    apply hψinj
    exact (congrArg ψ hr.symm).trans
      ((hψ (rationalPrimeArithmeticRestriction a p hp g)).trans
        ((hI g hg).trans ψ.map_one.symm))
  have hu := numberField_unramifiedIn_of_inertia_eq_bot (rationalOriginalPrimePlace p hp) w hbot
  simpa only [rationalOriginalPrimePlace_eq_span] using hu

/-- The continuous representation itself constructs one faithful finite
Galois factor, unramified at every prime in the specified auxiliary set
where its original local inertia action is trivial. -/
theorem continuousArithmetic_faithful_unramified_factor
    {T : Type} [Group T] [TopologicalSpace T] [DiscreteTopology T]
    (a : 𝓞 ℚ) (χ : rationalArithmeticGaloisGroup a →ₜ* T)
    (Q : Finset Nat.Primes)
    (hI : ∀ (p : Q) g, g ∈ rationalPrimeNormInertia p.val.val p.val.property →
      χ (rationalPrimeArithmeticRestriction a p.val.val p.val.property g) = 1) :
    ∃ F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a),
      ∃ ψ : Gal(F/ℚ) →* T, Function.Injective ψ ∧
        (∀ g, ψ (AlgEquiv.restrictNormalHom F g) = χ g) ∧
        ∀ p : Q, Chebotarev.UnramifiedIn ℚ F (Ideal.span {(p.val.val : 𝓞 ℚ)}) := by
  let U := rationalUnramifiedExtension a
  letI : Algebra ℚ U := U.algebra'
  letI : IsGalois ℚ U := originalUnramifiedGaloisUnion_isGalois a
  obtain ⟨F, ψ, hi, hf⟩ := continuous_galois_faithful_finite_factor χ
  refine ⟨F, ψ, hi, hf, ?_⟩
  intro p
  exact rationalArithmetic_faithful_factor_unramified a χ.toMonoidHom F ψ hi hf
    p.val.val p.val.property (hI p)

end
end Dubon2026

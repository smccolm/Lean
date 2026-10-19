import Dubon2026.ArithmeticOriginalSupportKernel
import Dubon2026.AdicMatrixProductEmbedding

/-! Actual continuous descent from auxiliary to original arithmetic
support, with uniqueness. The required kernel containment is derived
from the original local inertia conditions, rather than supplied as a
deformation-theoretic assumption. -/

namespace Dubon2026
noncomputable section
open scoped NumberField BigOperators

private theorem continuous_surjective_unique_factor
    {G H T : Type*} [Group G] [Group H] [Group T]
    [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace T]
    [CompactSpace G] [T2Space H]
    (π : G →ₜ* H) (hs : Function.Surjective π) (χ : G →ₜ* T)
    (hk : π.toMonoidHom.ker ≤ χ.toMonoidHom.ker) :
    ∃! η : H →ₜ* T, ∀ g, η (π g) = χ g := by
  let f := π.toMonoidHom.liftOfSurjective hs ⟨χ.toMonoidHom, hk⟩
  have hf : f.comp π.toMonoidHom = χ.toMonoidHom :=
    π.toMonoidHom.liftOfRightInverse_comp _ _ _
  have hfc : Continuous f := by
    apply (IsQuotientMap.of_surjective_continuous hs π.continuous).continuous_iff.mpr
    exact χ.continuous.congr fun g => (DFunLike.congr_fun hf g).symm
  let η : H →ₜ* T := ⟨f, hfc⟩
  refine ⟨η, DFunLike.congr_fun hf, ?_⟩
  intro η' hη'
  apply DFunLike.ext
  intro h
  obtain ⟨g, rfl⟩ := hs h
  exact (hη' g).trans (DFunLike.congr_fun hf g).symm

/-- A discrete continuous representation of the auxiliary arithmetic
group descends uniquely and continuously to the actual original-support
group when its original auxiliary inertia actions are trivial. -/
theorem continuousArithmetic_original_support_descent
    {T : Type} [Group T] [TopologicalSpace T] [DiscreteTopology T]
    (a b : 𝓞 ℚ) (hb : b ≠ 0) (Q : Finset Nat.Primes)
    (hba : b = a * ∏ p ∈ Q, (p.val : 𝓞 ℚ)) (hab : a ∣ b)
    (χ : rationalArithmeticGaloisGroup b →ₜ* T)
    (hI : ∀ (p : Q) g, g ∈ rationalPrimeNormInertia p.val.val p.val.property →
      χ (rationalPrimeArithmeticRestriction b p.val.val p.val.property g) = 1) :
    ∃! η : rationalArithmeticGaloisGroup a →ₜ* T,
      ∀ g, η (rationalArithmeticSupportRestriction a b hab g) = χ g :=
  continuous_surjective_unique_factor (rationalArithmeticSupportRestriction a b hab)
    (rationalArithmeticSupportRestriction_surjective a b hab) χ
    (continuousArithmetic_original_support_kernel a b hb Q hba hab χ hI)

/-- Separated adic coefficients also give the required kernel
containment: all actual power reductions descend by the discrete
theorem, and the existing adic matrix embedding detects equality. -/
theorem adicArithmetic_original_support_kernel
    {A ι : Type} [CommRing A] [WithIdeal A] [T2Space A]
    [Fintype ι] [DecidableEq ι]
    (a b : 𝓞 ℚ) (hb : b ≠ 0) (Q : Finset Nat.Primes)
    (hba : b = a * ∏ p ∈ Q, (p.val : 𝓞 ℚ)) (hab : a ∣ b)
    (τ : rationalArithmeticGaloisGroup b →ₜ* Matrix.GeneralLinearGroup ι A)
    (hI : ∀ (p : Q) g, g ∈ rationalPrimeNormInertia p.val.val p.val.property →
      τ (rationalPrimeArithmeticRestriction b p.val.val p.val.property g) = 1) :
    (rationalArithmeticSupportRestriction a b hab).toMonoidHom.ker ≤ τ.toMonoidHom.ker := by
  intro g hg
  change τ g = 1
  apply adicMatrixReductionProduct_injective
  funext n
  letI : DiscreteTopology (A ⧸ (WithIdeal.i : Ideal A) ^ n) := adicPowerQuotient_discrete n
  let f := Matrix.GeneralLinearGroup.map (n := ι)
    (Ideal.Quotient.mk ((WithIdeal.i : Ideal A) ^ n))
  let χ : rationalArithmeticGaloisGroup b →ₜ*
      Matrix.GeneralLinearGroup ι (A ⧸ (WithIdeal.i : Ideal A) ^ n) :=
    ⟨f.comp τ.toMonoidHom, (adicMatrixPowerReduction_continuous n).comp τ.continuous⟩
  have hχ : ∀ (p : Q) x, x ∈ rationalPrimeNormInertia p.val.val p.val.property →
      χ (rationalPrimeArithmeticRestriction b p.val.val p.val.property x) = 1 := by
    intro p x hx
    change f (τ (rationalPrimeArithmeticRestriction b p.val.val p.val.property x)) = 1
    rw [hI p x hx, map_one]
  have hk := continuousArithmetic_original_support_kernel a b hb Q hba hab χ hχ hg
  change f (τ g) = f 1
  exact hk.trans f.map_one.symm

/-- The actual continuous adic matrix representation descends uniquely
to original arithmetic support from the auxiliary inertia relations.
No compatible choices of representations on the power quotients are
needed. -/
theorem adicArithmetic_original_support_descent
    {A ι : Type} [CommRing A] [WithIdeal A] [T2Space A]
    [Fintype ι] [DecidableEq ι]
    (a b : 𝓞 ℚ) (hb : b ≠ 0) (Q : Finset Nat.Primes)
    (hba : b = a * ∏ p ∈ Q, (p.val : 𝓞 ℚ)) (hab : a ∣ b)
    (τ : rationalArithmeticGaloisGroup b →ₜ* Matrix.GeneralLinearGroup ι A)
    (hI : ∀ (p : Q) g, g ∈ rationalPrimeNormInertia p.val.val p.val.property →
      τ (rationalPrimeArithmeticRestriction b p.val.val p.val.property g) = 1) :
    ∃! η : rationalArithmeticGaloisGroup a →ₜ* Matrix.GeneralLinearGroup ι A,
      ∀ g, η (rationalArithmeticSupportRestriction a b hab g) = τ g :=
  continuous_surjective_unique_factor (rationalArithmeticSupportRestriction a b hab)
    (rationalArithmeticSupportRestriction_surjective a b hab) τ
    (adicArithmetic_original_support_kernel a b hb Q hba hab τ hI)

end
end Dubon2026

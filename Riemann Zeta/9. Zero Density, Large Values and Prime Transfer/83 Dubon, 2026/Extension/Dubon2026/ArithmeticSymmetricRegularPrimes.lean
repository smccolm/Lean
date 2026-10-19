import Dubon2026.SymmetricRegularRootElement
import Dubon2026.ArithmeticCyclotomicAuxiliaryPrimes
import Dubon2026.RationalArithmeticFrobeniusLift

/-! Actual regular auxiliary primes for the higher symmetric residual image.
The prescribed root, regular original element, finite Galois factor and
original local Frobenius lift are constructed. DUB-17 still needs residual
image containment for modular representations and dual-Selmer detection. -/

namespace Dubon2026
noncomputable section
open scoped NumberField MatrixGroups
attribute [local instance] rationalArithmeticOriginalFiniteGalois

/-- Conjugate actual invertible matrices have the same characteristic polynomial. -/
theorem generalLinearGroup_charpoly_eq_of_isConj {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] {A B : Matrix.GeneralLinearGroup ι K}
    (h : IsConj A B) : A.val.charpoly = B.val.charpoly := by
  obtain ⟨C, hC⟩ := isConj_iff.mp h
  rw [← hC]
  change A.val.charpoly = (C.val * A.val * (C⁻¹).val).charpoly
  rw [Matrix.charpoly_mul_comm, ← mul_assoc, ← Units.val_mul,
    inv_mul_cancel, Units.val_one, one_mul]

/-- A sufficiently large actual symmetric SL2 residual image supplies good
congruence primes with a split regular residual Frobenius. The original
finite factor and actual completion Frobenius equality are retained. -/
theorem rationalArithmetic_exists_symmetric_regular_auxiliary_primes
    (a : 𝓞 ℚ) (ha : a ≠ 0) (q level degree : ℕ) [NeZero q]
    (hqa : (q : 𝓞 ℚ) ∣ a)
    {K : Type} [Field K] [Finite K] [TopologicalSpace K] [DiscreteTopology K]
    [NeZero (2 : K)] [NeZero (3 : K)]
    (hsize : 2 * degree < Nat.card K - 1)
    (ρ : rationalArithmeticGaloisGroup a →ₜ* Matrix.GeneralLinearGroup (Fin (degree + 1)) K)
    (himage : ((homogeneousSymmetricGL (R := K) degree).comp
      Matrix.SpecialLinearGroup.toGL).range ≤ ρ.toMonoidHom.range) :
    let U := rationalUnramifiedExtension a
    letI : Algebra ℚ U := U.algebra'
    ∃ u : Kˣ, orderOf u = Nat.card K - 1 ∧
      ∃ F : FiniteGaloisIntermediateField ℚ U,
        ∃ ψ : Gal(F/ℚ) →* Matrix.GeneralLinearGroup (Fin (degree + 1)) K,
          (∀ g : Gal(U/ℚ), ψ (AlgEquiv.restrictNormalHom F g) = ρ g) ∧
          (letI : NumberField F := NumberField.of_module_finite ℚ F
           ∀ S : Finset ℕ, ∃ p : ℕ, ∃ hp : p.Prime,
             p ∉ S ∧ ¬ (p : 𝓞 ℚ) ∣ a ∧ p ≡ 1 [MOD q ^ level] ∧
             Chebotarev.UnramifiedIn ℚ F (Ideal.span {(p : 𝓞 ℚ)}) ∧
             ∃ τ : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp),
               Chebotarev.frobeniusClass ℚ F (Ideal.span {(p : 𝓞 ℚ)}) =
                 ConjClasses.mk (AlgEquiv.restrictNormalHom F
                   (rationalPrimeArithmeticRestriction a p hp τ)) ∧
               IsConj (ρ (rationalPrimeArithmeticRestriction a p hp τ))
                 (homogeneousSymmetricGL degree
                   (Matrix.SpecialLinearGroup.toGL (ringSL2UnitDiagonal u))) ∧
               (ρ (rationalPrimeArithmeticRestriction a p hp τ)).val.charpoly.Separable) := by
  let U := rationalUnramifiedExtension a
  letI : Algebra ℚ U := U.algebra'
  letI : IsGalois ℚ U := originalUnramifiedGaloisUnion_isGalois a
  obtain ⟨ζ, hζ, F, _, ψ, hψ, hF⟩ :=
    rationalArithmetic_exists_cyclotomic_auxiliary_prime a ha q level hqa ρ
  obtain ⟨u, hu, γ, hfix, hγ, hregular⟩ :=
    galois_exists_root_fixing_symmetric_regular degree hsize ρ.toMonoidHom himage hζ
  change ρ γ = homogeneousSymmetricGL degree
    (Matrix.SpecialLinearGroup.toGL (ringSL2UnitDiagonal u)) at hγ
  refine ⟨u, hu, F, ψ, hψ, ?_⟩
  letI : Algebra ℚ F := F.algebra'
  letI : NumberField F := NumberField.of_module_finite ℚ F
  intro S
  obtain ⟨p, hp, hpS, hpa, hmod, hunr, _, hconj⟩ := hF γ hfix S
  have hlift := rationalArithmetic_exists_local_frobenius a p hp F
  obtain ⟨τ, hτ⟩ := hlift hunr
  have hc : IsConj (Chebotarev.frobeniusClass ℚ F
      (Ideal.span {(p : 𝓞 ℚ)})).out
      (AlgEquiv.restrictNormalHom F (rationalPrimeArithmeticRestriction a p hp τ)) := by
    apply ConjClasses.mk_eq_mk_iff_isConj.mp
    exact (Quotient.out_eq _).trans hτ
  have hc' := ψ.map_isConj hc
  rw [hψ] at hc'
  have hres := hc'.symm.trans hconj
  refine ⟨p, hp, hpS, hpa, hmod, hunr, τ, hτ, ?_, ?_⟩
  · simpa only [hγ] using hres
  · rw [generalLinearGroup_charpoly_eq_of_isConj hres]
    exact hregular

end
end Dubon2026

import Dubon2026.RationalArithmeticNormFrobenius
import Dubon2026.ArithmeticSymmetricDimensionalPrime
import Dubon2026.RationalRegularPrimeInertia

/-! # Retaining the selected split torus witness at the original auxiliary prime

The earlier native prime selection already constructs this conjugacy. Keeping
it in the prime property permits the actual tame deformation classification
required by the arithmetic patching chain for Dubon Theorem 2.6.
-/

namespace Dubon2026
noncomputable section
open Matrix
open scoped NumberField MatrixGroups
attribute [local instance] rationalArithmeticOriginalFiniteGalois

/-- The original good congruence prime with its actual finite unramified factor
and explicit split regular torus conjugacy, including the weight separation bound. -/
def RationalArithmeticTorusAuxiliaryPrime
    (a : 𝓞 ℚ) (q degree level : ℕ) [Fact q.Prime]
    (R : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin (degree + 1)) (ZMod q))
    (p : Nat.Primes) : Prop :=
  ¬ (p.val : 𝓞 ℚ) ∣ a ∧ p.val ≡ 1 [MOD q ^ level] ∧
  ∃ u : (ZMod q)ˣ, 2 * degree < orderOf u ∧
    (let U := rationalUnramifiedExtension a
     letI : Algebra ℚ U := U.algebra'
     letI : IsGalois ℚ U := originalUnramifiedGaloisUnion_isGalois a
     ∃ F : FiniteGaloisIntermediateField ℚ U,
       ∃ ψ : Gal(F/ℚ) →* GeneralLinearGroup (Fin (degree + 1)) (ZMod q),
         (∀ w : Gal(U/ℚ), ψ (AlgEquiv.restrictNormalHom F w) = R w) ∧
         (letI : NumberField F := NumberField.of_module_finite ℚ F
          Chebotarev.UnramifiedIn ℚ F (Ideal.span {(p.val : 𝓞 ℚ)}) ∧
          ∃ γ : Gal(rationalPrimeLocalClosure p.val p.property / rationalPrimeLocalField p.val p.property),
            Chebotarev.frobeniusClass ℚ F (Ideal.span {(p.val : 𝓞 ℚ)}) =
              ConjClasses.mk (AlgEquiv.restrictNormalHom F
                (rationalPrimeArithmeticRestriction a p.val p.property γ)) ∧
            IsConj (R (rationalPrimeArithmeticRestriction a p.val p.property γ))
              (homogeneousSymmetricGL degree (SpecialLinearGroup.toGL (ringSL2UnitDiagonal u)))))

/-- The retained split torus witness proves the earlier regular-prime property. -/
theorem RationalArithmeticTorusAuxiliaryPrime.regular
    (a : 𝓞 ℚ) (q degree level : ℕ) [Fact q.Prime]
    (R : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin (degree + 1)) (ZMod q))
    (p : Nat.Primes) (h : RationalArithmeticTorusAuxiliaryPrime a q degree level R p) :
    RationalArithmeticRegularAuxiliaryPrime a q level R p := by
  obtain ⟨hpa, hmod, u, hu, F, ψ, hψ, hunr, γ, hγ, hconj⟩ := h
  refine ⟨hpa, hmod, F, ψ, hψ, hunr, γ, hγ, ?_⟩
  rw [generalLinearGroup_charpoly_eq_of_isConj hconj]
  exact homogeneousSymmetricGL_unitDiagonal_separable u degree hu

attribute [local instance] rationalPrimeLocalField_charZero
  rationalPrimeOriginalNorm rationalPrimeOriginalNorm_ultrametric
  rationalPrimeOriginalClosureNorm rationalPrimeOriginalClosureNormedAlgebra
  rationalPrimeOriginalClosureNorm_ultrametric algebraicLocalIntegerAction
attribute [local instance 1100] rationalPrimeOriginalNormedField

/-- Every actual original residue Frobenius has the split torus conjugacy
retained by selection, so it can be used in the tame local-ring computation. -/
theorem RationalArithmeticTorusAuxiliaryPrime.original_frobenius_conjugate
    (a : 𝓞 ℚ) (q degree level : ℕ) [Fact q.Prime]
    (R : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin (degree + 1)) (ZMod q))
    (p : Nat.Primes) (h : RationalArithmeticTorusAuxiliaryPrime a q degree level R p)
    (φ : Gal(rationalPrimeLocalClosure p.val p.property / rationalPrimeLocalField p.val p.property))
    (hφ : ∀ x : IsLocalRing.ResidueField (algebraicLocalIntegerRing
      (rationalPrimeLocalClosure p.val p.property)), φ • x = x ^ p.val) :
    ∃ u : (ZMod q)ˣ, 2 * degree < orderOf u ∧
      IsConj (R (rationalPrimeArithmeticRestriction a p.val p.property φ))
        (homogeneousSymmetricGL degree (SpecialLinearGroup.toGL (ringSL2UnitDiagonal u))) := by
  obtain ⟨_, _, u, hu, F, ψ, hψ, hunr, γ, hγ, hconj⟩ := h
  have hf := rationalArithmetic_original_residue_frobenius_class a p.val p.property F hunr φ hφ
  have hfg := ConjClasses.mk_eq_mk_iff_isConj.mp (hf.symm.trans hγ)
  have hrep := ψ.map_isConj hfg
  have hrep' : IsConj
      (R (rationalPrimeArithmeticRestriction a p.val p.property φ))
      (R (rationalPrimeArithmeticRestriction a p.val p.property γ)) := by
    convert hrep using 1 <;> exact (hψ _).symm
  exact ⟨u, hu, hrep'.trans hconj⟩

end
end Dubon2026

import Dubon2026.ChebotarevRationalPrime
import Dubon2026.RationalArithmeticNormFrobenius
import Dubon2026.RationalPrimeFiniteTameGenerator

/-! DUB-17/18 -> arithmetic automorphy -> the actual residual determinant.
The assembled representation has the prescribed determinant at every good
Frobenius. Reuse the existing finite-factor Chebotarev theorem and the
actual norm-residue Frobenius lift to identify continuous discrete
characters globally. This discharges global determinant compatibility
before applying fixed-determinant arithmetic constructions. -/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance] rationalPrimeLocalField_charZero rationalArithmeticOriginalFiniteGalois
  rationalPrimeOriginalNorm rationalPrimeOriginalNorm_ultrametric
  rationalPrimeOriginalClosureNorm rationalPrimeOriginalClosureNormedAlgebra
  rationalPrimeOriginalClosureNorm_ultrametric algebraicLocalIntegerAction
attribute [local instance 1100] rationalPrimeOriginalNormedField

theorem sourceArithmeticCharacters_eq_of_frobenius
    {T : Type} [CommGroup T] [TopologicalSpace T] [DiscreteTopology T]
    (a : 𝓞 ℚ) (χ₁ χ₂ : rationalArithmeticGaloisGroup a →ₜ* T)
    (S : Finset ℕ)
    (hFrob : ∀ (p : ℕ) (hp : p.Prime), p ∉ S →
      ∀ g : Gal(rationalPrimeLocalClosure p hp/rationalPrimeLocalField p hp),
        (∀ z : IsLocalRing.ResidueField (algebraicLocalIntegerRing
          (rationalPrimeLocalClosure p hp)), g • z = z ^ p) →
        χ₁ (rationalPrimeArithmeticRestriction a p hp g) =
          χ₂ (rationalPrimeArithmeticRestriction a p hp g)) :
    χ₁ = χ₂ := by
  let U := rationalUnramifiedExtension a
  letI : Algebra ℚ U := U.algebra'
  letI : IsGalois ℚ U := originalUnramifiedGaloisUnion_isGalois a
  let χ : Gal(U/ℚ) →ₜ* T × T := χ₁.prod χ₂
  have hc := continuous_rational_galois_exists_frobenius_prime χ
  rcases hc with ⟨F, ψ, hψ, hF⟩
  letI : Algebra ℚ F := F.algebra'
  letI : NumberField F := NumberField.of_module_finite ℚ F
  apply DFunLike.ext
  intro g
  obtain ⟨p, hp, hpS, hunr, hclass, _⟩ := hF g S
  obtain ⟨φ, hφ⟩ := rationalPrimeOriginalNorm_exists_frobenius p hp
  have hlocal := rationalArithmetic_original_residue_frobenius_class a p hp F hunr φ hφ
  have hconj : IsConj (AlgEquiv.restrictNormalHom F g)
      (AlgEquiv.restrictNormalHom F (rationalPrimeArithmeticRestriction a p hp φ)) :=
    ConjClasses.mk_eq_mk_iff_isConj.mp (hclass.symm.trans hlocal)
  have he : χ g = χ (rationalPrimeArithmeticRestriction a p hp φ) := by
    have hh := isConj_iff_eq.mp (ψ.map_isConj hconj)
    exact (hψ g).symm.trans (hh.trans (hψ (rationalPrimeArithmeticRestriction a p hp φ)))
  exact (congrArg Prod.fst he).trans
    ((hFrob p hp hpS φ hφ).trans (congrArg Prod.snd he).symm)

end
end Dubon2026

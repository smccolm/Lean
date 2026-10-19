import Dubon2026.RationalPrimeUnramifiedDimension
import Dubon2026.RationalArithmeticFrobeniusImageGenerator
import Dubon2026.CyclicMatrixTraceInvariants

/-! The selected auxiliary prime's original finite Frobenius class now
determines the actual unramified adjoint cohomology dimension at that
same prime. This consumes the existing symmetric regular-prime output,
without requiring a different Frobenius lift or an assumed cyclic image.
It serves DUB-17's local deformation dimension dependency. -/

namespace Dubon2026
noncomputable section
open Matrix
open scoped NumberField MatrixGroups
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] rationalArithmeticOriginalFiniteGalois

/-- At the very same original auxiliary prime, the original regular
symmetric residual Frobenius gives unramified adjoint H1 dimension equal
to the symmetric degree. Local image generation and H1 finiteness are
derived from the actual finite factor and original completion. -/
theorem rationalPrime_symmetric_unramified_finrank
    (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime) (q n : ℕ) [Fact q.Prime]
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin (n + 1)) (ZMod q))
    (hρ : Continuous ρ)
    (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    (ψ : Gal(F/ℚ) →* GeneralLinearGroup (Fin (n + 1)) (ZMod q))
    (hψ : ∀ w : rationalArithmeticGaloisGroup a,
      ψ (AlgEquiv.restrictNormalHom F w) = ρ w)
    (hunr : Chebotarev.UnramifiedIn ℚ F (Ideal.span {(p : 𝓞 ℚ)}))
    (γ : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp))
    (hγ : Chebotarev.frobeniusClass ℚ F (Ideal.span {(p : 𝓞 ℚ)}) =
      ConjClasses.mk (AlgEquiv.restrictNormalHom F (rationalPrimeArithmeticRestriction a p hp γ)))
    (u : (ZMod q)ˣ) (hu : 2 * n < orderOf u)
    (hconj : IsConj (ρ (rationalPrimeArithmeticRestriction a p hp γ))
      (homogeneousSymmetricGL n (SpecialLinearGroup.toGL (ringSL2UnitDiagonal u)))) :
  let R := ρ.comp (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
    let hR := hρ.comp (rationalPrimeArithmeticRestriction a p hp).continuous
    Module.finrank (ZMod q) (continuousRepresentationH1Restriction
      (matrixTraceZeroAdjointRep R) (matrixTraceZeroAdjointAction_continuous R hR)
      (rationalPrimeNormInertia p hp).subtype continuous_subtype_val).ker = n := by
  let R := ρ.comp (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
  let hR := hρ.comp (rationalPrimeArithmeticRestriction a p hp).continuous
  have hgen (g : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp)) :
      R g ∈ Subgroup.zpowers (R γ) := by
    exact rationalArithmetic_local_frobenius_generates_representation_image
      a p hp ρ F ψ hψ hunr γ hγ g
  have hd := matrixTrace_invariants_finrank_of_symmetric_generator n R γ hgen u hu hconj
  exact (rationalPrime_unramified_finrank_eq_invariants p hp q
    (matrixTraceZeroAdjointRep R) (matrixTraceZeroAdjointAction_continuous R hR)).trans hd

end
end Dubon2026

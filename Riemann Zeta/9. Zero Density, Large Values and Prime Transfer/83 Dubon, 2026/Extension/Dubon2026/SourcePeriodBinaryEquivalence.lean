import Dubon2026.SourcePeriodBinaryIntertwiner
import Dubon2026.SourcePeriodCocycle

/-! An actual equivalence of the original dual period coefficient module.
DUB-17/18 -> residual modular Galois association -> the original nonzero
period H1 eigensystem in the column binary convention. The existing monomial
basis, native dual basis and already proved invertible intertwiner supply
the equivalence; no independent symmetric-power model is introduced.
-/

namespace Dubon2026
noncomputable section
open Matrix Matrix.SpecialLinearGroup Module MvPolynomial
open scoped MatrixGroups
variable {K : Type*} [Field K]

/-- Original inverse row substitution is the existing column action at inverse transpose. -/
theorem sourceModularBinaryFormSLRep_eq_column (n : ℕ) (g : SL(2, ℤ)) :
    sourceModularBinaryFormSLRep K n g =
      homogeneousGLRepresentation n (polarizedContragredient (mapGL K g)) := by
  have hinv : (mapGL K g).inv =
      ((g⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom K) :=
    congrArg Units.val (map_inv (mapGL K) g).symm
  apply LinearMap.ext
  intro P
  apply Subtype.ext
  change matrixPolynomialAction _ P.val = matrixPolynomialAction _ P.val
  change matrixPolynomialAction
      (((g⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom K)).transpose
      P.val = matrixPolynomialAction (mapGL K g).inv.transpose P.val
  rw [hinv]

/-- The native dual action has precisely the contragredient symmetric matrix. -/
theorem sourcePeriodDual_toMatrix (n : ℕ) (g : SL(2, ℤ)) :
    LinearMap.toMatrix (binaryHomogeneousMonomialBasis (R := K) n).dualBasis
      (binaryHomogeneousMonomialBasis n).dualBasis
      ((sourceModularBinaryFormSLRep K n).dual g) =
        (polarizedContragredient
          (homogeneousSymmetricGL n (polarizedContragredient (mapGL K g)))).val := by
  change LinearMap.toMatrix _ _
    (Module.Dual.transpose (sourceModularBinaryFormSLRep K n g⁻¹)) = _
  rw [LinearMap.toMatrix_transpose, sourceModularBinaryFormSLRep_eq_column]
  change (homogeneousSymmetricGL n (polarizedContragredient (mapGL K g⁻¹))).val.transpose = _
  rw [map_inv, map_inv, map_inv]
  rfl

/-- The actual change of coefficient convention, on the original homogeneous module. -/
def sourcePeriodBinaryEquiv (n : ℕ) (hn : (n.factorial : K) ≠ 0) :
    Module.Dual K (homogeneousSubmodule (Fin 2) K n) ≃ₗ[K]
      homogeneousSubmodule (Fin 2) K n :=
  ((binaryHomogeneousMonomialBasis (R := K) n).dualBasis.equiv
    (binaryHomogeneousMonomialBasis n) (Equiv.refl _)).trans
      (GeneralLinearGroup.toLin' (binaryHomogeneousMonomialBasis n)
        (sourcePeriodBinaryIntertwiner n hn)).toLinearEquiv

/-- The coefficient equivalence is represented by the proved original intertwiner. -/
theorem sourcePeriodBinaryEquiv_toMatrix (n : ℕ) (hn : (n.factorial : K) ≠ 0) :
    LinearMap.toMatrix (binaryHomogeneousMonomialBasis (R := K) n).dualBasis
      (binaryHomogeneousMonomialBasis n) (sourcePeriodBinaryEquiv n hn).toLinearMap =
        (sourcePeriodBinaryIntertwiner n hn).val := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  change (binaryHomogeneousMonomialBasis (R := K) n).repr
    ((GeneralLinearGroup.toLin' (binaryHomogeneousMonomialBasis n)
      (sourcePeriodBinaryIntertwiner n hn)).toLinearEquiv
        (((binaryHomogeneousMonomialBasis (R := K) n).dualBasis.equiv
          (binaryHomogeneousMonomialBasis n) (Equiv.refl _))
            ((binaryHomogeneousMonomialBasis (R := K) n).dualBasis j))) i = _
  rw [Basis.equiv_apply]
  simp [GeneralLinearGroup.toLin'_apply, Fintype.linearCombination_apply,
    Matrix.mulVec, dotProduct, Finsupp.single_apply]

/-- The coefficient equivalence transports the genuine dual period action to
the genuine column substitution action at every modular-group element. -/
theorem sourcePeriodBinaryEquiv_intertwine
    (n : ℕ) (hn : (n.factorial : K) ≠ 0) (g : SL(2, ℤ)) :
    (sourcePeriodBinaryEquiv n hn).toLinearMap.comp
        ((sourceModularBinaryFormSLRep K n).dual g) =
      (homogeneousGLRepresentation n (mapGL K g)).comp
        (sourcePeriodBinaryEquiv n hn).toLinearMap := by
  apply (LinearMap.toMatrix (binaryHomogeneousMonomialBasis (R := K) n).dualBasis
    (binaryHomogeneousMonomialBasis n)).injective
  rw [LinearMap.toMatrix_comp _ (binaryHomogeneousMonomialBasis n).dualBasis,
    LinearMap.toMatrix_comp _ (binaryHomogeneousMonomialBasis n),
    sourcePeriodBinaryEquiv_toMatrix, sourcePeriodDual_toMatrix]
  exact (congrArg Units.val (sourcePeriodBinaryIntertwiner_intertwine n hn g)).symm

end
end Dubon2026

import Dubon2026.SourceGammaOneHeckeFieldNaturality

/-! DUB-17/18 -> original all-weight adic association -> arithmetic Gamma1
realization -> actual Galois/Hecke compatibility. The proved coefficient map
and its inverse give the genuine arithmetic automorphism of each actual
integral-ratio field. Both Hecke maps commute with this action. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open CongruenceSubgroup
variable {L : Type*} [Field L] [Algebra ℚ L]

/-- The arithmetic coefficient automorphism of the actual modular integral-ratio field. -/
def arithmeticRingAut (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (σ : L ≃ₐ[ℚ] L) : functionFieldOver Γ L ≃+* functionFieldOver Γ L where
  toFun := fieldCoefficientMap Γ σ.toAlgHom
  invFun := fieldCoefficientMap Γ σ.symm.toAlgHom
  left_inv x := by
    apply Subtype.ext
    ext n
    exact σ.symm_apply_apply (x.val.coeff n)
  right_inv x := by
    apply Subtype.ext
    ext n
    exact σ.apply_symm_apply (x.val.coeff n)
  map_mul' x y := (fieldCoefficientMap Γ σ.toAlgHom).map_mul x y
  map_add' x y := (fieldCoefficientMap Γ σ.toAlgHom).map_add x y

theorem arithmeticRingAut_constants
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (σ : L ≃ₐ[ℚ] L) (a : L) :
    arithmeticRingAut Γ σ (algebraMap L (functionFieldOver Γ L) a) =
      algebraMap L (functionFieldOver Γ L) (σ a) :=
  fieldCoefficientMap_constants Γ σ.toAlgHom a

theorem arithmeticRingAut_j
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (σ : L ≃ₐ[ℚ] L) :
    arithmeticRingAut Γ σ (jCoordinateOver Γ L) = jCoordinateOver Γ L :=
  fieldCoefficientMap_j Γ σ.toAlgHom

theorem heckeAlpha_arithmetic (M d : ℕ) (σ : L ≃ₐ[ℚ] L)
    (x : laurentBaseChange L (x1FunctionField M)) :
    arithmeticRingAut (Gamma1 M ⊓ Gamma0 (d * M)) σ (heckeAlpha L M d x) =
      heckeAlpha L M d (arithmeticRingAut (Gamma1 M) σ x) :=
  heckeAlpha_coefficientMap M d σ.toAlgHom x

theorem heckeBeta_arithmetic (M d : ℕ) [NeZero d] (σ : L ≃ₐ[ℚ] L)
    (x : laurentBaseChange L (x1FunctionField M)) :
    arithmeticRingAut (Gamma1 M ⊓ Gamma0 (d * M)) σ (heckeBeta L M d x) =
      heckeBeta L M d (arithmeticRingAut (Gamma1 M) σ x) :=
  heckeBeta_coefficientMap M d σ.toAlgHom x

end
end Dubon2026.SourceFunctionField.GammaOne

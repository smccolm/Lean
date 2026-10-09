import Dubon2026.FiniteAdelicLocalHom
import Dubon2026.AdelicRealScalar

/-! # Genuine local units and scalar matrices in the original finite adelic ring -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

/-- The genuine finite idele whose original v-coordinate is u and whose other coordinates are one. -/
def finiteAdeleLocalUnit (v : HeightOneSpectrum ℤ) (u : (v.adicCompletion ℚ)ˣ) :
    (FiniteAdeleRing ℤ ℚ)ˣ := by
  classical
  exact
    { val := RestrictedProduct.mulSingle (fun w : HeightOneSpectrum ℤ => w.adicCompletionIntegers ℚ) v u.val
      inv := RestrictedProduct.mulSingle (fun w : HeightOneSpectrum ℤ => w.adicCompletionIntegers ℚ) v (u⁻¹).val
      val_inv := by
        apply DFunLike.ext
        intro w
        change RestrictedProduct.mulSingle (fun t : HeightOneSpectrum ℤ => t.adicCompletionIntegers ℚ) v u.val w *
          RestrictedProduct.mulSingle (fun t : HeightOneSpectrum ℤ => t.adicCompletionIntegers ℚ) v (u⁻¹).val w = 1
        by_cases h : w = v
        · subst w
          rw [RestrictedProduct.mulSingle_eq_same, RestrictedProduct.mulSingle_eq_same]
          exact u.val_inv
        · rw [RestrictedProduct.mulSingle_eq_of_ne _ _ h, RestrictedProduct.mulSingle_eq_of_ne _ _ h, one_mul]
      inv_val := by
        apply DFunLike.ext
        intro w
        change RestrictedProduct.mulSingle (fun t : HeightOneSpectrum ℤ => t.adicCompletionIntegers ℚ) v (u⁻¹).val w *
          RestrictedProduct.mulSingle (fun t : HeightOneSpectrum ℤ => t.adicCompletionIntegers ℚ) v u.val w = 1
        by_cases h : w = v
        · subst w
          rw [RestrictedProduct.mulSingle_eq_same, RestrictedProduct.mulSingle_eq_same]
          exact u.inv_val
        · rw [RestrictedProduct.mulSingle_eq_of_ne _ _ h, RestrictedProduct.mulSingle_eq_of_ne _ _ h, one_mul] }

/-- Original place evaluation of this actual finite idele is exactly its given local unit. -/
theorem finiteAdeleLocalUnit_same (v : HeightOneSpectrum ℤ) (u : (v.adicCompletion ℚ)ˣ) :
    Units.map (finiteAdelePlace v).toMonoidHom (finiteAdeleLocalUnit v u) = u := by
  classical
  apply Units.ext
  exact RestrictedProduct.mulSingle_eq_same (fun w : HeightOneSpectrum ℤ => w.adicCompletionIntegers ℚ) v u.val

/-- At every other original place the actual finite idele is the identity unit. -/
theorem finiteAdeleLocalUnit_ne (v w : HeightOneSpectrum ℤ) (h : w ≠ v) (u : (v.adicCompletion ℚ)ˣ) :
    Units.map (finiteAdelePlace w).toMonoidHom (finiteAdeleLocalUnit v u) = 1 := by
  classical
  apply Units.ext
  exact RestrictedProduct.mulSingle_eq_of_ne (fun t : HeightOneSpectrum ℤ => t.adicCompletionIntegers ℚ) u.val h

/-- Inserting the original local scalar matrix gives precisely the scalar of the genuine inserted finite idele. -/
theorem finiteAdelicLocalGL2_scalar (v : HeightOneSpectrum ℤ) (u : (v.adicCompletion ℚ)ˣ) :
    finiteAdelicLocalGL2 v (GeneralLinearGroup.scalar (Fin 2) u) =
      GeneralLinearGroup.scalar (Fin 2) (finiteAdeleLocalUnit v u) := by
  apply finiteAdelicGL2_ext
  intro w
  rw [gl2Scalar_map]
  by_cases h : w = v
  · subst w
    rw [finiteAdelicLocalGL2_same, finiteAdeleLocalUnit_same]
  · rw [finiteAdelicLocalGL2_ne v w h, finiteAdeleLocalUnit_ne v w h, map_one]

end
end Dubon2026

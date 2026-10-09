import Dubon2026.AdelicLocalMixedCoefficient

/-! # Exact original finite-adelic factorization into one genuine place and its genuine complement -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

/-- Actual one-place insertion and coordinate removal give the original finite adelic group as the genuine product of that local group and its complement. -/
def finiteAdelicLocalAwayEquiv (v : HeightOneSpectrum ℤ) :
    (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ) × finiteAdelicAwayGroup v) ≃*
      GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ) where
  toFun a := finiteAdelicLocalGL2 v a.1 * a.2.val
  invFun b := (GeneralLinearGroup.map (finiteAdelePlace v) b,
    ⟨finiteAdelicPlaceRemoval v b, finiteAdelicPlaceRemoval_same v b⟩)
  left_inv a := by
    apply Prod.ext
    · change GeneralLinearGroup.map (finiteAdelePlace v) (finiteAdelicLocalGL2 v a.1 * a.2.val) = a.1
      rw [map_mul, finiteAdelicLocalGL2_same, a.2.property, mul_one]
    · apply Subtype.ext
      change finiteAdelicPlaceRemoval v (finiteAdelicLocalGL2 v a.1 * a.2.val) = a.2.val
      rw [finiteAdelicPlaceRemoval, map_mul, finiteAdelicLocalGL2_same, a.2.property, mul_one,
        inv_mul_cancel_left]
  right_inv b := finiteAdelicLocal_mul_removal v b
  map_mul' a b := by
    change finiteAdelicLocalGL2 v (a.1 * b.1) * (a.2.val * b.2.val) =
      (finiteAdelicLocalGL2 v a.1 * a.2.val) * (finiteAdelicLocalGL2 v b.1 * b.2.val)
    rw [finiteAdelicLocalGL2_mul]
    have hc := finiteAdelicLocalGL2_commute_of_place_one v a.2.val a.2.property b.1
    calc
      _ = finiteAdelicLocalGL2 v a.1 * (finiteAdelicLocalGL2 v b.1 * a.2.val) * b.2.val := by
        simp only [mul_assoc]
      _ = finiteAdelicLocalGL2 v a.1 * (a.2.val * finiteAdelicLocalGL2 v b.1) * b.2.val := by rw [hc.eq]
      _ = _ := by simp only [mul_assoc]

/-- The actual product equivalence inserts exactly the original local matrix and actual away-place matrix. -/
theorem finiteAdelicLocalAwayEquiv_apply (v : HeightOneSpectrum ℤ)
    (g : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) (a : finiteAdelicAwayGroup v) :
    finiteAdelicLocalAwayEquiv v (g, a) = finiteAdelicLocalGL2 v g * a.val := rfl

/-- The inverse genuine factorization recovers the original finite place coordinate. -/
theorem finiteAdelicLocalAwayEquiv_symm_fst (v : HeightOneSpectrum ℤ)
    (a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    ((finiteAdelicLocalAwayEquiv v).symm a).1 = GeneralLinearGroup.map (finiteAdelePlace v) a := rfl

/-- The inverse genuine factorization recovers exactly the original removed-coordinate factor. -/
theorem finiteAdelicLocalAwayEquiv_symm_snd (v : HeightOneSpectrum ℤ)
    (a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    ((finiteAdelicLocalAwayEquiv v).symm a).2.val = finiteAdelicPlaceRemoval v a := rfl

end
end Dubon2026

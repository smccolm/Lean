import Dubon2026.FiniteAdelicGL2Level

/-! # Genuine one-place general-linear groups inside the original finite adelic group -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

/-- Evaluation of the original finite adele at its genuine finite place. -/
def finiteAdelePlace (v : HeightOneSpectrum ℤ) : FiniteAdeleRing ℤ ℚ →+* v.adicCompletion ℚ :=
  RestrictedProduct.evalRingHom (fun w : HeightOneSpectrum ℤ => w.adicCompletion ℚ) v

/-- The original finite adele supported at exactly one place, with zero at every other place. -/
def finiteAdelePlaceSingle (v : HeightOneSpectrum ℤ) (x : v.adicCompletion ℚ) : FiniteAdeleRing ℤ ℚ := by
  classical
  exact RestrictedProduct.single (fun w : HeightOneSpectrum ℤ => w.adicCompletionIntegers ℚ) v x

/-- Actual evaluation recovers the original one-place entry. -/
theorem finiteAdelePlace_single_same (v : HeightOneSpectrum ℤ) (x : v.adicCompletion ℚ) :
    finiteAdelePlace v (finiteAdelePlaceSingle v x) = x := by
  classical
  exact RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum ℤ => w.adicCompletionIntegers ℚ) v x

/-- The one-place entry vanishes at every other genuine place. -/
theorem finiteAdelePlace_single_ne (v w : HeightOneSpectrum ℤ) (h : w ≠ v)
    (x : v.adicCompletion ℚ) : finiteAdelePlace w (finiteAdelePlaceSingle v x) = 0 := by
  classical
  exact RestrictedProduct.single_eq_of_ne (fun u : HeightOneSpectrum ℤ => u.adicCompletionIntegers ℚ) x h

/-- Insert a genuine local matrix at one place and the actual identity matrix at every other place. -/
def finiteAdelePlaceMatrix (v : HeightOneSpectrum ℤ) (a : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) :
    Matrix (Fin 2) (Fin 2) (FiniteAdeleRing ℤ ℚ) :=
  fun i j => (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing ℤ ℚ)) i j +
    finiteAdelePlaceSingle v (a i j - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j)

/-- The inserted matrix is exactly the original local matrix at its genuine place. -/
theorem finiteAdelePlaceMatrix_same (v : HeightOneSpectrum ℤ)
    (a : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) :
    (finiteAdelePlaceMatrix v a).map (finiteAdelePlace v) = a := by
  ext i j
  simp [finiteAdelePlaceMatrix, finiteAdelePlace_single_same, Matrix.one_apply]

/-- The inserted matrix is exactly the identity at every other place. -/
theorem finiteAdelePlaceMatrix_ne (v w : HeightOneSpectrum ℤ) (h : w ≠ v)
    (a : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) :
    (finiteAdelePlaceMatrix v a).map (finiteAdelePlace w) = 1 := by
  ext i j
  simp [finiteAdelePlaceMatrix, finiteAdelePlace_single_ne v w h, Matrix.one_apply]

/-- Actual finite-place evaluations separate the original finite adelic matrices. -/
theorem finiteAdeleMatrix_ext {a b : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing ℤ ℚ)}
    (h : ∀ v, a.map (finiteAdelePlace v) = b.map (finiteAdelePlace v)) : a = b := by
  funext i j
  apply DFunLike.ext
  intro v
  exact congrArg (fun M => M i j) (h v)

/-- The original local general-linear matrix inserted at its actual finite place. -/
def finiteAdelicLocalGL2 (v : HeightOneSpectrum ℤ)
    (g : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) :
    GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ) where
  val := finiteAdelePlaceMatrix v g.val
  inv := finiteAdelePlaceMatrix v (g⁻¹).val
  val_inv := by
    apply finiteAdeleMatrix_ext
    intro w
    rw [Matrix.map_mul]
    simp only [Matrix.map_one, map_zero, map_one]
    by_cases h : w = v
    · subst w
      rw [finiteAdelePlaceMatrix_same, finiteAdelePlaceMatrix_same]
      exact g.val_inv
    · rw [finiteAdelePlaceMatrix_ne v w h, finiteAdelePlaceMatrix_ne v w h, one_mul]
  inv_val := by
    apply finiteAdeleMatrix_ext
    intro w
    rw [Matrix.map_mul]
    simp only [Matrix.map_one, map_zero, map_one]
    by_cases h : w = v
    · subst w
      rw [finiteAdelePlaceMatrix_same, finiteAdelePlaceMatrix_same]
      exact g.inv_val
    · rw [finiteAdelePlaceMatrix_ne v w h, finiteAdelePlaceMatrix_ne v w h, one_mul]

/-- The genuine local insertion has precisely its original local GL2 coordinate. -/
theorem finiteAdelicLocalGL2_same (v : HeightOneSpectrum ℤ)
    (g : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) :
    GeneralLinearGroup.map (finiteAdelePlace v) (finiteAdelicLocalGL2 v g) = g :=
  Units.ext (finiteAdelePlaceMatrix_same v g.val)

/-- All other local GL2 coordinates of the genuine one-place insertion are the identity. -/
theorem finiteAdelicLocalGL2_ne (v w : HeightOneSpectrum ℤ) (h : w ≠ v)
    (g : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) :
    GeneralLinearGroup.map (finiteAdelePlace w) (finiteAdelicLocalGL2 v g) = 1 :=
  Units.ext (finiteAdelePlaceMatrix_ne v w h g.val)

end
end Dubon2026

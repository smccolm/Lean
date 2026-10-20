import Dubon2026.NumberFieldFiniteAdelicMatrixProjection

/-! # Original local matrices inside the number-field finite adeles

The existing rational GL2 insertion is reused at the required original
CM field and rank. This is the first part of the DUB-17 source local
level bridge: paired conjugate-place insertion will construct the
actual split unitary factors and realize the already proved parabolic
quotients inside the original global unitary level.
-/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix
open scoped NumberField

variable (K : Type*) [Field K] [NumberField K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Evaluation of the original finite adele at its genuine finite place. -/
def numberFieldFiniteAdelePlace (v : HeightOneSpectrum (𝓞 K)) : FiniteAdeleRing (𝓞 K) K →+* v.adicCompletion K :=
  RestrictedProduct.evalRingHom (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K) v

/-- The original finite adele supported at exactly one place, with zero at every other place. -/
def numberFieldFiniteAdelePlaceSingle (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K) : FiniteAdeleRing (𝓞 K) K := by
  classical
  exact RestrictedProduct.single (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletionIntegers K) v x

/-- Actual evaluation recovers the original one-place entry. -/
theorem numberFieldFiniteAdelePlace_single_same (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K) :
    numberFieldFiniteAdelePlace K v (numberFieldFiniteAdelePlaceSingle K v x) = x := by
  classical
  exact RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletionIntegers K) v x

/-- The one-place entry vanishes at every other genuine place. -/
theorem numberFieldFiniteAdelePlace_single_ne (v w : HeightOneSpectrum (𝓞 K)) (h : w ≠ v)
    (x : v.adicCompletion K) : numberFieldFiniteAdelePlace K w (numberFieldFiniteAdelePlaceSingle K v x) = 0 := by
  classical
  exact RestrictedProduct.single_eq_of_ne (fun u : HeightOneSpectrum (𝓞 K) => u.adicCompletionIntegers K) x h

/-- Insert a genuine local matrix at one place and the actual identity matrix at every other place. -/
def numberFieldFiniteAdelePlaceMatrix (v : HeightOneSpectrum (𝓞 K)) (a : Matrix ι ι (v.adicCompletion K)) :
    Matrix ι ι (FiniteAdeleRing (𝓞 K) K) :=
  fun i j => (1 : Matrix ι ι (FiniteAdeleRing (𝓞 K) K)) i j +
    numberFieldFiniteAdelePlaceSingle K v (a i j - (1 : Matrix ι ι (v.adicCompletion K)) i j)

omit [Fintype ι] in
/-- The inserted matrix is exactly the original local matrix at its genuine place. -/
theorem numberFieldFiniteAdelePlaceMatrix_same (v : HeightOneSpectrum (𝓞 K))
    (a : Matrix ι ι (v.adicCompletion K)) :
    (numberFieldFiniteAdelePlaceMatrix K v a).map (numberFieldFiniteAdelePlace K v) = a := by
  ext i j
  simp [numberFieldFiniteAdelePlaceMatrix, numberFieldFiniteAdelePlace_single_same, Matrix.one_apply]

omit [Fintype ι] in
/-- The inserted matrix is exactly the identity at every other place. -/
theorem numberFieldFiniteAdelePlaceMatrix_ne (v w : HeightOneSpectrum (𝓞 K)) (h : w ≠ v)
    (a : Matrix ι ι (v.adicCompletion K)) :
    (numberFieldFiniteAdelePlaceMatrix K v a).map (numberFieldFiniteAdelePlace K w) = 1 := by
  ext i j
  simp [numberFieldFiniteAdelePlaceMatrix, numberFieldFiniteAdelePlace_single_ne K v w h, Matrix.one_apply]

omit [Fintype ι] [DecidableEq ι] in
/-- Actual finite-place evaluations separate the original finite adelic matrices. -/
theorem numberFieldFiniteAdeleMatrix_ext {a b : Matrix ι ι (FiniteAdeleRing (𝓞 K) K)}
    (h : ∀ v, a.map (numberFieldFiniteAdelePlace K v) = b.map (numberFieldFiniteAdelePlace K v)) : a = b := by
  funext i j
  apply DFunLike.ext
  intro v
  exact congrArg (fun M => M i j) (h v)

/-- The original local general-linear matrix inserted at its actual finite place. -/
def numberFieldFiniteAdelicLocalGL (v : HeightOneSpectrum (𝓞 K))
    (g : GeneralLinearGroup ι (v.adicCompletion K)) :
    GeneralLinearGroup ι (FiniteAdeleRing (𝓞 K) K) where
  val := numberFieldFiniteAdelePlaceMatrix K v g.val
  inv := numberFieldFiniteAdelePlaceMatrix K v (g⁻¹).val
  val_inv := by
    apply numberFieldFiniteAdeleMatrix_ext K
    intro w
    rw [Matrix.map_mul]
    simp only [Matrix.map_one, map_zero, map_one]
    by_cases h : w = v
    · subst w
      rw [numberFieldFiniteAdelePlaceMatrix_same K, numberFieldFiniteAdelePlaceMatrix_same K]
      exact g.val_inv
    · rw [numberFieldFiniteAdelePlaceMatrix_ne K v w h, numberFieldFiniteAdelePlaceMatrix_ne K v w h, one_mul]
  inv_val := by
    apply numberFieldFiniteAdeleMatrix_ext K
    intro w
    rw [Matrix.map_mul]
    simp only [Matrix.map_one, map_zero, map_one]
    by_cases h : w = v
    · subst w
      rw [numberFieldFiniteAdelePlaceMatrix_same K, numberFieldFiniteAdelePlaceMatrix_same K]
      exact g.inv_val
    · rw [numberFieldFiniteAdelePlaceMatrix_ne K v w h, numberFieldFiniteAdelePlaceMatrix_ne K v w h, one_mul]

/-- The genuine local insertion has precisely its original local matrix coordinate. -/
theorem numberFieldFiniteAdelicLocalGL_same (v : HeightOneSpectrum (𝓞 K))
    (g : GeneralLinearGroup ι (v.adicCompletion K)) :
    GeneralLinearGroup.map (numberFieldFiniteAdelePlace K v) (numberFieldFiniteAdelicLocalGL K v g) = g :=
  Units.ext (numberFieldFiniteAdelePlaceMatrix_same K v g.val)

/-- All other local matrix coordinates of the genuine one-place insertion are the identity. -/
theorem numberFieldFiniteAdelicLocalGL_ne (v w : HeightOneSpectrum (𝓞 K)) (h : w ≠ v)
    (g : GeneralLinearGroup ι (v.adicCompletion K)) :
    GeneralLinearGroup.map (numberFieldFiniteAdelePlace K w) (numberFieldFiniteAdelicLocalGL K v g) = 1 :=
  Units.ext (numberFieldFiniteAdelePlaceMatrix_ne K v w h g.val)

end
end Dubon2026

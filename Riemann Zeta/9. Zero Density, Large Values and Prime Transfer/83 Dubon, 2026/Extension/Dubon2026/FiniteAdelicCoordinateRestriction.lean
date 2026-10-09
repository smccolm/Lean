import Dubon2026.FiniteAdelicLocalHom

/-! # Actual finite adelic matrices restricted to any genuine set of finite places -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Filter

/-- Piecewise selection of two actual finite adeles retains their genuine almost-integrality. -/
def finiteAdelePiecewise (S : Set (HeightOneSpectrum ℤ)) (a b : FiniteAdeleRing ℤ ℚ) : FiniteAdeleRing ℤ ℚ := by
  classical
  refine ⟨fun v => if v ∈ S then a v else b v, ?_⟩
  filter_upwards [a.property, b.property] with v ha hb
  by_cases hv : v ∈ S
  · simpa only [if_pos hv] using ha
  · simpa only [if_neg hv] using hb

/-- A retained original place sees the literal original selected adele entry. -/
theorem finiteAdelePiecewise_mem (S : Set (HeightOneSpectrum ℤ)) (a b : FiniteAdeleRing ℤ ℚ)
    (v : HeightOneSpectrum ℤ) (hv : v ∈ S) : finiteAdelePlace v (finiteAdelePiecewise S a b) = finiteAdelePlace v a := by
  classical
  change (if v ∈ S then a v else b v) = a v
  exact if_pos hv

/-- An unretained original place sees the literal original alternative adele entry. -/
theorem finiteAdelePiecewise_not_mem (S : Set (HeightOneSpectrum ℤ)) (a b : FiniteAdeleRing ℤ ℚ)
    (v : HeightOneSpectrum ℤ) (hv : v ∉ S) : finiteAdelePlace v (finiteAdelePiecewise S a b) = finiteAdelePlace v b := by
  classical
  change (if v ∈ S then a v else b v) = b v
  exact if_neg hv

/-- Retain the original matrix on the given actual places and put the identity matrix elsewhere. -/
def finiteAdelicMatrixOn (S : Set (HeightOneSpectrum ℤ))
    (a : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing ℤ ℚ)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing ℤ ℚ) :=
  fun i j => finiteAdelePiecewise S (a i j) ((1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing ℤ ℚ)) i j)

/-- Every selected genuine coordinate of the retained matrix is exactly its original coordinate. -/
theorem finiteAdelicMatrixOn_mem (S : Set (HeightOneSpectrum ℤ))
    (a : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing ℤ ℚ)) (v : HeightOneSpectrum ℤ) (hv : v ∈ S) :
    (finiteAdelicMatrixOn S a).map (finiteAdelePlace v) = a.map (finiteAdelePlace v) := by
  ext i j
  exact finiteAdelePiecewise_mem S (a i j) _ v hv

/-- Every other genuine coordinate of the retained matrix is the actual identity. -/
theorem finiteAdelicMatrixOn_not_mem (S : Set (HeightOneSpectrum ℤ))
    (a : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing ℤ ℚ)) (v : HeightOneSpectrum ℤ) (hv : v ∉ S) :
    (finiteAdelicMatrixOn S a).map (finiteAdelePlace v) = 1 := by
  have he : (finiteAdelicMatrixOn S a).map (finiteAdelePlace v) =
      (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing ℤ ℚ)).map (finiteAdelePlace v) := by
    ext i j
    exact finiteAdelePiecewise_not_mem S (a i j) _ v hv
  simpa only [Matrix.map_one, map_zero, map_one] using he

/-- Actual finite adelic GL2 restricted to selected places is again genuine finite adelic GL2. -/
def finiteAdelicGL2On (S : Set (HeightOneSpectrum ℤ))
    (g : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ) where
  val := finiteAdelicMatrixOn S g.val
  inv := finiteAdelicMatrixOn S (g⁻¹).val
  val_inv := by
    apply finiteAdeleMatrix_ext
    intro v
    rw [Matrix.map_mul]
    simp only [Matrix.map_one, map_zero, map_one]
    by_cases hv : v ∈ S
    · rw [finiteAdelicMatrixOn_mem S _ v hv, finiteAdelicMatrixOn_mem S _ v hv, ← Matrix.map_mul]
      change (g.val * g.inv).map (finiteAdelePlace v) = 1
      rw [g.val_inv]
      simp only [Matrix.map_one, map_zero, map_one]
    · rw [finiteAdelicMatrixOn_not_mem S _ v hv, finiteAdelicMatrixOn_not_mem S _ v hv, one_mul]
  inv_val := by
    apply finiteAdeleMatrix_ext
    intro v
    rw [Matrix.map_mul]
    simp only [Matrix.map_one, map_zero, map_one]
    by_cases hv : v ∈ S
    · rw [finiteAdelicMatrixOn_mem S _ v hv, finiteAdelicMatrixOn_mem S _ v hv, ← Matrix.map_mul]
      change (g.inv * g.val).map (finiteAdelePlace v) = 1
      rw [g.inv_val]
      simp only [Matrix.map_one, map_zero, map_one]
    · rw [finiteAdelicMatrixOn_not_mem S _ v hv, finiteAdelicMatrixOn_not_mem S _ v hv, one_mul]

/-- The actual restricted invertible matrix retains its literal original selected coordinate. -/
theorem finiteAdelicGL2On_mem (S : Set (HeightOneSpectrum ℤ))
    (g : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) (v : HeightOneSpectrum ℤ) (hv : v ∈ S) :
    GeneralLinearGroup.map (finiteAdelePlace v) (finiteAdelicGL2On S g) = GeneralLinearGroup.map (finiteAdelePlace v) g :=
  Units.ext (finiteAdelicMatrixOn_mem S g.val v hv)

/-- The actual restricted invertible matrix has identity at every other genuine coordinate. -/
theorem finiteAdelicGL2On_not_mem (S : Set (HeightOneSpectrum ℤ))
    (g : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) (v : HeightOneSpectrum ℤ) (hv : v ∉ S) :
    GeneralLinearGroup.map (finiteAdelePlace v) (finiteAdelicGL2On S g) = 1 :=
  Units.ext (finiteAdelicMatrixOn_not_mem S g.val v hv)

end
end Dubon2026

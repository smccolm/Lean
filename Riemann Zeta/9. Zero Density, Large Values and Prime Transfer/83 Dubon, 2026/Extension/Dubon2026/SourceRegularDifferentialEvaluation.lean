import Dubon2026.SourceRegularDifferentialLie

/-! Evaluation of the original infinitesimal action over every coefficient algebra.
This is the exact base-change compatibility needed to prove preservation of
the source Borel covariance, rather than assuming an induced Lie action.
-/

namespace Dubon2026
noncomputable section
open Matrix TrivSqZeroExt

variable {R S A : Type*} [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra R A]

/-- An original coefficient algebra map acts on both components of its dual numbers. -/
def sourceDualCoefficientMap (f : S →ₐ[R] A) : DualNumber S →ₐ[R] DualNumber A where
  toFun x := ⟨f x.fst, f x.snd⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' x y := by ext <;> simp
  map_mul' x y := by ext <;> simp
  commutes' r := by ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl']

/-- The actual epsilon component commutes with original coefficient evaluation. -/
theorem sourceDualCoefficientMap_snd (f : S →ₐ[R] A) (x : DualNumber S) :
    (sourceDualCoefficientMap f x).snd = f x.snd := rfl

/-- The actual infinitesimal matrix commutes with the original coefficient map. -/
theorem sourceInfinitesimalMatrix_map {n : ℕ} (f : S →ₐ[R] A)
    (X : Matrix (Fin n) (Fin n) S) :
    GeneralLinearGroup.map (sourceDualCoefficientMap f).toRingHom (sourceInfinitesimalMatrix X) =
      sourceInfinitesimalMatrix (X.map f) := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  by_cases h : i = j <;> apply TrivSqZeroExt.ext <;>
    simp [sourceDualCoefficientMap, sourceInfinitesimalMatrix,
      TrivSqZeroExt.algebraMap_eq_inl, h]

variable {n : ℕ}

/-- The original matrix point translated by `1 + ε X` over its actual coefficient algebra. -/
def sourceInfinitesimalPointAt (X : Matrix (Fin n) (Fin n) R)
    (g : GeneralLinearGroup (Fin n) A) : GeneralLinearGroup (Fin n) (DualNumber A) :=
  GeneralLinearGroup.map (inlAlgHom R A A).toRingHom g *
    sourceInfinitesimalMatrix (X.map (algebraMap R A))

/-- Evaluation of the same original generic infinitesimal point is its actual infinitesimal translate at the evaluation matrix. -/
theorem sourceRegularInfinitesimalPoint_map (X : Matrix (Fin n) (Fin n) R)
    (g : GeneralLinearGroup (Fin n) A) :
    GeneralLinearGroup.map
      (sourceDualCoefficientMap (generalLinearRegularEval (R := R) g)).toRingHom
      (sourceRegularInfinitesimalPoint X) = sourceInfinitesimalPointAt X g := by
  rw [sourceRegularInfinitesimalPoint, sourceInfinitesimalPointAt, map_mul,
    sourceInfinitesimalMatrix_map]
  congr 1
  · have h := generalLinearRegularGeneric_eval R n g
    apply Units.ext
    apply Matrix.ext
    intro i j
    apply TrivSqZeroExt.ext
    · exact congrArg (fun u => u.val i j) h
    · exact map_zero (generalLinearRegularEval (R := R) g)
  · congr 1
    ext i j
    exact (generalLinearRegularEval (R := R) g).commutes (X i j)

/-- Evaluating the original dual-number differential is exactly evaluating the same function at the infinitesimally translated original matrix point. -/
theorem sourceRegularInfinitesimalEval_natural (X : Matrix (Fin n) (Fin n) R)
    (g : GeneralLinearGroup (Fin n) A) :
    (sourceDualCoefficientMap (generalLinearRegularEval (R := R) g)).comp
      (sourceRegularInfinitesimalEval X) =
      generalLinearRegularEval (R := R) (A := DualNumber A) (sourceInfinitesimalPointAt X g) := by
  rw [sourceRegularInfinitesimalEval, generalLinearRegularEval_natural,
    sourceRegularInfinitesimalPoint_map]

/-- Original evaluation of the differential equals the epsilon coefficient of the original function evaluated at the actual infinitesimal translate. -/
theorem sourceRegularDifferential_eval (X : Matrix (Fin n) (Fin n) R)
    (g : GeneralLinearGroup (Fin n) A) (p : GeneralLinearRegularFunctions R n) :
    generalLinearRegularEval g (sourceRegularDifferential X p) =
      (generalLinearRegularEval (R := R) (A := DualNumber A) (sourceInfinitesimalPointAt X g) p).snd := by
  have h := congrArg TrivSqZeroExt.snd
    (AlgHom.congr_fun (sourceRegularInfinitesimalEval_natural X g) p)
  exact h

end
end Dubon2026

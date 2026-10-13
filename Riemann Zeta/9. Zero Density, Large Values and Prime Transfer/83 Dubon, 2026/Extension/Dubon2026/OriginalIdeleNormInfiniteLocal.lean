import Dubon2026.OriginalIdeleInfiniteOrbitNorm

/-! # Actual ininfinite components of the descended idele norm are actual field norms

The actual coset product supplies a concrete local unit whose determinant
norm is the original base infinite component of the descended idele norm.
This composes original adele descent, completed decomposition-field descent
and original Galois products. It removes the archimedean-local norm comparison
assumption in DUB-17's native norm-index and reciprocity chain.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
attribute [local instance] IsCyclic.commGroup
variable (w : InfinitePlace L)

omit [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)] in
/-- The original infinite component of original idele base change is its actual completed base embedding. -/
theorem originalIdeleBaseChangeMap_infiniteComponent (a : (AdeleRing (𝓞 K) K)ˣ) :
    numberFieldIdeleInfiniteComponent L w (originalIdeleBaseChangeMap K L a) =
      Units.map (originalInfiniteCompletionBaseChange K L w).toMonoidHom
        (numberFieldIdeleInfiniteComponent K (w.comap (algebraMap K L)) a) := rfl

attribute [-instance] UniformSpace.Completion.instSMul in
/-- The original infinite component of the original idele norm is the actual local norm of the explicit original coset product. -/
theorem originalIdeleNorm_infiniteComponent_eq_localNorm :
    letI : Algebra ((w.comap (algebraMap K L)).Completion) (w.Completion) :=
      (originalInfiniteCompletionBaseChange K L w).toAlgebra
    ∀ a : (AdeleRing (𝓞 L) L)ˣ,
      numberFieldIdeleInfiniteComponent K (w.comap (algebraMap K L)) (originalIdeleNorm K L a) =
        Units.map (Algebra.norm ((w.comap (algebraMap K L)).Completion) (S := w.Completion))
          (originalIdeleInfiniteOrbitNormPreimage K L w a) := by
  letI : Algebra ((w.comap (algebraMap K L)).Completion) (w.Completion) :=
    (originalInfiniteCompletionBaseChange K L w).toAlgebra
  intro a
  have h : Units.map (originalInfiniteCompletionBaseChange K L w).toMonoidHom
      (numberFieldIdeleInfiniteComponent K (w.comap (algebraMap K L)) (originalIdeleNorm K L a)) =
      ∏ τ : OriginalInfiniteDecompositionGroup K L w,
        Units.map (numberFieldGaloisArchimedeanTransport K L τ.val w w τ.property).toMonoidHom
          (originalIdeleInfiniteOrbitNormPreimage K L w a) := by
    rw [← originalIdeleBaseChangeMap_infiniteComponent, originalIdeleBaseChangeMap_norm, map_prod]
    exact originalIdeleInfiniteOrbitNormPreimage_product K L w a
  apply Units.ext
  apply (originalInfiniteCompletionBaseChange K L w).injective
  change originalInfiniteCompletionBaseChange K L w (numberFieldIdeleInfiniteComponent K (w.comap (algebraMap K L)) (originalIdeleNorm K L a)).val =
    originalInfiniteCompletionBaseChange K L w (Algebra.norm ((w.comap (algebraMap K L)).Completion)
      (originalIdeleInfiniteOrbitNormPreimage K L w a).val)
  rw [originalInfiniteNorm_galois_product]
  have hv := congrArg Units.val h
  rw [Units.coe_prod] at hv
  exact hv

attribute [-instance] UniformSpace.Completion.instSMul in
/-- Every actual infinite component of an original idele norm lies in the actual corresponding local field-unit norm image. -/
theorem originalIdeleNorm_infiniteComponent_mem_localNorm :
    letI : Algebra ((w.comap (algebraMap K L)).Completion) (w.Completion) :=
      (originalInfiniteCompletionBaseChange K L w).toAlgebra
    ∀ a : (AdeleRing (𝓞 L) L)ˣ,
      numberFieldIdeleInfiniteComponent K (w.comap (algebraMap K L)) (originalIdeleNorm K L a) ∈
        (Units.map (Algebra.norm ((w.comap (algebraMap K L)).Completion) (S := w.Completion))).range := by
  letI : Algebra ((w.comap (algebraMap K L)).Completion) (w.Completion) :=
    (originalInfiniteCompletionBaseChange K L w).toAlgebra
  intro a
  exact ⟨originalIdeleInfiniteOrbitNormPreimage K L w a,
    (originalIdeleNorm_infiniteComponent_eq_localNorm K L w a).symm⟩

end
end Dubon2026

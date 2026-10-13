import Dubon2026.OriginalIdeleFiniteOrbitNorm

/-! # Actual finite components of the descended idele norm are actual field norms

The actual coset product supplies a concrete local unit whose determinant
norm is the original base finite component of the descended idele norm.
This composes original adele descent, completed decomposition-field descent
and original Galois products. It removes the finite-local norm comparison
assumption in DUB-17's native norm-index and reciprocity chain.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
attribute [local instance] IsCyclic.commGroup
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]

attribute [-instance] UniformSpace.Completion.instSMul in
/-- The original finite component of the original idele norm is the actual local norm of the explicit original coset product. -/
theorem originalIdeleNorm_finiteComponent_eq_localNorm :
    letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
      (originalAdicBaseChangeMap K L v w).toAlgebra
    ∀ a : (AdeleRing (𝓞 L) L)ˣ,
      numberFieldIdeleFiniteComponent K v (originalIdeleNorm K L a) =
        Units.map (Algebra.norm (v.adicCompletion K) (S := w.adicCompletion L))
          (originalIdeleFiniteOrbitNormPreimage K L w a) := by
  letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
    (originalAdicBaseChangeMap K L v w).toAlgebra
  intro a
  have h : Units.map (originalAdicBaseChangeMap K L v w).toMonoidHom
      (numberFieldIdeleFiniteComponent K v (originalIdeleNorm K L a)) =
      ∏ τ : OriginalFiniteDecompositionGroup K L w,
        Units.map (numberFieldGaloisLocalTransport K L τ.val w w τ.property).toMonoidHom
          (originalIdeleFiniteOrbitNormPreimage K L w a) := by
    rw [← originalIdeleBaseChangeMap_finiteComponent, originalIdeleBaseChangeMap_norm, map_prod]
    exact originalIdeleFiniteOrbitNormPreimage_product K L w a
  apply Units.ext
  apply (originalAdicBaseChangeMap K L v w).injective
  change originalAdicBaseChangeMap K L v w (numberFieldIdeleFiniteComponent K v (originalIdeleNorm K L a)).val =
    originalAdicBaseChangeMap K L v w (Algebra.norm (v.adicCompletion K)
      (originalIdeleFiniteOrbitNormPreimage K L w a).val)
  rw [originalAdicNorm_galois_product]
  have hv := congrArg Units.val h
  rw [Units.coe_prod] at hv
  exact hv

attribute [-instance] UniformSpace.Completion.instSMul in
/-- Every actual finite component of an original idele norm lies in the actual corresponding local field-unit norm image. -/
theorem originalIdeleNorm_finiteComponent_mem_localNorm :
    letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
      (originalAdicBaseChangeMap K L v w).toAlgebra
    ∀ a : (AdeleRing (𝓞 L) L)ˣ,
      numberFieldIdeleFiniteComponent K v (originalIdeleNorm K L a) ∈
        (Units.map (Algebra.norm (v.adicCompletion K) (S := w.adicCompletion L))).range := by
  letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
    (originalAdicBaseChangeMap K L v w).toAlgebra
  intro a
  exact ⟨originalIdeleFiniteOrbitNormPreimage K L w a,
    (originalIdeleNorm_finiteComponent_eq_localNorm K L v w a).symm⟩

end
end Dubon2026

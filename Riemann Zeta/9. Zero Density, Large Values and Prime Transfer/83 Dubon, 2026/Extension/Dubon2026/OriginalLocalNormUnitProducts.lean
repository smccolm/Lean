import Dubon2026.OriginalIdeleLocalNormMaps

/-! # Literal original local unit norms as decomposition-group products

These unit equalities retain the original completed embeddings and are
the local identities needed when assembling a norm preimage supported at
one chosen upper place over each original base place in DUB-17's chain.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

attribute [-instance] UniformSpace.Completion.instSMul in
/-- The actual finite-local unit norm becomes the actual original decomposition-group unit product. -/
theorem originalFiniteLocalNorm_baseChange (w : HeightOneSpectrum (𝓞 L)) (u : (w.adicCompletion L)ˣ) :
    letI := originalFinitePrimeBelow_liesOver K L w
    Units.map (originalAdicBaseChangeMap K L (originalFinitePrimeBelow K L w) w).toMonoidHom
        (originalFiniteLocalNorm K L w u) =
      ∏ τ : OriginalFiniteDecompositionGroup K L w,
        Units.map (numberFieldGaloisLocalTransport K L τ.val w w τ.property).toMonoidHom u := by
  letI := originalFinitePrimeBelow_liesOver K L w
  letI : Algebra ((originalFinitePrimeBelow K L w).adicCompletion K) (w.adicCompletion L) :=
    (originalAdicBaseChangeMap K L (originalFinitePrimeBelow K L w) w).toAlgebra
  apply Units.ext
  change originalAdicBaseChangeMap K L (originalFinitePrimeBelow K L w) w
    (Algebra.norm ((originalFinitePrimeBelow K L w).adicCompletion K) u.val) = _
  rw [Units.coe_prod]
  exact originalAdicNorm_galois_product K L (originalFinitePrimeBelow K L w) w u.val

attribute [-instance] UniformSpace.Completion.instSMul in
/-- The actual infinite-local unit norm becomes the actual original decomposition-group unit product. -/
theorem originalInfiniteLocalNorm_baseChange (w : InfinitePlace L) (u : w.Completionˣ) :
    Units.map (originalInfiniteCompletionBaseChange K L w).toMonoidHom
        (originalInfiniteLocalNorm K L w u) =
      ∏ τ : OriginalInfiniteDecompositionGroup K L w,
        Units.map (numberFieldGaloisArchimedeanTransport K L τ.val w w τ.property).toMonoidHom u := by
  letI : Algebra (w.comap (algebraMap K L)).Completion w.Completion :=
    (originalInfiniteCompletionBaseChange K L w).toAlgebra
  apply Units.ext
  change originalInfiniteCompletionBaseChange K L w
    (Algebra.norm (w.comap (algebraMap K L)).Completion u.val) = _
  rw [Units.coe_prod]
  exact originalInfiniteNorm_galois_product K L w u.val

end
end Dubon2026

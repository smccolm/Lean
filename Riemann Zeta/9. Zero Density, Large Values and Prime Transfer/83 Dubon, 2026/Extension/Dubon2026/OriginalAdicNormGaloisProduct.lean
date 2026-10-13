import Dubon2026.OriginalAdicDecompositionAction
import Mathlib.RingTheory.Norm.Transitivity

/-! # Actual original finite-local norms are decomposition-group products

The proved original base-completion/fixed-subfield equivalence transports
the existing field norm formula. Thus the local determinant norm is the
product of actual original completed decomposition-group transports.
This is the finite-local comparison needed for the descended idele norm
and local norm containment in DUB-17's global norm-index upper bound.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]

attribute [-instance] UniformSpace.Completion.instSMul in
/-- The actual local field norm maps to the product of the actual original decomposition-group conjugates. -/
theorem originalAdicNorm_galois_product :
    letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
      (originalAdicBaseChangeMap K L v w).toAlgebra
    ∀ x : w.adicCompletion L,
      originalAdicBaseChangeMap K L v w (Algebra.norm (v.adicCompletion K) x) =
        ∏ σ : OriginalFiniteDecompositionGroup K L w,
          numberFieldGaloisLocalTransport K L σ.val w w σ.property x := by
  letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
    (originalAdicBaseChangeMap K L v w).toAlgebra
  letI := originalAdicDecompositionAction K L w
  letI := originalAdicDecompositionAction_faithful K L w
  let B := FixedPoints.subfield (OriginalFiniteDecompositionGroup K L w) (w.adicCompletion L)
  let e := originalAdicBaseFixedEquiv K L v w
  have he : (algebraMap B (w.adicCompletion L)).comp e.toRingHom =
      algebraMap (v.adicCompletion K) (w.adicCompletion L) := by
    apply RingHom.ext
    intro x
    exact originalAdicBaseFixedEquiv_val K L v w x
  intro x
  have hn := Algebra.norm_eq_of_ringEquiv e he x
  have hp := Algebra.norm_eq_prod_automorphisms B x
  have hm := congrArg (algebraMap B (w.adicCompletion L)) hn
  change originalAdicBaseChangeMap K L v w (Algebra.norm (v.adicCompletion K) x) =
    algebraMap B (w.adicCompletion L) (Algebra.norm B x) at hm
  rw [hm, hp]
  exact (Fintype.prod_equiv
    (FixedPoints.toAlgAutMulEquiv (OriginalFiniteDecompositionGroup K L w) (w.adicCompletion L)).toEquiv
    (fun σ => numberFieldGaloisLocalTransport K L σ.val w w σ.property x)
    (fun τ => τ x) (fun _ => rfl)).symm

end
end Dubon2026

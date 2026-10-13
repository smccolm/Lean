import Dubon2026.OriginalInfiniteDecompositionAction
import Mathlib.RingTheory.Norm.Transitivity

/-! # Actual original archimedean-local norms are decomposition-group products

The proved original base-completion/fixed-subfield equivalence transports
the existing field norm formula. Thus the local determinant norm is the
product of actual original completed decomposition-group transports.
This is the archimedean-local comparison needed for the descended idele norm
and local norm containment in DUB-17's global norm-index upper bound.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (w : InfinitePlace L)

attribute [-instance] UniformSpace.Completion.instSMul in
/-- The actual local field norm maps to the product of the actual original decomposition-group conjugates. -/
theorem originalInfiniteNorm_galois_product :
    letI : Algebra ((w.comap (algebraMap K L)).Completion) (w.Completion) :=
      (originalInfiniteCompletionBaseChange K L w).toAlgebra
    ∀ x : w.Completion,
      originalInfiniteCompletionBaseChange K L w (Algebra.norm ((w.comap (algebraMap K L)).Completion) x) =
        ∏ σ : OriginalInfiniteDecompositionGroup K L w,
          numberFieldGaloisArchimedeanTransport K L σ.val w w σ.property x := by
  letI : Algebra ((w.comap (algebraMap K L)).Completion) (w.Completion) :=
    (originalInfiniteCompletionBaseChange K L w).toAlgebra
  letI := originalInfiniteDecompositionAction K L w
  letI := originalInfiniteDecompositionAction_faithful K L w
  let B := FixedPoints.subfield (OriginalInfiniteDecompositionGroup K L w) (w.Completion)
  let e := originalInfiniteCompletionBaseFixedEquiv K L w
  have he : (algebraMap B (w.Completion)).comp e.toRingHom =
      algebraMap ((w.comap (algebraMap K L)).Completion) (w.Completion) := by
    apply RingHom.ext
    intro x
    exact originalInfiniteCompletionBaseFixedEquiv_val K L w x
  intro x
  have hn := Algebra.norm_eq_of_ringEquiv e he x
  have hp := Algebra.norm_eq_prod_automorphisms B x
  have hm := congrArg (algebraMap B (w.Completion)) hn
  change originalInfiniteCompletionBaseChange K L w (Algebra.norm ((w.comap (algebraMap K L)).Completion) x) =
    algebraMap B (w.Completion) (Algebra.norm B x) at hm
  rw [hm, hp]
  exact (Fintype.prod_equiv
    (FixedPoints.toAlgAutMulEquiv (OriginalInfiniteDecompositionGroup K L w) (w.Completion)).toEquiv
    (fun σ => numberFieldGaloisArchimedeanTransport K L σ.val w w σ.property x)
    (fun τ => τ x) (fun _ => rfl)).symm

end
end Dubon2026

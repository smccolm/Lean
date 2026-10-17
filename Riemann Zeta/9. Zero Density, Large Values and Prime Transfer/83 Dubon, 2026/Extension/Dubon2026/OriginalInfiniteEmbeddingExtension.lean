import Dubon2026.NumberFieldGaloisArchimedeanTransport
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Extend the same original complex embedding through its completion

Pinned completion extension is applied directly to the specified complex
embedding, retaining its exact values rather than choosing a new embedding.
Density then proves compatibility with the original completed Galois
transport. This is the coefficient comparison needed to make original
infinite-coordinate vanishing kill DUB-17's actual real Mackey terms.
-/
namespace Dubon2026
noncomputable section
open NumberField

variable {L : Type} [Field L]

private theorem originalInfiniteEmbedding_isometry (j : L →+* ℂ) :
    Isometry (j.comp (WithAbs.equiv (InfinitePlace.mk j).1).toRingHom) :=
  AddMonoidHomClass.isometry_of_norm _ (fun _ => rfl)

/-- The original specified embedding extends through its actual infinite
completion by the pinned isometric completion extension. -/
def originalInfiniteEmbeddingExtension (j : L →+* ℂ) :
    (InfinitePlace.mk j).Completion →+* ℂ :=
  (originalInfiniteEmbedding_isometry j).extensionHom

/-- The completed embedding retains exactly the original field values. -/
theorem originalInfiniteEmbeddingExtension_algebraMap (j : L →+* ℂ) (x : L) :
    originalInfiniteEmbeddingExtension j (algebraMap L (InfinitePlace.mk j).Completion x) = j x := by
  exact (originalInfiniteEmbedding_isometry j).extensionHom_coe ((WithAbs.equiv _).symm x)

/-- The extension of the original embedding is continuous. -/
theorem originalInfiniteEmbeddingExtension_continuous (j : L →+* ℂ) :
    Continuous (originalInfiniteEmbeddingExtension j) :=
  (originalInfiniteEmbedding_isometry j).completion_extension.continuous

variable (K : Type) [Field K] [Algebra K L]

/-- An exact original field-level Galois square extends through the
literal original completed transport, with no completion compatibility premise. -/
theorem originalInfiniteEmbeddingExtension_transport
    (j : L →+* ℂ) (g : Gal(L/K))
    (hw : g • InfinitePlace.mk j = InfinitePlace.mk j)
    (σ : Gal(ℂ/ℝ)) (hcomm : ∀ x : L, j (g x) = σ (j x))
    (z : (InfinitePlace.mk j).Completion) :
    originalInfiniteEmbeddingExtension j
      (numberFieldGaloisArchimedeanTransport K L g (InfinitePlace.mk j) (InfinitePlace.mk j) hw z) =
      σ (originalInfiniteEmbeddingExtension j z) := by
  have hσ : Continuous σ := σ.toLinearMap.continuous_of_finiteDimensional
  refine UniformSpace.Completion.induction_on z
    (isClosed_eq ((originalInfiniteEmbeddingExtension_continuous j).comp
      (numberFieldGaloisArchimedeanTransport_continuous K L g _ _ hw))
      (hσ.comp (originalInfiniteEmbeddingExtension_continuous j))) ?_
  intro x
  change originalInfiniteEmbeddingExtension j
      (numberFieldGaloisArchimedeanTransport K L g _ _ hw
        (algebraMap L (InfinitePlace.mk j).Completion (WithAbs.equiv _ x))) =
      σ (originalInfiniteEmbeddingExtension j
        (algebraMap L (InfinitePlace.mk j).Completion (WithAbs.equiv _ x)))
  rw [numberFieldGaloisArchimedeanTransport_algebraMap,
    originalInfiniteEmbeddingExtension_algebraMap, originalInfiniteEmbeddingExtension_algebraMap]
  exact hcomm _

end
end Dubon2026

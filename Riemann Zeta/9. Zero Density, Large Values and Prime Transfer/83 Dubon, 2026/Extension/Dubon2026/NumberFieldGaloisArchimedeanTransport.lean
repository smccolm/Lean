import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.Topology.Algebra.UniformRing

/-! # Original Galois transport at the original infinite places

The pinned original action on infinite places gives norm-preserving maps
on the original valued fields. Their completion supplies the infinite
part of the original idele action used by DUB-17's supported sequence.
-/

namespace Dubon2026
noncomputable section
open NumberField UniformSpace
variable (K L : Type) [Field K] [Field L] [Algebra K L]

/-- The original automorphism on the original fields equipped with their infinite-place norms. -/
def numberFieldGaloisArchimedeanWithAbs (σ : Gal(L/K)) (v w : InfinitePlace L) :
    WithAbs v.val ≃+* WithAbs w.val := WithAbs.congr _ _ σ.toRingEquiv

/-- Actual Galois transport of infinite places makes the original field map an isometry. -/
theorem numberFieldGaloisArchimedeanWithAbs_isometry (σ : Gal(L/K))
    (v w : InfinitePlace L) (h : σ • v = w) :
    Isometry (numberFieldGaloisArchimedeanWithAbs K L σ v w) := by
  apply AddMonoidHomClass.isometry_of_norm
  intro x
  change w (σ x.ofAbs) = v x.ofAbs
  rw [← h, InfinitePlace.smul_apply, AlgEquiv.symm_apply_apply]

/-- The inverse original archimedean field map is also an isometry. -/
theorem numberFieldGaloisArchimedeanWithAbs_symm_isometry (σ : Gal(L/K))
    (v w : InfinitePlace L) (h : σ • v = w) :
    Isometry (numberFieldGaloisArchimedeanWithAbs K L σ v w).symm := by
  apply AddMonoidHomClass.isometry_of_norm
  intro x
  change v (σ.symm x.ofAbs) = w x.ofAbs
  exact congrArg (fun p : InfinitePlace L => p x.ofAbs) h

/-- The actual original Galois transport between the original archimedean completions. -/
def numberFieldGaloisArchimedeanTransport (σ : Gal(L/K))
    (v w : InfinitePlace L) (h : σ • v = w) : v.Completion ≃+* w.Completion :=
  Completion.mapRingEquiv (numberFieldGaloisArchimedeanWithAbs K L σ v w)
    (numberFieldGaloisArchimedeanWithAbs_isometry K L σ v w h).continuous
    (numberFieldGaloisArchimedeanWithAbs_symm_isometry K L σ v w h).continuous

/-- The completed archimedean transport extends the actual original global automorphism. -/
theorem numberFieldGaloisArchimedeanTransport_algebraMap (σ : Gal(L/K))
    (v w : InfinitePlace L) (h : σ • v = w) (x : L) :
    numberFieldGaloisArchimedeanTransport K L σ v w h (algebraMap L v.Completion x) =
      algebraMap L w.Completion (σ x) := by
  change Completion.mapRingHom (numberFieldGaloisArchimedeanWithAbs K L σ v w).toRingHom
    (numberFieldGaloisArchimedeanWithAbs_isometry K L σ v w h).continuous
      (↑(WithAbs.toAbs v.val x) : v.Completion) = _
  rw [Completion.mapRingHom_coe]
  rfl

/-- The completed original archimedean transport is continuous. -/
theorem numberFieldGaloisArchimedeanTransport_continuous (σ : Gal(L/K))
    (v w : InfinitePlace L) (h : σ • v = w) :
    Continuous (numberFieldGaloisArchimedeanTransport K L σ v w h) :=
  Completion.continuous_map

end
end Dubon2026

import Dubon2026.MatrixAdjointSchur

/-! # Descent of actual scalar adjoint invariants to the original coefficient field -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G ι K L : Type} [Group G] [Fintype ι] [DecidableEq ι]
  [Field K] [Field L] [Algebra K L]

/-- Extend each original representation matrix through the actual coefficient-field embedding. -/
def matrixCoefficientExtension (ρ : G →* GeneralLinearGroup ι K) :
    G →* GeneralLinearGroup ι L :=
  (GeneralLinearGroup.map (algebraMap K L)).comp ρ

/-- The original invariant matrix remains invariant under the actual extended representation. -/
def matrixAdjointInvariantScalarExtension (ρ : G →* GeneralLinearGroup ι K)
    (X : (matrixAdjointRepresentation ρ).invariants) :
    (matrixAdjointRepresentation (matrixCoefficientExtension (L := L) ρ)).invariants :=
  ⟨X.val.map (algebraMap K L), by
    intro g
    have h := congrArg (RingHom.mapMatrix (algebraMap K L)) (X.property g)
    change (RingHom.mapMatrix (algebraMap K L))
      ((ρ g).val * X.val * (ρ g⁻¹).val) = (RingHom.mapMatrix (algebraMap K L)) X.val at h
    change (RingHom.mapMatrix (algebraMap K L)) (ρ g).val *
      (RingHom.mapMatrix (algebraMap K L)) X.val *
        (RingHom.mapMatrix (algebraMap K L)) (ρ g⁻¹).val =
          (RingHom.mapMatrix (algebraMap K L)) X.val
    simpa only [map_mul] using h⟩

/-- Irreducibility after extension to an actual algebraically closed field forces every invariant matrix to be scalar over the original field itself. -/
theorem matrixAdjointInvariant_eq_scalar_of_extension [Nonempty ι] [IsAlgClosed L]
    (ρ : G →* GeneralLinearGroup ι K)
    [Representation.IsIrreducible (matrixStandardRepresentation (matrixCoefficientExtension (L := L) ρ))]
    (X : (matrixAdjointRepresentation ρ).invariants) :
    ∃ c : K, X.val = c • (1 : Matrix ι ι K) := by
  obtain ⟨d, hd⟩ := matrixAdjointInvariant_eq_scalar
    (matrixCoefficientExtension (L := L) ρ) (matrixAdjointInvariantScalarExtension (L := L) ρ X)
  let i : ι := Classical.choice inferInstance
  have hdii : algebraMap K L (X.val i i) = d := by
    simpa [matrixAdjointInvariantScalarExtension] using
      congrArg (fun Y : Matrix ι ι L => Y i i) hd
  refine ⟨X.val i i, ?_⟩
  ext j k
  apply (algebraMap K L).injective
  have hjk := congrArg (fun Y : Matrix ι ι L => Y j k) hd
  rw [← hdii] at hjk
  by_cases he : j = k
  · simpa [matrixAdjointInvariantScalarExtension, Matrix.smul_apply, he] using hjk
  · simpa [matrixAdjointInvariantScalarExtension, Matrix.smul_apply, he] using hjk

end
end Dubon2026

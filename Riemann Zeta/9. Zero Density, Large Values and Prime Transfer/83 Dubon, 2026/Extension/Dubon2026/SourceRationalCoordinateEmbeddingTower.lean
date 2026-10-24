import Dubon2026.SourceRationalShiftPowerSpan
import Dubon2026.SourceCurvePicardCorrespondence
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.RatFunc.IntermediateField

/-! DUB-17/18 -> reverse genus -> exceptional place fibers.
Embeddings preserving the literal rational coordinate preserve the entire
rational-function base. The existing rational-coordinate embedding and
native finite Galois tower results discharge the extension hypotheses
needed for actual place restriction, in arbitrary characteristic. -/
namespace Dubon2026.SourceCurve
noncomputable section
variable {K F M : Type*} [Field K] [Field F] [Field M]
variable [Algebra K F] [Algebra K M]

theorem ratFunc_algHom_ext (f g : RatFunc K →ₐ[K] M)
    (h : f RatFunc.X = g RatFunc.X) : f = g := by
  have he : f.comp (IntermediateField.adjoin K {RatFunc.X}).val =
      g.comp (IntermediateField.adjoin K {RatFunc.X}).val := by
    apply IntermediateField.adjoin_algHom_ext K
    intro x hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    exact h
  apply AlgHom.ext
  intro x
  have hx : x ∈ IntermediateField.adjoin K ({RatFunc.X} : Set (RatFunc K)) := by
    rw [RatFunc.adjoin_X]
    trivial
  exact congrArg (fun e => e ⟨x, hx⟩) he

variable [Algebra (RatFunc K) M] [IsScalarTower K (RatFunc K) M]

theorem coordinateEmbedding_comp_eq (x : F) (hx : Transcendental K x)
    (ψ : F →ₐ[K] M) (hψ : ψ x = algebraMap (RatFunc K) M RatFunc.X) :
    ψ.comp (rationalCoordinateEmbedding K x hx) =
      IsScalarTower.toAlgHom K (RatFunc K) M := by
  apply ratFunc_algHom_ext
  change ψ (rationalCoordinateEmbedding K x hx RatFunc.X) = _
  rw [rationalCoordinateEmbedding_X]
  exact hψ

theorem finite_galois_along_coordinate
    [FiniteDimensional (RatFunc K) M] [IsGalois (RatFunc K) M]
    (x : F) (hx : Transcendental K x) (ψ : F →ₐ[K] M)
    (hψ : ψ x = algebraMap (RatFunc K) M RatFunc.X) :
    letI := algebraAlong ψ
    FiniteDimensional F M ∧ IsGalois F M := by
  letI := algebraAlong ψ
  letI := algebraAlong (rationalCoordinateEmbedding K x hx)
  haveI : IsScalarTower (RatFunc K) F M :=
    IsScalarTower.of_algebraMap_eq fun r =>
      (congrArg (fun e => e r) (coordinateEmbedding_comp_eq x hx ψ hψ)).symm
  exact ⟨Module.Finite.of_restrictScalars_finite (RatFunc K) F M,
    IsGalois.tower_top_of_isGalois (RatFunc K) F M⟩

end
end Dubon2026.SourceCurve

import Dubon2026.PolarizedPointTopology
import Mathlib.Topology.Homeomorph.Lemmas

/-! The faithful doubled realization respects the source coordinate
topology. For the compact separated coefficient rings used in the CM
deformation problem, the existing compact-embedding theorem identifies
continuous polarized lifts with their genuine continuous matrix lifts.
This is required to reuse the native framed fibers for DUB-17. -/

namespace Dubon2026
open Matrix

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
  [TopologicalSpace R]

/-- The source inverse-transpose operation is continuous in the original matrix-unit topology. -/
theorem polarizedContragredient_continuous :
    Continuous (polarizedContragredient (R := R) (ι := ι)) := by
  apply Units.continuous_iff.mpr
  exact ⟨Units.continuous_coe_inv.matrix_transpose, Units.continuous_val.matrix_transpose⟩

/-- The original scalar-matrix map is continuous. -/
theorem polarizedScalar_continuous :
    Continuous (GeneralLinearGroup.scalar ι (R := R)) := by
  apply Units.continuous_iff.mpr
  exact ⟨(continuous_pi fun _ => Units.continuous_val).matrix_diagonal,
    (continuous_pi fun _ => Units.continuous_coe_inv).matrix_diagonal⟩

/-- The actual block diagonal construction is continuous in both original matrix blocks. -/
theorem polarizedBlockDiagonal_continuous :
    Continuous (fun x : GeneralLinearGroup ι R × GeneralLinearGroup ι R =>
      polarizedBlockDiagonal x.1 x.2) := by
  apply Units.continuous_iff.mpr
  exact ⟨(Units.continuous_val.comp continuous_fst).matrix_fromBlocks continuous_const continuous_const
      (Units.continuous_val.comp continuous_snd),
    (Units.continuous_coe_inv.comp continuous_fst).matrix_fromBlocks continuous_const continuous_const
      (Units.continuous_coe_inv.comp continuous_snd)⟩

variable [IsTopologicalRing R]

/-- The original space and its multiplier-twisted dual give a continuous matrix representation. -/
theorem polarizedIdentityBlockRepresentation_continuous :
    Continuous (polarizedIdentityBlockRepresentation (R := R) (ι := ι)) := by
  exact polarizedBlockDiagonal_continuous.comp
    (continuous_fst.prodMk ((polarizedScalar_continuous.comp continuous_snd).mul
      (polarizedContragredient_continuous.comp continuous_fst)))

/-- The full source polarized representation has continuous original doubled matrices. -/
theorem polarizedBlockRepresentation_continuous :
    Continuous (polarizedBlockRepresentation (R := R) (ι := ι)) := by
  have hc : Continuous (polarizedComponentBlockRepresentation (R := R) (ι := ι)) :=
    continuous_of_discreteTopology
  exact (polarizedIdentityBlockRepresentation_continuous.comp
    (polarizedPointHomeomorph.continuous.fst)).mul
      (hc.comp (polarizedPointHomeomorph.continuous.snd))

/-- Over the original compact separated coefficient ring, polarized points form a compact space. -/
theorem polarizedPoint_compactSpace [CompactSpace R] [T2Space R] :
    CompactSpace (PolarizedGaloisGroup ι R) := by
  letI : CompactSpace (Matrix ι ι R) := inferInstanceAs (CompactSpace (ι → ι → R))
  exact polarizedPointHomeomorph.symm.compactSpace

/-- The faithful matrix realization is a closed embedding in the actual coefficient topology. -/
theorem polarizedBlockRepresentation_isClosedEmbedding
    [CompactSpace R] [T2Space R] [Nonempty ι] [Nontrivial R] :
    Topology.IsClosedEmbedding (polarizedBlockRepresentation (R := R) (ι := ι)) := by
  letI := polarizedPoint_compactSpace (R := R) (ι := ι)
  exact polarizedBlockRepresentation_continuous.isClosedEmbedding polarizedBlockRepresentation_injective

/-- Continuous polarized lifts are exactly the same continuous doubled matrix lifts
over the compact separated coefficient rings used by the native framed construction. -/
theorem continuous_polarized_iff_block [CompactSpace R] [T2Space R] [Nonempty ι] [Nontrivial R]
    {X : Type*} [TopologicalSpace X] (f : X → PolarizedGaloisGroup ι R) :
    Continuous f ↔ Continuous (fun x => polarizedBlockRepresentation (f x)) :=
  (polarizedBlockRepresentation_isClosedEmbedding (R := R) (ι := ι)).isEmbedding.continuous_iff

end Dubon2026

import Dubon2026.PolarizedBlockContinuity

/-! The source polarized target over an actual compact coefficient ring
is a topological group. This reuses the proved faithful matrix embedding
for the continuous CM residual extension required by DUB-17. -/

namespace Dubon2026

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
  [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R] [T2Space R]
  [Nonempty ι] [Nontrivial R]

/-- The original compact polarized coefficient points inherit the genuine continuous group laws. -/
instance polarizedPointIsTopologicalGroup : IsTopologicalGroup (PolarizedGaloisGroup ι R) :=
  (polarizedBlockRepresentation_isClosedEmbedding (R := R) (ι := ι)).isEmbedding.isInducing.topologicalGroup
    polarizedBlockRepresentation

end Dubon2026

import Dubon2026.RepresentationCoordinateGeneration

/-! # Finite type and Noetherianity for original finitely generated groups -/

namespace Dubon2026

noncomputable section

variable {G ι R : Type*} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]

/-- The actual coordinate algebra of the original finitely generated group is finitely generated over the original coefficient ring. -/
theorem representationCoordinateAlgebra_finiteType [Group.FG G] :
    Algebra.FiniteType R (RepresentationCoordinateAlgebra G ι R) := by
  obtain ⟨S, hS, hfin⟩ := Monoid.fg_iff.mp (inferInstance : Monoid.FG G)
  letI := hfin.to_subtype
  refine ⟨Subalgebra.fg_def.mpr ⟨Set.range (fun t : S × ι × ι =>
    representationCoordinateMatrix G ι R t.1.val t.2.1 t.2.2), Set.finite_range _, ?_⟩⟩
  exact representationCoordinateMatrix_generators_adjoin G ι R S hS

/-- The genuine coordinate algebra of the original finitely generated group is Noetherian over a Noetherian coefficient ring. -/
theorem representationCoordinateAlgebra_isNoetherian_of_fg [Group.FG G] [IsNoetherianRing R] :
    IsNoetherianRing (RepresentationCoordinateAlgebra G ι R) := by
  letI := representationCoordinateAlgebra_finiteType (G := G) (ι := ι) (R := R)
  exact Algebra.FiniteType.isNoetherianRing R (RepresentationCoordinateAlgebra G ι R)

end
end Dubon2026

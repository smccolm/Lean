import Dubon2026.SourceFiniteSubfieldIrreducible

/-! DUB-17/18 -> automorphy -> absolute irreducibility of the original residual
symmetric powers. A literal embedded SL₂ lower bound suffices over every
coefficient extension; the residual action and its original group are retained. -/
namespace Dubon2026
noncomputable section
open Matrix

/-- The actual rank-two action with an embedded finite SL₂ subgroup has
irreducible symmetric powers after every extension of coefficients. -/
theorem finiteSubfield_symmetric_absoluteIrreducible
    {G K E L : Type} [Group G] [Field K] [Finite K] [Field E] [Field L]
    [Algebra E L] (q n : ℕ) [Fact q.Prime] [CharP K q]
    (θ : K →+* E) (hn : 2 * n < Nat.card K - 1) (hchar : n < q)
    (ρ : G →* GeneralLinearGroup (Fin 2) E)
    (himage : ((GeneralLinearGroup.map θ).comp
      (SpecialLinearGroup.toGL (n := Fin 2) (R := K))).range ≤ ρ.range) :
    Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L) ((homogeneousSymmetricGL n).comp ρ))) := by
  apply finiteSubfield_matrixRepresentation_irreducible_of_symmetricSL2_image q n
    ((algebraMap E L).comp θ) hn hchar
  rintro x ⟨s, rfl⟩
  obtain ⟨g, hg⟩ := himage (show GeneralLinearGroup.map θ (SpecialLinearGroup.toGL s) ∈
    ((GeneralLinearGroup.map θ).comp SpecialLinearGroup.toGL).range from ⟨s, rfl⟩)
  refine ⟨g, ?_⟩
  change GeneralLinearGroup.map (algebraMap E L) (homogeneousSymmetricGL n (ρ g)) =
    GeneralLinearGroup.map ((algebraMap E L).comp θ)
      (homogeneousSymmetricGL n (SpecialLinearGroup.toGL s))
  rw [hg, ← homogeneousSymmetricGL_map]
  rfl

end
end Dubon2026

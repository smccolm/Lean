import Dubon2026.SourceGammaOneDiagonalHom

/-! DUB-17/18 -> original all-weight adic association -> geometric
finite-cohomology realization -> the actual Gamma1 image is finite index.
The existing raised-level surjection onto the upper Hecke subgroup and
native subgroup index formulas discharge finiteness, without constructing
a new coset enumeration. -/
namespace Dubon2026
noncomputable section
open CongruenceSubgroup

/-- The image of the existing level-raising homomorphism is exactly its
original upper-congruence Hecke subgroup. -/
theorem sourceRaisedLevelConjugation_range (Q N : ℕ) [NeZero N] :
    (sourceRaisedLevelConjugation Q N).range = heckeUpperSubgroup Q N := by
  ext g
  constructor
  · rintro ⟨h, rfl⟩
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mpr
      (sourceRaisedLevelConjugation_upper Q N h)
  · intro hg
    exact sourceRaisedLevelConjugation_surjective_upper Q N ⟨g, hg⟩

/-- Finiteness of the actual raised-level image follows from the already
proved finite upper Hecke subgroup. -/
theorem sourceRaisedLevelConjugation_range_finiteIndex (Q N : ℕ) [NeZero N] :
    (sourceRaisedLevelConjugation Q N).range.FiniteIndex := by
  rw [sourceRaisedLevelConjugation_range]
  exact sourceHeckeUpper_finiteIndex

/-- The concrete Gamma1 diagonal cover has finite-index image in the
original Gamma0 group, as required by coinduction and Shapiro. -/
theorem sourceGammaOneDiagonalHom_range_finiteIndex
    (Q N : ℕ) [NeZero Q] [NeZero N] :
    (sourceGammaOneDiagonalHom Q N).range.FiniteIndex := by
  let H := (Gamma1 (Q * N ^ 2)).subgroupOf (Gamma0 (Q * N))
  letI : H.FiniteIndex := inferInstance
  letI := sourceRaisedLevelConjugation_range_finiteIndex Q N
  have hr : (sourceGammaOneDiagonalHom Q N).range =
      H.map (sourceRaisedLevelConjugation Q N) := by
    rw [sourceGammaOneDiagonalHom, MonoidHom.range_comp, Subgroup.inclusion_range]
  constructor
  rw [hr, Subgroup.index_map_of_injective H (sourceRaisedLevelConjugation_injective Q N)]
  exact mul_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := H))
    (Subgroup.FiniteIndex.index_ne_zero (H := (sourceRaisedLevelConjugation Q N).range))

end
end Dubon2026

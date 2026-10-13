import Dubon2026.FaithfulLocalFieldFixedPoints

/-! # Original local H2 for a faithful cyclic field action

The original fixed field meets every topological hypothesis of the existing
local theorem. Reindexing by the proved actual Galois equivalence preserves
the original unit coefficient and its cohomology. This removes the need for
a base-completion comparison in DUB-17's unrestricted finite-place H2 input.
-/

namespace Dubon2026
noncomputable section
attribute [local instance] Units.mulDistribMulActionRight
variable (G F : Type) [Group G] [Finite G] [IsCyclic G]
  [NontriviallyNormedField F] [IsUltrametricDist F] [LocallyCompactSpace F]
  [MulSemiringAction G F] [FaithfulSMul G F]

/-- The actual local unit H2 is finite, of the original cyclic stabilizer order. -/
theorem faithfulLocalField_second_cohomology_order
    (hnorm : ∀ (g : G) (x : F), ‖g • x‖ = ‖x‖) :
    Finite (groupCohomology (Rep.ofMulDistribMulAction G Fˣ) 2) ∧
      Nat.card (groupCohomology (Rep.ofMulDistribMulAction G Fˣ) 2) = Nat.card G := by
  let E := FixedPoints.subfield G F
  letI : NontriviallyNormedField E := {
    toNormedField := inferInstance
    non_trivial := normPreserving_fixedField_exists_norm_gt_one G F hnorm }
  haveI : LocallyCompactSpace E := (normPreserving_fixedField_isClosed G F hnorm).locallyCompactSpace
  letI : NormedAlgebra E F := {
    toAlgebra := inferInstance
    norm_smul_le := fun a b => (norm_mul (a : F) b).le }
  let e := FixedPoints.toAlgAutMulEquiv G F
  haveI : IsCyclic Gal(F/E) := isCyclic_of_surjective e.toMonoidHom e.surjective
  obtain ⟨hfin, hcard⟩ := normedLocalField_cyclic_second_cohomology_order E F
  let c := (faithfulFieldUnitCohomologyIso G F 2).toLinearEquiv.toEquiv
  haveI := hfin
  refine ⟨Finite.of_equiv _ c, ?_⟩
  exact (Nat.card_congr c.symm).trans (hcard.trans (Nat.card_congr e.symm.toEquiv))

end
end Dubon2026

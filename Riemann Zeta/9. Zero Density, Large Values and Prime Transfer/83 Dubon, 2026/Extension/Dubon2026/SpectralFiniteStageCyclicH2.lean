import Dubon2026.SpectralFiniteStageInvariantRange

/-! # The normalized cyclic computation of every original finite local H2 -/

namespace Dubon2026
noncomputable section

variable (K Ω : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [ValuativeRel K] [(NormedField.valuation (K := K)).Compatible]
  [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- The actual finite-stage invariant and the literal rational cyclic
map have equal images, both computed as the degree annihilator. -/
theorem spectralFiniteStageFullInvariant_range (E : FiniteGaloisIntermediateField K Ω) :
    letI : NeZero (Module.finrank K E) := ⟨Module.finrank_pos.ne'⟩
    (spectralFiniteStageFullInvariant K Ω E).range =
      (rationalCyclicInvariant (Module.finrank K E)).toIntLinearMap.range := by
  haveI : NeZero (Module.finrank K E) := ⟨Module.finrank_pos.ne'⟩
  ext q
  exact (spectralFiniteStageFullInvariant_mem_range_iff K Ω E q).trans
    (rationalCyclicInvariant_mem_range_iff (Module.finrank K E) q).symm

/-- Every original finite Galois local H2, including ramified and
noncyclic field extensions, is canonically cyclic of the actual field
degree. The equivalence is fixed by the proved arithmetic invariant. -/
def spectralFiniteStageH2CyclicEquiv (E : FiniteGaloisIntermediateField K Ω) :
    GaloisUnitH2FiniteStage K Ω E ≃ₗ[ℤ] ZMod (Module.finrank K E) := by
  haveI : NeZero (Module.finrank K E) := ⟨Module.finrank_pos.ne'⟩
  exact ((LinearEquiv.ofInjective (spectralFiniteStageFullInvariant K Ω E)
    (spectralFiniteStageFullInvariant_injective K Ω E)).trans
      (LinearEquiv.ofEq _ _ (spectralFiniteStageFullInvariant_range K Ω E))).trans
        (LinearEquiv.ofInjective
          (rationalCyclicInvariant (Module.finrank K E)).toIntLinearMap
          (rationalCyclicInvariant_injective (Module.finrank K E))).symm

/-- The finite cyclic computation retains the original full invariant,
rather than choosing an arbitrary isomorphism of finite groups. -/
theorem spectralFiniteStageH2CyclicEquiv_invariant
    (E : FiniteGaloisIntermediateField K Ω) (x : GaloisUnitH2FiniteStage K Ω E) :
    letI : NeZero (Module.finrank K E) := ⟨Module.finrank_pos.ne'⟩
    rationalCyclicInvariant (Module.finrank K E) (spectralFiniteStageH2CyclicEquiv K Ω E x) =
      spectralFiniteStageFullInvariant K Ω E x := by
  haveI : NeZero (Module.finrank K E) := ⟨Module.finrank_pos.ne'⟩
  exact LinearEquiv.ofInjective_symm_apply
    (rationalCyclicInvariant (Module.finrank K E)).toIntLinearMap
    (h := rationalCyclicInvariant_injective (Module.finrank K E)) _

/-- The order of the original finite cohomology group is exactly the
degree of its original field extension. -/
theorem spectralFiniteStageH2_card (E : FiniteGaloisIntermediateField K Ω) :
    Nat.card (GaloisUnitH2FiniteStage K Ω E) = Module.finrank K E := by
  haveI : NeZero (Module.finrank K E) := ⟨Module.finrank_pos.ne'⟩
  rw [Nat.card_congr (spectralFiniteStageH2CyclicEquiv K Ω E).toEquiv, Nat.card_eq_fintype_card,
    ZMod.card]

end
end Dubon2026

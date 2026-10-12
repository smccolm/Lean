import Dubon2026.LocalFieldFiniteStageInvariant

/-! # The normalized cyclic computation of every original finite local H2 -/

namespace Dubon2026
noncomputable section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- The actual finite-stage invariant and the literal rational cyclic
map have equal images, both computed as the degree annihilator. -/
theorem localFieldFiniteStageInvariant_range (E : FiniteGaloisIntermediateField K Ω) :
    letI : NeZero (Module.finrank K E) := ⟨Module.finrank_pos.ne'⟩
    (localFieldFiniteStageInvariant K Ω E).range =
      (rationalCyclicInvariant (Module.finrank K E)).toIntLinearMap.range := by
  haveI : NeZero (Module.finrank K E) := ⟨Module.finrank_pos.ne'⟩
  ext q
  exact (localFieldFiniteStageInvariant_mem_range_iff K Ω E q).trans
    (rationalCyclicInvariant_mem_range_iff (Module.finrank K E) q).symm

/-- Every original finite Galois local H2, including ramified and
noncyclic field extensions, is canonically cyclic of the actual field
degree. The equivalence is fixed by the proved arithmetic invariant. -/
def localFieldFiniteStageH2CyclicEquiv (E : FiniteGaloisIntermediateField K Ω) :
    GaloisUnitH2FiniteStage K Ω E ≃ₗ[ℤ] ZMod (Module.finrank K E) := by
  haveI : NeZero (Module.finrank K E) := ⟨Module.finrank_pos.ne'⟩
  exact ((LinearEquiv.ofInjective (localFieldFiniteStageInvariant K Ω E)
    (localFieldFiniteStageInvariant_injective K Ω E)).trans
      (LinearEquiv.ofEq _ _ (localFieldFiniteStageInvariant_range K Ω E))).trans
        (LinearEquiv.ofInjective
          (rationalCyclicInvariant (Module.finrank K E)).toIntLinearMap
          (rationalCyclicInvariant_injective (Module.finrank K E))).symm

/-- The finite cyclic computation retains the original full invariant,
rather than choosing an arbitrary isomorphism of finite groups. -/
theorem localFieldFiniteStageH2CyclicEquiv_invariant
    (E : FiniteGaloisIntermediateField K Ω) (x : GaloisUnitH2FiniteStage K Ω E) :
    letI : NeZero (Module.finrank K E) := ⟨Module.finrank_pos.ne'⟩
    rationalCyclicInvariant (Module.finrank K E) (localFieldFiniteStageH2CyclicEquiv K Ω E x) =
      localFieldFiniteStageInvariant K Ω E x := by
  haveI : NeZero (Module.finrank K E) := ⟨Module.finrank_pos.ne'⟩
  exact LinearEquiv.ofInjective_symm_apply
    (rationalCyclicInvariant (Module.finrank K E)).toIntLinearMap
    (h := rationalCyclicInvariant_injective (Module.finrank K E)) _

/-- The order of the original finite cohomology group is exactly the
degree of its original field extension. -/
theorem localFieldFiniteStageH2_card (E : FiniteGaloisIntermediateField K Ω) :
    Nat.card (GaloisUnitH2FiniteStage K Ω E) = Module.finrank K E := by
  haveI : NeZero (Module.finrank K E) := ⟨Module.finrank_pos.ne'⟩
  rw [Nat.card_congr (localFieldFiniteStageH2CyclicEquiv K Ω E).toEquiv, Nat.card_eq_fintype_card,
    ZMod.card]

end
end Dubon2026

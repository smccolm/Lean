import Dubon2026.FiniteGaloisH2BaseChangeComparison

/-! # The inverse continuous comparison preserves actual finite base change

Use the existing same-cocycle square and its proved equivalences. The
inverse form is needed to apply normalized local invariants to the
algebraic idele localization in DUB-17's auxiliary-class total formula.
-/
namespace Dubon2026
noncomputable section

/-- Converting an actual algebraic base-change class to continuous H2 is exactly the actual continuous base change. -/
theorem continuousDiscreteH2Equiv_symm_finiteGaloisBaseChange
    (K E L M : Type) [Field K] [Field E] [Field L] [Field M]
    [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
    [IsScalarTower K E M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional E M] [IsGalois K L] [IsGalois E M]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits E M)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits E M)]
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) :
    (continuousDiscreteH2Equiv (Rep.ofAlgebraAutOnUnits E M)
      (discreteGaloisUnitAction_continuous (K := E) (Ω := M))).symm
      (groupCohomology.map (galoisBaseChangeRestriction K E L M)
        (galoisUnitBaseChangeInclusion K E L M) 2 x) =
    finiteGaloisUnitBaseChangeH2 K E L M
      ((continuousDiscreteH2Equiv (Rep.ofAlgebraAutOnUnits K L)
        (discreteGaloisUnitAction_continuous (K := K) (Ω := L))).symm x) := by
  let eL := continuousDiscreteH2Equiv (Rep.ofAlgebraAutOnUnits K L)
    (discreteGaloisUnitAction_continuous (K := K) (Ω := L))
  let eM := continuousDiscreteH2Equiv (Rep.ofAlgebraAutOnUnits E M)
    (discreteGaloisUnitAction_continuous (K := E) (Ω := M))
  apply eM.injective
  rw [eM.apply_symm_apply]
  have h := continuousDiscreteH2Equiv_finiteGaloisBaseChange K E L M (eL.symm x)
  change eM (finiteGaloisUnitBaseChangeH2 K E L M (eL.symm x)) =
    groupCohomology.map _ _ 2 (eL (eL.symm x)) at h
  rw [eL.apply_symm_apply] at h
  exact h.symm

end
end Dubon2026

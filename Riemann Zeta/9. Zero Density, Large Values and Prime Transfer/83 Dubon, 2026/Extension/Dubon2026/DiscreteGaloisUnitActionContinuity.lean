import Dubon2026.ContinuousInfiniteGaloisUnitH1

/-! # The actual Krull-topological action on original discrete unit coefficients -/

namespace Dubon2026
noncomputable section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- The actual Krull-topological Galois action on the original discrete unit
coefficients is jointly continuous. Each original unit stabilizer equals the
stabilizer of its original field value, which is open by algebraicity. -/
theorem discreteGaloisUnitAction_continuous [Algebra.IsIntegral K Ω] :
    Continuous (fun z : Gal(Ω/K) × Rep.ofAlgebraAutOnUnits K Ω =>
      (Rep.ofAlgebraAutOnUnits K Ω).ρ z.1 z.2) := by
  letI : TopologicalSpace Ωˣ :=
    inferInstanceAs (TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω))
  letI : DiscreteTopology Ωˣ :=
    inferInstanceAs (DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω))
  letI : ContinuousSMul Gal(Ω/K) Ωˣ :=
    (continuousSMul_iff_stabilizer_isOpen).mpr (by
      intro u
      have he : (MulAction.stabilizer Gal(Ω/K) u : Set Gal(Ω/K)) =
          (MulAction.stabilizer Gal(Ω/K) (u : Ω) : Set Gal(Ω/K)) := by
        ext g
        change g • u = u ↔ g (u : Ω) = (u : Ω)
        constructor
        · intro h
          exact congrArg Units.val h
        · intro h
          exact Units.ext h
      rw [he]
      exact stabilizer_isOpen_of_isIntegral (K := K) (u : Ω))
  exact (show Continuous (fun z : Gal(Ω/K) × Ωˣ => z.1 • z.2) from continuous_smul)

/-- The original discrete-coefficient continuous Galois unit H1 vanishes with
its action-continuity premise discharged by the original Krull topology. -/
theorem discreteInfiniteGaloisUnitH1_eq_zero [IsGalois K Ω]
    (x : ContinuousRepresentationH1 (Rep.ofAlgebraAutOnUnits K Ω)
      (discreteGaloisUnitAction_continuous (K := K) (Ω := Ω))) : x = 0 := by
  exact continuousInfiniteGaloisUnitH1_eq_zero
    (discreteGaloisUnitAction_continuous (K := K) (Ω := Ω)) x

end
end Dubon2026

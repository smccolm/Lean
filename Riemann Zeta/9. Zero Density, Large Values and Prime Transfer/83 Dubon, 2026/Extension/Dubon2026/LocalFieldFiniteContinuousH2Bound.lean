import Dubon2026.LocalFieldFiniteGaloisSecondCohomologyBound
import Dubon2026.ContinuousDiscreteH2Comparison
import Dubon2026.GaloisUnitFiniteStageInflation

/-! # The original continuous finite-stage local H2 order bound -/

namespace Dubon2026
noncomputable section

/-- The same actual cocycle comparison transports the proved local H2
bound to the original continuous Galois-unit H2 quotient. The discrete
coefficient topology is the one used in continuous Galois cohomology. -/
theorem localField_finite_continuous_h2_card_dvd
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [FiniteDimensional K L] [IsGalois K L]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)] :
    Finite (GaloisUnitContinuousH2 (K := K) (Ω := L)) ∧
      Nat.card (GaloisUnitContinuousH2 (K := K) (Ω := L)) ∣ Module.finrank K L := by
  obtain ⟨hfinite, hdvd⟩ := localField_finite_galois_second_cohomology_card_dvd K L
  haveI := hfinite
  let e := continuousDiscreteH2Equiv (Rep.ofAlgebraAutOnUnits K L)
    (discreteGaloisUnitAction_continuous (K := K) (Ω := L))
  refine ⟨Finite.of_equiv _ e.symm.toEquiv, ?_⟩
  rw [Nat.card_congr e.toEquiv]
  rwa [IsGalois.card_aut_eq_finrank K L] at hdvd

end
end Dubon2026

import Dubon2026.LocalFieldFiniteH2BaseChangeKilling
import Dubon2026.FiniteGaloisH2BaseChangeComparison

/-! # Degree killing for the original algebraic finite local H2

The proved continuous/discrete equivalence retains the original cocycles.
It transports actual finite local killing to the algebraic H2 used by
original global localization. This removes a topology interface premise
from DUB-17's cyclic killing and invariant sum-zero dependency.
-/
namespace Dubon2026
noncomputable section

/-- Degree-dividing base change kills the actual algebraic finite local-unit H2 class. -/
theorem localFieldAlgebraicH2_baseChange_zero_of_degree_dvd
    (K E L M : Type) [Field K] [CharZero K] [Field E] [Field L] [Field M]
    [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
    [IsScalarTower K E M] [IsScalarTower K L M]
    [FiniteDimensional K E] [FiniteDimensional K L] [FiniteDimensional E M]
    [IsGalois K L] [IsGalois E M]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (q : ℕ) (hq : q ∣ Module.finrank K E)
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) (hx : q • x = 0) :
    groupCohomology.map (galoisBaseChangeRestriction K E L M)
      (galoisUnitBaseChangeInclusion K E L M) 2 x = 0 := by
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K L) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K L) := ⟨rfl⟩
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits E M) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits E M) := ⟨rfl⟩
  let e := continuousDiscreteH2Equiv (Rep.ofAlgebraAutOnUnits K L)
    (discreteGaloisUnitAction_continuous (K := K) (Ω := L))
  let y := e.symm x
  have hy : q • y = 0 := by
    change q • e.symm x = 0
    rw [← map_nsmul, hx, map_zero]
  have hkill := localFieldFiniteH2_baseChange_zero_of_degree_dvd K E L M q hq y hy
  have h := continuousDiscreteH2Equiv_finiteGaloisBaseChange K E L M y
  rw [hkill, map_zero] at h
  change 0 = groupCohomology.map (galoisBaseChangeRestriction K E L M)
    (galoisUnitBaseChangeInclusion K E L M) 2 (e (e.symm x)) at h
  rw [e.apply_symm_apply] at h
  exact h.symm

end
end Dubon2026

import Dubon2026.LocalFieldActualFiniteBaseChangeKilling
import Dubon2026.OriginalFiniteGaloisContinuousInflation
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Actual finite local H2 classes are killed by degree-dividing base change

A common algebraic closure is constructed. Literal inflation is injective
for the original finite coefficient field, and actual base-change
composition compares its class with the full local invariant calculation.
This supplies the finite-completion killing obligation for DUB-17's
constructed cyclic cyclotomic stage without a closure or comparison premise.
-/
namespace Dubon2026
noncomputable section

/-- In characteristic zero, a degree-dividing base extension kills the original finite local-unit H2 class in every actual common finite extension. -/
theorem localFieldFiniteH2_baseChange_zero_of_degree_dvd
    (K E L M : Type) [Field K] [CharZero K] [Field E] [Field L] [Field M]
    [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
    [IsScalarTower K E M] [IsScalarTower K L M]
    [FiniteDimensional K E] [FiniteDimensional K L] [FiniteDimensional E M]
    [IsGalois K L] [IsGalois E M]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits E M)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits E M)]
    (q : ℕ) (hq : q ∣ Module.finrank K E)
    (x : GaloisUnitContinuousH2 (K := K) (Ω := L)) (hx : q • x = 0) :
    finiteGaloisUnitBaseChangeH2 K E L M x = 0 := by
  letI : FiniteDimensional K M := FiniteDimensional.trans K E M
  let Ω := AlgebraicClosure M
  haveI : CharZero M := Algebra.charZero_of_charZero K M
  haveI : CharZero E := Algebra.charZero_of_charZero K E
  haveI : Algebra.IsAlgebraic K Ω := Algebra.IsAlgebraic.trans K M Ω
  haveI : IsGalois K Ω := { }
  haveI : IsGalois E Ω := IsGalois.tower_top_of_isGalois K E Ω
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω) := ⟨rfl⟩
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω) := ⟨rfl⟩
  let y := continuousGaloisUnitBaseChangeH2 K K L Ω x
  have hy : q • y = 0 := by
    change q • continuousGaloisUnitBaseChangeH2 K K L Ω x = 0
    rw [← map_nsmul, hx, map_zero]
  have hkill := localFieldContinuousH2_baseChange_zero_of_degree_dvd K E Ω q hq y hy
  apply originalFiniteGalois_continuousH2Inflation_injective E M Ω
  rw [map_zero]
  change continuousGaloisUnitBaseChangeH2 E E M Ω
    (continuousGaloisUnitBaseChangeH2 K E L M x) = 0
  rw [continuousGaloisUnitBaseChangeH2_comp K E E L M Ω,
    ← continuousGaloisUnitBaseChangeH2_comp K K E L Ω Ω]
  exact hkill

end
end Dubon2026

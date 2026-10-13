import Dubon2026.LocalFieldContinuousInvariantFiniteRestriction
import Dubon2026.GaloisUnitBaseChangeComposition

/-! # Actual finite base change kills degree-dividing local H2 torsion

For DUB-17's constructed cyclotomic stage, only vanishing is needed.
The actual finite field is identified with its image in the same closure;
existing normalized invariant scaling applies there. The already proved
literal base-change composition then gives vanishing on the original
field, avoiding a separate normalized-invariant transport theorem.
-/
namespace Dubon2026
noncomputable section
open scoped ValuativeRel

/-- A finite extension whose actual degree is divisible by an annihilator kills the original continuous local-unit H2 class under literal base change. -/
theorem localFieldContinuousH2_baseChange_zero_of_degree_dvd
    (K E Ω : Type) [Field K] [Field E] [Field Ω]
    [Algebra K E] [Algebra K Ω] [Algebra E Ω] [IsScalarTower K E Ω]
    [FiniteDimensional K E] [IsGalois K Ω] [IsSepClosed Ω]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω)]
    (q : ℕ) (hq : q ∣ Module.finrank K E)
    (x : GaloisUnitContinuousH2 (K := K) (Ω := Ω)) (hx : q • x = 0) :
    letI : IsGalois E Ω := IsGalois.tower_top_of_isGalois K E Ω
    continuousGaloisUnitBaseChangeH2 K E Ω Ω x = 0 := by
  letI : IsGalois E Ω := IsGalois.tower_top_of_isGalois K E Ω
  let φ := IsScalarTower.toAlgHom K E Ω
  let F : IntermediateField K Ω := φ.fieldRange
  let e : E ≃ₐ[K] F := AlgEquiv.ofInjective φ φ.injective
  letI : FiniteDimensional K F := Module.Finite.equiv e.toLinearEquiv
  letI : Algebra F E := e.symm.toRingHom.toAlgebra
  letI : IsScalarTower F E Ω := IsScalarTower.of_algebraMap_eq' (by
    ext y
    change y.val = (e (e.symm y)).val
    rw [e.apply_symm_apply])
  letI : IsGalois F Ω := IsGalois.tower_top_of_isGalois K F Ω
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits F Ω) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits F Ω) := ⟨rfl⟩
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  letI : NontriviallyNormedField K := localFieldOriginalNorm K
  haveI : IsUltrametricDist K := localFieldOriginalNorm_isUltrametric K
  haveI : CompleteSpace K := localFieldOriginalNorm_complete K
  haveI : (NormedField.valuation (K := K)).Compatible := localFieldOriginalNorm_compatible K
  letI : NontriviallyNormedField F := spectralNorm.nontriviallyNormedField K F
  letI : NormedAlgebra K F := spectralNorm.normedAlgebra K F
  letI : IsUltrametricDist F := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel F := ValuativeRel.ofValuation (NormedField.valuation (K := F))
  haveI : IsNonarchimedeanLocalField F := spectralFiniteExtension_isNonarchimedeanLocalField K F
  haveI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation F) :=
    spectralValuation_hasExtension K F
  have hkill : continuousGaloisUnitBaseChangeH2 K F Ω Ω x = 0 := by
    apply (localFieldContinuousH2InvariantEquiv F Ω).injective
    rw [map_zero, localFieldContinuousH2InvariantEquiv_finite_restriction]
    have hd : Module.finrank K F = Module.finrank K E := e.toLinearEquiv.finrank_eq.symm
    obtain ⟨m, hm⟩ := hq
    rw [hd, hm, mul_nsmul, ← map_nsmul, hx, map_zero, smul_zero]
  rw [← continuousGaloisUnitBaseChangeH2_comp K F E Ω Ω Ω x, hkill, map_zero]

end
end Dubon2026

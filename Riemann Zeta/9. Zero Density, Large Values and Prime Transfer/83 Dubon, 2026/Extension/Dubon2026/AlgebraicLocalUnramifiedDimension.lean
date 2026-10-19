import Dubon2026.AlgebraicLocalInertiaCyclicity
import Dubon2026.AlgebraicLocalInertiaDepth
import Dubon2026.NormLocalResidueFinite
import Dubon2026.ContinuousUnramifiedDimension
import Dubon2026.LocalFieldFiniteCoefficientH1

/-! The actual local unramified H1 dimension for the original finite
prime-field representation. Local compactness, actual residue Frobenius,
proved inertia quotient cyclicity/depth and native H1 finiteness discharge
all arithmetic inputs of the finite-inflation dimension comparison.
This supplies DUB-17's unramified local dimension input; the original
modular representation and local deformation-condition consumers remain. -/

namespace Dubon2026
noncomputable section

variable (K L : Type) [NontriviallyNormedField K] [NormedField L]
  [NormedAlgebra K L] [IsUltrametricDist K] [IsUltrametricDist L] [CompleteSpace K]
  [LocallyCompactSpace K] [IsGalois K L] [IsAlgClosed L] [CharZero L]
  (q : ℕ) [Fact q.Prime] (A : Rep (ZMod q) Gal(L/K))
  [FiniteDimensional (ZMod q) A] [TopologicalSpace A] [DiscreteTopology A]
  [ContinuousSMul (ZMod q) A]
  (hA : Continuous (fun z : Gal(L/K) × A => A.ρ z.1 z.2))

/-- The original continuous inertia-restriction kernel has exactly the
original invariant dimension. Frobenius, cyclicity, quotient depth, residue
finiteness and local H1 finiteness are proved from the actual local field. -/
theorem algebraicLocal_unramified_finrank_eq_invariants :
    Module.finrank (ZMod q) (continuousRepresentationH1Restriction A hA
      (algebraicLocalInertia K L).subtype continuous_subtype_val).ker =
      Module.finrank (ZMod q) A.ρ.invariants := by
  letI : Finite A := Module.finite_of_finite (ZMod q)
  letI : ValuativeRel K := ValuativeRel.ofValuation (NormedField.valuation (K := K))
  letI : IsNonarchimedeanLocalField K := normValuation_isNonarchimedeanLocalField K
  have hq : (q : K) ≠ 0 := by
    intro hz
    have hzL : (q : L) = 0 := by
      simpa only [map_natCast, map_zero] using congrArg (algebraMap K L) hz
    exact (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero) hzL
  letI : Finite (ContinuousRepresentationH1 A hA) := localField_finiteCoefficientH1 K L q A hA hq
  letI : FiniteDimensional (ZMod q) (ContinuousRepresentationH1 A hA) := Module.Finite.of_finite
  letI : Finite (IsLocalRing.ResidueField (algebraicLocalIntegerRing K)) := normLocal_residue_finite K
  obtain ⟨φ, hφ⟩ := algebraicLocal_exists_residueFrobenius K L
  exact continuous_unramified_finrank_eq_invariants_of_cyclic_depth A hA
    (algebraicLocalInertia K L) q φ
    (algebraicLocal_frobenius_generates_inertia_quotient K L φ hφ)
    (algebraicLocal_exists_inertia_quotient_card_dvd K L)

end
end Dubon2026

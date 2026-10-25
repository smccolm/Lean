import Dubon2026.SourceModularPrincipalDivisorCharts
import Dubon2026.SourceModularPrimePicardInjectivity

/-! DUB-17/18 -> original Picard inertia -> arithmetic compatibility of
the actual reduction map. Retain the two chart specifications on the same
constant reduction whose Picard map is injective on invertible torsion.
Both wild genus cases and the tame case discharge genus equality. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open SourceCurve SourceCurve.RegularProlongation
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N : ℕ) [NeZero N]
local notation "kk" => IsLocalRing.ResidueField A
local notation "FF" => modularFunctionFieldCoeff N Qbar
local notation "Fb" => modularFunctionFieldCoeff N kk
attribute [local instance] residueModularAlgebra residueConstantsClosed

theorem exists_modular_constant_reduction_with_charts_of_prime
    (p : ℕ) [CharP kk p] (hp : p.Prime) (hNk : (N : kk) ≠ 0) :
    let hNQ : (N : Qbar) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    ∃ R : ConstantReduction A FF Fb,
      R.toRegularProlongation = modularRegularProlongation A N hNQ hNk ∧
      genusFF kk Fb = genusFF Qbar FF ∧
      (∀ P Q, jCoeff N kk ∈ Q.toValuationSubring →
        (R.placeMap P = Q ↔ ChartDomain A P (jCoeff N Qbar) ∧
          ChartReducesTo A R.toRegularProlongation (jCoeff N Qbar) P Q)) ∧
      (∀ P Q, jCoeff N kk ∉ Q.toValuationSubring →
        (R.placeMap P = Q ↔ ChartDomain A P (jCoeff N Qbar)⁻¹ ∧
          ChartReducesTo A R.toRegularProlongation (jCoeff N Qbar)⁻¹ P Q)) ∧
      ∀ m : ℕ, (m : kk) ≠ 0 →
        Set.InjOn R.pic0Map (↑(Pic0.torsion (K := Qbar) (F := FF) m)) := by
  dsimp only
  have hgen : genusFF kk Fb = genusFF Qbar FF :=
    (modular_residue_genusFF_eq_originalGenus_of_prime A N p hp hNk).trans
      (coefficient_genusFF_eq_originalGenus N).symm
  let hNQ : (N : Qbar) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  letI hFdim : FiniteDimensional (IntermediateField.adjoin Qbar {jCoeff N Qbar}) FF :=
    finiteDimensional_coeff_field N Qbar
  letI hFbdim : FiniteDimensional (IntermediateField.adjoin kk {jCoeff N kk}) Fb :=
    finiteDimensional_coeff_field N kk
  obtain ⟨r, hr₁, hr₂, hr⟩ :=
    exists_modular_principal_divisor_reduction_map_with_charts_of_genus_eq A N hNk hgen
  let R : ConstantReduction A FF Fb := ConstantReduction.ofPlaceMap
    (modularRegularProlongation A N hNQ hNk) r
    (fun P => place_residue_bijective_of_finite_coordinate (jCoeff N Qbar) P)
    (fun Q => place_residue_bijective_of_finite_coordinate (jCoeff N kk) Q) hr
  refine ⟨R, rfl, hgen, hr₁, hr₂, fun m hm x hx y hy hxy => ?_⟩
  apply sub_eq_zero.mp
  apply modular_pic0_eq_zero_of_torsion_of_genus_eq A N hNk hgen R rfl m hm (x - y)
  · rw [nsmul_sub, Pic0.mem_torsion_iff.mp hx, Pic0.mem_torsion_iff.mp hy, sub_self]
  · rw [map_sub, hxy, sub_self]

end
end Dubon2026.SourceFunctionField.GaussReduction

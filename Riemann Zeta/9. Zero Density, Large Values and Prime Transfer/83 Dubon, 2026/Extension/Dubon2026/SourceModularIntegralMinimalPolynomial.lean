import Dubon2026.SourceReductionMinimalPolynomial
import Dubon2026.SourceModularReductionDimension

/-! DUB-17/18 -> original Frobenius/inertia -> actual good reduction ->
genus comparison -> pole-bound preservation. Integral coordinates make every
actual Gauss-ring element integral over the intersection with the rational j
field. If it is also integral over the polynomial j chart, the coefficients
of its actual chart minimal polynomial lie in the Gauss valuation ring.
The modular consumer derives the prolongation and all coordinate degrees;
no quantification over valuation extensions remains. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
variable {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L) (N : ℕ) [NeZero N]
local notation "FF" => modularFunctionFieldCoeff N L
local notation "kk" => IsLocalRing.ResidueField A
attribute [local instance] residueModularAlgebra

theorem isIntegral_modular_j_intersection (hNL : (N : L) ≠ 0) (hNk : (N : kk) ≠ 0)
    (f : gaussRing A N) :
    IsIntegral ↥((IntermediateField.adjoin L ({jCoeff N L} : Set FF)).toSubfield.toSubring ⊓
      (gaussRing A N).toSubring : Subring FF) (f : FF) := by
  let R := modularRegularProlongation A N hNL hNk
  let x : R.integers := ⟨jCoeff N L, jCoeff_mem_gaussRing A N⟩
  have hres : R.residue x = jCoeff N kk := modularResidueHom_jCoeff A N hNL hNk
  apply SourceCurve.RegularProlongation.isIntegral_coordinate_intersection R x
  · rw [hres]
    exact transcendental_jCoeff N kk
  · rw [hres]
    exact (reduction_coordinate_degree A N hNL hNk).2
  · rw [hres]
    exact (reduction_coordinate_degree A N hNL hNk).1

theorem modular_j_minpoly_coeff_mem_gaussRing (hNL : (N : L) ≠ 0) (hNk : (N : kk) ≠ 0)
    (f : gaussRing A N) (hint : IsIntegral (Algebra.adjoin L ({jCoeff N L} : Set FF)) (f : FF))
    (i : ℕ) :
    (((minpoly (Algebra.adjoin L ({jCoeff N L} : Set FF)) (f : FF)).coeff i :
      Algebra.adjoin L ({jCoeff N L} : Set FF)) : FF) ∈ gaussRing A N := by
  let R := modularRegularProlongation A N hNL hNk
  let x : R.integers := ⟨jCoeff N L, jCoeff_mem_gaussRing A N⟩
  have hres : R.residue x = jCoeff N kk := modularResidueHom_jCoeff A N hNL hNk
  apply SourceCurve.RegularProlongation.coe_minpoly_adjoin_coeff_mem_integers R x _ _ _ f hint i
  · rw [hres]
    exact transcendental_jCoeff N kk
  · rw [hres]
    exact (reduction_coordinate_degree A N hNL hNk).2
  · rw [hres]
    exact (reduction_coordinate_degree A N hNL hNk).1

end
end Dubon2026.SourceFunctionField.GaussReduction

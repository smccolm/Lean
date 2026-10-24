import Dubon2026.SourceReductionIntegralFiberEquality
import Dubon2026.SourceModularCoefficientCurve
import Dubon2026.SourceModularTameReductionPlaceMap

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> higher symmetric-power
continuation -> automorphy and residual association -> original weight-two
Frobenius/inertia -> modular good reduction -> principal-divisor pushforward.
For the actual tame modular reduction map, every integral j-chart function
with nonzero reduction satisfies the exact finite-j fiber-order identity.
Principal-divisor existence, separability, coordinate degree equality,
chart lifting and both map-fiber descriptions are derived from actual
modular results. Denominator clearing and the inverse-chart application
are still required for the full principal-divisor identity. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open SourceCurve SourceCurve.RegularProlongation
open scoped Classical
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N : ℕ) [NeZero N]
local notation "kk" => IsLocalRing.ResidueField A
local notation "FF" => modularFunctionFieldCoeff N Qbar
local notation "Fb" => modularFunctionFieldCoeff N kk
attribute [local instance] residueModularAlgebra residueConstantsClosed

theorem exists_modular_reduction_map_with_integral_fiber_identity
    (p : ℕ) [CharP kk p] (hp : 5 ≤ p) (hNk : (N : kk) ≠ 0) :
    let hNQ : (N : Qbar) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    let R := modularRegularProlongation A N hNQ hNk
    ∃ r : Place Qbar FF → Place kk Fb,
      (∀ P Q, jCoeff N kk ∈ Q.toValuationSubring →
        (r P = Q ↔ ChartDomain A P (jCoeff N Qbar) ∧
          ChartReducesTo A R (jCoeff N Qbar) P Q)) ∧
      (∀ P Q, jCoeff N kk ∉ Q.toValuationSubring →
        (r P = Q ↔ ChartDomain A P (jCoeff N Qbar)⁻¹ ∧
          ChartReducesTo A R (jCoeff N Qbar)⁻¹ P Q)) ∧
      ∀ (f : gaussRing A N), IsIntegral (Algebra.adjoin Qbar {jCoeff N Qbar}) (f : FF) →
        modularResidueHom A N hNQ hNk f ≠ 0 →
        ∀ (D : Divisor Qbar FF), (∀ P, D P = P.ord (f : FF)) →
        ∀ Q : Place kk Fb, jCoeff N kk ∈ Q.toValuationSubring →
          (∑ P ∈ D.support.filter (fun P => r P = Q), D P) =
            Q.ord (modularResidueHom A N hNQ hNk f) := by
  classical
  dsimp only
  letI hPF : HasPrincipalDivisors Qbar FF := hasPrincipalDivisors_coeff_field N Qbar
  letI hPb : HasPrincipalDivisors kk Fb := hasPrincipalDivisors_coeff_field N kk
  let hNQ : (N : Qbar) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  let R := modularRegularProlongation A N hNQ hNk
  let x : R.integers := ⟨jCoeff N Qbar, jCoeff_mem_gaussRing A N⟩
  have hres : R.residue x = jCoeff N kk := modularResidueHom_jCoeff A N hNQ hNk
  have hx : Transcendental kk (R.residue x) := by
    rw [hres]
    exact transcendental_jCoeff N kk
  haveI : Algebra.IsSeparable (IntermediateField.adjoin kk ({R.residue x} : Set Fb)) Fb := by
    rw [hres]
    exact isSeparable_coeff_field N kk
  have hfin : 0 < Module.finrank (IntermediateField.adjoin kk ({R.residue x} : Set Fb)) Fb := by
    rw [hres]
    exact (reduction_coordinate_degree A N hNQ hNk).2
  have hdeg : Module.finrank (IntermediateField.adjoin Qbar ({(x : FF)} : Set FF)) FF =
      Module.finrank (IntermediateField.adjoin kk ({R.residue x} : Set Fb)) Fb := by
    rw [hres]
    exact (reduction_coordinate_degree A N hNQ hNk).1
  have hchart : ∀ g : Fb, IsIntegral (Algebra.adjoin kk {R.residue x}) g →
      ∃ f : R.integers, IsIntegral (Algebra.adjoin Qbar {(x : FF)}) (f : FF) ∧ R.residue f = g := by
    intro g hg
    rw [hres] at hg
    exact (modular_integral_charts_lift_of_five_le A N p hp hNk).1 g hg
  obtain ⟨r, hr₁, hr₂⟩ := exists_modular_reduction_place_map_of_five_le A N p hp hNk
  refine ⟨r, hr₁, hr₂, ?_⟩
  intro f hfi hf D hD Q hQ
  apply sum_fiber_orders_eq_residue_order_of_integral_chart R x hx hfin hdeg hchart f hfi hf Q
    (hres ▸ hQ) D hD (D.support.filter fun P => r P = Q)
  intro P
  simp only [Finset.mem_filter, Finsupp.mem_support_iff, hr₁ P Q hQ]
  rfl

end
end Dubon2026.SourceFunctionField.GaussReduction

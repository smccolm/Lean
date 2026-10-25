import Dubon2026.SourceOriginalInertiaChartTransport
import Dubon2026.SourceModularConstantReductionCharts

/-! DUB-17/18 -> original Picard inertia -> modular reduction.
The actual modular reduction is invariant under the original arithmetic
inertia action on places. Its proved chart descriptions and transported
chart conditions discharge compatibility; the same reduction retains genus
preservation and injectivity on every invertible Picard torsion subgroup.
Descent to the original Picard action and Tate module remains subsequent. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open SourceCurve SourceCurve.RegularProlongation
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N : ℕ) [NeZero N]
local notation "kk" => IsLocalRing.ResidueField A
local notation "FF" => modularFunctionFieldCoeff N Qbar
local notation "Fb" => modularFunctionFieldCoeff N kk
attribute [local instance] residueModularAlgebra residueConstantsClosed

theorem exists_modular_reduction_invariant_on_original_places
    (p : ℕ) [CharP kk p] (hp : p.Prime) (hNk : (N : kk) ≠ 0) :
    let hNQ : (N : Qbar) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    ∃ R : ConstantReduction A FF Fb,
      R.toRegularProlongation = modularRegularProlongation A N hNQ hNk ∧
      genusFF kk Fb = genusFF Qbar FF ∧
      (∀ m : ℕ, (m : kk) ≠ 0 →
        Set.InjOn R.pic0Map (↑(Pic0.torsion (K := Qbar) (F := FF) m))) ∧
      ∀ τ : Qbar ≃ₐ[ℚ] Qbar,
        τ ∈ (A.inertiaSubgroup ℚ).map (A.decompositionSubgroup ℚ).subtype →
        ∀ P : Place Qbar (modularFunctionFieldOver N Qbar),
          R.placeMap (originalCoefficientPlaceEquiv N (originalArithmeticPlace N τ P)) =
            R.placeMap (originalCoefficientPlaceEquiv N P) := by
  dsimp only
  obtain ⟨R, hR, hgen, h₁, h₂, hinj⟩ :=
    exists_modular_constant_reduction_with_charts_of_prime A N p hp hNk
  refine ⟨R, hR, hgen, hinj, ?_⟩
  intro τ hτ P
  obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hτ
  rw [← coefficientArithmeticPlace_original]
  let P' := originalCoefficientPlaceEquiv N P
  let Q := R.placeMap P'
  have htransport (y : FF) (hy : coefficientArithmeticRingAut N d.val.symm y = y)
      (h : ChartDomain A P' y ∧ ChartReducesTo A R.toRegularProlongation y P' Q) :
      ChartDomain A (coefficientArithmeticPlace N d.val P') y ∧
        ChartReducesTo A R.toRegularProlongation y (coefficientArithmeticPlace N d.val P') Q := by
    refine ⟨chartDomain_coefficientArithmeticPlace A N d P' y hy h.1, ?_⟩
    rw [hR] at h ⊢
    exact chartReducesTo_coefficientArithmeticPlace A N hNk d hd P' Q y hy h.2
  by_cases hQ : jCoeff N kk ∈ Q.toValuationSubring
  · exact (h₁ _ Q hQ).mpr (htransport _ (coefficientArithmeticRingAut_j N d.val.symm)
      ((h₁ P' Q hQ).mp rfl))
  · apply (h₂ _ Q hQ).mpr
    apply htransport _ _ ((h₂ P' Q hQ).mp rfl)
    rw [map_inv₀, coefficientArithmeticRingAut_j]

end
end Dubon2026.SourceFunctionField.GaussReduction

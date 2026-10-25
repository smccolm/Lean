import Dubon2026.SourceDecompositionChartTransport
import Dubon2026.SourceModularConstantReductionCharts

/-! DUB-17/18 -> original Frobenius/Picard compatibility -> the same
actual modular reduction on places. Both exact chart descriptions combine
with the transported original and residue actions. All-prime genus and
Picard injectivity remain properties of this same constructed reduction. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open SourceCurve SourceCurve.RegularProlongation
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N : ℕ) [NeZero N]
local notation "kk" => IsLocalRing.ResidueField A
local notation "FF" => modularFunctionFieldCoeff N Qbar
local notation "Fb" => modularFunctionFieldCoeff N kk
attribute [local instance] residueModularAlgebra residueConstantsClosed

theorem exists_modular_reduction_decomposition_equivariant
    (p : ℕ) [CharP kk p] (hp : p.Prime) (hNk : (N : kk) ≠ 0) :
    let hNQ : (N : Qbar) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    ∃ R : ConstantReduction A FF Fb,
      R.toRegularProlongation = modularRegularProlongation A N hNQ hNk ∧
      genusFF kk Fb = genusFF Qbar FF ∧
      (∀ m : ℕ, (m : kk) ≠ 0 →
        Set.InjOn R.pic0Map (↑(Pic0.torsion (K := Qbar) (F := FF) m))) ∧
      ∀ (d : A.decompositionSubgroup ℚ) (P : Place Qbar (modularFunctionFieldOver N Qbar)),
        R.placeMap (originalCoefficientPlaceEquiv N (originalArithmeticPlace N d.val P)) =
          residueCoefficientPlace N kk (MulSemiringAction.toRingAut (A.decompositionSubgroup ℚ) kk d)
            (R.placeMap (originalCoefficientPlaceEquiv N P)) := by
  dsimp only
  obtain ⟨R, hR, hgen, h₁, h₂, hinj⟩ :=
    exists_modular_constant_reduction_with_charts_of_prime A N p hp hNk
  refine ⟨R, hR, hgen, hinj, ?_⟩
  intro d P
  rw [← coefficientArithmeticPlace_original]
  let P' := originalCoefficientPlaceEquiv N P
  let Q := R.placeMap P'
  let e := MulSemiringAction.toRingAut (A.decompositionSubgroup ℚ) kk d
  let Q' := residueCoefficientPlace N kk e Q
  have htransport (y : FF) (hy : coefficientArithmeticRingAut N d.val.symm y = y)
      (h : ChartDomain A P' y ∧ ChartReducesTo A R.toRegularProlongation y P' Q) :
      ChartDomain A (coefficientArithmeticPlace N d.val P') y ∧
        ChartReducesTo A R.toRegularProlongation y (coefficientArithmeticPlace N d.val P') Q' := by
    refine ⟨chartDomain_coefficientArithmeticPlace A N d P' y hy h.1, ?_⟩
    rw [hR] at h ⊢
    exact chartReducesTo_decomposition A N hNk d P' Q y hy h.2
  have hQiff : jCoeff N kk ∈ Q'.toValuationSubring ↔ jCoeff N kk ∈ Q.toValuationSubring :=
    residueCoefficientPlace_j_mem N kk e Q
  by_cases hQ : jCoeff N kk ∈ Q.toValuationSubring
  · exact (h₁ _ Q' (hQiff.mpr hQ)).mpr
      (htransport _ (coefficientArithmeticRingAut_j N d.val.symm) ((h₁ P' Q hQ).mp rfl))
  · apply (h₂ _ Q' (fun h => hQ (hQiff.mp h))).mpr
    apply htransport _ _ ((h₂ P' Q hQ).mp rfl)
    rw [map_inv₀, coefficientArithmeticRingAut_j]

theorem exists_modular_reduction_arithmeticFrobenius_equivariant
    (p : ℕ) [Fact p.Prime] [CharP kk p] (hNk : (N : kk) ≠ 0) :
    let hNQ : (N : Qbar) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    ∃ R : ConstantReduction A FF Fb,
      R.toRegularProlongation = modularRegularProlongation A N hNQ hNk ∧
      genusFF kk Fb = genusFF Qbar FF ∧
      (∀ m : ℕ, (m : kk) ≠ 0 →
        Set.InjOn R.pic0Map (↑(Pic0.torsion (K := Qbar) (F := FF) m))) ∧
      ∀ τ : Qbar ≃ₐ[ℚ] Qbar,
        (∃ hτ : τ ∈ A.decompositionSubgroup ℚ,
          ∀ a : kk, (⟨τ, hτ⟩ : A.decompositionSubgroup ℚ) • a = a ^ p) →
        ∀ P : Place Qbar (modularFunctionFieldOver N Qbar),
          R.placeMap (originalCoefficientPlaceEquiv N (originalArithmeticPlace N τ P)) =
            residueCoefficientPlace N kk (frobeniusEquiv kk p)
              (R.placeMap (originalCoefficientPlaceEquiv N P)) := by
  obtain ⟨R, hR, hgen, hinj, hplace⟩ :=
    exists_modular_reduction_decomposition_equivariant A N p Fact.out hNk
  refine ⟨R, hR, hgen, hinj, ?_⟩
  intro τ hτ P
  obtain ⟨hd, hF⟩ := hτ
  let d : A.decompositionSubgroup ℚ := ⟨τ, hd⟩
  have he : MulSemiringAction.toRingAut (A.decompositionSubgroup ℚ) kk d = frobeniusEquiv kk p := by
    ext a
    exact hF a
  simpa only [he] using hplace d P

end
end Dubon2026.SourceFunctionField.GaussReduction

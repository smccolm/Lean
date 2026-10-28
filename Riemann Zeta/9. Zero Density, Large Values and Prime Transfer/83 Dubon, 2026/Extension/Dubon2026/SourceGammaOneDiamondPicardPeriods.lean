import Dubon2026.SourceGammaOneDiamondEndpoint
import Dubon2026.SourceGammaOnePicardPeriodEquiv

/-! DUB-17/18 -> original all-weight association -> arithmetic Gamma1
diamond/Picard comparison. The original Picard-period equivalence
intertwines the independently constructed field diamond and the native
dual slash diamond. The actual moving lemma discharges representatives;
native Tate-torus naturality then gives the integral period tensor action.
Arithmetic constant-field naturality and Galois compatibility remain.
-/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open SourceCurve CongruenceSubgroup SourceWeightTwoJacobi
variable (M : ℕ) [NeZero M] (g : Gamma0 M) (hT : ModularGroup.T ∈ Gamma1 M)
local notation "FC" => functionFieldOver (Gamma1 M) ℂ
local notation "Λ" => sourceWeightTwoIntegralLattice (Gamma1 M)

theorem picardPeriodEquiv_diamond (x : Pic0 ℂ FC) :
    picardPeriodEquiv M hT (complexDiamondPicard M g x) =
      periodQuotientDiamond M g (picardPeriodEquiv M hT x) := by
  have he (c : analyticDegree.ker) :
      picardPeriodEquiv M hT (analyticPicardHom M hT c) = analyticPeriodHom M c :=
    picardPeriodEquiv_analytic_divisor M hT c
  obtain ⟨c, rfl⟩ := analyticPicardHom_surjective M hT x
  rw [← analyticPicardHom_diamond M g hT, he, he, analyticPeriodHom_diamond]

theorem complexPicardTatePeriodQuotient_diamond (p : ℕ) [Fact p.Prime]
    (x : TateModule p (Pic0 ℂ FC)) :
    TateModule.ofAddEquiv p (picardPeriodEquiv M hT)
        (TateModule.tateMap p (complexDiamondPicard M g).toAddMonoidHom x) =
      TateModule.tateMap p (periodQuotientDiamond M g).toAddMonoidHom
        (TateModule.ofAddEquiv p (picardPeriodEquiv M hT) x) := by
  apply Subtype.ext
  funext k
  exact picardPeriodEquiv_diamond M g hT ((x : ℕ → Pic0 ℂ FC) k)

theorem complexPicardTatePeriodTensorEquiv_diamond (p : ℕ) [Fact p.Prime]
    (x : TateModule p (Pic0 ℂ FC)) :
    complexPicardTatePeriodTensorEquiv M p hT
        (TateModule.tateMap p (complexDiamondPicard M g).toAddMonoidHom x) =
      (periodLatticeDiamond M g).baseChange ℤ_[p]
        (complexPicardTatePeriodTensorEquiv M p hT x) := by
  apply (TateModule.Period.phi2 ℂ p Λ (integralPeriodBasis M)).injective
  rw [periodTateTensor_diamond]
  simp only [complexPicardTatePeriodTensorEquiv, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  exact complexPicardTatePeriodQuotient_diamond M g hT p x

end
end Dubon2026.SourceFunctionField.GammaOne

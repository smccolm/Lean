import Dubon2026.SourceOriginalCoefficientPlaceAction
import Dubon2026.SourceReductionChartGluing
import Dubon2026.SourceModularReductionDimension

/-! DUB-17/18 -> original Picard inertia -> actual reduction-place
invariance. Native inertia fixes coefficient residues, the original place
action transports nonunits, and the proved arithmetic chart action
transports integral equations. Together these preserve the exact chart
reduction condition; no place-map or Picard invariance is assumed. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open SourceCurve SourceCurve.RegularProlongation
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N : ℕ)
local notation "kk" => IsLocalRing.ResidueField A
local notation "F" => modularFunctionFieldCoeff N Qbar
local notation "Fb" => modularFunctionFieldCoeff N kk
attribute [local instance] residueModularAlgebra

theorem residue_inertia_smul (d : A.decompositionSubgroup ℚ)
    (hd : d ∈ A.inertiaSubgroup ℚ) (a : A) :
    IsLocalRing.residue A (d • a) = IsLocalRing.residue A a := by
  rw [IsLocalRing.ResidueField.residue_smul]
  have h1 := MonoidHom.mem_ker.mp hd
  have h2 := congrArg (fun e : RingAut kk => e (IsLocalRing.residue A a)) h1
  simpa using h2

theorem chartDomain_coefficientArithmeticPlace (d : A.decompositionSubgroup ℚ)
    (P : Place Qbar F) (y : F)
    (hy : coefficientArithmeticRingAut N d.val.symm y = y)
    (hP : ChartDomain A P y) :
    ChartDomain A (coefficientArithmeticPlace N d.val P) y := by
  obtain ⟨a, ha⟩ := hP
  refine ⟨d • a, (nonunit_coefficientArithmeticPlace_iff N d.val P _).mpr ?_⟩
  rw [map_sub, hy, coefficientArithmeticRingAut_constants]
  change y - algebraMap Qbar F (d.val.symm (d.val a)) ∈ P.toValuationSubring.nonunits
  simpa only [AlgEquiv.symm_apply_apply] using ha

theorem chartReducesTo_coefficientArithmeticPlace [NeZero N]
    (hNk : (N : kk) ≠ 0) (d : A.decompositionSubgroup ℚ)
    (hd : d ∈ A.inertiaSubgroup ℚ) (P : Place Qbar F) (Q : Place kk Fb)
    (y : F) (hy : coefficientArithmeticRingAut N d.val.symm y = y)
    (hP : ChartReducesTo A
      (modularRegularProlongation A N (Nat.cast_ne_zero.mpr (NeZero.ne N)) hNk) y P Q) :
    ChartReducesTo A
      (modularRegularProlongation A N (Nat.cast_ne_zero.mpr (NeZero.ne N)) hNk) y
      (coefficientArithmeticPlace N d.val P) Q := by
  intro f hf a ha
  have hd' : d⁻¹ ∈ A.inertiaSubgroup ℚ := (A.inertiaSubgroup ℚ).inv_mem hd
  let f' := inertiaGaussHom A N d⁻¹ hd' f
  have hf' : IsIntegral (Algebra.adjoin Qbar {y}) (f' : F) :=
    coefficientArithmeticRingAut_isIntegral N d.val.symm y hy hf
  have ha' : (f' : F) - algebraMap Qbar F (d⁻¹ • a) ∈ P.toValuationSubring.nonunits := by
    have h := (nonunit_coefficientArithmeticPlace_iff N d.val P _).mp ha
    rw [map_sub, coefficientArithmeticRingAut_constants] at h
    exact h
  have h := hP f' hf' (d⁻¹ • a) ha'
  change modularResidueHom A N (Nat.cast_ne_zero.mpr (NeZero.ne N)) hNk f' -
    algebraMap kk Fb (IsLocalRing.residue A (d⁻¹ • a)) ∈ Q.toValuationSubring.nonunits at h
  rw [residue_inertia_smul A d⁻¹ hd'] at h
  have hr := inertiaGaussHom_modularResidue A N hNk d⁻¹ hd' f
  change modularResidueHom A N (Nat.cast_ne_zero.mpr (NeZero.ne N)) hNk f' = _ at hr
  rw [hr] at h
  exact h

end
end Dubon2026.SourceFunctionField.GaussReduction

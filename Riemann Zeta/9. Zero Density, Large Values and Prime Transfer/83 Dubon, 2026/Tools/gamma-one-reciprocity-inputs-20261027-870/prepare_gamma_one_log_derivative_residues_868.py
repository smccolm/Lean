from pathlib import Path
import json,hashlib
p=Path(__file__).parent
body=r"""import SourceComplexLogDerivativeResidues
import SourceWeightTwoPeriodUntwist
import Dubon2026.SourceGammaOneExactRamification

/-! DUB-17/18 -> original all-weight arithmetic association -> original
Gamma1 Picard/H1 -> Abel-Jacobi converse -> analytic reciprocity.
The original divisor and its actual ramification-weighted meromorphic
orders supply the exact compact-support residue sum. The holomorphic
multiplier is the existing normalized endpoint primitive of a real cusp
form object, not an independently supplied primitive or residue formula. -/
namespace Dubon2026
noncomputable section
open UpperHalfPlane MeasureTheory Filter CongruenceSubgroup Matrix.SpecialLinearGroup
open SourceCurve SourceFunctionField SourceFunctionField.GammaOne SourcePeriodUntwist
open scoped MatrixGroups Topology

theorem sourceGamma1_logDerivative_residue_integral (N : ℕ) [NeZero N]
    (hT : ModularGroup.T ∈ Gamma1 N)
    (D : Divisor ℂ (functionFieldOver (Gamma1 N) ℂ)) (F : ℍ → ℂ)
    (hF : ∀ τ : ℍ, MeromorphicAt (F ∘ ofComplex) (τ : ℂ))
    (ho : ∀ τ : ℍ, meromorphicOrderAt (F ∘ ofComplex) (τ : ℂ) =
      (((analyticRamification hT τ : ℤ) * D (analyticPlace hT τ) : ℤ) : WithTop ℤ))
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) 2)
    (h : ℂ → ℂ) (hh : ContDiff ℝ 1 h) (hsupp : HasCompactSupport h)
    (hU : tsupport h ⊆ upperHalfPlaneSet) :
    ∫ z : ℂ, Ek g z * (deriv (F ∘ ofComplex) z / F (ofComplex z)) *
      ((fderiv ℝ h z 1 + Complex.I * fderiv ℝ h z Complex.I) / 2) =
      -(Real.pi : ℂ) * ∑ᶠ a : ℂ,
        (((analyticRamification hT (ofComplex a) : ℤ) *
          D (analyticPlace hT (ofComplex a)) : ℤ) : ℂ) * Ek g a * h a := by
  have hm : ∀ z ∈ upperHalfPlaneSet, MeromorphicAt (F ∘ ofComplex) z := by
    intro z hz
    exact hF ⟨z, hz⟩
  have hf : ∀ z ∈ upperHalfPlaneSet, meromorphicOrderAt (F ∘ ofComplex) z ≠ ⊤ := by
    intro z hz
    rw [ho ⟨z, hz⟩]
    exact WithTop.coe_ne_top
  have hi := SourceComplexReciprocity.LogDerivStokes.integral_mul_logDeriv_mul_dbar
    upperHalfPlaneSet isOpen_upperHalfPlaneSet (F ∘ ofComplex) hm hf
    (Ek g) (differentiableOn_Ek g) h hh hsupp hU
  change _ = -(Real.pi : ℂ) * _ at hi
  rw [hi]
  congr 1
  apply finsum_congr
  intro a
  by_cases ha : 0 < a.im
  · have he : ((ofComplex a : ℍ) : ℂ) = a := ofComplex_apply_of_im_pos ha
    have ho' := ho (ofComplex a)
    rw [he] at ho'
    simp [ho']
  · have hz : h a = 0 := image_eq_zero_of_notMem_tsupport (fun ht => ha (hU ht))
    simp [hz]

end
end Dubon2026
"""
with (p/'SourceGammaOneLogDerivativeResidues.lean').open('x',encoding='utf-8',newline='\n') as f:f.write(body)
r={'gate':'DUB-17/18','chain':['all-weight arithmetic association','original Gamma1 coefficient Hecke realization','Picard/H1','Abel-Jacobi converse','analytic reciprocity','actual original-divisor compact-support residue identity'],'reuseChecked':[{'path':str(p/'SourceWeightTwoPeriodUntwist.lean'),'sha256':hashlib.sha256((p/'SourceWeightTwoPeriodUntwist.lean').read_bytes()).hexdigest().upper(),'review':'Audited normalized endpoint primitive and its actual holomorphicity reused. Exact original field, analytic place, ramification and finite order formula retained.'}],'assumptionsToDischarge':['actual finite orders imply local residue identity','existing actual cusp-form endpoint primitive supplies holomorphic multiplier','sum uses original divisor coefficients and exact ramification, with outside-upper-half-plane terms vanishing by actual support'],'remaining':'Actual F, exact divisor orders and compact test support are explicit inputs. The theorem does not construct F from Abel-Jacobi. Modular winding/period/Petersson comparison, original principal-divisor converse and entire all-weight arithmetic chain remain.'}
with (p/'gamma-one-log-derivative-residues-route-868.json').open('x',encoding='utf-8') as f:json.dump(r,f,indent=2)

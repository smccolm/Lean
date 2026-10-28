from pathlib import Path
import json,hashlib
s=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
body=r"""import Dubon2026.SourceWeightTwoEndpointPeriods
import Dubon2026.SourceWeightTwoPrimitiveCusps

/-! DUB-17/18 -> original all-weight association -> original Gamma1 Picard/H1
-> Abel-Jacobi converse -> analytic reciprocity -> invariant untwisting.
Use the existing normalized primitive and cusp limits directly; no new
path integral or primitive-existence premise is needed. -/
namespace Dubon2026.SourcePeriodUntwist
noncomputable section
open UpperHalfPlane Filter Matrix.SpecialLinearGroup
open scoped MatrixGroups Topology

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]

/-- Complex-coordinate endpoint primitive with the actual period normalization. -/
def Ek (k : CuspForm (Γ.map (mapGL ℝ)) 2) (z : ℂ) : ℂ :=
  sourceWeightTwoAlong Γ UpperHalfPlane.I (ofComplex z) k

theorem Ek_hasDerivAt (k : CuspForm (Γ.map (mapGL ℝ)) 2) {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (Ek k) (k (ofComplex z)) z := by
  have h := sourceWeightTwoPrimitive_hasDerivAt k
    (Γ.map (mapGL ℝ)).strictWidthInfty_pos
    (Γ.map (mapGL ℝ)).strictWidthInfty_mem_strictPeriods (ofComplex z)
  rw [ofComplex_apply_of_im_pos hz] at h
  exact h.sub_const _

theorem Ek_smul (k : CuspForm (Γ.map (mapGL ℝ)) 2) (γ : Γ) (τ : ℍ) :
    Ek k (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ) =
      Ek k τ + sourceWeightTwoPeriodValue Γ k γ := by
  simp only [Ek, ofComplex_apply, sourceWeightTwoAlong_apply]
  rw [sourceWeightTwoPrimitive_period Γ k γ τ]
  ring

theorem Ek_exists_cusp_limit (k : CuspForm (Γ.map (mapGL ℝ)) 2) (σ : SL(2, ℤ)) :
    ∃ L : ℂ, Tendsto (fun τ : ℍ => Ek k ((σ • τ : ℍ) : ℂ)) atImInfty (𝓝 L) := by
  obtain ⟨L, hL⟩ := sourceWeightTwoPrimitive_exists_cusp_limit k
    (Γ.map (mapGL ℝ)).strictWidthInfty_pos
    (Γ.map (mapGL ℝ)).strictWidthInfty_mem_strictPeriods σ
  refine ⟨L - sourceWeightTwoPrimitive (Γ.map (mapGL ℝ)).strictWidthInfty k UpperHalfPlane.I, ?_⟩
  simpa only [Ek, ofComplex_apply, sourceWeightTwoAlong_apply] using hL.sub_const
    (sourceWeightTwoPrimitive (Γ.map (mapGL ℝ)).strictWidthInfty k UpperHalfPlane.I)

theorem differentiableOn_Ek (k : CuspForm (Γ.map (mapGL ℝ)) 2) :
    DifferentiableOn ℂ (Ek k) upperHalfPlaneSet :=
  fun _ hz => (Ek_hasDerivAt k hz).differentiableAt.differentiableWithinAt

theorem analyticAt_Ek (k : CuspForm (Γ.map (mapGL ℝ)) 2) {z : ℂ} (hz : 0 < z.im) :
    AnalyticAt ℂ (Ek k) z :=
  (differentiableOn_Ek k).analyticAt (isOpen_upperHalfPlaneSet.mem_nhds hz)

/-- The unit-modulus factor that cancels the actual real-period multiplier. -/
def R (k : CuspForm (Γ.map (mapGL ℝ)) 2) (z : ℂ) : ℂ :=
  Complex.exp (-(2 * Real.pi * Complex.I) * ((Ek k z).re : ℂ))

theorem R_ne_zero (k : CuspForm (Γ.map (mapGL ℝ)) 2) (z : ℂ) :
    R k z ≠ 0 := Complex.exp_ne_zero _

theorem norm_R (k : CuspForm (Γ.map (mapGL ℝ)) 2) (z : ℂ) :
    ‖R k z‖ = 1 := by
  rw [R, Complex.norm_exp]
  simp

theorem multiplier_mul_R_smul (k : CuspForm (Γ.map (mapGL ℝ)) 2) (γ : Γ) (τ : ℍ) :
    Complex.exp (2 * Real.pi * Complex.I * ((sourceWeightTwoPeriodValue Γ k γ).re : ℂ)) *
      R k (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ) = R k τ := by
  rw [R, R, Ek_smul k γ τ, ← Complex.exp_add]
  congr 1
  simp only [Complex.add_re]
  push_cast
  ring

theorem hasFDerivAt_R (k : CuspForm (Γ.map (mapGL ℝ)) 2) {z : ℂ} (hz : 0 < z.im) :
    HasFDerivAt (R k) (R k z • (-(2 * Real.pi * Complex.I) •
      (Complex.ofRealCLM.comp (Complex.reCLM.comp (k (ofComplex z) • (1 : ℂ →L[ℝ] ℂ)))))) z := by
  have h1 : HasFDerivAt (Ek k) (k (ofComplex z) • (1 : ℂ →L[ℝ] ℂ)) z :=
    (Ek_hasDerivAt k hz).complexToReal_fderiv
  have h2 : HasFDerivAt (fun w => ((Ek k w).re : ℂ))
      (Complex.ofRealCLM.comp (Complex.reCLM.comp (k (ofComplex z) • (1 : ℂ →L[ℝ] ℂ)))) z :=
    Complex.ofRealCLM.hasFDerivAt.comp z (Complex.reCLM.hasFDerivAt.comp z h1)
  exact (h2.const_mul (-(2 * Real.pi * Complex.I))).cexp

theorem fderiv_R_apply (k : CuspForm (Γ.map (mapGL ℝ)) 2)
    {z : ℂ} (hz : 0 < z.im) (v : ℂ) :
    fderiv ℝ (R k) z v =
      R k z * (-(2 * Real.pi * Complex.I) * ((k (ofComplex z) * v).re : ℂ)) := by
  rw [(hasFDerivAt_R k hz).fderiv]
  simp [smul_eq_mul]

theorem contDiffAt_R (k : CuspForm (Γ.map (mapGL ℝ)) 2) {z : ℂ} (hz : 0 < z.im) :
    ContDiffAt ℝ 1 (R k) z := by
  have h1 : ContDiffAt ℝ 1 (Ek k) z :=
    ((analyticAt_Ek k hz).contDiffAt (n := 1)).restrict_scalars ℝ
  have h2 : ContDiffAt ℝ 1 (fun w => ((Ek k w).re : ℂ)) z :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp z (Complex.reCLM.contDiff.contDiffAt.comp z h1)
  exact Complex.contDiff_exp.contDiffAt.comp z (contDiffAt_const.mul h2)

end
end Dubon2026.SourcePeriodUntwist
"""
with (s/'SourceWeightTwoPeriodUntwist.lean').open('x',encoding='utf-8',newline='\n') as f:f.write(body)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest().upper()
inputs=[r/'SourceWeightTwoEndpointPeriods.lean',r/'SourceWeightTwoPeriods.lean',r/'SourceWeightTwoPrimitiveCusps.lean',s/'gamma-one-reciprocity-reuse-848/S_ModularCurve_exists_invariant_untwist_of_multiplier_eq_exp_periodOf.lean.txt']
route=dict(chain='DUB17 Theorem 2.6 / DUB18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> original finite homogeneous-coefficient Gamma1 Hecke characters -> Picard/H1, Hecke, diamond, full/parabolic and transpose comparisons -> Abel-Jacobi principal-divisor converse -> analytic reciprocity -> invariant untwisting.',reuseChecked=[dict(path=str(p),sha256=sha(p)) for p in inputs],shorterRoute='Use actual normalized endpoint primitives, existing Eichler derivative and every translated cusp limit. Replace the primary repeated segment FTC and primitive-existence proof. Use native meromorphic normal forms for the next regularization dependency instead of introducing the primary limUnder regularization.',assumptionsToDischarge='Derive the untwisting factor, its nonvanishing, norm, transformation and real derivatives from the actual cusp form. These feed the invariant meromorphic local model, its cusp behavior and the analytic reciprocity identity.',remaining='Invariant normalized meromorphic local models, cusp derivative decay, analytic reciprocity and meromorphic construction from the actual Abel-Jacobi condition remain. No higher gate closes; 16/20, DUB17--20 OPEN.',externalClosureBuilt=False)
with (s/'gamma-one-period-untwist-route-849.json').open('x',encoding='utf-8') as f:json.dump(route,f,indent=2);f.write('\n')
print('Prepared actual period untwisting from existing primitives.')

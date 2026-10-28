from pathlib import Path
import json,hashlib
p=Path(r'E:\Lean\.tmp\dubon83')
src=p/'anthropic-flt-residual-closure-20261020/P2M/Sol/S_FLT_Gamma0FundamentalSet_tendsto_integral_mul_smoothedFundamental.lean.txt'
s=src.read_text(encoding='utf-8-sig')
b=s[s.index('theorem integral_plane_eq_integral_uhp'):s.index('theorem tendsto_integral_HT')]
b=b.replace('hT Γ T','smoothedFundamental Γ T')
a="""theorem smooth_eq_zero_of_im_nonpos {T : ℝ} {z : ℂ} (hz : ¬ 0 < z.im) :
    smoothedFundamental Γ T z = 0 :=
  image_eq_zero_of_notMem_tsupport fun h =>
    hz (SourceSmoothedFundamental.tsupport_subset Γ T h)

"""
b=b.replace('hT_eq_zero_of_im_nonpos','smooth_eq_zero_of_im_nonpos')
c="""theorem tendsto_integral_plane (hΓ : (-1 : SL(2, ℤ)) ∈ Γ)
    (P : ℍ → ℂ) (hP : ∀ γ ∈ Γ, ∀ τ : ℍ, P (γ • τ) = P τ)
    (hPm : AEStronglyMeasurable P volume) (hPi : IntegrableOn P (closedDomain Γ) volume) :
    Tendsto (fun T : ℝ => ∫ z : ℂ, P (ofComplex z) *
      (((z.im ^ 2)⁻¹ * smoothedFundamental Γ T z : ℝ) : ℂ)) atTop
      (𝓝 ((1 / 2 : ℂ) * ∫ τ in closedDomain Γ, P τ)) := by
  simp_rw [integral_plane_eq_integral_uhp]
  exact tendsto_integral_smooth Γ hΓ P hP hPm hPi

"""
head="""import SourceModularSmoothIntegralLimit

/-! Exact source planar/hyperbolic conversion and the smoothed integral limit.
DUB-17/18 -> original Gamma1 Picard/H1 -> Abel-Jacobi converse -> analytic
reciprocity. The coordinate conversion is adapted from the frozen Apache-2.0
anthropics/fermats-last-theorem source
S_FLT_Gamma0FundamentalSet_tendsto_integral_mul_smoothedFundamental.
The bespoke finite tiling argument is replaced by the existing local generic
projective fundamental domain, native unfolding and proved two-element fibers.
The original subgroup, closed coset domain and factor 1/2 are retained. -/
namespace Dubon2026.SourceSmoothedUnfolding
noncomputable section
open UpperHalfPlane hiding I
open Filter Complex Set MeasureTheory SourceSmoothedFundamental
open scoped MatrixGroups Topology NNReal ENNReal
variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]

"""
with (p/'SourceModularSmoothPlaneIntegral.lean').open('x',encoding='utf-8') as f:f.write(head+a+b+c+'end\nend Dubon2026.SourceSmoothedUnfolding\n')
with (p/'smooth-native-unfolding-route-883.json').open('x',encoding='utf-8') as f:json.dump(dict(primary=dict(path=str(src),sha256=hashlib.sha256(src.read_bytes()).hexdigest().upper(),read='Definitions, all initial cutoff/mass/measure-conversion/dominated-convergence proofs, declaration inventory and final theorem read. The unused bespoke finite-tiling proof was not fully read or copied.'),shorterRoute='Native measurable tsum replaces the ENNReal measurability construction; existing CongruenceTraceDomain supplies the projective fundamental domain; native linear/nonlinear unfolding plus exact two-element projection fibers replaces bespoke finite-tile enumeration. Existing fd_ae_eq_fdo proves the literal closed-domain transfer.',chain=['DUB-17/18','original all-weight arithmetic association','original Gamma1 Picard/H1','Abel-Jacobi converse','analytic reciprocity','winding/Petersson comparison','source-normalized smoothed invariant integral limit'],remaining='Winding-period limit and actual smooth comparison local model, analytic reciprocity, original principal-divisor converse and full all-weight arithmetic chain. 16/20; DUB-17--20 OPEN.'),f,indent=2)

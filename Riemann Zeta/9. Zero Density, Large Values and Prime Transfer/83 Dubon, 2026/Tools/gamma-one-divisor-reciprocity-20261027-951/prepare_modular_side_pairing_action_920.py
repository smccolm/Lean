from pathlib import Path
import json,hashlib
p=Path(r'E:\Lean\.tmp\dubon83')
src=p/'anthropic-flt-residual-closure-20261020/P2M/Sol/S_ModularCurve_gammaFundamentalSet_boundary_sidePairing_of_slash_eq_add.lean.txt'
t=src.read_text(encoding='utf-8')
def block(a,b):return t[t.index(a):t.index(b)]
header='''import Mathlib

/-! DUB-17/18 -> original all-weight arithmetic association -> Gamma1 Picard/H1
-> Abel-Jacobi converse -> analytic reciprocity -> winding-period integral ->
modular boundary side pairing. Use the native weight-two slash action and the
literal Quotient.out representatives. This replaces the source's additional
denominator-cocycle/slash definitions and arbitrary-section infrastructure.
Adapted from pinned Apache-2.0 anthropics/fermats-last-theorem source.
No pairing identity or boundary integrability is assumed in these action facts. -/
namespace Dubon2026.SourceModularSidePairing
noncomputable section
open UpperHalfPlane Complex MeasureTheory
open scoped MatrixGroups ModularForm
variable {Γ : Subgroup SL(2, ℤ)}

/-- Actual subgroup transition at the fixed source coset representatives. -/
def pairElt (Γ : Subgroup SL(2, ℤ)) (g : SL(2, ℤ)) (q : SL(2, ℤ) ⧸ Γ) : SL(2, ℤ) :=
  (Quotient.out (g • q))⁻¹ * g * Quotient.out q

theorem pairElt_mem (g : SL(2, ℤ)) (q : SL(2, ℤ) ⧸ Γ) :
    pairElt Γ g q ∈ Γ := by
  have h : (QuotientGroup.mk (Quotient.out (g • q)) : SL(2, ℤ) ⧸ Γ) =
      QuotientGroup.mk (g * Quotient.out q) := by
    rw [QuotientGroup.out_eq']
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  rw [pairElt, mul_assoc]
  exact QuotientGroup.eq.mp h

theorem inv_mul_eq_pairElt (g : SL(2, ℤ)) (q : SL(2, ℤ) ⧸ Γ) :
    (Quotient.out (g • q))⁻¹ * g = pairElt Γ g q * (Quotient.out q)⁻¹ := by
  simp [pairElt, mul_assoc]

theorem sum_comp_smul [Fintype (SL(2, ℤ) ⧸ Γ)]
    (g : SL(2, ℤ)) (f : SL(2, ℤ) ⧸ Γ → ℂ) : ∑ q, f (g • q) = ∑ q, f q :=
  Fintype.sum_equiv (MulAction.toPerm g) _ _ fun _ => rfl

/-- Native weight-two slash pullback in complex coordinates. -/
def tilePull (φ : ℍ → ℂ) (σ : SL(2, ℤ)) (z : ℂ) : ℂ :=
  (φ ∣[(2 : ℤ)] σ) (ofComplex z)

theorem slash_tile_pair (φ : ℍ → ℂ) (g : SL(2, ℤ)) (q : SL(2, ℤ) ⧸ Γ) :
    (φ ∣[(2 : ℤ)] (Quotient.out (g • q))⁻¹) ∣[(2 : ℤ)] g =
      (φ ∣[(2 : ℤ)] pairElt Γ g q) ∣[(2 : ℤ)] (Quotient.out q)⁻¹ := by
  rw [← SlashAction.slash_mul, ← SlashAction.slash_mul, inv_mul_eq_pairElt]

theorem slash_T_apply (φ : ℍ → ℂ) (τ : ℍ) :
    (φ ∣[(2 : ℤ)] ModularGroup.T) τ = φ (ModularGroup.T • τ) := by
  simp [ModularForm.SL_slash_apply, ModularGroup.T, denom]

theorem slash_S_apply (φ : ℍ → ℂ) (τ : ℍ) :
    (φ ∣[(2 : ℤ)] ModularGroup.S) τ = φ (ModularGroup.S • τ) / (τ : ℂ) ^ 2 := by
  simp [ModularForm.SL_slash_apply, ModularGroup.S, denom, zpow_neg, div_eq_mul_inv]

'''
geom=block('theorem T_smul_coe','theorem tilePull_T_pt')
# ray_pt_im is merely an unused source convenience; omit it.
a=geom.index('theorem ray_pt_im');b=geom.index('theorem T_smul_leftRay')
geom=geom[:a]+geom[b:]
tp='''theorem tilePull_T_pt (φ : ℍ → ℂ) (q : SL(2, ℤ) ⧸ Γ) {y : ℝ} (hy : 0 < y) :
    tilePull φ (Quotient.out (ModularGroup.T • q))⁻¹ (1 / 2 + y * Complex.I) =
      tilePull (φ ∣[(2 : ℤ)] pairElt Γ ModularGroup.T q) (Quotient.out q)⁻¹
        (-(1 / 2) + y * Complex.I) := by
  have h := congrFun (slash_tile_pair φ ModularGroup.T q)
    (ofComplex (-(1 / 2) + y * Complex.I))
  simpa only [slash_T_apply, T_smul_leftRay hy, tilePull] using h

'''
arc=block('theorem exp_arc_im_pos','theorem tilePull_S_pt')
sp='''theorem tilePull_S_pt (φ : ℍ → ℂ) (q : SL(2, ℤ) ⧸ Γ) {θ : ℝ} (h1 : 0 < θ) (h2 : θ < Real.pi) :
    tilePull φ (Quotient.out (ModularGroup.S • q))⁻¹ (Complex.exp (↑(Real.pi - θ) * Complex.I)) =
      tilePull (φ ∣[(2 : ℤ)] pairElt Γ ModularGroup.S q) (Quotient.out q)⁻¹
        (Complex.exp (θ * Complex.I)) * Complex.exp (θ * Complex.I) ^ 2 := by
  have h := congrFun (slash_tile_pair φ ModularGroup.S q)
    (ofComplex (Complex.exp (θ * Complex.I)))
  rw [slash_S_apply, S_smul_arc h1 h2, ofComplex_apply_of_im_pos (exp_arc_im_pos h1 h2)] at h
  change tilePull φ (Quotient.out (ModularGroup.S • q))⁻¹
      (Complex.exp (↑(Real.pi - θ) * Complex.I)) / Complex.exp (θ * Complex.I) ^ 2 =
      tilePull (φ ∣[(2 : ℤ)] pairElt Γ ModularGroup.S q) (Quotient.out q)⁻¹
        (Complex.exp (θ * Complex.I)) at h
  exact (div_eq_iff (pow_ne_zero 2 (Complex.exp_ne_zero _))).mp h

theorem tilePull_eq_div (φ : ℍ → ℂ) (σ : SL(2, ℤ)) (z : ℂ) :
    tilePull φ σ z = φ (σ • ofComplex z) / denom (σ : GL (Fin 2) ℝ) (ofComplex z) ^ 2 := by
  simp only [tilePull, ModularForm.SL_slash_apply, zpow_neg, zpow_ofNat, div_eq_mul_inv]

theorem tilePull_add_mul (φ ψ : ℍ → ℂ) (a : ℂ) (σ : SL(2, ℤ)) (z : ℂ) :
    tilePull (fun w => φ w + a * ψ w) σ z = tilePull φ σ z + a * tilePull ψ σ z := by
  simp only [tilePull_eq_div]
  ring

theorem slash_eq_of_twist {φ ψ : ℍ → ℂ} {c : SL(2, ℤ) → ℂ}
    (hφ : ∀ γ ∈ Γ, ∀ τ : ℍ, φ (γ • τ) / denom (γ : GL (Fin 2) ℝ) τ ^ 2 = φ τ + c γ * ψ τ)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Γ) :
    φ ∣[(2 : ℤ)] γ = fun w => φ w + c γ * ψ w := by
  funext w
  simpa only [ModularForm.SL_slash_apply, zpow_neg, zpow_ofNat, div_eq_mul_inv] using hφ γ hγ w

end
end Dubon2026.SourceModularSidePairing
'''
out=header+geom+tp+arc+sp
with (p/'SourceModularSidePairingAction.lean').open('x',encoding='utf-8',newline='\n') as f:f.write(out)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
r=Path(r'E:\Lean\Riemann Zeta')
route=dict(chain='DUB-17/18 -> all-weight arithmetic association -> original Gamma1 Picard/H1 -> Abel-Jacobi converse -> analytic reciprocity -> winding-period integral -> Green/side-pairing identity',source=dict(path=str(src),sha256=sha(src),fullMathematicalSourceRead=True),reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in [r/'.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/SlashActions.lean',r/'9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026/Extension/Dubon2026/CongruenceTraceDomain.lean',p/'SourceSmoothModularGeometry.lean',p/'SourceSmoothOrbitIntegralGeometry.lean']],shorterRoute='Native SlashAction.slash_mul replaces the duplicate denominator cocycle and bespoke slash action. Fix actual Quotient.out representatives rather than generalize to arbitrary sections. Existing projective domain tiling and AE-disjointness can replace the separate source finite-domain tiling proof. Existing action/dbar geometry is reused for Green integration.',assumptionsToDischarge=['Actual T/S boundary pullback identities','Finite coset reindexing and exact side-pairing integral formulas','Subsequent Green identity must discharge boundary integrability and identify the winding period'],remaining='Green integration and actual period-lattice realization of the side pairing; complete winding/Petersson reciprocity and full original arithmetic chain. 16/20; DUB-17--20 OPEN.')
with (p/'modular-side-pairing-reuse-route-920.json').open('x',encoding='utf-8') as f:json.dump(route,f,indent=2)
print('Prepared actual side-pairing action with native slash composition; arbitrary-section and duplicate derivative infrastructure deferred.')

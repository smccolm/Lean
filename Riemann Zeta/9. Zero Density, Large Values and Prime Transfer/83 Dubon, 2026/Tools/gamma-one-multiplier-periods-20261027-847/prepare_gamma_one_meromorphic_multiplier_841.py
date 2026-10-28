from pathlib import Path
import json,hashlib
p=Path(r'E:\Lean\.tmp\dubon83');r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
f=p/'gamma-one-period-core-reuse-755b/S_ModularCurve_exists_cuspForm_multiplier_eq_exp_periodOf_of_norm_eq_one.lean.txt';lines=f.read_text(encoding='utf-8').splitlines()
fixed='''theorem exists_smul_eq_self_of_trace_sq_lt_four (γ : SL(2, ℤ))
    (h : (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 < 4) : ∃ τ : ℍ, γ • τ = τ := by
  let g : GL (Fin 2) ℝ := γ
  have hdet : g.val.det = 1 := SourceFunctionField.SubgroupStabilizer.det_coe_SL γ
  have hell : g.IsElliptic := by
    change g.val.discr < 0
    rw [Matrix.discr_fin_two, hdet, mul_one, sub_neg]
    rw [Matrix.trace_fin_two] at h ⊢
    change ((γ 0 0 : ℝ) + (γ 1 1 : ℝ)) ^ 2 < 4
    exact_mod_cast h
  refine ⟨fixedPt g hell, ?_⟩
  change g • fixedPt g hell = fixedPt g hell
  exact (gl_smul_eq_self_iff_eq_fixedPt (by rw [hdet]; norm_num) hell).mpr rfl
'''
par='\n'.join(lines[31:36])+'\n'+'\n'.join(lines[143:155])+'\n'+'\n'.join(lines[156:212])+'\n'
par=par.replace(':= parabolic_classification ',':= SourceParabolic.classification ')
germ='\n'.join(lines[273:340])+'\n'
for mod,imports,body in [
 ('SourceModularEllipticFixedPoint',['Dubon2026.SourceStabilizerMeromorphicOrder','Mathlib.Analysis.Complex.UpperHalfPlane.FixedPoints'],fixed),
 ('SourceMeromorphicMultiplierParabolic',['SourceModularEllipticFixedPoint','Dubon2026.SourceParabolicClassification'],par),
 ('SourceMeromorphicMultiplierGerm',['SourceMeromorphicMultiplierParabolic'],germ)]:
 header=''.join('import '+i+'\n' for i in imports)+'\n/-! DUB-17/18 -> original Gamma1 Picard/H1 -> Abel-Jacobi -> actual\nmeromorphic multiplier correction. Reuse native elliptic fixed points and\nthe repository Mobius-germ and signed parabolic classification results.\nAdapt the remaining actual multiplier calculation from the Apache-2.0\nscope-755b primary at revision 6e837e75355538c7f80bab5b956861e86c4eacc2.\nNo congruence level or central-sign normalization is discarded. -/\nnamespace Dubon2026.SourceMeromorphicMultiplier\nnoncomputable section\nopen UpperHalfPlane Filter SourceFunctionField.SubgroupStabilizer\nopen scoped MatrixGroups Topology\n'
 with (p/(mod+'.lean')).open('x',encoding='utf-8',newline='\n') as out:out.write(header+body+'\nend\nend Dubon2026.SourceMeromorphicMultiplier\n')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
files=[f,r/'SourceStabilizerMeromorphicOrder.lean',r/'SourceSubgroupStabilizerCharacter.lean',r/'SourceParabolicClassification.lean',r/'SourceGammaOneExactRamification.lean',r/'SourceGammaOneMeromorphicPrincipalDivisor.lean',Path(r'E:\Lean\Riemann Zeta\.lake\packages\mathlib\Mathlib\Analysis\Complex\UpperHalfPlane\FixedPoints.lean')]
with (p/'gamma-one-meromorphic-multiplier-route-841.json').open('x',encoding='utf-8') as out:json.dump(dict(chain='DUB17/18 -> original all-weight arithmetic association -> actual Gamma1 Picard/H1 -> Abel-Jacobi -> actual meromorphic multiplier -> unitary cusp-form period representation.',reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in files],shorterRoute='Reuse SourceStabilizerMeromorphicOrder moeb_sub, continuity and coordinate identities; reuse SourceParabolic.classification and SubgroupStabilizer.chi. Replace the primary explicit real square-root fixed-point calculation by native UpperHalfPlane.fixedPt and gl_smul_eq_self_iff_eq_fixedPt. The existing two_mul_ramification_eq_stabilizer_card is for plusMinus(Gamma1 N), which supplies the correct central-sign normalization at every nonzero level.',assumptionsToDischarge='Derive multiplicativity from a nonzero cusp limit; parabolic triviality from translated cusp limits; elliptic triviality from the actual meromorphic germ order and signed stabilizer cardinality. Then consume the proved unitary-character period representation, rather than assume its multiplier hypotheses.',remaining='Actual meromorphic construction from the Abel-Jacobi condition, analytic reciprocity, original Picard/H1/Hecke comparison and all-weight arithmetic association remain; DUB17--20 OPEN.'),out,indent=2);out.write('\n')
print('Prepared multiplier foundations with native fixed-point and local-germ reuse.')

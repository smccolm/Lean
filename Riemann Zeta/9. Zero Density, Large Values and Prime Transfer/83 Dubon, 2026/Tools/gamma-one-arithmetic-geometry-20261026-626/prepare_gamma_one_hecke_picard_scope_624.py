from pathlib import Path
import json,re,hashlib
p=Path(r'E:\Lean\.tmp\dubon83')
prod=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
mods=['SourceGammaOneResidues','SourceGammaOneHeckePicard'];ns='Dubon2026.SourceFunctionField.GammaOne.'
roots=[ns+n for n in ['heckeDivisor_mem_degZero','isPrincipal_heckeDivisor','heckePicard_mk']]
extra=[ns+n for n in ['gamma1_finite_coordinate','gamma1_hecke_finite_coordinate','heckeAlpha_finite','heckeBeta_finite']]+['Dubon2026.SourceCurve.'+n for n in ['place_residue_bijective_of_finite_coordinate','Divisor.geometricCorrespondence','Divisor.geometricCorrespondence_mem_degZero','Divisor.isPrincipal_geometricCorrespondence','Pic0.geometricCorrespondence','Pic0.geometricCorrespondence_mk']]
reuse=['SourceCurveFiniteCoordinateResidues','SourceCurvePicardCorrespondence','SourceOriginalHeckePicard']
route=dict(chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero Galois association -> arithmetic realization of original finite Gamma1 Hecke characters -> geometric/H1 comparison -> actual Gamma1 Picard Hecke correspondence.',
reuseChecked=[dict(path=str(prod/(m+'.lean')),sha256=sha(prod/(m+'.lean'))) for m in reuse],
selectedRoute='Apply existing closed-residue and actual divisor pullback/pushforward, degree and norm theorems directly to the already proved actual Gamma1 fields and finite Hecke maps. No new curve or Picard foundations; no extraneous generalization.',
assumptionsToDischarge='Every place of the actual Gamma1 and Hecke fields over algebraically closed constants has the same residue field as the constants. The literal beta pullback followed by alpha pushforward preserves degree zero and principal divisors. It therefore defines the actual Gamma1 Hecke endomorphism of degree-zero divisor classes, with exact representative evaluation. Finite-map, residue-degree, degree-preservation and principal-divisor-preservation inputs are derived.',
remaining='Geometric/H1 and diamond comparison, arithmetic action compatibility, geometric Galois realization of the finite characters, original all-weight characteristic-zero association, required local/image/regularity, arithmetic automorphy and literal higher symmetric-power continuation remain required. 16/20; DUB-17--20 OPEN.',
productionStatus='Scratch development; audits and production promotion pending.',rootPinsChanged=False,proofLimitsChanged=False)
def output(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output('gamma1-actual-picard-hecke-route-624.json',json.dumps(route,indent=2)+'\n')
s=(p/'prepare_gamma_one_hecke_field_audit_622.py').read_text(encoding='utf-8')
for k,v in [('mods',mods),('roots',roots),('extra',extra)]:s=re.sub(r'^'+k+'=.+$',lambda _,k=k,v=v:k+'='+repr(v),s,flags=re.M)
s=s.replace('source-gamma-one-hecke-field-5','source-gamma-one-hecke-picard-2').replace('SourceGammaOneHeckeFieldAudit5','SourceGammaOneHeckePicardAudit2').replace('SourceGammaOneHeckeFieldDependencyAudit5','SourceGammaOneHeckePicardDependencyAudit2').replace('SOURCE GAMMA ONE HECKE FIELD','SOURCE GAMMA ONE HECKE PICARD').replace('gamma1-finite-hecke-field-route-622.json','gamma1-actual-picard-hecke-route-624.json')
a=s.index("dep=dep[:dep.index('  logInfo m!')]");b=s.index("\noutput('SourceGammaOneHeckePicardDependencyAudit2",a)
msg='SOURCE GAMMA ONE HECKE PICARD DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in degree-zero and principal-divisor preservation or the representative evaluation of the actual Gamma1 Picard Hecke operator. Only declaration values are traversed. Actual finite coordinates and finite Hecke maps, closed residue fields and existing norm/degree identities discharge all advertised geometric-construction inputs. Geometric/H1 and diamond comparison, arithmetic action compatibility, finite-character Galois realization, original all-weight characteristic-zero association and higher continuation remain required. 16/20; DUB-17--20 OPEN.'
s=s[:a]+"dep=dep[:dep.index('  logInfo m!')]+ "+repr('  logInfo m!"'+msg+'"\n\n#eval runPlanarPairingDependencyAudit\n')+s[b:]
output('prepare_gamma_one_hecke_picard_audit_624.py',s)
s=(p/'record_gamma_one_hecke_field_622.py').read_text(encoding='utf-8').replace('source-gamma-one-hecke-field-5','source-gamma-one-hecke-picard-2').replace('SourceGammaOneHeckeFieldAudit5','SourceGammaOneHeckePicardAudit2').replace('SourceGammaOneHeckeFieldDependencyAudit5','SourceGammaOneHeckePicardDependencyAudit2').replace('SOURCE GAMMA ONE HECKE FIELD','SOURCE GAMMA ONE HECKE PICARD').replace('gamma1-finite-hecke-field-route-622.json','gamma1-actual-picard-hecke-route-624.json')
s=s.replace('==(5,17,27)','==(2,7,17)').replace('==5','==2').replace('all 27 required proof dependencies','all 17 required proof dependencies').replace('linterScopes=5','linterScopes=2').replace('requiredProofValueEdges=27','requiredProofValueEdges=17').replace('modules=5,queries=17','modules=2,queries=7').replace('proofEdges=27','proofEdges=17')
output('record_gamma_one_hecke_picard_624.py',s)

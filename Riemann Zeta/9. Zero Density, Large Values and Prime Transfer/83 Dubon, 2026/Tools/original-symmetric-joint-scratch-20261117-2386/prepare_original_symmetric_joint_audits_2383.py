from pathlib import Path
import hashlib,json,re
p=Path(__file__).parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
base=json.loads((p/'source-original-cyclotomic-symmetric-audit-config-2354b.json').read_text())
prior=json.loads((p/'source-projective-finite-audit-config-2321.json').read_text())
base['modules']+=json.loads((p/'source-original-symmetric-adjoint-audit-config-2366.json').read_text())['modules']+json.loads((p/'source-original-twisted-kernel-audit-config-2377.json').read_text())['modules']
pairs=[('SourceFiniteLinearOriginalConsequences2381a','SourceFiniteLinearOriginalConsequences'),('SourceGammaOneSymmetricResidualCohomology2382a','SourceGammaOneSymmetricResidualCohomology')]
c=dict(files=[],modules=[],queries=[],theorems=[],constructions=[],roots=[],proofEdges=[],scope='Two final assembly modules: one actual original residual representation retains finite image alternatives, original symmetric spanning, absolute irreducibility and adjoint H0 on both literal arithmetic and absolute cyclotomic kernels, and actual arithmetic twisted-kernel detection.')
def write(name,t):
 f=p/name;assert not f.exists();f.write_text(t,encoding='utf-8')
for old,new in pairs:
 f=p/(old+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0
 t=f.read_text(encoding='utf-8')
 for a,b in pairs:t=re.sub(r'(?m)^import '+a+'$', 'import '+b,t)
 write(new+'.lean',t)
 c['files'].append(dict(source=str(f),sourceSha256=sha(f),module=new,path=str(p/(new+'.lean')),canonicalSha256=sha(p/(new+'.lean'))))
 c['modules'].append(new)
 ns=re.search(r'(?m)^namespace (\S+)',t)[1]
 th=[ns+'.'+n for n in re.findall(r'(?m)^theorem (\S+)',t)]
 df=[ns+'.'+n for n in re.findall(r'(?m)^def (\S+)',t)]
 c['queries']+=th+df;c['theorems']+=th;c['constructions']+=df
c['roots']=[c['theorems'][-1]]
oldEdges=json.loads((p/'source-original-residue-consumer-edges-2361.json').read_text())['required']
omittedWrappers={
 'Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction.exists_gammaOne_original_residue_absolute_symmetric_irreducibility',
 'Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction.exists_gammaOne_original_symmetric_kernel_spanning'}
c['proofEdges']=list(dict.fromkeys(
 json.loads((p/'source-original-twisted-kernel-audit-config-2377.json').read_text())['proofEdges']+
 [n for n in oldEdges if n not in omittedWrappers]+c['queries']+[
 'Dubon2026.HasOriginalSymmetricAdjointVanishing',
 'Dubon2026.original_symmetric_adjoint_vanishing_of_absolute',
 'Dubon2026.matrixTraceZeroAdjointInvariants_eq_bot',
 'Dubon2026.matrixAdjointInvariant_eq_scalar_of_extension']))
c['sourceAssemblyReview']='The joint source starts from the actual arithmetic twisted-kernel consumer and constructs all other conclusions from its same original residual image bounds. The two earlier existential irreducibility/spanning wrappers remain independently proved and audited; their generic mathematical proofs, rather than unused existential wrappers, occur in this joint consumer.'

assert len(c['proofEdges'])==len(set(c['proofEdges']))
arr=lambda xs:'#['+', '.join('`'+n for n in xs)+']'
for old,new in [('SourceOriginalSymmetricAudit1','SourceOriginalSymmetricJointAudit1'),('SourceOriginalResidueConsumerAudit2361','SourceOriginalSymmetricJointDependencyAudit1'),('SourceOriginalSymmetricDeclarations2354','SourceOriginalSymmetricJointDeclarations2383')]:
 t=(p/(old+'.lean')).read_text(encoding='utf-8')
 t=re.sub(r'(?m)^import Source.*\n','',t)
 t='import '+c['modules'][-1]+'\n'+t
 if old=='SourceOriginalSymmetricAudit1':
  t=re.sub(r'(?m)^#print axioms .*\n','',t)
  t=t.replace('open Lean\n','open Lean\n\n'+'\n'.join('#print axioms '+q for q in c['queries'])+'\n',1)
  t=re.sub(r'let modules : Array Name := #\[.*\]','let modules : Array Name := '+arr(c['modules']),t)
  t=re.sub(r'(?m)^#lint in .*\n','',t)
  t+='\n'.join('#lint in '+m for m in c['modules'])+'\n'
  t=t.replace('SOURCE ORIGINAL SYMMETRIC AXIOM AUDIT PASS','SOURCE ORIGINAL SYMMETRIC JOINT AXIOM AUDIT PASS')
  t=t.replace('The original-form consumer derives absolute symmetric-power irreducibility in the large-image branch over actual finite coefficient extensions and bases, including restriction to the original arithmetic and absolute Galois cyclotomic kernels. Arithmetic large-image exclusions remain OPEN.','One actual original residual action has the image alternatives, original symmetric spanning, absolute irreducibility, adjoint H0 vanishing and actual arithmetic twisted-kernel detection. Arithmetic image exclusions and remaining local and auxiliary-prime conditions remain OPEN.')
 elif old=='SourceOriginalResidueConsumerAudit2361':
  for label,values in [('roots',c['roots']),('localModules',prior['modules']+base['modules']+c['modules']),('required',c['proofEdges'])]:
   t=re.sub('let '+label+r' : Array Name := #\[.*\]','let '+label+' : Array Name := '+arr(values),t)
  t=t.replace('SOURCE ORIGINAL RESIDUE SINGLE-CONSUMER VALUE AUDIT PASS','SOURCE ORIGINAL SYMMETRIC JOINT VALUE AUDIT PASS')
 else:t=re.sub(r'let mods : Array Name := #\[.*\]','let mods : Array Name := '+arr(c['modules']),t)
 write(new+'.lean',t)
write('source-original-symmetric-joint-audit-config-2383.json',json.dumps(c,indent=2)+'\n')
print(json.dumps(dict(modules=2,queries=len(c['queries']),requiredEdges=len(c['proofEdges']))))

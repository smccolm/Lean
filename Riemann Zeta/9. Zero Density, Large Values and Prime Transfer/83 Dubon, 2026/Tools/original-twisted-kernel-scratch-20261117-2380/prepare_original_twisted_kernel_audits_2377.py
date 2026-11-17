from pathlib import Path
import hashlib,json,re
p=Path(__file__).parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
base=json.loads((p/'source-original-cyclotomic-symmetric-audit-config-2354b.json').read_text())
prior=json.loads((p/'source-projective-finite-audit-config-2321.json').read_text())
pairs=[
 ('SourceFiniteLinearOriginalScalar2367a','SourceFiniteLinearOriginalScalar'),
 ('SourceFiniteLinearTwistedKernel2368a','SourceFiniteLinearTwistedKernel'),
 ('SourceOriginalTwistedDetectionProperty2369a','SourceOriginalTwistedDetectionProperty'),
 ('SourceOriginalTwistedTopology2369b','SourceOriginalTwistedTopology'),
 ('SourceGammaOneTwistedKernelDetection2370b','SourceGammaOneTwistedKernelDetection'),
 ('SourceArithmeticCyclotomicSquare2372b','SourceArithmeticCyclotomicSquare'),
 ('SourceOriginalArithmeticTwistedDetection2373a','SourceOriginalArithmeticTwistedDetection'),
 ('SourceGammaOneArithmeticTwistedDetection2374a','SourceGammaOneArithmeticTwistedDetection')]

c=dict(files=[],modules=[],queries=[],theorems=[],constructions=[],roots=[],proofEdges=[],scope='Eight additional modules: original scalar witnesses and actual arithmetic twisted-cohomology joint-kernel detection on the large-image branch, without a supplied character witness or finite-image H1-vanishing certificate.')
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
c['proofEdges']=list(dict.fromkeys(prior['proofEdges']+c['queries']+[
 'Dubon2026.residualSubfieldGL2_exists_scalar_character_square',
 'Dubon2026.SourceDickson.scalar_factor_descends',
 'Dubon2026.continuousH1_exists_nonzero_kernel_of_central_scalar',
 'Dubon2026.rationalArithmeticCyclotomicCharacter_surjective',
 'Dubon2026.rationalPrimitiveRoot_autToPow_surjective',
 'Dubon2026.matrixTraceZeroCharacterRep_apply_of_scalarGL']))
assert len(c['proofEdges'])==len(set(c['proofEdges']))
arr=lambda xs:'#['+', '.join('`'+n for n in xs)+']'
for old,new in [('SourceOriginalSymmetricAudit1','SourceOriginalTwistedKernelAudit1'),('SourceOriginalResidueConsumerAudit2361','SourceOriginalTwistedKernelDependencyAudit1'),('SourceOriginalSymmetricDeclarations2354','SourceOriginalTwistedKernelDeclarations2377')]:
 t=(p/(old+'.lean')).read_text(encoding='utf-8')
 t=re.sub(r'(?m)^import Source.*\n','',t)
 t='import '+c['modules'][-1]+'\n'+t
 if old=='SourceOriginalSymmetricAudit1':
  t=re.sub(r'(?m)^#print axioms .*\n','',t)
  t=t.replace('open Lean\n','open Lean\n\n'+'\n'.join('#print axioms '+q for q in c['queries'])+'\n',1)
  t=re.sub(r'let modules : Array Name := #\[.*\]','let modules : Array Name := '+arr(c['modules']),t)
  t=re.sub(r'(?m)^#lint in .*\n','',t)
  t+='\n'.join('#lint in '+m for m in c['modules'])+'\n'
  t=t.replace('SOURCE ORIGINAL SYMMETRIC AXIOM AUDIT PASS','SOURCE ORIGINAL TWISTED KERNEL AXIOM AUDIT PASS')
  t=t.replace('The original-form consumer derives absolute symmetric-power irreducibility in the large-image branch over actual finite coefficient extensions and bases, including restriction to the original arithmetic and absolute Galois cyclotomic kernels. Arithmetic large-image exclusions remain OPEN.','The actual original-form consumer derives twisted-cohomology detection on the actual arithmetic residual/cyclotomic kernel in the large-image branch. The original scalar and cyclotomic witnesses are constructed. Arithmetic image exclusions and remaining local and auxiliary-prime conditions remain OPEN.')
 elif old=='SourceOriginalResidueConsumerAudit2361':
  for label,values in [('roots',c['roots']),('localModules',prior['modules']+base['modules']+c['modules']),('required',c['proofEdges'])]:
   t=re.sub('let '+label+r' : Array Name := #\[.*\]','let '+label+' : Array Name := '+arr(values),t)
  t=t.replace('SOURCE ORIGINAL RESIDUE SINGLE-CONSUMER VALUE AUDIT PASS','SOURCE ORIGINAL TWISTED KERNEL VALUE AUDIT PASS')
 else:t=re.sub(r'let mods : Array Name := #\[.*\]','let mods : Array Name := '+arr(c['modules']),t)
 write(new+'.lean',t)
write('source-original-twisted-kernel-audit-config-2377.json',json.dumps(c,indent=2)+'\n')
print(json.dumps(dict(modules=8,queries=len(c['queries']),requiredEdges=len(c['proofEdges']))))

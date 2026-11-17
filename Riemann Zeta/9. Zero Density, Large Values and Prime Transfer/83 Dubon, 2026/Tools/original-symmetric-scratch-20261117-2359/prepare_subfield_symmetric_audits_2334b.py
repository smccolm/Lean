from pathlib import Path
import re,json,hashlib
p=Path(__file__).parent
pairs=[('SourceFiniteSubfieldIrreducible2330a','SourceFiniteSubfieldIrreducible'),('SourceSubfieldSymmetricAbsolute2331a','SourceSubfieldSymmetricAbsolute'),('SourceFiniteLinearSymmetric2332b','SourceFiniteLinearSymmetric'),('SourceGammaOneAbsoluteSymmetricResidual2333a','SourceGammaOneAbsoluteSymmetricResidual')]
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
files=[];queries=[]
for old,new in pairs:
 f=p/(old+'.lean');assert (p/(old+'.exit')).read_text().strip()=='0' and (p/(old+'.log')).stat().st_size==0
 t=f.read_text(encoding='utf-8')
 for a,b in pairs:t=re.sub(r'(?m)^import '+a+'$', 'import '+b,t)
 target=p/(new+'.lean');assert target.read_text(encoding='utf-8')==t
 files.append(dict(source=str(f),sourceSha256=sha(f),module=new,path=str(target),canonicalSha256=sha(target)))
 ns=re.search(r'(?m)^namespace (\S+)',t)[1]
 queries += [ns+'.'+n for n in re.findall(r'(?m)^theorem (\S+)',t)]
mods=[b for a,b in pairs];root=queries[-1];oldc=json.loads((p/'source-projective-finite-audit-config-2321.json').read_text())
required=oldc['proofEdges']+queries[:-1]+['Dubon2026.symmetricMatrixThreeOperators_submodule_eq_top','Dubon2026.homogeneousSymmetricGL_map']
assert len(required)==len(set(required))
arr=lambda xs:'#['+', '.join('`'+x for x in xs)+']'
def write(n,t):
 f=p/n;assert not f.exists();f.write_text(t,encoding='utf-8')
t=(p/'SourceProjectiveFiniteAudit1.lean').read_text(encoding='utf-8');t=t.replace('import SourceGammaOneFiniteProjectiveLinearResidual','import '+mods[-1]);t=re.sub(r'(?m)^#print axioms .*\n','',t);t=t.replace('open Lean\n','open Lean\n\n'+'\n'.join('#print axioms '+q for q in queries)+'\n',1);t=re.sub(r'let modules : Array Name := #\[.*\]','let modules : Array Name := '+arr(mods),t);t=re.sub(r'(?m)^#lint in .*\n','',t);t += '\n'.join('#lint in '+m for m in mods)+'\n';t=t.replace('SOURCE PROJECTIVE FINITE AXIOM AUDIT PASS','SOURCE SUBFIELD SYMMETRIC AXIOM AUDIT PASS');t=t.replace('The original-form consumer proves the full projective classification, explicit matrix conjugacy and small-image-or-linear-subfield bounds over an actual finite coefficient extension.','The original-form consumer derives absolute symmetric-power irreducibility in the large-image branch over one actual finite coefficient extension and basis.');write('SourceSubfieldSymmetricAudit1.lean',t)
t=(p/'SourceProjectiveFiniteDependencyAudit1.lean').read_text(encoding='utf-8');t=t.replace('import SourceGammaOneFiniteProjectiveLinearResidual','import '+mods[-1]);
for label,vals in [('roots',[root]),('localModules',oldc['modules']+mods),('required',required)]:t=re.sub('let '+label+r' : Array Name := #\[.*\]','let '+label+' : Array Name := '+arr(vals),t)
t=t.replace('SOURCE PROJECTIVE FINITE VALUE AUDIT PASS','SOURCE SUBFIELD SYMMETRIC VALUE AUDIT PASS');write('SourceSubfieldSymmetricDependencyAudit1.lean',t)
t=(p/'SourceProjectiveFiniteDeclarations2321.lean').read_text(encoding='utf-8').replace('import SourceGammaOneFiniteProjectiveLinearResidual','import '+mods[-1]);t=re.sub(r'let mods : Array Name := #\[.*\]','let mods : Array Name := '+arr(mods),t);write('SourceSubfieldSymmetricDeclarations2334.lean',t)
config=dict(files=files,modules=mods,queries=queries,theorems=queries,constructions=[],roots=[root],proofEdges=required,failedPreparation='First inline generator stopped before audit generation because the old root was already in the inherited dependency edge set; four canonical import-only copies had been written and are now checked byte-for-byte. No proof or dependency was omitted.')
write('source-subfield-symmetric-audit-config-2334.json',json.dumps(config,indent=2)+'\n')
print(json.dumps(dict(modules=mods,queries=len(queries),requiredValueEdges=len(required))))

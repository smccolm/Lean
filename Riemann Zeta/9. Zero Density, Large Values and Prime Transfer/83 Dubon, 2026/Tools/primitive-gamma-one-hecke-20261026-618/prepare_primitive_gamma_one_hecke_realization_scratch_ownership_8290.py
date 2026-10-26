from pathlib import Path
import hashlib,json
p=Path(__file__).parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
route=json.loads((p/'primitive-gamma-one-hecke-promotion-route-618.json').read_text())
certs=[]
for name,digest in route['receipts'].items():
    assert sha(p/name)==digest
    certs.append(json.loads((p/name).read_text()))
names=[]
for i,c in zip(route['scopeIds'],certs,strict=True):
    name=f'SourcePrimitiveGammaOneHeckeRealizationScratchOwnership{i}For8290'
    out=p/(name+'.lean')
    assert not out.exists()
    mods=c['modules']
    s=''.join('import '+m+'\n' for m in mods)+'import Lean\n\nopen Lean\n\n'
    s+='private def inspectOwnership : CoreM Unit := do\n  let env ← getEnv\n'
    s+='  let mods : Array Name := #['+', '.join('`'+m for m in mods)+']\n'
    s+='''  for (name, info) in env.constants.toList do
    if info.isTheorem then
      if let some idx := env.getModuleIdxFor? name then
        let m := env.allImportedModuleNames[idx.toNat]!
        if mods.contains m then logInfo m!"OWNER {m}: {name}"

#eval inspectOwnership
'''
    out.write_text(s,encoding='utf-8')
    names.append(name)
f=p/'source-primitive-gamma-one-hecke-realization-scratch-ownership-8290.json'
assert not f.exists()
f.write_text(json.dumps(names,indent=2)+'\n')
print(json.dumps(dict(scopes=len(names),expectedSum=sum(c['exhaustiveTheorems'] for c in certs))))

from pathlib import Path
import ast,datetime,hashlib,json,re,subprocess

s=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta')
p=r/'9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026'
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
script=s/'integrate_source_original_symmetric_residual_9755b.py'
t=script.read_text(encoding='utf-8')
marker='# All frozen source, receipt and document checks precede production mutation.'
assert t.count(marker)==1
prefix=t.split(marker)[0]
# The exact prepared transaction preconditions run without writing any of its
# pending production, audit, documentation or archive outputs.
assert not re.search(r'\.write_(?:text|bytes)\(',prefix)
scope={'__file__':str(script)}
exec(compile(prefix,str(script),'exec'),scope)
assert len(scope['pending'])==30
for target,body in scope['pending']:
    source=s/target.name
    strip=lambda text:'\n'.join(line for line in text.splitlines() if not line.startswith('import '))
    assert strip(body)==strip(source.read_text(encoding='utf-8'))
    assert target.parent==p/'Extension/Dubon2026'
    assert not target.exists()
c=json.loads((p/'Tools/scaffold.json').read_text(encoding='utf-8'))
assert len(c['productionModules'])==9725
files=[p/'Extension/Dubon2026'/(name.replace('.','/')+'.lean') for name in c['productionModules']]
assert all(f.exists() for f in files)
frozen=[r/'lean-toolchain',r/'lakefile.toml',r/'lake-manifest.json',
        r/'run_lake_build.bat',p/'run_dubon_build.bat',p/'push_to_github.bat']
report=dict(recordedUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    productionModulesBefore=9725, productionModulesAfter=9755,
    script=dict(path=str(script),sha256=sha(script)),
    existingLean={f.relative_to(p).as_posix():sha(f) for f in files},
    frozenFiles={str(f):sha(f) for f in frozen},
    importsOnly=True, publicQueries=44, scratchTheorems=126,scratchOtherDeclarations=52,
    theoremRegistrations=37,constructionRegistrations=7,
    priorCanonical=dict(path=str(p/'Tools/projective-residual-image-20261117-2326/canonical-evidence-9725.json'),sha256=sha(p/'Tools/projective-residual-image-20261117-2326/canonical-evidence-9725.json')),
    workingTree=subprocess.run(['git','status','--short'],cwd=r,capture_output=True,text=True,check=True).stdout.splitlines())
target=s/'source-original-symmetric-residual-preflight-9755.json'
assert not target.exists();target.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(preflight=True,existingLean=len(files),importsOnly=True,sha256=sha(target))))

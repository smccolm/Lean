from pathlib import Path
import ast,json,re,hashlib
p=Path(r'E:\Lean\.tmp\dubon83')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
route=p/'gamma-one-differential-inputs-promotion-route-641.json'
rd=json.loads(route.read_text(encoding='utf-8'))
certs=[json.loads((p/n).read_text(encoding='utf-8')) for n in rd['receipts']]
for n,h in rd['receipts'].items():assert sha(p/n)==h
scripts=[f for f in p.iterdir() if re.search(r'8335\.(py|ps1)$',f.name) and f.name!='prepare_gamma_one_differential_inputs_promotion_8335.py']
assert len(scripts)==9,len(scripts)
for f in scripts:
 t=f.read_text(encoding='utf-8')
 if f.suffix=='.py':ast.parse(t)
 assert '16/22' not in t and 'DUB-17-22' not in t
s=(p/'integrate_source_gamma_one_differential_inputs_8335.py').read_text(encoding='utf-8')
assert '== 8316' in s and '(19, 19, 85, 73, 12)' in s
assert 'receipt8316' in s and 'canonical-evidence-8316.json' in s
assert 'count == 138' in s and 'appliedSourceGammaOneDifferentialInputs' in s
review=dict(status='Prepared; preceding 8316 canonical PASS, immutable archive and renewed-search publication required before integration.',
route=route.name,routeSha256=sha(route),modules=19,queries=85,theorems=73,constructions=12,exhaustiveScratchChecks=138,proofValueEdges=136,scopes=8,receipts=rd['receipts'],
expectedConsumers=24024,expectedConstructions=2325,fullGoal='16/20; DUB-17--20 OPEN; all 20 gates unchanged.',
sourceBodies='Audited statements, proof bodies and comments unchanged; only scratch project imports qualified.',
scripts=[dict(path=str(f),sha256=sha(f)) for f in scripts],productionMutation=False,
precedingHelperFailure=dict(path=str(p/'prepare_gamma_one_differential_inputs_promotion_8335.py'),sha256=sha(p/'prepare_gamma_one_differential_inputs_promotion_8335.py'),
reason='The generated-script filename scan included its own generator and rejected the literal forbidden-status test strings in that generator. All nine intended helpers were produced, but no production action or review receipt ran. This fresh review restricts the scan to the intended helpers and parses all Python helpers.'))
f=p/'gamma-one-differential-inputs-preexecution-review-8335.json';assert not f.exists()
f.write_text(json.dumps(review,indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(scripts=len(scripts),modules=19,queries=85,exhaustive=138,edges=136,productionMutation=False)))

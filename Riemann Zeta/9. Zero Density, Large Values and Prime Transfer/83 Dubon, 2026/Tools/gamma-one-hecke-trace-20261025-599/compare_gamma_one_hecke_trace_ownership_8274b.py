from pathlib import Path
import json,re,hashlib
p=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
data=json.loads((r/'Tools/source-gamma-one-hecke-trace.json').read_text())
certs=data['scratchCertificates']
names=json.loads((p/'source-gamma-one-hecke-trace-scratch-ownership-8274.json').read_text())
bad=r'(^|\s)(warning:|error(?:\(|:)|PANIC\b)|sorryAx'
def rows(name):
    f=p/(name+'.log')
    assert f.with_suffix('.exit').read_text().strip()=='0'
    t=f.read_text(encoding='utf-16')
    assert not re.search(bad,t)
    return re.findall(r'^OWNER (\S+): (\S+)$',t,re.M),dict(path=str(f),sha256=sha(f),sourceSha256=sha(f.with_suffix('.lean')))
allmods=[m for c in certs for m in c['modules']]
assert len(names)==len(certs)==6
def norm(n):
    for m in allmods: n=n.replace('_private.'+m+'.','_private.Dubon2026.'+m+'.')
    return n
sources={}
scopes=[]
for name,c in zip(names,certs,strict=True):
    rr,log=rows(name)
    assert len(rr)==len(set(n for _,n in rr))==c['exhaustiveTheorems']
    for m,n in rr: sources.setdefault(norm(n),[]).append(dict(scope=name,module='Dubon2026.'+m))
    scopes.append(dict(modules=c['modules'],count=len(rr),log=log))
pr,pl=rows('SourceGammaOneHeckeTraceOwnership8274')
prod={n:m for m,n in pr}
assert len(prod)==len(pr)

# Import qualification may change automatic private instance suffixes.
# Accept only exact, injective, owner-preserving instances of those two naming rules.
renamings={}
available=set(prod)-set(sources)
for name in sorted(set(sources)-set(prod)):
 owners={row['module'] for row in sources[name]}
 assert len(owners)==1
 owner=next(iter(owners))
 stem=owner.split('.')[-1]
 suffix='_'+stem[0].lower()+stem[1:]
 if not name.startswith('_private.'+owner+'.') or suffix not in name: continue
 candidates={name.replace(suffix,'_dubon2026'),name.replace(suffix,'')}
 matches={n for n in candidates if n in available and prod[n]==owner}
 if len(matches)==1:
  renamed=next(iter(matches))
  renamings[name]=renamed
  available.remove(renamed)
assert len(set(renamings.values()))==len(renamings)
normalized={}
for name,rows_ in sources.items():
 n=renamings.get(name,name)
 assert n not in normalized
 normalized[n]=rows_
sources=normalized
sourceChecks=[]
for m in allmods:
 scratch=p/(m+'.lean');production=r/'Extension/Dubon2026'/(m+'.lean')
 strip=lambda f:re.sub(r'(?m)^import .*\n','',f.read_text(encoding='utf-8'))
 assert strip(scratch)==strip(production),m
 sourceChecks.append(dict(module=m,scratchSha256=sha(scratch),productionSha256=sha(production),bodyIdentical=True))
prior=json.loads((r/'Tools/lean-reuse-audit-20261015.json').read_text(encoding='utf-8'))['appliedSourcePrimitiveFiniteH1Realization']['receipt8248']
old=r/prior['log']
oldnames=set(re.findall(r'^PASS (\S+):',old.read_text(encoding='utf-8-sig'),re.M))
assert len(oldnames)==prior['projectTheorems']
# Preserve the failed comparison; explain generated ownership by exact independent probes.
retentions={}
retentionLogs=[]
for label in ['SourceGammaOneHeckeTraceGeneratedRetention8274b','SourceGammaOneHeckeTraceScratchRetention8274b']:
 f=p/(label+'.log')
 assert f.with_suffix('.exit').read_text().strip()=='0'
 t=f.read_text(encoding='utf-16')
 assert not re.search(bad,t)
 rows_=dict((name,(owner,ty,val)) for owner,name,ty,val in re.findall(r'^RETAINED (\S+): (\S+) (\d+) (\d+)$',t,re.M))
 assert rows_
 for name,axioms in re.findall(r"^'(.+)' depends on axioms:\s*\[([^]]*)\]",t,re.M):
  assert set(a.strip() for a in axioms.split(','))<={'propext','Classical.choice','Quot.sound'}
 assert len(re.findall(r"^'.+' depends on axioms:",t,re.M))==len(rows_)
 retentions[label]=rows_
 retentionLogs.append(dict(path=str(f),sha256=sha(f),sourceSha256=sha(f.with_suffix('.lean'))))
retained=retentions['SourceGammaOneHeckeTraceGeneratedRetention8274b']
scratchRetained=retentions['SourceGammaOneHeckeTraceScratchRetention8274b']
upstreamRetained={name:dict(owner=owner,typeHash=ty,valueHash=val) for name,(owner,ty,val) in retained.items() if owner.startswith('Mathlib.')}
assert set(upstreamRetained)=={'ZMod.chineseRemainder.congr_simp'}
for name,row in upstreamRetained.items():
 assert scratchRetained[name][1:]==(row['typeHash'],row['valueHash'])
 assert scratchRetained[name][0]=='SourcePrincipalCoprimeReduction'
assert retained['Dubon2026.sourceGammaOneDiagonalHom.eq_1'][0]=='Dubon2026.SourceGammaOneCoverFiniteIndex'
result=dict(scratchSum=sum(s['count'] for s in scopes),scratchDistinct=len(sources),
    generatedNameRenamings=renamings,productionFocused=len(prod),
    duplicateScratchNames={n:v for n,v in sources.items() if len(v)>1},
    missingFromFocused={n:sources[n] for n in set(sources)-set(prod)},
    missingFromFocusedAlreadyInPrevious=sorted((set(sources)-set(prod))&oldnames),
    productionNamesNotInScratch=sorted(set(prod)-set(sources)),
    upstreamRetainedGenerated=upstreamRetained,retainedGeneratedFingerprints=retained,retentionLogs=retentionLogs,unexplainedMissing=sorted(set(sources)-set(prod)-oldnames-set(upstreamRetained)),scopes=scopes,
    productionOwnership=pl,previousGlobal=dict(path=str(old),sha256=sha(old)))
ok=(result['scratchSum']==111 and result['unexplainedMissing']==result['productionNamesNotInScratch']==[]
    and set(result['missingFromFocused'])==(set(result['missingFromFocusedAlreadyInPrevious'])|set(upstreamRetained))
    and result['productionFocused']==result['scratchDistinct']-len(result['missingFromFocused']))
result['renameEvidence']=dict(reason='Only exact owner-preserving automatic private module suffix changes are normalized. All 26 mathematical source bodies are identical after stripping imports; every public and private theorem remains accounted for. Independent generated-name probes retain the exact Chinese-remainder theorem type/value hashes under its Mathlib owner and identify the already-audited cover equation owner.',sourceChecks=sourceChecks)
result['passed']=ok
f=p/('source-gamma-one-hecke-trace-ownership-comparison-8274b.json' if ok else
     'source-gamma-one-hecke-trace-ownership-diagnostic-8274c.json')
assert not f.exists()
f.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ('scopes','productionOwnership','previousGlobal')},indent=2))
assert ok,'Exact ownership comparison failed; diagnostic preserved. Inspect before any successor.'

from pathlib import Path
import re,json
s=Path(__file__).parent
versions=json.loads((s/'peaked-exponent-versions-1552.json').read_text(encoding='utf-8'))
changes={'SourcePeakedBernoulliResidueWeights':'1541b','SourcePeakedBernoulliConvolution':'1543b','SourcePeakedBernoulliVanishing':'1544b','SourcePeakedBernoulliSpan':'1546b','SourcePeakedExponents':'1550c','SourceGammaOnePeakedCuspOrders':'1551b'}
for m,newv in changes.items():
 old=s/(m+versions[m]+'.lean');new=s/(m+newv+'.lean');assert not new.exists()
 t=old.read_text(encoding='utf-8')
 if m=='SourcePeakedBernoulliResidueWeights':
  a=t.index('theorem summable_Zres ');b=t.index('omit [NeZero N] in',a);t=t[:a]+t[b:]
 if m=='SourcePeakedBernoulliSpan':
  t=t.replace('def evenSub (N : ℕ) [NeZero N]', 'def evenSub (N : ℕ)')
  a=t.index('theorem mem_evenSub ');b=t.index('theorem T_eq_zero_imp ',a);t=t[:a]+t[b:]
 for n,v in changes.items():t=t.replace('import '+n+versions[n]+'\n','import '+n+v+'\n')
 assert not old.with_suffix('.lean.txt').exists()
 old.rename(old.with_suffix('.lean.txt'))
 new.write_text(t,encoding='utf-8')
versions.update(changes)
def write(n,t):
 f=s/n;assert not f.exists();f.write_text(t,encoding='utf-8')
write('peaked-exponent-versions-1555.json',json.dumps(versions,indent=2)+'\n')
c=(s/'build_integral_trace_canonical_1531.ps1').read_text(encoding='utf-8')
c=re.sub(r'\$names=@\([^\n]+\)',"$names=@("+','.join(repr(m+v) for m,v in changes.items())+')',c)
c=c.replace("$ev=$base+'-1531'","$ev=$base")
write('build_peaked_trim_1555.ps1',c)
review=dict(reason='Exhaustive preflight found one unused NeZero binder in the even-function subspace; remove it. Proof-value preflight identified two unused auxiliary lemmas, summable_Zres and mem_evenSub; defer both rather than promote incidental lemmas. Native Fourier inversion uses the actual linear equivalence and LinearEquiv.map_eq_zero_iff, not a theorem named ZMod.dft_injective. The actual cusp endpoint statement is unchanged. All prior sources and failed logs remain intact.',changes=changes)
write('peaked-exponent-trim-review-1555.json',json.dumps(review,indent=2)+'\n')

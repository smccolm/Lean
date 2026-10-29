from pathlib import Path
import json,re
s=Path(__file__).parent
versions={
'SourceGammaOnePeakedCuspClasses':'1534a',
'SourcePeakedBernoulliFourier':'1539b',
'SourcePeakedBernoulliMoments':'1540a',
'SourcePeakedBernoulliResidueWeights':'1541a',
'SourcePeakedBernoulliCharacterInversion':'1542b',
'SourcePeakedBernoulliConvolution':'1543a',
'SourcePeakedBernoulliVanishing':'1544a',
'SourcePeakedBernoulliFourierInversion':'1545a',
'SourcePeakedBernoulliSpan':'1546a',
'SourcePeakedBernoulliProgressions':'1547a',
'SourcePeakedBernoulliTotient':'1548a',
'SourcePeakedExponentHelpers':'1549b',
'SourcePeakedExponents':'1550b',
'SourceGammaOnePeakedCuspOrders':'1551a'}
mods=[m+v for m,v in versions.items()]
ths=[];defs=[]
for m in mods:
 f=s/(m+'.lean')
 assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 code=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',f.read_text(encoding='utf-8'),flags=re.S))
 ns=re.search(r'^namespace (\S+)',code,re.M)[1]+'.'
 ths += [ns+x for x in re.findall(r'^theorem\s+([\w.\x27]+)',code,re.M)]
 defs += [ns+x for x in re.findall(r'^(?:noncomputable )?def\s+([\w.\x27]+)',code,re.M)]
assert len(set(ths+defs))==len(ths+defs)
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
c=(s/'SourceIntegralTraceAudit1.lean').read_text(encoding='utf-8')
c='\n'.join('import '+m for m in mods)+'\nimport Mathlib.Tactic\n'+c[c.index('\nopen Lean'):]
c=re.sub(r'(#print axioms [^\n]+\n)+',''.join('#print axioms '+x+'\n' for x in ths+defs),c,count=1)
for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:c=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),c)
c=re.sub(r'#lint in [^\n]+\n','',c).rstrip()+'\n\n'+''.join('#lint in '+m+'\n' for m in mods)
c=c.replace('INTEGRAL TRACE','PEAKED EXPONENT PREFLIGHT').replace('Frobenius Normalization','Peaked exponent')
def write(n,t):
 f=s/n;assert not f.exists();f.write_text(t,encoding='utf-8')
write('SourcePeakedExponentPreflight1552.lean',c)
write('peaked-exponent-versions-1552.json',json.dumps(versions,indent=2)+'\n')
write('peaked-exponent-preflight-config-1552.json',json.dumps(dict(modules=mods,theorems=ths,constructions=defs),indent=2)+'\n')
c=(s/'audit_integral_trace_1532.ps1').read_text(encoding='utf-8')
c=re.sub(r'\$names=@\([^\n]+\)',"$names=@('SourcePeakedExponentPreflight1552')",c)
c=c[:c.index("python 'E:")]+"exit 0\n"
write('audit_peaked_exponent_preflight_1552.ps1',c)
print(json.dumps(dict(modules=len(mods),theorems=len(ths),constructions=len(defs))))

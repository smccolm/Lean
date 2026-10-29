from pathlib import Path
import json
s=Path(__file__).parent
versions={
'SourceGammaOneEvenIntegralRatios':'1502a',
'SourceLevelOneCoefficientRing':'1504a',
'SourceLevelOneIntegralWeightFactor':'1506a',
'SourceTraceProductCoefficientRing':'1508a',
'SourceIntegralLevelOneTraceCoefficients':'1509b',
'SourceTraceExponentialCoefficientVanishing':'1511a',
'SourceIntegralTraceParameters':'1512a',
'SourceIntegralTracePowerCoefficients':'1513a',
'SourceIntegralTraceCoefficientExtraction':'1514c',
'SourceIntegralTraceModularForm':'1515a',
'SourceIntegralTraceCuspTransversal':'1516a',
'SourceIntegralTraceTranslates':'1517b',
'SourceIntegralTraceTranslationCoefficients':'1518b',
'SourceIntegralTracePeriodWidth':'1519b',
'SourceIntegralTraceAnalyticProducts':'1522a',
'SourceIntegralTraceSlashPeriods':'1523b',
'SourceIntegralTraceTranslationAssembly':'1524a',
'SourceIntegralTraceTransversalSplit':'1525b',
'SourceIntegralTraceDecomposition':'1526b',
'SourceIntegralTraceDegenerateCusp':'1527c',
'SourceEvenWeightPeakedTraceIntegrality':'1529a'}
src=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
pending=[]
for m,v in versions.items():
 f=s/(m+v+'.lean')
 assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 assert not (src/(m+'.lean')).exists(),m
 c=f.read_text(encoding='utf-8')
 for nm,ver in versions.items():c=c.replace('import '+nm+ver+'\n','import '+nm+'\n')
 target=s/(m+'.lean');assert not target.exists();pending.append((target,c))
target=s/'integral-trace-versions-1531.json';assert not target.exists();pending.append((target,json.dumps(versions,indent=2)+'\n'))
runner=(s/'build_gamma_one_integral_eisenstein_canonical_1500.ps1').read_text(encoding='utf-8-sig')
a=runner.index('$names=@(');b=runner.index('\nforeach',a)
runner=runner[:a]+"$names=@("+','.join(repr(n) for n in versions)+')'+runner[b:]
runner=runner.replace("$ev=$base+'-1500'","$ev=$base+'-1531'")
target=s/'build_integral_trace_canonical_1531.ps1';assert not target.exists();pending.append((target,runner))
for target,c in pending:target.write_text(c,encoding='utf-8')
print(json.dumps(dict(modules=len(versions),status='Canonical scratch even-weight trace modules prepared; mathematical bodies and comments frozen. Production remains untouched.')))

from pathlib import Path
import json
s=Path(__file__).parent
versions={'SourceRationalLocalFrobenius':'1450a','SourceRationalLocalClosureEmbedding':'1456a','SourceGammaOneDiamondQuotientLocal':'1449f','SourceGammaOneDiamondQuotientHeckeFamily':'1454b','SourceGammaOneDiamondQuotientWords':'1451e','SourceGammaOneDiamondQuotientWordKernel':'1455b','SourceGammaOneDiamondQuotientCharacter':'1452c','SourceGammaOneDiamondQuotientCharacterAssembly':'1457c','SourceGammaOneDiamondQuotientGaloisHecke':'1458a','SourceGammaOneDiamondQuotientChosenFrobenius':'1459b'}
pending=[]
for m,v in versions.items():
 f=s/(m+v+'.lean')
 assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 c=f.read_text(encoding='utf-8')
 for nm,ver in versions.items():c=c.replace('import '+nm+ver+'\n','import '+nm+'\n')
 t=s/(m+'.lean');assert not t.exists(),t;pending.append((t,c))
t=s/'gamma-one-quotient-character-versions-1460.json';assert not t.exists();pending.append((t,json.dumps(versions,indent=2)+'\n'))
runner=(s/'build_gamma_one_transfer_canonical_1446.ps1').read_text(encoding='utf-8-sig')
a=runner.index('$names=@(');b=runner.index('\nforeach',a)
runner=runner[:a]+"$names=@("+','.join(repr(n) for n in versions)+')'+runner[b:]
runner=runner.replace("$ev=$base+'-1446'","$ev=$base+'-1460'")
t=s/'build_gamma_one_quotient_character_canonical_1460.ps1';assert not t.exists();pending.append((t,runner))
for t,c in pending:t.write_text(c,encoding='utf-8')
print(json.dumps(dict(modules=len(versions),status='Prepared original quotient character consumers; bodies/comments retained.')))

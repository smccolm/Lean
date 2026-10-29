from pathlib import Path
s=Path(__file__).parent
for old,new,before,after in [
 ('SourceIntegralTraceTranslates1517a','SourceIntegralTraceTranslates1517b','  rw [Finset.sum_apply]; rfl','  rfl'),
 ('SourceIntegralTraceTranslationCoefficients1518a','SourceIntegralTraceTranslationCoefficients1518b','import SourceIntegralTraceTranslates1517a','import SourceIntegralTraceTranslates1517b')]:
 a=s/(old+'.lean');b=s/(new+'.lean');assert not b.exists()
 t=a.read_text(encoding='utf-8');assert before in t
 b.write_text(t.replace(before,after),encoding='utf-8');a.rename(a.with_suffix('.lean.txt'))

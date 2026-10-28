from pathlib import Path
import re,json,hashlib,shutil
p=Path(r'E:\Lean\.tmp\dubon83')
mods=['SourceModularSmoothCutoff','SourceModularSmoothGeometry','SourceModularSmoothCosetSum','SourceModularSmoothCover','SourceModularSmoothedFundamentalSupport','SourceModularSmoothedFundamental']
ev={m:m+('875a' if i<2 else '876d' if i<4 else '876e') for i,m in enumerate(mods)}
# Previous compiles are immutable evidence; all changes below are documentation only.
d=p/'smooth-partition-source-before-attribution-877a';d.mkdir()
for m in mods:
 f=p/(m+'.lean')
 assert (p/(ev[m]+'.exit')).read_text().strip()=='0'
 assert (p/(ev[m]+'.log')).stat().st_size==0
 shutil.copyfile(f,d/(m+'.lean.txt'))
 s=f.read_text(encoding='utf-8')
 s=s.replace('Native proper discontinuity, Mobius imaginary-part identity, and coset\nequivalence are reused.', 'Native proper discontinuity and the Mobius imaginary-part identity are\nreused. The exact chosen-representative coset decomposition is proved.')
 at='Adapted from anthropics/fermats-last-theorem (Apache-2.0), frozen primary\nDef_ModularCurve_SmoothedFundamental and\nS_ModularCurve_contDiff_and_finsum_smoothedFundamental_eq_one;\nexact hashes are recorded in modular-smooth-partition-route-875.json.\n'
 pos=s.index('/-! ')+4;s=s[:pos]+at+s[pos:]
 f.write_text(s,encoding='utf-8')
body=(p/'SourceModularSmoothedFundamental.lean').read_text(encoding='utf-8')
body=body[body.index('theorem smooth_partition'):body.index('\nend\nend Dubon2026.SourceSmoothedFundamental')]
sig=body[:body.index(' :=')]
sig=sig.replace('theorem smooth_partition\n    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (T : ℝ)', 'theorem sourceGamma1_smooth_partition (N : ℕ) [NeZero N] (T : ℝ)')
sig=re.sub(r'\bΓ\b','(CongruenceSubgroup.Gamma1 N)',sig)
out='import SourceModularSmoothedFundamental\n\n/-! Actual original Gamma1 specialization of the compact smooth orbit partition.\nThis supplies the cutoff hypotheses for the winding-period limit serving\nDUB-17/18 through the original Picard/H1 and Abel-Jacobi chain. -/\nnamespace Dubon2026\nnoncomputable section\nopen UpperHalfPlane SourceSmoothedFundamental\nopen scoped MatrixGroups Topology ContDiff\n\n'+sig+' :=\n  smooth_partition (CongruenceSubgroup.Gamma1 N) T\n\nend\nend Dubon2026\n'
with (p/'SourceGammaOneSmoothPartition.lean').open('x',encoding='utf-8') as f:f.write(out)
alltext='\n'.join((p/(m+'.lean')).read_text(encoding='utf-8') for m in mods)
names=re.findall(r'^(?:noncomputable )?(?:theorem|def) ([^\s(]+)',alltext,re.M)
print(json.dumps(dict(possiblyUnconsumed=[n for n in names if len(re.findall(r'(?<![\w])'+re.escape(n)+r'(?![\w])',alltext))==1]),ensure_ascii=True))

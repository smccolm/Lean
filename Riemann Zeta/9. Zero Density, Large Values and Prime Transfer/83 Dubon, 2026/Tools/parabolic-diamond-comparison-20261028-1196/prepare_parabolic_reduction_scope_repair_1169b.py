from pathlib import Path
import ast,json
p=Path(__file__).parent
def write(n,s):
 f=p/n;assert not f.exists();f.write_text(s,encoding='utf-8')
old='SourceParabolicReductionKernelDependencyAudit1'
s=(p/(old+'.lean')).read_text(encoding='utf-8')
start=s.index(' occur in the ')
end=s.index('; DUB17--20 OPEN.',start)
s=s[:start]+' occur in the native finite torsion annihilator and actual integral parabolic H1 reduction-kernel proofs. Only moduli coprime to the fixed nonzero integer are covered. Exceptional primes and finite character descent remain'+s[end:]
write(old+'b.lean',s)
s=(p/'record_parabolic_reduction_kernel_1169.py').read_text(encoding='utf-8')
s=s.replace('source-parabolic-reduction-kernel-1-scratch-receipt','source-parabolic-reduction-kernel-1b-scratch-receipt').replace('source-parabolic-reduction-kernel-1-reuse-review','source-parabolic-reduction-kernel-1b-reuse-review').replace(old,old+'b')
s=s.replace("boundary = 'Scratch-audited", "boundary = 'Supersedes receipt 1 only to correct a copied dependency-audit prose label; all mathematical source, query and proof-dependency requirements are identical. Scratch-audited")
ast.parse(s);write('record_parabolic_reduction_kernel_1169b.py',s)
s=(p/'audit_parabolic_reduction_kernel_1169.ps1').read_text(encoding='utf-8')
line=next(l for l in s.splitlines() if l.startswith('$names='))
s=s.replace(line,"$names=@('"+old+"b')").replace('record_parabolic_reduction_kernel_1169.py','record_parabolic_reduction_kernel_1169b.py')
write('audit_parabolic_reduction_kernel_1169b.ps1',s)

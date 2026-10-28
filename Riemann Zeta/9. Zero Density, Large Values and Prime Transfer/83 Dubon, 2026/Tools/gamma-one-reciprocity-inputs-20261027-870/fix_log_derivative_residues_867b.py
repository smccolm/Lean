from pathlib import Path
import shutil
p=Path(r'E:\Lean\.tmp\dubon83')
f=p/'SourceComplexLogDerivativeResidues.lean'
d=p/'log-derivative-residues-failed-867a';d.mkdir()
shutil.copy2(f,d/(f.name+'.txt'))
for e in ['.log','.exit']:shutil.copy2(f.with_suffix(e),d/f.with_suffix(e).name)
t=f.read_text(encoding='utf-8')
a=t.index('  have hp : DifferentiableAt');b=t.index('\ntheorem analyticAt_dslope',a)
t=t[:a]+"""  have hd : DifferentiableAt ℂ (fun w : ℂ => w - a) z := differentiableAt_id.sub_const a
  have hp : DifferentiableAt ℂ (fun w : ℂ => (w - a) ^ n) z := hd.zpow (Or.inl hsub)
  rw [logDeriv_mul (f := fun w : ℂ => (w - a) ^ n) (g := G) z
    (zpow_ne_zero n hsub) hG0 hp hG, logDeriv_fun_zpow hd]
  simp [logDeriv_apply]
"""+t[b:]
f.write_text(t,encoding='utf-8',newline='\n')

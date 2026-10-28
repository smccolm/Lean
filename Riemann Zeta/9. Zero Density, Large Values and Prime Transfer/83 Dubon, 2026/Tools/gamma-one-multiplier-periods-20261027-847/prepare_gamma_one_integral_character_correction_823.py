from pathlib import Path
import json,hashlib
p=Path(r'E:\Lean\.tmp\dubon83')
bad=p/'integral-character-initial-lift-failed-822a';bad.mkdir()
for ext in ['.lean','.log','.exit']:(bad/('SourceIntegralCharacterInitialLift'+ext)).write_bytes((p/('SourceIntegralCharacterInitialLift'+ext)).read_bytes())
f=p/'SourceIntegralCharacterInitialLift.lean';s=f.read_text(encoding='utf-8');old='{ι : Type*} {M : ι → Type*}';assert old in s;s=s.replace(old,'{ι : Type} {M : ι → Type}');f.write_text(s,encoding='utf-8')
lines=(p/'gamma-one-period-core-reuse-796/S_ModularCurve_Period_exists_parabolicHoms_int_castAddHom_comp_eq_of_forall_isOfFinOrder.lean.txt').read_text(encoding='utf-8').splitlines()
for mod,a,b,imports,pre,post in [
 ('SourceIntegralCharacterCuspConjugacy',414,485,['SourceIntegralCharacterInitialLift'],'','end CuspGeneral\n'),
 ('SourceIntegralCharacterCuspSum',487,502,['SourceIntegralCharacterCuspConjugacy'],'section CuspGeneral\nvariable {G : Type} [Group G] (H : Subgroup G)\n','end CuspGeneral\n'),
 ('SourceIntegralCharacterCorrection',506,565,['SourceIntegralCharacterCuspSum','SourceCuspCorrectionRealization'],'','')]:
 body='\n'.join(lines[a-1:b])+'\n'
 body=body.replace('{G : Type*}', '{G : Type}')
 body=body.replace('abbrev M23 : Fin 2 → Type := fun i => Multiplicative (ZMod (i.val + 2))','/-- The actual cyclic factors of the modular free-product presentation. -/\nabbrev M23 : Fin 2 → Type := SourceModularFreeProduct.G23')
 body=body.replace('abbrev G23 : Type := Monoid.CoprodI M23','/-- The actual modular free product. -/\nabbrev G23 : Type := Monoid.CoprodI M23')
 start='def tP : G23 := Monoid.CoprodI.of (M := M23) (i := 0) (Multiplicative.ofAdd 1) *\n  Monoid.CoprodI.of (M := M23) (i := 1) (Multiplicative.ofAdd 1)'
 body=body.replace(start,'/-- The actual parabolic generator used by the audited cusp correction. -/\nabbrev tP : G23 := SourceCuspCorrection.τ')
 body=body.replace('Monoid.CoprodI.exists_addMonoidHom_conj_pow_minimalPeriod_eq_of_finsum_eq_zero tP rfl H ℤ a ha0','SourceCuspCorrection.engine H ℤ a ha0')
 body=body.replace('have h1 := hφ\' q.out.out hp\'','have h1 := hφ\' q.out.out\n    change φ\' (Additive.ofMul ⟨_, hp\'⟩) = a (Quotient.mk (MulAction.orbitRel (Subgroup.zpowers tP) (G23 ⧸ H)) (q.out.out : G23 ⧸ H)) at h1')
 header=''.join('import '+i+'\n' for i in imports)+'\n/-! DUB-17/18 -> original Gamma1 Picard/H1 -> Abel-Jacobi -> unitary\nmultiplier logarithms -> integral parabolic-character lifting. The native\ntransfer formula proves zero total cusp value; the audited actual edge-chain\ncorrection then removes all parabolic values without changing reduction\nmodulo n. Adapted from the Apache-2.0 integral-lift primary in scope 796,\nrevision 6e837e75355538c7f80bab5b956861e86c4eacc2.\nThe original modular-group transport remains a separate obligation. -/\nnamespace Dubon2026.SourceIntegralCharacterLift\nnoncomputable section\nopen Subgroup\n'
 with (p/(mod+'.lean')).open('x',encoding='utf-8',newline='\n') as out:out.write(header+pre+body+post+'\nend\nend Dubon2026.SourceIntegralCharacterLift\n')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
files=[Path(r'E:\Lean\Riemann Zeta\.lake\packages\mathlib\Mathlib\GroupTheory\Transfer.lean'),p/'source-cusp-correction-1-scratch-receipt.json',p/'source-modular-free-product-1-scratch-receipt.json']
with (p/'gamma-one-integral-character-correction-route-823.json').open('x',encoding='utf-8') as out:json.dump(dict(chain='DUB-17/18 -> original all-weight arithmetic association -> Gamma1 Picard/H1 -> Abel-Jacobi -> unitary multiplier logarithms -> integral parabolic-character lifting -> zero total cusp values and actual correction.',reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in files],shorterRoute='Use the pinned native transfer_eq_prod_quotient_orbitRel_zpowers_quot; no transfer theory is reproved. Apply the already audited SourceCuspCorrection.engine on the identical C2*C3 group and primitive cusp generators.',assumptionsToDischarge='Every integer character has zero sum over actual primitive cusp values. Divisibility of its parabolic values by n permits an actual correction n*phi, preserving reduction modulo n and killing every parabolic conjugate. Includes n=0.',remaining='Original SL2 and Gamma1 transport, unitary logarithms, analytic reciprocity, and full all-weight arithmetic association remain; 16/20; DUB-17--20 OPEN.'),out,indent=2);out.write('\n')
print('Preserved 822a universe failure; prepared native-transfer cusp correction.')

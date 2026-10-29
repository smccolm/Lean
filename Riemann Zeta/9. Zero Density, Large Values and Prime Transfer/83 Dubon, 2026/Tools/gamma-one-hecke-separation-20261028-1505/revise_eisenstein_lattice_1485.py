from pathlib import Path
s=Path(r'E:\Lean\.tmp\dubon83'); a=s/'SourceGammaOneEisensteinLattice1484a.lean'; b=s/'SourceGammaOneEisensteinLattice1484b.lean'
assert a.exists() and not b.exists() and not a.with_suffix('.lean.txt').exists()
t=a.read_text(encoding='utf-8')
t=t.replace('    simp only [hb]\n    congr 1\n    apply Subtype.ext', '    apply Sigma.ext hb\n    apply Subtype.heq_iff_coe_heq.mpr\n    apply heq_of_eq')
t=t.replace('  exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (congrArg Prod.snd h)', '  have h1 : x.1.1 = y.1.1 := congrArg (fun q : ℤ × ℤ => q.1) h\n  have h2 : x.2 = y.2 := congrArg (fun q : ℤ × ℤ => q.2) h\n  exact Prod.ext (Subtype.ext h1) h2')
t=t.replace('  have ht := (rowClassEquiv N c).summable_iff.mpr hs', '  have ht := (rowClassEquiv N c).summable_iff.mpr hs\n  change Summable (fun p : (Σ b : ZMod N, rows N ![c, b]) =>\n    eisSummand 4 ![p.2.1 0, p.2.1 1] z) at ht')
t=t.replace('(rowClassEquiv N c).tsum_eq _', '(rowClassEquiv N c).tsum_eq\n          (fun p : {m : ℤ // (m : ZMod N) = c} × ℤ => eisSummand 4 ![p.1.1, p.2] z)')
b.write_text(t,encoding='utf-8'); a.rename(a.with_suffix('.lean.txt'))

from pathlib import Path
p=Path(__file__).parent
f=p/'SourceGammaOneTwistedCongruence1419a.lean';assert f.with_suffix('.exit').read_text().strip()=='1'
s=f.read_text(encoding='utf-8')
s=s.replace('variable (Q p n w : ℕ)', '''private theorem proj_eq_of_congruence {A : Type*} [AddCommGroup A]
    (p r : ℕ) [Fact p.Prime] (x y : TateModule p A)
    (h : x - y ∈ (maximalIdeal ℤ_[p] ^ r) • (⊤ : Submodule ℤ_[p] (TateModule p A))) :
    TateModule.proj p A r x = TateModule.proj p A r y := by
  have hz := (TateModule.proj_eq_zero_iff r (x - y)).mpr h
  exact sub_eq_zero.mp ((map_sub (TateModule.proj p A r) x y).symm.trans hz)

variable (Q p n w : ℕ)''')
start=s.index('  have hp : TateModule.proj');end=s.index('  change binaryCyclotomicCoefficientRep',start)
s=s[:start]+'''  have hp := proj_eq_of_congruence p (n + 1) (arithmeticTateGaloisRep M p σ⁻¹ x) x (hT x)
  have he := binaryArithmeticTateDual_eq_of_proj_eq Q p n w φ hp
'''+s[end:]
t=p/'SourceGammaOneTwistedCongruence1419b.lean';assert not t.exists();t.write_text(s,encoding='utf-8')
inert=f.with_suffix('.lean.txt');assert not inert.exists();f.rename(inert)
s=(p/'build_gamma_one_twisted_congruence_1419.ps1').read_text(encoding='utf-8').replace('1419a','1419b')
t=p/'build_gamma_one_twisted_congruence_1419b.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')
f=p/'SourceGammaOneTwistedContinuity1420a.lean';assert not f.with_suffix('.log').exists()
f.write_text(f.read_text(encoding='utf-8').replace('SourceGammaOneTwistedCongruence1419a','SourceGammaOneTwistedCongruence1419b'),encoding='utf-8')

from pathlib import Path
p=Path(__file__).parent
f=p/'SourceGammaOneTwistedContinuity1420c.lean';assert f.with_suffix('.exit').read_text().strip()=='1'
s=f.read_text(encoding='utf-8')
s=s.replace('variable (Q p n w : ℕ)', '''private theorem one_congruence {R W G : Type*} [CommRing R] [AddCommGroup W]
    [Module R W] [Monoid G] (ρ : G →* Module.End R W) (U : Submodule R W) :
    ∀ x : W, ρ 1 x - x ∈ U := by
  intro x
  rw [map_one]
  change x - x ∈ U
  rw [sub_self]
  exact U.zero_mem

variable (Q p n w : ℕ)''')
start=s.index('  have hm :');end=s.index('  have hi :',start)
s=s[:start]+'''  have hm : (1 : G) ∈ U := one_congruence (arithmeticTateGaloisRep M p)
    ((maximalIdeal ℤ_[p] ^ (n + 1)) • (⊤ : Submodule ℤ_[p] T))
'''+s[end:]
t=p/'SourceGammaOneTwistedContinuity1420d.lean';assert not t.exists();t.write_text(s,encoding='utf-8')
inert=f.with_suffix('.lean.txt');assert not inert.exists();f.rename(inert)
s=(p/'build_gamma_one_twisted_continuity_1420c.ps1').read_text(encoding='utf-8').replace('1420c','1420d')
t=p/'build_gamma_one_twisted_continuity_1420d.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')

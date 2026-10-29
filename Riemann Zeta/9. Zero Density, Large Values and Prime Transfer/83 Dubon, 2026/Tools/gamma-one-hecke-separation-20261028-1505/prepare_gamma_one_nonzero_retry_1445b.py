from pathlib import Path
s=Path(__file__).parent
f=s/'SourceGammaOneDiamondQuotientNonzero1445a.lean';c=f.read_text(encoding='utf-8').replace('local notation "w" => (k - 2).toNat','local notation "w" => Int.toNat (k - 2)')
t=s/'SourceGammaOneDiamondQuotientNonzero1445b.lean';assert not t.exists();t.write_text(c,encoding='utf-8')
t=f.with_suffix('.lean.txt');assert not t.exists();f.rename(t)
print('Use the checked Int.toNat notation without changing elaboration options.')

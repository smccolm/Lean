from pathlib import Path
s=Path(__file__).parent
f=s/'SourceGammaOneDiamondQuotientGalois1438e.lean';c=f.read_text(encoding='utf-8')
c=c.replace('Submodule.hasQuotient (R := ZMod N) (M := T →ₗ[ℤ_[p]] V)','@Submodule.hasQuotient (ZMod N) (T →ₗ[ℤ_[p]] V) inferInstance inferInstance inferInstance')
c=c.replace('Representation.quotient (k := ZMod N) (V := T →ₗ[ℤ_[p]] V)','Representation.quotient (k := ZMod N)')
t=s/'SourceGammaOneDiamondQuotientGalois1438f.lean';assert not t.exists();t.write_text(c,encoding='utf-8')
t=f.with_suffix('.lean.txt');assert not t.exists();f.rename(t)
# Isolate the inferred carrier structures before changing any mathematics.
v=c[c.index('variable (Q p n w'):c.index('private local instance : HasQuotient')]
probe='''import SourceGammaOneTateDiamondRelations1437e
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open SourceCurve CongruenceSubgroup
'''+v+'''
example : AddCommGroup V := inferInstance
example : AddCommGroup (T →ₗ[ℤ_[p]] V) := inferInstance
example : Module (ZMod N) (T →ₗ[ℤ_[p]] V) := inferInstance
example : HasQuotient (T →ₗ[ℤ_[p]] V)
    (Submodule (ZMod N) (T →ₗ[ℤ_[p]] V)) := inferInstance
example : AddCommGroup ((T →ₗ[ℤ_[p]] V) ⧸ binaryTateDiamondRelations Q p n w) := inferInstance
end
end Dubon2026.SourceFunctionField.GammaOne
'''
t=s/'GammaOneQuotientCarrierProbe1438f.lean';assert not t.exists();t.write_text(probe,encoding='utf-8')
print('Removed notation/argument-name collisions; prepared an isolated carrier probe.')

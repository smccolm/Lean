from pathlib import Path
s=Path(__file__).parent
f=s/'SourceGammaOneDiamondQuotientWords1451c.lean';c=f.read_text(encoding='utf-8')
marker='theorem binaryDiamondQuotientOriginalTransfer_word\n'
cache='''private local instance : AddCommGroup
    ((T →ₗ[ℤ_[p]] V) ⧸ binaryTateDiamondRelations Q p n w) := inferInstance
private local instance : Module (ZMod N)
    ((T →ₗ[ℤ_[p]] V) ⧸ binaryTateDiamondRelations Q p n w) := inferInstance

'''
assert c.count(marker)==1;c=c.replace(marker,cache+marker)
old='''  rw [sourceGammaOneOriginalHeckeWord_change, ← hz]
  have hw := binaryDiamondQuotientOriginalTransfer_word Q p n w hlarge Hq hH a z
  rw [ha, LinearMap.zero_apply, map_zero] at hw
  exact hw.symm'''
new='''  let β := binaryDiamondQuotientOriginalTransfer Q p n w hlarge
  let u := fun ell => sourceBinaryH1PrimeOperators (ZMod N) Q w
    (sourceGammaOneHeckePrimeForget Q N ell)
  have hw := binaryDiamondQuotientOriginalTransfer_word Q p n w hlarge Hq hH a z
  have hzero := LinearMap.congr_fun ha z
  have hzword := hw.symm.trans ((congrArg β hzero).trans (map_zero β))
  have hc := sourceGammaOneOriginalHeckeWord_change Q N w a x
  exact hc.trans ((congrArg (FreeAlgebra.lift ℤ u a) hz.symm).trans hzword)'''
assert c.count(old)==1;c=c.replace(old,new)
t=s/'SourceGammaOneDiamondQuotientWords1451d.lean';assert not t.exists();t.write_text(c,encoding='utf-8')
a=f.with_suffix('.lean.txt');assert not a.exists();f.rename(a)
print('Cache the actual quotient structures and compose proved map identities without concrete rewriting.')

from pathlib import Path
s=Path(__file__).parent
f=s/'SourceGammaOneDiamondQuotientCharacter1452b.lean';c=f.read_text(encoding='utf-8')
marker='variable (Q p n : ℕ)'
helper='''private theorem character_on_range {A B C : Type} [Ring A] [Ring B] [Ring C]
    (θ : A →ₐ[ℤ] B) (ψ : A →+* C) (h : ∀ a, θ a = 0 → ψ a = 0) :
    ∃ χ : θ.range →+* C, χ.comp θ.rangeRestrict.toRingHom = ψ := by
  have hker : RingHom.ker θ.rangeRestrict.toRingHom ≤ RingHom.ker ψ := by
    intro a ha
    exact h a (congrArg Subtype.val (RingHom.mem_ker.mp ha))
  exact ⟨sourceFiniteOperatorCharacterDescend θ.rangeRestrict.toRingHom
    θ.rangeRestrict_surjective ψ hker, sourceFiniteOperatorCharacterDescend_comp _ _ _ _⟩

'''
assert c.count(marker)==1;c=c.replace(marker,helper+marker)
a=c.index('  let θ :=');b=c.index('\nend\n',a)
c=c[:a]+'''  let ψ := (sourcePrimitiveH1AdicQuotientCharacter f hk τ n).comp
    (sourceGammaOneOriginalHeckeWord Q N w).toRingHom
  have hs := character_on_range (FreeAlgebra.lift ℤ Hq) ψ
  apply hs
  intro a ha
  have ht := binaryDiamondQuotientOriginalTransfer_word_kernel Q p n w hlarge Hq hH
  have h1 := ht hlift
  have h2 := h1 a ha
  exact sourcePrimitiveParabolicH1AdicQuotientCharacter_zero f hk τ p Fact.out hcop n
    (sourceGammaOneOriginalHeckeWord Q N w a) h2
'''+c[b:]
t=s/'SourceGammaOneDiamondQuotientCharacter1452c.lean';assert not t.exists();t.write_text(c,encoding='utf-8')
a=f.with_suffix('.lean.txt');assert not a.exists();f.rename(a)
print('Apply native character descent through a narrow range lemma to avoid repeated concrete ring synthesis.')

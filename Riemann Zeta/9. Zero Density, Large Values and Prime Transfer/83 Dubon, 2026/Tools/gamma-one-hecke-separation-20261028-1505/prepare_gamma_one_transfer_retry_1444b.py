from pathlib import Path
s=Path(__file__).parent
f=s/'SourceGammaOneDiamondQuotientTransfer1444a.lean';c=f.read_text(encoding='utf-8')
a=c.index('variable (Q p n w')
c=c[:a]+'''private theorem descended_intertwining {R W U Z : Type*} [CommRing R]
    [AddCommGroup W] [Module R W] [AddCommGroup U] [Module R U]
    [AddCommGroup Z] [Module R Z] (q : W →ₗ[R] Z) (hq : Function.Surjective q)
    (α : W →ₗ[R] U) (β : Z →ₗ[R] U) (H : Module.End R W)
    (Hq : Module.End R Z) (H₀ : Module.End R U)
    (hβ : ∀ x, β (q x) = α x) (hH : ∀ x, Hq (q x) = q (H x))
    (hα : ∀ x, α (H x) = H₀ (α x)) : β.comp Hq = H₀.comp β := by
  apply LinearMap.ext
  intro z
  obtain ⟨x, rfl⟩ := hq z
  exact (congrArg β (hH x)).trans ((hβ (H x)).trans
    ((hα x).trans (congrArg H₀ (hβ x).symm)))

'''+c[a:]
a=c.index(' := by\n  apply Submodule.linearMap_qext',c.index('theorem binaryDiamondQuotientOriginalTransfer_hecke'))
b=c.index('\ntheorem binaryDiamondQuotientOriginalTransfer_parabolic',a)
c=c[:a]+''' := by
  have hs := descended_intertwining (R := ZMod N) (W := T →ₗ[ℤ_[p]] V) (U := H1 V)
    (binaryTateDiamondRelations Q p n w).mkQ (binaryTateDiamondRelations Q p n w).mkQ_surjective
    (binaryTateOriginalTransfer Q p n w hlarge) (binaryDiamondQuotientOriginalTransfer Q p n w hlarge)
    (binaryTatePrimeOperators Q p n w ell) Hq
    (sourceBinaryH1PrimeOperators (ZMod N) Q w (sourceGammaOneHeckePrimeForget Q N ell))
  have h1 := hs (binaryDiamondQuotientOriginalTransfer_mk Q p n w hlarge)
  have h2 := h1 (fun φ => LinearMap.congr_fun hH φ)
  exact h2 (binaryTateOriginalTransfer_hecke Q p n w hlarge ell)
'''+c[b:]
c=c.replace('  obtain ⟨y, hy⟩ := hlift x hx','  have h1 := hlift x\n  have h2 := h1 hx\n  obtain ⟨y, hy⟩ := h2')
c=c.replace('  change sourceGammaOneConstantH1Transfer Q N w (E (E.symm y)).val = _\n  rw [E.apply_symm_apply]\n  exact hy','''  have he := congrArg (fun z : binaryParabolicH1 Q N w =>
    sourceGammaOneConstantH1Transfer Q N w z.val) (E.apply_symm_apply y)
  exact he.trans hy''')
t=s/'SourceGammaOneDiamondQuotientTransfer1444b.lean';assert not t.exists();t.write_text(c,encoding='utf-8')
t=f.with_suffix('.lean.txt');assert not t.exists();f.rename(t)
print('Staged actual transfer consumer through a small surjective-linear-map argument.')

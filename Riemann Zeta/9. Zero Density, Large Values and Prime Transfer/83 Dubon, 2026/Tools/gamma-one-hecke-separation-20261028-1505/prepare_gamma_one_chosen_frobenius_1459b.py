from pathlib import Path
s=Path(__file__).parent
f=s/'SourceGammaOneDiamondQuotientChosenFrobenius1459a.lean';c=f.read_text(encoding='utf-8')
a=c.index('/-!');b=c.index('namespace ',a)
c=c[:a]+'''/-! DUB-17/18 -> original all-weight association -> finite original
Hecke-character realization. The proved projected Frobenius identity and
surjectivity of the actual quotient map give the polynomial for every
original quotient Hecke operator with its exact quotient square. Thus the
family carrying the original adic character retains Frobenius. Degree
and genus preservation remain the explicit geometric inputs. -/
'''+c[b:]
marker='variable (Q p n w : ℕ)'
helper='''private theorem polynomial_of_projection {R W Z : Type*} [CommRing R]
    [AddCommGroup W] [Module R W] [AddCommGroup Z] [Module R Z]
    (q : W →ₗ[R] Z) (hq : Function.Surjective q)
    (F : Module.End R Z) (H : Module.End R W) (Hq : Module.End R Z) (a : R)
    (hH : ∀ x, Hq (q x) = q (H x))
    (hpoly : ∀ x, F (q (H x)) = F (F (q x)) + a • q x) :
    F * Hq = F * F + a • 1 := by
  apply LinearMap.ext
  intro z
  obtain ⟨x, rfl⟩ := hq z
  change F (Hq (q x)) = F (F (q x)) + a • q x
  exact (congrArg F (hH x)).trans (hpoly x)

'''
c=c.replace(marker,helper+marker)
a=c.index('  have hs :=');b=c.index('\nend\n',a)
c=c[:a]+'''  have hs := gammaOne_diamond_quotient_frobenius_of_degree_genus_eq Q p n w A ell
  have h1 := hs hdeg
  have h2 := h1 hgen
  have h3 := h2 d hd hp
  let q := (binaryTateDiamondRelations Q p n w).mkQ
  let F := binaryDiamondQuotientGaloisRep Q p n w d.val
  let H := binaryTatePrimeOperators Q p n w ell
  have h4 := polynomial_of_projection q (binaryTateDiamondRelations Q p n w).mkQ_surjective
    F H Hq ((ell.val : ZMod N) ^ (w + 1))
  have h5 := h4 (fun x => LinearMap.congr_fun hH x)
  exact h5 h3
'''+c[b:]
t=s/'SourceGammaOneDiamondQuotientChosenFrobenius1459b.lean';assert not t.exists();t.write_text(c,encoding='utf-8')
a=f.with_suffix('.lean.txt');assert not a.exists();f.rename(a)
print('Use the already proved projected polynomial directly; avoid unpacking a redundant operator witness.')

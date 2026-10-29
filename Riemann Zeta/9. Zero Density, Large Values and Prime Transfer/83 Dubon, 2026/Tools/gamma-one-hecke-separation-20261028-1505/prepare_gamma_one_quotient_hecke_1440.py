from pathlib import Path
s=Path(__file__).parent
base=(s/'SourceGammaOneDiamondQuotientPolynomial1439a.lean').read_text(encoding='utf-8')
vs=base[base.index('variable (Q p n w'):base.index('theorem gammaOne_diamond')]
sig=base[base.index('    (ell :'):base.index(' :\n    ∀ φ',base.index('theorem gammaOne_diamond'))]
c='''import SourceGammaOneDiamondQuotientPolynomial1439a

/-! DUB-17/18 -> original all-weight association -> finite Hecke-character
quotient. The proved quotient Frobenius identity and invertibility of
the genuine Galois action force the original Hecke operator to preserve
the diamond relations. Descend that actual operator and obtain its
Frobenius polynomial on the entire quotient. Nonzero original character
realization and coordinate-degree/genus preservation remain open. -/
namespace Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
noncomputable section
open SourceCurve CongruenceSubgroup IntermediateField

private theorem hecke_stable_of_quotient_polynomial {R W G : Type*} [CommRing R]
    [AddCommGroup W] [Module R W] [Group G] (K : Submodule R W)
    (ρ : Representation R G (W ⧸ K)) (H : Module.End R W) (g : G) (a : R)
    (hp : ∀ x, ρ g (K.mkQ (H x)) = ρ g (ρ g (K.mkQ x)) + a • K.mkQ x) :
    K ≤ K.comap H := by
  intro x hx
  have hzero : K.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero K).mpr hx
  have hpoly : ρ g (K.mkQ (H x)) = 0 := by simpa only [hzero, map_zero, smul_zero, add_zero] using hp x
  have hback (y : W ⧸ K) : ρ g⁻¹ (ρ g y) = y :=
    LinearMap.congr_fun ((ρ.map_mul g⁻¹ g).symm.trans
      ((congrArg ρ (inv_mul_cancel g)).trans ρ.map_one)) y
  apply (Submodule.Quotient.mk_eq_zero K).mp
  calc
    K.mkQ (H x) = ρ g⁻¹ (ρ g (K.mkQ (H x))) := (hback _).symm
    _ = 0 := by rw [hpoly, map_zero]

private theorem exists_hecke_quotient {R W G : Type*} [CommRing R]
    [AddCommGroup W] [Module R W] [Group G] (K : Submodule R W)
    (ρ : Representation R G (W ⧸ K)) (H : Module.End R W) (g : G) (a : R)
    (hp : ∀ x, ρ g (K.mkQ (H x)) = ρ g (ρ g (K.mkQ x)) + a • K.mkQ x) :
    ∃ Hq : Module.End R (W ⧸ K),
      Hq.comp K.mkQ = K.mkQ.comp H ∧ ρ g * Hq = ρ g * ρ g + a • 1 := by
  let Hq := K.mapQ K H (hecke_stable_of_quotient_polynomial K ρ H g a hp)
  refine ⟨Hq, rfl, ?_⟩
  apply Submodule.linearMap_qext
  apply LinearMap.ext
  intro x
  exact hp x

'''+vs+'''theorem gammaOne_diamond_relations_hecke_of_degree_genus_eq
'''+sig+''' :
    binaryTateDiamondRelations Q p n w ≤
      (binaryTateDiamondRelations Q p n w).comap (binaryTatePrimeOperators Q p n w ell) := by
  have hs := gammaOne_diamond_quotient_frobenius_of_degree_genus_eq Q p n w A ell
  have h1 := hs hdeg
  have h2 := h1 hgen
  have h3 := h2 d hd hp
  exact hecke_stable_of_quotient_polynomial (binaryTateDiamondRelations Q p n w)
    (binaryDiamondQuotientGaloisRep Q p n w) (binaryTatePrimeOperators Q p n w ell)
    d.val ((ell.val : ZMod N) ^ (w + 1)) h3

theorem exists_gammaOne_diamond_quotient_hecke_frobenius_of_degree_genus_eq
'''+sig+''' :
    ∃ Hq : Module.End (ZMod N) ((T →ₗ[ℤ_[p]] V) ⧸ binaryTateDiamondRelations Q p n w),
      Hq.comp (binaryTateDiamondRelations Q p n w).mkQ =
        (binaryTateDiamondRelations Q p n w).mkQ.comp (binaryTatePrimeOperators Q p n w ell) ∧
      binaryDiamondQuotientGaloisRep Q p n w d.val * Hq =
        binaryDiamondQuotientGaloisRep Q p n w d.val *
          binaryDiamondQuotientGaloisRep Q p n w d.val +
          (ell.val : ZMod N) ^ (w + 1) • 1 := by
  have hs := gammaOne_diamond_quotient_frobenius_of_degree_genus_eq Q p n w A ell
  have h1 := hs hdeg
  have h2 := h1 hgen
  have h3 := h2 d hd hp
  exact exists_hecke_quotient (binaryTateDiamondRelations Q p n w)
    (binaryDiamondQuotientGaloisRep Q p n w) (binaryTatePrimeOperators Q p n w ell)
    d.val ((ell.val : ZMod N) ^ (w + 1)) h3

end
end Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
'''
t=s/'SourceGammaOneDiamondQuotientHecke1440a.lean';assert not t.exists();t.write_text(c,encoding='utf-8')
print('Prepared actual Hecke stability and descended operator consumer.')

import Dubon2026.ChebotarevRootCongruence
import Dubon2026.ChebotarevRationalPrime

/-! Prescribed Frobenius and cyclotomic congruences in the same actual finite
Galois field. This supplies the congruence condition in DUB-17 auxiliary-prime
selection, before imposing residual regularity and dual Selmer detection. -/

namespace Dubon2026
noncomputable section
open NumberField Chebotarev

/-- A Galois element fixing the specified primitive root is realized at a
genuine rational prime outside any finite set, congruent to one modulo the
root order, with its exact Frobenius conjugacy class. -/
theorem finiteGalois_exists_prime_congruent_one_of_fixed_root
    (L : Type) [Field L] [NumberField L] [Algebra ℚ L] [IsGalois ℚ L]
    {m : ℕ} [NeZero m] {ζ : L} (hζ : IsPrimitiveRoot ζ m)
    (σ : Gal(L/ℚ)) (hσ : σ ζ = ζ) (S : Finset ℕ) :
    ∃ p : ℕ, p.Prime ∧ p ∉ S ∧ p ≡ 1 [MOD m] ∧
      UnramifiedIn ℚ L (Ideal.span {(p : 𝓞 ℚ)}) ∧
      frobeniusClass ℚ L (Ideal.span {(p : 𝓞 ℚ)}) = ConjClasses.mk σ := by
  classical
  let B := S ∪ Finset.range (m + 1)
  let I := B.image fun p : ℕ => Ideal.span {(p : 𝓞 ℚ)}
  obtain ⟨v, hv, hvI⟩ :=
    ((infinite_setOf_frobenius_class (ConjClasses.mk σ)).diff I.finite_toSet).nonempty
  obtain ⟨p, hp, rfl⟩ := rationalNonzeroPrime_eq_span v hv.1 hv.2.1.1
  have hpB : p ∉ B := fun h => hvI (Finset.mem_image.mpr ⟨p, h, rfl⟩)
  have hpm : m < p := by
    have h : ¬ p < m + 1 := fun hpr =>
      hpB (Finset.mem_union_right S (Finset.mem_range.mpr hpr))
    omega
  have hcop : p.Coprime m :=
    hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (NeZero.pos m) hpm)
  let v : Ideal (𝓞 ℚ) := Ideal.span {(p : 𝓞 ℚ)}
  haveI : v.IsPrime := hv.1
  have hnorm : Ideal.absNorm v = p := by
    rw [Ideal.absNorm_span_natCast, NumberField.RingOfIntegers.rank,
      Module.finrank_self, pow_one]
  have hc : (Ideal.absNorm v).Coprime m := hnorm ▸ hcop
  have hchar := finiteGalois_frobenius_cyclotomic_character ℚ L m hζ v hv.2.1 hc
  have hconj : IsConj (frobeniusClass ℚ L v).out σ := by
    apply ConjClasses.mk_eq_mk_iff_isConj.mp
    exact (Quotient.out_eq _).trans hv.2.2
  have hcharσ : hζ.autToPow ℚ σ = 1 := by
    have he : hζ.autToPow ℚ σ = hζ.autToPow ℚ 1 := by
      apply Units.ext
      apply ZMod.val_injective
      apply hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
      rw [hζ.autToPow_spec ℚ σ, hζ.autToPow_spec ℚ 1]
      exact hσ
    exact he.trans (map_one _)
  have hunit : ZMod.unitOfCoprime (Ideal.absNorm v) hc = 1 := by
    rw [← hchar, isConj_iff_eq.mp ((hζ.autToPow ℚ).map_isConj hconj), hcharσ]
  have hcast : (p : ZMod m) = 1 := by
    simpa only [ZMod.coe_unitOfCoprime, hnorm, Units.val_one] using
      congrArg (fun x : (ZMod m)ˣ => (x : ZMod m)) hunit
  refine ⟨p, hp, fun h => hpB (Finset.mem_union_left _ h), ?_, hv.2.1, hv.2.2⟩
  exact (ZMod.natCast_eq_natCast_iff p 1 m).mp (by simpa using hcast)

end
end Dubon2026

import Dubon2026.RationalCyclotomicPrincipalCharacterSum

/-! # The full finite support of the actual rational principal character

The proved principal product is reindexed by rational primes. Its actual
local reciprocity character has finite support and total character killed
by two. This supplies the support and real-place cancellation required for
DUB-17's odd-primary arithmetic unit invariant sum, without a Kummer premise.
-/
namespace Dubon2026
noncomputable section
open Polynomial IsCyclotomicExtension
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped BigOperators NumberField ValuativeRel
attribute [local instance] arithmeticFiniteLocalStageAlgebra
  arithmeticFiniteLocalStageGalois arithmeticFiniteLocalStageRationalAlgebra

/-- The actual rational principal local-reciprocity character has finite support
and its finite sum is killed by two. -/
theorem rationalArithmeticPrincipalCharacter_exists_support_two_nsmul
    (a : 𝓞 ℚ)
    (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    [IsCyclic Gal(F/ℚ)]
    (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (k : ℕ)
    [IsCyclotomicExtension {q ^ (k + 1)} ℚ F]
    {n : ℕ} [NeZero n] (χ : Gal(F/ℚ) →* Multiplicative (ZMod n)) (u : ℚˣ) :
    ∃ U : Finset Nat.Primes,
      (∀ p ∉ U, (χ (rationalArithmeticFiniteLocalReciprocityAut a F p.val p.property u)).toAdd = 0) ∧
      2 • (∑ p ∈ U, (χ (rationalArithmeticFiniteLocalReciprocityAut a F p.val p.property u)).toAdd) = 0 := by
  classical
  let N := q ^ (k + 1)
  letI : NeZero N := ⟨pow_ne_zero _ hq.ne_zero⟩
  let hζ := IsCyclotomicExtension.zeta_spec N ℚ F
  obtain ⟨S, hS, houtside, _, _, htwo⟩ :=
    rationalPrimeNormalizedResidual_exists_arithmetic_principal_character_sum a F q hq hq2 k hζ u χ
  let r := rationalPrimeNormalizedResidual q hq u
  let U : Finset Nat.Primes := insert ⟨q, hq⟩ (S.map Rat.HeightOneSpectrum.primesEquiv.toEmbedding)
  have hlocal_q :
      (χ (rationalArithmeticFiniteLocalReciprocityAut a F q hq u)).toAdd =
      (χ (rationalArithmeticFiniteLocalReciprocityAut a F q hq r)).toAdd := by
    rw [rationalArithmeticFiniteLocalReciprocityAut_normalizedResidual a F q hq hq2 k hζ u]
  have hlocal_away (v : HeightOneSpectrum ℤ) (hvq : Rat.HeightOneSpectrum.natGenerator v ≠ q) :
      (χ (rationalArithmeticFiniteLocalReciprocityAut a F
        (Rat.HeightOneSpectrum.natGenerator v) (Rat.HeightOneSpectrum.prime_natGenerator v) u)).toAdd =
      (χ (arithmeticCyclotomicAwayAut a F v r)).toAdd := by
    unfold rationalArithmeticFiniteLocalReciprocityAut
    rw [← arithmeticCyclotomicAwayAut_eq_finiteLocalReciprocity a F v u]
    rw [arithmeticCyclotomicAwayAut_normalizedResidual a F q hq k hζ v hvq u]
  have hzero_outside (v : HeightOneSpectrum ℤ) (hvS : v ∉ S)
      (hvq : Rat.HeightOneSpectrum.natGenerator v ≠ q) :
      (χ (rationalArithmeticFiniteLocalReciprocityAut a F
        (Rat.HeightOneSpectrum.natGenerator v) (Rat.HeightOneSpectrum.prime_natGenerator v) u)).toAdd = 0 := by
    rw [hlocal_away v hvq]
    have hvN : ¬Rat.HeightOneSpectrum.natGenerator v ∣ N := by
      intro hdvd
      have hdvdq : Rat.HeightOneSpectrum.natGenerator v ∣ q :=
        (Rat.HeightOneSpectrum.prime_natGenerator v).dvd_of_dvd_pow hdvd
      exact hvq (((Nat.dvd_prime hq).mp hdvdq).resolve_left
        (Rat.HeightOneSpectrum.prime_natGenerator v).ne_one)
    rw [arithmeticCyclotomicAwayAut_eq_one_of_valuation_eq_one a F N v hvN hζ r (houtside v hvS)]
    change χ 1 = 1
    exact χ.map_one
  refine ⟨U, ?_, ?_⟩
  · intro p hpU
    have hpq : p.val ≠ q := by
      intro hpq
      apply hpU
      exact Finset.mem_insert.mpr (Or.inl (Subtype.ext hpq))
    let v : HeightOneSpectrum ℤ := Rat.HeightOneSpectrum.primesEquiv.symm p
    have hvp : Rat.HeightOneSpectrum.primesEquiv v = p :=
      Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply p
    have hgen : Rat.HeightOneSpectrum.natGenerator v = p.val := congrArg Subtype.val hvp
    have hvS : v ∉ S := by
      intro hvS
      apply hpU
      simp only [U, Finset.mem_insert, Finset.mem_map]
      exact Or.inr ⟨v, hvS, hvp⟩
    have hvq : Rat.HeightOneSpectrum.natGenerator v ≠ q := by
      intro h
      exact hpq (hgen.symm.trans h)
    simpa only [hgen] using hzero_outside v hvS hvq
  · have hqnot : (⟨q, hq⟩ : Nat.Primes) ∉ S.map Rat.HeightOneSpectrum.primesEquiv.toEmbedding := by
      intro hmem
      obtain ⟨v, hvS, hvq⟩ := Finset.mem_map.mp hmem
      have hgen : Rat.HeightOneSpectrum.natGenerator v = q := congrArg Subtype.val hvq
      apply hS v hvS
      change Rat.HeightOneSpectrum.natGenerator v ∣ N
      rw [hgen]
      exact dvd_pow_self q (by omega)
    have hSneq (v : HeightOneSpectrum ℤ) (hvS : v ∈ S) : Rat.HeightOneSpectrum.natGenerator v ≠ q := by
      intro hvq
      apply hS v hvS
      change Rat.HeightOneSpectrum.natGenerator v ∣ N
      rw [hvq]
      exact dvd_pow_self q (by omega)
    have hUexpand : (∑ p ∈ U,
        (χ (rationalArithmeticFiniteLocalReciprocityAut a F p.val p.property u)).toAdd) =
        (χ (rationalArithmeticFiniteLocalReciprocityAut a F q hq u)).toAdd +
        ∑ v ∈ S, (χ (rationalArithmeticFiniteLocalReciprocityAut a F
          (Rat.HeightOneSpectrum.natGenerator v) (Rat.HeightOneSpectrum.prime_natGenerator v) u)).toAdd := by
      let f : Nat.Primes → ZMod n := fun p =>
        (χ (rationalArithmeticFiniteLocalReciprocityAut a F p.val p.property u)).toAdd
      change (insert ⟨q, hq⟩ (S.map Rat.HeightOneSpectrum.primesEquiv.toEmbedding)).sum f = _
      calc
        _ = f ⟨q, hq⟩ + (S.map Rat.HeightOneSpectrum.primesEquiv.toEmbedding).sum f :=
          Finset.sum_insert hqnot
        _ = _ := by rw [Finset.sum_map]; rfl
    rw [hUexpand, hlocal_q]
    have hsum : (∑ v ∈ S, (χ (rationalArithmeticFiniteLocalReciprocityAut a F
          (Rat.HeightOneSpectrum.natGenerator v) (Rat.HeightOneSpectrum.prime_natGenerator v) u)).toAdd) =
        ∑ v ∈ S, (χ (arithmeticCyclotomicAwayAut a F v r)).toAdd := by
      apply Finset.sum_congr rfl
      intro v hv
      exact hlocal_away v (hSneq v hv)
    change 2 • ((χ (rationalArithmeticFiniteLocalReciprocityAut a F q hq r)).toAdd +
      ∑ v ∈ S, (χ (rationalArithmeticFiniteLocalReciprocityAut a F
        (Rat.HeightOneSpectrum.natGenerator v) (Rat.HeightOneSpectrum.prime_natGenerator v) u)).toAdd) = 0
    rw [hsum]
    exact htwo

end
end Dubon2026

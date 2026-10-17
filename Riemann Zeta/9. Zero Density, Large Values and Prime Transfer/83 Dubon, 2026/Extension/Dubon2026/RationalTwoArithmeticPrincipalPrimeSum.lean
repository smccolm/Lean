import Dubon2026.RationalTwoArithmeticPrincipalInvariantSum

/-! # Original two-primary principal invariants indexed by rational primes

The constructed support is transported through the existing equivalence
between rational finite places and primes, retaining the prime two and
the actual real term. DUB-17 needs this exact indexing to compare with
the existing arithmetic unit-H2 prime invariant.
-/
namespace Dubon2026
noncomputable section
open IsDedekindDomain HeightOneSpectrum
open scoped BigOperators NumberField

attribute [local instance] arithmeticFiniteLocalStageAlgebra
  arithmeticFiniteLocalStageGalois arithmeticFiniteLocalStageRationalAlgebra

/-- The actual principal character has finite prime support and its finite
sum plus the original real invariant is zero, including the prime two. -/
theorem rationalTwoArithmeticCyclicSubfield_exists_principal_prime_sum
    (a : 𝓞 ℚ) (E : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    [IsCyclic Gal(E/ℚ)] (q : ℚˣ)
    {d : ℕ} [NeZero d] (χ : Gal(E/ℚ) →* Multiplicative (ZMod d))
    (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    (hEF : E.toIntermediateField ≤ F.toIntermediateField)
    (n : ℕ) (hn : 1 ≤ n) [IsCyclotomicExtension {2 ^ (n + 1)} ℚ F] :
    ∃ T : Finset Nat.Primes,
      (∀ p ∉ T, rationalCyclicInvariant d
        (χ (rationalArithmeticFiniteLocalReciprocityAut a E p.val p.property q)).toAdd = 0) ∧
      (∑ p ∈ T, rationalCyclicInvariant d
        (χ (rationalArithmeticFiniteLocalReciprocityAut a E p.val p.property q)).toAdd) +
        rationalCyclicInvariant d (χ (rationalRealArithmeticFiniteRestriction a E
          (if 0 < q.val then 1 else Complex.conjAe))).toAdd = 0 := by
  classical
  obtain ⟨S, hS, hout, hsum⟩ :=
    rationalTwoArithmeticCyclicSubfield_exists_principal_invariant_sum a E q χ F hEF n hn
  let T : Finset Nat.Primes := insert ⟨2, Nat.prime_two⟩
    (S.map Rat.HeightOneSpectrum.primesEquiv.toEmbedding)
  let f : Nat.Primes → AddCircle (1 : ℚ) := fun p => rationalCyclicInvariant d
    (χ (rationalArithmeticFiniteLocalReciprocityAut a E p.val p.property q)).toAdd
  have hnot : (⟨2, Nat.prime_two⟩ : Nat.Primes) ∉
      S.map Rat.HeightOneSpectrum.primesEquiv.toEmbedding := by
    intro hm
    obtain ⟨v, hv, he⟩ := Finset.mem_map.mp hm
    have hgen : Rat.HeightOneSpectrum.natGenerator v = 2 := congrArg Subtype.val he
    apply hS v hv
    rw [hgen]
    exact dvd_pow_self 2 (by omega)
  have hexpand : (∑ p ∈ T, f p) = f ⟨2, Nat.prime_two⟩ +
      ∑ v ∈ S, f (Rat.HeightOneSpectrum.primesEquiv v) := by
    change (insert ⟨2, Nat.prime_two⟩ (S.map Rat.HeightOneSpectrum.primesEquiv.toEmbedding)).sum f = _
    calc
      _ = f ⟨2, Nat.prime_two⟩ + (S.map Rat.HeightOneSpectrum.primesEquiv.toEmbedding).sum f :=
        Finset.sum_insert hnot
      _ = _ := by rw [Finset.sum_map]; rfl
  refine ⟨T, ?_, ?_⟩
  · intro p hp
    have hp2 : p.val ≠ 2 := by
      intro he
      exact hp (Finset.mem_insert.mpr (Or.inl (Subtype.ext he)))
    let v : HeightOneSpectrum ℤ := Rat.HeightOneSpectrum.primesEquiv.symm p
    have he : Rat.HeightOneSpectrum.primesEquiv v = p :=
      Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply p
    have hgen : Rat.HeightOneSpectrum.natGenerator v = p.val := congrArg Subtype.val he
    have hv : v ∉ S := by
      intro hm
      apply hp
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_map.mpr ⟨v, hm, he⟩))
    have hrec := hout v hv (fun heq => hp2 (hgen.symm.trans heq))
    have hrecp : rationalArithmeticFiniteLocalReciprocityAut a E p.val p.property q = 1 := by
      simpa only [hgen] using hrec
    rw [hrecp, map_one, toAdd_one, map_zero]
  · change (∑ p ∈ T, f p) + _ = 0
    rw [hexpand]
    change rationalCyclicInvariant d
        (χ (rationalArithmeticFiniteLocalReciprocityAut a E 2 Nat.prime_two q)).toAdd +
      (∑ v ∈ S, rationalCyclicInvariant d
        (χ (rationalArithmeticFiniteLocalReciprocityAut a E
          (Rat.HeightOneSpectrum.natGenerator v) (Rat.HeightOneSpectrum.prime_natGenerator v) q)).toAdd) +
      rationalCyclicInvariant d (χ (rationalRealArithmeticFiniteRestriction a E
        (if 0 < q.val then 1 else Complex.conjAe))).toAdd = 0
    exact (add_right_comm _ _ _).trans hsum

end
end Dubon2026

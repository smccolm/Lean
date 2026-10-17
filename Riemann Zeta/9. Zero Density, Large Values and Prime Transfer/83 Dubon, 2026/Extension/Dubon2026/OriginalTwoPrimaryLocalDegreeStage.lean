import Dubon2026.TwoPowerCyclicSubfieldLocalDegrees

/-! # A constructed two-primary cyclic splitting subfield in the original union

A single conductor bound handles the prescribed finite support. The
cyclotomic field is placed in the unchanged original unramified union;
the actual totally complex cyclic subfield retains the required completed
degrees. This removes the field-existence and degree assumptions from
DUB-17's two-primary local splitting step. Global killing and continuous
descent are the subsequent dependencies toward the full-order class.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
attribute [-instance] UniformSpace.Completion.instSMul

/-- Construct a cyclotomic stage in the original arithmetic union and a
totally complex cyclic subfield with the required local degrees on all
of the prescribed finite support. -/
theorem originalUnramifiedUnion_exists_two_primary_localDegree_subfield
    {Ω : Type} [Field Ω] [CharZero Ω] [Algebra ℚ Ω] [IsSepClosed Ω]
    (a : 𝓞 ℚ) (r : ℕ) (h2a : (2 : 𝓞 ℚ) ∣ a)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∃ (k : ℕ) (F : FiniteGaloisIntermediateField ℚ Ω),
      letI : NumberField F := NumberField.of_module_finite ℚ F
      r + 2 ≤ k ∧ IsCyclotomicExtension {2 ^ (k + 1)} ℚ F ∧
      F.toIntermediateField ≤ originalUnramifiedGaloisUnion (Ω := Ω) a ∧
      ∃ E : IntermediateField ℚ F,
        IsGalois ℚ E ∧ IsCyclic Gal(E/ℚ) ∧ IsTotallyComplex E ∧
        Module.finrank E F ≤ 2 ∧
        ∀ p ∈ S, ∀ w : HeightOneSpectrum (𝓞 E),
          w.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) →
          let v := originalFinitePrimeBelow ℚ E w
          letI := originalFinitePrimeBelow_liesOver ℚ E w
          letI : Algebra (v.adicCompletion ℚ) (w.adicCompletion E) :=
            (originalAdicBaseChangeMap ℚ E v w).toAlgebra
          2 ^ (r + 1) ∣ Module.finrank (v.adicCompletion ℚ) (w.adicCompletion E) := by
  let b := S.sup fun p => p ^ (2 ^ (r + 1) * (2 - 1)) - 1
  let k := b + r + 2
  have hk : r + 2 ≤ k := by omega
  have hlarge (p : ℕ) (hp : p ∈ S) :
      p ^ (2 ^ (r + 1) * (2 - 1)) - 1 < 2 ^ (k + 1) := by
    have hb : b < 2 ^ b := Nat.lt_pow_self (by decide)
    exact lt_of_le_of_lt (Finset.le_sup (f := fun p => p ^ (2 ^ (r + 1) * (2 - 1)) - 1) hp)
      (hb.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (2 ^ (k + 1))
  let F := originalPrimitiveRootStage ℚ Ω hζ
  letI : NumberField F := NumberField.of_module_finite ℚ F
  have hcycOriginal : @IsCyclotomicExtension {2 ^ (k + 1)} ℚ F _ _ F.algebra' :=
    originalPrimitiveRootStage_isCyclotomic ℚ Ω hζ
  have hrat : (F.algebra' : Algebra ℚ F) = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  have hcyc : IsCyclotomicExtension {2 ^ (k + 1)} ℚ F := hrat ▸ hcycOriginal
  letI := hcyc
  refine ⟨k, F, hk, hcyc, ?_, ?_⟩
  · change IntermediateField.adjoin ℚ ({ζ} : Set Ω) ≤ _
    apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact originalQUnramifiedUnion_mem_of_powerRoot a 2 (k + 1) h2a ζ hζ
  · obtain ⟨E, hgal, hcyclic, hcomplex, hdegree, hlocal⟩ :=
      originalTwoPowerCyclotomic_exists_cyclic_localDegree_subfield k r hk F
    refine ⟨E, hgal, hcyclic, hcomplex, hdegree, ?_⟩
    intro p hp w hw
    letI : Fact p.Prime := ⟨hS p hp⟩
    exact hlocal p (fun _ => hlarge p hp) w hw

end
end Dubon2026

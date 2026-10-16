import Dubon2026.CyclotomicHigherResidueOrder
import Dubon2026.OriginalCyclotomicLocalDegreeStage

/-! # Constructed cyclotomic stages with prime-power local degrees

The original completed-field degree formulas and a single finite conductor
bound construct the local divisibility needed to kill odd-primary classes.
The stage remains inside the actual prescribed unramified Galois union,
as required by DUB-17's reciprocity and full-order class dependency chain.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical

attribute [-instance] UniformSpace.Completion.instSMul in
/-- A large conductor gives prescribed prime-power divisibility of the actual
completion degree, both at its conductor prime and at every away-prime. -/
theorem cyclotomicPrimePower_higher_completion_degree_dvd
    (q k r : ℕ) [hq : Fact q.Prime]
    (L : Type) [Field L] [NumberField L] [IsCyclotomicExtension {q ^ (k + 1)} ℚ L]
    (hk : r + 1 ≤ k) (p : ℕ) [hp : Fact p.Prime]
    (hlarge : p ≠ q → p ^ (q ^ r * (q - 1)) - 1 < q ^ (k + 1))
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver (Ideal.span {(p : ℤ)})] :
    let v := originalFinitePrimeBelow ℚ L w
    letI := originalFinitePrimeBelow_liesOver ℚ L w
    letI : Algebra (v.adicCompletion ℚ) (w.adicCompletion L) :=
      (originalAdicBaseChangeMap ℚ L v w).toAlgebra
    q ^ (r + 1) ∣ Module.finrank (v.adicCompletion ℚ) (w.adicCompletion L) := by
  let v := originalFinitePrimeBelow ℚ L w
  letI := originalFinitePrimeBelow_liesOver ℚ L w
  letI : Algebra (v.adicCompletion ℚ) (w.adicCompletion L) :=
    (originalAdicBaseChangeMap ℚ L v w).toAlgebra
  letI : IsGalois ℚ L := IsCyclotomicExtension.isGalois {q ^ (k + 1)} ℚ L
  change q ^ (r + 1) ∣ Module.finrank (v.adicCompletion ℚ) (w.adicCompletion L)
  rw [originalAdicBaseChange_finrank_eq_decomposition_card ℚ L v w]
  by_cases hpq : p = q
  · subst p
    rw [cyclotomicPrimePower_original_decomposition_order_at q k L w]
    exact dvd_mul_of_dvd_left (pow_dvd_pow q hk) _
  · rw [cyclotomicPrimePower_original_decomposition_order_away q k L p hpq w]
    exact cyclotomicPrimePower_higher_order_dvd_of_large q p k r hq.out hp.out.one_lt
      (fun h => hpq ((Nat.prime_dvd_prime_iff_eq hq.out hp.out).mp h).symm) (hlarge hpq)

attribute [-instance] UniformSpace.Completion.instSMul in
/-- Construct an actual cyclic stage in the original unramified union whose
completion degrees are divisible by the prescribed prime power on the given support. -/
theorem originalCyclotomic_exists_higher_localDegree_stage
    {Ω : Type} [Field Ω] [CharZero Ω] [Algebra ℚ Ω] [IsSepClosed Ω]
    (a : 𝓞 ℚ) (q r : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∃ (k : ℕ) (F : FiniteGaloisIntermediateField ℚ Ω),
      letI : NumberField F := NumberField.of_module_finite ℚ F
      r + 1 ≤ k ∧ IsCyclotomicExtension {q ^ (k + 1)} ℚ F ∧ IsCyclic Gal(F/ℚ) ∧
      F.toIntermediateField ≤ originalUnramifiedGaloisUnion (Ω := Ω) a ∧
      ∀ (p : ℕ), p ∈ S → ∀ (w : HeightOneSpectrum (𝓞 F)),
        w.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) →
        let v := originalFinitePrimeBelow ℚ F w
        letI := originalFinitePrimeBelow_liesOver ℚ F w
        letI : Algebra (v.adicCompletion ℚ) (w.adicCompletion F) :=
          (originalAdicBaseChangeMap ℚ F v w).toAlgebra
        q ^ (r + 1) ∣ Module.finrank (v.adicCompletion ℚ) (w.adicCompletion F) := by
  letI : Fact q.Prime := ⟨hq⟩
  letI : NeZero q := ⟨hq.ne_zero⟩
  let b := S.sup fun p => p ^ (q ^ r * (q - 1)) - 1
  let k := b + r + 1
  have hk : r + 1 ≤ k := by omega
  have hlarge (p : ℕ) (hp : p ∈ S) : p ^ (q ^ r * (q - 1)) - 1 < q ^ (k + 1) := by
    have hb : b < q ^ b := Nat.lt_pow_self hq.one_lt
    exact lt_of_le_of_lt (Finset.le_sup (f := fun p => p ^ (q ^ r * (q - 1)) - 1) hp)
      (hb.trans_le (Nat.pow_le_pow_right hq.pos (by omega)))
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (q ^ (k + 1))
  let F := originalPrimitiveRootStage ℚ Ω hζ
  letI : NumberField F := NumberField.of_module_finite ℚ F
  have hcycOriginal : @IsCyclotomicExtension {q ^ (k + 1)} ℚ F _ _ F.algebra' :=
    originalPrimitiveRootStage_isCyclotomic ℚ Ω hζ
  have hrat : (F.algebra' : Algebra ℚ F) = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  have hcyc : IsCyclotomicExtension {q ^ (k + 1)} ℚ F := hrat ▸ hcycOriginal
  letI := hcyc
  refine ⟨k, F, hk, hcyc, ?_, ?_, ?_⟩
  · exact cyclotomicPrimePower_galois_isCyclic q k F hq2
  · change IntermediateField.adjoin ℚ ({ζ} : Set Ω) ≤ _
    apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact originalQUnramifiedUnion_mem_of_powerRoot a q (k + 1) hqa ζ hζ
  · intro p hp w hw
    letI : Fact p.Prime := ⟨hS p hp⟩
    letI : w.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := hw
    exact cyclotomicPrimePower_higher_completion_degree_dvd q k r F hk p (fun _ => hlarge p hp) w

end
end Dubon2026

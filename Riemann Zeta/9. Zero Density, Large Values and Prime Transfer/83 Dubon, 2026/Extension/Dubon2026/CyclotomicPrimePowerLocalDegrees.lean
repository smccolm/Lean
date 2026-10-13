import Dubon2026.CyclotomicPrimePowerResidueOrder
import Dubon2026.OriginalAdicDecompositionDegree
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.NumberTheory.Cyclotomic.Gal

/-! # Actual local degrees in prime-power cyclotomic extensions

Pinned cyclotomic residue and ramification formulas are transported to
the original decomposition groups. Odd auxiliary-prime power extensions
are cyclic, and one sufficiently large conductor gives the degree
divisibility needed to kill the finitely supported local H2 invariants
on DUB-17's reciprocity/global-duality dependency chain.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField
variable (q k : ℕ) [hq : Fact q.Prime]
  (L : Type) [Field L] [NumberField L] [hL : IsCyclotomicExtension {q ^ (k + 1)} ℚ L]

include hL in
/-- An actual odd-prime-power cyclotomic number field has cyclic original Galois group. -/
theorem cyclotomicPrimePower_galois_isCyclic (hq2 : q ≠ 2) : IsCyclic Gal(L/ℚ) := by
  letI : NeZero q := ⟨hq.out.ne_zero⟩
  letI := ZMod.isCyclic_units_of_prime_pow q hq.out hq2 (k + 1)
  let hζ := IsCyclotomicExtension.zeta_spec (q ^ (k + 1)) ℚ L
  exact isCyclic_of_injective (hζ.autToPow ℚ) (hζ.autToPow_injective ℚ)

/-- At an away-prime the actual original decomposition order equals its multiplicative residue order. -/
theorem cyclotomicPrimePower_original_decomposition_order_away
    (p : ℕ) [hp : Fact p.Prime] (hpq : p ≠ q)
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver (Ideal.span {(p : ℤ)})] :
    Nat.card (OriginalFiniteDecompositionGroup ℚ L w) =
      orderOf (p : ZMod (q ^ (k + 1))) := by
  letI : NeZero q := ⟨hq.out.ne_zero⟩
  letI : IsGalois ℚ L := IsCyclotomicExtension.isGalois {q ^ (k + 1)} ℚ L
  have hpn : ¬ p ∣ q ^ (k + 1) := by
    intro h
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp.out hq.out).mp (hp.out.dvd_of_dvd_pow h))
  rw [originalRationalDecomposition_card_eq L p w,
    IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd p L w.asIdeal hpn,
    IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd p L w.asIdeal hpn, one_mul]

/-- At the conductor prime the actual original decomposition order is the full ramification degree. -/
theorem cyclotomicPrimePower_original_decomposition_order_at
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver (Ideal.span {(q : ℤ)})] :
    Nat.card (OriginalFiniteDecompositionGroup ℚ L w) = q ^ k * (q - 1) := by
  letI : IsGalois ℚ L := IsCyclotomicExtension.isGalois {q ^ (k + 1)} ℚ L
  rw [originalRationalDecomposition_card_eq L q w,
    IsCyclotomicExtension.Rat.ramificationIdx_eq_of_prime_pow q k L w.asIdeal,
    IsCyclotomicExtension.Rat.inertiaDeg_eq_of_prime_pow q k L w.asIdeal, mul_one]

/-- One large prime-power conductor gives actual original decomposition-degree divisibility at each specified prime, including the conductor prime. -/
theorem cyclotomicPrimePower_original_decomposition_dvd
    (hk : 1 ≤ k) (p : ℕ) [hp : Fact p.Prime]
    (hlarge : p ≠ q → p ^ (q - 1) - 1 < q ^ (k + 1))
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver (Ideal.span {(p : ℤ)})] :
    q ∣ Nat.card (OriginalFiniteDecompositionGroup ℚ L w) := by
  by_cases hpq : p = q
  · subst p
    rw [cyclotomicPrimePower_original_decomposition_order_at q k L w]
    exact dvd_mul_of_dvd_left (dvd_pow_self q (by omega)) _
  · rw [cyclotomicPrimePower_original_decomposition_order_away q k L p hpq w]
    apply cyclotomicPrimePower_order_dvd_of_large q p k hq.out hp.out.one_lt
      (fun h => hpq ((Nat.prime_dvd_prime_iff_eq hq.out hp.out).mp h).symm) (hlarge hpq)

attribute [-instance] UniformSpace.Completion.instSMul in
/-- The same divisibility holds for the actual original completed extension degree. -/
theorem cyclotomicPrimePower_original_completion_degree_dvd
    (hk : 1 ≤ k) (p : ℕ) [Fact p.Prime]
    (hlarge : p ≠ q → p ^ (q - 1) - 1 < q ^ (k + 1))
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver (Ideal.span {(p : ℤ)})] :
    let v := originalFinitePrimeBelow ℚ L w
    letI := originalFinitePrimeBelow_liesOver ℚ L w
    letI : Algebra (v.adicCompletion ℚ) (w.adicCompletion L) :=
      (originalAdicBaseChangeMap ℚ L v w).toAlgebra
    q ∣ Module.finrank (v.adicCompletion ℚ) (w.adicCompletion L) := by
  let v := originalFinitePrimeBelow ℚ L w
  letI := originalFinitePrimeBelow_liesOver ℚ L w
  letI : Algebra (v.adicCompletion ℚ) (w.adicCompletion L) :=
    (originalAdicBaseChangeMap ℚ L v w).toAlgebra
  letI : IsGalois ℚ L := IsCyclotomicExtension.isGalois {q ^ (k + 1)} ℚ L
  change q ∣ Module.finrank (v.adicCompletion ℚ) (w.adicCompletion L)
  rw [originalAdicBaseChange_finrank_eq_decomposition_card ℚ L v w]
  exact cyclotomicPrimePower_original_decomposition_dvd q k L hk p hlarge w

end
end Dubon2026

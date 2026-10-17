import Dubon2026.ArithmeticCyclicPrimePowerSubfield
import Dubon2026.TwoPowerCyclotomicComplexSubfield

/-! # Cyclic two-power fields inside the original arithmetic union

The native cyclotomic character gives a cyclic subfield of index at most
two. Its actual degree and the native cyclic degree-divisor theorem give
every prescribed two-power degree. This removes the odd-prime condition
from the auxiliary-field input for DUB-17's original class-generator transfer.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat
attribute [local instance] arithmeticOrbitLocalUnionAlgebra

/-- The original arithmetic union contains a cyclic Galois field of every
two-power degree when two is among the allowed ramified primes. -/
theorem rationalArithmetic_exists_cyclic_twoPower_subfield
    (a : 𝓞 ℚ) (n : ℕ) (h2a : (2 : 𝓞 ℚ) ∣ a) :
    ∃ D : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a),
      IsCyclic Gal(D/ℚ) ∧ Module.finrank ℚ D = 2 ^ n := by
  letI : NeZero (2 ^ (n + 3)) := ⟨by positivity⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) (2 ^ (n + 3))
  let F := originalPrimitiveRootStage ℚ (AlgebraicClosure ℚ) hζ
  have hcycl : @IsCyclotomicExtension {2 ^ (n + 3)} ℚ F _ _ F.algebra' :=
    originalPrimitiveRootStage_isCyclotomic ℚ (AlgebraicClosure ℚ) hζ
  letI : IsCyclotomicExtension {2 ^ (n + 3)} ℚ F := hcycl
  have hF : F.toIntermediateField ≤ originalUnramifiedGaloisUnion (Ω := AlgebraicClosure ℚ) a := by
    change IntermediateField.adjoin ℚ ({ζ} : Set (AlgebraicClosure ℚ)) ≤ _
    apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact originalQUnramifiedUnion_mem_of_powerRoot a 2 (n + 3) h2a ζ hζ
  obtain ⟨E, hgalE, hcyclicE, hindex, _⟩ :=
    originalTwoPowerCyclotomic_exists_complex_cyclic_subfield ℚ F n
  letI : IsGalois ℚ E := hgalE
  letI : IsCyclic Gal(E/ℚ) := hcyclicE
  have hdegree : Module.finrank ℚ F = 2 ^ (n + 2) := by
    rw [IsCyclotomicExtension.finrank F
      (Polynomial.cyclotomic.irreducible_rat (NeZero.pos (2 ^ (n + 3))))]
    simp only [show n + 3 = (n + 2) + 1 by omega,
      Nat.totient_prime_pow_succ Nat.prime_two, Nat.reduceSub, mul_one]
  have ht := Module.finrank_mul_finrank ℚ E F
  have hi : Module.finrank E F = 1 ∨ Module.finrank E F = 2 := by
    have hp := Module.finrank_pos (R := E) (M := F)
    omega
  have hd : 2 ^ n ∣ Module.finrank ℚ E := by
    rcases hi with hi | hi
    · rw [hi, mul_one, hdegree] at ht
      rw [ht]
      exact pow_dvd_pow 2 (by omega)
    · rw [hi, hdegree] at ht
      have he : Module.finrank ℚ E = 2 ^ (n + 1) := by
        have hp : 2 ^ (n + 2) = 2 ^ (n + 1) * 2 := by
          simpa only [show n + 2 = (n + 1) + 1 by omega] using (pow_succ 2 (n + 1))
        omega
      rw [he]
      exact pow_dvd_pow 2 (by omega)
  obtain ⟨D, hgalD, hcyclicD, hD⟩ := originalCyclic_exists_intermediate_degree
    ℚ E (2 ^ n) (by positivity) hd
  letI : IsGalois ℚ D := hgalD
  let i : D →ₐ[ℚ] rationalUnramifiedExtension a :=
    (IntermediateField.inclusion hF).comp (E.val.comp D.val)
  let C := finiteGaloisEmbeddingStage i
  let e := finiteGaloisEmbeddingStageEquiv i
  exact ⟨C, e.autCongr.isCyclic.mp hcyclicD, e.toLinearEquiv.finrank_eq.symm.trans hD⟩

/-- All allowed primes have actual cyclic fields of every prime-power
degree in the unchanged arithmetic union. -/
theorem rationalArithmetic_exists_cyclic_allPrimePower_subfield
    (a : 𝓞 ℚ) (q n : ℕ) (hq : q.Prime) (hqa : (q : 𝓞 ℚ) ∣ a) :
    ∃ D : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a),
      IsCyclic Gal(D/ℚ) ∧ Module.finrank ℚ D = q ^ n := by
  by_cases hq2 : q = 2
  · subst q
    exact rationalArithmetic_exists_cyclic_twoPower_subfield a n hqa
  · exact rationalArithmetic_exists_cyclic_primePower_subfield a q n hq hq2 hqa

end
end Dubon2026

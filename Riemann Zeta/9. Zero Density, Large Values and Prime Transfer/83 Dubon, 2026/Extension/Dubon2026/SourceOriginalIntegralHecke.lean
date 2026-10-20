import Dubon2026.SourceHeckePrimeAdjoint
import Dubon2026.SourcePrimeHeckeGeneration

/-! Finite integral Hecke algebra for the actual original Gamma0 cusp space.
DUB-17 Theorem 2.6 and DUB-18 Corollary 8.2 -> higher symmetric-power continuation
-> modular Galois association -> coefficient-field arithmetic.
The actual convergent period map, its injectivity, finite integral symbol module
and original Hecke adjoints are constructed. No pairing, lattice, injectivity,
finite-generation or Hecke-compatibility premise remains in the finite-algebra
consumer. The Galois association and higher automorphy obligations remain separate.
-/

namespace Dubon2026
noncomputable section
open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

private def originalPrimeIntegralAdjoint (Q : ℕ) (k : ℤ)
    (p : {p : ℕ // Nat.Prime p}) :
    Module.End ℤ (SourceModularSymbols ℤ (Gamma0 Q) (k - 2).toNat) := by
  haveI : NeZero p.val := ⟨p.property.ne_zero⟩
  exact SourceModularSymbols.integralHeckePrime ℤ (k - 2).toNat Q p.property

private theorem originalPrimeIntegralAdjoint_pairing
    (Q : ℕ) [NeZero Q] (k : ℤ) (hk : 2 ≤ k)
    (p : {p : ℕ // Nat.Prime p}) f x :
    sourceOriginalPeriodMap Q k hk (cuspHeckeLinear Q k p.val f) x =
      sourceOriginalPeriodMap Q k hk f (originalPrimeIntegralAdjoint Q k p x) := by
  haveI : NeZero p.val := ⟨p.property.ne_zero⟩
  rw [cuspHeckeLinear_prime Q k p.property]
  exact congrArg (fun L => L x)
    (SourceModularSymbols.periodMap_integralHeckePrime (R := ℤ) p.property f (by omega))

private theorem originalIntegralAdjoint_exists (Q : ℕ) [NeZero Q] (k : ℤ) (hk : 2 ≤ k)
    (n : ℕ+) :
    ∃ v : Module.End ℤ (SourceModularSymbols ℤ (Gamma0 Q) (k - 2).toNat),
      ∀ f x, sourceOriginalPeriodMap Q k hk (cuspHeckeLinear Q k (n : ℕ) f) x =
        sourceOriginalPeriodMap Q k hk f (v x) :=
  sourceOriginalHeckeAdjoint_exists_of_prime Q k hk (originalPrimeIntegralAdjoint Q k)
    (originalPrimeIntegralAdjoint_pairing Q k hk) n

/-- Constructed integral adjoint for every positive-index original Hecke operator. -/
def sourceOriginalIntegralHeckeAdjoint (Q : ℕ) [NeZero Q] (k : ℤ) (hk : 2 ≤ k) (n : ℕ+) :
    Module.End ℤ (SourceModularSymbols ℤ (Gamma0 Q) (k - 2).toNat) :=
  (originalIntegralAdjoint_exists Q k hk n).choose

/-- The constructed integral operator is adjoint to the actual original Hecke operator. -/
theorem sourceOriginalIntegralHeckeAdjoint_pairing
    (Q : ℕ) [NeZero Q] (k : ℤ) (hk : 2 ≤ k) (n : ℕ+) f x :
    sourceOriginalPeriodMap Q k hk (cuspHeckeLinear Q k (n : ℕ) f) x =
      sourceOriginalPeriodMap Q k hk f (sourceOriginalIntegralHeckeAdjoint Q k hk n x) :=
  (originalIntegralAdjoint_exists Q k hk n).choose_spec f x

/-- The integral algebra of the actual original Hecke operators is finite at every source weight. -/
theorem sourceOriginalIntegralHeckeAlgebra_finite (Q : ℕ) [NeZero Q] (k : ℤ) (hk : 2 ≤ k) :
    Module.Finite ℤ (sourceOriginalIntegralHeckeAlgebra Q k) :=
  sourceOriginalIntegralHeckeAlgebra_finite_of_adjoint Q k hk
    (sourceOriginalIntegralHeckeAdjoint Q k hk) (sourceOriginalIntegralHeckeAdjoint_pairing Q k hk)

/-- Every actual original positive-index Hecke operator is integral over the integers. -/
theorem sourceOriginalHecke_isIntegral (Q : ℕ) [NeZero Q] (k : ℤ) (hk : 2 ≤ k) (n : ℕ+) :
    IsIntegral ℤ (cuspHeckeLinear Q k (n : ℕ)) := by
  letI := sourceOriginalIntegralHeckeAlgebra_finite Q k hk
  have hn : cuspHeckeLinear Q k (n : ℕ) ∈ sourceOriginalIntegralHeckeAlgebra Q k :=
    Algebra.subset_adjoin ⟨n, rfl⟩
  exact (IsIntegral.of_finite ℤ
    (⟨cuspHeckeLinear Q k (n : ℕ), hn⟩ : sourceOriginalIntegralHeckeAlgebra Q k)).map
      (sourceOriginalIntegralHeckeAlgebra Q k).val

end
end Dubon2026

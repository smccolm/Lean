import Dubon2026.SourcePeriodInjective
import Dubon2026.SourceOriginalPeriodMap

/-! Injectivity discharged for the actual original Gamma0 period map.
DUB-17/18 -> modular Galois association -> integral Hecke finiteness.
This reduction takes integral adjoints for the original positive-index Hecke
action as input. SourceOriginalIntegralHecke constructs them and proves adjointness.
-/

namespace Dubon2026
noncomputable section
open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

/-- The constructed original period map is injective for every source weight at least two. -/
theorem sourceOriginalPeriodMap_injective (Q : ℕ) [NeZero Q] (k : ℤ) (hk : 2 ≤ k) :
    Function.Injective (sourceOriginalPeriodMap Q k hk) :=
  SourceModularSymbols.periodMap_injective (R := ℤ) (Γ := Gamma0 Q) (by omega)

/-- With actual integral adjoint operators, the original integral Hecke algebra is finite; injectivity and finite cycles are now derived. -/
theorem sourceOriginalIntegralHeckeAlgebra_finite_of_adjoint
    (Q : ℕ) [NeZero Q] (k : ℤ) (hk : 2 ≤ k)
    (u : ℕ+ → Module.End ℤ (SourceModularSymbols ℤ (Gamma0 Q) (k - 2).toNat))
    (h : ∀ (n : ℕ+) f x,
      sourceOriginalPeriodMap Q k hk (cuspHeckeLinear Q k (n : ℕ) f) x =
        sourceOriginalPeriodMap Q k hk f (u n x)) :
    Module.Finite ℤ (sourceOriginalIntegralHeckeAlgebra Q k) :=
  sourceOriginalIntegralHeckeAlgebra_finite_of_actual_period Q k hk
    (sourceOriginalPeriodMap_injective Q k hk) u h

/-- Original positive-index Hecke integrality from actual adjointness, with period injectivity proved. -/
theorem sourceOriginalHecke_isIntegral_of_adjoint
    (Q : ℕ) [NeZero Q] (k : ℤ) (hk : 2 ≤ k)
    (u : ℕ+ → Module.End ℤ (SourceModularSymbols ℤ (Gamma0 Q) (k - 2).toNat))
    (h : ∀ (n : ℕ+) f x,
      sourceOriginalPeriodMap Q k hk (cuspHeckeLinear Q k (n : ℕ) f) x =
        sourceOriginalPeriodMap Q k hk f (u n x))
    (n : ℕ+) :
    IsIntegral ℤ (cuspHeckeLinear Q k (n : ℕ)) :=
  sourceOriginalHecke_isIntegral_of_actual_period Q k hk
    (sourceOriginalPeriodMap_injective Q k hk) u h n

end
end Dubon2026

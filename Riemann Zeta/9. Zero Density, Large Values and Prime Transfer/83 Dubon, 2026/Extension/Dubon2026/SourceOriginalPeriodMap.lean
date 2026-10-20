import Dubon2026.SourcePeriodMap
import Dubon2026.SourceOriginalHeckePeriodReduction

/-! The constructed period map on the original Gamma0 cusp space.
DUB-17/18 -> modular Galois association -> integral Hecke finiteness.
The period map is now the actual convergent cusp integral on the existing
integral symbols. Its injectivity and adjointness to the original Hecke
operators are explicit inputs of this reduction, discharged in SourceOriginalIntegralHecke.
-/

namespace Dubon2026
noncomputable section
open Matrix.SpecialLinearGroup CongruenceSubgroup MvPolynomial
open scoped MatrixGroups

/-- The actual period map of the original Gamma0 cusp forms, with the original weight. -/
def sourceOriginalPeriodMap (Q : ℕ) [NeZero Q] (k : ℤ) (hk : 2 ≤ k) :
    CuspForm ((Gamma0 Q).map (mapGL ℝ)) k →ₗ[ℂ]
      (SourceModularSymbols ℤ (Gamma0 Q) (k - 2).toNat →ₗ[ℤ] ℂ) :=
  SourceModularSymbols.periodMap ℤ (Gamma0 Q) (by omega)

/-- The constructed original period functional evaluates to the genuine convergent cusp integral. -/
theorem sourceOriginalPeriodMap_symbol (Q : ℕ) [NeZero Q] (k : ℤ) (hk : 2 ≤ k)
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (α β : OnePoint ℚ)
    (P : homogeneousSubmodule (Fin 2) ℤ (k - 2).toNat) :
    sourceOriginalPeriodMap Q k hk f
      (SourceModularSymbols.symbol (R := ℤ) (w := (k - 2).toNat) (Gamma0 Q) α β P) =
      sourceCuspIntegral (SourceModularSymbols.periodIntegrand f P) β α :=
  SourceModularSymbols.periodMap_symbol _ f α β P

/-- Finite integral Hecke algebra from injectivity and adjointness of the constructed original period map. -/
theorem sourceOriginalIntegralHeckeAlgebra_finite_of_actual_period
    (Q : ℕ) [NeZero Q] (k : ℤ) (hk : 2 ≤ k)
    (hP : Function.Injective (sourceOriginalPeriodMap Q k hk))
    (u : ℕ+ → Module.End ℤ (SourceModularSymbols ℤ (Gamma0 Q) (k - 2).toNat))
    (h : ∀ (n : ℕ+) f x,
      sourceOriginalPeriodMap Q k hk (cuspHeckeLinear Q k (n : ℕ) f) x =
        sourceOriginalPeriodMap Q k hk f (u n x)) :
    Module.Finite ℤ (sourceOriginalIntegralHeckeAlgebra Q k) :=
  sourceOriginalIntegralHeckeAlgebra_finite_of_period Q k
    (sourceOriginalPeriodMap Q k hk) hP u h

/-- Every original positive-index Hecke operator is integral once the constructed period map's injectivity and adjointness are proved. -/
theorem sourceOriginalHecke_isIntegral_of_actual_period
    (Q : ℕ) [NeZero Q] (k : ℤ) (hk : 2 ≤ k)
    (hP : Function.Injective (sourceOriginalPeriodMap Q k hk))
    (u : ℕ+ → Module.End ℤ (SourceModularSymbols ℤ (Gamma0 Q) (k - 2).toNat))
    (h : ∀ (n : ℕ+) f x,
      sourceOriginalPeriodMap Q k hk (cuspHeckeLinear Q k (n : ℕ) f) x =
        sourceOriginalPeriodMap Q k hk f (u n x))
    (n : ℕ+) :
    IsIntegral ℤ (cuspHeckeLinear Q k (n : ℕ)) :=
  sourceOriginalHecke_isIntegral_of_period Q k (sourceOriginalPeriodMap Q k hk) hP u h n

end
end Dubon2026

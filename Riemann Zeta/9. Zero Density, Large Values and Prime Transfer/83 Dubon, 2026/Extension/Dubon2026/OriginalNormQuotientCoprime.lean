/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the retained NYLL-ClassFieldTheory-LICENSE.txt.
The coprime-order cancellation argument is adapted to the original additive norm quotient.
-/
import Dubon2026.OriginalIdeleClassNativeNormQuotient

/-! # Coprime cancellation in the literal original norm quotient

The already proved degree annihilation and pinned additive-order divisibility
give coprime cancellation directly on the actual quotient. Consequently an
original class whose coprime power is a norm is itself a norm. This is the
exact cancellation required after tower transitivity for cyclotomic descent
in DUB-17's prime norm-index dependency.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]

/-- Multiplication by an integer coprime to the degree is injective on the
literal original class norm quotient. -/
theorem originalIdeleClassNormQuotient_coprime_nsmul_injective
    (d : ℕ) (hd : d.Coprime (Module.finrank K L)) :
    Function.Injective (fun x : OriginalIdeleClassNormQuotient K L => d • x) := by
  intro x y h
  change d • x = d • y at h
  have hD : d • (x - y) = 0 := by rw [nsmul_sub, h, sub_self]
  have hOrder : addOrderOf (x - y) ∣ Nat.gcd d (Module.finrank K L) :=
    Nat.dvd_gcd (addOrderOf_dvd_of_nsmul_eq_zero hD)
      (addOrderOf_dvd_of_nsmul_eq_zero (originalIdeleClassNormQuotient_degree_nsmul_zero K L (x - y)))
  rw [hd.gcd_eq_one] at hOrder
  exact sub_eq_zero.mp (AddMonoid.addOrderOf_eq_one_iff.mp (Nat.dvd_one.mp hOrder))

/-- A coprime power being an original norm forces the original class to be a norm. -/
theorem originalIdeleClassNorm_mem_of_coprime_pow
    (d : ℕ) (hd : d.Coprime (Module.finrank K L))
    (c : OriginalNumberFieldIdeleClassGroup K)
    (hc : c ^ d ∈ (originalIdeleClassNorm K L).range) :
    c ∈ (originalIdeleClassNorm K L).range := by
  let π := (originalIdeleClassNormLinear K L).range.mkQ
  have hPow : d • π (Additive.ofMul c) = 0 := by
    rw [← map_nsmul]
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    obtain ⟨b, hb⟩ := hc
    exact ⟨Additive.ofMul b, congrArg Additive.ofMul hb⟩
  have hZero : π (Additive.ofMul c) = 0 :=
    originalIdeleClassNormQuotient_coprime_nsmul_injective K L d hd
      (hPow.trans (nsmul_zero d).symm)
  obtain ⟨b, hb⟩ := (Submodule.Quotient.mk_eq_zero _).mp hZero
  exact ⟨b.toMul, congrArg Additive.toMul hb⟩

end
end Dubon2026

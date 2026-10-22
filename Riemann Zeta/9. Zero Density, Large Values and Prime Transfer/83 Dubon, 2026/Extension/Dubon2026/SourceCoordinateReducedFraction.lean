import Dubon2026.SourceConstantFieldTraceOrders
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma

/-! DUB-17/18 -> arithmetic Picard injectivity -> principal-divisor descent
-> rational coordinate traces. Adapted from
S_AlgebraicCurve_mem_span_range_algebraMap_of_constantFieldExtension,
anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
Only reduced rational fractions and denominator-root descent are selected.
Actual original fiber existence and trace regularity discharge the premises.
-/
namespace Dubon2026.SourceCurve.ConstantField
noncomputable section
open Polynomial

theorem exists_coprime_fraction_of_mem {K F : Type*} [Field K] [Field F] [Algebra K F]
    {x t : F} (ht : t ∈ IntermediateField.adjoin K (Set.singleton x)) (ht0 : t ≠ 0) :
    ∃ p q : K[X], IsCoprime p q ∧ q ≠ 0 ∧ aeval x q ≠ 0 ∧ aeval x p ≠ 0 ∧
      t = aeval x p / aeval x q := by
  classical
  obtain ⟨p₀, q₀, hpq₀⟩ := (IntermediateField.mem_adjoin_simple_iff (F := K) (α := x) t).mp ht
  have hq₀0 : q₀ ≠ 0 := by
    rintro rfl
    apply ht0
    rw [hpq₀, map_zero, div_zero]
  have haq₀ : aeval x q₀ ≠ 0 := by
    intro h
    apply ht0
    rw [hpq₀, h, div_zero]

  set g := gcd p₀ q₀ with hg
  have hg0 : g ≠ 0 := fun h => hq₀0 ((gcd_eq_zero_iff p₀ q₀).1 h).2
  set p := p₀ / g with hp
  set q := q₀ / g with hq
  have hcop : IsCoprime p q := isCoprime_div_gcd_div_gcd hq₀0
  have hp₀ : p₀ = g * p := (EuclideanDomain.mul_div_cancel' hg0 (gcd_dvd_left _ _)).symm
  have hq₀' : q₀ = g * q := (EuclideanDomain.mul_div_cancel' hg0 (gcd_dvd_right _ _)).symm
  have hag : aeval x g ≠ 0 := by
    intro h
    apply haq₀
    rw [hq₀', map_mul, h, zero_mul]
  have haq : aeval x q ≠ 0 := by
    intro h
    apply haq₀
    rw [hq₀', map_mul, h, mul_zero]
  have hq0 : q ≠ 0 := by
    rintro h
    exact haq (by rw [h, map_zero])
  have ht' : t = aeval x p / aeval x q := by
    rw [hpq₀, hp₀, hq₀', map_mul, map_mul, mul_div_mul_left _ _ hag]
  have hap : aeval x p ≠ 0 := by
    intro h
    apply ht0
    rw [ht', h, zero_div]

  exact ⟨p, q, hcop, hq0, haq, hap, ht'⟩

theorem aeval_mem {k L : Type*} [Field k] [Field L] [Algebra k L]
    (w : Place k L) {t : L} (ht : t ∈ w.toValuationSubring) (p : k[X]) :
    aeval t p ∈ w.toValuationSubring := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | monomial n a =>
    rw [aeval_monomial]
    exact mul_mem (w.algebraMap_mem' a) (pow_mem ht n)

end
end Dubon2026.SourceCurve.ConstantField

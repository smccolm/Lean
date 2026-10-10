import Dubon2026.EmptySelmerClassKernel
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.GroupTheory.FiniteAbelian.Basic

/-! # Finiteness of the actual number-field Selmer groups -/

namespace Dubon2026

open scoped NumberField

noncomputable section
open IsDedekindDomain
open scoped nonZeroDivisors

/-- The image of original ordinary units in the actual empty-set Selmer group is finite for every positive exponent. -/
theorem numberField_emptySelmer_unitRange_finite (K : Type*) [Field K] [NumberField K]
    (n : ℕ) (hn : n ≠ 0) :
    Finite (IsDedekindDomain.selmerGroup.fromUnit (R := 𝓞 K) (K := K) (n := n)).range := by
  letI : Fact (0 < n) := ⟨Nat.pos_of_ne_zero hn⟩
  letI : Group.FG (𝓞 K)ˣ := Group.fg_iff_monoid_fg.mpr inferInstance
  let f := IsDedekindDomain.selmerGroup.fromUnit (R := 𝓞 K) (K := K) (n := n)
  have hker : f.ker = (powMonoidHom (α := (𝓞 K)ˣ) n).range :=
    IsDedekindDomain.selmerGroup.fromUnit_ker
  letI : Finite ((𝓞 K)ˣ ⧸ f.ker) := by
    rw [hker]
    exact CommGroup.finite_of_fg_torsion _
      (CommGroup.isTorsion_quotient_range_powMonoidHom (𝓞 K)ˣ hn)
  exact Finite.of_equiv ((𝓞 K)ˣ ⧸ f.ker)
    (QuotientGroup.quotientKerEquivRange f).toEquiv

/-- The genuine empty-set Selmer group of every number field is finite for each positive exponent. -/
theorem numberField_emptySelmer_finite (K : Type*) [Field K] [NumberField K]
    (n : ℕ) (hn : n ≠ 0) :
    Finite (IsDedekindDomain.selmerGroup (R := 𝓞 K) (K := K) (S := ∅) (n := n)) := by
  let f := emptySelmerClassMap (R := 𝓞 K) (K := K) n hn
  letI : Finite (OriginalFractionalIdealClassQuotient (R := 𝓞 K) (K := K)) :=
    Finite.of_equiv (ClassGroup (𝓞 K)) (ClassGroup.equiv K).toEquiv
  letI : Finite f.ker := by
    change Finite (emptySelmerClassMap (R := 𝓞 K) (K := K) n hn).ker
    rw [emptySelmerClassMap_kernel_eq_unitRange]
    exact numberField_emptySelmer_unitRange_finite K n hn
  exact f.finite_iff_finite_ker_range.mpr ⟨inferInstance, inferInstance⟩

/-- The actual Selmer group of every number field, finite set of original primes and positive exponent is finite. -/
theorem numberField_selmer_finite (K : Type*) [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite) (n : ℕ) (hn : n ≠ 0) :
    Finite (IsDedekindDomain.selmerGroup (R := 𝓞 K) (K := K) (S := S) (n := n)) := by
  letI : Fintype S := hS.fintype
  letI : NeZero n := ⟨hn⟩
  letI := numberField_emptySelmer_finite K n hn
  let f := IsDedekindDomain.selmerGroup.valuation (R := 𝓞 K) (K := K) (S := S) (n := n)
  letI : Finite f.ker := by
    change Finite (IsDedekindDomain.selmerGroup.valuation
      (R := 𝓞 K) (K := K) (S := S) (n := n)).ker
    rw [IsDedekindDomain.selmerGroup.valuation_ker_eq]
    let e := Subgroup.subgroupOfEquivOfLe
      (IsDedekindDomain.selmerGroup.monotone
        (R := 𝓞 K) (K := K) (n := n) (S := ∅) (S' := S) (Set.empty_subset S))
    exact Finite.of_equiv
      (IsDedekindDomain.selmerGroup (R := 𝓞 K) (K := K) (S := ∅) (n := n)) e.toEquiv.symm
  exact f.finite_iff_finite_ker_range.mpr ⟨inferInstance, inferInstance⟩

end
end Dubon2026

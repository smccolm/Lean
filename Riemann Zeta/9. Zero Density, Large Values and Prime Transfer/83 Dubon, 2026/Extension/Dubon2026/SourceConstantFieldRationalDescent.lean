import Dubon2026.SourceCoordinateReducedFraction
import Mathlib.FieldTheory.IsAlgClosed.Basic

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

variable {K F K' F' : Type*} [Field K] [Field F] [Field K'] [Field F'] [Algebra K F]
  [Algebra K' F'] [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F']
  [IsScalarTower K F F']

variable (F F') in
theorem span_range_eq_adjoin (R : Type*) [CommSemiring R] [Algebra R F'] :
    Subalgebra.toSubmodule (Algebra.adjoin R (Set.range (algebraMap F F'))) =
      Submodule.span R (Set.range (algebraMap F F')) := by
  rw [Algebra.adjoin_eq_span]
  have : Set.range (algebraMap F F') = ((algebraMap F F').range.toSubmonoid : Set F') := by
    ext y; simp
  rw [this, Submonoid.closure_eq]

theorem mem_span_of_coordinate_regular [IsAlgClosed K'] {x : F}
    (hvalues : ∀ c : K', ∃ v' : Place K' F',
      0 < v'.ord (algebraMap F F' x - algebraMap K' F' c))
    {t : F'} (ht : t ∈ IntermediateField.adjoin K' (Set.singleton (algebraMap F F' x)))
    (hreg : ∀ c : K', c ∉ Set.range (algebraMap K K') →
      ∀ v' : Place K' F', 0 < v'.ord (algebraMap F F' x - algebraMap K' F' c) →
        0 ≤ v'.ord t) : t ∈ Submodule.span K' (Set.range (algebraMap F F')) := by
  classical
  set x' := algebraMap F F' x with hx'def
  rcases eq_or_ne t 0 with rfl | ht0
  · exact zero_mem _
  obtain ⟨p, q, hcop, hq0, haq, hap, ht'⟩ := exists_coprime_fraction_of_mem ht ht0
  have hroots : ∀ c ∈ q.roots, c ∈ Set.range (algebraMap K K') := by
    intro c hc
    by_contra hcK
    have hqc : q.IsRoot c := (mem_roots hq0).1 hc
    obtain ⟨v', hv'⟩ := hvalues c
    have h0t := hreg c hcK v' hv'
    have hsub_ne : x' - algebraMap K' F' c ≠ 0 := by
      intro h
      rw [h, Place.ord_zero] at hv'
      exact lt_irrefl _ hv'
    have hx'mem : x' ∈ v'.toValuationSubring := by
      have := add_mem (v'.mem_of_ord_nonneg hv'.le) (v'.algebraMap_mem' c)
      simpa using this

    obtain ⟨q₂, hq₂⟩ := dvd_iff_isRoot.2 hqc
    have haq2_ne : aeval x' q₂ ≠ 0 := by
      intro h
      apply haq
      rw [hq₂, map_mul, h, mul_zero]
    have hordq : 1 ≤ v'.ord (aeval x' q) := by
      rw [hq₂, map_mul, map_sub, aeval_X, aeval_C, v'.ord_mul hsub_ne haq2_ne]
      have := v'.ord_nonneg_of_mem (aeval_mem v' hx'mem q₂)
      omega

    have hpc : eval c p ≠ 0 := by
      intro h
      exact Polynomial.not_isUnit_X_sub_C c
        (hcop.isUnit_of_dvd' (dvd_iff_isRoot.2 h) (dvd_iff_isRoot.2 hqc))
    have hordp : v'.ord (aeval x' p) = 0 := by
      have hp_eq : p = C (eval c p) + (X - C c) * (p /ₘ (X - C c)) := by
        have := modByMonic_add_div p (X - C c)
        rw [modByMonic_X_sub_C_eq_C_eval] at this
        exact this.symm
      rcases eq_or_ne (aeval x' (p /ₘ (X - C c))) 0 with h2 | h2
      · rw [hp_eq, map_add, map_mul, h2, mul_zero, add_zero, aeval_C, Place.ord_algebraMap]
      · rw [hp_eq, map_add, map_mul, aeval_C, map_sub, aeval_X, aeval_C]
        apply ord_algebraMap_add_eq_zero v' hpc
        rw [v'.ord_mul hsub_ne h2]
        have := v'.ord_nonneg_of_mem (aeval_mem v' hx'mem (p /ₘ (X - C c)))
        omega
    have : v'.ord t = v'.ord (aeval x' p) - v'.ord (aeval x' q) := by
      rw [ht', div_eq_mul_inv, v'.ord_mul hap (inv_ne_zero haq), v'.ord_inv]
      ring
    omega

  set A : Subalgebra K' F' := Algebra.adjoin K' (Set.range (algebraMap F F')) with hA
  suffices hmem : t ∈ A by
    have : t ∈ Subalgebra.toSubmodule A := hmem
    rwa [span_range_eq_adjoin] at this
  have hφA : ∀ f : F, algebraMap F F' f ∈ A := fun f => Algebra.subset_adjoin ⟨f, rfl⟩
  have hx'A : x' ∈ A := hφA x
  have hpA : aeval x' p ∈ A := by
    rw [aeval_eq_sum_range]
    exact Subalgebra.sum_mem _ fun i _ => Subalgebra.smul_mem _ (Subalgebra.pow_mem _ hx'A _) _
  have hsplit : Multiset.card q.roots = q.natDegree :=
    splits_iff_card_roots.1 (IsAlgClosed.splits q)
  have hq_eq := C_leadingCoeff_mul_prod_multiset_X_sub_C hsplit
  have hlc : q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hq0
  have hprod : aeval x' (q.roots.map fun c => X - C c).prod =
      (q.roots.map fun c => x' - algebraMap K' F' c).prod := by
    rw [map_multiset_prod, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro c _
    simp
  have hinvA : (aeval x' q)⁻¹ ∈ A := by
    rw [← hq_eq, map_mul, aeval_C, hprod, mul_inv, ← Multiset.prod_map_inv]
    refine Subalgebra.mul_mem _ ?_ ?_
    · rw [← map_inv₀]
      exact A.algebraMap_mem _
    · refine multiset_prod_mem _ (fun y hy => ?_)
      rw [Multiset.mem_map] at hy
      obtain ⟨c, hc, rfl⟩ := hy
      obtain ⟨a, rfl⟩ := hroots c hc
      have : (x' - algebraMap K' F' (algebraMap K K' a))⁻¹ =
          algebraMap F F' (x - algebraMap K F a)⁻¹ := by
        rw [map_inv₀, map_sub, ← IsScalarTower.algebraMap_apply,
          ← IsScalarTower.algebraMap_apply]
      rw [this]
      exact hφA _
  rw [ht', div_eq_mul_inv]
  exact A.mul_mem hpA hinvA

end
end Dubon2026.SourceCurve.ConstantField

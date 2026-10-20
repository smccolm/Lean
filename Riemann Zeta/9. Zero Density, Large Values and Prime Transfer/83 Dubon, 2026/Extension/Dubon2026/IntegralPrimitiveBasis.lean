/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Int.Basic

/-! # Integral reduction input for original unitary arithmetic quotient finiteness

Adapted from TauCetiProject/TauCeti, commit
9fc5d5a87d00cb696e606ccdae66420cc837c05e, under Apache-2.0.
Only the dependency needed for positive definite integral form classes is
ported. The exact open chain is DUB-17 -> integral unitary auxiliary
automorphic modules -> finite original arithmetic double cosets ->
bounded classes of the actual integral trace lattices. The construction,
local comparison and determinant bound for those original lattices remain
separate obligations; this result alone does not close that chain.
-/

namespace Dubon2026

noncomputable section

variable {M : Type*} [AddCommGroup M] [Module ℤ M]

/-- An integral vector is primitive when an integral functional takes value one on it. -/
def IntegralPrimitive (v : M) : Prop := ∃ f : M →ₗ[ℤ] ℤ, f v = 1

/-- A vector is primitive exactly when an integer-valued linear functional takes the value one
on it. This is the introduction and elimination interface for `IntegralPrimitive`. -/
theorem integralPrimitive_def {v : M} : IntegralPrimitive v ↔ ∃ f : M →ₗ[ℤ] ℤ, f v = 1 := Iff.rfl

/-- A primitive integral vector is nonzero. -/
theorem IntegralPrimitive.ne_zero {v : M} (h : IntegralPrimitive v) : v ≠ 0 := by
  rintro rfl
  obtain ⟨f, hf⟩ := h
  simp at hf

/-- Every nonzero vector in a free integer module is a positive integer multiple of a
primitive vector. The multiplier is the greatest common divisor of the coordinates in any
integral basis. -/
theorem exists_eq_zsmul_integralPrimitive [Module.Free ℤ M] {v : M}
    (hv : v ≠ 0) : ∃ (d : ℤ) (w : M), 0 < d ∧ IntegralPrimitive w ∧ v = d • w := by
  classical
  let ι := Module.Free.ChooseBasisIndex ℤ M
  let b : Module.Basis ι ℤ M := Module.Free.chooseBasis ℤ M
  let c : ι →₀ ℤ := b.repr v
  let s : Finset ι := c.support
  let d : ℤ := s.gcd c
  have hc0 : c ≠ 0 := fun h ↦ hv (b.repr.injective (h.trans (map_zero b.repr).symm))
  have hs : s.Nonempty := by
    simpa only [s] using Finsupp.support_nonempty_iff.mpr hc0
  obtain ⟨j, hj⟩ := hs
  have hcj : c j ≠ 0 := Finsupp.mem_support_iff.mp hj
  have hd0 : d ≠ 0 := by
    simpa only [d, Finset.gcd_ne_zero_iff] using ⟨j, hj, hcj⟩
  have hd_nonneg : 0 ≤ d := by
    simpa only [d] using (Finset.Int.finsetGcd_nonneg : 0 ≤ s.gcd c)
  have hd : 0 < d := lt_of_le_of_ne hd_nonneg (Ne.symm hd0)
  let q : ι → ℤ := fun k ↦ c k / d
  have hq : (Function.support q).Finite := by
    refine s.finite_toSet.subset fun k hk ↦ ?_
    by_contra hks
    have hck : c k = 0 := Finsupp.notMem_support_iff.mp hks
    exact hk (by simp [q, hck])
  let qf : ι →₀ ℤ := Finsupp.ofSupportFinite q hq
  let w : M := b.repr.symm qf
  have hcd (j : ι) : c j = d * q j := by
    by_cases hj : j ∈ s
    · exact (Int.ediv_mul_cancel (Finset.gcd_dvd hj)).symm.trans (mul_comm _ _)
    · have hcj : c j = 0 := Finsupp.notMem_support_iff.mp hj
      simp [q, hcj]
  have hvw : v = d • w := by
    have hrepr : b.repr v = d • qf := by
      ext j
      simp only [Finsupp.smul_apply, qf, Finsupp.ofSupportFinite_coe, smul_eq_mul]
      simpa only [c, d, q] using hcd j
    calc
      v = b.repr.symm (b.repr v) := (b.repr.symm_apply_apply v).symm
      _ = b.repr.symm (d • qf) := congrArg b.repr.symm hrepr
      _ = d • w := by
        simp only [w, LinearEquiv.map_smul]
        exact Int.cast_smul_eq_zsmul ℤ d _
  have hqgcd : s.gcd q = 1 := by
    simpa only [q, d] using Finset.gcd_div_eq_one (s := s) (f := c) hj hcj
  obtain ⟨a, ha⟩ := Finset.gcd_eq_sum_mul (R := ℤ) s q
  refine ⟨d, w, hd, ?_, hvw⟩
  let f : M →ₗ[ℤ] ℤ := ∑ k ∈ s, a k • b.coord k
  refine integralPrimitive_def.2 ⟨f, ?_⟩
  simp only [f, LinearMap.sum_apply, LinearMap.smul_apply, w, b.coord_repr_symm, qf,
    Finsupp.ofSupportFinite_coe, smul_eq_mul]
  simpa only [mul_comm] using (hqgcd.symm.trans ha).symm

/-- A primitive vector of a finite free integer module belongs to an integral basis of it. -/
theorem IntegralPrimitive.exists_basis [Module.Free ℤ M] [Module.Finite ℤ M] {v : M}
    (hv : IntegralPrimitive v) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℤ M) (j : Fin n), b j = v := by
  obtain ⟨f, hf⟩ := integralPrimitive_def.1 hv
  obtain ⟨m, ⟨c⟩⟩ := Submodule.nonempty_basis_of_pid (Module.finBasis ℤ M) (LinearMap.ker f)
  refine ⟨m + 1, Module.Basis.mkFinCons v c ?_ ?_, 0, ?_⟩
  · intro a x hx hax
    have h := congrArg f hax
    simp only [map_add, map_smul, hf, LinearMap.mem_ker.1 hx, map_zero, add_zero, smul_eq_mul,
      mul_one] at h
    exact h
  · exact fun z ↦ ⟨-f z, by simp [LinearMap.mem_ker, hf]⟩
  · simp


end
end Dubon2026

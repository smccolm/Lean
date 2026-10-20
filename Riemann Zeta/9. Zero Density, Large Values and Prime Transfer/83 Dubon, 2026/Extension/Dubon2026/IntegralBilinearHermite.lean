/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

import Dubon2026.IntegralPrimitiveBasis
import Dubon2026.IntegralNearestMultiple
import Dubon2026.IntegralMatrixCondensation
import Dubon2026.IntegralBilinearGramDet
import Mathlib.LinearAlgebra.QuadraticForm.Basic

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

open Module LinearMap.BilinForm

universe u

/-- **A positive definite integral form attains its minimum at a primitive vector.** On a
nontrivial free `ℤ`-module, a bilinear form whose values `B(x, x)` on nonzero vectors are positive
integers has a nonzero vector of least norm, and every such vector is primitive: a proper multiple
`d • w`, `d ≥ 2`, has norm `d² B(w, w) > B(w, w)`. -/
theorem integralBilinForm_exists_primitive_minimum {M : Type*} [AddCommGroup M] [Module.Free ℤ M]
    [Nontrivial M] (B : LinearMap.BilinForm ℤ M) (hpos : B.toQuadraticMap.PosDef) :
    ∃ v, IntegralPrimitive v ∧ ∀ x, x ≠ 0 → B v v ≤ B x x := by
  classical
  have hpos' : ∀ x, x ≠ 0 → 0 < B x x := fun x hx ↦ by simpa using hpos x hx
  have hex : ∃ k : ℕ, ∃ x : M, x ≠ 0 ∧ B x x = k := by
    obtain ⟨x, hx⟩ := exists_ne (0 : M)
    exact ⟨(B x x).toNat, x, hx, (Int.toNat_of_nonneg (hpos' x hx).le).symm⟩
  obtain ⟨v, hv0, hvk⟩ := Nat.find_spec hex
  have hmin : ∀ x, x ≠ 0 → B v v ≤ B x x := fun x hx ↦ by
    rw [hvk, ← Int.toNat_of_nonneg (hpos' x hx).le]
    exact_mod_cast Nat.find_min' hex ⟨x, hx, (Int.toNat_of_nonneg (hpos' x hx).le).symm⟩
  refine ⟨v, ?_, hmin⟩
  obtain ⟨d, w, hd, hw, hvw⟩ := exists_eq_zsmul_integralPrimitive hv0
  have hww := hpos' w hw.ne_zero
  have hle := hmin w hw.ne_zero
  rw [hvw] at hle
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, ← mul_assoc] at hle
  have hdd : d * d ≤ 1 := le_of_mul_le_mul_right (by rwa [one_mul]) hww
  have hd1 : d = 1 := by nlinarith
  rwa [hvw, hd1, one_smul]

/-- The arithmetic closing the inductive step of Hermite's inequality: if `3 μ² ≤ 4 s`, the
bound `3 ^ C · sⁿ ≤ 4 ^ C · D'` holds in rank `n`, and `μ · D' = μⁿ · D`, then
`3 ^ (C + n) · μ ^ (n + 1) ≤ 4 ^ (C + n) · D`. -/
private theorem three_pow_mul_pow_succ_le {μ s D D' : ℤ} {n C : ℕ} (hμ : 0 < μ)
    (hs : 3 * μ ^ 2 ≤ 4 * s) (hD' : 3 ^ C * s ^ n ≤ 4 ^ C * D') (hD : μ * D' = μ ^ n * D) :
    3 ^ (C + n) * μ ^ (n + 1) ≤ 4 ^ (C + n) * D := by
  have h₁ : 3 ^ C * (3 * μ ^ 2) ^ n ≤ 4 ^ n * (4 ^ C * D') :=
    calc 3 ^ C * (3 * μ ^ 2) ^ n ≤ 3 ^ C * (4 * s) ^ n :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hs _) (by positivity)
      _ = 4 ^ n * (3 ^ C * s ^ n) := by ring
      _ ≤ 4 ^ n * (4 ^ C * D') := mul_le_mul_of_nonneg_left hD' (by positivity)
  refine le_of_mul_le_mul_left (a := μ ^ n) ?_ (by positivity)
  calc μ ^ n * (3 ^ (C + n) * μ ^ (n + 1)) = 3 ^ C * (3 * μ ^ 2) ^ n * μ := by ring
    _ ≤ 4 ^ n * (4 ^ C * D') * μ := mul_le_mul_of_nonneg_right h₁ hμ.le
    _ = 4 ^ n * 4 ^ C * (μ * D') := by ring
    _ = μ ^ n * (4 ^ (C + n) * D) := by rw [hD]; ring

/-- The statement of Hermite's inequality for forms on free `ℤ`-modules with a basis indexed by
`Fin n`, with the powers cleared. -/
private def HermiteBound (n : ℕ) : Prop :=
  ∀ {M : Type u} [AddCommGroup M] [Nontrivial M] (B : LinearMap.BilinForm ℤ M),
    B.IsSymm → (∀ x, x ≠ 0 → 0 < B x x) → ∀ b : Basis (Fin n) ℤ M,
      ∃ x, x ≠ 0 ∧ 3 ^ n.choose 2 * B x x ^ n ≤ 4 ^ n.choose 2 * (toMatrix b B).det

/-- The inductive step of Hermite's inequality: the bound in rank `n` implies it in rank `n + 1`.
A vector `v` of least norm `μ` is primitive, so it extends to a basis `v, bK` with `bK` a basis of
the kernel `K` of a functional taking the value `1` on `v`; the bound is applied to the condensed
form `S(y, z) = μ B(y, z) - B(v, y) B(v, z)` on `K`. -/
private theorem hermiteBound_succ (n : ℕ) (ih : HermiteBound.{u} n) :
    HermiteBound.{u} (n + 1) := by
  intro M _ _ B hB hpos b
  classical
  have : Module.Free ℤ M := .of_basis b
  have : Module.Finite ℤ M := .of_basis b
  have hsymm : ∀ x y, B x y = B y x := isSymm_def.mp hB
  -- A primitive vector `v` of least norm `μ`.
  obtain ⟨v, hprim, hmin⟩ := integralBilinForm_exists_primitive_minimum B
    (fun x hx ↦ by simpa using hpos x hx)
  have hv0 := hprim.ne_zero
  set μ := B v v with hμ_def
  have hμ : 0 < μ := hpos v hv0
  obtain ⟨f, hf⟩ := integralPrimitive_def.mp hprim
  -- Split `M = ℤ v ⊕ K` along `f` and extend `v` by a basis of `K`.
  set K := LinearMap.ker f
  obtain ⟨m, ⟨bK⟩⟩ := Submodule.nonempty_basis_of_pid (Module.finBasis ℤ M) K
  have hli : ∀ (a : ℤ), ∀ x ∈ K, a • v + x = 0 → a = 0 := fun a x hx hax ↦ by
    simpa [hf, LinearMap.mem_ker.mp hx] using congrArg f hax
  have hsp : ∀ z : M, ∃ a : ℤ, z + a • v ∈ K := fun z ↦
    ⟨-f z, by simp [K, LinearMap.mem_ker, hf]⟩
  let c := Basis.mkFinCons v bK hli hsp
  have hmn : n = m := by simpa using Fintype.card_congr (b.indexEquiv c)
  subst hmn
  rw [← integralBilinForm_gramDet_eq B b c]
  -- The condensed form `S(y, z) = μ B(y, z) - B(v, y) B(v, z)` on `K`.
  let ℓ : K →ₗ[ℤ] ℤ := (B v).comp K.subtype
  let S : LinearMap.BilinForm ℤ K :=
    μ • B.compl₁₂ K.subtype K.subtype - (LinearMap.mul ℤ ℤ).compl₁₂ ℓ ℓ
  have hS : ∀ y z : K, S y z = μ * B y z - B v y * B v z := fun y z ↦ by simp [S, ℓ]
  have hSsymm : S.IsSymm := isSymm_def.mpr fun y z ↦ by
    rw [hS, hS, hsymm (y : M) z]
    ring
  have hkey : ∀ (t : ℤ) (y : M),
      μ * B (t • v + y) (t • v + y) = (t * μ + B v y) ^ 2 + (μ * B y y - B v y ^ 2) := by
    intro t y
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hsymm y v]
    ring
  -- `S` is positive definite: `B(z, z) = μ S(y, y)` for `z = -B(v, y) v + μ y`.
  have hSpos : ∀ y : K, y ≠ 0 → 0 < S y y := by
    intro y hy
    have hz : (-B v y) • v + μ • (y : M) ≠ 0 := by
      intro h
      have ht := hli _ _ (K.smul_mem μ y.2) h
      rw [ht, zero_smul, zero_add] at h
      exact hy (Subtype.ext ((smul_eq_zero.mp h).resolve_left hμ.ne'))
    have h₁ := hkey (-B v y) (μ • (y : M))
    have h₂ := mul_pos hμ (hpos _ hz)
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h₁
    have h₃ : 0 < μ ^ 2 * S y y := by
      rw [hS]
      nlinarith
    exact pos_of_mul_pos_right h₃ (sq_nonneg μ)
  -- Minimality of `μ` bounds `S` from below on nonzero vectors of `K`.
  have hSlow : ∀ y : K, y ≠ 0 → 3 * μ ^ 2 ≤ 4 * S y y := by
    intro y hy
    obtain ⟨k, hk⟩ := int_exists_nearest_multiple (B v y) hμ
    have hk' : 0 ≤ μ + 2 * |B v y - k * μ| := by positivity
    obtain ⟨t, ht⟩ : ∃ t : ℤ, 4 * (t * μ + B v y) ^ 2 ≤ μ ^ 2 :=
      ⟨-k, by nlinarith [mul_nonneg (sub_nonneg.mpr hk) hk', sq_abs (B v y - k * μ)]⟩
    have hne : t • v + (y : M) ≠ 0 := by
      intro h
      rw [hli t y y.2 h, zero_smul, zero_add] at h
      exact hy (Subtype.ext h)
    have h₁ := hkey t y
    have h₂ := mul_le_mul_of_nonneg_left (hmin _ hne) hμ.le
    rw [hS]
    nlinarith
  -- Chiò's condensation of the Gram matrix of `B` in `c` is the Gram matrix of `S` in `bK`.
  have hdet : μ * (toMatrix bK S).det = μ ^ n * (toMatrix c B).det := by
    have hc0 : toMatrix c B 0 0 = μ := by simp [c, toMatrix_apply, hμ_def]
    rw [← hc0, ← matrix_mul_det_condensation_eq_pow_mul_det]
    congr 2
    ext i j
    simp [c, toMatrix_apply, hS, hsymm (bK i : M) v, hμ_def]
  refine ⟨v, hv0, ?_⟩
  rcases n.eq_zero_or_pos with rfl | hn
  · simp only [pow_zero, Matrix.det_isEmpty, mul_one, one_mul] at hdet
    simpa using hdet.le
  have : Nontrivial K := nontrivial_of_ne _ _ (bK.ne_zero ⟨0, hn⟩)
  obtain ⟨y, hy, hyb⟩ := ih S hSsymm hSpos bK
  have hchoose : (n + 1).choose 2 = n.choose 2 + n := by simp [Nat.choose_succ_succ', add_comm]
  rw [hchoose]
  exact three_pow_mul_pow_succ_le hμ (hSlow y hy) hyb hdet

/-- Hermite's inequality for a basis indexed by `Fin n`, by induction on `n`. -/
private theorem hermiteBound (n : ℕ) : HermiteBound.{u} n := by
  induction n with
  | zero =>
    intro M _ _ B _ _ b
    obtain ⟨x, hx⟩ := exists_ne (0 : M)
    exact absurd (b.repr.injective (Subsingleton.elim _ _)) hx
  | succ n ih => exact hermiteBound_succ n ih

/-- **Hermite's inequality.** A symmetric positive definite integral bilinear form `B` on a free
`ℤ`-module of rank `n ≥ 1` takes on some nonzero vector `x` a value with
`3 ^ (n choose 2) · B(x, x) ^ n ≤ 4 ^ (n choose 2) · det B`, where `det B` is the Gram determinant
of `B` in any basis. Equivalently `B(x, x) ≤ (4 / 3) ^ ((n - 1) / 2) · (det B) ^ (1 / n)`. -/
theorem integralBilinForm_hermite_bound {M : Type*} [AddCommGroup M]
    [Nontrivial M] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : LinearMap.BilinForm ℤ M) (hB : B.IsSymm) (hpos : B.toQuadraticMap.PosDef)
    (b : Basis ι ℤ M) :
    ∃ x, x ≠ 0 ∧ 3 ^ (Fintype.card ι).choose 2 * B x x ^ Fintype.card ι ≤
      4 ^ (Fintype.card ι).choose 2 * (toMatrix b B).det := by
  have h := hermiteBound (Fintype.card ι) B hB (fun x hx ↦ by simpa using hpos x hx)
    (b.reindex (Fintype.equivFin ι))
  rw [integralBilinForm_gramDet_eq B b (b.reindex (Fintype.equivFin ι))] at h
  exact h


end
end Dubon2026

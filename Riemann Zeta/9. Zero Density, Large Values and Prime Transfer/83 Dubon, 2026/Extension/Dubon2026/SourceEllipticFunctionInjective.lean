/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
import Dubon2026.SourceEllipticFunctionEvaluation
import Mathlib.RingTheory.Norm.Basic

/-! Coordinate evaluation for the actual odd quotient pullback. Adapted from TauCeti
bfcff79b60964ba7bdb78b952828313686c327ba, Affine/Eval.lean, Apache-2.0.
DUB-17/18: this supplies the evaluation map and injectivity needed to construct the
actual odd quotient field embedding; it does not assert the quotient equation. -/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate

namespace Dubon2026.SourceEllipticFunctionField

section Field

variable {F : Type*} [Field F] {W : _root_.WeierstrassCurve.Affine F}
  {A : Type*} [Ring A] [Algebra F A]

/-- **An algebra homomorphism out of the coordinate ring under which the coordinate `x` stays
transcendental is injective.** A nonzero element of the kernel has nonzero norm over `F[x]`, and
that norm is a polynomial relation killing the image of `x`.

Over a field the coordinate ring is free of rank two over `F[X]`, which is what makes the norm
available; neither ellipticity nor commutativity of `A` is needed. -/
theorem algHom_injective (f : W.CoordinateRing →ₐ[F] A)
    (hx : Transcendental F (f (CoordinateRing.mk W (C X)))) :
    Function.Injective f := by
  apply (injective_iff_map_eq_zero f).2
  intro z hz
  by_contra hz₀
  obtain ⟨p, q, hpq⟩ := CoordinateRing.exists_smul_basis_eq z
  set N : F[X] := Algebra.norm F[X] z with hN_def
  have hN₀ : N ≠ 0 :=
    (Algebra.norm_ne_zero_iff_of_basis
      (CoordinateRing.basis W)).2 hz₀
  have hnorm : algebraMap F[X] W.CoordinateRing N =
      z * CoordinateRing.mk W
        (C p + C q * (-(Y : F[X][Y]) - C (C W.a₁ * X + C W.a₃))) := by
    rw [hN_def, ← hpq]
    simpa [CoordinateRing.smul] using
      CoordinateRing.coe_norm_smul_basis (W' := W) p q
  refine hx ⟨N, hN₀, ?_⟩
  have hhom : Polynomial.aeval
      (f (CoordinateRing.mk W (C X))) =
      f.comp (IsScalarTower.toAlgHom F F[X] W.CoordinateRing) := by
    apply Polynomial.algHom_ext
    simp
  rw [AlgHom.congr_fun hhom N, AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, hnorm, map_mul,
    hz, zero_mul]

end Field

end Dubon2026.SourceEllipticFunctionField

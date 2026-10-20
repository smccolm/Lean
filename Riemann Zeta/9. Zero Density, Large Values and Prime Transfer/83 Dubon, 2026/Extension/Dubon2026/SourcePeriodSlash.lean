/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
import Mathlib.NumberTheory.ModularForms.SlashActions
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold

/-! Analytic input to the actual original Hecke period pairing.
Selected from TauCetiProject/TauCeti 199786c594817a82fdd2fab04d3ae4cc5eb837d5,
with Chris Birkbeck's Apache-2.0 source contributions retained.
DUB-17/18 -> modular Galois association -> integral Hecke finiteness ->
period injectivity and adjointness -> convergent, additive cusp integrals.
Only declarations needed by that dependency chain are selected.
-/

namespace Dubon2026
open Complex Matrix Matrix.SpecialLinearGroup UpperHalfPlane
open scoped MatrixGroups ModularForm

/-- **The weight-`k` slash formula at a positive-determinant matrix**, free of the `σ` twist:

`f ∣[k] g = fun τ ↦ f (g • τ) * |det g| ^ (k - 1) * denom g τ ^ (-k)`.

Mathlib's `ModularForm.slash_def` carries `σ g` around the value of `f`, which is complex
conjugation on the negative-determinant branch. `ModularForm.SL_slash_def` drops it because
`det = 1`; here positivity alone is what does it. -/
theorem sourceSlash_def_of_det_pos (k : ℤ) {g : GL (Fin 2) ℝ}
    (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det) (f : ℍ → ℂ) :
    f ∣[k] g = fun τ ↦ f (g • τ) * |(g.det : ℝ)| ^ (k - 1) * denom g τ ^ (-k) := by
  rw [ModularForm.slash_def, UpperHalfPlane.σ,
    if_pos (by rwa [Matrix.GeneralLinearGroup.val_det_apply])]
  rfl

/-- The pointwise form of `sourceSlash_def_of_det_pos`, matching
`ModularForm.SL_slash_apply`. -/
theorem sourceSlash_apply_of_det_pos (k : ℤ) {g : GL (Fin 2) ℝ}
    (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det) (f : ℍ → ℂ) (τ : ℍ) :
    (f ∣[k] g) τ = f (g • τ) * |(g.det : ℝ)| ^ (k - 1) * denom g τ ^ (-k) :=
  congrFun (sourceSlash_def_of_det_pos k hg f) τ

/-- **Scalars pass through the slash of a positive-determinant matrix.** Mathlib's
`ModularForm.smul_slash` carries the twist `σ A c`, which is complex conjugation when the
determinant is negative, so scalars do not commute past a general slash. On the positive branch
they do.

This is what makes a Hecke operator `ℂ`-linear: it is a sum of slashes by representatives of
positive determinant. The scalar generality matches `ModularForm.SL_smul_slash`. -/
@[simp]
theorem sourceSmul_slash_of_det_pos {α : Type*} [SMul α ℂ] [IsScalarTower α ℂ ℂ]
    (k : ℤ) {g : GL (Fin 2) ℝ} (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det) (f : ℍ → ℂ)
    (c : α) : (c • f) ∣[k] g = c • f ∣[k] g := by
  ext τ : 1
  simp [sourceSlash_apply_of_det_pos k hg, smul_mul_assoc]

/-- The weight-`k` slash action of `GL(2, ℚ)`, induced from `GL(2, ℝ)` along `ℚ ↪ ℝ`. Scoped,
so it is opted into rather than imposed. -/
noncomputable instance sourceRatSlashAction : SlashAction ℤ (GL (Fin 2) ℚ) (ℍ → ℂ) :=
  monoidHomSlashAction (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ))

/-- The rational slash action is the real one at the mapped matrix. Definitional, but named:
it is how every `GL(2, ℝ)` lemma is brought to bear on a rational slash.

The three lemmas here mirror Mathlib's integral trio exactly, including the absence of a `_def`
suffix on this one: `ModularForm.SL_slash` is the transport
(`Mathlib/NumberTheory/ModularForms/SlashActions.lean:155`), `ModularForm.SL_slash_def` the
expanded formula (:158) and `ModularForm.SL_slash_apply` the pointwise one (:162). `_def` marks
the *expanded* statement in this family, not the transport, so it belongs to
`sourceRat_slash_def_of_det_pos` below. -/
lemma sourceRat_slash (k : ℤ) (g : GL (Fin 2) ℚ) (f : ℍ → ℂ) :
    f ∣[k] g = f ∣[k] (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) g) := (rfl)

/-- A rational matrix of positive determinant maps to a real one of positive determinant.
Stated with `Matrix.det`, the form `UpperHalfPlane.σ_eq_refl_of_det_pos` consumes. -/
lemma sourceDet_map_ratCast_pos {g : GL (Fin 2) ℚ} (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℚ).det) :
    0 < ((Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) g : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ).det := by
  rw [Matrix.GeneralLinearGroup.val_map_apply, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  simpa using hg

/-- **The expanded formula for a positive-determinant rational slash**, with no `σ` twist:

`f ∣[k] g = fun τ ↦ f (ĝ • τ) * |det ĝ| ^ (k - 1) * denom ĝ τ ^ (-k)`,

where `ĝ` abbreviates `Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) g`, the real image of `g`.
The distinction is not cosmetic: `g : GL (Fin 2) ℚ` does not act on `ℍ` at all, and `denom` is
likewise only defined at the real matrix, so every occurrence in the statement below is at `ĝ`.

Mathlib's `ModularForm.slash_def` carries `σ g` around the value of `f`, which is complex
conjugation on the negative-determinant branch. This is the analogue of
`ModularForm.SL_slash_def`, which drops the twist because `det = 1`; here positivity is the
hypothesis that does it. -/
lemma sourceRat_slash_def_of_det_pos (k : ℤ) {g : GL (Fin 2) ℚ}
    (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℚ).det) (f : ℍ → ℂ) :
    f ∣[k] g = fun τ ↦
      f ((Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) g) • τ) *
        |((Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) g).det : ℝ)| ^ (k - 1) *
          denom (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) g) τ ^ (-k) := by
  rw [sourceRat_slash, sourceSlash_def_of_det_pos k (sourceDet_map_ratCast_pos hg)]

/-- The pointwise form of `sourceRat_slash_def_of_det_pos`, matching
`ModularForm.SL_slash_apply`. -/
lemma sourceRat_slash_apply_of_det_pos (k : ℤ) {g : GL (Fin 2) ℚ}
    (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℚ).det) (f : ℍ → ℂ) (τ : ℍ) :
    (f ∣[k] g) τ =
      f ((Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) g) • τ) *
        |((Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) g).det : ℝ)| ^ (k - 1) *
          denom (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) g) τ ^ (-k) :=
  congrFun (sourceRat_slash_def_of_det_pos k hg f) τ

/-- **Scalars pass through the slash of a positive-determinant rational matrix.** Mathlib's
`ModularForm.smul_slash` carries the twist `σ A c`, which is complex conjugation when the
determinant is negative; on the positive branch `σ` is the identity
(`UpperHalfPlane.σ_eq_refl_of_det_pos`) and the scalar simply commutes.

This is what makes a Hecke operator `ℂ`-linear: it is a sum of slashes by representatives of
positive determinant. The scalar generality matches `ModularForm.SL_smul_slash`, the same
statement for the integral action. -/
@[simp]
lemma sourceRat_smul_slash_of_det_pos {α : Type*} [SMul α ℂ] [IsScalarTower α ℂ ℂ] (k : ℤ)
    {g : GL (Fin 2) ℚ} (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℚ).det) (f : ℍ → ℂ) (c : α) :
    (c • f) ∣[k] g = c • f ∣[k] g := by
  rw [sourceRat_slash, sourceRat_slash]
  exact sourceSmul_slash_of_det_pos k (sourceDet_map_ratCast_pos hg) f c

/-- **The `ℚ`/`ℝ` bridge for the slash by an integral matrix**: the rational action at
`mapGL ℚ σ` is the real action at `mapGL ℝ σ`. Both are ranges of `mapGL` out of the same
`SL(2, ℤ)`, and mathlib's `Matrix.SpecialLinearGroup.map_mapGL` relates them along `ℤ → ℚ → ℝ`.

This is the one lemma needed to state a hypothesis rationally and consume it at a level
`G.map (mapGL ℝ)`, or the other way about. -/
lemma sourceRat_slash_mapGL (k : ℤ) (f : ℍ → ℂ) (σ : SL(2, ℤ)) :
    f ∣[k] (mapGL ℚ σ : GL (Fin 2) ℚ) = f ∣[k] (mapGL ℝ σ : GL (Fin 2) ℝ) := by
  rw [sourceRat_slash, map_mapGL]

/-- **Primitives pull back along Möbius transformations.** If `Φ` is a primitive of `F` on `ℍ`,
then `z ↦ Φ (g • z)` is a primitive of the weight-`2` slash `F ∣[2] g`, for `g` of positive
determinant: the weight-`2` automorphy factor `det g · (cz + d)⁻²` is the derivative of
`z ↦ g • z`. -/
theorem sourceHasDerivAt_comp_smul {F : ℍ → ℂ} {Φ : ℂ → ℂ}
    (hΦ : ∀ z : ℍ, HasDerivAt Φ (F z) z) {g : GL (Fin 2) ℝ}
    (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det) (τ : ℍ) :
    HasDerivAt (fun z ↦ Φ (g • ofComplex z : ℍ)) ((F ∣[(2 : ℤ)] g) τ) τ := by
  have h := (hΦ (g • τ)).comp_of_eq (τ : ℂ) (hasStrictDerivAt_smul hg τ).hasDerivAt
    (by rw [ofComplex_apply])
  refine h.congr_deriv ?_
  have hden : denom g τ ≠ 0 := denom_ne_zero g τ
  rw [sourceSlash_apply_of_det_pos 2 hg, Matrix.GeneralLinearGroup.val_det_apply,
    abs_of_pos hg]
  push_cast
  field_simp

end Dubon2026

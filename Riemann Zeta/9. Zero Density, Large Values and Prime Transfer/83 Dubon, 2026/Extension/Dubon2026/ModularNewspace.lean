/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors

Orthogonality proofs adapt Newforms/Basic.lean at
7c41b9b1747d47298f76bdb51f07031087702198. The oldspace generators here are
independently defined with all d*M | N, including ordinary inclusion d=1.
-/
import Dubon2026.ModularDegeneracyCoefficients
import Dubon2026.ModularPeterssonLevel

/-! # The full classical oldspace and its Petersson orthogonal complement

The oldspace includes all g(dz) from every proper lower level M, with d*M | N.
In particular d=1 is included. These are actual cusp forms and actual Petersson
integrals, with no spectral or analytic conclusion encoded as a structure field.
-/

namespace Dubon2026

open Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups ModularForm

noncomputable section

/-- A classical oldform generator, including ordinary lower-level inclusion. -/
def IsCuspOldGenerator {N : ℕ} {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) : Prop :=
  ∃ (M : ℕ+) (_ : (M : ℕ) < N) (d : ℕ+) (h : (d : ℕ) * M ∣ N)
    (g : CuspForm ((Gamma0 M).map (mapGL ℝ)) k), cuspDegeneracyMap d h k g = f

/-- The full classical oldspace at level Gamma0(N). -/
def cuspOldspace (N : ℕ) (k : ℤ) :
    Submodule ℂ (CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :=
  Submodule.span ℂ {f | IsCuspOldGenerator f}

/-- Every degeneracy map from a proper lower level lands in the oldspace. -/
theorem cuspDegeneracyMap_mem_oldspace {M N : ℕ} (hM : 0 < M) (hMN : M < N)
    (d : ℕ) [NeZero d] (h : d * M ∣ N) {k : ℤ}
    (f : CuspForm ((Gamma0 M).map (mapGL ℝ)) k) :
    cuspDegeneracyMap d h k f ∈ cuspOldspace N k :=
  Submodule.subset_span ⟨⟨M, hM⟩, hMN, ⟨d, Nat.pos_of_neZero d⟩, h, f, rfl⟩

/-- Ordinary inclusion from a proper lower level is part of the oldspace. -/
theorem cuspLevelInclusion_mem_oldspace {M N : ℕ} (hM : 0 < M) (hMN : M < N)
    (h : M ∣ N) {k : ℤ} (f : CuspForm ((Gamma0 M).map (mapGL ℝ)) k) :
    cuspLevelInclusion h k f ∈ cuspOldspace N k := by
  have hh : 1 * M ∣ N := by simpa using h
  have he : cuspDegeneracyMap 1 hh k f = cuspLevelInclusion h k f := by
    ext τ
    rw [cuspDegeneracyMap_apply]
    change f (levelRaiseMatrix 1 • τ) = f τ
    congr 1
    apply UpperHalfPlane.ext
    simp [coe_levelRaiseMatrix_smul]
  rw [← he]
  exact cuspDegeneracyMap_mem_oldspace hM hMN 1 hh f

/-- Level one has no positive proper lower level, hence has zero oldspace. -/
theorem cuspOldspace_one (k : ℤ) : cuspOldspace 1 k = ⊥ := by
  apply le_antisymm ?_ bot_le
  apply Submodule.span_le.mpr
  rintro f ⟨M, hM, d, h, g, rfl⟩
  exact (Nat.not_lt_of_ge M.pos hM).elim

/-- The classical newspace is the Petersson orthogonal complement of the full oldspace. -/
def cuspNewspace (N : ℕ) [NeZero N] (k : ℤ) :
    Submodule ℂ (CuspForm ((Gamma0 N).map (mapGL ℝ)) k) where
  carrier := {f | ∀ g ∈ cuspOldspace N k, cuspPetersson f g = 0}
  zero_mem' g _ := cuspPetersson_zero_left g
  add_mem' hf hg u hu := by rw [cuspPetersson_add_left, hf u hu, hg u hu, add_zero]
  smul_mem' c f hf u hu := by rw [cuspPetersson_conj_smul_left, hf u hu, mul_zero]

/-- Positive definiteness gives a trivial intersection of the full old and new spaces. -/
theorem cuspOldspace_disjoint_newspace (N : ℕ) [NeZero N] (k : ℤ) :
    Disjoint (cuspOldspace N k) (cuspNewspace N k) := by
  rw [Submodule.disjoint_def]
  exact fun f hf hn => cuspPetersson_definite f (hn f hf)

/-- At level one the newspace is all cusp forms. This proves the level condition,
without claiming an eigenform condition or the absence of complex multiplication. -/
theorem cuspNewspace_one (k : ℤ) : cuspNewspace 1 k = ⊤ := by
  apply top_unique
  intro f _ g hg
  rw [cuspOldspace_one, Submodule.mem_bot] at hg
  rw [hg, cuspPetersson_zero_right]

/-- It suffices to check orthogonality on the full set of degeneracy generators. -/
theorem mem_cuspNewspace_iff_generators {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    f ∈ cuspNewspace N k ↔ ∀ g, IsCuspOldGenerator g → cuspPetersson f g = 0 := by
  constructor
  · intro hf g hg
    exact hf g (Submodule.subset_span hg)
  · intro hf g hg
    refine Submodule.span_induction hf ?_ ?_ ?_ hg
    · exact cuspPetersson_zero_right f
    · intro g h _ _ hg hh
      rw [cuspPetersson_add_right, hg, hh, add_zero]
    · intro c g _ hg
      rw [cuspPetersson_smul_right, hg, mul_zero]

/-- A diagnostic space retaining only d>1 dilations. It is deliberately not called
oldspace: ordinary lower-level inclusions are missing. -/
def strictCuspDilationSpan (N : ℕ) (k : ℤ) :
    Submodule ℂ (CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :=
  Submodule.span ℂ {f | ∃ (M d : ℕ+) (_ : 1 < (d : ℕ)) (h : (d : ℕ) * M ∣ N)
    (g : CuspForm ((Gamma0 M).map (mapGL ℝ)) k), cuspDegeneracyMap d h k g = f}

/-- Every vector in the span of strict dilations has first Fourier coefficient zero. -/
theorem strictCuspDilationSpan_coeff_one {N : ℕ} {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (hf : f ∈ strictCuspDilationSpan N k) :
    cuspCoefficients f 1 = 0 := by
  have hle : strictCuspDilationSpan N k ≤ LinearMap.ker (cuspCoefficientLinear N k 1) := by
    apply Submodule.span_le.mpr
    rintro g ⟨M, d, hd, h, g, rfl⟩
    exact cuspDegeneracyMap_coeff_one d h hd g
  exact hle hf

/-- A normalized lower-level inclusion is absent from the strict-dilation span. -/
theorem normalized_inclusion_not_strictDilationSpan {M N : ℕ} (h : M ∣ N) {k : ℤ}
    (f : CuspForm ((Gamma0 M).map (mapGL ℝ)) k) (hf : cuspCoefficients f 1 = 1) :
    cuspLevelInclusion h k f ∉ strictCuspDilationSpan N k := by
  intro hin
  have hz := strictCuspDilationSpan_coeff_one _ hin
  rw [cuspLevelInclusion_coeff, hf] at hz
  exact one_ne_zero hz

/-- The full oldspace differs from the strict-dilation span whenever a normalized
form is included from a positive proper lower level. -/
theorem cuspOldspace_ne_strictDilationSpan {M N : ℕ} (hM : 0 < M) (hMN : M < N)
    (h : M ∣ N) {k : ℤ} (f : CuspForm ((Gamma0 M).map (mapGL ℝ)) k)
    (hf : cuspCoefficients f 1 = 1) : cuspOldspace N k ≠ strictCuspDilationSpan N k := by
  intro he
  exact normalized_inclusion_not_strictDilationSpan h f hf
    (he ▸ cuspLevelInclusion_mem_oldspace hM hMN h f)

end
end Dubon2026

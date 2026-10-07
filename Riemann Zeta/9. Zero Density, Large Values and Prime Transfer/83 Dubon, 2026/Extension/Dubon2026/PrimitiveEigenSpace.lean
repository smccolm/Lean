import Dubon2026.PrimitiveMultiplicityOne
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-! # The actual good Hecke eigenspace of a primitive form is one dimensional -/

namespace Dubon2026

open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

noncomputable section

/-- The actual simultaneous good Hecke eigenspace inside the genuine newspace. -/
def primitiveGoodEigenSpace {N : ℕ} [NeZero N] {k : ℤ} (f : PrimitiveCuspForm N k) :
    Submodule ℂ (CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :=
  cuspNewspace N k ⊓ ⨅ (n : ℕ) (_ : 0 < n) (_ : n.Coprime N),
    Module.End.eigenspace (cuspHeckeLinear N k n) (cuspCoefficients f.toCuspForm n)

/-- Membership is exactly actual newness and the genuine simultaneous good Hecke equations. -/
theorem mem_primitiveGoodEigenSpace {N : ℕ} [NeZero N] {k : ℤ}
    (f : PrimitiveCuspForm N k) (g : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    g ∈ primitiveGoodEigenSpace f ↔ g ∈ cuspNewspace N k ∧
      ∀ n, 0 < n → n.Coprime N → cuspHeckeLinear N k n g = cuspCoefficients f.toCuspForm n • g := by
  simp only [primitiveGoodEigenSpace, Submodule.mem_inf, Submodule.mem_iInf,
    Module.End.mem_eigenspace_iff]

/-- The primitive form belongs to the genuine simultaneous eigenspace defined by its coefficients. -/
theorem primitiveCuspForm_mem_goodEigenSpace {N : ℕ} [NeZero N] {k : ℤ}
    (f : PrimitiveCuspForm N k) : f.toCuspForm ∈ primitiveGoodEigenSpace f :=
  (mem_primitiveGoodEigenSpace f _).mpr ⟨f.isNew, fun _ hn hnN => primitiveCuspForm_eigenvector f hn hnN⟩

/-- Actual newform multiplicity one identifies the complete good eigenspace with the line through f. -/
theorem primitiveGoodEigenSpace_eq_span {N : ℕ} [NeZero N] {k : ℤ}
    (f : PrimitiveCuspForm N k) : primitiveGoodEigenSpace f = Submodule.span ℂ {f.toCuspForm} := by
  apply le_antisymm
  · intro g hg
    obtain ⟨hgnew, hge⟩ := (mem_primitiveGoodEigenSpace f g).mp hg
    rw [primitiveCuspForm_same_eigensystem_scalar f g hgnew hge]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton f.toCuspForm))
  · apply Submodule.span_le.mpr
    rintro g (rfl : g = f.toCuspForm)
    exact primitiveCuspForm_mem_goodEigenSpace f

/-- The genuine simultaneous good Hecke eigenspace has complex dimension exactly one. -/
theorem primitiveGoodEigenSpace_finrank {N : ℕ} [NeZero N] {k : ℤ}
    (f : PrimitiveCuspForm N k) : Module.finrank ℂ (primitiveGoodEigenSpace f) = 1 := by
  rw [primitiveGoodEigenSpace_eq_span]
  exact finrank_span_singleton (primitiveCuspForm_ne_zero f)

/-- The actual first Fourier coefficient is injective on the genuine primitive eigenspace. -/
theorem primitiveGoodEigenSpace_firstCoefficient_injective {N : ℕ} [NeZero N] {k : ℤ}
    (f : PrimitiveCuspForm N k) :
    Function.Injective (fun g : primitiveGoodEigenSpace f => cuspCoefficients g.val 1) := by
  intro g h hgh
  dsimp only at hgh
  apply Subtype.ext
  obtain ⟨hgn, hge⟩ := (mem_primitiveGoodEigenSpace f g.val).mp g.property
  obtain ⟨hhn, hhe⟩ := (mem_primitiveGoodEigenSpace f h.val).mp h.property
  rw [primitiveCuspForm_same_eigensystem_scalar f g.val hgn hge,
    primitiveCuspForm_same_eigensystem_scalar f h.val hhn hhe, hgh]

end
end Dubon2026

import Dubon2026.AdelicAlgebraicFiniteSpan
import Dubon2026.FiniteAdelicClassicalTranslate

/-! # Actual classical restrictions of every original finite-adelic combination -/

namespace Dubon2026

noncomputable section
open Matrix Matrix.SpecialLinearGroup IsDedekindDomain UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- Literal restriction of each original algebraic adelic function to the real special-linear group. -/
def adelicCyclicRealRestriction :
    (adelicLiftCyclicRepresentation N k f).toSubmodule →ₗ[ℂ] (SL(2, ℝ) → ℂ) where
  toFun v g := v.val (adelicRealSL2Embedding g)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Each actual finite-place orbit vector restricts to the genuine corrected rational slash translate. -/
theorem adelicCyclicRealRestriction_finiteOrbit
    (a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    adelicCyclicRealRestriction f
      ((adelicLiftCyclicRepresentation N k f).toRepresentation
        (rationalAdelicFiniteGL2Embedding a) (adelicCyclicGenerator N f)) =
      realWeightLiftLinear k (finiteAdelicClassicalTranslate N k f a) := by
  funext g
  exact finiteAdelicClassicalTranslate_real_lift N k f a g

/-- Every original finite-adelic combination has an actual classical rational-slash function, with equality on the entire real group. -/
theorem adelicAlgebraicFiniteSpan_classical_restriction
    (v : (adelicLiftCyclicRepresentation N k f).toSubmodule)
    (hv : v ∈ adelicAlgebraicFiniteSpan f) :
    ∃ F ∈ rationalCuspSlashSpan f, realWeightLiftLinear k F = adelicCyclicRealRestriction f v := by
  have hs : adelicAlgebraicFiniteSpan f ≤
      ((rationalCuspSlashSpan f).map (realWeightLiftLinear k)).comap (adelicCyclicRealRestriction f) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    exact ⟨finiteAdelicClassicalTranslate N k f a,
      finiteAdelicClassicalTranslate_mem_span f a, (adelicCyclicRealRestriction_finiteOrbit f a).symm⟩
  exact hs hv

/-- Faithfulness of the genuine real lift gives uniqueness of the reconstructed classical function. -/
theorem adelicAlgebraicFiniteSpan_classical_unique
    (v : (adelicLiftCyclicRepresentation N k f).toSubmodule) (F G : ℍ → ℂ)
    (hF : realWeightLiftLinear k F = adelicCyclicRealRestriction f v)
    (hG : realWeightLiftLinear k G = adelicCyclicRealRestriction f v) : F = G :=
  realWeightLiftLinear_injective k (hF.trans hG.symm)

end
end Dubon2026

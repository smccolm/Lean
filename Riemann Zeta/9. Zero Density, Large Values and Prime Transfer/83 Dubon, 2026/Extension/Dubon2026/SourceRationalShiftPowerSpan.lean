import Dubon2026.SourceRationalPartialFractions
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! DUB-17/18 -> global residue identity -> rational-function spanning.
Over the actual algebraically closed constants, irreducible denominators
are linear and their remainders are constant. Thus shifted integer powers
span the rational function field. Their pullbacks can consume the already
proved original power-differential residue identities.
-/
namespace Dubon2026.SourceCurve
noncomputable section
open Polynomial
variable (K : Type*) [Field K]

/-- Shifted integer powers of the actual rational-function coordinate. -/
def rationalShiftPowerGenerators : Set (RatFunc K) :=
  {f | ∃ (c : K) (n : ℤ), f = (RatFunc.X - RatFunc.C c) ^ n}

theorem rationalShiftPowerSpan_eq_top [IsAlgClosed K] :
    Submodule.span K (rationalShiftPowerGenerators K) = ⊤ := by
  apply top_unique
  rw [← p1PartialFractionSpan_eq_top (K := K)]
  apply Submodule.span_le.mpr
  intro f hf
  rcases hf with hpoly | hatom
  · obtain ⟨n, rfl⟩ := hpoly
    exact Submodule.subset_span ⟨0, (n : ℤ), by simp⟩
  · obtain ⟨p, c, m, hpmon, hpirr, hdeg, _hm, rfl⟩ := hatom
    have hd : p.degree = 1 := IsAlgClosed.degree_eq_one_of_irreducible K hpirr
    have hc : c = C (c.coeff 0) :=
      eq_C_of_degree_le_zero (Nat.WithBot.lt_one_iff_le_zero.mp (hd ▸ hdeg))
    have hp : p = X - C (-(p.coeff 0)) := by
      rw [eq_X_add_C_of_degree_eq_one hd, hpmon.leadingCoeff, C_1, one_mul,
        C_neg, sub_neg_eq_add]
      simp only [coeff_add, coeff_X_zero, coeff_C, zero_add, ite_true]
    rw [hc, hp, RatFunc.algebraMap_C, map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C,
      div_eq_mul_inv, ← RatFunc.smul_eq_C_mul]
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨-(p.coeff 0), -(m : ℤ), by
      rw [zpow_neg, zpow_natCast]⟩

theorem linearMap_eq_zero_of_shift_powers [IsAlgClosed K]
    {V : Type*} [AddCommGroup V] [Module K V] (φ : RatFunc K →ₗ[K] V)
    (hφ : ∀ (c : K) (n : ℤ), φ ((RatFunc.X - RatFunc.C c) ^ n) = 0) : φ = 0 := by
  have hspan : Submodule.span K (rationalShiftPowerGenerators K) ≤ LinearMap.ker φ := by
    apply Submodule.span_le.mpr
    rintro f ⟨c, n, rfl⟩
    exact hφ c n
  rw [rationalShiftPowerSpan_eq_top K] at hspan
  exact LinearMap.ker_eq_top.mp (top_unique hspan)

variable {F : Type*} [Field F] [Algebra K F]

/-- Evaluation of rational functions in a transcendental field coordinate. -/
def rationalCoordinateEmbedding (x : F) (hx : Transcendental K x) : RatFunc K →ₐ[K] F :=
  (IntermediateField.adjoin K {x}).val.comp
    (RatFunc.algEquivOfTranscendental x hx).toAlgHom

theorem rationalCoordinateEmbedding_X (x : F) (hx : Transcendental K x) :
    rationalCoordinateEmbedding K x hx RatFunc.X = x := by
  change ((RatFunc.algEquivOfTranscendental x hx RatFunc.X :
    IntermediateField.adjoin K {x}) : F) = x
  rw [RatFunc.algEquivOfTranscendental_X]

end
end Dubon2026.SourceCurve

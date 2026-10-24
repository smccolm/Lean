import Dubon2026.SourceReductionChartGluing
import Dubon2026.SourceReductionIndependent

/-! DUB-17/18 -> modular good reduction -> principal-divisor pushforward ->
equality of total chart orders. Each coordinate factor is rescaled by an
actual constant so that it is Gauss integral with nonzero reduction. Factors
at integral constants reduce to the corresponding residue coordinate factor;
the others reduce to one. Existing constant embeddings and native inverse
nonunit membership replace the external constant and inverse-ring helpers.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_RegularProlongation_sum_ord_eq_sum_ord_residue_of_isIntegral_adjoin. -/
namespace Dubon2026.SourceCurve.RegularProlongation
noncomputable section
open IsLocalRing
open scoped Classical
variable {L : Type*} [Field L] {A : ValuationSubring L}
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

/-- A coordinate factor with Gauss-integral coefficients and nonzero reduction. -/
def normalizedChartFactor (R : RegularProlongation A F Fbar) (x : R.integers) (c : L) : R.integers :=
  if hc : c ∈ A then x - constHom R ⟨c, hc⟩
  else 1 - constHom R ⟨c⁻¹, (A.mem_or_inv_mem c).resolve_left hc⟩ * x

/-- The nonzero constant removed from the normalized coordinate factor. -/
def chartFactorScalar (A : ValuationSubring L) (c : L) : L := if c ∈ A then 1 else -c

theorem chartFactorScalar_ne_zero (c : L) : chartFactorScalar A c ≠ 0 := by
  unfold chartFactorScalar
  split_ifs with hc
  · exact one_ne_zero
  · exact neg_ne_zero.mpr (fun h => hc (h ▸ zero_mem A))

theorem coe_normalizedChartFactor_of_mem (R : RegularProlongation A F Fbar) (x : R.integers)
    {c : L} (hc : c ∈ A) : (normalizedChartFactor R x c : F) = (x : F) - algebraMap L F c := by
  rw [normalizedChartFactor, dif_pos hc]
  rfl

theorem coe_normalizedChartFactor_of_not_mem (R : RegularProlongation A F Fbar) (x : R.integers)
    {c : L} (hc : c ∉ A) :
    (normalizedChartFactor R x c : F) = 1 - algebraMap L F c⁻¹ * (x : F) := by
  rw [normalizedChartFactor, dif_neg hc]
  rfl

theorem sub_eq_scalar_mul_normalizedChartFactor (R : RegularProlongation A F Fbar)
    (x : R.integers) (c : L) :
    (x : F) - algebraMap L F c = algebraMap L F (chartFactorScalar A c) *
      (normalizedChartFactor R x c : F) := by
  unfold chartFactorScalar
  split_ifs with hc
  · rw [coe_normalizedChartFactor_of_mem R x hc, map_one, one_mul]
  · have hc0 : c ≠ 0 := fun h => hc (h ▸ zero_mem A)
    have : algebraMap L F c ≠ 0 := (map_ne_zero _).mpr hc0
    rw [coe_normalizedChartFactor_of_not_mem R x hc, map_neg, map_inv₀]
    field_simp
    ring

theorem residue_normalizedChartFactor_of_mem (R : RegularProlongation A F Fbar)
    (x : R.integers) {c : L} (hc : c ∈ A) :
    R.residue (normalizedChartFactor R x c) = R.residue x -
      algebraMap (ResidueField A) Fbar (IsLocalRing.residue A ⟨c, hc⟩) := by
  rw [normalizedChartFactor, dif_pos hc, map_sub, residue_constHom]

theorem residue_normalizedChartFactor_of_not_mem (R : RegularProlongation A F Fbar)
    (x : R.integers) {c : L} (hc : c ∉ A) : R.residue (normalizedChartFactor R x c) = 1 := by
  have hi : c⁻¹ ∈ A := (A.mem_or_inv_mem c).resolve_left hc
  have hz : IsLocalRing.residue A ⟨c⁻¹, hi⟩ = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff]
    exact ValuationSubring.coe_mem_nonunits_iff.mp (A.inv_mem_nonunits_iff.mpr (Or.inr hc))
  rw [normalizedChartFactor, dif_neg hc, map_sub, map_one, map_mul, residue_constHom,
    hz, map_zero, zero_mul, sub_zero]

theorem residue_normalizedChartFactor_ne_zero (R : RegularProlongation A F Fbar)
    (x : R.integers) (hx : Transcendental (ResidueField A) (R.residue x)) (c : L) :
    R.residue (normalizedChartFactor R x c) ≠ 0 := by
  by_cases hc : c ∈ A
  · rw [residue_normalizedChartFactor_of_mem R x hc]
    intro h
    exact hx (sub_eq_zero.mp h ▸ isAlgebraic_algebraMap _)
  · rw [residue_normalizedChartFactor_of_not_mem R x hc]
    exact one_ne_zero

theorem coe_normalizedChartFactor_ne_zero (R : RegularProlongation A F Fbar)
    (x : R.integers) (hx : Transcendental (ResidueField A) (R.residue x)) (c : L) :
    (normalizedChartFactor R x c : F) ≠ 0 := by
  intro h
  apply residue_normalizedChartFactor_ne_zero R x hx c
  rw [show normalizedChartFactor R x c = 0 from Subtype.ext h, map_zero]

theorem isIntegral_normalizedChartFactor (R : RegularProlongation A F Fbar)
    (x : R.integers) (c : L) :
    IsIntegral (Algebra.adjoin L {(x : F)}) (normalizedChartFactor R x c : F) := by
  have hx : IsIntegral (Algebra.adjoin L {(x : F)}) (x : F) :=
    isIntegral_algebraMap (x := (⟨(x : F), Algebra.self_mem_adjoin_singleton L (x : F)⟩ :
      Algebra.adjoin L {(x : F)}))
  by_cases hc : c ∈ A
  · rw [coe_normalizedChartFactor_of_mem R x hc]
    exact hx.sub (isIntegral_algebraMap (R := L) (A := F) (x := c)).tower_top
  · rw [coe_normalizedChartFactor_of_not_mem R x hc]
    exact isIntegral_one.sub ((isIntegral_algebraMap (R := L) (A := F) (x := c⁻¹)).tower_top.mul hx)

end
end Dubon2026.SourceCurve.RegularProlongation

import Dubon2026.SourceOriginalWeilCoverSimplePoleBounds

/-! DUB-17/18 -> auxiliary point division -> cover Abel converse -> integral-period exponential and principality. Adapt the native original-curve deduction to the literal cover, using proved chart, residue and meromorphic comparison inputs. No global regularity or completed Abel converse is assumed. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) (radicand : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C radicand : Polynomial FF)

theorem cover_simple_poles_sub_regular (η ζ : Ω[EE⁄ℂ])
    (hη : ∀ v : Place ℂ EE, -1 ≤ v.ordDifferential η)
    (hζ : ζ ∈ regularDifferentials ℂ EE) :
    ∀ v : Place ℂ EE, -1 ≤ v.ordDifferential (η - ζ) := by
  intro v
  have hz := (mem_cover_regularDifferentials_iff_ord_nonneg N n radicand ζ).mp hζ v
  have hz' : -1 ≤ v.ordDifferential ζ := by omega
  have hn := cover_simple_pole_smul_bound N n radicand v (-1) (ω := ζ) hz'
  rw [neg_one_smul ℂ ζ] at hn
  rw [sub_eq_add_neg η ζ]
  exact cover_simple_pole_add_bound N n radicand v (ω := η) (η := -ζ) (hη v) hn

theorem cover_residues_sub_regular (D : Divisor ℂ EE) (η ζ : Ω[EE⁄ℂ])
    (hη : ∀ v : Place ℂ EE, -1 ≤ v.ordDifferential η)
    (hres : ∀ v, v.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n radicand v) (v.uniformizer * v.differentialCoeff η) = (D v : ℂ))
    (hζ : ζ ∈ regularDifferentials ℂ EE) :
    ∀ v, v.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n radicand v) (v.uniformizer * v.differentialCoeff (η - ζ)) = (D v : ℂ) := by
  intro v
  rw [← coverDifferentialResidue_simplePole N n radicand v (η - ζ)
    (cover_simple_poles_sub_regular N n radicand η ζ hη hζ v), map_sub,
    coverDifferentialResidue_eq_zero_of_regular N n radicand v ζ
      ((mem_cover_regularDifferentials_iff_ord_nonneg N n radicand ζ).mp hζ v), sub_zero,
    coverDifferentialResidue_simplePole N n radicand v η (hη v), hres]


end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart

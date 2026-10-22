import Dubon2026.SourceOriginalPathIntegralSubtraction
import Dubon2026.SourceOriginalSimplePoleBounds
import Dubon2026.SourceOriginalRegularOrders

/-! DUB-17/18 -> original torsion cardinality -> Abel converse -> period correction.
Subtracting an actual original regular differential preserves every simple-pole
bound and every prescribed divisor residue. The proof uses the already proved
linear local residue map, including zero differentials and cancelled poles.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem original_simple_poles_sub_regular (η ζ : Ω[F⁄ℂ])
    (hη : ∀ v : Place ℂ F, -1 ≤ v.ordDifferential η)
    (hζ : ζ ∈ regularDifferentials ℂ F) :
    ∀ v : Place ℂ F, -1 ≤ v.ordDifferential (η - ζ) := by
  intro v
  have hz := (mem_original_regularDifferentials_iff_ord_nonneg N ℂ ζ).mp hζ v
  have hz' : -1 ≤ v.ordDifferential ζ := by omega
  simpa only [neg_one_smul, sub_eq_add_neg] using
    original_simple_pole_add_bound N v (hη v)
      (original_simple_pole_smul_bound N v (-1) hz')

theorem original_residues_sub_regular (D : Divisor ℂ F) (η ζ : Ω[F⁄ℂ])
    (hη : ∀ v : Place ℂ F, -1 ≤ v.ordDifferential η)
    (hres : ∀ v, originalPlaceEval N ℂ v (v.uniformizer * v.differentialCoeff η) = (D v : ℂ))
    (hζ : ζ ∈ regularDifferentials ℂ F) :
    ∀ v, originalPlaceEval N ℂ v (v.uniformizer * v.differentialCoeff (η - ζ)) = (D v : ℂ) := by
  intro v
  rw [← originalDifferentialResidue_simplePole N v (η - ζ)
    (original_simple_poles_sub_regular N η ζ hη hζ v), map_sub,
    originalDifferentialResidue_eq_zero_of_regular N v ζ
      ((mem_original_regularDifferentials_iff_ord_nonneg N ℂ ζ).mp hζ v), sub_zero,
    originalDifferentialResidue_simplePole N v η (hη v), hres]

end
end Dubon2026.SourceFunctionField.OriginalChart

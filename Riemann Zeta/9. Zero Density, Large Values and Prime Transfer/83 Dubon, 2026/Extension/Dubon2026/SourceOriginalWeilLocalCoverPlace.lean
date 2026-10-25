import Dubon2026.SourceOriginalWeilLocalSplittingField
import Dubon2026.SourceCurveRealizedLaurentPlace
import Dubon2026.SourceCurveResidueRestriction

/-! DUB-17/18 -> auxiliary Kummer cover analytic entry -> actual cover place.
The existing Laurent-place construction applied to the actual local field
embedding gives a cover place over the specified original place. The base
uniformizer has order one, so every cover order equals its Laurent order. -/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve CuspTaylor Polynomial
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (f : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (X ^ n - C f : FF[X])

theorem exists_originalWeil_local_cover_place
    (D : Divisor ℂ FF) (hf : f ≠ 0)
    (hfD : ∀ v : Place ℂ FF, v.ord f = (n : ℤ) * D v) (v : Place ℂ FF) :
    ∃ (w : Place ℂ EE) (e : EE →ₐ[ℂ] realizedField), w.restrict FF = v ∧
      (∀ g : FF, e (algebraMap FF EE g) = chartLaurentHom N v g) ∧
      ∀ a : EE, w.ord a = (e a).val.order :=
  Place.exists_place_of_realized_laurent_extension (chartLaurentHom N v) v
    (chartLaurentHom_order N v) (exists_originalWeil_local_splittingField N n D f hf hfD v)

end
end Dubon2026.SourceFunctionField.OriginalChart

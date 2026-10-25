import Dubon2026.SourceOriginalWeilLocalCoverPlace
import Dubon2026.SourceCurveConvergentKummerPlaces

/-! DUB-17/18 -> auxiliary torsion-cover analytic entry -> every cover place.
Native Galois transitivity moves the constructed normalized local embedding
to any specified place in the same fiber. Its exact order comparison proves
ramification index one for all nonzero torsion orders on this complex cover.
Global charts, Abel comparison and auxiliary point division remain open. -/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve CuspTaylor Polynomial
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (f : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (X ^ n - C f : FF[X])

theorem exists_originalWeil_normalized_local_embedding
    (D : Divisor ℂ FF) (hf : f ≠ 0)
    (hfD : ∀ v : Place ℂ FF, v.ord f = (n : ℤ) * D v) (w : Place ℂ EE) :
    ∃ e : EE →ₐ[ℂ] realizedField,
      (∀ g : FF, e (algebraMap FF EE g) = chartLaurentHom N (w.restrict FF) g) ∧
      ∀ a : EE, w.ord a = (e a).val.order :=
  Place.exists_normalized_convergent_kummer_embedding n f hf w
    (chartLaurentHom N (w.restrict FF))
    (exists_originalWeil_local_cover_place N n f D hf hfD (w.restrict FF))

theorem originalWeil_complex_kummer_unramified
    (D : Divisor ℂ FF) (hf : f ≠ 0)
    (hfD : ∀ v : Place ℂ FF, v.ord f = (n : ℤ) * D v) (w : Place ℂ EE) :
    w.ramificationIndex (F := FF) = 1 := by
  obtain ⟨e, he, ho⟩ := exists_originalWeil_normalized_local_embedding N n f D hf hfD w
  apply Nat.cast_injective (R := ℤ)
  rw [w.ramificationIndex_cast, ho, he]
  exact (chartLaurentHom_order N (w.restrict FF) _ (w.restrict FF).uniformizer_ne_zero).trans
    (w.restrict FF).ord_uniformizer

end
end Dubon2026.SourceFunctionField.OriginalChart

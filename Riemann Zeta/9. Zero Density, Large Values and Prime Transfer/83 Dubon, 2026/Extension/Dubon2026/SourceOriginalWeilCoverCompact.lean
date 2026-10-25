import Dubon2026.SourceOriginalWeilRestrictionTopology
import Dubon2026.SourceOriginalWeilCoverHausdorff
import Dubon2026.SourceCurveUnramifiedFiberCard
import Dubon2026.SourceFiniteFiberOpenMap
import Dubon2026.SourceOriginalComplexCompact

/-! DUB-17/18 -> auxiliary point division -> compact cover Abel comparison.
The actual unramified restriction has finite fibers of constant cardinal.
Its proved continuity and openness make it proper, and the original base
is compact. This proves compactness of the literal Kummer cover without
assuming an algebraic-curve compactification or a covering-space model.
-/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Polynomial
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (f : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (X ^ n - C f : FF[X])
local instance compactCoverFinite : FiniteDimensional FF EE := Place.kummerFinite n f
local instance compactCoverIntegral : Algebra.IsIntegral FF EE := Place.kummerIntegral n f
variable (D : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hf : f ≠ 0)
variable (hfD : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord f = (n : ℤ) * D v)
include D hf hfD

theorem card_restriction_fiber (v : Place ℂ FF) :
    Nat.card {w : Place ℂ EE // w.restrict FF = v} = Module.finrank FF EE :=
  Place.card_unramified_restriction_fiber v
    (original_place_residue_algebraMap_bijective N ℂ v)
    (originalWeilKummerCover_residue_bijective N ℂ n f)
    (OriginalChart.originalWeil_complex_kummer_unramified N n f D hf hfD)

theorem place_compactSpace :
    @CompactSpace (Place ℂ EE) (placeTopology N n f D hf hfD) := by
  letI := placeTopology N n f D hf hfD
  letI := OriginalChart.placeTopology N
  letI := place_t2Space N n f D hf hfD
  letI := OriginalChart.place_compactSpace N
  apply compactSpace_of_open_constant_finite_fibers (fun w : Place ℂ EE => w.restrict FF)
    (continuous_restriction N n f D hf hfD) (isOpenMap_restriction N n f D hf hfD)
  · intro v
    exact @Set.toFinite _ _ (Place.finite_placeFiber (E := EE) v)
  · intro v v'
    exact (card_restriction_fiber N n f D hf hfD v).trans
      (card_restriction_fiber N n f D hf hfD v').symm

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart

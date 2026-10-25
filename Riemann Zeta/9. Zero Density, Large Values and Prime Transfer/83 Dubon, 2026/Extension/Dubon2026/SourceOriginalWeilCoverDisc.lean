import Dubon2026.SourceOriginalWeilEveryLocalCover
import Dubon2026.SourceCurveNormalizedCommonDisc
import Dubon2026.SourceOriginalWeilKummerGeometry

/-! DUB-17/18 -> original Weil nondegeneracy -> auxiliary Kummer point division.
Every place of the literal torsion cover has a common positive meromorphic disk,
with its actual normalized orders and the original base chart embedding.
Global compatible charts, compactness, Abel comparison and division remain open. -/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve CuspTaylor Polynomial IntermediateField Metric
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (f : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (X ^ n - C f : FF[X])

local instance coverIntegral : Algebra.IsIntegral FF EE :=
  Place.kummerIntegral n f

theorem exists_originalWeil_cover_common_disc
    (D : Divisor ℂ FF) (hf : f ≠ 0)
    (hfD : ∀ v : Place ℂ FF, v.ord f = (n : ℤ) * D v) (w : Place ℂ EE) :
    ∃ (e : EE →ₐ[ℂ] realizedField) (R : ℝ), 0 < R ∧
      (∀ g : FF, e (algebraMap FF EE g) = chartLaurentHom N (w.restrict FF) g) ∧
      ∀ a : EE, ∃ G : ℂ → ℂ,
        MeromorphicOn G (ball 0 R) ∧ Represents (e a).val G ∧
        (a ≠ 0 → meromorphicOrderAt G 0 = (w.ord a : WithTop ℤ)) ∧
        (a ≠ 0 → ∀ z ∈ ball 0 R, meromorphicOrderAt G z ≠ ⊤) :=
  exists_normalized_common_disc_with (algebraMap FF EE (jOver N ℂ))
    (originalWeilKummerCover_finite_coordinate N ℂ n f).2 w
    (fun e => ∀ g : FF, e (algebraMap FF EE g) = chartLaurentHom N (w.restrict FF) g)
    (exists_originalWeil_normalized_local_embedding N n f D hf hfD w)

end
end Dubon2026.SourceFunctionField.OriginalChart

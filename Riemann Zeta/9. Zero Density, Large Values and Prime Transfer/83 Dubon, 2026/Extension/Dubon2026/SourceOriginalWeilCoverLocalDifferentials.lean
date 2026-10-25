import Dubon2026.SourceOriginalWeilKummerGeometry
import Dubon2026.SourceCurveLocalDifferentials
import Dubon2026.SourceCurveExactDerivativeOrder

/-! DUB-17/18 -> cover Abel comparison -> actual differential readings.
The literal finite cover coordinate supplies local differential spanning,
and the existing curve theorem supplies rank one. These identify regular
algebraic differentials with their actual uniformizer coefficient condition.
-/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Polynomial KaehlerDifferential
variable (N : ℕ) [NeZero N] (n : ℕ) (r : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (X ^ n - C r : Polynomial FF)

theorem cover_place_dCoordGenerates (v : Place ℂ EE) : v.DCoordGenerates := by
  letI := (originalWeilKummerCover_finite_coordinate N ℂ n r).2
  exact finite_coordinate_place_dCoordGenerates (algebraMap FF EE (jOver N ℂ)) v

theorem cover_differentials_nontrivial : Nontrivial Ω[EE⁄ℂ] :=
  Module.nontrivial_of_finrank_eq_succ (n := 0)
    (originalWeilKummerCover_curve N ℂ n r).kaehler_free_rank_one.2

theorem mem_cover_regularDifferentials_iff (ω : Ω[EE⁄ℂ]) :
    ω ∈ regularDifferentials ℂ EE ↔
      ∀ v : Place ℂ EE, v.differentialCoeff ω ∈ v.toValuationSubring := by
  letI : ∀ v : Place ℂ EE, v.DCoordGenerates := cover_place_dCoordGenerates N n r
  letI := cover_differentials_nontrivial N n r
  constructor
  · intro h v
    obtain ⟨a, ha, he⟩ := h v
    rwa [v.differentialCoeff_unique he]
  · intro h v
    exact ⟨v.differentialCoeff ω, h v, (v.differentialCoeff_smul_dCoord ω).symm⟩

theorem mem_cover_regularDifferentials_iff_ord_nonneg (ω : Ω[EE⁄ℂ]) :
    ω ∈ regularDifferentials ℂ EE ↔
      ∀ v : Place ℂ EE, 0 ≤ v.ordDifferential ω := by
  rw [mem_cover_regularDifferentials_iff]
  exact forall_congr' fun v => v.mem_iff_ord_nonneg

theorem cover_ordDifferential_D_eq_ord_sub_one (v : Place ℂ EE) {f : EE}
    (hf : v.ord f ≠ 0) :
    v.ordDifferential (D ℂ EE f) = v.ord f - 1 := by
  letI := (originalWeilKummerCover_finite_coordinate N ℂ n r).2
  letI := finite_coordinate_place_differentials (algebraMap FF EE (jOver N ℂ)) v
  letI := finite_coordinate_place_residue (algebraMap FF EE (jOver N ℂ)) v
  letI := cover_place_dCoordGenerates N n r v
  letI := cover_differentials_nontrivial N n r
  exact v.ordDifferential_D_eq_ord_sub_one hf

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart

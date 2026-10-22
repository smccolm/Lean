import Dubon2026.SourceOriginalFiberAbelJacobi
import Dubon2026.SourceOriginalPrincipalFiberComparison
import Dubon2026.SourcePeriodCosetConstancy
import Dubon2026.SourceCurvePicardGroup

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi -> principal
divisor kernel. Every literal principal divisor of the original modular
function field has Abel-Jacobi vector in the integer span of actual loop
periods. Local weighted-fiber constancy is proved from original chart
orders, primitives and residues; native constancy on the parameter plane
then compares the fibers over zero and one of f and its reciprocal.
The converse kernel statement and period discreteness remain separate.
Adapted from S_AlgebraicCurve_abelJacobiDiv_mem_pathPeriodLattice_of_isPrincipal,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ
attribute [local instance] placeTopology

theorem original_abelJacobiDiv_mem_of_isPrincipal {n : ℕ}
    (b : Fin n → regularDifferentials ℂ F) (P₀ : Place ℂ F)
    (D : Divisor ℂ F) (hD : Divisor.IsPrincipal D) :
    abelJacobiDiv N (fun i => (b i : Ω[F⁄ℂ])) P₀ D ∈
      pathPeriodLattice N (fun i => (b i : Ω[F⁄ℂ])) := by
  obtain ⟨f, _, hDf⟩ := hD
  let bb : Fin n → Ω[F⁄ℂ] := fun i => (b i : Ω[F⁄ℂ])
  let Λ := pathPeriodLattice N bb
  let AJ := abelJacobiDiv N bb P₀
  let Z : F → ℂ → Divisor ℂ F := fun g t => originalZeroDivisor N (g - algebraMap ℂ F t)
  have hZ : ∀ (g : F) (t : ℂ) (v : Place ℂ F),
      Z g t v = max (v.ord (g - algebraMap ℂ F t)) 0 :=
    fun g t v => originalZeroDivisor_apply N _ v
  have hconst : ∀ (g : F) (t s : ℂ), AJ (Z g t) - AJ (Z g s) ∈ Λ := fun g =>
    PeriodCoset.sub_mem_of_eventually_sub_mem Λ.toAddSubgroup (fun t => AJ (Z g t))
      fun t₀ => eventually_original_abelJacobiDiv_fiber_sub_mem N b P₀ g (Z g) (hZ g) t₀
  have hD1 : D = Z f 0 - Z f⁻¹ 0 := by
    have he : D = originalPrincipalDivisor N ℂ f := Finsupp.ext hDf
    rw [he, original_principal_zero_difference]
    simp only [Z, map_zero, sub_zero]
  have hD2 : Z f 1 = Z f⁻¹ 1 := by
    simp only [Z, map_one]
    exact original_zero_fiber_one_eq N f
  have hsplit : AJ D = -(AJ (Z f 1) - AJ (Z f 0)) + (AJ (Z f⁻¹ 1) - AJ (Z f⁻¹ 0)) := by
    rw [hD1, map_sub, hD2]
    abel
  change AJ D ∈ Λ
  rw [hsplit]
  exact Λ.add_mem (Λ.neg_mem (hconst f 1 0)) (hconst f⁻¹ 1 0)

end
end Dubon2026.SourceFunctionField.OriginalChart

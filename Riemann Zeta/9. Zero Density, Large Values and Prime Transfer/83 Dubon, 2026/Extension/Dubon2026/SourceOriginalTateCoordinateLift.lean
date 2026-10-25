import Dubon2026.SourceTateTorusCoordinateLift
import Dubon2026.SourceOriginalTatePeriod
import Dubon2026.SourceOriginalTateGalois

/-! DUB-17/18 -> original Tate Weil nondegeneracy -> finite torsion lifts.
Transport the divided-lattice lift through the proved original Abel and
arithmetic/complex comparisons. All comparison and surjectivity inputs
are derived for the actual original curve. -/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve KaehlerDifferential OriginalConstantField
variable (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]
local notation "F" => modularFunctionFieldOver N ℂ

theorem originalTateTorsionCoordinate_surjective_of_basis {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (regularDifferentials ℂ F)) (P₀ : Place ℂ F)
    (k : ℕ) : Function.Surjective (originalTateTorsionCoordinate N p k) := by
  let e := originalPicardPeriodEquiv N b P₀
  let t := originalTatePeriodQuotientEquiv N p b P₀
  intro q
  obtain ⟨y, hy⟩ := TateModule.Period.exists_tate_coordinate_of_torsion_image ℂ p
    (pathPeriodLattice N (fun i => (b i).val))
    (e.toAddMonoidHom.comp (complexPicardMap N)) k q.val
    (Pic0.mem_torsion_iff.mp q.property)
  refine ⟨t.symm y, Subtype.ext ?_⟩
  apply complexPicardMap_injective N
  apply e.injective
  have ht := originalTatePeriodQuotientEquiv_apply N p b P₀ (t.symm y) k
  have ht' := congrArg (fun z : TateModule p ((Fin n → ℂ) ⧸
    pathPeriodLattice N (fun i => (b i).val)) => z.val k) (t.apply_symm_apply y)
  exact ht.symm.trans (ht'.trans hy)

theorem originalTateTorsionCoordinate_surjective (k : ℕ) :
    Function.Surjective (originalTateTorsionCoordinate N p k) := by
  letI := finite_original_regularDifferentials N ℂ
  let b := Module.finBasis ℂ (regularDifferentials ℂ F)
  obtain ⟨P₀⟩ := nonempty_original_places N ℂ
  exact originalTateTorsionCoordinate_surjective_of_basis N p b P₀ k

end
end Dubon2026.SourceFunctionField.OriginalChart

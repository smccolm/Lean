import Dubon2026.SourceRadialMeromorphicJumpPeriodClosure
import Dubon2026.SourceRadialCellBoundaryCoordinates

/-! DUB-17/18 -> original Abel-Jacobi -> meromorphic loop-period generation.
Compare principal-log cell readings modulo actual residue periods, then use
the constructed paired-arc jumps and original carrier intersection chains.
The exact readings will anchor the global pole-avoiding path atlas.
Adapted from S_AlgebraicCurve_CellDissection_exists_int_pathIntegral_eq_sum_periods_add_sum_residues,
anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.RadialMeromorphicPeriods
noncomputable section
open Set Filter Complex RadialCellDissection RadialDissectionPeriods
open scoped Real Topology
variable {X R : Type*} [TopologicalSpace X]

/-- A cell primitive reading with the principal logarithmic residue term. -/
noncomputable def pval {𝒟 : RadialCellDissection X} (S : Finset (X))
    (residue : X → R → ℂ) (Ψ : R → 𝒟.ιC → ℂ → ℂ) (D : 𝒟.ιC) (x : X) : R → ℂ :=
  fun r => Ψ r D ((𝒟.cell D).ζ x) + ρ 𝒟 S residue D r * Complex.log ((𝒟.cell D).ζ x - (𝒟.cell D).R.q)


theorem zsmul_ρ_mem_Λres {𝒟 : RadialCellDissection X} (S : Finset (X))
    (residue : X → R → ℂ) (D : 𝒟.ιC) (n : ℤ) :
    (fun r => ρ 𝒟 S residue D r * (n * (2 * π * I))) ∈ Λres 𝒟 S residue := by
  have : (fun r => ρ 𝒟 S residue D r * (n * (2 * π * I))) = n • ((2 * π * I) • ρ 𝒟 S residue D) := by
    funext r; simp only [Pi.smul_apply, smul_eq_mul, zsmul_eq_mul]; ring
  rw [this]
  have hmem : (2 * π * I) • ρ 𝒟 S residue D ∈ Set.range (fun D : 𝒟.ιC => (2 * π * I) • ρ 𝒟 S residue D) :=
    ⟨D, rfl⟩
  exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure hmem) _


theorem hfun_sub_pval_mem {𝒟 : RadialCellDissection X} (S : Finset (X))
    (residue : X → R → ℂ) (Ψ : R → 𝒟.ιC → ℂ → ℂ) (D : 𝒟.ιC) (s : ℝ) :
    hfun S residue Ψ D s - pval S residue Ψ D ((𝒟.cell D).bdry s) ∈ Λres 𝒟 S residue := by
  obtain ⟨-, hζ⟩ := (𝒟.cell D).bdry_coordinates s
  set Rr := (𝒟.cell D).R with hR
  have hne : Rr.loop s - Rr.q ≠ 0 := sub_ne_zero.mpr (Rr.loop_ne_center s)

  have hexp : exp (logTerm (D := 𝒟) D s) = exp (Complex.log (Rr.loop s - Rr.q)) := by
    rw [exp_log hne, logTerm, exp_add, Rr.loop_sub_center, ← ofReal_exp, Real.exp_log (Rr.hpos s)]
  obtain ⟨n, hn⟩ := exp_eq_exp_iff_exists_int.1 hexp
  have : hfun S residue Ψ D s - pval S residue Ψ D ((𝒟.cell D).bdry s) =
      fun r => ρ 𝒟 S residue D r * (n * (2 * π * I)) := by
    funext r
    simp only [hfun, pval, Pi.sub_apply, hζ, hn]
    ring
  rw [this]
  exact zsmul_ρ_mem_Λres S residue D n

/-- The sum of actual primitive jumps and cell residue periods. -/
noncomputable def ΛJ (𝒟 : RadialCellDissection X) (S : Finset (X)) (residue : X → R → ℂ)
    (J : 𝒟.ιE → R → ℂ) : AddSubgroup (R → ℂ) :=
  AddSubgroup.closure (Set.range J) ⊔ Λres 𝒟 S residue

end
end Dubon2026.SourceFunctionField.CellGeometry.RadialMeromorphicPeriods

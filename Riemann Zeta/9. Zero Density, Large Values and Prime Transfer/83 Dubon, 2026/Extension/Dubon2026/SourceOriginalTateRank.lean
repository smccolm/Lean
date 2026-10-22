import Dubon2026.SourceOriginalTatePeriod

/-! DUB-17/18 -> arithmetic modular realization -> original Tate rank.
The actual original integral period lattice is already proved finite free
of rank 2g. Its basis and the explicit Tate comparison give a finite free
p-adic module of that same rank on the literal original arithmetic Picard group.
No basis, finite-rank or dimension premise remains in the final theorem.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]
local notation "F" => modularFunctionFieldOver N ℂ

theorem original_tate_free_finite_rank :
    Module.Free ℤ_[p] (TateModule p (originalJZero N)) ∧
      Module.Finite ℤ_[p] (TateModule p (originalJZero N)) ∧
      Module.finrank ℤ_[p] (TateModule p (originalJZero N)) = 2 * originalGenus N ℂ := by
  letI := finite_original_regularDifferentials N ℂ
  let b := Module.finBasis ℂ (regularDifferentials ℂ F)
  obtain ⟨P₀⟩ := nonempty_original_places N ℂ
  obtain ⟨hfree, hfinite, hrank⟩ := original_period_lattice_free_finite_rank N b
  let L := pathPeriodLattice N (fun i => (b i : Ω[F⁄ℂ]))
  letI : Module.Free ℤ L := hfree
  letI : Module.Finite ℤ L := hfinite
  let lb := Module.finBasis ℤ L
  let e := originalTatePeriodTensorEquiv N p b P₀ lb
  let tb := (Algebra.TensorProduct.basis ℤ_[p] lb).map e.symm
  refine ⟨Module.Free.of_basis tb, Module.Finite.of_basis tb, ?_⟩
  rw [Module.finrank_eq_card_basis tb, Fintype.card_fin]
  rw [hrank, finrank_original_regularDifferentials_eq_genus N ℂ]

end
end Dubon2026.SourceFunctionField.OriginalChart

import Dubon2026.SourceOriginalPicardAbelMap
import Dubon2026.SourceOriginalPeriodLatticeRank

/-! DUB-17/18 -> original torsion cardinality -> complex Picard comparison.
The literal original degree-zero divisor-class group is additively equivalent
to the quotient by its actual path-period lattice, which is free of rank 2g.
The equivalence sends every original divisor class to its original Abel vector.
This discharges the complex comparison; Qbar transport remains a distinct input
to the arithmetic torsion and Tate-module chain.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N]
attribute [local instance] placeTopology
local notation "F" => modularFunctionFieldOver N ℂ

theorem original_picard_period_comparison {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (regularDifferentials ℂ F)) (P₀ : Place ℂ F) :
    Module.Free ℤ (pathPeriodLattice N (fun i => (b i : Ω[F⁄ℂ]))) ∧
      Module.Finite ℤ (pathPeriodLattice N (fun i => (b i : Ω[F⁄ℂ]))) ∧
      Module.finrank ℤ (pathPeriodLattice N (fun i => (b i : Ω[F⁄ℂ]))) = 2 * n ∧
      ∃ E : Pic0 ℂ F ≃+ (Fin n → ℂ) ⧸ pathPeriodLattice N (fun i => (b i : Ω[F⁄ℂ])),
        ∀ D : Divisor.degZero (K := ℂ) («F» := F),
          E (Pic0.mk D) = (pathPeriodLattice N (fun i => (b i : Ω[F⁄ℂ]))).mkQ
            (abelJacobiDiv N (fun i => (b i : Ω[F⁄ℂ])) P₀ D.val) := by
  obtain ⟨hfree, hfinite, hrank⟩ := original_period_lattice_free_finite_rank N b
  exact ⟨hfree, hfinite, hrank, originalPicardPeriodEquiv N b P₀, fun _ => rfl⟩

end
end Dubon2026.SourceFunctionField.OriginalChart

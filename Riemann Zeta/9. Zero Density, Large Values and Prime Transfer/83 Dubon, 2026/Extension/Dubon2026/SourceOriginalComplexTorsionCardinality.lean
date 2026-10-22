import Dubon2026.SourceComplexLatticeTorsion
import Dubon2026.SourceAdditiveTorsionTransport
import Dubon2026.SourceOriginalPicardPeriodComparison
import Dubon2026.SourceOriginalNumericalGenus

/-! DUB-17/18 -> original Jacobian Tate module -> exact original torsion cardinality.
The actual complex Picard equivalence transports n-torsion to the actual period
quotient. The native free-module ModN count and proved rank 2g give n^(2g), for
every nonzero natural n. The genus is that of the original modular field.
Comparison with Qbar remains necessary for the arithmetic Tate realization.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem original_complex_torsion_cardinality (m : ℕ) (hm : m ≠ 0) :
    Nat.card (Pic0.torsion (K := ℂ) («F» := F) m) = m ^ (2 * originalGenus N ℂ) := by
  letI := finite_original_regularDifferentials N ℂ
  let b := Module.finBasis ℂ (regularDifferentials ℂ F)
  obtain ⟨P₀⟩ := nonempty_original_places N ℂ
  obtain ⟨hfree, hfinite, hrank, E, _⟩ := original_picard_period_comparison N b P₀
  let L := pathPeriodLattice N (fun i => (b i : Ω[F⁄ℂ]))
  letI : Module.Free ℤ L := hfree
  letI : Module.Finite ℤ L := hfinite
  change Nat.card (Submodule.torsionBy ℤ (Pic0 ℂ F) (m : ℤ)) = _
  rw [ComplexLatticeTorsion.natCard_torsionBy_congr E (m : ℤ),
    ComplexLatticeTorsion.natCard_torsion_quotient L m hm, hrank,
    finrank_original_regularDifferentials_eq_genus N ℂ]

end
end Dubon2026.SourceFunctionField.OriginalChart

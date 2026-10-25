import Dubon2026.SourceOriginalWeilCoverRiemannRoch
import Dubon2026.SourceCurveTwoPoleDimensions

/-! DUB-17/18 -> auxiliary point division -> cover Abel converse.
The actual finite-coordinate Riemann-Roch identity supplies the two-pole
dimension increase and the resulting differential with exactly two simple
poles. The existing original proof is adapted to the same literal Kummer
field. Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_exists_ordDifferential_eq_neg_one_of_ne.
-/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N] (n : ℕ) (r : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C r : Polynomial FF)

theorem cover_two_pole_dimensions {ω₀ : Ω[EE⁄ℂ]} (hω₀ : ω₀ ≠ 0)
    (P Q : Place ℂ EE) :
    let K₀ := coverCanonicalDivisor N n r (ω := ω₀) hω₀
    let P1 : Divisor ℂ EE := Finsupp.single P 1
    let Q1 : Divisor ℂ EE := Finsupp.single Q 1
    (ell (K₀ + P1 + Q1) : ℤ) = ell (K₀ + P1) + 1 ∧
      (ell (K₀ + P1 + Q1) : ℤ) = ell (K₀ + Q1) + 1 := by
  letI := originalWeilKummerCover_curve N ℂ n r
  have hexRR := exists_cover_riemann_roch_constant N n r
  obtain ⟨γ, hRR⟩ := hexRR
  exact two_pole_dimensions_of_riemann_roch (F := EE)
    (coverCanonicalDivisor N n r (ω := ω₀) hω₀) γ (hRR hω₀) P Q
    (Module.finrank_of_bijective_algebraMap (originalWeilKummerCover_residue_bijective N ℂ n r P))
    (Module.finrank_of_bijective_algebraMap (originalWeilKummerCover_residue_bijective N ℂ n r Q))

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart

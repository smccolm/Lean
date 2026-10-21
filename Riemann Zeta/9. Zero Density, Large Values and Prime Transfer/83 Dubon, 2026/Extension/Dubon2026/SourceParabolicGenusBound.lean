import Dubon2026.SourceManinParabolicDimension
import Dubon2026.SourceLevelIndexFormula
import Dubon2026.SourceLevelEllipticCosets
import Dubon2026.SourceCuspCount

/-! DUB-17/18 -> original parabolic Hecke realization -> period surjectivity
-> matching dimensions. This assembles the actual Manin-relation inequality
with proved index, elliptic fixed-point and cusp-orbit counts. The genus
expression remains explicitly arithmetic; its geometric identification and
the matching cusp-form lower bound are separate unresolved obligations.
-/
namespace Dubon2026
open SourceLevelProjective

theorem sourceParabolic_dimension_le_two_mul_genusFormula (N : ℕ) [NeZero N] :
    (Module.finrank ℂ (SourceCuspBoundary.parabolicHoms N) : ℚ) ≤
      2 * genusFormula N := by
  have h := SourceManin.parabolic_dimension_bound N
  rw [SourceManin.CuspSpace.card_cuspSpace_eq_cuspCount (NeZero.ne N),
    SourceElliptic.card_fixed_S, SourceElliptic.card_fixed_ST,
    gamma0_index] at h
  have hq : 6 * (Module.finrank ℂ (SourceCuspBoundary.parabolicHoms N) : ℚ)
      + 6 * (cuspCount N : ℚ) + 3 * (nuTwo N : ℚ) + 4 * (nuThree N : ℚ)
      ≤ 12 + (dedekindPsi N : ℚ) := by exact_mod_cast h
  unfold genusFormula
  linarith

end Dubon2026

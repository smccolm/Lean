import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.RingTheory.Norm.Transitivity

/-! # Actual Galois norm invariance over a complete nonarchimedean base -/

namespace Dubon2026
noncomputable section

variable {K L : Type} [NontriviallyNormedField K] [NormedField L]
  [NormedAlgebra K L] [IsUltrametricDist K] [CompleteSpace K]

/-- Uniqueness of the original norm extension and the actual minimal
polynomial identity prove invariance under every original Galois automorphism. -/
theorem completeNonarchimedeanGalois_norm_map [Algebra.IsAlgebraic K L]
    (g : Gal(L/K)) (x : L) : ‖g x‖ = ‖x‖ := by
  rw [NormedAlgebra.norm_eq_spectralNorm K, NormedAlgebra.norm_eq_spectralNorm K]
  exact (spectralNorm_eq_of_equiv g x).symm

/-- The actual field norm has absolute value equal to the actual extension
degree power of the original element norm. Galois norm invariance is proved
from the complete nonarchimedean base, not assumed as a certificate. -/
theorem completeNonarchimedeanGalois_norm_fieldNorm
    [FiniteDimensional K L] [IsGalois K L] (x : L) :
    ‖Algebra.norm K x‖ = ‖x‖ ^ Module.finrank K L := by
  rw [← norm_algebraMap' L (Algebra.norm K x), Algebra.norm_eq_prod_automorphisms, norm_prod]
  simp_rw [completeNonarchimedeanGalois_norm_map]
  rw [Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    IsGalois.card_aut_eq_finrank]

end
end Dubon2026

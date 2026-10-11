import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.FieldTheory.Separable

/-! # Separability lifted from the actual residue polynomial -/

namespace Dubon2026
noncomputable section

open Polynomial

/-- For a monic first polynomial, the actual resultant commutes with an
arbitrary coefficient map even when the second polynomial loses degree. -/
theorem monic_resultant_map {R S : Type} [CommRing R] [CommRing S]
    [Nontrivial S] (φ : R →+* S) (f g : R[X]) (hf : f.Monic) :
    (f.map φ).resultant (g.map φ) = φ (f.resultant g) := by
  have hg : (g.map φ).natDegree ≤ g.natDegree := Polynomial.natDegree_map_le
  have hd : (g.map φ).natDegree + (g.natDegree - (g.map φ).natDegree) =
      g.natDegree := Nat.add_sub_of_le hg
  have h := Polynomial.resultant_add_right_deg (f.map φ) (g.map φ)
    (f.map φ).natDegree (g.map φ).natDegree
    (g.natDegree - (g.map φ).natDegree) le_rfl
  rw [hd, (hf.map φ).coeff_natDegree, one_pow, one_mul] at h
  rw [← h, hf.natDegree_map φ, Polynomial.resultant_map_map]

/-- A monic polynomial over the original local ring is separable when its
actual residue polynomial is separable. The proof lifts the resultant unit. -/
theorem local_monic_separable_of_residue {R : Type} [CommRing R]
    [IsLocalRing R] (f : R[X]) (hf : f.Monic)
    (hs : (f.map (IsLocalRing.residue R)).Separable) : f.Separable := by
  apply (Polynomial.separable_def f).mpr
  apply (Polynomial.isUnit_resultant_iff_isCoprime hf).mp
  apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
  rw [← monic_resultant_map (IsLocalRing.residue R) f f.derivative hf,
    ← Polynomial.derivative_map]
  exact ((Polynomial.isUnit_resultant_iff_isCoprime
    (hf.map (IsLocalRing.residue R))).mpr ((Polynomial.separable_def _).mp hs)).ne_zero

end
end Dubon2026

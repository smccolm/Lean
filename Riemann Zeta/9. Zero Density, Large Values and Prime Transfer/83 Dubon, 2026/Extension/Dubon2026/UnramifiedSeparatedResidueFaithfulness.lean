import Mathlib.RingTheory.Unramified.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! # Original unramified automorphisms are determined by their residue action -/

namespace Dubon2026
noncomputable section

open IsLocalRing

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing S]
  [Algebra.FormallyUnramified R S] [IsHausdorff (maximalIdeal S) S]

/-- Actual formal unramifiedness and original adic separatedness make
original algebra automorphisms equal when their actual residue actions agree. -/
theorem unramifiedSeparated_algEquiv_eq_of_residue (f g : S ≃ₐ[R] S)
    (h : ∀ x, residue S (f x) = residue S (g x)) : f = g := by
  have hI : (⨅ n : ℕ, maximalIdeal S ^ n) = ⊥ := by
    simpa [Ideal.smul_eq_mul] using
      (inferInstance : IsHausdorff (maximalIdeal S) S).iInf_pow_smul
  have he : f.toAlgHom = g.toAlgHom :=
    Algebra.FormallyUnramified.ext_of_iInf (maximalIdeal S) hI h
  ext x
  exact DFunLike.congr_fun he x

end
end Dubon2026

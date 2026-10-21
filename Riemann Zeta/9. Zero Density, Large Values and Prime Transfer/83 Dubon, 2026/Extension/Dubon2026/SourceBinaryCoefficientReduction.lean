import Dubon2026.SourceBinaryCohomologyChange
import Mathlib.Data.ZMod.Basic

/-! Exact prime reduction on the actual homogeneous coefficient module.
DUB-17/18 -> residual modular Galois association -> residual binary H1
eigensystem -> injective tensor coefficient change -> prime-reduction kernel.

The coefficient lifting and division arguments adapt the Bockstein section of
anthropics/fermats-last-theorem, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_HeckeEis_exists_coeffH1_map_ringHom_binaryFormRepSL.lean
(Apache-2.0; retained LICENSE and NOTICE). Existing homogeneous spaces and
the proved literal coefficient map are retained.
-/

namespace Dubon2026
noncomputable section
open MvPolynomial

/-- Surjective scalar coefficient change is surjective on each original binary homogeneous space. -/
theorem sourceBinaryCoefficientMap_surjective {R S : Type} [CommRing R] [CommRing S]
    (w : ℕ) (φ : R →+* S) (hφ : Function.Surjective φ) :
    Function.Surjective (homogeneousCoefficientMap (ι := Fin 2) w φ) := by
  classical
  intro v
  let s : S → R := fun a => (hφ a).choose
  have hs (a : S) : φ (s a) = a := (hφ a).choose_spec
  let P := ∑ m ∈ v.val.support, monomial m (s (v.val.coeff m))
  have hP : P ∈ homogeneousSubmodule (Fin 2) R w := by
    rw [mem_homogeneousSubmodule]
    refine IsHomogeneous.sum _ _ _ fun m hm => ?_
    refine isHomogeneous_monomial _ ?_
    rw [Finsupp.degree_eq_weight_one]
    exact (mem_homogeneousSubmodule w _).mp v.property (mem_support_iff.mp hm)
  refine ⟨⟨P, hP⟩, Subtype.ext ?_⟩
  change map φ P = v.val
  simp only [P, map_sum, map_monomial, hs]
  exact v.val.as_sum.symm

/-- The kernel of original binary coefficient change modulo a prime consists of prime multiples. -/
theorem sourceBinaryCoefficientMap_zmod_kernel (w ell : ℕ)
    (v : homogeneousSubmodule (Fin 2) ℤ w)
    (hv : homogeneousCoefficientMap w (Int.castRingHom (ZMod ell)) v = 0) :
    ∃ u : homogeneousSubmodule (Fin 2) ℤ w, (ell : ℤ) • u = v := by
  classical
  have hcoef (m : Fin 2 →₀ ℕ) : (ell : ℤ) ∣ v.val.coeff m := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ ell).mp
    have h := congrArg (fun P : homogeneousSubmodule (Fin 2) (ZMod ell) w =>
      P.val.coeff m) hv
    exact h
  choose t ht using hcoef
  let P := ∑ m ∈ v.val.support, monomial m (t m)
  have hP : P ∈ homogeneousSubmodule (Fin 2) ℤ w := by
    rw [mem_homogeneousSubmodule]
    refine IsHomogeneous.sum _ _ _ fun m hm => ?_
    refine isHomogeneous_monomial _ ?_
    rw [Finsupp.degree_eq_weight_one]
    exact (mem_homogeneousSubmodule w _).mp v.property (mem_support_iff.mp hm)
  refine ⟨⟨P, hP⟩, Subtype.ext ?_⟩
  apply MvPolynomial.ext
  intro m
  change (ell : ℤ) * P.coeff m = v.val.coeff m
  simp only [P, coeff_sum, coeff_monomial, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_eq_single m]
  · rw [if_pos rfl, ← ht]
  · intro d _ hdm
    rw [if_neg hdm]
  · intro hm
    rw [if_pos rfl, ← ht]
    exact Finsupp.notMem_support_iff.mp hm

/-- Nonzero integer multiplication is injective on the original integral binary coefficient module. -/
theorem sourceBinaryCoefficient_int_smul_injective (w : ℕ) (d : ℤ) (hd : d ≠ 0) :
    Function.Injective (fun v : homogeneousSubmodule (Fin 2) ℤ w => d • v) := by
  intro u v huv
  apply Subtype.ext
  apply MvPolynomial.ext
  intro m
  apply mul_left_cancel₀ hd
  exact congrArg (fun P : homogeneousSubmodule (Fin 2) ℤ w => P.val.coeff m) huv

end
end Dubon2026

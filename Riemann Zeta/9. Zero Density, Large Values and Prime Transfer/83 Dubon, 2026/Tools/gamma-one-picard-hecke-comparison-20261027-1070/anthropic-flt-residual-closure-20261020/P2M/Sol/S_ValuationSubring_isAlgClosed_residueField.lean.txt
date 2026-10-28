import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Algebra.Polynomial.Lifts
import Theorems.Thm_ValuationSubring_exists_root_mem_of_monic
import P2M.Util
namespace P2MW.S_ValuationSubring_isAlgClosed_residueField

set_option autoImplicit false

open IsLocalRing

theorem solution {K : Type*} [Field K] [IsAlgClosed K] (A : ValuationSubring K) :
    IsAlgClosed (IsLocalRing.ResidueField A) := by
  apply IsAlgClosed.of_exists_root
  intro p hmonic hirr
  have hlift : p ∈ Polynomial.lifts (residue A) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    exact fun n => residue_surjective _
  obtain ⟨f, hmap, hdeg, hf⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hmonic
  have hd : f.natDegree ≠ 0 := by
    rw [Polynomial.natDegree_eq_of_degree_eq hdeg]
    exact hirr.natDegree_pos.ne'
  obtain ⟨x, hx⟩ := ValuationSubring.exists_root_mem_of_monic A f hf hd
  refine ⟨residue A x, ?_⟩
  have hx0 : f.eval x = 0 := by
    have h1 : (algebraMap A K) (f.eval x) = 0 := by
      rw [← hx, Polynomial.aeval_def]
      exact (Polynomial.eval₂_at_apply (algebraMap A K) x).symm
    exact Subtype.coe_injective (by simpa using h1)
  rw [← hmap, Polynomial.eval_map, Polynomial.eval₂_at_apply, hx0, map_zero]

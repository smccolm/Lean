import Dubon2026.SourceOriginalTwoPoleDifferential
import Dubon2026.SourceOriginalSimplePoleBounds

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi converse ->
prescribed residues. The original global residue theorem normalizes the
proved two-pole differential to residues +1 and -1. No existence of a
third-kind differential or global residue identity is assumed.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem original_two_pole_residue_sum {P Q : Place ℂ F} (hPQ : P ≠ Q)
    (ω : Ω[F⁄ℂ])
    (hreg : ∀ v : Place ℂ F, v ≠ P → v ≠ Q → 0 ≤ v.ordDifferential ω) :
    originalDifferentialResidue N P ω + originalDifferentialResidue N Q ω = 0 := by
  classical
  have hs : Function.support (fun v => originalDifferentialResidue N v ω) ⊆
      ({P, Q} : Finset (Place ℂ F)) := by
    intro v hv
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
    by_contra hn
    push Not at hn
    exact hv (originalDifferentialResidue_eq_zero_of_regular N v ω (hreg v hn.1 hn.2))
  have h := originalDifferentialResidue_finsum N ω
  rwa [finsum_eq_sum_of_support_subset _ hs, Finset.sum_pair hPQ] at h

open scoped Classical in
theorem exists_original_normalized_two_pole_differential {P Q : Place ℂ F} (hPQ : P ≠ Q) :
    ∃ η : Ω[F⁄ℂ], (∀ v : Place ℂ F, -1 ≤ v.ordDifferential η) ∧
      ∀ v : Place ℂ F, originalDifferentialResidue N v η =
        (if v = P then 1 else 0) - (if v = Q then 1 else 0) := by
  classical
  obtain ⟨ω, _, hP, hQ, hreg⟩ := exists_original_two_pole_differential N hPQ
  have hbound : ∀ v : Place ℂ F, -1 ≤ v.ordDifferential ω := by
    intro v
    by_cases hvP : v = P
    · rw [hvP, hP]
    by_cases hvQ : v = Q
    · rw [hvQ, hQ]
    have h := hreg v hvP hvQ
    omega
  have hPn := originalDifferentialResidue_ne_zero_of_simplePole N P ω hP
  have hsum := original_two_pole_residue_sum N hPQ ω hreg
  have hQres : originalDifferentialResidue N Q ω = -originalDifferentialResidue N P ω :=
    eq_neg_of_add_eq_zero_right hsum
  refine ⟨(originalDifferentialResidue N P ω)⁻¹ • ω,
    fun v => original_simple_pole_smul_bound N v _ (hbound v), ?_⟩
  intro v
  rw [map_smul, smul_eq_mul]
  by_cases hvP : v = P
  · subst v
    simp [hPQ, hPn]
  by_cases hvQ : v = Q
  · subst v
    rw [hQres, mul_neg, inv_mul_cancel₀ hPn]
    simp [hPQ.symm]
  rw [originalDifferentialResidue_eq_zero_of_regular N v ω (hreg v hvP hvQ), mul_zero]
  simp only [if_neg hvP, if_neg hvQ, sub_self]

end
end Dubon2026.SourceFunctionField

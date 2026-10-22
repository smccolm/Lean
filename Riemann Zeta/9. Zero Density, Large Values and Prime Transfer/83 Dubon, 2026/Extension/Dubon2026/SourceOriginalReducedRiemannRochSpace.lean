import Dubon2026.SourceOriginalMeromorphicRRBounds
import Dubon2026.SourceReducedSpaceMinimum

/-! DUB-17/18 -> arithmetic torsion comparison -> finite torsion descent.
The least one-point pole bound admitting a nonzero function has a
one-dimensional Riemann--Roch space. Its unique effective representative
will make finite-order divisor classes invariant under a power of each constant-field automorphism. Existing original pole clearing, finite spaces
and the degree-growth inequality supply all foundations.
Adapted from exists_reduced in
S_AlgebraicCurve_Divisor_exists_torsion_descent_of_constantFieldExtension_of_finite,
anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.OriginalConstantField
noncomputable section
open SourceCurve
variable (N : ℕ) [NeZero N]
local notation "FC" => modularFunctionFieldOver N ℂ

theorem exists_original_reduced_space (c : Divisor ℂ FC) (hc : Divisor.degree c = 0)
    (P : Place ℂ FC) :
    ∃ (r : ℕ) (f : FC), f ≠ 0 ∧ f ∈ LSpace (c + (r : ℤ) • Finsupp.single P (1 : ℤ)) ∧
      ∀ h ∈ LSpace (c + (r : ℤ) • Finsupp.single P (1 : ℤ)), ∃ a : ℂ, a • f = h := by
  classical
  letI := hasPrincipalDivisors_original N ℂ
  letI : ∀ v : Place ℂ FC, Module.Finite ℂ v.ResidueField := finite_original_place_residue N ℂ
  apply ConstantField.exists_reduced_space_of_nonempty (finite_original_lSpace N ℂ) c hc P
    (Module.finrank_of_bijective_algebraMap (original_place_residue_algebraMap_bijective N ℂ P))
  obtain ⟨k, f, hf0, hf⟩ := exists_original_pole_clearing_function N P (-c)
  refine ⟨k, fun hbot => hf0 ?_⟩
  have he : Finsupp.single P (k : ℤ) - -c = c + (k : ℤ) • Finsupp.single P (1 : ℤ) := by
    simp only [sub_neg_eq_add, Finsupp.smul_single, smul_eq_mul, mul_one]
    exact add_comm _ _
  have hf' : f ∈ LSpace (c + (k : ℤ) • Finsupp.single P (1 : ℤ)) :=
    Eq.mp (congrArg (fun D : Divisor ℂ FC => f ∈ LSpace D) he) hf
  have hfbot : f ∈ (⊥ : Submodule ℂ FC) :=
    Eq.mp (congrArg (fun S : Submodule ℂ FC => f ∈ S) hbot) hf'
  exact hfbot

end
end Dubon2026.SourceFunctionField.OriginalConstantField

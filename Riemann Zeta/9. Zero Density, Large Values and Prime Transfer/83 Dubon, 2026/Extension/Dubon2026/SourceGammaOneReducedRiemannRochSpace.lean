import Dubon2026.SourceGammaOneCurveInputs
import Dubon2026.SourceCurveFiniteCoordinateDimensionBounds
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
namespace Dubon2026.SourceFunctionField.GammaOne.ConstantField
noncomputable section
open SourceCurve CongruenceSubgroup
variable (N : ℕ) [NeZero N]
local notation "FC" => functionFieldOver (Gamma1 N) ℂ

theorem exists_reduced_space (c : Divisor ℂ FC) (hc : Divisor.degree c = 0)
    (P : Place ℂ FC) :
    ∃ (r : ℕ) (f : FC), f ≠ 0 ∧ f ∈ LSpace (c + (r : ℤ) • Finsupp.single P (1 : ℤ)) ∧
      ∀ h ∈ LSpace (c + (r : ℤ) • Finsupp.single P (1 : ℤ)), ∃ a : ℂ, a • f = h := by
  classical
  letI := finiteDimensional_jCoordinateOver (Γ := Gamma1 N)
    (by simp [Gamma1_mem, ModularGroup.T]) ℂ
  letI := gamma1_isCurveOver N ℂ
  letI : ∀ v : Place ℂ FC, Module.Finite ℂ v.ResidueField :=
    finite_coordinate_place_residue (jCoordinateOver (Gamma1 N) ℂ)
  letI := finite_lSpace_zero_of_place P
  apply SourceCurve.ConstantField.exists_reduced_space_of_nonempty (fun D => finite_lSpace D) c hc P
    (Module.finrank_of_bijective_algebraMap (place_residue_bijective_of_finite_coordinate (jCoordinateOver (Gamma1 N) ℂ) P))
  obtain ⟨k, f, hf0, hf⟩ := exists_pole_clearing_function_of_finite_coordinate
    (jCoordinateOver (Gamma1 N) ℂ) (transcendental_jCoordinateOver (Gamma1 N) ℂ) P (-c)
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
end Dubon2026.SourceFunctionField.GammaOne.ConstantField

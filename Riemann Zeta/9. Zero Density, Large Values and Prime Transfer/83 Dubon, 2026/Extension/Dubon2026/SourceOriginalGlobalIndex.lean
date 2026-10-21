import Dubon2026.SourceCurveGlobalIndex
import Dubon2026.SourceOriginalGenusBound

/-! DUB-17/18 -> original parabolic Hecke realization -> period surjectivity
-> matching cusp-form dimension -> original regular differential dimension
-> function-field Riemann--Roch. The actual degree-dimension maximum proves
finite global repartition quotients. Evaluating at zero removes the auxiliary
maximum parameter and gives the index formula with the actual zero-divisor
index. Residue duality and equality with the canonical genus remain open.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]

theorem finite_original_index_quotient
    (D : Divisor L (modularFunctionFieldOver N L)) :
    Module.Finite L (adeleSpace L (modularFunctionFieldOver N L) ⧸
      adeleBddPrincipal L (modularFunctionFieldOver N L) D) := by
  haveI : HasPrincipalDivisors L (modularFunctionFieldOver N L) :=
    hasPrincipalDivisors_original N L
  haveI : ∀ v : Place L (modularFunctionFieldOver N L), Module.Finite L v.ResidueField :=
    finite_original_place_residue N L
  haveI := finite_original_lSpace N L (0 : Divisor L (modularFunctionFieldOver N L))
  obtain ⟨γ, D₀, h⟩ := original_degree_dimension_maximum N L
  exact (indexOfSpecialty_eq_of_genusReached h D).1

theorem original_index_formula (D : Divisor L (modularFunctionFieldOver N L)) :
    (ell D : ℤ) - indexOfSpecialty D =
      Divisor.degree D + 1 - indexOfSpecialty (0 : Divisor L (modularFunctionFieldOver N L)) := by
  haveI : HasPrincipalDivisors L (modularFunctionFieldOver N L) :=
    hasPrincipalDivisors_original N L
  haveI : ∀ v : Place L (modularFunctionFieldOver N L), Module.Finite L v.ResidueField :=
    finite_original_place_residue N L
  haveI := finite_original_lSpace N L (0 : Divisor L (modularFunctionFieldOver N L))
  obtain ⟨γ, D₀, h⟩ := original_degree_dimension_maximum N L
  have hD := (indexOfSpecialty_eq_of_genusReached h D).2
  have h0 := (indexOfSpecialty_eq_of_genusReached h 0).2
  have he0 : ell (0 : Divisor L (modularFunctionFieldOver N L)) = 1 := by
    rw [ell, original_lSpace_zero_eq_range N L, LinearMap.finrank_range_of_inj
      (f := Algebra.linearMap L (modularFunctionFieldOver N L))
      (algebraMap L (modularFunctionFieldOver N L)).injective, Module.finrank_self]
  rw [he0, map_zero] at h0
  push_cast at h0
  linarith

theorem finite_original_omegaSpace
    (D : Divisor L (modularFunctionFieldOver N L)) :
    Module.Finite L (omegaSpace D) := by
  haveI := finite_original_index_quotient N L D
  exact Module.Finite.equiv (omegaSpaceEquivIndexDual D).symm

theorem original_omega_dimension_formula
    (D : Divisor L (modularFunctionFieldOver N L)) :
    (ell D : ℤ) - Module.finrank L (omegaSpace D) =
      Divisor.degree D + 1 -
        Module.finrank L (omegaSpace (0 : Divisor L (modularFunctionFieldOver N L))) := by
  rw [finrank_omegaSpace_eq_indexOfSpecialty, finrank_omegaSpace_eq_indexOfSpecialty]
  exact original_index_formula N L D

end
end Dubon2026.SourceFunctionField

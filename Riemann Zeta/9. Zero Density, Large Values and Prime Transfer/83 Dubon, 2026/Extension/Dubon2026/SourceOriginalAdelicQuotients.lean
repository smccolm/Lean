import Dubon2026.SourceCurveAdeleQuotientDimension
import Dubon2026.SourceOriginalPrincipalDivisors
import Dubon2026.SourceOriginalRegularFinite

/-! DUB-17/18 -> the matching cusp-form lower dimension bound -> regular
differential dimension -> the unresolved original function-field
Riemann--Roch theorem. For the literal original field, finite changes
of divisor bounds have finite repartition quotient with dimension exactly
the degree difference. All finite-residue inputs are discharged. Actual
global functions lie in the repartition space, and their bounded part is
the already proved finite original divisor space. Global index stabilization
and residue duality remain necessary for Riemann--Roch.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve

variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L]

theorem nonempty_original_places : Nonempty (Place L (modularFunctionFieldOver N L)) := by
  classical
  by_contra h
  haveI : IsEmpty (Place L (modularFunctionFieldOver N L)) := not_nonempty_iff.mp h
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  haveI : FiniteDimensional (IntermediateField.adjoin L {jOver N L})
      (modularFunctionFieldOver N L) := finiteDimensional_original N L
  have hd := sum_positive_orders_eq_finrank_adjoin (jOver N L) (transcendental_jOver N L)
  simp only [finsum_of_isEmpty] at hd
  have hp := Module.finrank_pos (R := IntermediateField.adjoin L {jOver N L})
    (M := modularFunctionFieldOver N L)
  omega

theorem original_diagonal_mem_adeleSpace (f : modularFunctionFieldOver N L) :
    diagonalHom L (modularFunctionFieldOver N L) f ∈
      adeleSpace L (modularFunctionFieldOver N L) := by
  haveI : HasPrincipalDivisors L (modularFunctionFieldOver N L) :=
    hasPrincipalDivisors_original N L
  exact diagonal_mem_adeleSpace f

/-- Actual original divisor functions are exactly the bounded global repartitions. -/
def originalLSpaceEquivBoundedGlobals (D : Divisor L (modularFunctionFieldOver N L)) :
    LSpace D ≃ₗ[L] (adeleBdd D ⊓ globalSub L (modularFunctionFieldOver N L) :
      Submodule L (Place L (modularFunctionFieldOver N L) → modularFunctionFieldOver N L)) := by
  haveI := nonempty_original_places N L
  exact lSpaceEquivAdeleBddInfGlobal D

theorem finite_original_bounded_globals [IsAlgClosed L]
    (D : Divisor L (modularFunctionFieldOver N L)) :
    Module.Finite L (adeleBdd D ⊓ globalSub L (modularFunctionFieldOver N L) :
      Submodule L (Place L (modularFunctionFieldOver N L) → modularFunctionFieldOver N L)) := by
  haveI := finite_original_lSpace N L D
  exact Module.Finite.equiv (originalLSpaceEquivBoundedGlobals N L D)

theorem finrank_original_adeleBdd_quotient [IsAlgClosed L]
    {D₁ D₂ : Divisor L (modularFunctionFieldOver N L)} (hD : D₁ ≤ D₂) :
    Module.Finite L (adeleBdd D₂ ⧸ (adeleBdd D₁).comap (adeleBdd D₂).subtype) ∧
      (Module.finrank L (adeleBdd D₂ ⧸ (adeleBdd D₁).comap (adeleBdd D₂).subtype) : ℤ) =
        Divisor.degree D₂ - Divisor.degree D₁ := by
  haveI : ∀ v : Place L (modularFunctionFieldOver N L), Module.Finite L v.ResidueField :=
    finite_original_place_residue N L
  exact finrank_adeleBdd_quotient hD

end
end Dubon2026.SourceFunctionField

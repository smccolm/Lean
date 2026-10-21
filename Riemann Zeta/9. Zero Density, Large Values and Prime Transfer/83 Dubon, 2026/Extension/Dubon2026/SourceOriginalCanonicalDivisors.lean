import Dubon2026.SourceCurveDifferentialSupport
import Dubon2026.SourceCurveCanonicalDivisor
import Dubon2026.SourceOriginalLocalFinite
import Dubon2026.SourceOriginalResidueFinite
import Dubon2026.SourceOriginalLocalDifferentials
import Dubon2026.SourceOriginalDivisorSupport

/-! DUB-17/18 -> regular differential dimension -> canonical divisors.
The actual j-coordinate derivative has finite support: coordinate poles and
the different ideal bound the exceptions to local order zero. Since D(j)
spans the actual differential space, the proved principal-divisor support
extends this to every nonzero original differential. No canonical-divisor or
finite differential-support premise remains.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve KaehlerDifferential

variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L]

theorem finite_original_D_jOver_support :
    {v : Place L (modularFunctionFieldOver N L) |
      v.ordDifferential (D L (modularFunctionFieldOver N L) (jOver N L)) ≠ 0}.Finite := by
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  haveI : FiniteDimensional (IntermediateField.adjoin L {jOver N L})
      (modularFunctionFieldOver N L) := finiteDimensional_original N L
  haveI : ∀ v : Place L (modularFunctionFieldOver N L),
      Module.Finite v.toValuationSubring Ω[v.toValuationSubring⁄L] :=
    finite_original_place_differentials N L
  haveI : ∀ v : Place L (modularFunctionFieldOver N L), Algebra.IsAlgebraic L v.ResidueField :=
    original_place_residue_isAlgebraic N L
  haveI : ∀ v : Place L (modularFunctionFieldOver N L), Algebra.IsSeparable L v.ResidueField :=
    fun _ => inferInstance
  haveI : ∀ v : Place L (modularFunctionFieldOver N L), v.DCoordGenerates :=
    original_place_dCoordGenerates N L
  haveI : Nontrivial Ω[modularFunctionFieldOver N L⁄L] :=
    Module.nontrivial_of_finrank_eq_succ (n := 0) (finrank_original_differentials N L)
  apply finite_differential_support_of_finite_coordinate (jOver N L) (transcendental_jOver N L)
  exact (finite_original_divisor_support N L (jOver N L)).subset fun _ hv => ne_of_lt hv

theorem finite_original_differential_support
    {ω : Ω[modularFunctionFieldOver N L⁄L]} (hω : ω ≠ 0) :
    {v : Place L (modularFunctionFieldOver N L) | v.ordDifferential ω ≠ 0}.Finite := by
  haveI : ∀ v : Place L (modularFunctionFieldOver N L), v.DCoordGenerates :=
    original_place_dCoordGenerates N L
  haveI : Nontrivial Ω[modularFunctionFieldOver N L⁄L] :=
    Module.nontrivial_of_finrank_eq_succ (n := 0) (finrank_original_differentials N L)
  have hmem : ω ∈ Submodule.span (modularFunctionFieldOver N L)
      {D L (modularFunctionFieldOver N L) (jOver N L)} := by
    rw [span_D_jOver N L]
    exact Submodule.mem_top
  obtain ⟨c, hcω⟩ := Submodule.mem_span_singleton.mp hmem
  have hc0 : c ≠ 0 := by
    intro h
    apply hω
    rw [← hcω, h, zero_smul]
  have hcoeff : ∀ v : Place L (modularFunctionFieldOver N L),
      v.differentialCoeff (D L (modularFunctionFieldOver N L) (jOver N L)) ≠ 0 := by
    intro v h
    apply D_jOver_ne_zero N L
    rw [← v.differentialCoeff_smul_dCoord (D L (modularFunctionFieldOver N L) (jOver N L)),
      h, zero_smul]
  refine ((finite_original_divisor_support N L c).union (finite_original_D_jOver_support N L)).subset ?_
  intro v hv
  by_cases hc : v.ord c = 0
  · right
    intro hj
    apply hv
    rw [← hcω, v.ordDifferential_smul hc0 (hcoeff v), hc, hj, add_zero]
  · exact Or.inl hc

/-- The actual finite divisor of local orders of a nonzero original differential. -/
def originalCanonicalDivisor {ω : Ω[modularFunctionFieldOver N L⁄L]} (hω : ω ≠ 0) :
    Divisor L (modularFunctionFieldOver N L) :=
  Finsupp.ofSupportFinite (fun v => v.ordDifferential ω) (finite_original_differential_support N L hω)

theorem originalCanonicalDivisor_apply {ω : Ω[modularFunctionFieldOver N L⁄L]} (hω : ω ≠ 0)
    (v : Place L (modularFunctionFieldOver N L)) :
    originalCanonicalDivisor N L hω v = v.ordDifferential ω := rfl

/-- Canonical divisors exist for the literal original modular function field. -/
theorem hasCanonicalDivisor_original :
    HasCanonicalDivisor (K := L) (F := modularFunctionFieldOver N L) :=
  ⟨fun _ hω => ⟨originalCanonicalDivisor N L hω, originalCanonicalDivisor_apply N L hω⟩⟩

end
end Dubon2026.SourceFunctionField

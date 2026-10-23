import Dubon2026.SourceCurveSeparatingDifferentialSupport
import Dubon2026.SourceModularCoefficientLocalDifferentials
import Dubon2026.SourceModularCoefficientDivisorSupport
import Dubon2026.SourceCurveCanonicalDivisor

/-! DUB-17/18 -> actual good reduction -> reverse genus inequality ->
canonical degree. The existing original-field canonical-divisor proof now
applies to the actual residue coefficient field: the proved separating j
coordinate, finite integral local differentials and nonzero spanning local
uniformizer differentials discharge every characteristic-dependent premise.
The finite different-ideal support and rank-one differential reduction are
reused; no canonical-degree or genus identity is claimed here. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve KaehlerDifferential

variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [PerfectField L]

theorem finite_coeff_D_j_support :
    {v : Place L (modularFunctionFieldCoeff N L) |
      v.ordDifferential (D L (modularFunctionFieldCoeff N L) (jCoeff N L)) ≠ 0}.Finite := by
  haveI := isSeparable_coeff_field N L
  haveI : FiniteDimensional (IntermediateField.adjoin L {jCoeff N L})
      (modularFunctionFieldCoeff N L) := finiteDimensional_coeff_field N L
  haveI : ∀ v : Place L (modularFunctionFieldCoeff N L),
      Module.Finite v.toValuationSubring Ω[v.toValuationSubring⁄L] :=
    finite_coeff_place_differentials N L
  haveI : ∀ v : Place L (modularFunctionFieldCoeff N L), Algebra.IsAlgebraic L v.ResidueField :=
    coeff_place_residue_isAlgebraic N L
  haveI : ∀ v : Place L (modularFunctionFieldCoeff N L), Algebra.IsSeparable L v.ResidueField :=
    fun _ => inferInstance
  haveI : ∀ v : Place L (modularFunctionFieldCoeff N L), v.DCoordGenerates :=
    coeff_place_dCoordGenerates N L
  haveI : Nontrivial Ω[modularFunctionFieldCoeff N L⁄L] :=
    Module.nontrivial_of_finrank_eq_succ (n := 0) (finrank_coeff_differentials N L)
  apply finite_differential_support_of_separating_coordinate (jCoeff N L) (transcendental_jCoeff N L)
  exact (finite_coeff_divisor_support N L (jCoeff N L)).subset fun _ hv => ne_of_lt hv

theorem finite_coeff_differential_support
    {ω : Ω[modularFunctionFieldCoeff N L⁄L]} (hω : ω ≠ 0) :
    {v : Place L (modularFunctionFieldCoeff N L) | v.ordDifferential ω ≠ 0}.Finite := by
  haveI : ∀ v : Place L (modularFunctionFieldCoeff N L), v.DCoordGenerates :=
    coeff_place_dCoordGenerates N L
  haveI : Nontrivial Ω[modularFunctionFieldCoeff N L⁄L] :=
    Module.nontrivial_of_finrank_eq_succ (n := 0) (finrank_coeff_differentials N L)
  have hmem : ω ∈ Submodule.span (modularFunctionFieldCoeff N L)
      {D L (modularFunctionFieldCoeff N L) (jCoeff N L)} := by
    rw [span_D_jCoeff N L]
    exact Submodule.mem_top
  obtain ⟨c, hcω⟩ := Submodule.mem_span_singleton.mp hmem
  have hc0 : c ≠ 0 := by
    intro h
    apply hω
    rw [← hcω, h, zero_smul]
  have hcoeff : ∀ v : Place L (modularFunctionFieldCoeff N L),
      v.differentialCoeff (D L (modularFunctionFieldCoeff N L) (jCoeff N L)) ≠ 0 := by
    intro v h
    apply D_jCoeff_ne_zero N L
    rw [← v.differentialCoeff_smul_dCoord (D L (modularFunctionFieldCoeff N L) (jCoeff N L)),
      h, zero_smul]
  refine ((finite_coeff_divisor_support N L c).union (finite_coeff_D_j_support N L)).subset ?_
  intro v hv
  by_cases hc : v.ord c = 0
  · right
    intro hj
    apply hv
    rw [← hcω, v.ordDifferential_smul hc0 (hcoeff v), hc, hj, add_zero]
  · exact Or.inl hc

/-- The actual finite divisor of local orders of a nonzero coefficient-field differential. -/
def coeffCanonicalDivisor {ω : Ω[modularFunctionFieldCoeff N L⁄L]} (hω : ω ≠ 0) :
    Divisor L (modularFunctionFieldCoeff N L) :=
  Finsupp.ofSupportFinite (fun v => v.ordDifferential ω) (finite_coeff_differential_support N L hω)

theorem coeffCanonicalDivisor_apply {ω : Ω[modularFunctionFieldCoeff N L⁄L]} (hω : ω ≠ 0)
    (v : Place L (modularFunctionFieldCoeff N L)) :
    coeffCanonicalDivisor N L hω v = v.ordDifferential ω := rfl

/-- Canonical divisors exist for the literal modular coefficient field. -/
theorem hasCanonicalDivisor_coeff :
    HasCanonicalDivisor (K := L) (F := modularFunctionFieldCoeff N L) :=
  ⟨fun _ hω => ⟨coeffCanonicalDivisor N L hω, coeffCanonicalDivisor_apply N L hω⟩⟩

end
end Dubon2026.SourceFunctionField

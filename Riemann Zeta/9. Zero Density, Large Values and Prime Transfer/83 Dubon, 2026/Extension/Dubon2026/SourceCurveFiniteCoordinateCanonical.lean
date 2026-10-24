import Dubon2026.SourceCurveFiniteCoordinateGeometry
import Dubon2026.SourceCurveDifferentialSupport
import Dubon2026.SourceCurveSeparatingFunctionSupport
import Dubon2026.SourceCurveRegularComparison

/-! DUB-17/18 -> Picard torsion injectivity -> unramified Kummer-cover
genus -> canonical degree. Finite coordinates and the actual nonzero
coordinate differential discharge finite support of every canonical divisor.
The local finiteness argument and rank-one comparison are existing proofs;
no Riemann--Roch or genus identity is assumed or asserted here. -/
namespace Dubon2026.SourceCurve
noncomputable section
open IntermediateField KaehlerDifferential
variable {K F : Type*} [Field K] [CharZero K] [IsAlgClosed K]
  [Field F] [Algebra K F]
variable (t : F) [FiniteDimensional K⟮t⟯ F]

theorem finite_coordinate_D_support (ht : Transcendental K t) (hDt : D K F t ≠ 0) :
    {v : Place K F | v.ordDifferential (D K F t) ≠ 0}.Finite := by
  letI : ∀ v : Place K F, Module.Finite v.toValuationSubring Ω[v.toValuationSubring⁄K] :=
    finite_coordinate_place_differentials t
  letI : ∀ v : Place K F, Module.Finite K v.ResidueField :=
    finite_coordinate_place_residue t
  letI : ∀ v : Place K F, Algebra.IsSeparable K v.ResidueField := fun _ => inferInstance
  letI : ∀ v : Place K F, v.DCoordGenerates := finite_coordinate_place_dCoordGenerates t
  letI : Nontrivial Ω[F⁄K] := nontrivial_of_ne _ _ hDt
  apply finite_differential_support_of_finite_coordinate t ht
  exact (finite_function_support_of_separating_coordinate t ht t).subset fun _ hv => ne_of_lt hv

theorem finite_coordinate_differential_support
    (ht : Transcendental K t) (hDt : D K F t ≠ 0) {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    {v : Place K F | v.ordDifferential ω ≠ 0}.Finite := by
  letI := isCurveOver_finite_coordinate t ht hDt
  letI : ∀ v : Place K F, v.DCoordGenerates := finite_coordinate_place_dCoordGenerates t
  letI : Nontrivial Ω[F⁄K] := nontrivial_of_ne _ _ hDt
  obtain ⟨c, hcω⟩ := RegularDifferentialsComparison.exists_smul_eq hDt ω
  have hc0 : c ≠ 0 := by
    intro hc
    apply hω
    rw [← hcω, hc, zero_smul]
  refine ((finite_function_support_of_separating_coordinate t ht c).union
    (finite_coordinate_D_support t ht hDt)).subset ?_
  intro v hv
  by_cases hc : v.ord c = 0
  · right
    intro hj
    apply hv
    rw [← hcω, v.ordDifferential_smul hc0
      (RegularDifferentialsComparison.differentialCoeff_ne_zero hDt v), hc, hj, add_zero]
  · exact Or.inl hc

theorem hasCanonicalDivisor_finite_coordinate
    (ht : Transcendental K t) (hDt : D K F t ≠ 0) :
    HasCanonicalDivisor (K := K) (F := F) := by
  refine ⟨fun ω hω => ?_⟩
  exact ⟨Finsupp.ofSupportFinite (fun v => v.ordDifferential ω)
    (finite_coordinate_differential_support t ht hDt hω), fun _ => rfl⟩

end
end Dubon2026.SourceCurve

import Dubon2026.SourceOriginalWeilCoverChartDerivativeGerms

/-! DUB-17/18 -> auxiliary Abel comparison -> actual differential readings.
Adapt the existing original-curve residue-germ derivation argument to the
literal Kummer splitting field and its constructed uniformizer charts.
The local spanning and field-reading inputs are proved for this actual cover.
The original derivation proof was adapted from anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_exists_isPrimitiveAlong_of_mem_regularDifferentials.
-/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Filter KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (r : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C r : Polynomial FF)
variable (A : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hr : r ≠ 0)
variable (hrA : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord r = (n : ℤ) * A v)
include A hr hrA

/-- The cover field acts on chart germs by its proved residue germ map. -/
abbrev chartGermAlgebra (v : Place ℂ (EE)) :
    Algebra (EE) (Germ (𝓝[≠] (0 : ℂ)) ℂ) :=
  (chartReadHom N n r A hr hrA v).toAlgebra

theorem chartGerm_smul (v : Place ℂ (EE))
    (f : EE) (m : Germ (𝓝[≠] (0 : ℂ)) ℂ) :
    letI := chartGermAlgebra N n r A hr hrA v
    letI : SMul (EE) (Germ (𝓝[≠] (0 : ℂ)) ℂ) :=
      (chartGermAlgebra N n r A hr hrA v).toSMul
    letI : Module (EE) (Germ (𝓝[≠] (0 : ℂ)) ℂ) :=
      @Algebra.toModule _ _ _ _ (chartGermAlgebra N n r A hr hrA v)
    f • m = chartReadHom N n r A hr hrA v f * m := rfl

theorem chartGerm_scalarTower (v : Place ℂ (EE)) :
    letI := chartGermAlgebra N n r A hr hrA v
    letI : SMul (EE) (Germ (𝓝[≠] (0 : ℂ)) ℂ) :=
      (chartGermAlgebra N n r A hr hrA v).toSMul
    letI : Module (EE) (Germ (𝓝[≠] (0 : ℂ)) ℂ) :=
      @Algebra.toModule _ _ _ _ (chartGermAlgebra N n r A hr hrA v)
    IsScalarTower ℂ (EE) (Germ (𝓝[≠] (0 : ℂ)) ℂ) := by
  letI := chartGermAlgebra N n r A hr hrA v
  letI : SMul (EE) (Germ (𝓝[≠] (0 : ℂ)) ℂ) :=
    (chartGermAlgebra N n r A hr hrA v).toSMul
  letI : Module (EE) (Germ (𝓝[≠] (0 : ℂ)) ℂ) :=
    @Algebra.toModule _ _ _ _ (chartGermAlgebra N n r A hr hrA v)
  refine ⟨fun c f m => ?_⟩
  refine Germ.inductionOn m fun f => ?_
  rw [chartGerm_smul, chartGerm_smul, Algebra.smul_def, map_mul,
    chartReadHom_apply, chartRead_algebraMap, chartReadHom_apply]
  apply Germ.coe_eq.mpr
  exact Eventually.of_forall fun z => mul_assoc c _ _

/-- Analytic differentiation of the actual cover chart germs. -/
def chartReadDerivation (v : Place ℂ (EE)) :
    letI := chartGermAlgebra N n r A hr hrA v
    letI : SMul (EE) (Germ (𝓝[≠] (0 : ℂ)) ℂ) :=
      (chartGermAlgebra N n r A hr hrA v).toSMul
    letI : Module (EE) (Germ (𝓝[≠] (0 : ℂ)) ℂ) :=
      @Algebra.toModule _ _ _ _ (chartGermAlgebra N n r A hr hrA v)
    Derivation ℂ (EE) (Germ (𝓝[≠] (0 : ℂ)) ℂ) := by
  letI := chartGermAlgebra N n r A hr hrA v
  letI : SMul (EE) (Germ (𝓝[≠] (0 : ℂ)) ℂ) :=
    (chartGermAlgebra N n r A hr hrA v).toSMul
  letI : Module (EE) (Germ (𝓝[≠] (0 : ℂ)) ℂ) :=
    @Algebra.toModule _ _ _ _ (chartGermAlgebra N n r A hr hrA v)
  exact {
    toFun := fun f => (deriv (chartRead N n r A hr hrA v f) : Germ (𝓝[≠] (0 : ℂ)) ℂ)
    map_add' := fun f g => by
      rw [← Germ.coe_add]
      exact Germ.coe_eq.mpr (deriv_chartRead_add N n r A hr hrA v f g)
    map_smul' := fun c f => by
      rw [RingHom.id_apply, ← Germ.coe_smul]
      exact Germ.coe_eq.mpr (deriv_chartRead_smul N n r A hr hrA v c f)
    map_one_eq_zero' := by
      change (deriv (chartRead N n r A hr hrA v 1) : Germ (𝓝[≠] (0 : ℂ)) ℂ) = 0
      rw [deriv_chartRead_one, Germ.coe_zero]
    leibniz' := fun f g => by
      change (deriv (chartRead N n r A hr hrA v (f * g)) : Germ (𝓝[≠] (0 : ℂ)) ℂ) =
        f • (deriv (chartRead N n r A hr hrA v g) : Germ (𝓝[≠] (0 : ℂ)) ℂ) +
          g • (deriv (chartRead N n r A hr hrA v f) : Germ (𝓝[≠] (0 : ℂ)) ℂ)
      rw [chartGerm_smul, chartGerm_smul, chartReadHom_apply, chartReadHom_apply,
        ← Germ.coe_mul, ← Germ.coe_mul, ← Germ.coe_add]
      apply Germ.coe_eq.mpr
      filter_upwards [deriv_chartRead_mul N n r A hr hrA v f g] with z hz
      rw [hz]
      simp only [Pi.add_apply, Pi.mul_apply]
      ring }

theorem chartReadDerivation_apply (v : Place ℂ (EE))
    (f : EE) :
    chartReadDerivation N n r A hr hrA v f = (deriv (chartRead N n r A hr hrA v f) : Germ (𝓝[≠] (0 : ℂ)) ℂ) := rfl

theorem chartReadDerivation_lift_smul_D (v : Place ℂ (EE))
    (h g : EE) :
    letI := chartGermAlgebra N n r A hr hrA v
    letI : SMul (EE) (Germ (𝓝[≠] (0 : ℂ)) ℂ) :=
      (chartGermAlgebra N n r A hr hrA v).toSMul
    letI : Module (EE) (Germ (𝓝[≠] (0 : ℂ)) ℂ) :=
      @Algebra.toModule _ _ _ _ (chartGermAlgebra N n r A hr hrA v)
    letI := chartGerm_scalarTower N n r A hr hrA v
    (chartReadDerivation N n r A hr hrA v).liftKaehlerDifferential (h • D ℂ (EE) g) =
      (chartRead N n r A hr hrA v h * deriv (chartRead N n r A hr hrA v g) : Germ (𝓝[≠] (0 : ℂ)) ℂ) := by
  letI := chartGermAlgebra N n r A hr hrA v
  letI : SMul (EE) (Germ (𝓝[≠] (0 : ℂ)) ℂ) :=
    (chartGermAlgebra N n r A hr hrA v).toSMul
  letI : Module (EE) (Germ (𝓝[≠] (0 : ℂ)) ℂ) :=
    @Algebra.toModule _ _ _ _ (chartGermAlgebra N n r A hr hrA v)
  letI := chartGerm_scalarTower N n r A hr hrA v
  rw [map_smul, Derivation.liftKaehlerDifferential_comp_D, chartReadDerivation_apply,
    chartGerm_smul, chartReadHom_apply]

theorem readDifferential_eq_expression_germ (v : Place ℂ (EE))
    (ω : Ω[EE⁄ℂ]) (h g : EE)
    (he : ω = h • D ℂ (EE) g) :
    readDifferential N n r A hr hrA v ω =ᶠ[𝓝[≠] (0 : ℂ)]
      chartRead N n r A hr hrA v h * deriv (chartRead N n r A hr hrA v g) := by
  letI := chartGermAlgebra N n r A hr hrA v
  letI : SMul (EE) (Germ (𝓝[≠] (0 : ℂ)) ℂ) :=
    (chartGermAlgebra N n r A hr hrA v).toSMul
  letI : Module (EE) (Germ (𝓝[≠] (0 : ℂ)) ℂ) :=
    @Algebra.toModule _ _ _ _ (chartGermAlgebra N n r A hr hrA v)
  letI := chartGerm_scalarTower N n r A hr hrA v
  haveI := cover_place_dCoordGenerates N n r v
  have he' : ω = v.differentialCoeff ω • D ℂ (EE) v.uniformizer :=
    (v.differentialCoeff_smul_dCoord ω).symm
  have h1 := chartReadDerivation_lift_smul_D N n r A hr hrA v (v.differentialCoeff ω) v.uniformizer
  have h2 := chartReadDerivation_lift_smul_D N n r A hr hrA v h g
  rw [← he'] at h1
  rw [← he] at h2
  exact Germ.coe_eq.mp (h1.symm.trans h2)

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart

import Dubon2026.SourceOriginalPathIntegralLaws
import Dubon2026.SourceOriginalComplexConnected

/-! DUB-17/18 -> original torsion cardinality -> complex Abel-Jacobi.
Connectedness and the native local path connectedness of the constructed
complex charts give actual paths between all original places. Integrating
original regular differentials defines the Abel-Jacobi vector and divisor
map. Their path ambiguity lies in the integer span of actual loop periods.
No path existence, integral law or period membership is supplied as an
assumption. Discreteness, full real span and the principal-divisor kernel
remain distinct obligations before the torsion comparison can apply.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
Definitions/Def_AlgebraicCurve_ComplexLineIntegral and
S_AlgebraicCurve_exists_ball_abelJacobiVec_sub_sub_mem_pathPeriodLattice.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Set KaehlerDifferential
variable (N : ℕ) [NeZero N]
attribute [local instance] placeTopology

theorem place_pathConnectedSpace : PathConnectedSpace (Place ℂ (modularFunctionFieldOver N ℂ)) := by
  letI := placeChartedSpace N
  letI := place_connectedSpace N
  letI := ChartedSpace.locPathConnectedSpace ℂ (Place ℂ (modularFunctionFieldOver N ℂ))
  exact PathConnectedSpace.of_locPathConnectedSpace

/-- An actual continuous path between original places, using proved path connectedness. -/
def originalPath (P Q : Place ℂ (modularFunctionFieldOver N ℂ)) : Path P Q := by
  letI := place_pathConnectedSpace N
  exact PathConnectedSpace.somePath P Q

/-- Integrals of the given original differentials along one actual chosen path. -/
def abelJacobiVec {n : ℕ} (b : Fin n → Ω[modularFunctionFieldOver N ℂ⁄ℂ])
    (P₀ P : Place ℂ (modularFunctionFieldOver N ℂ)) : Fin n → ℂ :=
  fun i => pathIntegral N (b i) (originalPath N P₀ P)

/-- Additive extension of the actual Abel-Jacobi point vectors to original divisors. -/
def abelJacobiDiv {n : ℕ} (b : Fin n → Ω[modularFunctionFieldOver N ℂ⁄ℂ])
    (P₀ : Place ℂ (modularFunctionFieldOver N ℂ)) :
    Divisor ℂ (modularFunctionFieldOver N ℂ) →+ (Fin n → ℂ) :=
  Finsupp.liftAddHom fun v => zmultiplesHom (Fin n → ℂ) (abelJacobiVec N b P₀ v)

theorem abelJacobiDiv_single {n : ℕ} (b : Fin n → Ω[modularFunctionFieldOver N ℂ⁄ℂ])
    (P₀ v : Place ℂ (modularFunctionFieldOver N ℂ)) (m : ℤ) :
    abelJacobiDiv N b P₀ (Finsupp.single v m) = m • abelJacobiVec N b P₀ v := by
  simp [abelJacobiDiv]

theorem abelJacobiDiv_apply {n : ℕ} (b : Fin n → Ω[modularFunctionFieldOver N ℂ⁄ℂ])
    (P₀ : Place ℂ (modularFunctionFieldOver N ℂ))
    (D : Divisor ℂ (modularFunctionFieldOver N ℂ)) :
    abelJacobiDiv N b P₀ D = D.sum fun v m => m • abelJacobiVec N b P₀ v := by
  simp only [abelJacobiDiv, Finsupp.liftAddHom_apply]
  rfl

/-- The integer span of periods over actual continuous loops on the original curve. -/
def pathPeriodLattice {n : ℕ} (b : Fin n → Ω[modularFunctionFieldOver N ℂ⁄ℂ]) :
    Submodule ℤ (Fin n → ℂ) :=
  Submodule.span ℤ {u | ∃ (P : Place ℂ (modularFunctionFieldOver N ℂ)) (γ : Path P P),
    u = fun i => pathIntegral N (b i) γ}

theorem mem_pathPeriodLattice_of_loop {n : ℕ} (b : Fin n → Ω[modularFunctionFieldOver N ℂ⁄ℂ])
    {P : Place ℂ (modularFunctionFieldOver N ℂ)} (γ : Path P P) :
    (fun i => pathIntegral N (b i) γ) ∈ pathPeriodLattice N b :=
  Submodule.subset_span ⟨P, γ, rfl⟩

theorem abelJacobiVec_sub_mem {n : ℕ} (b : Fin n → Ω[modularFunctionFieldOver N ℂ⁄ℂ])
    (hb : ∀ i, b i ∈ regularDifferentials ℂ (modularFunctionFieldOver N ℂ))
    {P₀ P : Place ℂ (modularFunctionFieldOver N ℂ)} (γ : Path P₀ P) :
    abelJacobiVec N b P₀ P - (fun i => pathIntegral N (b i) γ) ∈ pathPeriodLattice N b := by
  have hloop := mem_pathPeriodLattice_of_loop N b ((originalPath N P₀ P).trans γ.symm)
  convert hloop using 1
  funext i
  simp only [abelJacobiVec, Pi.sub_apply, pathIntegral_trans N (hb i),
    pathIntegral_symm N (hb i)]
  ring

end
end Dubon2026.SourceFunctionField.OriginalChart

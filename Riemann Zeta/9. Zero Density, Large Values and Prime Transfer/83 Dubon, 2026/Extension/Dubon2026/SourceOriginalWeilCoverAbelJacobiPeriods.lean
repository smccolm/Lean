import Dubon2026.SourceOriginalWeilCoverPathIntegralLaws
import Dubon2026.SourceOriginalWeilCoverConnected

/-! DUB-17/18 -> auxiliary point division -> cover Abel comparison.
The native original-curve path and local Abel arguments are adapted to the
literal Kummer splitting field and its constructed complex manifold.
All path and primitive inputs are proved; Abel inversion and its principal
kernel remain required. Adapted from anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
Def_AlgebraicCurve_ComplexLineIntegral and
S_AlgebraicCurve_exists_ball_abelJacobiVec_sub_sub_mem_pathPeriodLattice.
-/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Set KaehlerDifferential
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (r : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C r : Polynomial FF)
variable (A : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hr : r ≠ 0)
variable (hrA : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord r = (n : ℤ) * A v)
include A hr hrA
local notation "CoverPath" => @Path (Place ℂ EE) (placeTopology N n r A hr hrA)

theorem place_pathConnectedSpace :
    letI := placeTopology N n r A hr hrA
    PathConnectedSpace (Place ℂ EE) := by
  letI := placeTopology N n r A hr hrA
  letI := placeChartedSpace N n r A hr hrA
  letI := place_connectedSpace N n r A hr hrA
  letI := ChartedSpace.locPathConnectedSpace ℂ (Place ℂ (EE))
  exact PathConnectedSpace.of_locPathConnectedSpace

/-- An actual continuous path between actual cover places, using proved path connectedness. -/
def coverPath (P Q : Place ℂ (EE)) : CoverPath P Q := by
  letI := placeTopology N n r A hr hrA
  letI := place_pathConnectedSpace N n r A hr hrA
  exact PathConnectedSpace.somePath P Q

/-- Integrals of the given cover differentials along one actual chosen path. -/
def abelJacobiVec {k : ℕ} (b : Fin k → Ω[EE⁄ℂ])
    (P₀ P : Place ℂ (EE)) : Fin k → ℂ :=
  fun i => pathIntegral N n r A hr hrA (b i) (coverPath N n r A hr hrA P₀ P)

/-- Additive extension of the actual Abel-Jacobi point vectors to cover divisors. -/
def abelJacobiDiv {k : ℕ} (b : Fin k → Ω[EE⁄ℂ])
    (P₀ : Place ℂ (EE)) :
    Divisor ℂ (EE) →+ (Fin k → ℂ) :=
  Finsupp.liftAddHom fun v => zmultiplesHom (Fin k → ℂ) (abelJacobiVec N n r A hr hrA b P₀ v)

theorem abelJacobiDiv_single {k : ℕ} (b : Fin k → Ω[EE⁄ℂ])
    (P₀ v : Place ℂ (EE)) (m : ℤ) :
    abelJacobiDiv N n r A hr hrA b P₀ (Finsupp.single v m) = m • abelJacobiVec N n r A hr hrA b P₀ v := by
  letI := placeTopology N n r A hr hrA
  simp [abelJacobiDiv]

/-- The integer span of periods over actual continuous loops on the actual cover. -/
def pathPeriodLattice {k : ℕ} (b : Fin k → Ω[EE⁄ℂ]) :
    Submodule ℤ (Fin k → ℂ) :=
  Submodule.span ℤ {u | ∃ (P : Place ℂ (EE)) (γ : CoverPath P P),
    u = fun i => pathIntegral N n r A hr hrA (b i) γ}

theorem mem_pathPeriodLattice_of_loop {k : ℕ} (b : Fin k → Ω[EE⁄ℂ])
    {P : Place ℂ (EE)} (γ : CoverPath P P) :
    (fun i => pathIntegral N n r A hr hrA (b i) γ) ∈ pathPeriodLattice N n r A hr hrA b :=
  Submodule.subset_span ⟨P, γ, rfl⟩

theorem abelJacobiVec_sub_mem {k : ℕ} (b : Fin k → Ω[EE⁄ℂ])
    (hb : ∀ i, b i ∈ regularDifferentials ℂ (EE))
    {P₀ P : Place ℂ (EE)} (γ : CoverPath P₀ P) :
    abelJacobiVec N n r A hr hrA b P₀ P - (fun i => pathIntegral N n r A hr hrA (b i) γ) ∈ pathPeriodLattice N n r A hr hrA b := by
  letI := placeTopology N n r A hr hrA
  have hloop := mem_pathPeriodLattice_of_loop N n r A hr hrA b ((coverPath N n r A hr hrA P₀ P).trans γ.symm)
  convert hloop using 1
  funext i
  simp only [abelJacobiVec, Pi.sub_apply, pathIntegral_trans N n r A hr hrA (hb i),
    pathIntegral_symm N n r A hr hrA (hb i)]
  ring

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart

import Dubon2026.SourceOriginalWeilCoverChartPathIntegrals

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
open SourceCurve Set Metric KaehlerDifferential
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (r : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C r : Polynomial FF)
variable (A : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hr : r ≠ 0)
variable (hrA : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord r = (n : ℤ) * A v)
include A hr hrA
local notation "CoverPath" => @Path (Place ℂ EE) (placeTopology N n r A hr hrA)

theorem abelJacobiVec_chart_primitive {k : ℕ}
    (b : Fin k → Ω[EE⁄ℂ])
    (hb : ∀ i, b i ∈ regularDifferentials ℂ (EE))
    (P₀ v : Place ℂ (EE)) (Φ : Fin k → ℂ → ℂ)
    (hΦ : ∀ i, ∀ z ∈ ball (0 : ℂ) (placeRadius N n r A hr hrA v),
      HasDerivAt (Φ i) (readDifferential N n r A hr hrA v (b i) z) z)
    {z : ℂ} (hz : z ∈ ball 0 (placeRadius N n r A hr hrA v)) :
    abelJacobiVec N n r A hr hrA b P₀ (placeFamily N n r A hr hrA v z) - abelJacobiVec N n r A hr hrA b P₀ v -
      (fun i => Φ i z - Φ i 0) ∈ pathPeriodLattice N n r A hr hrA b := by
  letI := placeTopology N n r A hr hrA
  obtain ⟨γ, hγ⟩ := exists_cover_chart_path_integrals N n r A hr hrA b hb v Φ hΦ hz
  have hm := abelJacobiVec_sub_mem N n r A hr hrA b hb ((coverPath N n r A hr hrA P₀ v).trans γ)
  convert hm using 1
  funext i
  simp only [Pi.sub_apply, pathIntegral_trans N n r A hr hrA (hb i), hγ i, abelJacobiVec]
  ring

theorem exists_abelJacobiVec_chart_primitive {k : ℕ}
    (b : Fin k → Ω[EE⁄ℂ])
    (hb : ∀ i, b i ∈ regularDifferentials ℂ (EE))
    (P₀ v : Place ℂ (EE)) :
    ∃ Φ : Fin k → ℂ → ℂ,
      (∀ i, ∀ z ∈ ball (0 : ℂ) (placeRadius N n r A hr hrA v),
        HasDerivAt (Φ i) (readDifferential N n r A hr hrA v (b i) z) z) ∧
      ∀ z ∈ ball (0 : ℂ) (placeRadius N n r A hr hrA v),
        abelJacobiVec N n r A hr hrA b P₀ (placeFamily N n r A hr hrA v z) - abelJacobiVec N n r A hr hrA b P₀ v -
          (fun i => Φ i z - Φ i 0) ∈ pathPeriodLattice N n r A hr hrA b := by
  letI := placeTopology N n r A hr hrA
  choose Φ hΦ using fun i => exists_readDifferential_primitive_on_chart N n r A hr hrA v (b i) (hb i)
  exact ⟨Φ, hΦ, fun z hz => abelJacobiVec_chart_primitive N n r A hr hrA b hb P₀ v Φ hΦ hz⟩

theorem abelJacobiDiv_chart_difference {k : ℕ}
    (b : Fin k → Ω[EE⁄ℂ])
    (hb : ∀ i, b i ∈ regularDifferentials ℂ EE)
    (P₀ v : Place ℂ EE) :
    ∃ Φ : Fin k → ℂ → ℂ,
      (∀ i, ∀ z ∈ ball (0 : ℂ) (placeRadius N n r A hr hrA v),
        HasDerivAt (Φ i) (readDifferential N n r A hr hrA v (b i) z) z) ∧
      ∀ z ∈ ball (0 : ℂ) (placeRadius N n r A hr hrA v),
        abelJacobiDiv N n r A hr hrA b P₀
          (Finsupp.single (placeFamily N n r A hr hrA v z) 1 - Finsupp.single v 1) -
          (fun i => Φ i z - Φ i 0) ∈ pathPeriodLattice N n r A hr hrA b := by
  obtain ⟨Φ, hΦ, hlocal⟩ := exists_abelJacobiVec_chart_primitive N n r A hr hrA b hb P₀ v
  refine ⟨Φ, hΦ, fun z hz => ?_⟩
  simpa only [map_sub, abelJacobiDiv_single, one_zsmul] using hlocal z hz

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart

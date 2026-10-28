import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_ComplexLineIntegral
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_exists_abelJacobiDiv_sub_mem_pathPeriodLattice_and_image_mem_nhds

open AlgebraicCurve
open scoped Manifold ContDiff Topology

theorem AlgebraicCurve.exists_abelJacobiDiv_sub_mem_pathPeriodLattice_and_image_mem_nhds
    (F : Type*) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [T2Space (Place ℂ F)] [ConnectedSpace (Place ℂ F)]
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) (hb : ∀ i, b i ∈ regularDifferentials ℂ F)
    (v : Fin n → Place ℂ F)
    (hv : IsUnit (Matrix.det (Matrix.of fun i j : Fin n =>
        (v j).evalAt ((v j).differentialCoeff (b i)))))
    (P₀ : Place ℂ F) :
    ∃ Φ : (Fin n → Place ℂ F) → (Fin n → ℂ), Φ v = 0 ∧
      (∀ U ∈ 𝓝 v, Φ '' U ∈ 𝓝 (0 : Fin n → ℂ)) ∧
      ∀ᶠ P in 𝓝 v,
        abelJacobiDiv b P₀ ((∑ j, Finsupp.single (P j) 1) - ∑ j, Finsupp.single (v j) 1) - Φ P ∈
          pathPeriodLattice b := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_exists_abelJacobiDiv_sub_mem_pathPeriodLattice_and_image_mem_nhds.solution

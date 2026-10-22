import Dubon2026.SourceOriginalArcPathIntegral
import Dubon2026.SourceOriginalDissectionEdgePaths
import Dubon2026.SourceOriginalRegularPathIntegralLaws

/-! DUB-17/18 -> original Abel-Jacobi -> actual fundamental-cycle loops.
Transfer the proved arc identity to the dissection's actual oriented edges.
Regularity on its skeleton supplies primitives for every path used below.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.OriginalEdgePaths
noncomputable section
open SourceCurve Set KaehlerDifferential OriginalChart CellDissection
attribute [local instance] placeTopology placeChartedSpace
variable {N : ℕ} [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem pathIntegral_edgePath (D : CellDissection N) (e : D.ιE) {θ : Ω[F⁄ℂ]}
    (hθ : ∀ s ∈ (D.cell (D.arcOf (e, true)).1).R.arcIcc (D.arcOf (e, true)).2,
      0 ≤ ((D.cell (D.arcOf (e, true)).1).bdry s).ordDifferential θ) :
    (∃ g, IsPrimitiveAlong N θ (edgePath D e) g) ∧
      pathIntegral N θ (edgePath D e) = D.edgeInt θ e := by
  obtain ⟨⟨g, hg⟩, hi⟩ := pathIntegral_arcPath (D.cell (D.arcOf (e, true)).1)
    (D.arcOf (e, true)).2 hθ
  exact ⟨⟨g, hg⟩, hi⟩

theorem edgePath_mem_skeleton (D : CellDissection N) (e : D.ιE) (t : unitInterval) :
    edgePath D e t ∈ D.skeleton :=
  mem_iUnion.2 ⟨D.arcOf (e, true), edgePath_mem_arc D e t⟩

theorem vert_mem_skeleton (D : CellDissection N) (e : D.ιE) :
    D.vert (D.ends e).1 ∈ D.skeleton ∧ D.vert (D.ends e).2 ∈ D.skeleton := by
  constructor
  · rw [← (edgePath D e).source]; exact edgePath_mem_skeleton D e 0
  · rw [← (edgePath D e).target]; exact edgePath_mem_skeleton D e 1

/-- Nonnegative differential order at every actual point of the dissection skeleton. -/
def RegOnSkeleton (D : CellDissection N) (θ : Ω[F⁄ℂ]) : Prop :=
  ∀ x ∈ D.skeleton, 0 ≤ x.ordDifferential θ

theorem pathIntegral_cast {θ : Ω[F⁄ℂ]} {P Q P' Q' : Place ℂ F} (γ : Path P Q)
    (hP : P' = P) (hQ : Q' = Q) :
    pathIntegral N θ (γ.cast hP hQ) = pathIntegral N θ γ := by
  subst hP; subst hQ; rfl

theorem mem_skeleton_trans (D : CellDissection N) {P Q R : Place ℂ F}
    {γ : Path P Q} {δ : Path Q R}
    (hγ : ∀ t, γ t ∈ D.skeleton) (hδ : ∀ t, δ t ∈ D.skeleton) :
    ∀ t, (γ.trans δ) t ∈ D.skeleton := by
  intro t
  rw [Path.trans_apply]
  split_ifs
  · exact hγ _
  · exact hδ _

theorem primitive_on_skeleton (D : CellDissection N) {θ : Ω[F⁄ℂ]}
    {P Q : Place ℂ F} {γ : Path P Q} (hθ : RegOnSkeleton D θ)
    (hγ : ∀ t, γ t ∈ D.skeleton) : ∃ g, IsPrimitiveAlong N θ γ g :=
  exists_isPrimitiveAlong_of_coeff_mem N θ γ
    (fun t => (γ t).mem_of_ord_nonneg (hθ _ (hγ t)))

theorem pathIntegral_trans_on_skeleton (D : CellDissection N) {θ : Ω[F⁄ℂ]}
    {P Q R : Place ℂ F} (γ : Path P Q) (δ : Path Q R) (hθ : RegOnSkeleton D θ)
    (hγ : ∀ t, γ t ∈ D.skeleton) (hδ : ∀ t, δ t ∈ D.skeleton) :
    pathIntegral N θ (γ.trans δ) = pathIntegral N θ γ + pathIntegral N θ δ :=
  pathIntegral_trans_of_coeff_mem N γ δ
    (fun t => (γ t).mem_of_ord_nonneg (hθ _ (hγ t)))
    (fun t => (δ t).mem_of_ord_nonneg (hθ _ (hδ t)))

end
end Dubon2026.SourceFunctionField.CellGeometry.OriginalEdgePaths

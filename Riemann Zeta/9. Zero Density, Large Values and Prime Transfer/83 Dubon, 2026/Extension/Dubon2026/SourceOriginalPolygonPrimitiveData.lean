import Dubon2026.SourceOriginalCellPrimitiveArcIntegral
import Dubon2026.SourceOriginalConstructedJumpReduction

/-! DUB-17/18 -> original Abel-Jacobi -> polygon-word jump formula.
Local analytic primitive data and their actual endpoint readings are the
inputs to the polygon telescoping theorem. Their existence is proved by the
preceding normalized original-cell consumer; these definitions alone assert
no existence, period generation or reciprocity theorem.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.DissectionPeriods
noncomputable section
open SourceCurve Set KaehlerDifferential CellDissection
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] {κ : Type*}
local notation "F" => modularFunctionFieldOver N ℂ

/-- Analytic primitives for an actual original regular differential family on cell neighborhoods. -/
structure PrimData (D : CellDissection N) (η : κ → Ω[F⁄ℂ]) (V : D.ιC → Set ℂ)
    (Ψ : κ → D.ιC → ℂ → ℂ) : Prop where
  hVo : ∀ C, IsOpen (V C)
  hKV : ∀ C, (D.cell C).R.K ⊆ V C
  hVt : ∀ C, V C ⊆ (D.cell C).ζ.target
  hΨ : ∀ i C, ∀ w ∈ V C, HasDerivAt (Ψ i C) (coeffIn (D.cell C).ζ (η i) w) w
  hη : ∀ i (Q : Place ℂ F), 0 ≤ Q.ordDifferential (η i)

/-- The actual primitive difference on every point of each positively oriented arc. -/
def IsJump (D : CellDissection N) (Ψ : κ → D.ιC → ℂ → ℂ) (J : D.ιE → κ → ℂ) : Prop :=
  ∀ i e, ∀ s ∈ (D.cell (D.arcOf (e, true)).1).R.arcIcc (D.arcOf (e, true)).2,
    Ψ i (D.arcOf (e, true)).1 ((D.cell (D.arcOf (e, true)).1).R.loop s) -
      Ψ i (D.arcOf (e, false)).1
        ((D.cell (D.arcOf (e, false)).1).ζ ((D.cell (D.arcOf (e, true)).1).bdry s)) = J e i

/-- Primitive values at an actual original place in a specified cell chart. -/
noncomputable def gvec (D : CellDissection N) (Ψ : κ → D.ιC → ℂ → ℂ)
    (y : Place ℂ F) (C : D.ιC) : κ → ℂ := fun i => Ψ i C ((D.cell C).ζ y)

/-- Primitive values at the starting point of an actual oriented arc. -/
noncomputable def Avec (D : CellDissection N) (Ψ : κ → D.ιC → ℂ → ℂ) (q : D.ιE × Bool) :
    κ → ℂ := fun i => Ψ i (D.arcOf q).1
      ((D.cell (D.arcOf q).1).R.loop ((D.cell (D.arcOf q).1).R.φs (D.arcOf q).2.castSucc))

/-- Primitive values at the final point of an actual oriented arc. -/
noncomputable def Bvec (D : CellDissection N) (Ψ : κ → D.ιC → ℂ → ℂ) (q : D.ιE × Bool) :
    κ → ℂ := fun i => Ψ i (D.arcOf q).1
      ((D.cell (D.arcOf q).1).R.loop ((D.cell (D.arcOf q).1).R.φs (D.arcOf q).2.succ))

/-- The actual positive edge integrals of the original differential family. -/
noncomputable def Ivec (D : CellDissection N) (η : κ → Ω[F⁄ℂ]) (e : D.ιE) : κ → ℂ :=
  fun i => D.edgeInt (η i) e

end
end Dubon2026.SourceFunctionField.CellGeometry.DissectionPeriods

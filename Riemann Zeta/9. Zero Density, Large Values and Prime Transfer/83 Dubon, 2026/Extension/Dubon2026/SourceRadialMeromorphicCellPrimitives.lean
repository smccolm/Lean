import Dubon2026.SourceRadialMeromorphicPoleNeighborhoods
import Dubon2026.SourceCellRadialPrimitive

/-! DUB-17/18 -> cover Abel converse -> meromorphic loop generation.
Apply the proved radial primitive theorem to the residue-subtracted analytic
coefficient on a common neighborhood excluding other marked poles. -/
namespace Dubon2026.SourceFunctionField.CellGeometry.RadialMeromorphicPeriods
noncomputable section
open Set
variable {X R : Type*} [TopologicalSpace X]

/-- Analytic primitives on common pole-excluded radial cell neighborhoods. -/
structure RegPrimData (D : RadialCellDissection X) (S : Finset X)
    (f : R → D.ιC → ℂ → ℂ) (V : D.ιC → Set ℂ) (Ψ : R → D.ιC → ℂ → ℂ) : Prop where
  hVo : ∀ C, IsOpen (V C)
  hVstar : ∀ C, StarConvex ℝ (D.cell C).R.q (V C)
  hKV : ∀ C, (D.cell C).R.K ⊆ V C
  hVgood : ∀ C, V C ⊆ goodSet (S := S) C
  hΨ : ∀ r C, ∀ w ∈ V C, HasDerivAt (Ψ r C) (f r C w) w

theorem exists_regPrimData (D : RadialCellDissection X) (S : Finset X)
    (f : R → D.ιC → ℂ → ℂ) (hS : PolePos D S)
    (hf : ∀ r C, ∀ w ∈ goodSet (S := S) C, AnalyticAt ℂ (f r C) w) :
    ∃ (V : D.ιC → Set ℂ) (Ψ : R → D.ιC → ℂ → ℂ), RegPrimData D S f V Ψ := by
  have hcell : ∀ C : D.ιC, ∃ (V : Set ℂ) (Ψ : R → ℂ → ℂ), IsOpen V ∧
      StarConvex ℝ (D.cell C).R.q V ∧ (D.cell C).R.K ⊆ V ∧ V ⊆ goodSet (S := S) C ∧
      ∀ r, ∀ w ∈ V, HasDerivAt (Ψ r) (f r C w) w := by
    intro C
    obtain ⟨W, hWo, _, hWstar, hKW, hsub⟩ :=
      (D.cell C).R.exists_open_starConvex_neighborhood _ (isOpen_goodSet C) (K_subset_goodSet hS C)
    have hdiff : ∀ r, DifferentiableOn ℂ (f r C) W :=
      fun r w hw => (hf r C w (hsub hw)).differentiableAt.differentiableWithinAt
    have hprim := fun r => exists_radial_primitive hWo hWstar (hdiff r)
    choose Ψ _ hΨ using hprim
    exact ⟨W, Ψ, hWo, hWstar, hKW, hsub, hΨ⟩
  choose V Ψ hVo hVs hKV hVg hΨ using hcell
  exact ⟨V, fun r C => Ψ C r, ⟨hVo, hVs, hKV, hVg, fun r C => hΨ C r⟩⟩

end
end Dubon2026.SourceFunctionField.CellGeometry.RadialMeromorphicPeriods

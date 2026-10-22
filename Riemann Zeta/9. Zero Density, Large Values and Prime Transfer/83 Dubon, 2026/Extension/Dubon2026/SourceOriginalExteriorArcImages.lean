import Dubon2026.SourceOriginalInteriorArcImages

/-! DUB-17/18 -> original Abel-Jacobi -> actual exterior boundary partners.
The inverse-j power image of each pole arc is a reciprocal base side.
Original evaluation commutes with inversion. This derives regularity of j,
its exact outer-window side image, and injectivity on every pole boundary arc.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.OriginalPoleRegionFamily
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] {W : RadialRegion} (B : OriginalPoleRegionFamily N W)
local notation "F" => modularFunctionFieldOver N ℂ

theorem arc_image (v : originalPositiveFiber N (jOver N ℂ)⁻¹ 0) (a : Fin (B.C v).R.N) :
    (∀ P ∈ (B.C v).arc a, jOver N ℂ ∈ P.toValuationSubring) ∧
    ∃ k : Fin W.N, (fun P => originalPlaceEval N ℂ P (jOver N ℂ)) '' (B.C v).arc a = W.arcSet k ∧
      InjOn (fun P => originalPlaceEval N ℂ P (jOver N ℂ)) ((B.C v).arc a) := by
  have hread (P : Place ℂ F) (hP : P ∈ (B.C v).ζ.source) :
      originalPlaceEval N ℂ P (jOver N ℂ)⁻¹ = B.R.q + (B.C v).ζ P ^
        ((v : Place ℂ F).ord (jOver N ℂ)⁻¹).toNat := by
    rw [B.reciprocal.1, zero_add]
    exact ((B.geometry v).2.2.2 P hP).2
  obtain ⟨k, hk, hinj⟩ := (B.C v).powered_arc_image (B.geometry v).2.2.1 a
    (fun P => originalPlaceEval N ℂ P (jOver N ℂ)⁻¹) hread
  have hr (P : Place ℂ F) (hP : P ∈ (B.C v).arc a) : jOver N ℂ ∈ P.toValuationSubring := by
    have hz : originalPlaceEval N ℂ P (jOver N ℂ)⁻¹ ∈ B.R.arcSet k :=
      hk ▸ mem_image_of_mem (fun P => originalPlaceEval N ℂ P (jOver N ℂ)⁻¹) hP
    obtain ⟨t, _, ht⟩ := hz
    have hne : originalPlaceEval N ℂ P (jOver N ℂ)⁻¹ ≠ 0 := fun h =>
      B.R.loop_ne_center t ((ht.trans h).trans B.reciprocal.1.symm)
    by_contra hreg
    have hjz : originalPlaceEval N ℂ P (jOver N ℂ) = 0 := by
      simp only [originalPlaceEval, dif_neg hreg]
    apply hne
    rw [originalPlaceEval_inv, hjz, inv_zero]
  obtain ⟨σ, _, hσ⟩ := B.reciprocal.2.2.2.2.2.2
  refine ⟨hr, σ.symm k, ?_, ?_⟩
  · calc
      (fun P => originalPlaceEval N ℂ P (jOver N ℂ)) '' (B.C v).arc a =
          (fun P => (originalPlaceEval N ℂ P (jOver N ℂ)⁻¹)⁻¹) '' (B.C v).arc a := by
            apply image_congr
            intro P _
            rw [originalPlaceEval_inv, inv_inv]
      _ = (fun z : ℂ => z⁻¹) '' ((fun P => originalPlaceEval N ℂ P (jOver N ℂ)⁻¹) '' (B.C v).arc a) :=
        (image_image _ _ _).symm
      _ = (fun z : ℂ => z⁻¹) '' B.R.arcSet k := by rw [hk]
      _ = W.arcSet (σ.symm k) := by simpa only [Equiv.apply_symm_apply] using hσ (σ.symm k)
  · intro P hP Q hQ he
    apply hinj hP hQ
    change originalPlaceEval N ℂ P (jOver N ℂ)⁻¹ = originalPlaceEval N ℂ Q (jOver N ℂ)⁻¹
    rw [originalPlaceEval_inv, originalPlaceEval_inv]
    exact congrArg Inv.inv he

end
end Dubon2026.SourceFunctionField.CellGeometry.OriginalPoleRegionFamily

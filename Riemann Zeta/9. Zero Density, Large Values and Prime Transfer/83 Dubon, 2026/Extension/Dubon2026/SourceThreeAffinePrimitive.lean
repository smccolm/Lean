import Dubon2026.SourceCupThreePrimitive
import Dubon2026.SourceThreeFunctionHecke

/-! The actual affine cocycle required for the characteristic-three odd twist.
DUB-17/18 -> residual modular Galois association -> all-prime weight-two
reduction -> characteristic-three odd twist. The proved cup primitive puts
the actual constant cocycle in the image of the coefficient difference.
The sign is matched to the existing original affine action.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup CategoryTheory groupCohomology

variable (F : Type) [Field F] (Q : ℕ) (h3Q : 3 ∣ Q)

/-- The actual constant inclusion applied to a native original trivial cocycle. -/
def sourceThreeConstantCocycle (z : cocycles₁ (Rep.trivial F (Gamma0 Q) F)) :
    cocycles₁ (sourceAffineFunctionRep 3 Q F h3Q) :=
  mapCocycles₁ (MonoidHom.id _) (sourceThreeConstantMap F Q h3Q) z

/-- The actual constant cocycle evaluates to the original trivial cocycle. -/
theorem sourceThreeConstantCocycle_apply (z : cocycles₁ (Rep.trivial F (Gamma0 Q) F))
    (g : Gamma0 Q) (u : ZMod 3) :
    sourceThreeConstantCocycle F Q h3Q z g u = z g := rfl

/-- Native H1 constant inclusion is represented by the actual constant cocycle. -/
theorem sourceThreeConstantH1_cocycle (z : cocycles₁ (Rep.trivial F (Gamma0 Q) F)) :
    sourceThreeConstantH1 F Q h3Q (H1π (Rep.trivial F (Gamma0 Q) F) z) =
      H1π (sourceAffineFunctionRep 3 Q F h3Q) (sourceThreeConstantCocycle F Q h3Q z) := by
  change groupCohomology.map (MonoidHom.id _) (sourceThreeConstantMap F Q h3Q) 1
      (H1π (Rep.trivial F (Gamma0 Q) F) z) =
    H1π (sourceAffineFunctionRep 3 Q F h3Q)
      (mapCocycles₁ (MonoidHom.id _) (sourceThreeConstantMap F Q h3Q) z)
  exact H1π_comp_map_apply (A := Rep.trivial F (Gamma0 Q) F)
    (B := sourceAffineFunctionRep 3 Q F h3Q)
    (MonoidHom.id _) (sourceThreeConstantMap F Q h3Q) z

variable [CharP F 3]

/-- The actual constant native cocycle is in the image of the original
translation difference, with its primitive derived from the original group. -/
theorem sourceThreeConstantCocycle_difference_range
    (z : cocycles₁ (Rep.trivial F (Gamma0 Q) F)) :
    ∃ w : cocycles₁ (sourceAffineFunctionRep 3 Q F h3Q),
      mapCocycles₁ (MonoidHom.id _) (sourceThreeFunctionDifferenceMap F Q h3Q) w =
        sourceThreeConstantCocycle F Q h3Q z := by
  let x : Additive (Gamma0 Q) →+ F :=
    (cocycles₁IsoOfIsTrivial (Rep.trivial F (Gamma0 Q) F)).hom z
  obtain ⟨H, hH⟩ := SourceCupThree.exists_cup_primitive Q h3Q F x
  have hHx (g h : Gamma0 Q) :
      H (g * h) = H g + H h + SourceCupThree.cst F (SourceCupThree.phi Q g) * z h := by
    rw [SourceCupThree.cst_phi]
    exact hH g h
  let wf : Gamma0 Q → ZMod 3 → F :=
    fun g u => -H g + SourceCupThree.cst F u * z g
  have hw : wf ∈ cocycles₁ (sourceAffineFunctionRep 3 Q F h3Q) := by
    apply (mem_cocycles₁_iff _).mpr
    intro g h
    funext u
    change wf (g * h) u = sourceAffineFunctionAction 3 Q F g (wf h) u + wf g u
    rw [sourceThreeFunctionAction_apply F Q h3Q]
    dsimp only [wf]
    rw [hHx, cocycles₁_map_mul_of_isTrivial, map_sub]
    ring
  refine ⟨⟨wf, hw⟩, ?_⟩
  apply cocycles₁_ext
  intro g
  funext u
  change wf g (u + 2) - wf g (u + 1) = z g
  dsimp only [wf]
  rw [map_add, map_add, map_ofNat, map_one]
  ring

/-- The actual constant native H1 class lies in the range of the original
translation-difference map, without assuming an affine lifting class. -/
theorem sourceThreeConstantH1_difference_range
    (z : cocycles₁ (Rep.trivial F (Gamma0 Q) F)) :
    sourceThreeConstantH1 F Q h3Q (H1π (Rep.trivial F (Gamma0 Q) F) z) ∈
      LinearMap.range (sourceThreeFunctionDifferenceH1 F Q h3Q) := by
  obtain ⟨w, hw⟩ := sourceThreeConstantCocycle_difference_range F Q h3Q z
  refine ⟨H1π (sourceAffineFunctionRep 3 Q F h3Q) w, ?_⟩
  change groupCohomology.map (MonoidHom.id _) (sourceThreeFunctionDifferenceMap F Q h3Q) 1
    (H1π (sourceAffineFunctionRep 3 Q F h3Q) w) = _
  rw [H1π_comp_map_apply, hw, sourceThreeConstantH1_cocycle]

end
end Dubon2026

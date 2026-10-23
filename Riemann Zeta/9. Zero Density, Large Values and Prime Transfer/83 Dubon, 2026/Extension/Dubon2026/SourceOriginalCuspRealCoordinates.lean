import Dubon2026.SourceOriginalCuspRealHeckeMatrix
import Dubon2026.SourceWeightTwoDualRealGenerators

/-! DUB-17/18 -> original rank-two matrix descent -> transport the two
proved cusp-dual generators into the actual lattice's real coordinates.
The matrix action is the existing integral original Hecke action, identified
through the faithful cusp-period transpose, rather than an independent action.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve KaehlerDifferential CongruenceSubgroup Matrix

private theorem transport_two_real_generators {I J M P : Type*}
    [AddCommGroup M] [Module ℝ M] [AddCommGroup P] [Module ℝ P]
    (e : M ≃ₗ[ℝ] P) (f : I → M → M) (g : J → P → P)
    (hf : ∀ i, ∃ j, ∀ x, e (f i x) = g j (e x))
    (h : ∃ w : Fin 2 → M,
      Submodule.span ℝ (Set.range fun t : I × Fin 2 => f t.1 (w t.2)) = ⊤) :
    ∃ w : Fin 2 → P,
      Submodule.span ℝ (Set.range fun t : J × Fin 2 => g t.1 (w t.2)) = ⊤ := by
  obtain ⟨w, hw⟩ := h
  refine ⟨fun k => e (w k), ?_⟩
  have hsp : Submodule.span ℝ (e '' Set.range (fun t : I × Fin 2 => f t.1 (w t.2))) = ⊤ := by
    rw [Submodule.span_image_linearEquiv, hw, Submodule.map_top, LinearMap.range_eq_top]
    exact e.surjective
  apply top_unique
  rw [← hsp]
  apply Submodule.span_mono
  rintro _ ⟨_, ⟨⟨t, k⟩, rfl⟩, rfl⟩
  obtain ⟨u, hu⟩ := hf t
  exact ⟨(u, k), (hu (w k)).symm⟩

variable (N : ℕ) [NeZero N]
local notation "V" => regularDifferentials ℂ (modularFunctionFieldOver N ℂ)
local notation "S" => CuspForm (Gamma0 N) 2

/-- Actual cusp-dual vectors expressed in the original real integral-lattice coordinates. -/
def originalCuspRealCoordinates {n m : ℕ} (b : Module.Basis (Fin n) ℂ V)
    (lb : Module.Basis (Fin m) ℤ (pathPeriodLattice N (fun i => (b i).val))) :
    Module.Dual ℂ S ≃ₗ[ℝ] (Fin m → ℝ) :=
  ((originalCuspPeriodDualEquiv N b).symm.restrictScalars ℝ).trans
    (originalPeriodRealBasis N b lb).equivFun

theorem originalCuspRealCoordinates_operator {n m : ℕ} (b : Module.Basis (Fin n) ℂ V)
    (lb : Module.Basis (Fin m) ℤ (pathPeriodLattice N (fun i => (b i).val)))
    (T : Module.End ℂ S) (φ : Module.Dual ℂ S) :
    originalCuspRealCoordinates N b lb (T.dualMap φ) =
      originalCuspRealHeckeMatrix N b lb T *ᵥ originalCuspRealCoordinates N b lb φ := by
  let e := originalCuspPeriodDualEquiv N b
  have ht : e.symm (T.dualMap φ) = originalCuspPeriodTranspose N b T (e.symm φ) := by
    apply e.injective
    rw [LinearEquiv.apply_symm_apply, originalCuspPeriodTranspose_apply]
    exact (congrArg T.dualMap (e.apply_symm_apply φ)).symm
  have hm := LinearMap.toMatrix_mulVec_repr (originalPeriodRealBasis N b lb)
    (originalPeriodRealBasis N b lb) ((originalCuspPeriodTranspose N b T).restrictScalars ℝ)
      (e.symm φ)
  change ((originalPeriodRealBasis N b lb).repr (e.symm (T.dualMap φ)) : Fin m → ℝ) = _
  exact (congrArg (fun v => ((originalPeriodRealBasis N b lb).repr v : Fin m → ℝ)) ht).trans
    hm.symm

theorem originalFullHecke_real_matrix_two_generators {n m : ℕ}
    (b : Module.Basis (Fin n) ℂ V)
    (lb : Module.Basis (Fin m) ℤ (pathPeriodLattice N (fun i => (b i).val))) :
    ∃ w : Fin 2 → Fin m → ℝ,
      Submodule.span ℝ (Set.range fun t : originalFullLatticeHeckeAlgebra N b × Fin 2 =>
        (originalLatticeHeckeMatrix N b lb t.1).map (Int.cast : ℤ → ℝ) *ᵥ w t.2) = ⊤ := by
  refine transport_two_real_generators (originalCuspRealCoordinates N b lb)
    (fun t : sourceOriginalIntegralHeckeAlgebra N 2 => t.val.dualMap)
    (fun t : originalFullLatticeHeckeAlgebra N b =>
      fun v => (originalLatticeHeckeMatrix N b lb t).map (Int.cast : ℤ → ℝ) *ᵥ v)
    ?_ (sourceWeightTwoDual_real_two_generators N)
  intro t
  have hr : originalCuspRealHeckeMatrix N b lb t.val ∈ Set.range
      (fun u : originalFullLatticeHeckeAlgebra N b =>
        (originalLatticeHeckeMatrix N b lb u).map (Int.cast : ℤ → ℝ)) :=
    (originalCuspRealHeckeMatrix_range N b lb).le ⟨t, rfl⟩
  obtain ⟨u, hu⟩ := hr
  refine ⟨u, fun φ => ?_⟩
  exact (originalCuspRealCoordinates_operator N b lb t.val φ).trans
    (congrArg (fun A : Matrix (Fin m) (Fin m) ℝ =>
      A *ᵥ originalCuspRealCoordinates N b lb φ) hu).symm

end
end Dubon2026.SourceFunctionField.OriginalChart

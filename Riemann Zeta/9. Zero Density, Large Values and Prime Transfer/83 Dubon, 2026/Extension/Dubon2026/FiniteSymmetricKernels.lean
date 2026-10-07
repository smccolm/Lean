import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-! # Kernel decompositions and compressed finite-group projections -/

namespace Dubon2026

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- A commuting operator product has the sum of kernels when its first factor is symmetric. -/
theorem symmetric_ker_mul_eq_sup [FiniteDimensional ℂ V] {A B : V →ₗ[ℂ] V}
    (hA : A.IsSymmetric) (hAB : Commute A B) :
    LinearMap.ker (A * B) = LinearMap.ker A ⊔ LinearMap.ker B := by
  have hc : IsCompl (LinearMap.range A) (LinearMap.ker A) := by
    rw [← hA.orthogonal_range]
    exact Submodule.isCompl_orthogonal_of_hasOrthogonalProjection
  apply le_antisymm
  · intro x hx
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp
      (show x ∈ LinearMap.range A ⊔ LinearMap.ker A by rw [hc.sup_eq_top]; trivial)
    have hAv : A v = 0 := hv
    have hABv : A (B v) = 0 := by
      rw [← Module.End.mul_apply, hAB.eq, Module.End.mul_apply, hAv, map_zero]
    have hABu : A (B u) = 0 := by
      change A (B (u + v)) = 0 at hx
      simpa only [map_add, hABv, add_zero] using hx
    have hBu : B u ∈ LinearMap.range A := by
      obtain ⟨t, rfl⟩ := hu
      exact ⟨B t, LinearMap.congr_fun hAB.eq t⟩
    have hzero : B u = 0 := Submodule.disjoint_def.mp hc.disjoint (B u) hBu hABu
    exact Submodule.mem_sup.mpr ⟨v, hv, u, hzero, add_comm v u⟩
  · refine sup_le ?_ ?_
    · intro x hx
      change A (B x) = 0
      rw [← Module.End.mul_apply, hAB.eq, Module.End.mul_apply, show A x = 0 from hx, map_zero]
    · intro x hx
      change A (B x) = 0
      rw [show B x = 0 from hx, map_zero]

/-- A finite commuting symmetric family decomposes its product kernel into individual kernels. -/
theorem symmetric_ker_noncommProd [FiniteDimensional ℂ V] {I : Type*}
    (s : Finset I) (A : I → V →ₗ[ℂ] V)
    (hc : Set.Pairwise (↑s) (fun i j => Commute (A i) (A j)))
    (hA : ∀ i ∈ s, (A i).IsSymmetric) :
    LinearMap.ker (s.noncommProd A hc) = ⨆ i ∈ s, LinearMap.ker (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Module.End.one_eq_id]
  | insert i s hi ih =>
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hi,
      symmetric_ker_mul_eq_sup (hA i (Finset.mem_insert_self i s))]
    · rw [ih _ (fun j hj => hA j (Finset.mem_insert_of_mem hj))]
      simp_rw [Finset.mem_insert_coe, iSup_insert, Finset.mem_coe]
    · exact s.noncommProd_commute _ _ _ (fun j hj =>
        hc (Finset.mem_insert_self i s) (Finset.mem_insert_of_mem hj) (by aesop))

/-- Compressing the complement of an orthogonal projection has zero kernel energy only on its fixed vectors. -/
theorem symmetric_projection_compression_kernel {e p : V →ₗ[ℂ] V}
    (he : e.IsSymmetric) (hp : p.IsSymmetricProjection) (x : V)
    (hex : e x = x) (hzero : e (x - p x) = 0) : p x = x := by
  have hp2 : p (p x) = p x := LinearMap.congr_fun hp.isIdempotentElem x
  have hinner : inner ℂ x (x - p x) = 0 := by
    calc
      inner ℂ x (x - p x) = inner ℂ (e x) (x - p x) := congrArg (fun v => inner ℂ v (x - p x)) hex.symm
      _ = inner ℂ x (e (x - p x)) := he _ _
      _ = 0 := by rw [hzero, inner_zero_right]
  have hnorm : inner ℂ (x - p x) (x - p x) = 0 := by
    rw [inner_sub_left, hp.isSymmetric, map_sub, hp2, sub_self, inner_zero_right, sub_zero]
    exact hinner
  exact (sub_eq_zero.mp ((inner_self_eq_zero (𝕜 := ℂ)).mp hnorm)).symm

end
end Dubon2026

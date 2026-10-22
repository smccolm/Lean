import Dubon2026.SourceOriginalTateAdicContinuity
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! DUB-17/18 -> actual modular Galois realization -> native p-adic continuity.
The existing discrete original torsion coordinates make the actual Tate action
locally constant modulo each p-power. The exact projection kernel turns this
into a norm estimate for every p-adic linear coordinate. Native p-adic power
bounds then prove continuity, without changing the p-adic topology.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve IsLocalRing Filter
open scoped Topology
local notation "Qbar" => AlgebraicClosure ℚ
variable (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]
local notation "T" => TateModule p (originalJZero N)

omit [NeZero N] in
theorem originalTate_linear_coordinate_mem (n : ℕ) (l : T →ₗ[ℤ_[p]] ℤ_[p])
    {x : T} (hx : x ∈ (maximalIdeal ℤ_[p] ^ n) • (⊤ : Submodule ℤ_[p] T)) :
    l x ∈ maximalIdeal ℤ_[p] ^ n := by
  refine Submodule.smul_induction_on hx (fun a ha y _ => ?_) (fun y z hy hz => ?_)
  · rw [map_smul, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ ha
  · rw [map_add]
    exact (maximalIdeal ℤ_[p] ^ n).add_mem hy hz

theorem originalTateGaloisRep_linear_coordinate_continuous (l : T →ₗ[ℤ_[p]] ℤ_[p]) (x : T) :
    Continuous (fun σ : Qbar ≃ₐ[ℚ] Qbar => l (originalTateGaloisRep N p σ x)) := by
  apply continuous_iff_continuousAt.mpr
  intro σ
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨n, hn⟩ := PadicInt.exists_pow_neg_lt p hε
  have hc := originalTateGaloisRep_coordinate_continuous N p n x
  have ho : IsOpen {τ : Qbar ≃ₐ[ℚ] Qbar |
      originalTateTorsionCoordinate N p n (originalTateGaloisRep N p τ x) =
        originalTateTorsionCoordinate N p n (originalTateGaloisRep N p σ x)} :=
    hc.isOpen_preimage {z | z = originalTateTorsionCoordinate N p n
      (originalTateGaloisRep N p σ x)} (isOpen_discrete _)
  filter_upwards [ho.mem_nhds (by rfl)] with τ hτ
  have hz : TateModule.proj p (originalJZero N) n
      (originalTateGaloisRep N p τ x - originalTateGaloisRep N p σ x) = 0 := by
    rw [map_sub, sub_eq_zero]
    exact congrArg Subtype.val hτ
  have hm := originalTate_linear_coordinate_mem N p n l
    ((TateModule.proj_eq_zero_iff n _).mp hz)
  rw [map_sub, PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow] at hm
  rw [dist_eq_norm]
  have hb : ‖l (originalTateGaloisRep N p τ x) - l (originalTateGaloisRep N p σ x)‖ ≤
      (p : ℝ) ^ (-(n : ℤ)) := by
    rwa [PadicInt.norm_le_pow_iff_mem_span_pow]
  exact hb.trans_lt hn

theorem originalTateGaloisRep_matrix_continuous {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ_[p] T) :
    Continuous (fun σ : Qbar ≃ₐ[ℚ] Qbar =>
      LinearMap.toMatrix b b (originalTateGaloisRep N p σ)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simpa only [LinearMap.toMatrix_apply, Module.Basis.coord_apply] using
    originalTateGaloisRep_linear_coordinate_continuous N p (b.coord i) (b j)

end
end Dubon2026.SourceFunctionField

import Dubon2026.SourceOriginalRegularEvaluationSeparation
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi -> Jacobi inversion.
The actual center-evaluation vectors of an original regular-differential
basis span its full complex coordinate space. A functional annihilating
them would give a regular differential vanishing at every center. The
proved evaluation separation forces it to vanish, contradicting basis
independence. This supplies the frame for the local inverse-function step.
Adapted from S_AlgebraicCurve_exists_degree_eq_zero_and_abelJacobiDiv_sub_mem_pathPeriodLattice,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Set Metric KaehlerDifferential
variable (N : ℕ) [NeZero N]

theorem span_readDifferential_center_eq_top {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (regularDifferentials ℂ (modularFunctionFieldOver N ℂ))) :
    Submodule.span ℂ (range fun v : Place ℂ (modularFunctionFieldOver N ℂ) =>
      fun i => readDifferential N v (b i) 0) = ⊤ := by
  classical
  by_contra htop
  obtain ⟨f, hf0, hker⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr htop)
  let c : Fin n → ℂ := fun i => f (fun j => if i = j then 1 else 0)
  have hfx : ∀ x : Fin n → ℂ, f x = ∑ i, x i * c i := fun x => by
    rw [LinearMap.pi_apply_eq_sum_univ f x]
    rfl
  let η : regularDifferentials ℂ (modularFunctionFieldOver N ℂ) := ∑ i, c i • b i
  have he : (η : Ω[modularFunctionFieldOver N ℂ⁄ℂ]) = ∑ i, c i • (b i : Ω[modularFunctionFieldOver N ℂ⁄ℂ]) := by
    simp only [η, Submodule.coe_sum, Submodule.coe_smul]
  have hz : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), readDifferential N v η 0 = 0 := by
    intro v
    rw [he, readDifferential_sum_smul N v c _ (fun i => (b i).2)
      (mem_ball_self (place_spec N v).1)]
    have hv : f (fun i => readDifferential N v (b i) 0) = 0 :=
      hker (Submodule.subset_span ⟨v, rfl⟩)
    rw [hfx] at hv
    exact (Finset.sum_congr rfl fun i _ => mul_comm (c i) (readDifferential N v (b i) 0)).trans hv
  have hη := eq_zero_of_forall_readDifferential_center N η η.2 hz
  have hη' : η = 0 := Subtype.ext hη
  have hc : ∀ i, c i = 0 := Fintype.linearIndependent_iff.mp b.linearIndependent c hη'
  apply hf0
  ext x
  simp [hfx, hc]

end
end Dubon2026.SourceFunctionField.OriginalChart

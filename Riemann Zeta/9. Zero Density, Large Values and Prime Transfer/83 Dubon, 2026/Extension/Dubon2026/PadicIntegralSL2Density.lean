import Dubon2026.SL2Reduction
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Topology.Algebra.Group.Matrix

/-! # Genuine integral SL2 approximation in the actual p-adic compact group -/

namespace Dubon2026

noncomputable section
open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups

/-- Every actual p-adic determinant-one matrix has an integral determinant-one lift at every prime-power precision. -/
theorem integralSL2_padic_congruence (p : ℕ) [Fact p.Prime]
    (g : SL(2, ℤ_[p])) (n : ℕ) :
    ∃ γ : SL(2, ℤ), ∀ i j : Fin 2,
      PadicInt.toZModPow n ((γ i j : ℤ) : ℤ_[p]) = PadicInt.toZModPow n (g i j) := by
  letI : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  obtain ⟨γ, hγ⟩ := SL2Reduction.SL2_reduction_surjective (p ^ n)
    (Matrix.SpecialLinearGroup.map (PadicInt.toZModPow n) g)
  refine ⟨γ, fun i j => ?_⟩
  have he := congrArg (fun A : SL(2, ZMod (p ^ n)) => A i j) hγ
  change (γ i j : ZMod (p ^ n)) = PadicInt.toZModPow n (g i j) at he
  simpa only [map_intCast] using he

/-- The genuine integral lift approximates every matrix entry with the exact p-adic precision. -/
theorem integralSL2_padic_approximation (p : ℕ) [Fact p.Prime]
    (g : SL(2, ℤ_[p])) (n : ℕ) :
    ∃ γ : SL(2, ℤ), ∀ i j : Fin 2,
      ‖g i j - ((γ i j : ℤ) : ℤ_[p])‖ ≤ (p : ℝ) ^ (-(n : ℤ)) := by
  obtain ⟨γ, hγ⟩ := integralSL2_padic_congruence p g n
  refine ⟨γ, fun i j => ?_⟩
  rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow,
    RingHom.mem_ker, map_sub, ← hγ i j, sub_self]

/-- The existing actual integral reduction theorem proves density in the genuine p-adic special linear group. -/
theorem integralSL2_dense_padic (p : ℕ) [Fact p.Prime] :
    DenseRange (Matrix.SpecialLinearGroup.map (Int.castRingHom ℤ_[p]) :
      SL(2, ℤ) →* SL(2, ℤ_[p])) := by
  letI : MetricSpace (Matrix (Fin 2) (Fin 2) ℤ_[p]) :=
    inferInstanceAs (MetricSpace (Fin 2 → Fin 2 → ℤ_[p]))
  letI : MetricSpace SL(2, ℤ_[p]) :=
    inferInstanceAs (MetricSpace {A : Matrix (Fin 2) (Fin 2) ℤ_[p] // A.det = 1})
  apply Metric.denseRange_iff.mpr
  intro g ε hε
  obtain ⟨n, hn⟩ := PadicInt.exists_pow_neg_lt p hε
  obtain ⟨γ, hγ⟩ := integralSL2_padic_approximation p g n
  refine ⟨γ, ?_⟩
  change dist (g : Matrix (Fin 2) (Fin 2) ℤ_[p])
    ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℤ_[p]) γ) :
      Matrix (Fin 2) (Fin 2) ℤ_[p]) < ε
  apply (dist_pi_lt_iff hε).mpr
  intro i
  apply (dist_pi_lt_iff hε).mpr
  intro j
  rw [dist_eq_norm]
  exact (hγ i j).trans_lt hn

end
end Dubon2026

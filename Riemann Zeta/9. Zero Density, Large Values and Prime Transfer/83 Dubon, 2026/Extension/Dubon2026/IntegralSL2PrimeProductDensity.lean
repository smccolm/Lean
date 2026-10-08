import Dubon2026.FinitePadicSL2Approximation

/-! # Density of the genuine diagonal integral group in products of p-adic compact groups -/

namespace Dubon2026

noncomputable section
open Matrix Matrix.SpecialLinearGroup Filter
open scoped MatrixGroups Topology

/-- One actual integral determinant-one matrix meets every basic neighborhood in the product of distinct p-adic compact groups. -/
theorem integralSL2_dense_prime_product {ι : Type*}
    (p : ι → ℕ) [∀ i, Fact (p i).Prime] (hp : Function.Injective p) :
    DenseRange (fun γ : SL(2, ℤ) => fun i : ι =>
      Matrix.SpecialLinearGroup.map (Int.castRingHom ℤ_[p i]) γ) := by
  classical
  letI (i : ι) : MetricSpace (Matrix (Fin 2) (Fin 2) ℤ_[p i]) :=
    inferInstanceAs (MetricSpace (Fin 2 → Fin 2 → ℤ_[p i]))
  letI (i : ι) : MetricSpace SL(2, ℤ_[p i]) :=
    inferInstanceAs (MetricSpace {A : Matrix (Fin 2) (Fin 2) ℤ_[p i] // A.det = 1})
  intro g
  apply mem_closure_iff_nhds.mpr
  intro U hU
  rw [nhds_pi, Filter.mem_pi'] at hU
  obtain ⟨S, t, ht, hsub⟩ := hU
  choose ε hε hball using (fun i => Metric.mem_nhds_iff.mp (ht i))
  choose n hn using (fun i => PadicInt.exists_pow_neg_lt (p i) (hε i))
  obtain ⟨γ, hγ⟩ := integralSL2_finite_padic_approximation
    (fun i : S => p i.val) (hp.comp Subtype.val_injective)
    (fun i : S => g i.val) (fun i : S => n i.val)
  refine ⟨(fun i => Matrix.SpecialLinearGroup.map (Int.castRingHom ℤ_[p i]) γ), ?_, ⟨γ, rfl⟩⟩
  apply hsub
  intro i hi
  apply hball i
  rw [Metric.mem_ball, dist_comm]
  change dist (g i : Matrix (Fin 2) (Fin 2) ℤ_[p i])
    ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℤ_[p i]) γ) :
      Matrix (Fin 2) (Fin 2) ℤ_[p i]) < ε i
  apply (dist_pi_lt_iff (hε i)).mpr
  intro a
  apply (dist_pi_lt_iff (hε i)).mpr
  intro b
  rw [dist_eq_norm]
  exact (hγ ⟨i, hi⟩ a b).trans_lt (hn i)

end
end Dubon2026

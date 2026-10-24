import Dubon2026.SourceConstantFieldOrderResidues

/-! DUB-17/18 -> good reduction -> principal-divisor pushforward -> local
fiber-order inequality. The actual local quotient by the r-th maximal-ideal
power is finite dimensional with dimension at most r when the constant
residue map is surjective. Membership in the power gives the exact order
bound. Existing residue-value lifting supplies the finite digit expansion.
Adapted from the local quotient step of
S_AlgebraicCurve_RegularProlongation_ord_residue_le_sum_ord_of_isIntegral_adjoin,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. -/
namespace Dubon2026.SourceCurve.Place
noncomputable section
open IsLocalRing
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem le_ord_of_mem_maximalIdeal_pow (P : Place K F) (r : ℕ) (y : P.toValuationSubring)
    (hy : y ∈ (maximalIdeal P.toValuationSubring) ^ r) :
    (y : F) = 0 ∨ (r : ℤ) ≤ P.ord (y : F) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible P.toValuationSubring
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hy
  obtain ⟨a, rfl⟩ := hy
  by_cases ha : (a : F) = 0
  · left; push_cast; rw [ha, zero_mul]
  · right
    have hϖ0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
    push_cast
    rw [P.ord_mul ha (pow_ne_zero _ hϖ0), show P.ord ((ϖ : F) ^ r) = (r : ℤ) * P.ord (ϖ : F) by
      rw [← zpow_natCast, P.ord_zpow], P.ord_coe_irreducible hϖ, mul_one]
    have := ord_nonneg_of_mem P a.2
    omega

theorem finite_quotient_maximalIdeal_pow (P : Place K F)
    (hres : Function.Surjective (algebraMap K P.ResidueField)) (r : ℕ) :
    Module.Finite K (P.toValuationSubring ⧸ (maximalIdeal P.toValuationSubring) ^ r) ∧
      Module.finrank K (P.toValuationSubring ⧸ (maximalIdeal P.toValuationSubring) ^ r) ≤ r := by
  classical
  set O := P.toValuationSubring
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O

  have key : ∀ s : ℕ, ∀ y : O, ∃ a : ℕ → K,
      y - ∑ i ∈ Finset.range s, algebraMap K O (a i) * ϖ ^ i ∈ (maximalIdeal O) ^ s := by
    intro s
    induction s with
    | zero => intro y; exact ⟨fun _ => 0, by simp⟩
    | succ s ih =>
      intro y
      obtain ⟨a, ha⟩ := ih y
      rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at ha
      obtain ⟨b, hb⟩ := ha
      obtain ⟨c, hc⟩ := ConstantField.exists_sub_algebraMap_mem_maximalIdeal P hres b
      rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at hc
      obtain ⟨d, hd⟩ := hc
      refine ⟨Function.update a s c, ?_⟩
      rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
      refine ⟨d, ?_⟩
      rw [Finset.sum_range_succ, Function.update_self,
        Finset.sum_congr rfl fun i hi =>
          by rw [Function.update_of_ne (Finset.mem_range.mp hi).ne],
        ← sub_sub, ← hb]
      linear_combination (ϖ ^ s) * hd

  let φ : (Fin r → K) →ₗ[K] O ⧸ (maximalIdeal O) ^ r :=
    Fintype.linearCombination K fun i : Fin r =>
      Ideal.Quotient.mkₐ K ((maximalIdeal O) ^ r) (ϖ ^ (i : ℕ))
  have hφ : Function.Surjective φ := by
    intro q
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mkₐ_surjective K _ q
    obtain ⟨a, ha⟩ := key r y
    refine ⟨fun i => a i, ?_⟩
    simp only [φ, Fintype.linearCombination_apply, ← map_smul, ← map_sum]
    rw [eq_comm, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq]
    convert ha using 2
    rw [← Fin.sum_univ_eq_sum_range (fun i => algebraMap K O (a i) * ϖ ^ i) r]
    exact Finset.sum_congr rfl fun i _ => Algebra.smul_def _ _
  haveI : Module.Finite K (O ⧸ (maximalIdeal O) ^ r) := Module.Finite.of_surjective φ hφ
  exact ⟨this, (LinearMap.finrank_le_finrank_of_surjective hφ).trans (Module.finrank_fin_fun K).le⟩


end
end Dubon2026.SourceCurve.Place

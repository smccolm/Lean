import Dubon2026.SourceHasseCoefficientExpansion
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Adjoin.Field

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> exact
residue-field degree -> prime j nonmembership -> the one-root Hasse case.
The final argument already takes place over algebraically closed constants.
Native integral-element and splitting results therefore replace the archived
general Laurent coefficient proof. This extra intermediate field hypothesis
does not narrow the final prime-nonmembership theorem: that theorem ascends to
the algebraic closure before using this lemma. -/
namespace Dubon2026.SourceFunctionField
noncomputable section

theorem laurent_eq_constant_of_pow_eq_constant
    {K : Type*} [Field K] [IsAlgClosed K] {x : LaurentSeries K} {γ : K} {M : ℕ}
    (hM : 0 < M) (hγ : γ ≠ 0) (hx : x ^ M = HahnSeries.C γ) :
    ∃ c : K, c ≠ 0 ∧ x = HahnSeries.C c := by
  have hC : ∀ a : K, algebraMap K (LaurentSeries K) a = HahnSeries.C a :=
    fun a => algebraMap_laurent_eq_single K a
  have hint : IsIntegral K x := IsIntegral.of_pow hM (by
    rw [hx, ← hC]
    exact isIntegral_algebraMap)
  have hmem : x ∈ (algebraMap K (LaurentSeries K)).range :=
    minpoly.mem_range_of_degree_eq_one K x
      (IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hint))
  obtain ⟨c, hc⟩ := hmem
  rw [hC] at hc
  refine ⟨c, ?_, hc.symm⟩
  intro hc0
  rw [← hc, hc0, map_zero, zero_pow (Nat.ne_of_gt hM)] at hx
  have hzero : (0 : K) = γ := by
    apply HahnSeries.C_injective (Γ := ℤ)
    rw [map_zero]
    exact hx
  exact hγ hzero.symm

theorem hasse_one_root_closed {K : Type*} [Field K] [IsAlgClosed K] {M : ℕ}
    (hM : (M : K) ≠ 0) {c : K} (hc : c ≠ 0) {β : K}
    (hstar : Polynomial.aeval (jqModC K)
        (Polynomial.C c * (Polynomial.X - Polynomial.C β) ^ M) *
        (HahnSeries.single (1 : ℤ) (1 : K) * HahnSeries.ofPowerSeries ℤ K
          (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) ^ M = 1) :
    ∃ γ : K, γ ≠ 0 ∧ (jqModC K - HahnSeries.C β) *
      (HahnSeries.single (1 : ℤ) (1 : K) * HahnSeries.ofPowerSeries ℤ K
        (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) = HahnSeries.C γ := by
  let D : LaurentSeries K := HahnSeries.single (1 : ℤ) (1 : K) *
    HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24
  have hC : ∀ a : K, algebraMap K (LaurentSeries K) a = HahnSeries.C a :=
    fun a => algebraMap_laurent_eq_single K a
  have hgroup : HahnSeries.C c * ((jqModC K - HahnSeries.C β) * D) ^ M = 1 := by
    rw [map_mul, map_pow, map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
      Polynomial.aeval_C, hC, hC] at hstar
    rw [mul_pow, ← mul_assoc]
    exact hstar
  have hpow : ((jqModC K - HahnSeries.C β) * D) ^ M = HahnSeries.C c⁻¹ := by
    have h := congrArg (fun z : LaurentSeries K => HahnSeries.C c⁻¹ * z) hgroup
    dsimp only at h
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul, mul_one] at h
    exact h
  have hMpos : 0 < M := Nat.pos_of_ne_zero (fun h => hM (by rw [h, Nat.cast_zero]))
  exact laurent_eq_constant_of_pow_eq_constant hMpos (inv_ne_zero hc) hpow

end
end Dubon2026.SourceFunctionField

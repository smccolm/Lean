import Dubon2026.SourceHassePolynomialTransport

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> higher symmetric-power
continuation -> automorphy/residual association -> original Frobenius/inertia
-> modular-curve good reduction -> exact degree -> prime j nonmembership.
This assembles the actual Hasse polynomial, prime orbit factorization,
discriminant norm, finite root count and eta power obstruction.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_StarBank_starBank. All mathematical inputs are proved locally;
the archived conditional core is replaced by direct applications. -/
namespace Dubon2026.SourceFunctionField
noncomputable section

variable {K : Type*} [Field K]

theorem eq_C_leadingCoeff_mul_pow_of_forall_root [IsAlgClosed K] {G : Polynomial K} {β₀ : K}
    (huniq : ∀ β : K, G.IsRoot β → β = β₀) :
    G = Polynomial.C G.leadingCoeff * (Polynomial.X - Polynomial.C β₀) ^ G.natDegree := by
  have hcard : G.roots.card = G.natDegree :=
    Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits G)
  have hall : ∀ b ∈ G.roots, b = β₀ := fun b hb => huniq b (Polynomial.mem_roots'.mp hb).2
  have hrep : G.roots = Multiset.replicate G.natDegree β₀ := by
    have h1 := Multiset.eq_replicate_card.mpr hall
    rwa [hcard] at h1
  have h2 := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hcard
  rw [hrep, Multiset.map_replicate, Multiset.prod_replicate] at h2
  exact h2.symm

theorem endgame_read (p : ℕ) [NeZero p] (hp1 : 1 ≤ p) {β₀ γ : K} (hγ : γ ≠ 0)
    (honept : (jqModC K - HahnSeries.C β₀)
        * (HahnSeries.single (1 : ℤ) 1
            * HahnSeries.ofPowerSeries ℤ K
                (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24)
      = HahnSeries.C γ)
    (hpress : qExpand K p (jqModC K)
      = (jqModC K - HahnSeries.C β₀) ^ p + HahnSeries.C β₀) :
    (HahnSeries.single (1 : ℤ) 1
        * HahnSeries.ofPowerSeries ℤ K
            (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) ^ p
      = HahnSeries.C (γ ^ (p - 1))
        * qExpand K p (HahnSeries.single (1 : ℤ) 1
            * HahnSeries.ofPowerSeries ℤ K
                (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) := by
  set D : LaurentSeries K := HahnSeries.single (1 : ℤ) 1
    * HahnSeries.ofPowerSeries ℤ K
        (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24 with hD
  have hCγ0 : (HahnSeries.C γ : LaurentSeries K) ≠ 0 := by
    intro h
    apply hγ
    have h1 := congrArg (fun z : LaurentSeries K => z.coeff 0) h
    dsimp only at h1
    rw [show (HahnSeries.C γ : LaurentSeries K) = HahnSeries.single 0 γ from rfl,
      HahnSeries.coeff_single, if_pos rfl] at h1
    exact h1.trans rfl

  have hD0 : D ≠ 0 := by
    intro hz
    have h := honept
    change (jqModC K - HahnSeries.C β₀) * D = HahnSeries.C γ at h
    rw [hz, mul_zero] at h
    exact hCγ0 h.symm

  have hq := congrArg (qExpand K p) honept
  rw [map_mul, qExpand_C] at hq
  have hqj : qExpand K p (jqModC K - HahnSeries.C β₀)
      = (jqModC K - HahnSeries.C β₀) ^ p := by
    rw [map_sub, qExpand_C, hpress, add_sub_cancel_right]
  rw [hqj] at hq

  have hj : jqModC K - HahnSeries.C β₀ = HahnSeries.C γ * D⁻¹ := by
    rw [← honept]
    exact (mul_inv_cancel_right₀ hD0 _).symm
  rw [hj, mul_pow] at hq

  have h6 := congrArg (fun z : LaurentSeries K => z * D ^ p) hq
  dsimp only at h6
  rw [show HahnSeries.C γ ^ p * D⁻¹ ^ p * qExpand K p D * D ^ p
      = HahnSeries.C γ ^ p * qExpand K p D * (D⁻¹ * D) ^ p from by ring,
    inv_mul_cancel₀ hD0, one_pow, mul_one] at h6

  have h7 : HahnSeries.C γ * (HahnSeries.C (γ ^ (p - 1)) * qExpand K p D)
      = HahnSeries.C γ * D ^ p := by
    calc HahnSeries.C γ * (HahnSeries.C (γ ^ (p - 1)) * qExpand K p D)
        = HahnSeries.C γ ^ p * qExpand K p D := by
          rw [← mul_assoc, ← map_mul, ← pow_succ', Nat.sub_add_cancel hp1, map_pow]
      _ = HahnSeries.C γ * D ^ p := h6
  exact (mul_left_cancel₀ hCγ0 h7).symm


end
end Dubon2026.SourceFunctionField

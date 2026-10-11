import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-! # Explicit averaging witnesses for original finite-group cocycles -/

namespace Dubon2026
noncomputable section

variable {K G : Type} [Field K] [Group G] [Fintype G] (A : Rep K G)

/-- If the actual group order is invertible in the coefficient field, every
original one-cocycle is the coboundary of its negative average. -/
theorem finiteOneCocycle_average_coboundary
    (hn : (Fintype.card G : K) ≠ 0) (c : groupCohomology.cocycles₁ A) :
    groupCohomology.d₀₁ A (-((Fintype.card G : K)⁻¹ • ∑ h, c h)) = c.val := by
  funext g
  have hperm : (∑ h, c (g * h)) = ∑ h, c h :=
    Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun _ => rfl)
  have hs : (∑ h, c h) = A.ρ g (∑ h, c h) + (Fintype.card G : K) • c g := by
    calc
      (∑ h, c h) = ∑ h, c (g * h) := hperm.symm
      _ = ∑ h, (A.ρ g (c h) + c g) := by
        apply Finset.sum_congr rfl
        intro h _
        exact (groupCohomology.mem_cocycles₁_iff _).mp c.property g h
      _ = A.ρ g (∑ h, c h) + (Fintype.card G : K) • c g := by
        simp only [Finset.sum_add_distrib, ← map_sum, Finset.sum_const,
          Finset.card_univ, Nat.cast_smul_eq_nsmul]
  have hnvalue : (Fintype.card G : K) • c g = (∑ h, c h) - A.ρ g (∑ h, c h) := by
    apply eq_sub_iff_add_eq.mpr
    calc
      (Fintype.card G : K) • c g + A.ρ g (∑ h, c h) =
          A.ρ g (∑ h, c h) + (Fintype.card G : K) • c g := add_comm _ _
      _ = ∑ h, c h := hs.symm
  change A.ρ g (-((Fintype.card G : K)⁻¹ • ∑ h, c h)) -
    (-((Fintype.card G : K)⁻¹ • ∑ h, c h)) = c g
  rw [map_neg, map_smul, sub_neg_eq_add]
  calc
    -((Fintype.card G : K)⁻¹ • A.ρ g (∑ h, c h)) +
        (Fintype.card G : K)⁻¹ • (∑ h, c h) =
      (Fintype.card G : K)⁻¹ • ((∑ h, c h) - A.ρ g (∑ h, c h)) := by
        rw [smul_sub]
        abel
    _ = (Fintype.card G : K)⁻¹ • ((Fintype.card G : K) • c g) :=
      congrArg (fun x => (Fintype.card G : K)⁻¹ • x) hnvalue.symm
    _ = c g := by rw [smul_smul, inv_mul_cancel₀ hn, one_smul]

/-- Averaging the second variable of an original two-cocycle gives an explicit
one-cochain whose original differential is that same two-cocycle. -/
theorem finiteTwoCocycle_average_coboundary
    (hn : (Fintype.card G : K) ≠ 0) (c : groupCohomology.cocycles₂ A) :
    groupCohomology.d₁₂ A (fun g => (Fintype.card G : K)⁻¹ • ∑ t, c (g, t)) = c.val := by
  funext z
  rcases z with ⟨g, h⟩
  have hperm : (∑ t, c (g, h * t)) = ∑ t, c (g, t) :=
    Fintype.sum_equiv (Equiv.mulLeft h) _ _ (fun _ => rfl)
  have hs : (∑ t, c (g * h, t)) + (Fintype.card G : K) • c (g, h) =
      A.ρ g (∑ t, c (h, t)) + ∑ t, c (g, t) := by
    calc
      (∑ t, c (g * h, t)) + (Fintype.card G : K) • c (g, h) =
          ∑ t, (c (g * h, t) + c (g, h)) := by
            simp only [Finset.sum_add_distrib, Finset.sum_const,
              Finset.card_univ, Nat.cast_smul_eq_nsmul]
      _ = ∑ t, (A.ρ g (c (h, t)) + c (g, h * t)) := by
        apply Finset.sum_congr rfl
        intro t _
        exact (groupCohomology.mem_cocycles₂_iff _).mp c.property g h t
      _ = A.ρ g (∑ t, c (h, t)) + ∑ t, c (g, t) := by
        rw [Finset.sum_add_distrib, ← map_sum, hperm]
  have hnvalue : (Fintype.card G : K) • c (g, h) =
      A.ρ g (∑ t, c (h, t)) - (∑ t, c (g * h, t)) + ∑ t, c (g, t) := by
    apply add_left_cancel (a := ∑ t, c (g * h, t))
    calc
      (∑ t, c (g * h, t)) + (Fintype.card G : K) • c (g, h) =
          A.ρ g (∑ t, c (h, t)) + ∑ t, c (g, t) := hs
      _ = (∑ t, c (g * h, t)) +
          (A.ρ g (∑ t, c (h, t)) - (∑ t, c (g * h, t)) + ∑ t, c (g, t)) := by abel
  change A.ρ g ((Fintype.card G : K)⁻¹ • ∑ t, c (h, t)) -
      (Fintype.card G : K)⁻¹ • (∑ t, c (g * h, t)) +
      (Fintype.card G : K)⁻¹ • (∑ t, c (g, t)) = c (g, h)
  rw [map_smul, ← smul_sub, ← smul_add, ← hnvalue,
    smul_smul, inv_mul_cancel₀ hn, one_smul]

end
end Dubon2026

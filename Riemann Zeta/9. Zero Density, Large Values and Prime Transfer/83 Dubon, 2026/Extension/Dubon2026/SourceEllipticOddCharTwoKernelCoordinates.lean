import Dubon2026.SourceEllipticOddCharTwoQuotientCoefficients
import Dubon2026.SourceEllipticOddSummingFold
import Dubon2026.SourceEllipticOddCharTwoCosets

/-! Actual characteristic-two ordinary quotient coordinates and discriminant.
The odd summing-set equation, nonzero tangent term and x-coordinate injection
are reused from the proved actual torsion structure. The quotient-coordinate
orbit trace supplies the two-torsion coset identities. These discharge the
finite norm premises for odd quotient ellipticity, then cyclic quotient
products, inertia census and good reduction in DUB-17 / DUB-18.
Adapted from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2. -/
namespace Dubon2026.SourceEllipticVelu.OddDiscriminant.CharTwo
open WeierstrassCurve
noncomputable section
section VGlue



variable {F : Type*} [Field F] [DecidableEq F] (h2 : (2 : F) = 0) (V : WeierstrassCurve F)
  (ha₁ : V.a₁ = 1) (ha₃ : V.a₃ = 0) (ha₄ : V.a₄ = 0)
  {n : ℕ} {Q : V.toAffine.Point} (hQ : addOrderOf Q = 2 * n + 1)

include hQ in

theorem kQ_equation {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    V.toAffine.Equation ((coordsOrZero (k • Q))).1 ((coordsOrZero (k • Q))).2 := by
  exact (isOddVeluSet_oddOrderSummingSet hQ).equation _
    (mem_oddOrderSummingSet.mpr ⟨k, hk1, hkn, rfl⟩)

include h2 ha₁ ha₃ hQ in

theorem xk_ne_zero {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    ((coordsOrZero (k • Q))).1 ≠ 0 := by
  have hg := (isOddVeluSet_oddOrderSummingSet hQ).gy_ne_zero _
    (mem_oddOrderSummingSet.mpr ⟨k, hk1, hkn, rfl⟩)
  rwa [veluGy_V h2 V ha₁ ha₃] at hg

include h2 ha₁ ha₃ ha₄ hQ in

theorem xvSum_V (v : F) :
    xvSum V Q n v = v + ∑ k ∈ Finset.Icc 1 n,
      (((coordsOrZero (k • Q))).1 / (v - ((coordsOrZero (k • Q))).1)
        + ((coordsOrZero (k • Q))).1 ^ 2 / (v - ((coordsOrZero (k • Q))).1) ^ 2) := by
  unfold xvSum
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [Finset.mem_Icc] at hk
  rw [veluT_V h2 V ha₁ ha₃ ha₄, veluU_V h2 V ha₁ ha₃ ha₄ (kQ_equation V hQ hk.1 hk.2)]

include h2 ha₁ ha₃ ha₄ hQ in

theorem row_iff_chain :
    (veluQuotient V (oddOrderSummingSet V Q n)).Δ *
        (∏ P ∈ oddOrderSummingSet V Q n, veluU V P.1 P.2) ^ 4
      = V.Δ ^ (2 * n + 1) ↔
    (V.a₆ + (∑ k ∈ Finset.Icc 1 n, ((coordsOrZero (k • Q))).1)
        + (∑ k ∈ Finset.Icc 1 n, ((coordsOrZero (k • Q))).1) ^ 2)
      * (∏ k ∈ Finset.Icc 1 n, ((coordsOrZero (k • Q))).1 ^ 2) ^ 4
    = V.a₆ ^ (2 * (Finset.Icc 1 n).card + 1) := by
  have hS : ∀ P ∈ oddOrderSummingSet V Q n, V.toAffine.Equation P.1 P.2 :=
    (isOddVeluSet_oddOrderSummingSet hQ).equation
  rw [Δ_veluQuotient_V h2 V ha₁ ha₃ ha₄ _ hS,
    prod_veluU_V h2 V ha₁ ha₃ ha₄ _ hS, Δ_V h2 V ha₁ ha₃ ha₄,
    sum_oddOrderSummingSet_eq hQ (fun P => P.1),
    prod_oddOrderSummingSet_eq hQ (fun P => P.1),
    Nat.card_Icc, Nat.add_sub_cancel, ← Finset.prod_pow]


end VGlue

end
end Dubon2026.SourceEllipticVelu.OddDiscriminant.CharTwo

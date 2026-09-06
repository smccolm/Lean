import GafniTao.WeightedMixedShellEnergy

/-!
# Weighted transfer for four different source families

This is the coordinate-dependent version of the existing finite weighted
transfer.  Each coordinate has its own source family, representative map,
and fiber bound.  It is needed because a resonant zero quadruple may select
four different dyadic height shells.
-/

open scoped BigOperators

namespace GafniTao

noncomputable section

def mappedQuadrupleOf {Alpha Beta : Type*}
    (f0 f1 f2 f3 : Alpha → Beta)
    (q : (Alpha × Alpha) × (Alpha × Alpha)) :
    (Beta × Beta) × (Beta × Beta) :=
  ((f0 q.1.1, f1 q.1.2), (f2 q.2.1, f3 q.2.2))

/-- Product-multiplicity fibers for four coordinate-dependent maps. -/
theorem weighted_mixed_quadruple_sum_le_fiber_product_mul_card
    {Alpha Beta : Type*} [DecidableEq Alpha] [DecidableEq Beta]
    (S0 S1 S2 S3 : Finset Alpha)
    (Q : Finset ((Alpha × Alpha) × (Alpha × Alpha)))
    (U : Finset ((Beta × Beta) × (Beta × Beta)))
    (weight : Alpha → Nat) (f0 f1 f2 f3 : Alpha → Beta)
    (L0 L1 L2 L3 : Nat)
    (hQ : Q ⊆ quadrupleProductOf S0 S1 S2 S3)
    (hMaps : Set.MapsTo (mappedQuadrupleOf f0 f1 f2 f3)
      (Q : Set _) (U : Set _))
    (hLocal0 : ∀ b, (∑ x ∈ S0.filter (fun y => f0 y = b), weight x) ≤ L0)
    (hLocal1 : ∀ b, (∑ x ∈ S1.filter (fun y => f1 y = b), weight x) ≤ L1)
    (hLocal2 : ∀ b, (∑ x ∈ S2.filter (fun y => f2 y = b), weight x) ≤ L2)
    (hLocal3 : ∀ b, (∑ x ∈ S3.filter (fun y => f3 y = b), weight x) ≤ L3) :
    (∑ q ∈ Q, weightedQuadruple weight q) ≤
      (L0 * L1 * L2 * L3) * U.card := by
  classical
  have hFiberwise := Finset.sum_fiberwise_eq_sum_filter Q U
    (mappedQuadrupleOf f0 f1 f2 f3) (weightedQuadruple weight)
  have hAll : Q.filter
      (fun q => mappedQuadrupleOf f0 f1 f2 f3 q ∈ U) = Q := by
    apply Finset.filter_eq_self.mpr
    intro q hq
    exact hMaps hq
  rw [hAll] at hFiberwise
  rw [← hFiberwise]
  calc
    (∑ u ∈ U,
        ∑ q ∈ Q.filter
          (fun x => mappedQuadrupleOf f0 f1 f2 f3 x = u),
          weightedQuadruple weight q) ≤
        ∑ _u ∈ U, L0 * L1 * L2 * L3 := by
      apply Finset.sum_le_sum
      intro u hu
      let A0 := S0.filter (fun x => f0 x = u.1.1)
      let A1 := S1.filter (fun x => f1 x = u.1.2)
      let A2 := S2.filter (fun x => f2 x = u.2.1)
      let A3 := S3.filter (fun x => f3 x = u.2.2)
      have hSubset :
          Q.filter (fun x => mappedQuadrupleOf f0 f1 f2 f3 x = u) ⊆
            quadrupleProductOf A0 A1 A2 A3 := by
        intro q hq
        rw [Finset.mem_filter] at hq
        have hmem := hQ hq.1
        change q ∈ (S0.product S1).product (S2.product S3) at hmem
        have hOuter := Finset.mem_product.mp hmem
        have hLeft := Finset.mem_product.mp hOuter.1
        have hRight := Finset.mem_product.mp hOuter.2
        rcases hLeft with ⟨hq0, hq1⟩
        rcases hRight with ⟨hq2, hq3⟩
        have hm := hq.2
        have hm0 := congrArg (fun v => v.1.1) hm
        have hm1 := congrArg (fun v => v.1.2) hm
        have hm2 := congrArg (fun v => v.2.1) hm
        have hm3 := congrArg (fun v => v.2.2) hm
        change q ∈ (A0.product A1).product (A2.product A3)
        apply Finset.mem_product.mpr
        exact ⟨Finset.mem_product.mpr
            ⟨Finset.mem_filter.mpr ⟨hq0, hm0⟩,
              Finset.mem_filter.mpr ⟨hq1, hm1⟩⟩,
          Finset.mem_product.mpr
            ⟨Finset.mem_filter.mpr ⟨hq2, hm2⟩,
              Finset.mem_filter.mpr ⟨hq3, hm3⟩⟩⟩
      calc
        (∑ q ∈ Q.filter
            (fun x => mappedQuadrupleOf f0 f1 f2 f3 x = u),
            weightedQuadruple weight q) ≤
            ∑ q ∈ quadrupleProductOf A0 A1 A2 A3,
              weightedQuadruple weight q :=
          Finset.sum_le_sum_of_subset hSubset
        _ = (∑ x ∈ A0, weight x) * (∑ x ∈ A1, weight x) *
              (∑ x ∈ A2, weight x) * (∑ x ∈ A3, weight x) := by
          have h01 :
              (∑ p ∈ A0.product A1, weight p.1 * weight p.2) =
                (∑ x ∈ A0, weight x) * (∑ x ∈ A1, weight x) := by
            calc
              (∑ p ∈ A0.product A1, weight p.1 * weight p.2) =
                  ∑ x ∈ A0, ∑ y ∈ A1, weight x * weight y := by
                exact Finset.sum_product A0 A1
                  (fun p => weight p.1 * weight p.2)
              _ = _ := (Finset.sum_mul_sum A0 A1 weight weight).symm
          have h23 :
              (∑ p ∈ A2.product A3, weight p.1 * weight p.2) =
                (∑ x ∈ A2, weight x) * (∑ x ∈ A3, weight x) := by
            calc
              (∑ p ∈ A2.product A3, weight p.1 * weight p.2) =
                  ∑ x ∈ A2, ∑ y ∈ A3, weight x * weight y := by
                exact Finset.sum_product A2 A3
                  (fun p => weight p.1 * weight p.2)
              _ = _ := (Finset.sum_mul_sum A2 A3 weight weight).symm
          unfold quadrupleProductOf
          calc
            (∑ q ∈ (A0.product A1).product (A2.product A3),
                weightedQuadruple weight q) =
                ∑ p ∈ A0.product A1, ∑ r ∈ A2.product A3,
                  weightedQuadruple weight (p, r) := by
              exact Finset.sum_product (A0.product A1) (A2.product A3)
                (fun q => weightedQuadruple weight q)
            _ = ∑ p ∈ A0.product A1, ∑ r ∈ A2.product A3,
                  (weight p.1 * weight p.2) *
                    (weight r.1 * weight r.2) := by
              apply Finset.sum_congr rfl
              intro p hp
              apply Finset.sum_congr rfl
              intro r hr
              dsimp only [weightedQuadruple]
              ring
            _ = (∑ p ∈ A0.product A1, weight p.1 * weight p.2) *
                  (∑ r ∈ A2.product A3, weight r.1 * weight r.2) :=
              (Finset.sum_mul_sum (A0.product A1) (A2.product A3)
                (fun p => weight p.1 * weight p.2)
                (fun r => weight r.1 * weight r.2)).symm
            _ = _ := by rw [h01, h23]; ring
        _ ≤ L0 * L1 * L2 * L3 := by
          gcongr
          · exact hLocal0 _
          · exact hLocal1 _
          · exact hLocal2 _
          · exact hLocal3 _
    _ = (L0 * L1 * L2 * L3) * U.card := by
      simp [mul_comm]

#print axioms mappedQuadrupleOf
#print axioms weighted_mixed_quadruple_sum_le_fiber_product_mul_card

end

end GafniTao

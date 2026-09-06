import GafniTao.FiniteEnergyColoring

/-!
# Weighted transfer from zero quadruples to ordinate quadruples

This is the finite multiplicity ledger needed after the four-coordinate
detector pigeonhole.  If every ordinate representative has total source
weight at most `L`, then a represented real quadruple has at most `L^4`
product-multiplicity preimages.
-/

open scoped BigOperators

namespace GafniTao

noncomputable section

def mappedQuadruple {Alpha Beta : Type*} (f : Alpha -> Beta)
    (q : (Alpha × Alpha) × (Alpha × Alpha)) :
    (Beta × Beta) × (Beta × Beta) :=
  ((f q.1.1, f q.1.2), (f q.2.1, f q.2.2))

def weightedQuadruple {Alpha : Type*} (weight : Alpha -> Nat)
    (q : (Alpha × Alpha) × (Alpha × Alpha)) : Nat :=
  weight q.1.1 * weight q.1.2 * weight q.2.1 * weight q.2.2

def quadrupleProduct {Alpha : Type*} (S : Finset Alpha) :
    Finset ((Alpha × Alpha) × (Alpha × Alpha)) :=
  Finset.product (Finset.product S S) (Finset.product S S)

def quadrupleProductOf {Alpha : Type*}
    (S0 S1 S2 S3 : Finset Alpha) :
    Finset ((Alpha × Alpha) × (Alpha × Alpha)) :=
  Finset.product (Finset.product S0 S1) (Finset.product S2 S3)

/-- A weighted quadruple family mapped into `U` has total weight at most
`L^4 |U|`, provided every one-coordinate fiber has weight at most `L`. -/
theorem weighted_quadruple_sum_le_fourth_power_mul_card
    {Alpha Beta : Type*} [DecidableEq Alpha] [DecidableEq Beta]
    (S : Finset Alpha)
    (Q : Finset ((Alpha × Alpha) × (Alpha × Alpha)))
    (U : Finset ((Beta × Beta) × (Beta × Beta)))
    (weight : Alpha -> Nat) (f : Alpha -> Beta) (L : Nat)
    (hQ : Q ⊆ quadrupleProduct S)
    (hMaps : Set.MapsTo (mappedQuadruple f) (Q : Set _) (U : Set _))
    (hLocal : forall b : Beta,
      (∑ x ∈ S.filter (fun y => f y = b), weight x) <= L) :
    (∑ q ∈ Q, weightedQuadruple weight q) <= L ^ 4 * U.card := by
  classical
  have hFiberwise := Finset.sum_fiberwise_eq_sum_filter Q U
    (mappedQuadruple f) (weightedQuadruple weight)
  have hAll : Q.filter (fun q => mappedQuadruple f q ∈ U) = Q := by
    apply Finset.filter_eq_self.mpr
    intro q hq
    exact hMaps hq
  rw [hAll] at hFiberwise
  rw [← hFiberwise]
  calc
    (∑ u ∈ U,
        ∑ q ∈ Q.filter (fun x => mappedQuadruple f x = u),
          weightedQuadruple weight q) <=
        ∑ _u ∈ U, L ^ 4 := by
      apply Finset.sum_le_sum
      intro u hu
      let S0 := S.filter (fun x => f x = u.1.1)
      let S1 := S.filter (fun x => f x = u.1.2)
      let S2 := S.filter (fun x => f x = u.2.1)
      let S3 := S.filter (fun x => f x = u.2.2)
      have hSubset :
          Q.filter (fun x => mappedQuadruple f x = u) ⊆
            quadrupleProductOf S0 S1 S2 S3 := by
        intro q hq
        rw [Finset.mem_filter] at hq
        have hqSRaw := hQ hq.1
        have hqSOuter :
            q.1 ∈ S.product S ∧ q.2 ∈ S.product S :=
          Finset.mem_product.mp (by
            simpa only [quadrupleProduct] using hqSRaw)
        have hqSLeft := Finset.mem_product.mp hqSOuter.1
        have hqSRight := Finset.mem_product.mp hqSOuter.2
        have hmap := hq.2
        have h00 : f q.1.1 = u.1.1 :=
          congrArg (fun v => v.1.1) hmap
        have h01 : f q.1.2 = u.1.2 :=
          congrArg (fun v => v.1.2) hmap
        have h20 : f q.2.1 = u.2.1 :=
          congrArg (fun v => v.2.1) hmap
        have h21 : f q.2.2 = u.2.2 :=
          congrArg (fun v => v.2.2) hmap
        unfold quadrupleProductOf
        apply Finset.mem_product.mpr
        constructor
        · apply Finset.mem_product.mpr
          exact ⟨Finset.mem_filter.mpr ⟨hqSLeft.1, h00⟩,
            Finset.mem_filter.mpr ⟨hqSLeft.2, h01⟩⟩
        · apply Finset.mem_product.mpr
          exact ⟨Finset.mem_filter.mpr ⟨hqSRight.1, h20⟩,
            Finset.mem_filter.mpr ⟨hqSRight.2, h21⟩⟩
      calc
        (∑ q ∈ Q.filter (fun x => mappedQuadruple f x = u),
            weightedQuadruple weight q) <=
            ∑ q ∈ quadrupleProductOf S0 S1 S2 S3,
              weightedQuadruple weight q :=
          Finset.sum_le_sum_of_subset hSubset
        _ = (∑ x ∈ S0, weight x) * (∑ x ∈ S1, weight x) *
              (∑ x ∈ S2, weight x) * (∑ x ∈ S3, weight x) := by
          have h01 :
              (∑ p ∈ S0.product S1, weight p.1 * weight p.2) =
                (∑ x ∈ S0, weight x) * (∑ x ∈ S1, weight x) := by
            calc
              (∑ p ∈ S0.product S1, weight p.1 * weight p.2) =
                  ∑ x ∈ S0, ∑ y ∈ S1, weight x * weight y := by
                exact Finset.sum_product S0 S1
                  (fun p => weight p.1 * weight p.2)
              _ = _ := (Finset.sum_mul_sum S0 S1 weight weight).symm
          have h23 :
              (∑ p ∈ S2.product S3, weight p.1 * weight p.2) =
                (∑ x ∈ S2, weight x) * (∑ x ∈ S3, weight x) := by
            calc
              (∑ p ∈ S2.product S3, weight p.1 * weight p.2) =
                  ∑ x ∈ S2, ∑ y ∈ S3, weight x * weight y := by
                exact Finset.sum_product S2 S3
                  (fun p => weight p.1 * weight p.2)
              _ = _ := (Finset.sum_mul_sum S2 S3 weight weight).symm
          unfold quadrupleProductOf
          calc
            (∑ q ∈ (S0.product S1).product (S2.product S3),
                weightedQuadruple weight q) =
                ∑ p ∈ S0.product S1, ∑ r ∈ S2.product S3,
                  weightedQuadruple weight (p, r) := by
              exact Finset.sum_product (S0.product S1) (S2.product S3)
                (fun q => weightedQuadruple weight q)
            _ = ∑ p ∈ S0.product S1, ∑ r ∈ S2.product S3,
                  (weight p.1 * weight p.2) *
                    (weight r.1 * weight r.2) := by
              apply Finset.sum_congr rfl
              intro p hp
              apply Finset.sum_congr rfl
              intro r hr
              dsimp only [weightedQuadruple]
              ring
            _ = (∑ p ∈ S0.product S1, weight p.1 * weight p.2) *
                  (∑ r ∈ S2.product S3, weight r.1 * weight r.2) :=
              (Finset.sum_mul_sum (S0.product S1) (S2.product S3)
                (fun p => weight p.1 * weight p.2)
                (fun r => weight r.1 * weight r.2)).symm
            _ = _ := by rw [h01, h23]; ring
        _ <= L * L * L * L := by
          gcongr <;> exact hLocal _
        _ = L ^ 4 := by ring
    _ = L ^ 4 * U.card := by simp [mul_comm]

#print axioms weighted_quadruple_sum_le_fourth_power_mul_card

end

end GafniTao

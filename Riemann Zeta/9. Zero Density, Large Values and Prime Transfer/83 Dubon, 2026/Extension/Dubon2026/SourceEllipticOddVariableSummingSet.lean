import Dubon2026.SourceEllipticOddVariableQuotient
import Dubon2026.SourceEllipticOddSummingStructure

/-! Transport the explicit odd quotient under actual variable changes.
The existing point-group additive equivalence transports the odd kernel;
coefficient and discriminant scaling transport its exact identity. This
discharges model-normalization inputs to the all-characteristic quotient
ellipticity needed by cyclic quotient products, inertia census and good
reduction for DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2.
Adapted from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2. Reuse the actual point
equivalence; no duplicate addition-law or point-map foundation is built. -/
namespace Dubon2026.SourceEllipticVelu.OddDiscriminant
open WeierstrassCurve Dubon2026.SourceEllipticVariableChange
noncomputable section
section SummingSetTransport

variable {K : Type*} [Field K] [DecidableEq K] (C : VariableChange K) (W : WeierstrassCurve K)


theorem variableChangeAddEquiv_symm_apply_odd (P : W.toAffine.Point) :
    (variableChangeAddEquiv C W.toAffine).symm P = vcInvFun C W.toAffine P := rfl

omit [DecidableEq K] in

theorem coordsOrZero_vcInvFun_of_ne_zero {P : W.toAffine.Point} (hP : P ≠ 0) :
    (coordsOrZero (vcInvFun C W.toAffine P)) = vcInvEmbedding C (coordsOrZero P) := by
  rcases P with _ | ⟨x, y, h⟩
  · exact absurd rfl hP
  · rfl

theorem variableChange_oddOrderSummingSet {Q : W.toAffine.Point} {n : ℕ}
    (hQ : addOrderOf Q = 2 * n + 1) :
    (oddOrderSummingSet (C • W)) ((variableChangeAddEquiv C W.toAffine).symm Q) n
      = ((oddOrderSummingSet W) Q n).map (vcInvEmbedding C) := by
  unfold oddOrderSummingSet
  rw [Finset.map_eq_image, Finset.image_image]
  refine Finset.image_congr fun k hk => ?_
  simp only [Finset.coe_Icc, Set.mem_Icc] at hk
  rw [← map_nsmul, variableChangeAddEquiv_symm_apply_odd, Function.comp_apply]
  refine coordsOrZero_vcInvFun_of_ne_zero C W ?_
  intro h0
  have hdvd : 2 * n + 1 ∣ k := hQ ▸ addOrderOf_dvd_of_nsmul_eq_zero h0
  have hle := Nat.le_of_dvd (by omega) hdvd
  omega


end SummingSetTransport

end
end Dubon2026.SourceEllipticVelu.OddDiscriminant

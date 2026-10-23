import Dubon2026.SourceEllipticVariableAddEquiv
import Dubon2026.SourceEllipticVeluQuotient

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
variable {K : Type*} [Field K]
section Embedding

variable (C : VariableChange K)

/-- Injective inverse coordinate change on the finite kernel pairs. -/
def vcInvEmbedding : K × K ↪ K × K where
  toFun P := (vcXInv C P.1, vcYInv C P.1 P.2)
  inj' := by
    intro P P' h
    have h1 : vcXInv C P.1 = vcXInv C P'.1 := congrArg Prod.fst h
    have h2 : vcYInv C P.1 P.2 = vcYInv C P'.1 P'.2 := congrArg Prod.snd h
    have hx : P.1 = P'.1 := by
      have := congrArg (vcX C) h1
      simpa only [vcX_vcXInv] using this
    have hy : P.2 = P'.2 := by
      have := congrArg (vcY C (vcXInv C P.1)) h2
      rw [vcY_vcYInv, hx] at this
      simpa only [vcY_vcYInv] using this
    exact Prod.ext hx hy

@[simp] theorem vcInvEmbedding_apply (P : K × K) :
    vcInvEmbedding C P = (vcXInv C P.1, vcYInv C P.1 P.2) := rfl

end Embedding


end
end Dubon2026.SourceEllipticVelu.OddDiscriminant

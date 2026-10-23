import Dubon2026.SourceEllipticOddCharTwoInvariants

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
section Sums

variable {F : Type*} [Field F] [DecidableEq F] (h2 : (2 : F) = 0) (V : WeierstrassCurve F)
  (ha₁ : V.a₁ = 1) (ha₃ : V.a₃ = 0) (ha₄ : V.a₄ = 0)

omit [DecidableEq F] in
include h2 ha₁ ha₃ ha₄ in

theorem veluTSum_V (S : Finset (F × F)) :
    veluTSum V S = ∑ P ∈ S, P.1 := by
  unfold veluTSum
  exact Finset.sum_congr rfl fun P _ => veluT_V h2 V ha₁ ha₃ ha₄ P.1 P.2

omit [DecidableEq F] in
include h2 ha₁ ha₃ ha₄ in

theorem veluWSum_V (S : Finset (F × F)) (hS : ∀ P ∈ S, V.toAffine.Equation P.1 P.2) :
    veluWSum V S = 0 := by
  unfold veluWSum
  exact Finset.sum_eq_zero fun P hP => veluW_V h2 V ha₁ ha₃ ha₄ (hS P hP)

omit [DecidableEq F] in
include h2 ha₁ ha₃ ha₄ in

theorem prod_veluU_V (S : Finset (F × F)) (hS : ∀ P ∈ S, V.toAffine.Equation P.1 P.2) :
    ∏ P ∈ S, veluU V P.1 P.2 = (∏ P ∈ S, P.1) ^ 2 := by
  rw [← Finset.prod_pow]
  exact Finset.prod_congr rfl fun P hP => veluU_V h2 V ha₁ ha₃ ha₄ (hS P hP)

end Sums

section QuotientΔ

variable {F : Type*} [Field F] (h2 : (2 : F) = 0) (V : WeierstrassCurve F)
  (ha₁ : V.a₁ = 1) (ha₃ : V.a₃ = 0) (ha₄ : V.a₄ = 0)

include h2 ha₁ ha₃ ha₄ in

theorem veluQuotient_coeffs (S : Finset (F × F))
    (hW : veluWSum V S = 0) :
    (veluQuotient V S).a₁ = 1 ∧ (veluQuotient V S).a₃ = 0 ∧
    (veluQuotient V S).a₄ = veluTSum V S ∧
    (veluQuotient V S).a₆ = V.a₆ + veluTSum V S := by
  refine ⟨by rw [veluQuotient_a₁, ha₁], by rw [veluQuotient_a₃, ha₃], ?_, ?_⟩
  · rw [veluQuotient_a₄, ha₄]
    linear_combination (-(3 : F)) * veluTSum V S * h2
  · rw [veluQuotient_a₆, hW, b₂_V h2 V ha₁]
    linear_combination (-veluTSum V S) * h2

include h2 ha₁ ha₃ ha₄ in

theorem Δ_veluQuotient_V (S : Finset (F × F))
    (hS : ∀ P ∈ S, V.toAffine.Equation P.1 P.2) :
    (veluQuotient V S).Δ = V.a₆ + (∑ P ∈ S, P.1) + (∑ P ∈ S, P.1) ^ 2 := by
  set t := ∑ P ∈ S, P.1 with ht
  have hW := veluWSum_V h2 V ha₁ ha₃ ha₄ S hS
  have hT := veluTSum_V h2 V ha₁ ha₃ ha₄ S
  obtain ⟨h1, h3, h4, h6⟩ := veluQuotient_coeffs h2 V ha₁ ha₃ ha₄ S hW
  rw [hT] at h4 h6
  rw [Δ_of_a₁_one_a₃_zero h2 (veluQuotient V S) h1 h3, h4, h6, ← ht]

end QuotientΔ


end
end Dubon2026.SourceEllipticVelu.OddDiscriminant.CharTwo

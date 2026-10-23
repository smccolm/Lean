import Dubon2026.SourceEllipticOddVariableCoefficients

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
section Sums

variable (C : VariableChange K) (W : WeierstrassCurve K) (S : Finset (K × K))

theorem variableChange_veluTSum :
    (veluTSum (C • W)) (S.map (vcInvEmbedding C))
      = ((C.u⁻¹ : Kˣ) : K) ^ 4 * (veluTSum W) S := by
  rw [veluTSum, veluTSum, Finset.sum_map, Finset.mul_sum]
  exact Finset.sum_congr rfl fun P _ => by
    simpa only [vcInvEmbedding_apply] using variableChange_veluT C W P.1 P.2

theorem variableChange_veluWSum :
    (veluWSum (C • W)) (S.map (vcInvEmbedding C))
      = ((C.u⁻¹ : Kˣ) : K) ^ 6 * ((veluWSum W) S - C.r * (veluTSum W) S) := by
  rw [veluWSum, Finset.sum_map]
  rw [show (veluWSum W) S - C.r * (veluTSum W) S
      = ∑ P ∈ S, ((veluW W) P.1 P.2 - C.r * (veluT W) P.1 P.2) by
    rw [veluWSum, veluTSum, Finset.mul_sum, ← Finset.sum_sub_distrib]]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun P _ => by
    simpa only [vcInvEmbedding_apply] using variableChange_veluW C W P.1 P.2

end Sums

section VarChangeQuotient

variable {K : Type*} [Field K] (C : VariableChange K) (W : WeierstrassCurve K)
  (S : Finset (K × K))

theorem variableChange_veluQuotient :
    (veluQuotient (C • W)) (S.map (vcInvEmbedding C)) = C • (veluQuotient W) S := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  have hT := variableChange_veluTSum C W S
  have hW := variableChange_veluWSum C W S
  ext
  · simp only [veluQuotient_a₁, variableChange_a₁]
  · simp only [veluQuotient_a₁, veluQuotient_a₂, variableChange_a₂]
  · simp only [veluQuotient_a₁, veluQuotient_a₃, variableChange_a₃]
  · simp only [veluQuotient_a₄, variableChange_a₄, veluQuotient_a₁, veluQuotient_a₂,
      veluQuotient_a₃, hT, Units.val_inv_eq_inv_val]
    field_simp
    ring
  · simp only [veluQuotient_a₆, variableChange_a₆, veluQuotient_a₁, veluQuotient_a₂,
      veluQuotient_a₃, veluQuotient_a₄, hT, hW, b₂, variableChange_a₁, variableChange_a₂,
      Units.val_inv_eq_inv_val]
    field_simp
    ring

theorem variableChange_veluQuotient_Δ :
    ((veluQuotient (C • W)) (S.map (vcInvEmbedding C))).Δ
      = ((C.u⁻¹ : Kˣ) : K) ^ 12 * ((veluQuotient W) S).Δ := by
  rw [variableChange_veluQuotient, variableChange_Δ]

end VarChangeQuotient

section VarChangeProdU

variable {K : Type*} [Field K] (C : VariableChange K) (W : WeierstrassCurve K)
  (S : Finset (K × K))

theorem variableChange_prod_veluU :
    ∏ P ∈ S.map (vcInvEmbedding C), (veluU (C • W)) P.1 P.2
      = ((C.u⁻¹ : Kˣ) : K) ^ (6 * S.card) * ∏ P ∈ S, (veluU W) P.1 P.2 := by
  rw [Finset.prod_map, pow_mul, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun P _ => by
    simpa only [vcInvEmbedding_apply] using variableChange_veluU C W P.1 P.2

end VarChangeProdU

section IdentityTransport

variable {K : Type*} [Field K] (C : VariableChange K) (W : WeierstrassCurve K)
  (S : Finset (K × K)) (n : ℕ)

theorem identity_variableChange_iff (hcard : S.card = n) :
    ((veluQuotient (C • W)) (S.map (vcInvEmbedding C))).Δ *
        (∏ P ∈ S.map (vcInvEmbedding C), (veluU (C • W)) P.1 P.2) ^ 4
      = (C • W).Δ ^ (2 * n + 1) ↔
    ((veluQuotient W) S).Δ * (∏ P ∈ S, (veluU W) P.1 P.2) ^ 4 = W.Δ ^ (2 * n + 1) := by
  have hu' : ((C.u⁻¹ : Kˣ) : K) ≠ 0 := C.u⁻¹.ne_zero
  have hfac : ((C.u⁻¹ : Kˣ) : K) ^ (12 * (2 * n + 1)) ≠ 0 := pow_ne_zero _ hu'
  rw [variableChange_veluQuotient_Δ, variableChange_prod_veluU, variableChange_Δ, hcard]
  rw [show ((C.u⁻¹ : Kˣ) : K) ^ 12 * ((veluQuotient W) S).Δ *
        (((C.u⁻¹ : Kˣ) : K) ^ (6 * n) * ∏ P ∈ S, (veluU W) P.1 P.2) ^ 4
      = ((C.u⁻¹ : Kˣ) : K) ^ (12 * (2 * n + 1)) *
        (((veluQuotient W) S).Δ * (∏ P ∈ S, (veluU W) P.1 P.2) ^ 4) from by ring,
     show (((C.u⁻¹ : Kˣ) : K) ^ 12 * W.Δ) ^ (2 * n + 1)
      = ((C.u⁻¹ : Kˣ) : K) ^ (12 * (2 * n + 1)) * W.Δ ^ (2 * n + 1) from by ring]
  exact mul_right_inj' hfac


end IdentityTransport

end
end Dubon2026.SourceEllipticVelu.OddDiscriminant

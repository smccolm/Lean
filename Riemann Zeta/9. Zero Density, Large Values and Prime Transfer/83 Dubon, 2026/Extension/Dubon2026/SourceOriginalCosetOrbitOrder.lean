import Dubon2026.SourceOriginalCosetFiber

/-! DUB-17/18 -> numerical modular genus -> exceptional fiber counts.
The orbit of a level coset under the full point stabilizer has size equal
to the actual original j-fiber order. Conjugating the coset stabilizer
identifies it with the genuine Gamma0 point stabilizer, so the native
orbit-stabilizer theorem and proved analytic ramification give the result.
-/
namespace Dubon2026.SourceFunctionField.FiberOrbits
noncomputable section
open UpperHalfPlane
open scoped MatrixGroups StabilizerCharacter

/-- Conjugation identifies the actual coset stabilizer with the point stabilizer. -/
def cosetStabilizerEquiv (N : ℕ) (τ : ℍ) (g : SL(2, ℤ)) :
    MulAction.stabilizer (MulAction.stabilizer SL(2, ℤ) τ) (g : X N) ≃
      MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) (g⁻¹ • τ) where
  toFun k := ⟨⟨g⁻¹ * ((k : MulAction.stabilizer SL(2, ℤ) τ) : SL(2, ℤ)) * g, by
    have hk : (g : X N) =
        ((((k : MulAction.stabilizer SL(2, ℤ) τ) : SL(2, ℤ)) * g : SL(2, ℤ)) : X N) := k.2.symm
    have hm := QuotientGroup.eq.mp hk
    simpa only [mul_assoc] using hm⟩, by
    change (g⁻¹ * ((k : MulAction.stabilizer SL(2, ℤ) τ) : SL(2, ℤ)) * g) • (g⁻¹ • τ) = _
    have hk : ((k : MulAction.stabilizer SL(2, ℤ) τ) : SL(2, ℤ)) • τ = τ :=
      (k : MulAction.stabilizer SL(2, ℤ) τ).2
    rw [mul_smul, mul_smul, smul_inv_smul, hk]⟩
  invFun δ := ⟨⟨g * ((δ : CongruenceSubgroup.Gamma0 N) : SL(2, ℤ)) * g⁻¹, by
    change (g * ((δ : CongruenceSubgroup.Gamma0 N) : SL(2, ℤ)) * g⁻¹) • τ = τ
    have hδ : ((δ : CongruenceSubgroup.Gamma0 N) : SL(2, ℤ)) • (g⁻¹ • τ) = g⁻¹ • τ := δ.2
    rw [mul_smul, mul_smul, hδ, smul_inv_smul]⟩, by
    change (((g * ((δ : CongruenceSubgroup.Gamma0 N) : SL(2, ℤ)) * g⁻¹) * g : SL(2, ℤ)) : X N) = g
    symm
    apply QuotientGroup.eq.mpr
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using
      (δ : CongruenceSubgroup.Gamma0 N).2⟩
  left_inv k := by
    apply Subtype.ext
    apply Subtype.ext
    simp [mul_assoc]
  right_inv δ := by
    apply Subtype.ext
    apply Subtype.ext
    simp [mul_assoc]

theorem card_coset_orbit_eq_place_order (N : ℕ) [NeZero N] (τ : ℍ) (g : SL(2, ℤ)) :
    (Nat.card (MulAction.orbit (MulAction.stabilizer SL(2, ℤ) τ) (g : X N)) : ℤ) =
      (point N τ g).1.ord (jOver N ℂ -
        algebraMap ℂ (modularFunctionFieldOver N ℂ) (JMultiplicity.jf τ)) := by
  let e := originalAnalyticRamification N (g⁻¹ • τ)
  have he : 0 < e := originalAnalyticRamification_pos N (g⁻¹ • τ)
  have hcard := Nat.card_congr
    (MulAction.orbitProdStabilizerEquivGroup (MulAction.stabilizer SL(2, ℤ) τ) (g : X N))
  rw [Nat.card_prod, Nat.card_congr (cosetStabilizerEquiv N τ g),
    ← original_two_mul_ramification_eq_stabilizer_card N (g⁻¹ • τ)] at hcard
  have hmul : (Nat.card (MulAction.orbit (MulAction.stabilizer SL(2, ℤ) τ) (g : X N)) * e) * 2 =
      Nat.card (MulAction.stabilizer SL(2, ℤ) τ) := by
    dsimp only [e]
    nlinarith [hcard]
  have hdiv := congrArg (fun n : ℕ => n / 2) hmul
  dsimp only at hdiv
  rw [Nat.mul_div_cancel _ two_pos] at hdiv
  have horder := original_analytic_j_multiplicity N (g⁻¹ • τ)
  rw [JMultiplicity.natCard_stabilizer_smul, JMultiplicity.jf_smul] at horder
  have hi : (e : ℤ) * (point N τ g).1.ord (jOver N ℂ -
      algebraMap ℂ (modularFunctionFieldOver N ℂ) (JMultiplicity.jf τ)) =
      ((Nat.card (MulAction.stabilizer SL(2, ℤ) τ) / 2 : ℕ) : ℤ) :=
    WithTop.coe_injective horder
  apply mul_right_cancel₀ (Int.natCast_pos.mpr he).ne'
  calc
    (Nat.card (MulAction.orbit (MulAction.stabilizer SL(2, ℤ) τ) (g : X N)) : ℤ) * e =
        ((Nat.card (MulAction.stabilizer SL(2, ℤ) τ) / 2 : ℕ) : ℤ) := by exact_mod_cast hdiv
    _ = (point N τ g).1.ord (jOver N ℂ -
        algebraMap ℂ (modularFunctionFieldOver N ℂ) (JMultiplicity.jf τ)) * e := by
      rw [← hi, mul_comm]

end
end Dubon2026.SourceFunctionField.FiberOrbits

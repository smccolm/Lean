import Dubon2026.SourceGammaOnePlusMinus
import Dubon2026.SourceGammaOneOrbitCounting
import Dubon2026.SourceGammaOneRamificationIsolation

/-! DUB-17/18 -> actual Gamma1 global charts -> exact elliptic ramification.
Compare actual j-fiber orders with relative stabilizer indices. The
existing j multiplicity and actual uniformizer divisibility give the
termwise bound; equality gives the required exact ramification formula.
The subsequent weighted fiber sum must still establish equality. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane SourceCurve
open scoped MatrixGroups StabilizerCharacter SubgroupStabilizer

theorem analytic_j_multiplicity {Γ : Subgroup SL(2, ℤ)}
    (hT : ModularGroup.T ∈ Γ) (τ : ℍ) :
    (analyticRamification hT τ : ℤ) * (analyticPlace hT τ).ord
      (jCoordinateOver Γ ℂ - algebraMap ℂ (functionFieldOver Γ ℂ) (JMultiplicity.jf τ)) =
        ((Nat.card (MulAction.stabilizer SL(2, ℤ) τ) / 2 : ℕ) : ℤ) := by
  have hx : jCoordinateOver Γ ℂ -
      algebraMap ℂ (functionFieldOver Γ ℂ) (JMultiplicity.jf τ) ≠ 0 :=
    Place.transcendental_sub_algebraMap_ne_zero (transcendental_jCoordinateOver Γ ℂ) _
  have h := analyticPlace_order hT τ _ hx
  rw [analyticOrder_j_sub hT] at h
  exact WithTop.coe_injective (h.symm.trans (JMultiplicity.main τ))

theorem analytic_j_order_le_relative_index {Γ : Subgroup SL(2, ℤ)}
    (hT : ModularGroup.T ∈ Γ) (τ : ℍ) :
    0 < (analyticPlace hT τ).ord
      (jCoordinateOver Γ ℂ - algebraMap ℂ (functionFieldOver Γ ℂ) (JMultiplicity.jf τ)) ∧
    (analyticPlace hT τ).ord
      (jCoordinateOver Γ ℂ - algebraMap ℂ (functionFieldOver Γ ℂ) (JMultiplicity.jf τ)) ≤
        ((plusMinus Γ).relIndex (MulAction.stabilizer SL(2, ℤ) τ) : ℤ) ∧
    ((analyticPlace hT τ).ord
      (jCoordinateOver Γ ℂ - algebraMap ℂ (functionFieldOver Γ ℂ) (JMultiplicity.jf τ)) =
        ((plusMinus Γ).relIndex (MulAction.stabilizer SL(2, ℤ) τ) : ℤ) →
      2 * analyticRamification hT τ = Nat.card (MulAction.stabilizer (plusMinus Γ) τ)) := by
  let A : ℤ := (analyticPlace hT τ).ord
    (jCoordinateOver Γ ℂ - algebraMap ℂ (functionFieldOver Γ ℂ) (JMultiplicity.jf τ))
  let B : ℕ := (plusMinus Γ).relIndex (MulAction.stabilizer SL(2, ℤ) τ)
  let s : ℕ := Nat.card (MulAction.stabilizer (plusMinus Γ) τ)
  let s₁ : ℕ := Nat.card (MulAction.stabilizer SL(2, ℤ) τ)
  let e := analyticRamification hT τ
  have hA : 0 < A := analyticPlace_j_sub_pos hT τ
  have hAe : A * (e : ℤ) = ((s₁ / 2 : ℕ) : ℤ) := by
    rw [mul_comm]
    exact analytic_j_multiplicity hT τ
  have hAe2 : 2 * (A * (e : ℤ)) = (s₁ : ℤ) := by
    rw [hAe]
    have h : 2 * (s₁ / 2) = s₁ :=
      Nat.mul_div_cancel' (StabilizerCharacter.two_dvd_card_stabilizer τ)
    exact_mod_cast h
  have hBs : (B : ℤ) * (s : ℤ) = (s₁ : ℤ) := by
    exact_mod_cast OrbitCounting.relIndex_stabilizer_mul_card_stabilizer (plusMinus Γ) τ
  obtain ⟨k, hk⟩ := plusMinus_stabilizer_card_dvd_two_mul_ramification hT τ
  have hk' : (2 : ℤ) * (e : ℤ) = (s : ℤ) * (k : ℤ) := by exact_mod_cast hk
  have hs : (0 : ℤ) < s := by
    exact_mod_cast (Nat.card_pos (α := MulAction.stabilizer (plusMinus Γ) τ))
  have he : (0 : ℤ) < e := by exact_mod_cast analyticRamification_pos hT τ
  have hkpos : (0 : ℤ) < k := by
    by_contra h
    have hkn : (k : ℤ) ≤ 0 := not_lt.mp h
    have : (s : ℤ) * k ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs.le hkn
    linarith
  have hAk : A * (k : ℤ) = (B : ℤ) := by
    apply mul_right_cancel₀ hs.ne'
    calc A * (k : ℤ) * s = A * ((s : ℤ) * k) := by ring
      _ = A * (2 * (e : ℤ)) := by rw [hk']
      _ = 2 * (A * (e : ℤ)) := by ring
      _ = (s₁ : ℤ) := hAe2
      _ = (B : ℤ) * s := hBs.symm
  refine ⟨hA, ?_, ?_⟩
  · change A ≤ (B : ℤ)
    nlinarith
  · intro hAB
    change A = (B : ℤ) at hAB
    have hk1 : (k : ℤ) = 1 := by
      apply mul_left_cancel₀ hA.ne'
      rw [hAk, hAB, mul_one]
    have : (2 : ℤ) * (e : ℤ) = s := by rw [hk', hk1, mul_one]
    exact_mod_cast this

end
end Dubon2026.SourceFunctionField.GammaOne

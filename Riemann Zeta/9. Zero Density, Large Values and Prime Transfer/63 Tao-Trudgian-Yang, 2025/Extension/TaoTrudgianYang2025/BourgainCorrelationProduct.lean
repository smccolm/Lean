import TaoTrudgianYang2025.BourgainRelativeLevels

/-!
# The finite relative-multiplicity/correlation product lower bound

Actual large local mass and the actual fourth-moment measure bound force
a lower bound on the product of relative multiplicity and squared correlation.
This retains the finite logarithmic losses preceding source (4.37).
-/

open MeasureTheory
open scoped Classical

noncomputable section

namespace TaoTrudgianYang2025

/-- The actual component mass and fourth moment yield the relative/correlation
product inequality. Only the regridded multiplicity upper comparison is supplied. -/
theorem BourgainComponentBand.relative_correlation_lower
    {N T B C τ α ε : ℝ} {W : Finset ℝ} {j q : ℕ}
    (hband : BourgainComponentBand N T B C τ α ε W j q)
    (hN : 0 < N) {d : ℝ} (hrel : (2 : ℝ)^j ≤ 2*d*(W.card : ℝ)) :
    let H := N^(ε/8)
    let U := T+H+1
    let a := N^(-bourgainSharedFloorExponent α τ ε)
    let J := bourgainZetaBandCount B U a
    let r := bourgainZetaBandCorrelation (bourgainDifferenceLevel W j) H U (a*(2 : ℝ)^q)
    N^(-2*α)*N^τ <
      1024*(Nat.log 2 W.card+1 : ℕ)^2*(J : ℝ)^2*C*U^(1+ε)*d*r^2 := by
  rcases hband with ⟨_, _, hpow, _, _, _, _, hV, _, hμ, hm, h4,
    _, _, _, heq, _⟩
  let R := (W.card : ℝ)
  let Q := (2 : ℝ)^j
  let D := bourgainDifferenceLevel W j
  let H := N^(ε/8)
  let U := T+H+1
  let a := N^(-bourgainSharedFloorExponent α τ ε)
  let J := bourgainZetaBandCount B U a
  let V := a*(2 : ℝ)^q
  let r := bourgainZetaBandCorrelation D H U V
  let μ := volume.real (bourgainZetaBand U V)
  let M := bourgainZetaBandMass D H U V
  let Z := (Nat.log 2 W.card+1 : ℕ)
  let K := 2*(Z : ℝ)*(2 : ℝ)^(j+1)*(J : ℝ)*(2*V)^2
  have hR : 0 < R := by
    dsimp only [R]
    exact_mod_cast (Nat.pow_pos (by norm_num : 0 < (2 : ℕ))).trans_le hpow
  have hQ : 0 < Q := by dsimp only [Q]; positivity
  have hD : (0 : ℝ) ≤ D.card := by positivity
  have hμ₀ : 0 ≤ μ := le_of_lt hμ
  have hV₀ : 0 ≤ V := le_of_lt hV
  have hmass : N^(-α)*R^(3/2 : ℝ)*N^(τ/2) < K*M := hm
  have hmass0 : 0 ≤ N^(-α)*R^(3/2 : ℝ)*N^(τ/2) := by positivity
  have hs := (sq_lt_sq₀ hmass0 (hmass0.trans hmass.le)).mpr hmass
  have hRpow : (R^(3/2 : ℝ))^2 = R^3 := by
    rw [← Real.rpow_mul_natCast hR.le]
    norm_num
  have hαpow : (N^(-α))^2 = N^(-2*α) := by
    rw [← Real.rpow_mul_natCast hN.le]
    congr 1
    norm_num
    ring
  have hτpow : (N^(τ/2))^2 = N^τ := by
    rw [← Real.rpow_mul_natCast hN.le]
    congr 1
    norm_num
  have hleft : (N^(-α)*R^(3/2 : ℝ)*N^(τ/2))^2 = N^(-2*α)*R^3*N^τ := by
    rw [mul_pow, mul_pow, hRpow, hαpow, hτpow]
  have hM : M^2 = r^2*μ*(D.card : ℝ) := by
    change M = r*Real.sqrt μ*Real.sqrt (D.card : ℝ) at heq
    rw [heq, mul_pow, mul_pow, Real.sq_sqrt hμ₀, Real.sq_sqrt hD]
  have hK : K = 16*(Z : ℝ)*Q*(J : ℝ)*V^2 := by
    dsimp only [K, Q]
    rw [pow_succ]
    ring
  have hright : (K*M)^2 =
      256*(Z : ℝ)^2*(J : ℝ)^2*r^2*(V^4*μ)*(Q^2*(D.card : ℝ)) := by
    rw [mul_pow, hK, hM]
    ring
  have hQD : Q*(D.card : ℝ) ≤ 2*R^2 := by
    dsimp only [Q, D, R]
    exact_mod_cast bourgainDifferenceLevel_card_le W j
  have hQ2D : Q^2*(D.card : ℝ) ≤ 4*d*R^3 := by
    calc
      _ = Q*(Q*(D.card : ℝ)) := by ring
      _ ≤ Q*(2*R^2) := mul_le_mul_of_nonneg_left hQD hQ.le
      _ ≤ (2*d*R)*(2*R^2) := mul_le_mul_of_nonneg_right hrel (by positivity)
      _ = _ := by ring
  have hfourth : V^4*μ ≤ C*U^(1+ε) := h4
  have hY : 0 ≤ C*U^(1+ε) := (mul_nonneg (pow_nonneg hV₀ _) hμ₀).trans hfourth
  have hF : 0 ≤ 256*(Z : ℝ)^2*(J : ℝ)^2*r^2 := by positivity
  have hupper : (K*M)^2 ≤
      1024*(Z : ℝ)^2*(J : ℝ)^2*C*U^(1+ε)*d*r^2*R^3 := by
    rw [hright]
    calc
      _ ≤ 256*(Z : ℝ)^2*(J : ℝ)^2*r^2*(C*U^(1+ε))*(Q^2*(D.card : ℝ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfourth hF) (by positivity)
      _ ≤ 256*(Z : ℝ)^2*(J : ℝ)^2*r^2*(C*U^(1+ε))*(4*d*R^3) :=
        mul_le_mul_of_nonneg_left hQ2D (mul_nonneg hF hY)
      _ = _ := by ring
  rw [hleft] at hs
  have hfinal : (N^(-2*α)*N^τ)*R^3 <
      (1024*(Z : ℝ)^2*(J : ℝ)^2*C*U^(1+ε)*d*r^2)*R^3 := by
    convert hs.trans_le hupper using 1
    ring
  exact (mul_lt_mul_iff_of_pos_right (pow_pos hR 3)).mp hfinal

end TaoTrudgianYang2025

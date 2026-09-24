import TaoTrudgianYang2025.ClassicalReflectedSourceFourier

/-!
# Subpower Fourier radius for actual normalized reflected blocks

For 0 <= sigma, N <= M and retained threshold L >= 1, the right-endpoint
normalization cancels the growing fixed-line weight in the defining base
of the Fourier radius. The derivative order is chosen before M,N,L,T.
-/

noncomputable section
open scoped FourierTransform
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

theorem classicalReflectedFourier_source_base_le
    (M N k : ℕ) (sigma L : ℝ)
    (hM : 0 < M) (hNM : N ≤ M) (hsigma : 0 ≤ sigma)
    (hL : 1 ≤ L) (hk : 1 < k) :
    1 + 4 * ((N : ℝ) ^ (-(-sigma)) *
        (Finset.Ioc N (min (2*N) M)).card) *
          SchwartzMap.seminorm ℝ k 0
            (𝓕 (classicalTypeILogProfileSchwartz (-sigma))) /
        (((k : ℝ)-1) * ((M : ℝ)^sigma * L)) ≤
      1 + (4 * SchwartzMap.seminorm ℝ k 0
        (𝓕 (classicalTypeILogProfileSchwartz (-sigma))) / ((k : ℝ)-1)) * N := by
  let a : ℝ := (M : ℝ)^sigma
  let b : ℝ := (N : ℝ)^sigma
  let c : ℝ := (Finset.Ioc N (min (2*N) M)).card
  let C : ℝ := SchwartzMap.seminorm ℝ k 0
    (𝓕 (classicalTypeILogProfileSchwartz (-sigma)))
  let q : ℝ := (k : ℝ)-1
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have ha : 0 < a := Real.rpow_pos_of_pos hMpos _
  have hb : 0 ≤ b := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hc : 0 ≤ c := Nat.cast_nonneg _
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hq : 0 < q := by
    have hkReal : (1 : ℝ) < k := by exact_mod_cast hk
    dsimp [q]
    linarith
  have hba : b ≤ a :=
    Real.rpow_le_rpow (Nat.cast_nonneg N) (by exact_mod_cast hNM) hsigma
  have hcardNat : (Finset.Ioc N (min (2*N) M)).card ≤ N := by
    simp only [Nat.card_Ioc]
    omega
  have hcN : c ≤ (N : ℝ) := by
    change ((Finset.Ioc N (min (2*N) M)).card : ℝ) ≤ (N : ℝ)
    exact_mod_cast hcardNat
  have haL : a ≤ a*L := by nlinarith
  have hden : q*a ≤ q*(a*L) := mul_le_mul_of_nonneg_left haL hq.le
  have hnum : 4*(b*c)*C ≤ 4*(a*(N : ℝ))*C := by gcongr
  simp only [neg_neg]
  change 1 + 4*(b*c)*C/(q*(a*L)) ≤ 1 + (4*C/q)*(N : ℝ)
  apply add_le_add le_rfl
  calc
    4*(b*c)*C/(q*(a*L)) ≤ 4*(a*(N : ℝ))*C/(q*(a*L)) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ 4*(a*(N : ℝ))*C/(q*a) :=
      div_le_div_of_nonneg_left (by positivity) (mul_pos hq ha) hden
    _ = _ := by field_simp

theorem exists_order_eventually_classicalReflectedFourierRadius_le_rpow
    (sigma theta : ℝ) (hsigma : 0 ≤ sigma) (htheta : 0 < theta) :
    ∃ k : ℕ, 1 < k ∧ ∀ᶠ T : ℝ in Filter.atTop,
      ∀ M N : ℕ, ∀ L : ℝ, 0 < M → N ≤ M → (N : ℝ) ≤ T → 1 ≤ L →
        classicalTypeIFourierRadius M N k (-sigma) ((M : ℝ)^sigma*L) ≤
          T^theta := by
  let k : ℕ := Nat.ceil (2/theta)+2
  have hk : 1 < k := by dsimp [k]; omega
  have hkReal : (1 : ℝ) < k := by exact_mod_cast hk
  have horder : 2 ≤ theta*((k : ℝ)-1) := by
    have hceil : 2/theta ≤ (Nat.ceil (2/theta) : ℝ) := Nat.le_ceil _
    have hmul := (div_le_iff₀ htheta).mp hceil
    dsimp [k]
    push_cast
    nlinarith
  let C : ℝ := 4 * SchwartzMap.seminorm ℝ k 0
    (𝓕 (classicalTypeILogProfileSchwartz (-sigma))) / ((k : ℝ)-1)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨k,hk,?_⟩
  filter_upwards [Filter.eventually_ge_atTop (max 1 (1+C))] with T hT
  intro M N L hM hNM hNT hL
  have hTone : 1 ≤ T := (le_max_left _ _).trans hT
  have hCT : 1+C ≤ T := (le_max_right _ _).trans hT
  have hTnonneg : 0 ≤ T := zero_le_one.trans hTone
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hV : 0 < (M : ℝ)^sigma*L :=
    mul_pos (Real.rpow_pos_of_pos hMpos _) (zero_lt_one.trans_le hL)
  apply classicalTypeIFourierRadius_le_rpow_of_base_growth
    M N k (-sigma) ((M : ℝ)^sigma*L) T 2 theta hV hk hTone horder
  have hbase := classicalReflectedFourier_source_base_le M N k sigma L
    hM hNM hsigma hL hk
  calc
    _ ≤ 1+C*(N : ℝ) := hbase
    _ ≤ 1+C*T := add_le_add le_rfl (mul_le_mul_of_nonneg_left hNT hC)
    _ ≤ (1+C)*T := by nlinarith
    _ ≤ T*T := mul_le_mul_of_nonneg_right hCT hTnonneg
    _ = _ := by rw [Real.rpow_two, pow_two]

end TaoTrudgianYang2025

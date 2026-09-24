import TaoTrudgianYang2025.ClassicalDirectSourceThreshold

/-!
# Normalized all-index direct interior source factory

The actual smooth block yields two physical dyadic lengths, normalized
coefficient-one sums, and a subpower ordinate shift on the original index
type. The Fourier order precedes the source line; no separation subset is
selected and the full-source additive energy is retained.
-/

noncomputable section
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

theorem dirichletPoly_coefficientOne_eq_sum_phase (N : ℕ) (t : ℝ) :
    dirichletPoly N (fun _ => 1) t =
      ∑ n ∈ Finset.Ioc N (2*N), dirichletPhase n t := by
  unfold dirichletPoly dyadicInterval
  apply Finset.sum_congr rfl
  intro n _hn
  simp only [one_mul,dirichletPhase]
  congr 1
  ring

theorem exists_order_eventually_interior_source_normalized_two_dyadic_family
    (a d delta : ℝ) (ha : 0 < a) (hd : 0 < d) (hdelta : 0 < delta) :
    ∃ k : ℕ, 1 < k ∧ ∀ s u : ℝ, 0 ≤ s → u ≤ 1 → u ≤ a*delta/2 →
      ∀ᶠ T : ℝ in Filter.atTop,
        let Y := ⌊T^a⌋₊
        let A := ⌊sharpZetaCutoff T⌋₊
        ∀ {ι : Type*} [Fintype ι] (r : ℕ) (W : ι → ℝ),
          let Q := 2^r*Y
          2 ≤ r → ((Y+1 : ℕ) : ℝ) ≤ (Q : ℝ)/2 → 2*Q ≤ A →
          2 ≤ typeILogarithmicScale T Q →
          (∀ x, ((3/4)*(T^(-u)/2))/(Nat.clog 2 A+1 : ℕ) ≤
            ‖typeISourceSmoothBlock Y A r s (W x)‖) →
          ∃ W' : ι → ℝ, ∃ label : ι → Fin 2,
            (∀ x, |W' x-W x| ≤ 2*Real.pi*T^d) ∧
            (∀ x, let N := classicalDirectDyadicLength Q (label x)
              1 < N ∧ (N : ℝ) ≤ T ∧ T^a ≤ (N : ℝ) ∧
                2 ≤ typeILogarithmicScale T N ∧ typeILogarithmicScale T N ≤ 1/a ∧
                (N : ℝ)^(s-delta) ≤
                  ‖∑ n ∈ Finset.Ioc N (2*N), dirichletPhase n (W' x)‖) ∧
            approximateAdditiveEnergyOf 1 W ≤
              (4*Nat.ceil (1+4*(2*Real.pi*T^d))+6)*approximateAdditiveEnergyOf 1 W' := by
  obtain ⟨k,hk,hRadius⟩ := exists_order_eventually_classicalDirectFourierRadius_le_rpow d hd
  refine ⟨k,hk,?_⟩
  intro s u hs huOne huDelta
  have hPowerEvent := (tendsto_rpow_atTop ha).eventually
    (Filter.eventually_ge_atTop (2 : ℝ))
  filter_upwards [hRadius s u hs huOne,
    eventually_classicalDirect_normalized_sourceThreshold_lower s a delta u hs ha hdelta huDelta,
    hPowerEvent,Filter.eventually_ge_atTop (8 : ℝ)] with T hRadiusT hThreshold hPower hT
  dsimp only
  intro ι _ r W hr hLower hUpper hScale hLarge
  let Y := ⌊T^a⌋₊
  let A := ⌊sharpZetaCutoff T⌋₊
  let Q := 2^r*Y
  let V := ((3/4)*(T^(-u)/2))/(Nat.clog 2 A+1 : ℕ)
  let f := typeIInteriorLogProfileSchwartz s
  let R := finiteFourierRadius f (Finset.Ioc (Q/2) (2*Q)) k ((Q : ℝ)^(-s)) V
  have hYTwo : 2 ≤ Y := Nat.le_floor hPower
  have hY : 0 < Y := by omega
  have hTOne : 1 ≤ T := by linarith
  have hTPos : 0 < T := by linarith
  have hV : 0 < V := by dsimp [V]; positivity
  have hGeometry (c : Fin 2) := classicalDirectDyadicLength_logarithmic_bounds
    T a r c hTOne ha hPower hr hScale
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  have hQGeometry : 1 < Q ∧ (Q : ℝ) ≤ T ∧ T^a ≤ (Q : ℝ) ∧
      2 ≤ typeILogarithmicScale T Q ∧ typeILogarithmicScale T Q ≤ 1/a := by
    simpa only [classicalDirectDyadicLength,if_neg h10,Q,Y] using hGeometry 1
  have hR : R ≤ T^d := hRadiusT Q (by omega) hQGeometry.2.1
  obtain ⟨W',label,hPert,hValues,_hEnergy⟩ :=
    exists_interior_source_indexed_two_dyadic_fourier_family
      s V k W hY hr hV hk hLower hUpper hLarge
  have hPert' : ∀ x, |W' x-W x| ≤ 2*Real.pi*T^d := by
    intro x
    exact (hPert x).trans (mul_le_mul_of_nonneg_left hR (by positivity))
  refine ⟨W',label,hPert',?_,?_⟩
  · intro x
    have hx := hGeometry (label x)
    refine ⟨hx.1,hx.2.1,hx.2.2.1,hx.2.2.2.1,hx.2.2.2.2,?_⟩
    have hNorm := hThreshold (classicalDirectDyadicLength Q (label x)) Q
      (classicalDirectDyadicLength_bounds Q (label x)).2 hx.2.2.1
    have hValue := hValues x
    dsimp only at hValue
    rw [dirichletPoly_coefficientOne_eq_sum_phase] at hValue
    exact hNorm.trans hValue
  · calc
      approximateAdditiveEnergyOf 1 W ≤
          approximateAdditiveEnergyOf (1+4*(2*Real.pi*T^d)) W' :=
        approximateAdditiveEnergyOf_perturbation_le hPert'
      _ ≤ (4*Nat.ceil (1+4*(2*Real.pi*T^d))+6)*approximateAdditiveEnergyOf 1 W' :=
        approximateAdditiveEnergyOf_le_natCeil_mul_unit _ _

end TaoTrudgianYang2025

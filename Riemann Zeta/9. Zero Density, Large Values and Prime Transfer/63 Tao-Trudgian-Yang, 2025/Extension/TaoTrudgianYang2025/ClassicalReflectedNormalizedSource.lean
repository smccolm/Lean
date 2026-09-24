import TaoTrudgianYang2025.ClassicalReflectedThresholdAbsorption

/-!
# Actual reflected source with normalized coefficient-one threshold

This consumes the full indexed source reflection/Fourier factory. The
small-loss condition is explicit and precedes every physical scale and
indexed family. The output retains all indices, geometry, uniform radius,
and the original-family energy bound.
-/

noncomputable section
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

theorem eventually_interior_source_normalized_indexed_fourier_data
    {sigma d u theta delta : ℝ} (hsigma : 1 / 2 < sigma)
    (hsigmaUpper : sigma < 1) (hd : 0 < d) (hdOne : d ≤ 1)
    (hdGap : d ≤ (sigma - 1 / 2) / 1000)
    (hu : 0 ≤ u) (huD : u ≤ d) (htheta : 0 < theta)
    (hdelta : 0 < delta)
    (hLoss : (2/((sigma-1/2)/2))*(u+3*d) ≤ delta/2) :
    ∃ Clog : ℝ, 0 < Clog ∧
      let CK := 32 * 2 ^ sigma +
        (20 * (4 * Real.pi) ^ sigma + 4 * Real.pi ^ sigma) *
          4 ^ (sigma + 1 / 2)
      let Cref := mediumReflectedThresholdConstant Clog CK
      let g := (sigma - 1 / 2) / 2
      let Uscale := 2 / g
      1 ≤ Cref ∧ 0 < g ∧ 0 < Uscale ∧
      ∃ k : ℕ, 1 < k ∧ ∃ T₀ : ℝ, 8 ≤ T₀ ∧
        ∀ {ι : Type*} [Fintype ι] [Nonempty ι]
          {T tau : ℝ} {Y A r : ℕ} (W : ι → ℝ), T₀ ≤ T →
          A = ⌊sharpZetaCutoff T⌋₊ → 0 < Y → 2 ≤ r →
          ((Y+1 : ℕ) : ℝ) ≤ (((2^r*Y : ℕ) : ℝ)/2) →
          2*(2^r*Y) ≤ A →
          tau = typeILogarithmicScale T (2^r*Y) → 1 < tau → tau < 2 →
          (∀ x, T-T^d ≤ W x ∧ W x ≤ 2*T+T^d) →
          (∀ x, ((3/4)*(T^(-u)/2))/(Nat.clog 2 A+1 : ℕ) ≤
            ‖typeISourceSmoothBlock Y A r sigma (W x)‖) →
          let Q := 2^r*Y
          let M := mediumTypeIDualCutoff T d Q
          let V := ((3/4)*(T^(-u)/2))/(Nat.clog 2 A+1 : ℕ)
          let R := (Real.pi*V)/
            (8*(Q : ℝ)*mediumTypeIStationaryKernel sigma T Q*
              (typeIDyadicCutoffMellinL1+1))
          let L := (R/(2*(M : ℝ)^sigma))/Nat.clog 2 M
          ∃ (W' : ι → ℝ) (label : ι → Fin (Nat.clog 2 M)),
            (∀ x, |W' x-W x| ≤ T^d+2*Real.pi*T^theta) ∧
            (∀ x, T/2-2*Real.pi*T^theta ≤ W' x ∧ W' x ≤ 5*T/2+2*Real.pi*T^theta) ∧
            (∀ x, ((2^(label x).val : ℕ) : ℝ)^(sigma-delta) ≤
              ‖∑ n ∈ Finset.Ioc (2^(label x).val) (min (2*2^(label x).val) M),
                dirichletPhase n (W' x)‖) ∧
            (∀ x, (M : ℝ)^sigma*L /
                (4*((2^(label x).val : ℕ) : ℝ)^sigma*classicalTypeIFourierL1 (-sigma)) ≤
              ‖∑ n ∈ Finset.Ioc (2^(label x).val) (min (2*2^(label x).val) M),
                dirichletPhase n (W' x)‖) ∧
            approximateAdditiveEnergyOf 1 W ≤
              (4*Nat.ceil (1+4*(T^d+2*Real.pi*T^theta))+6)*approximateAdditiveEnergyOf 1 W' ∧
            T^(1/2-u-d*sigma+(sigma-1)/tau-d)/Cref ≤ L ∧
            T^g/Cref ≤ L ∧
            (∀ x, 1 < 2^(label x).val ∧ 2^(label x).val < M ∧
              1/(1/2+d) ≤ typeILogarithmicScale T (2^(label x).val) ∧
              typeILogarithmicScale T (2^(label x).val) ≤ Uscale ∧
              classicalTypeIFourierRadius M (2^(label x).val) k (-sigma)
                ((M : ℝ)^sigma*L) ≤ T^theta) := by
  classical
  obtain ⟨Clog,hClog,hCref,hg,hUscale,k,hk,Tref,hTref,hdata⟩ :=
    eventually_interior_source_indexed_fourier_data hsigma hsigmaUpper
      hd hdOne hdGap hu huD htheta
  let CK : ℝ := 32*2^sigma+
    (20*(4*Real.pi)^sigma+4*Real.pi^sigma)*4^(sigma+1/2)
  let Cref := mediumReflectedThresholdConstant Clog CK
  let g : ℝ := (sigma-1/2)/2
  let Uscale := 2/g
  have hCrefPos : 0 < Cref := zero_lt_one.trans_le hCref
  have hAbsorb := eventually_classicalReflected_threshold_absorbed
    sigma (u+3*d) delta Uscale Cref (by positivity) hdelta hUscale hCrefPos hLoss
  obtain ⟨Tabs,habs⟩ := Filter.eventually_atTop.mp hAbsorb
  refine ⟨Clog,hClog,hCref,hg,hUscale,k,hk,max Tref Tabs,
    hTref.trans (le_max_left _ _),?_⟩
  intro ι _ _ T tau Y A r W hT hA hY hr hLower hUpper hTau htauOne htauTwo
    hRange hLarge
  dsimp only
  obtain ⟨W',label,hpert,hPositive,hValues,hEnergy,hExact,hGrowth,hGeometry⟩ :=
    hdata W ((le_max_left _ _).trans hT) hA hY hr hLower hUpper hTau
      htauOne htauTwo hRange hLarge
  have hAbsAt := habs T ((le_max_right _ _).trans hT)
  let Q := 2^r*Y
  let M := mediumTypeIDualCutoff T d Q
  let V : ℝ := ((3/4)*(T^(-u)/2))/(Nat.clog 2 A+1 : ℕ)
  let R := (Real.pi*V)/
    (8*(Q : ℝ)*mediumTypeIStationaryKernel sigma T Q*(typeIDyadicCutoffMellinL1+1))
  let L := (R/(2*(M : ℝ)^sigma))/Nat.clog 2 M
  have hTEight : 8 ≤ T := hTref.trans ((le_max_left _ _).trans hT)
  have hTOne : 1 ≤ T := by linarith
  have hTPos : 0 < T := by linarith
  have hLPos : 0 < L :=
    (div_pos (Real.rpow_pos_of_pos hTPos g) hCrefPos).trans_le hGrowth
  have hQOne : 1 < Q := by
    have hPow : 4 ≤ 2^r := by
      simpa using Nat.pow_le_pow_right (by omega : 0 < 2) hr
    have hFour : 4 ≤ Q := hPow.trans (Nat.le_mul_of_pos_right _ hY)
    omega
  have hScale : (Q : ℝ)^tau = T := by
    rw [hTau]
    simpa only [Q] using rpow_typeILogarithmicScale_eq hTPos hQOne
  refine ⟨W',label,hpert,hPositive,?_,hValues,hEnergy,hExact,hGrowth,hGeometry⟩
  intro x
  let N := 2^(label x).val
  have hGeom := hGeometry x
  have hNUpper : (N : ℝ) ≤ T^(1+d-1/tau) :=
    classicalReflected_dyadic_length_le_physical_scale hTPos (by linarith)
      hQOne hScale hGeom.2.1.le
  have hLowerL := classicalReflected_threshold_lower_of_physical_scale
    sigma tau d u T Cref L N hsigma.le hsigmaUpper.le (by linarith)
      htauTwo.le hd.le hTOne hCrefPos hNUpper hExact
  have hNeg : -u-3*d = -(u+3*d) := by ring
  rw [hNeg] at hLowerL
  have hPower := hAbsAt N L hGeom.1 hGeom.2.2.2.1 hLowerL
  have hFavorable := classicalReflected_normalized_threshold_ge sigma L M N
    (by linarith) hLPos.le (Nat.zero_lt_one.trans hGeom.1) hGeom.2.1.le
  exact hPower.trans (hFavorable.trans (hValues x))

end TaoTrudgianYang2025


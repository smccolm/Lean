import TaoTrudgianYang2025.ClassicalReflectedIndexedGeometry
import TaoTrudgianYang2025.ClassicalReflectedIndexedFourier

/-!
# All-index source reflection followed by uniform Fourier deweighting

One derivative order and one height threshold work for every original finite
indexed source family. The actual reflected dyadic labels are retained.
The energy estimate is for the full original family, with a single combined
displacement loss; no selected-subset energy is substituted for source energy.
-/

noncomputable section
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

theorem eventually_interior_source_indexed_fourier_data
    {sigma d u theta : ℝ} (hsigma : 1 / 2 < sigma)
    (hsigmaUpper : sigma < 1) (hd : 0 < d) (hdOne : d ≤ 1)
    (hdGap : d ≤ (sigma - 1 / 2) / 1000)
    (hu : 0 ≤ u) (huD : u ≤ d) (htheta : 0 < theta) :
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
  obtain ⟨Clog,hClog,hCref,hg,hUscale,Tref,hTref,hdata⟩ :=
    eventually_interior_source_indexed_reflected_data hsigma hsigmaUpper
      hd hdOne hdGap hu huD
  let CK : ℝ := 32*2^sigma+
    (20*(4*Real.pi)^sigma+4*Real.pi^sigma)*4^(sigma+1/2)
  let Cref := mediumReflectedThresholdConstant Clog CK
  let g : ℝ := (sigma-1/2)/2
  obtain ⟨k,hk,hradius⟩ :=
    exists_order_eventually_classicalReflectedFourierRadius_le_rpow
      sigma theta (by linarith) htheta
  have hsize : ∀ᶠ T : ℝ in Filter.atTop, Cref ≤ T^g :=
    (tendsto_rpow_atTop hg).eventually (Filter.eventually_ge_atTop Cref)
  obtain ⟨Taux,haux⟩ := Filter.eventually_atTop.mp (hradius.and hsize)
  refine ⟨Clog,hClog,hCref,hg,hUscale,k,hk,max Tref Taux,
    hTref.trans (le_max_left _ _),?_⟩
  intro ι _ _ T tau Y A r W hT hA hY hr hLower hUpper hTau htauOne htauTwo
    hRange hLarge
  dsimp only
  obtain ⟨U,label,hpert,hPositive,hLargeU,_hEnergy,hExact,hGrowth,hGeometry⟩ :=
    hdata W ((le_max_left _ _).trans hT) hA hY hr hLower hUpper hTau
      htauOne htauTwo hRange hLarge
  obtain ⟨hRadiusAt,hSizeAt⟩ := haux T ((le_max_right _ _).trans hT)
  let Q := 2^r*Y
  let M := mediumTypeIDualCutoff T d Q
  let V : ℝ := ((3/4)*(T^(-u)/2))/(Nat.clog 2 A+1 : ℕ)
  let R := (Real.pi*V)/
    (8*(Q : ℝ)*mediumTypeIStationaryKernel sigma T Q*(typeIDyadicCutoffMellinL1+1))
  let L := (R/(2*(M : ℝ)^sigma))/Nat.clog 2 M
  let N := fun x => 2^(label x).val
  have hTPos : 0 < T := by
    have h := hTref.trans ((le_max_left _ _).trans hT)
    linarith
  have hCrefPos : 0 < Cref := zero_lt_one.trans_le hCref
  have hL : 1 ≤ L := by
    have hOne : 1 ≤ T^g/Cref := (le_div_iff₀ hCrefPos).mpr (by simpa using hSizeAt)
    exact hOne.trans hGrowth
  have hM : 0 < M :=
    (Nat.zero_lt_one.trans (hGeometry (Classical.arbitrary ι)).1).trans
      (hGeometry (Classical.arbitrary ι)).2.1
  have hN : ∀ x, 0 < N x := fun x => Nat.zero_lt_one.trans (hGeometry x).1
  have hRadius : ∀ x,
      classicalTypeIFourierRadius M (N x) k (-sigma) ((M : ℝ)^sigma*L) ≤ T^theta := by
    intro x
    have hgeom := hGeometry x
    have hNreal : 1 ≤ (N x : ℝ) := by exact_mod_cast (hN x)
    have hLowerOne : 1 ≤ 1/(1/2+d) := by
      apply (le_div_iff₀ (by linarith : 0 < (1/2+d : ℝ))).mpr
      nlinarith [hdGap]
    have hNT : (N x : ℝ) ≤ T := by
      calc
        (N x : ℝ) ≤ (N x : ℝ)^typeILogarithmicScale T (N x) :=
          Real.self_le_rpow_of_one_le hNreal (hLowerOne.trans hgeom.2.2.1)
        _ = T := rpow_typeILogarithmicScale_eq hTPos hgeom.1
    exact hRadiusAt M (N x) L hM hgeom.2.1.le hNT hL
  obtain ⟨W',hshift,hValues,_hFourierEnergy⟩ :=
    exists_classicalReflected_bounded_varying_length_family
      M k N sigma L (T^theta) U hM hN (zero_lt_one.trans_le hL) hk
      hLargeU hRadius
  have hCombined : ∀ x, |W' x-W x| ≤ T^d+2*Real.pi*T^theta := by
    intro x
    calc
      |W' x-W x| ≤ |W' x-U x|+|U x-W x| := abs_sub_le _ _ _
      _ ≤ 2*Real.pi*T^theta+T^d := add_le_add (hshift x) (hpert x)
      _ = _ := by ring
  refine ⟨W',label,hCombined,?_,hValues,?_,hExact,hGrowth,?_⟩
  · intro x
    have hs := abs_le.mp (hshift x)
    have hp := hPositive x
    constructor <;> linarith
  · exact (approximateAdditiveEnergyOf_perturbation_le hCombined).trans
      (approximateAdditiveEnergyOf_le_natCeil_mul_unit _ _)
  · intro x
    exact ⟨(hGeometry x).1,(hGeometry x).2.1,(hGeometry x).2.2.1,
      (hGeometry x).2.2.2,hRadius x⟩

end TaoTrudgianYang2025


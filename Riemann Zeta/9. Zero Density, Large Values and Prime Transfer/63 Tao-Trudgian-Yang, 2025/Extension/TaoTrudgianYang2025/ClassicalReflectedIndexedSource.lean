import TaoTrudgianYang2025.ClassicalReflectedIndexed

/-!
# Actual interior source reflection retaining every index

The finite image is used only to invoke the pointwise native analytic
reflection theorem. The output is pulled back to the original index type;
its coincidences and multiplicity copies are never discarded in the
subsequent dyadic labeling or perturbation-energy inequality.
-/

noncomputable section
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

theorem eventually_interior_source_indexed_reflection
    {sigma d u : ℝ} (hsigma : 1/2 < sigma) (hsigmaUpper : sigma < 1)
    (hd : 0 < d) (hdOne : d ≤ 1) (hdGap : d ≤ (sigma-1/2)/1000)
    (hu : 0 ≤ u) (huD : u ≤ d) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧
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
        let S := R/(2*(M : ℝ)^sigma)
        1 < M ∧
        ∃ (W' : ι → ℝ) (label : ι → Fin (Nat.clog 2 M)),
          (∀ x, |W' x-W x| ≤ T^d) ∧
          (∀ x, T/2 ≤ W' x ∧ W' x ≤ 5*T/2) ∧
          (∀ x, S/Nat.clog 2 M ≤
            ‖dirichletPoly (2^(label x).val)
              (normalizedTypeIReflectedCoeff sigma M) (W' x)‖) ∧
          approximateAdditiveEnergyOf 1 W ≤
            (4*Nat.ceil (1+4*T^d)+6)*approximateAdditiveEnergyOf 1 W' := by
  classical
  obtain ⟨Tref,hTref,hReflect⟩ :=
    eventually_interior_source_family_reflects hsigma hsigmaUpper hd hdOne hdGap hu huD
  have hdStrict : d < 1 := by nlinarith [hdGap]
  obtain ⟨Twindow,_hTwindow,hWindow⟩ :=
    eventually_two_mul_rpow_le_half_sub_two hd hdStrict
  refine ⟨max Tref Twindow,hTref.trans (le_max_left _ _),?_⟩
  intro ι _ _ T tau Y A r W hT hA hY hr hLower hUpper hTau htauOne htauTwo
    hRange hLarge
  dsimp only
  let Wset := Finset.univ.image W
  have hWset : Wset.Nonempty := by
    exact ⟨W (Classical.arbitrary ι),
      Finset.mem_image.mpr ⟨Classical.arbitrary ι,Finset.mem_univ _,rfl⟩⟩
  have hWRange : ∀ t ∈ Wset, T-T^d ≤ t ∧ t ≤ 2*T+T^d := by
    intro t ht
    obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp ht
    exact hRange x
  have hWLarge : ∀ t ∈ Wset,
      ((3/4)*(T^(-u)/2))/(Nat.clog 2 A+1 : ℕ) ≤
        ‖typeISourceSmoothBlock Y A r sigma t‖ := by
    intro t ht
    obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp ht
    exact hLarge x
  obtain ⟨hM,hEach⟩ := hReflect Wset ((le_max_left _ _).trans hT)
    hA hY hr hLower hUpper hTau htauOne htauTwo hWRange hWLarge hWset
  let Q := 2^r*Y
  let M := mediumTypeIDualCutoff T d Q
  let V := ((3/4)*(T^(-u)/2))/(Nat.clog 2 A+1 : ℕ)
  let R := (Real.pi*V)/
    (8*(Q : ℝ)*mediumTypeIStationaryKernel sigma T Q*(typeIDyadicCutoffMellinL1+1))
  let S := R/(2*(M : ℝ)^sigma)
  obtain ⟨W',label,hpert,hblocks,henergy⟩ :=
    exists_reflected_bounded_dyadic_family M sigma (T^d) S W hM
      (fun x => hEach (W x) (Finset.mem_image.mpr ⟨x,Finset.mem_univ x,rfl⟩))
  refine ⟨hM,W',label,hpert,?_,hblocks,henergy⟩
  intro x
  have hx := hRange x
  have hp := abs_le.mp (hpert x)
  have hroom := hWindow T ((le_max_right _ _).trans hT)
  constructor <;> linarith

end TaoTrudgianYang2025

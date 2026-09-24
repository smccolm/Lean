import TaoTrudgianYang2025.ClassicalGeneralPhysicalTransfer

/-!
# Cardinality and energy bounds for the actual bottom global blocks

The source polynomial is normalized and split on every original index.
Its literal support supplies the linked general-LV scale window, while
both source logarithms and the full four-color energy loss are absorbed.
The common constant and line tolerance precede the shifted source line.
-/

noncomputable section
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

theorem classicalBottom_uniform_shifted_line_source_cardinality_bound
    (σ B a : ℝ) (hB : 0 ≤ B) (ha : 0 < a)
    (hLV : ∀ τ ∈ Set.Icc (1/(2*a)) (2/a), IsLargeValueBound σ τ (B*τ)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
        ∀ s u θ : ℝ, 0 ≤ s → s ≤ 1 → σ-δ/2 ≤ s →
          u ≤ a*δ/8 → θ ≤ 1 →
          ∀ᶠ T : ℝ in Filter.atTop,
            ∀ {ι : Type*} [Fintype ι] (r : ℕ) (W : ι → ℝ),
              r < 2 →
              (∀ x y : ι, x ≠ y → 1 ≤ |W x-W y|) →
              (∀ x, T-T^θ ≤ W x ∧ W x ≤ 2*T+T^θ) →
              (∀ x,
                ((3/4)*(T^(-u)/2))/(Nat.clog 2 ⌊sharpZetaCutoff T⌋₊+1 : ℕ) ≤
                  ‖typeISourceSmoothBlock ⌊T^a⌋₊ ⌊sharpZetaCutoff T⌋₊ r s (W x)‖) →
              (Fintype.card ι : ℝ) ≤ C*T^(B+ε) := by
  intro ε hε
  have hInv : 1/(a/2) = 2/a := by rw [div_div_eq_mul_div]; ring
  have hInput : ∀ τ ∈ Set.Icc (1/(2*a)) (1/(a/2)), IsLargeValueBound σ τ (B*τ) := by
    simpa only [hInv] using hLV
  obtain ⟨C,hC,δ,hδ,hPhysical⟩ :=
    classicalGeneral_uniform_physical_cardinality_bound σ B (2*a) (a/2)
      hB (by positivity) (by positivity) (by linarith) hInput (ε/2) (by positivity)
  let Cfinal := max 1 (C)
  refine ⟨Cfinal,le_max_left _ _,δ,hδ,?_⟩
  intro s u θ hs hsOne hsσ hu hθ
  filter_upwards [hPhysical θ hθ,
    eventually_classicalBottomSource_physical_bounds a ha,
    eventually_classicalBottomSource_normalized_threshold_lower s (a/2) (δ/2) u
      hs hsOne (by positivity) (by positivity) (by nlinarith),
    eventually_const_mul_classicalSource_two_clogs_le_rpow 1 (ε/8)
      (by norm_num) (by positivity),
    (tendsto_rpow_atTop ha).eventually (Filter.eventually_ge_atTop (2 : ℝ)),
    Filter.eventually_ge_atTop (8 : ℝ)]
    with T hPhysical hGeometry hThreshold hLog hYPower hT
  intro ι _ r W hr hSep hRange hLarge
  classical
  let Y := ⌊T^a⌋₊
  let A := ⌊sharpZetaCutoff T⌋₊
  let Q := 2^r*Y
  let k := Nat.clog 2 (A+1)
  let V : ℝ := ((3/4)*(T^(-u)/2))/(Nat.clog 2 A+1 : ℕ)
  let Vnorm : ℝ := (((Q : ℝ)/2)^s*V)/k
  have hTPos : 0 < T := by linarith
  have hTOne : 1 ≤ T := by linarith
  have hY : 0 < Y := by
    have hTwo : 2 ≤ Y := Nat.le_floor hYPower
    omega
  have hA : 1 < A := by
    apply lt_of_lt_of_le (by omega : 1 < (2 : ℕ))
    apply Nat.le_floor
    exact (show (2 : ℝ) ≤ 4*T by linarith).trans (four_mul_lt_sharpZetaCutoff T).le
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hV : 0 < V := by dsimp [V]; positivity
  obtain ⟨label,hCoeff,hValues,hLengths,_hCard,_hEnergy⟩ :=
    exists_source_normalized_indexed_dyadic_family Y A r s V W hY hA hs hV hLarge
  let Wᵢ := fun c : Fin k => fun x : EnergyColorFiber label c => W x.1
  let E := C*T^(B+ε/2)
  have hCNonneg : 0 ≤ C := zero_le_one.trans hC
  have hClass (c : Fin k) : (Fintype.card (EnergyColorFiber label c) : ℝ) ≤ E := by
    cases isEmpty_or_nonempty (EnergyColorFiber label c) with
    | inl hEmpty =>
      rw [Fintype.card_of_isEmpty,Nat.cast_zero]
      dsimp [E]
      positivity
    | inr hNonempty =>
      let x₀ : EnergyColorFiber label c := Classical.arbitrary _
      have hLabel (x : EnergyColorFiber label c) : label x.1 = c := x.2
      have hLengths' := hLengths x₀.1
      rw [hLabel x₀] at hLengths'
      have hGeom := hGeometry r (2^c.val) hr hLengths'.2 hLengths'.1
      have hNReal : 1 < ((2^c.val : ℕ) : ℝ) :=
        (Real.one_lt_rpow (by linarith : 1 < T) (by positivity : 0 < a/2)).trans_le hGeom.1
      have hNorm : ((2^c.val : ℕ) : ℝ)^(σ-δ) ≤ Vnorm :=
        (Real.rpow_le_rpow_of_exponent_le hNReal.le (by linarith)).trans
          (hThreshold (2^c.val) Q hQ hLengths'.1.le hGeom.1)
      have hSepi : ∀ x y : EnergyColorFiber label c,
          x ≠ y → 1 ≤ |Wᵢ c x-Wᵢ c y| := by
        intro x y hxy
        exact hSep x.1 y.1 (fun h => hxy (Subtype.ext h))
      have hLargei : ∀ x : EnergyColorFiber label c,
          Vnorm ≤ ‖dirichletPoly (2^c.val)
            (normalizedTypeISourceDirichletCoeff Y A r s) (Wᵢ c x)‖ := by
        intro x
        simpa only [hLabel x] using hValues x.1
      exact hPhysical (2^c.val) Vnorm (normalizedTypeISourceDirichletCoeff Y A r s)
        (Wᵢ c) hGeom.1 hGeom.2 hNorm (fun n _ => hCoeff n)
        (fun x => hRange x.1) hSepi hLargei
  have hkSmall : (k : ℝ) ≤ T^(ε/8) := by
    have hOne : (1 : ℝ) ≤ (Nat.clog 2 A+1 : ℕ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le (Nat.clog 2 A))
    calc
      (k : ℝ) ≤ (Nat.clog 2 A+1 : ℕ)*(k : ℝ) :=
        le_mul_of_one_le_left (Nat.cast_nonneg _) hOne
      _ ≤ T^(ε/8) := by simpa only [one_mul] using hLog
  have hkPower : (k : ℝ) ≤ T^(ε/2) :=
    hkSmall.trans (Real.rpow_le_rpow_of_exponent_le hTOne (by linarith))
  have hTotal : (Fintype.card ι : ℝ) ≤ (k : ℝ)*E := by
    simpa only [Fintype.card_fin] using cardinality_le_color_count_mul label E hClass
  calc
    (Fintype.card ι : ℝ) ≤ (k : ℝ)*E := hTotal
    _ ≤ T^(ε/2)*E := mul_le_mul_of_nonneg_right hkPower (by dsimp [E]; positivity)
    _ = C*T^(B+ε) := by
      dsimp only [E]
      rw [show B+ε = ε/2+(B+ε/2) by ring,
        Real.rpow_add hTPos (ε/2) (B+ε/2)]
      ring
    _ ≤ Cfinal*T^(B+ε) := mul_le_mul_of_nonneg_right
      (le_max_right _ _) (Real.rpow_nonneg hTPos.le _)


theorem classicalBottom_uniform_shifted_line_source_energy_bound
    (σ B a : ℝ) (hB : 0 ≤ B) (ha : 0 < a)
    (hLV : ∀ τ ∈ Set.Icc (1/(2*a)) (2/a), IsLargeValueEnergyBound σ τ (B*τ)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
        ∀ s u θ : ℝ, 0 ≤ s → s ≤ 1 → σ-δ/2 ≤ s →
          u ≤ a*δ/8 → θ ≤ 1 →
          ∀ᶠ T : ℝ in Filter.atTop,
            ∀ {ι : Type*} [Fintype ι] (r : ℕ) (W : ι → ℝ),
              r < 2 →
              (∀ x y : ι, x ≠ y → 1 ≤ |W x-W y|) →
              (∀ x, T-T^θ ≤ W x ∧ W x ≤ 2*T+T^θ) →
              (∀ x,
                ((3/4)*(T^(-u)/2))/(Nat.clog 2 ⌊sharpZetaCutoff T⌋₊+1 : ℕ) ≤
                  ‖typeISourceSmoothBlock ⌊T^a⌋₊ ⌊sharpZetaCutoff T⌋₊ r s (W x)‖) →
              (approximateAdditiveEnergyOf 1 W : ℝ) ≤ C*T^(B+ε) := by
  intro ε hε
  have hInv : 1/(a/2) = 2/a := by rw [div_div_eq_mul_div]; ring
  have hInput : ∀ τ ∈ Set.Icc (1/(2*a)) (1/(a/2)), IsLargeValueEnergyBound σ τ (B*τ) := by
    simpa only [hInv] using hLV
  obtain ⟨C,hC,δ,hδ,hPhysical⟩ :=
    classicalGeneral_uniform_physical_energy_bound σ B (2*a) (a/2)
      hB (by positivity) (by positivity) (by linarith) hInput (ε/2) (by positivity)
  let Cfinal := max 1 (9*C)
  refine ⟨Cfinal,le_max_left _ _,δ,hδ,?_⟩
  intro s u θ hs hsOne hsσ hu hθ
  filter_upwards [hPhysical θ hθ,
    eventually_classicalBottomSource_physical_bounds a ha,
    eventually_classicalBottomSource_normalized_threshold_lower s (a/2) (δ/2) u
      hs hsOne (by positivity) (by positivity) (by nlinarith),
    eventually_const_mul_classicalSource_two_clogs_le_rpow 1 (ε/8)
      (by norm_num) (by positivity),
    (tendsto_rpow_atTop ha).eventually (Filter.eventually_ge_atTop (2 : ℝ)),
    Filter.eventually_ge_atTop (8 : ℝ)]
    with T hPhysical hGeometry hThreshold hLog hYPower hT
  intro ι _ r W hr hSep hRange hLarge
  classical
  let Y := ⌊T^a⌋₊
  let A := ⌊sharpZetaCutoff T⌋₊
  let Q := 2^r*Y
  let k := Nat.clog 2 (A+1)
  let V : ℝ := ((3/4)*(T^(-u)/2))/(Nat.clog 2 A+1 : ℕ)
  let Vnorm : ℝ := (((Q : ℝ)/2)^s*V)/k
  have hTPos : 0 < T := by linarith
  have hTOne : 1 ≤ T := by linarith
  have hY : 0 < Y := by
    have hTwo : 2 ≤ Y := Nat.le_floor hYPower
    omega
  have hA : 1 < A := by
    apply lt_of_lt_of_le (by omega : 1 < (2 : ℕ))
    apply Nat.le_floor
    exact (show (2 : ℝ) ≤ 4*T by linarith).trans (four_mul_lt_sharpZetaCutoff T).le
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hV : 0 < V := by dsimp [V]; positivity
  obtain ⟨label,hCoeff,hValues,hLengths,_hCard,hEnergy⟩ :=
    exists_source_normalized_indexed_dyadic_family Y A r s V W hY hA hs hV hLarge
  let Wᵢ := fun c : Fin k => fun x : EnergyColorFiber label c => W x.1
  let E := C*T^(B+ε/2)
  have hCNonneg : 0 ≤ C := zero_le_one.trans hC
  have hClass (c : Fin k) : (approximateAdditiveEnergyOf 1 (Wᵢ c) : ℝ) ≤ E := by
    cases isEmpty_or_nonempty (EnergyColorFiber label c) with
    | inl hEmpty =>
      have hz : approximateAdditiveEnergyOf 1 (Wᵢ c) = 0 := by
        simp [approximateAdditiveEnergyOf,AdditiveQuadrupleOf]
      rw [hz,Nat.cast_zero]
      dsimp [E]
      positivity
    | inr hNonempty =>
      let x₀ : EnergyColorFiber label c := Classical.arbitrary _
      have hLabel (x : EnergyColorFiber label c) : label x.1 = c := x.2
      have hLengths' := hLengths x₀.1
      rw [hLabel x₀] at hLengths'
      have hGeom := hGeometry r (2^c.val) hr hLengths'.2 hLengths'.1
      have hNReal : 1 < ((2^c.val : ℕ) : ℝ) :=
        (Real.one_lt_rpow (by linarith : 1 < T) (by positivity : 0 < a/2)).trans_le hGeom.1
      have hNorm : ((2^c.val : ℕ) : ℝ)^(σ-δ) ≤ Vnorm :=
        (Real.rpow_le_rpow_of_exponent_le hNReal.le (by linarith)).trans
          (hThreshold (2^c.val) Q hQ hLengths'.1.le hGeom.1)
      have hSepi : ∀ x y : EnergyColorFiber label c,
          x ≠ y → 1 ≤ |Wᵢ c x-Wᵢ c y| := by
        intro x y hxy
        exact hSep x.1 y.1 (fun h => hxy (Subtype.ext h))
      have hLargei : ∀ x : EnergyColorFiber label c,
          Vnorm ≤ ‖dirichletPoly (2^c.val)
            (normalizedTypeISourceDirichletCoeff Y A r s) (Wᵢ c x)‖ := by
        intro x
        simpa only [hLabel x] using hValues x.1
      exact hPhysical (2^c.val) Vnorm (normalizedTypeISourceDirichletCoeff Y A r s)
        (Wᵢ c) hGeom.1 hGeom.2 hNorm (fun n _ => hCoeff n)
        (fun x => hRange x.1) hSepi hLargei
  have hkSmall : (k : ℝ) ≤ T^(ε/8) := by
    have hOne : (1 : ℝ) ≤ (Nat.clog 2 A+1 : ℕ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le (Nat.clog 2 A))
    calc
      (k : ℝ) ≤ (Nat.clog 2 A+1 : ℕ)*(k : ℝ) :=
        le_mul_of_one_le_left (Nat.cast_nonneg _) hOne
      _ ≤ T^(ε/8) := by simpa only [one_mul] using hLog
  obtain ⟨chosen,hEnergy⟩ := hEnergy
  have hSum :
      (approximateAdditiveEnergyOf 1 (Wᵢ (chosen 0)) : ℝ) +
        (approximateAdditiveEnergyOf 1 (Wᵢ (chosen 1)) : ℝ) +
        (approximateAdditiveEnergyOf 1 (Wᵢ (chosen 2)) : ℝ) +
        (approximateAdditiveEnergyOf 1 (Wᵢ (chosen 3)) : ℝ) ≤ 4*E := by
    linarith [hClass (chosen 0),hClass (chosen 1),hClass (chosen 2),hClass (chosen 3)]
  have hTotal : (approximateAdditiveEnergyOf 1 W : ℝ) ≤ 9*(k : ℝ)^4*E := by
    have hProd := mul_le_mul_of_nonneg_left hSum (by positivity : 0 ≤ 9*(k : ℝ)^4)
    dsimp only at hEnergy
    nlinarith
  have hkPower : (k : ℝ)^4 ≤ T^(ε/2) := by
    calc
      (k : ℝ)^4 ≤ (T^(ε/8))^4 := pow_le_pow_left₀ (Nat.cast_nonneg _) hkSmall 4
      _ = T^(ε/2) := by
        rw [← Real.rpow_natCast,← Real.rpow_mul hTPos.le]
        congr 1
        ring
  calc
    (approximateAdditiveEnergyOf 1 W : ℝ) ≤ 9*(k : ℝ)^4*E := hTotal
    _ ≤ 9*T^(ε/2)*E := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hkPower (by norm_num)) (by dsimp [E]; positivity)
    _ = (9*C)*T^(B+ε) := by
      dsimp only [E]
      rw [show B+ε = ε/2+(B+ε/2) by ring,
        Real.rpow_add hTPos (ε/2) (B+ε/2)]
      ring
    _ ≤ Cfinal*T^(B+ε) := mul_le_mul_of_nonneg_right
      (le_max_right _ _) (Real.rpow_nonneg hTPos.le _)


end TaoTrudgianYang2025

import TaoTrudgianYang2025.ClassicalReflectedColorGeometry

/-!
# All-index reflected transfers with dyadic and separation colors

Only occupied blocks must satisfy the physical scale hypotheses. Empty
fibers are handled explicitly. The original separated indexed family and
its actual bounded perturbation supply the multiplicity coloring; no
replacement cardinality or energy bound is assumed.
-/

noncomputable section
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

theorem classicalReflected_uniform_colored_cardinality_bound
    (σ B U : ℝ) (hB : 0 ≤ B) (hU : 2 ≤ U)
    (hLV : ∀ τ ∈ Set.Icc (2 : ℝ) U, IsZetaLargeValueBound σ τ (B*τ)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
        ∀ {ι κ : Type*} [Fintype ι] [LinearOrder ι] [Fintype κ]
          (A : ℕ) (N : κ → ℕ) (label : ι → κ) (T D : ℝ)
          (W W' : ι → ℝ),
          let L := Nat.ceil (2*D+2)
          let K := (Fintype.card (κ × (ZMod 2 × Fin (L+1))) : ℝ)
          0 < T → 0 ≤ D →
          (∀ x y : ι, x ≠ y → 1 ≤ |W x-W y|) →
          (∀ x, |W' x-W x| ≤ D) →
          (∀ x, T/4 ≤ W' x ∧ W' x ≤ 4*T) →
          (∀ x, 1 < N (label x) ∧ (N (label x) : ℝ) ≤ T ∧
            C ≤ (N (label x) : ℝ) ∧ 4 ≤ (N (label x) : ℝ)^(δ/2) ∧
            2-δ/2 ≤ typeILogarithmicScale T (N (label x)) ∧
            typeILogarithmicScale T (N (label x)) ≤ U+δ/2) →
          (∀ x, (N (label x) : ℝ)^(σ-δ) ≤
            ‖∑ n ∈ Finset.Ioc (N (label x)) (min (2*N (label x)) A),
              dirichletPhase n (W' x)‖) →
          (Fintype.card ι : ℝ) ≤ K*(4*(C*(2*T)^B*T^ε)) := by
  intro ε hε
  obtain ⟨C,hC,δ,hδ,hfinite⟩ :=
    classicalReflected_uniform_expanded_slab_cardinality_bound
      σ B U hB hU hLV ε hε
  refine ⟨C,hC,δ,hδ,?_⟩
  intro ι κ _ _ _ A N label T D W W'
  dsimp only
  intro hT hD hsep hpert hRange hData hLarge
  classical
  let L := Nat.ceil (2*D+2)
  let hlocal : ∀ z : ℤ, (unitBinFinset W' z).card ≤ L := fun z =>
    unitBinFinset_perturbation_card_le_natCeil W W' D hD hsep hpert z
  let color := fun x => (label x,boundedMultiplicityColor W' L hlocal x)
  let Wᵢ := fun c : κ × (ZMod 2 × Fin (L+1)) =>
    fun x : EnergyColorFiber color c => W' x.1
  let E := 4*(C*(2*T)^B*T^ε)
  have hCnonneg : 0 ≤ C := zero_le_one.trans hC
  have hclass (c : κ × (ZMod 2 × Fin (L+1))) :
      (Fintype.card (EnergyColorFiber color c) : ℝ) ≤ E := by
    cases isEmpty_or_nonempty (EnergyColorFiber color c) with
    | inl hempty =>
      rw [Fintype.card_of_isEmpty, Nat.cast_zero]
      dsimp [E]
      positivity
    | inr hnonempty =>
      let x₀ : EnergyColorFiber color c := Classical.arbitrary _
      have hlabel (x : EnergyColorFiber color c) : label x.1 = c.1 :=
        congrArg Prod.fst x.2
      have hgeom := hData x₀.1
      rw [hlabel x₀] at hgeom
      obtain ⟨hN,hNT,hCN,hPower,hLower,hUpper⟩ := hgeom
      have hsepi := oneSeparated_on_labeled_boundedMultiplicityColor W' label L hlocal c
      have hlargei : ∀ x : EnergyColorFiber color c,
          (N c.1 : ℝ)^(σ-δ) ≤
            ‖∑ n ∈ Finset.Ioc (N c.1) (min (2*N c.1) A),
              dirichletPhase n (Wᵢ c x)‖ := by
        intro x
        simpa only [hlabel x] using hLarge x.1
      have hp := hfinite A (N c.1) ((N c.1 : ℝ)^(σ-δ)) T (Wᵢ c)
        hN hT hCN hPower hLower hUpper (fun x => hRange x.1) hsepi hlargei le_rfl
      calc
        _ ≤ 4*(C*(2*T)^B*(N c.1 : ℝ)^ε) := hp
        _ ≤ E := by
          dsimp [E]
          gcongr
  exact cardinality_le_color_count_mul color E hclass

theorem classicalReflected_uniform_colored_energy_bound
    (σ B U : ℝ) (hB : 0 ≤ B) (hU : 2 ≤ U)
    (hLV : ∀ τ ∈ Set.Icc (2 : ℝ) U, IsZetaLargeValueEnergyBound σ τ (B*τ)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
        ∀ {ι κ : Type*} [Fintype ι] [LinearOrder ι] [Fintype κ]
          (A : ℕ) (N : κ → ℕ) (label : ι → κ) (T D : ℝ)
          (W W' : ι → ℝ),
          let L := Nat.ceil (2*D+2)
          let K := (Fintype.card (κ × (ZMod 2 × Fin (L+1))) : ℝ)
          0 < T → 0 ≤ D →
          (∀ x y : ι, x ≠ y → 1 ≤ |W x-W y|) →
          (∀ x, |W' x-W x| ≤ D) →
          (∀ x, T/4 ≤ W' x ∧ W' x ≤ 4*T) →
          (∀ x, 1 < N (label x) ∧ (N (label x) : ℝ) ≤ T ∧
            C ≤ (N (label x) : ℝ) ∧ 4 ≤ (N (label x) : ℝ)^(δ/2) ∧
            2-δ/2 ≤ typeILogarithmicScale T (N (label x)) ∧
            typeILogarithmicScale T (N (label x)) ≤ U+δ/2) →
          (∀ x, (N (label x) : ℝ)^(σ-δ) ≤
            ‖∑ n ∈ Finset.Ioc (N (label x)) (min (2*N (label x)) A),
              dirichletPhase n (W' x)‖) →
          (approximateAdditiveEnergyOf 1 W : ℝ) ≤ (4*Nat.ceil (1+4*D)+6)*(9*K^4*(2304*(C*(2*T)^B*T^ε))) := by
  intro ε hε
  obtain ⟨C,hC,δ,hδ,hfinite⟩ :=
    classicalReflected_uniform_expanded_slab_energy_bound
      σ B U hB hU hLV ε hε
  refine ⟨C,hC,δ,hδ,?_⟩
  intro ι κ _ _ _ A N label T D W W'
  dsimp only
  intro hT hD hsep hpert hRange hData hLarge
  classical
  let L := Nat.ceil (2*D+2)
  let hlocal : ∀ z : ℤ, (unitBinFinset W' z).card ≤ L := fun z =>
    unitBinFinset_perturbation_card_le_natCeil W W' D hD hsep hpert z
  let color := fun x => (label x,boundedMultiplicityColor W' L hlocal x)
  let Wᵢ := fun c : κ × (ZMod 2 × Fin (L+1)) =>
    fun x : EnergyColorFiber color c => W' x.1
  let E := 2304*(C*(2*T)^B*T^ε)
  have hCnonneg : 0 ≤ C := zero_le_one.trans hC
  have hclass (c : κ × (ZMod 2 × Fin (L+1))) :
      (approximateAdditiveEnergyOf 1 (Wᵢ c) : ℝ) ≤ E := by
    cases isEmpty_or_nonempty (EnergyColorFiber color c) with
    | inl hempty =>
      have hz : approximateAdditiveEnergyOf 1 (Wᵢ c) = 0 := by
        simp [approximateAdditiveEnergyOf, AdditiveQuadrupleOf]
      rw [hz, Nat.cast_zero]
      dsimp [E]
      positivity
    | inr hnonempty =>
      let x₀ : EnergyColorFiber color c := Classical.arbitrary _
      have hlabel (x : EnergyColorFiber color c) : label x.1 = c.1 :=
        congrArg Prod.fst x.2
      have hgeom := hData x₀.1
      rw [hlabel x₀] at hgeom
      obtain ⟨hN,hNT,hCN,hPower,hLower,hUpper⟩ := hgeom
      have hsepi := oneSeparated_on_labeled_boundedMultiplicityColor W' label L hlocal c
      have hlargei : ∀ x : EnergyColorFiber color c,
          (N c.1 : ℝ)^(σ-δ) ≤
            ‖∑ n ∈ Finset.Ioc (N c.1) (min (2*N c.1) A),
              dirichletPhase n (Wᵢ c x)‖ := by
        intro x
        simpa only [hlabel x] using hLarge x.1
      have hp := hfinite A (N c.1) ((N c.1 : ℝ)^(σ-δ)) T (Wᵢ c)
        hN hT hCN hPower hLower hUpper (fun x => hRange x.1) hsepi hlargei le_rfl
      calc
        _ ≤ 2304*(C*(2*T)^B*(N c.1 : ℝ)^ε) := hp
        _ ≤ E := by
          dsimp [E]
          gcongr
  cases isEmpty_or_nonempty κ with
  | inl hκ =>
    letI : IsEmpty ι := ⟨fun x => isEmptyElim (label x)⟩
    have hz : approximateAdditiveEnergyOf 1 W = 0 := by
      simp [approximateAdditiveEnergyOf, AdditiveQuadrupleOf]
    rw [hz, Nat.cast_zero]
    positivity
  | inr hκ =>
    obtain ⟨chosen,henergy⟩ := exists_energy_color_classes W' color
    let K : ℝ := Fintype.card (κ × (ZMod 2 × Fin (L+1)))
    have hSum :
        (approximateAdditiveEnergyOf 1 (Wᵢ (chosen 0)) : ℝ) +
          (approximateAdditiveEnergyOf 1 (Wᵢ (chosen 1)) : ℝ) +
          (approximateAdditiveEnergyOf 1 (Wᵢ (chosen 2)) : ℝ) +
          (approximateAdditiveEnergyOf 1 (Wᵢ (chosen 3)) : ℝ) ≤ 4*E := by
      linarith [hclass (chosen 0),hclass (chosen 1),hclass (chosen 2),hclass (chosen 3)]
    have hK : 0 ≤ 9*K^4 := by positivity
    have hshifted : (approximateAdditiveEnergyOf 1 W' : ℝ) ≤ 9*K^4*E := by
      have hprod := mul_le_mul_of_nonneg_left hSum hK
      change 4*(approximateAdditiveEnergyOf 1 W' : ℝ) ≤
        9*K^4*((approximateAdditiveEnergyOf 1 (Wᵢ (chosen 0)) : ℝ) +
          (approximateAdditiveEnergyOf 1 (Wᵢ (chosen 1)) : ℝ) +
          (approximateAdditiveEnergyOf 1 (Wᵢ (chosen 2)) : ℝ) +
          (approximateAdditiveEnergyOf 1 (Wᵢ (chosen 3)) : ℝ)) at henergy
      nlinarith
    have htransfer : approximateAdditiveEnergyOf 1 W ≤
        (4*Nat.ceil (1+4*D)+6)*approximateAdditiveEnergyOf 1 W' :=
      (approximateAdditiveEnergyOf_perturbation_le hpert).trans
        (approximateAdditiveEnergyOf_le_natCeil_mul_unit _ _)
    have htransferReal :
        (approximateAdditiveEnergyOf 1 W : ℝ) ≤
          (4*Nat.ceil (1+4*D)+6)*(approximateAdditiveEnergyOf 1 W' : ℝ) := by
      exact_mod_cast htransfer
    exact htransferReal.trans (mul_le_mul_of_nonneg_left hshifted (by positivity))


end TaoTrudgianYang2025

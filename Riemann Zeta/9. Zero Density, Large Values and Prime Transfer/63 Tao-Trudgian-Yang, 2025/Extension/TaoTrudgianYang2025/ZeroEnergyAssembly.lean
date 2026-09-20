import TaoTrudgianYang2025.ClassicalSlabEnergyTransfer

/-!
# Multiplicity-preserving zero-energy assembly

Restriction and reflection act on the indexed copies, not merely on the
set of distinct ordinates. These bridges support the dyadic assembly from
positive zero slabs to the paper's symmetric rectangle.
-/

noncomputable section

namespace TaoTrudgianYang2025

open RiemannZeta.GuthMaynard

/-- Injectively restricting the index set cannot increase additive energy.
This statement retains repeated values at distinct indices. -/
theorem approximateAdditiveEnergyOf_comp_injective_le
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (r : ℝ) (W : κ → ℝ) (f : ι → κ) (hf : Function.Injective f) :
    approximateAdditiveEnergyOf r (W ∘ f) ≤ approximateAdditiveEnergyOf r W := by
  classical
  unfold approximateAdditiveEnergyOf
  apply Finset.card_le_card_of_injOn (fun q => f ∘ q)
  · intro q hq
    simpa only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
      Function.comp_apply] using hq
  · intro q _ p _ hqp
    funext i
    exact hf (congrFun hqp i)

/-- A bijective reindexing preserves the full indexed energy exactly. -/
theorem approximateAdditiveEnergyOf_comp_equiv
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (r : ℝ) (W : κ → ℝ) (e : ι ≃ κ) :
    approximateAdditiveEnergyOf r (W ∘ e) = approximateAdditiveEnergyOf r W := by
  apply le_antisymm (approximateAdditiveEnergyOf_comp_injective_le r W e e.injective)
  have h := approximateAdditiveEnergyOf_comp_injective_le r (W ∘ e) e.symm e.symm.injective
  simpa only [Function.comp_def, Equiv.apply_symm_apply] using h

/-- Reflection preserves the tolerance of every indexed additive relation. -/
theorem approximateAdditiveEnergyOf_neg
    {ι : Type*} [Fintype ι] (r : ℝ) (W : ι → ℝ) :
    approximateAdditiveEnergyOf r (fun x => -W x) = approximateAdditiveEnergyOf r W := by
  classical
  unfold approximateAdditiveEnergyOf
  congr 1
  ext q
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have heq : -W (q 0) + -W (q 1) - -W (q 2) - -W (q 3) =
      -(W (q 0) + W (q 1) - W (q 2) - W (q 3)) := by ring
  rw [heq, abs_neg]

/-- Inclusion of weighted finite sets preserves each individual copy. -/
def weightedCopyInclusion {α : Type*} [DecidableEq α]
    {S T : Finset α} (weight : α → ℕ) (hST : S ⊆ T) :
    WeightedCopy S weight → WeightedCopy T weight :=
  fun x => ⟨⟨x.1.1, hST x.1.2⟩, x.2⟩

theorem weightedCopyInclusion_injective {α : Type*} [DecidableEq α]
    {S T : Finset α} (weight : α → ℕ) (hST : S ⊆ T) :
    Function.Injective (weightedCopyInclusion weight hST) := by
  intro x y h
  obtain ⟨x, ix⟩ := x
  obtain ⟨y, iy⟩ := y
  have hxy : x = y := Subtype.ext (congrArg (fun z => z.1.1) h)
  subst y
  have hi : ix = iy := Fin.ext (congrArg (fun z => z.2.val) h)
  exact congrArg (Sigma.mk x) hi

/-- Finite-set restriction is energy-monotone with the original weights. -/
theorem weightedCopy_energy_mono {α : Type*} [DecidableEq α]
    {S T : Finset α} (weight : α → ℕ) (hST : S ⊆ T)
    (r : ℝ) (W : α → ℝ) :
    approximateAdditiveEnergyOf r (fun x : WeightedCopy S weight => W x.1.1) ≤
      approximateAdditiveEnergyOf r (fun x : WeightedCopy T weight => W x.1.1) :=
  approximateAdditiveEnergyOf_comp_injective_le r
    (fun x : WeightedCopy T weight => W x.1.1)
    (weightedCopyInclusion weight hST) (weightedCopyInclusion_injective weight hST)

/-- A subfamily can be transferred to any containing finite set, even when
the original ambient set is not contained in the new one. -/
theorem weightedCopy_family_energy_le
    {α ι : Type*} [DecidableEq α] [Fintype ι]
    (S T : Finset α) (weight : α → ℕ) (f : ι → WeightedCopy S weight)
    (hf : Function.Injective f) (hT : ∀ i, (f i).1.1 ∈ T)
    (r : ℝ) (W : α → ℝ) :
    approximateAdditiveEnergyOf r (fun i => W (f i).1.1) ≤
      approximateAdditiveEnergyOf r (fun x : WeightedCopy T weight => W x.1.1) := by
  let g : ι → WeightedCopy T weight := fun i => ⟨⟨(f i).1.1, hT i⟩, (f i).2⟩
  have hg : Function.Injective g := by
    intro i j hij
    apply hf
    have hz : (f i).1 = (f j).1 := Subtype.ext (congrArg (fun z => z.1.1) hij)
    apply Sigma.ext hz
    apply (Fin.heq_ext_iff (congrArg (fun z : ↥S => weight z.1) hz)).mpr
    exact congrArg (fun z => z.2.val) hij
  exact approximateAdditiveEnergyOf_comp_injective_le r
    (fun x : WeightedCopy T weight => W x.1.1) g hg

/-- An indexed subfamily of paper zeros in a positive slab is bounded by
the actual multiplicity-preserving slab energy. -/
theorem zeroCopy_family_energy_le_classicalSlab
    {ι : Type*} [Fintype ι] (σ T H : ℝ) (f : ι → ZeroCopy σ T)
    (hf : Function.Injective f)
    (hH : ∀ i, H ≤ ((f i).1 : ℂ).im ∧ ((f i).1 : ℂ).im ≤ 2 * H) :
    approximateAdditiveEnergyOf 1 (fun i => ((f i).1 : ℂ).im) ≤
      classicalSlabZeroEnergy σ H := by
  apply weightedCopy_family_energy_le (paperZeros σ T) (zerosInRect σ 1 H (2 * H))
    (analyticVanishingOrder riemannZeta) f hf _ 1 Complex.im
  intro i
  have hz := (mem_paperZeros_iff ((f i).1 : ℂ)).mp (f i).1.2
  rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff, mem_ZeroRectangle]
  exact ⟨⟨hz.1, hz.2.1, (hH i).1, (hH i).2⟩, hz.2.2.2⟩

/-- Reflection maps every copy in a negative slab to a positive-slab copy
using the proved equality of conjugate analytic vanishing orders. -/
theorem zeroCopy_family_energy_le_classicalSlab_of_neg
    {ι : Type*} [Fintype ι] (σ T H : ℝ) (f : ι → ZeroCopy σ T)
    (hf : Function.Injective f)
    (hH : ∀ i, H ≤ -((f i).1 : ℂ).im ∧ -((f i).1 : ℂ).im ≤ 2 * H) :
    approximateAdditiveEnergyOf 1 (fun i => ((f i).1 : ℂ).im) ≤
      classicalSlabZeroEnergy σ H := by
  let g := zeroCopyConjEquiv σ T ∘ f
  have hg : Function.Injective g := (zeroCopyConjEquiv σ T).injective.comp hf
  have him (i : ι) : ((g i).1 : ℂ).im = -((f i).1 : ℂ).im := by
    rfl
  have henergy := zeroCopy_family_energy_le_classicalSlab σ T H g hg (by
    intro i
    rw [him]
    exact hH i)
  simpa only [him, approximateAdditiveEnergyOf_neg] using henergy

/-- A bounded-height indexed subfamily is controlled by the finite energy
of the fixed low-height paper rectangle. -/
theorem zeroCopy_family_energy_le_low_height
    {ι : Type*} [Fintype ι] (σ T H : ℝ) (f : ι → ZeroCopy σ T)
    (hf : Function.Injective f) (hH : ∀ i, |((f i).1 : ℂ).im| ≤ H) :
    approximateAdditiveEnergyOf 1 (fun i => ((f i).1 : ℂ).im) ≤
      zeroAdditiveEnergy σ H := by
  apply weightedCopy_family_energy_le (paperZeros σ T) (paperZeros σ H)
    (analyticVanishingOrder riemannZeta) f hf _ 1 Complex.im
  intro i
  have hz := (mem_paperZeros_iff ((f i).1 : ℂ)).mp (f i).1.2
  exact (mem_paperZeros_iff _).mpr ⟨hz.1, hz.2.1, hH i, hz.2.2.2⟩

/-- A bounded positive ordinate above the low-height cutoff belongs to a
dyadic slab with a logarithmically bounded index. The slab starts no higher
than the ordinate, even for the terminal partially occupied slab. -/
theorem exists_bounded_dyadic_slab
    (H T x : ℝ) (hH : 1 ≤ H) (hxH : H ≤ x) (hxT : x ≤ T) :
    ∃ n : Fin (⌊Real.logb 2 T⌋₊ + 1),
      H ≤ H * (2 : ℝ) ^ (n : ℕ) ∧
        H * (2 : ℝ) ^ (n : ℕ) ≤ x ∧
        x ≤ 2 * (H * (2 : ℝ) ^ (n : ℕ)) := by
  have hHpos : 0 < H := zero_lt_one.trans_le hH
  have hTpos : 0 < T := (hHpos.trans_le hxH).trans_le hxT
  obtain ⟨n, hnL, hnU⟩ := exists_nat_pow_near
    ((one_le_div hHpos).mpr hxH) (by norm_num : (1 : ℝ) < 2)
  have hpowpos : 0 < (2 : ℝ) ^ n := by positivity
  have hlow : H * (2 : ℝ) ^ n ≤ x := by
    have h := (le_div_iff₀ hHpos).mp hnL
    nlinarith
  have hupp : x ≤ 2 * (H * (2 : ℝ) ^ n) := by
    have h := (div_lt_iff₀ hHpos).mp hnU
    rw [pow_succ] at h
    nlinarith
  have hpowT : (2 : ℝ) ^ n ≤ T := by nlinarith
  have hnlog : (n : ℝ) ≤ Real.logb 2 T := by
    apply (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) hTpos).mpr
    simpa only [Real.rpow_natCast] using hpowT
  have hn : n ≤ ⌊Real.logb 2 T⌋₊ := Nat.le_floor hnlog
  refine ⟨⟨n, by omega⟩, ?_, hlow, hupp⟩
  have hpowone : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  nlinarith

/-- A low-height color, or a signed dyadic positive-height slab. -/
abbrev ZeroDyadicColor (T : ℝ) := Option (Bool × Fin (⌊Real.logb 2 T⌋₊ + 1))

/-- The geometric assertion represented by a zero's dyadic color. -/
def ZeroDyadicColorCondition (H T t : ℝ) (c : ZeroDyadicColor T) : Prop :=
  match c with
  | none => |t| ≤ H
  | some (negative, n) =>
      let U := H * (2 : ℝ) ^ (n : ℕ)
      H ≤ U ∧ U ≤ (if negative then -t else t) ∧ (if negative then -t else t) ≤ 2 * U

/-- Every multiplicity copy receives a signed dyadic color with the exact
source ordinate retained. -/
theorem exists_zeroDyadicColor (σ T H : ℝ) (hH : 1 ≤ H) :
    ∃ color : ZeroCopy σ T → ZeroDyadicColor T,
      ∀ z, ZeroDyadicColorCondition H T ((z.1 : ℂ).im) (color z) := by
  classical
  have hex : ∀ z : ZeroCopy σ T, ∃ c : ZeroDyadicColor T,
      ZeroDyadicColorCondition H T ((z.1 : ℂ).im) c := by
    intro z
    by_cases hlow : |(z.1 : ℂ).im| ≤ H
    · exact ⟨none, hlow⟩
    have hz := (mem_paperZeros_iff (z.1 : ℂ)).mp z.1.2
    obtain ⟨n, hnH, hnL, hnU⟩ := exists_bounded_dyadic_slab H T |(z.1 : ℂ).im|
      hH (le_of_not_ge hlow) hz.2.2.1
    by_cases hsign : 0 ≤ (z.1 : ℂ).im
    · refine ⟨some (false, n), hnH, ?_, ?_⟩
      · simpa only [Bool.false_eq_true, ↓reduceIte, abs_of_nonneg hsign] using hnL
      · simpa only [Bool.false_eq_true, ↓reduceIte, abs_of_nonneg hsign] using hnU
    · refine ⟨some (true, n), hnH, ?_, ?_⟩
      · simpa only [↓reduceIte, abs_of_neg (lt_of_not_ge hsign)] using hnL
      · simpa only [↓reduceIte, abs_of_neg (lt_of_not_ge hsign)] using hnU
  choose color hcolor using hex
  exact ⟨color, hcolor⟩

/-- Finite symmetric-rectangle assembly. All negative classes are reflected
with multiplicity, and every positive class is injected into its true slab.
Only a logarithmic number of colors is used. -/
theorem zeroAdditiveEnergy_le_dyadicSlabEnergy
    (σ T H M : ℝ) (hH : 1 ≤ H) (hM : 0 ≤ M)
    (hlow : (zeroAdditiveEnergy σ H : ℝ) ≤ M)
    (hslab : ∀ U : ℝ, H ≤ U → U ≤ T → (classicalSlabZeroEnergy σ U : ℝ) ≤ M) :
    (zeroAdditiveEnergy σ T : ℝ) ≤
      9 * (Fintype.card (ZeroDyadicColor T) : ℝ) ^ 4 * M := by
  classical
  obtain ⟨color, hcolor⟩ := exists_zeroDyadicColor σ T H hH
  let W : ZeroCopy σ T → ℝ := fun z => (z.1 : ℂ).im
  obtain ⟨label, henergy⟩ := exists_energy_color_classes W color
  let Wᵢ := fun i : Fin 4 => fun x : EnergyColorFiber color (label i) => W x.1
  have hclass (i : Fin 4) : (approximateAdditiveEnergyOf 1 (Wᵢ i) : ℝ) ≤ M := by
    have hspec (x : EnergyColorFiber color (label i)) :
        ZeroDyadicColorCondition H T (W x.1) (label i) := by
      simpa only [x.2] using hcolor x.1
    cases isEmpty_or_nonempty (EnergyColorFiber color (label i)) with
    | inl hempty =>
      have he : approximateAdditiveEnergyOf 1 (Wᵢ i) = 0 := by
        simp [approximateAdditiveEnergyOf]
      simpa only [he, Nat.cast_zero] using hM
    | inr hnonempty =>
      let x₀ := Classical.choice hnonempty
      have hz := (mem_paperZeros_iff (x₀.1.1 : ℂ)).mp x₀.1.1.2
      rcases Option.eq_none_or_eq_some (label i) with hlabel | ⟨c, hlabel⟩
      ·
        have hlowclass := zeroCopy_family_energy_le_low_height σ T H
          (fun x : EnergyColorFiber color (label i) => x.1) Subtype.val_injective (by
            intro x
            simpa only [hlabel, ZeroDyadicColorCondition] using hspec x)
        exact (show (approximateAdditiveEnergyOf 1 (Wᵢ i) : ℝ) ≤
          zeroAdditiveEnergy σ H by exact_mod_cast hlowclass).trans hlow
      ·
        obtain ⟨negative, n⟩ := c
        let U := H * (2 : ℝ) ^ (n : ℕ)
        have hspec' (x : EnergyColorFiber color (label i)) :
            H ≤ U ∧ U ≤ (if negative then -W x.1 else W x.1) ∧
              (if negative then -W x.1 else W x.1) ≤ 2 * U := by
          simpa only [hlabel, ZeroDyadicColorCondition] using hspec x
        have hUT : U ≤ T := by
          have h := (hspec' x₀).2.1
          cases negative <;> simp only [Bool.false_eq_true, ↓reduceIte] at h
          · exact (h.trans (le_abs_self _)).trans hz.2.2.1
          · exact (h.trans (neg_le_abs _)).trans hz.2.2.1
        have hbound := hslab U (hspec' x₀).1 hUT
        have hclassSlab : approximateAdditiveEnergyOf 1 (Wᵢ i) ≤
            classicalSlabZeroEnergy σ U := by
          cases negative
          · apply zeroCopy_family_energy_le_classicalSlab σ T U
              (fun x : EnergyColorFiber color (label i) => x.1) Subtype.val_injective
            intro x
            exact (hspec' x).2
          · apply zeroCopy_family_energy_le_classicalSlab_of_neg σ T U
              (fun x : EnergyColorFiber color (label i) => x.1) Subtype.val_injective
            intro x
            exact (hspec' x).2
        exact (show (approximateAdditiveEnergyOf 1 (Wᵢ i) : ℝ) ≤
          classicalSlabZeroEnergy σ U by exact_mod_cast hclassSlab).trans hbound
  have hsum : (approximateAdditiveEnergyOf 1 (Wᵢ 0) : ℝ) +
      (approximateAdditiveEnergyOf 1 (Wᵢ 1) : ℝ) +
      (approximateAdditiveEnergyOf 1 (Wᵢ 2) : ℝ) +
      (approximateAdditiveEnergyOf 1 (Wᵢ 3) : ℝ) ≤ 4 * M := by
    linarith [hclass 0, hclass 1, hclass 2, hclass 3]
  have hfactor : 0 ≤ 9 * (Fintype.card (ZeroDyadicColor T) : ℝ) ^ 4 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hsum hfactor
  change 4 * (zeroAdditiveEnergy σ T : ℝ) ≤
    9 * (Fintype.card (ZeroDyadicColor T) : ℝ) ^ 4 *
      ((approximateAdditiveEnergyOf 1 (Wᵢ 0) : ℝ) +
        (approximateAdditiveEnergyOf 1 (Wᵢ 1) : ℝ) +
        (approximateAdditiveEnergyOf 1 (Wᵢ 2) : ℝ) +
        (approximateAdditiveEnergyOf 1 (Wᵢ 3) : ℝ)) at henergy
  nlinarith

/-- The logarithmic number of signed dyadic colors costs an arbitrarily
small physical-height power. -/
theorem eventually_zeroDyadicColor_loss_le_rpow
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ T : ℝ in Filter.atTop,
      9 * (Fintype.card (ZeroDyadicColor T) : ℝ) ^ 4 ≤ T ^ η := by
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsmall := eventually_one_add_const_mul_log_le_rpow
    (3 + 2 / Real.log 2) (η / 8) (by linarith)
  have hnine := (tendsto_rpow_atTop (by linarith : 0 < η / 2)).eventually
    (Filter.eventually_ge_atTop (9 : ℝ))
  filter_upwards [hsmall, hnine, Filter.eventually_ge_atTop (8 : ℝ)] with
    T hsmall hnine hT
  have hTpos : 0 < T := by linarith
  have hlogone : 1 ≤ Real.log T := by
    have he : Real.exp 1 ≤ T := Real.exp_one_lt_three.le.trans (by linarith)
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) he
  have hlogb : 0 ≤ Real.logb 2 T := Real.logb_nonneg (by norm_num) (by linarith)
  have hfloor := Nat.floor_le hlogb
  have hcard : (Fintype.card (ZeroDyadicColor T) : ℝ) ≤ T ^ (η / 8) := by
    simp only [ZeroDyadicColor, Fintype.card_option, Fintype.card_prod,
      Fintype.card_bool, Fintype.card_fin, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_one]
    simp only [Real.logb] at hfloor ⊢
    rw [show (3 + 2 / Real.log 2) * Real.log T =
      3 * Real.log T + 2 * (Real.log T / Real.log 2) by ring] at hsmall
    nlinarith
  calc
    9 * (Fintype.card (ZeroDyadicColor T) : ℝ) ^ 4 ≤ 9 * (T ^ (η / 8)) ^ 4 := by
      gcongr
    _ = 9 * T ^ (η / 2) := by
      rw [← Real.rpow_natCast (T ^ (η / 8)) 4, ← Real.rpow_mul hTpos.le]
      congr 2
      norm_num
      ring
    _ ≤ T ^ (η / 2) * T ^ (η / 2) :=
      mul_le_mul_of_nonneg_right hnine (Real.rpow_nonneg hTpos.le _)
    _ = T ^ η := by rw [← Real.rpow_add hTpos]; congr 1; ring

/-- An eventual positive-slab estimate gives the symmetric paper-rectangle
estimate with an arbitrary epsilon loss. Bounded-height zeros are absorbed
using their actual finite energy; negative heights use conjugate copies. -/
theorem zeroAdditiveEnergy_bound_of_eventual_slab_bound
    (σ q C : ℝ) (hq : 0 ≤ q)
    (hslab : ∀ᶠ T : ℝ in Filter.atTop,
      (classicalSlabZeroEnergy σ T : ℝ) ≤ C * T ^ q) :
    ∀ η : ℝ, 0 < η → ∃ K : ℝ, 1 ≤ K ∧ ∀ᶠ T : ℝ in Filter.atTop,
      (zeroAdditiveEnergy σ T : ℝ) ≤ K * T ^ (q + η) := by
  intro η hη
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.mp hslab
  let H := max 1 T₀
  let K : ℝ := max 1 (max C (zeroAdditiveEnergy σ H : ℝ))
  have hK : 1 ≤ K := le_max_left _ _
  have hKC : C ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hKE : (zeroAdditiveEnergy σ H : ℝ) ≤ K :=
    (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨K, hK, ?_⟩
  filter_upwards [eventually_zeroDyadicColor_loss_le_rpow η hη,
    Filter.eventually_ge_atTop (1 : ℝ)] with T hcolors hT
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hTq : 1 ≤ T ^ q := Real.one_le_rpow hT hq
  have hbound := zeroAdditiveEnergy_le_dyadicSlabEnergy σ T H (K * T ^ q)
    (le_max_left _ _) (by positivity)
    (hKE.trans (le_mul_of_one_le_right hKpos.le hTq)) (by
      intro U hHU hUT
      have hUpos : 0 < U := (zero_lt_one.trans_le (le_max_left _ _)).trans_le hHU
      exact (hT₀ U ((le_max_right _ _).trans hHU)).trans
        (mul_le_mul hKC (Real.rpow_le_rpow hUpos.le hUT hq)
          (Real.rpow_nonneg hUpos.le _) hKpos.le))
  calc
    (zeroAdditiveEnergy σ T : ℝ) ≤
        9 * (Fintype.card (ZeroDyadicColor T) : ℝ) ^ 4 * (K * T ^ q) := hbound
    _ ≤ T ^ η * (K * T ^ q) :=
      mul_le_mul_of_nonneg_right hcolors (by positivity)
    _ = K * T ^ (q + η) := by rw [Real.rpow_add hTpos]; ring

/-- Source-facing zero-energy transfer from the two uniform large-value
energy hypotheses. The conclusion is the paper's shifted symmetric-rectangle
predicate, with analytic multiplicity and every epsilon quantifier retained. -/
theorem isZeroDensityEnergyBound_of_uniform_energy_bounds
    (σ B τ₀ : ℝ) (hσ : 1 / 2 < σ) (hσUpper : σ < 1)
    (hB : 0 ≤ B) (hτ₀ : 0 < τ₀)
    (hZeta : ∀ τ : ℝ, 1 ≤ τ → IsZetaLargeValueEnergyBound σ τ (B * τ))
    (hGeneral : ∀ τ : ℝ, τ₀ ≤ τ → IsLargeValueEnergyBound σ τ (B * τ)) :
    IsZeroDensityEnergyBound σ (B / (1 - σ)) := by
  intro ε hε
  obtain ⟨δ, hδ, _hσδ, C, _hC, hslab⟩ :=
    classicalSlabZeroEnergy_bound_of_uniform_energy_bounds σ B τ₀ hσ hσUpper.le
      hB hτ₀ hZeta hGeneral (ε / 2) (by linarith)
  obtain ⟨K, hK, hglobal⟩ := zeroAdditiveEnergy_bound_of_eventual_slab_bound
    (σ - δ) (B + ε / 2) C (by linarith) hslab (ε / 2) (by linarith)
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.mp hglobal
  let Cfinal := max K T₀
  have hCfinal : 1 ≤ Cfinal := hK.trans (le_max_left _ _)
  refine ⟨Cfinal, hCfinal, δ, hδ, ?_⟩
  intro T hT
  have hp := hT₀ T ((le_max_right _ _).trans hT)
  have hTpos : 0 < T := zero_lt_one.trans_le (hCfinal.trans hT)
  have hexponent : B / (1 - σ) * (1 - σ) + ε = (B + ε / 2) + ε / 2 := by
    rw [div_mul_cancel₀ B (by linarith : 1 - σ ≠ 0)]
    ring
  rw [hexponent]
  exact hp.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
    (Real.rpow_nonneg hTpos.le _))

end TaoTrudgianYang2025

import TaoTrudgianYang2025.EnergyExponents
import Mathlib.Topology.MetricSpace.Sequences

/-!
# Uniform zeta energy estimates over compact height-exponent ranges

A finite open cover makes the constants and threshold window uniform before
the source cutoff and threshold powers are chosen. This is the quantifier
bridge between pointwise energy bounds and the zero-energy transfer.
-/

noncomputable section

namespace TaoTrudgianYang2025

/-- Pointwise zeta energy bounds with exponent `B*τ` yield one uniform
estimate on a neighborhood of a closed physical height-exponent interval.
The neighborhood includes small finite-scale excursions beyond its endpoints.
A lower threshold
bound suffices: the pattern can use the lower edge of the chosen threshold
window without changing any coefficient or ordinate. -/
theorem zetaEnergyBound_uniform_near_logScale_interval
    (σ B l u : ℝ) (hB : 0 ≤ B) (hlu : l ≤ u)
    (hLV : ∀ τ ∈ Set.Icc l u, IsZetaLargeValueEnergyBound σ τ (B * τ)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
        ∀ P : ZetaLargeValuePattern,
          C ≤ P.N →
          (∃ α ∈ Set.Icc l u, |Real.logb P.N P.T - α| ≤ δ) →
          P.N ^ (σ - δ) ≤ P.V →
          (finsetAdditiveEnergy P.ordinates : ℝ) ≤ C * P.T ^ B * P.N ^ ε := by
  intro ε hε
  classical
  choose C₀ hC₀ δ₀ hδ₀ hbound using
    fun τ : Set.Icc l u => hLV τ τ.2 (ε / 2) (by linarith)
  let w : Set.Icc l u → ℝ := fun τ => min (δ₀ τ) (ε / (2 * (B + 1)))
  have hw (τ : Set.Icc l u) : 0 < w τ := by
    exact lt_min (hδ₀ τ) (div_pos hε (by positivity))
  let U : Set.Icc l u → Set ℝ :=
    fun τ => Set.Ioo (τ.1 - w τ / 2) (τ.1 + w τ / 2)
  have hcover : Set.Icc l u ⊆ ⋃ τ, U τ := by
    intro x hx
    refine Set.mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
    exact ⟨by linarith [hw ⟨x, hx⟩], by linarith [hw ⟨x, hx⟩]⟩
  obtain ⟨s, hs⟩ := isCompact_Icc.elim_finite_subcover U (fun _ => isOpen_Ioo) hcover
  have hsne : s.Nonempty := by
    obtain ⟨τ, hτ, _⟩ := Set.mem_iUnion₂.mp (hs (show l ∈ Set.Icc l u from ⟨le_rfl, hlu⟩))
    exact ⟨τ, hτ⟩
  let C := max 1 (s.sup' hsne C₀)
  let δ := s.inf' hsne w / 2
  have hδ : 0 < δ := div_pos
    ((Finset.lt_inf'_iff hsne).mpr (fun τ _ => hw τ)) (by norm_num)
  refine ⟨C, le_max_left _ _, δ, hδ, ?_⟩
  intro P hCN hscale hV
  let α := Real.logb P.N P.T
  obtain ⟨β, hβ, hαβ⟩ := hscale
  obtain ⟨τ, hτ, hβτ⟩ := Set.mem_iUnion₂.mp (hs hβ)
  have hδw : δ ≤ w τ / 2 :=
    div_le_div_of_nonneg_right (Finset.inf'_le w hτ) (by norm_num)
  have hβτ' : τ.1 - w τ / 2 < β ∧ β < τ.1 + w τ / 2 := hβτ
  have hαβ' : -δ ≤ α - β ∧ α - β ≤ δ := abs_le.mp hαβ
  have hα' : τ.1 - w τ < α ∧ α < τ.1 + w τ := by
    constructor <;> linarith [hβτ'.1, hβτ'.2, hαβ'.1, hαβ'.2]
  have hwδ : w τ ≤ δ₀ τ := min_le_left _ _
  have hδle : δ ≤ δ₀ τ := by linarith [hw τ]
  have hCτ : C₀ τ ≤ C :=
    (Finset.le_sup' C₀ hτ).trans (le_max_right _ _)
  have hNpos : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hlowV : P.N ^ (σ - δ₀ τ) ≤ P.V :=
    (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith)).trans hV
  let Q : ZetaLargeValuePattern := {
    P with
    V := P.N ^ (σ - δ₀ τ)
    V_pos := Real.rpow_pos_of_pos hNpos _
    large := fun t ht => hlowV.trans (P.large t ht)
  }
  have hTL : Q.N ^ (τ.1 - δ₀ τ) ≤ Q.T := by
    apply (Real.le_logb_iff_rpow_le P.one_lt_N P.T_pos).mp
    change τ.1 - δ₀ τ ≤ α
    linarith [hα'.1]
  have hTU : Q.T ≤ Q.N ^ (τ.1 + δ₀ τ) := by
    apply (Real.logb_le_iff_le_rpow P.one_lt_N P.T_pos).mp
    change α ≤ τ.1 + δ₀ τ
    linarith [hα'.2]
  have hVU : Q.V ≤ Q.N ^ (σ + δ₀ τ) :=
    Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith [hδ₀ τ])
  have henergy : (finsetAdditiveEnergy P.ordinates : ℝ) ≤
      C₀ τ * P.N ^ (B * τ.1 + ε / 2) :=
    hbound τ Q (hCτ.trans hCN) hTL hTU le_rfl hVU
  have hwSmall : w τ ≤ ε / (2 * (B + 1)) := min_le_right _ _
  have hwMul : w τ * (2 * (B + 1)) ≤ ε :=
    (le_div_iff₀ (by positivity : 0 < 2 * (B + 1))).mp hwSmall
  have hnear := mul_le_mul_of_nonneg_left hα'.1.le hB
  have hexponent : B * τ.1 + ε / 2 ≤ B * α + ε := by
    nlinarith [hw τ]
  have hid : P.N ^ (B * α + ε) = P.T ^ B * P.N ^ ε := by
    rw [Real.rpow_add hNpos, mul_comm B α, Real.rpow_mul hNpos.le]
    rw [show P.N ^ α = P.T from
      Real.rpow_logb hNpos P.one_lt_N.ne' P.T_pos]
  calc
    (finsetAdditiveEnergy P.ordinates : ℝ) ≤ C₀ τ * P.N ^ (B * τ.1 + ε / 2) :=
      henergy
    _ ≤ C * P.N ^ (B * α + ε) :=
      mul_le_mul hCτ
        (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le hexponent)
        (Real.rpow_nonneg hNpos.le _) (zero_le_one.trans (le_max_left _ _))
    _ = C * P.T ^ B * P.N ^ ε := by rw [hid]; ring

/-- Restriction of the neighborhood estimate to the closed scale interval. -/
theorem zetaEnergyBound_uniform_on_logScale_interval
    (σ B l u : ℝ) (hB : 0 ≤ B) (hlu : l ≤ u)
    (hLV : ∀ τ ∈ Set.Icc l u, IsZetaLargeValueEnergyBound σ τ (B * τ)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
        ∀ P : ZetaLargeValuePattern,
          C ≤ P.N →
          Real.logb P.N P.T ∈ Set.Icc l u →
          P.N ^ (σ - δ) ≤ P.V →
          (finsetAdditiveEnergy P.ordinates : ℝ) ≤ C * P.T ^ B * P.N ^ ε := by
  intro ε hε
  obtain ⟨C, hC, δ, hδ, hbound⟩ :=
    zetaEnergyBound_uniform_near_logScale_interval σ B l u hB hlu hLV ε hε
  refine ⟨C, hC, δ, hδ, ?_⟩
  intro P hCN hscale hV
  apply hbound P hCN ⟨Real.logb P.N P.T, hscale, ?_⟩ hV
  simpa using hδ.le

/-- General large-value version of compact-range uniformity. It applies to
arbitrary normalized coefficients, as required by the Type II branch. -/
theorem largeValueEnergyBound_uniform_near_logScale_interval
    (σ B l u : ℝ) (hB : 0 ≤ B) (hlu : l ≤ u)
    (hLV : ∀ τ ∈ Set.Icc l u, IsLargeValueEnergyBound σ τ (B * τ)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
        ∀ P : LargeValuePattern,
          C ≤ P.N →
          (∃ α ∈ Set.Icc l u, |Real.logb P.N P.T - α| ≤ δ) →
          P.N ^ (σ - δ) ≤ P.V →
          (finsetAdditiveEnergy P.ordinates : ℝ) ≤ C * P.T ^ B * P.N ^ ε := by
  intro ε hε
  classical
  choose C₀ hC₀ δ₀ hδ₀ hbound using
    fun τ : Set.Icc l u => hLV τ τ.2 (ε / 2) (by linarith)
  let w : Set.Icc l u → ℝ := fun τ => min (δ₀ τ) (ε / (2 * (B + 1)))
  have hw (τ : Set.Icc l u) : 0 < w τ := by
    exact lt_min (hδ₀ τ) (div_pos hε (by positivity))
  let U : Set.Icc l u → Set ℝ :=
    fun τ => Set.Ioo (τ.1 - w τ / 2) (τ.1 + w τ / 2)
  have hcover : Set.Icc l u ⊆ ⋃ τ, U τ := by
    intro x hx
    refine Set.mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
    exact ⟨by linarith [hw ⟨x, hx⟩], by linarith [hw ⟨x, hx⟩]⟩
  obtain ⟨s, hs⟩ := isCompact_Icc.elim_finite_subcover U (fun _ => isOpen_Ioo) hcover
  have hsne : s.Nonempty := by
    obtain ⟨τ, hτ, _⟩ := Set.mem_iUnion₂.mp (hs (show l ∈ Set.Icc l u from ⟨le_rfl, hlu⟩))
    exact ⟨τ, hτ⟩
  let C := max 1 (s.sup' hsne C₀)
  let δ := s.inf' hsne w / 2
  have hδ : 0 < δ := div_pos
    ((Finset.lt_inf'_iff hsne).mpr (fun τ _ => hw τ)) (by norm_num)
  refine ⟨C, le_max_left _ _, δ, hδ, ?_⟩
  intro P hCN hscale hV
  let α := Real.logb P.N P.T
  obtain ⟨β, hβ, hαβ⟩ := hscale
  obtain ⟨τ, hτ, hβτ⟩ := Set.mem_iUnion₂.mp (hs hβ)
  have hδw : δ ≤ w τ / 2 :=
    div_le_div_of_nonneg_right (Finset.inf'_le w hτ) (by norm_num)
  have hβτ' : τ.1 - w τ / 2 < β ∧ β < τ.1 + w τ / 2 := hβτ
  have hαβ' : -δ ≤ α - β ∧ α - β ≤ δ := abs_le.mp hαβ
  have hα' : τ.1 - w τ < α ∧ α < τ.1 + w τ := by
    constructor <;> linarith [hβτ'.1, hβτ'.2, hαβ'.1, hαβ'.2]
  have hwδ : w τ ≤ δ₀ τ := min_le_left _ _
  have hδle : δ ≤ δ₀ τ := by linarith [hw τ]
  have hCτ : C₀ τ ≤ C :=
    (Finset.le_sup' C₀ hτ).trans (le_max_right _ _)
  have hNpos : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hlowV : P.N ^ (σ - δ₀ τ) ≤ P.V :=
    (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith)).trans hV
  let Q : LargeValuePattern := {
    P with
    V := P.N ^ (σ - δ₀ τ)
    V_pos := Real.rpow_pos_of_pos hNpos _
    large := fun t ht => hlowV.trans (P.large t ht)
  }
  have hTL : Q.N ^ (τ.1 - δ₀ τ) ≤ Q.T := by
    apply (Real.le_logb_iff_rpow_le P.one_lt_N P.T_pos).mp
    change τ.1 - δ₀ τ ≤ α
    linarith [hα'.1]
  have hTU : Q.T ≤ Q.N ^ (τ.1 + δ₀ τ) := by
    apply (Real.logb_le_iff_le_rpow P.one_lt_N P.T_pos).mp
    change α ≤ τ.1 + δ₀ τ
    linarith [hα'.2]
  have hVU : Q.V ≤ Q.N ^ (σ + δ₀ τ) :=
    Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith [hδ₀ τ])
  have henergy : (finsetAdditiveEnergy P.ordinates : ℝ) ≤
      C₀ τ * P.N ^ (B * τ.1 + ε / 2) :=
    hbound τ Q (hCτ.trans hCN) hTL hTU le_rfl hVU
  have hwSmall : w τ ≤ ε / (2 * (B + 1)) := min_le_right _ _
  have hwMul : w τ * (2 * (B + 1)) ≤ ε :=
    (le_div_iff₀ (by positivity : 0 < 2 * (B + 1))).mp hwSmall
  have hnear := mul_le_mul_of_nonneg_left hα'.1.le hB
  have hexponent : B * τ.1 + ε / 2 ≤ B * α + ε := by
    nlinarith [hw τ]
  have hid : P.N ^ (B * α + ε) = P.T ^ B * P.N ^ ε := by
    rw [Real.rpow_add hNpos, mul_comm B α, Real.rpow_mul hNpos.le]
    rw [show P.N ^ α = P.T from
      Real.rpow_logb hNpos P.one_lt_N.ne' P.T_pos]
  calc
    (finsetAdditiveEnergy P.ordinates : ℝ) ≤ C₀ τ * P.N ^ (B * τ.1 + ε / 2) :=
      henergy
    _ ≤ C * P.N ^ (B * α + ε) :=
      mul_le_mul hCτ
        (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le hexponent)
        (Real.rpow_nonneg hNpos.le _) (zero_le_one.trans (le_max_left _ _))
    _ = C * P.T ^ B * P.N ^ ε := by rw [hid]; ring

end TaoTrudgianYang2025

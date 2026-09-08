import RiemannZeta.GuthMaynard.ClassicalDetector
import RiemannZeta.GuthMaynard.ClassicalLargeValues
import RiemannZeta.GuthMaynard.BetaDependence
import Mathlib.Analysis.Complex.PhragmenLindelof

open Complex Finset Set Topology
open scoped BigOperators

namespace RiemannZeta.GuthMaynard

open Filter Asymptotics PhragmenLindelof

/-- A Dirichlet polynomial on an arbitrary finite positive support. -/
noncomputable def finiteDirichletSeries
    (S : Finset ℕ) (a : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑ n ∈ S, a n * (n : ℂ) ^ (-s)

/-- The coefficient mass used to bound a finite Dirichlet polynomial in the
closed right half-plane. -/
noncomputable def finiteDirichletMass (S : Finset ℕ) (a : ℕ → ℂ) : ℝ :=
  ∑ n ∈ S, ‖a n‖

theorem norm_finiteDirichletSeries_le_mass
    (S : Finset ℕ) (a : ℕ → ℂ) (s : ℂ)
    (hS : ∀ n ∈ S, 0 < n) (hs : 0 ≤ s.re) :
    ‖finiteDirichletSeries S a s‖ ≤ finiteDirichletMass S a := by
  unfold finiteDirichletSeries finiteDirichletMass
  calc
    ‖∑ n ∈ S, a n * (n : ℂ) ^ (-s)‖ ≤
        ∑ n ∈ S, ‖a n * (n : ℂ) ^ (-s)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ S, ‖a n‖ := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul, Complex.norm_natCast_cpow_of_pos (hS n hn)]
      exact mul_le_of_le_one_right (norm_nonneg _) <|
        Real.rpow_le_one_of_one_le_of_nonpos
          (by exact_mod_cast (hS n hn)) (by simp [hs])

theorem differentiable_finiteDirichletSeries_add
    (S : Finset ℕ) (a : ℕ → ℂ) (z : ℂ) (hS : ∀ n ∈ S, 0 < n) :
    Differentiable ℂ (fun w : ℂ => finiteDirichletSeries S a (z + w)) := by
  intro w
  apply AnalyticAt.differentiableAt
  unfold finiteDirichletSeries
  have hEq :
      (fun u : ℂ => ∑ n ∈ S, a n * (n : ℂ) ^ (-(z + u))) =
        ∑ n ∈ S, fun u : ℂ => a n * (n : ℂ) ^ (-(z + u)) := by
    funext u
    simp
  rw [hEq]
  apply Finset.analyticAt_sum
  intro n hn
  have hnPos : 0 < n := hS n hn
  have hpow : AnalyticAt ℂ (fun u : ℂ => (n : ℂ) ^ (-(z + u))) w :=
    analyticAt_const.cpow ((analyticAt_const.add analyticAt_id).neg)
      (Complex.natCast_mem_slitPlane.mpr hnPos.ne')
  exact analyticAt_const.mul hpow

/-- Rational localization of a finite Dirichlet polynomial. -/
noncomputable def localizedFiniteDirichlet
    (S : Finset ℕ) (a : ℕ → ℂ) (k : ℕ) (z : ℂ) (H : ℝ) (w : ℂ) : ℂ :=
  (((H : ℂ) / (H + w)) ^ k) * finiteDirichletSeries S a (z + w)

theorem localizedFiniteDirichlet_le_mass
    (S : Finset ℕ) (a : ℕ → ℂ) (k : ℕ) (z w : ℂ) (H : ℝ)
    (hS : ∀ n ∈ S, 0 < n) (hH : 0 < H) (hz : 0 ≤ z.re) (hw : 0 ≤ w.re) :
    ‖localizedFiniteDirichlet S a k z H w‖ ≤ finiteDirichletMass S a := by
  rw [localizedFiniteDirichlet, norm_mul]
  calc
    ‖((H : ℂ) / (H + w)) ^ k‖ * ‖finiteDirichletSeries S a (z + w)‖ ≤
        1 * finiteDirichletMass S a := by
      gcongr
      · exact localizer_norm_le_one k H hH w hw
      · exact norm_finiteDirichletSeries_le_mass S a (z + w) hS (by simp; linarith)
    _ = finiteDirichletMass S a := one_mul _

theorem localizedFiniteDirichlet_halfPlane_bound
    (S : Finset ℕ) (a : ℕ → ℂ) (k : ℕ) (z : ℂ) (H C : ℝ)
    (hS : ∀ n ∈ S, 0 < n) (hH : 0 < H) (hz : 0 ≤ z.re)
    (hBoundary : ∀ y : ℝ,
      ‖localizedFiniteDirichlet S a k z H (y * I)‖ ≤ C)
    (w : ℂ) (hw : 0 ≤ w.re) :
    ‖localizedFiniteDirichlet S a k z H w‖ ≤ C := by
  apply PhragmenLindelof.right_half_plane_of_bounded_on_real
      (f := localizedFiniteDirichlet S a k z H)
  · exact (by
      unfold localizedFiniteDirichlet
      apply DifferentiableOn.diffContOnCl
      intro u hu
      have hne : (H : ℂ) + u ≠ 0 := by
        intro h
        have hre := congrArg Complex.re h
        simp only [add_re, ofReal_re, zero_re] at hre
        rw [closure_setOf_lt_re] at hu
        change 0 ≤ u.re at hu
        linarith
      exact ((((differentiableAt_const (c := (H : ℂ))).div
        ((differentiableAt_const (c := (H : ℂ))).add differentiableAt_id) hne).pow k).mul
          (differentiable_finiteDirichletSeries_add S a z hS u)).differentiableWithinAt)
  · refine ⟨1, by norm_num, 0, ?_⟩
    apply Asymptotics.IsBigO.of_bound (finiteDirichletMass S a)
    have hopen : ∀ᶠ u in (Bornology.cobounded ℂ ⊓ Filter.principal {u : ℂ | 0 < u.re}),
        0 < u.re := Filter.le_principal_iff.mp inf_le_right
    filter_upwards [hopen] with u hu
    simp only [zero_mul, Real.exp_zero, norm_one, mul_one]
    exact localizedFiniteDirichlet_le_mass S a k z u H hS hH hz hu.le
  · refine ⟨finiteDirichletMass S a, ?_⟩
    rw [eventually_map]
    exact Filter.eventually_atTop.mpr ⟨0, fun x hx =>
      localizedFiniteDirichlet_le_mass S a k z x H hS hH hz (by simpa using hx)⟩
  · exact hBoundary
  · exact hw

/-- A large value to the right of a fixed vertical line produces a comparably
large value on that line after a controlled ordinate displacement. -/
theorem exists_nearby_large_value_finiteDirichlet
    (S : Finset ℕ) (coeff : ℕ → ℂ) (k : ℕ) (z : ℂ) (H R A a : ℝ)
    (hS : ∀ n ∈ S, 0 < n) (hH : 0 < H) (hR : 0 < R) (hA : 0 < A)
    (hz : 0 ≤ z.re) (ha : 0 ≤ a)
    (hLarge : A ≤ ‖finiteDirichletSeries S coeff (z + a)‖)
    (hFactor : 3 / 4 < ‖((H : ℂ) / (H + (a : ℂ))) ^ k‖)
    (hExterior : finiteDirichletMass S coeff * (H / R) ^ k < (3 / 4) * A) :
    ∃ y : ℝ, |y| ≤ R ∧
      (3 / 4) * A ≤ ‖finiteDirichletSeries S coeff (z + y * I)‖ := by
  by_contra! hNo
  have hBoundary : ∀ y : ℝ,
      ‖localizedFiniteDirichlet S coeff k z H (y * I)‖ ≤ (3 / 4) * A := by
    intro y
    rw [localizedFiniteDirichlet, norm_mul]
    by_cases hy : |y| ≤ R
    · calc
        ‖((H : ℂ) / (H + (y : ℂ) * I)) ^ k‖ *
            ‖finiteDirichletSeries S coeff (z + (y : ℂ) * I)‖ ≤
            1 * ((3 / 4) * A) := by
          gcongr
          · exact localizer_norm_le_one k H hH (y * I) (by simp)
          · exact (hNo y hy).le
        _ = (3 / 4) * A := one_mul _
    · have hyR : R ≤ |y| := le_of_lt (lt_of_not_ge hy)
      calc
        ‖((H : ℂ) / (H + (y : ℂ) * I)) ^ k‖ *
            ‖finiteDirichletSeries S coeff (z + (y : ℂ) * I)‖ ≤
            (H / R) ^ k * finiteDirichletMass S coeff := by
          gcongr
          · exact localizer_norm_boundary_le k H R y hH hR hyR
          · exact norm_finiteDirichletSeries_le_mass S coeff
              (z + y * I) hS (by simp [hz])
        _ = finiteDirichletMass S coeff * (H / R) ^ k := by ring
        _ ≤ (3 / 4) * A := hExterior.le
  have hPL := localizedFiniteDirichlet_halfPlane_bound
    S coeff k z H ((3 / 4) * A) hS hH hz hBoundary (a : ℂ) (by simpa using ha)
  rw [localizedFiniteDirichlet, norm_mul] at hPL
  have hStrict : (3 / 4) * A <
      ‖((H : ℂ) / (H + (a : ℂ))) ^ k‖ *
        ‖finiteDirichletSeries S coeff (z + a)‖ := by
    calc
      (3 / 4) * A < ‖((H : ℂ) / (H + (a : ℂ))) ^ k‖ * A := by gcongr
      _ ≤ ‖((H : ℂ) / (H + (a : ℂ))) ^ k‖ *
          ‖finiteDirichletSeries S coeff (z + a)‖ := by gcongr
  exact (not_lt_of_ge hPL) hStrict

/-- The actual support of the nonconstant sharp zeta--Möbius convolution. -/
noncomputable def sharpMollifiedTailSupport (A X : ℕ) : Finset ℕ :=
  Ioc X (A * X)

/-- The finite analytic tail to which exact beta removal is applied. -/
noncomputable def sharpMollifiedTail (A X : ℕ) (s : ℂ) : ℂ :=
  finiteDirichletSeries (sharpMollifiedTailSupport A X)
    (sharpMollifiedCoeff A X) s

theorem sharpMollifiedTail_apply (A X : ℕ) (s : ℂ) :
    sharpMollifiedTail A X s =
      ∑ n ∈ Ioc X (A * X),
        sharpMollifiedCoeff A X n * (n : ℂ) ^ (-s) := rfl

theorem sharpMollifiedTailSupport_pos (A X n : ℕ)
    (hn : n ∈ sharpMollifiedTailSupport A X) : 0 < n := by
  rw [sharpMollifiedTailSupport, Finset.mem_Ioc] at hn
  omega

/-- A crude polynomial coefficient-mass bound, sufficient for rational
localization. The sharper divisor estimate is retained for large-values
normalization after localization. -/
theorem sharpMollifiedTail_mass_le_sq (A X : ℕ) :
    finiteDirichletMass (sharpMollifiedTailSupport A X)
        (sharpMollifiedCoeff A X) ≤ (A * X : ℝ) ^ 2 := by
  unfold finiteDirichletMass
  calc
    (∑ n ∈ sharpMollifiedTailSupport A X, ‖sharpMollifiedCoeff A X n‖) ≤
        ∑ _n ∈ sharpMollifiedTailSupport A X, (A * X : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      calc
        ‖sharpMollifiedCoeff A X n‖ ≤ (n.divisors.card : ℝ) :=
          norm_sharpMollifiedCoeff_le_divisors_card A X n
        _ ≤ (n : ℝ) := by exact_mod_cast Nat.card_divisors_le_self n
        _ ≤ (A * X : ℝ) := by
          exact_mod_cast (Finset.mem_Ioc.mp hn).2
    _ = ((sharpMollifiedTailSupport A X).card : ℝ) * (A * X : ℝ) := by simp
    _ ≤ (A * X : ℝ) * (A * X : ℝ) := by
      gcongr
      have hCard := Finset.card_le_card (show sharpMollifiedTailSupport A X ⊆
          Finset.Icc 1 (A * X) by
            intro n hn
            rw [sharpMollifiedTailSupport, Finset.mem_Ioc] at hn
            exact Finset.mem_Icc.mpr ⟨by omega, hn.2⟩)
      have hCard' : (sharpMollifiedTailSupport A X).card ≤ A * X := by
        simpa using hCard
      exact_mod_cast hCard'
    _ = (A * X : ℝ) ^ 2 := by ring

/-- The previously proved quantitative mollified-tail witness in the generic
finite-series representation used by beta removal. -/
theorem norm_sharpMollifiedTail_finiteSeries_ge {σ T : ℝ} {ρ : ℂ} (X : ℕ)
    (hT : 3 / 4 ≤ T) (hρmem : ρ ∈ zerosInRect σ 1 T (2 * T))
    (hσ : 0 < σ) (hX : 1 ≤ X) (hXA : X ≤ ⌊sharpZetaCutoff T⌋₊) :
    1 - 149 * sharpZetaCutoff T ^ (-ρ.re) *
        (∑ n ∈ Icc 1 X, (n : ℝ) ^ (-ρ.re)) ≤
      ‖sharpMollifiedTail ⌊sharpZetaCutoff T⌋₊ X ρ‖ := by
  simpa only [sharpMollifiedTail_apply] using
    norm_sharpMollifiedTail_ge X hT hρmem hσ hX hXA

/-- A polynomial mass times the rational-localizer decay is uniformly small
once the localizer degree dominates the mass exponent. -/
theorem rpow_mass_mul_localizer_lt_three_eighths
    (B δ T : ℝ) (k : ℕ) (hT : 8 ≤ T)
    (hExponent : 2 * (B + 1) ≤ δ * (k : ℝ)) :
    T ^ B * (T ^ (δ / 2) / T ^ δ) ^ k < 3 / 8 := by
  have hTpos : 0 < T := by linarith
  have hTone : 1 ≤ T := by linarith
  have hRatio : (T ^ (δ / 2) / T ^ δ) ^ k =
      T ^ ((-(δ / 2)) * (k : ℝ)) := by
    rw [← Real.rpow_sub hTpos]
    have hsub : δ / 2 - δ = -(δ / 2) := by ring
    rw [hsub, ← Real.rpow_natCast, ← Real.rpow_mul hTpos.le]
  have hPower : T ^ B * (T ^ (δ / 2) / T ^ δ) ^ k ≤ T ^ (-1 : ℝ) := by
    rw [hRatio, ← Real.rpow_add hTpos]
    apply Real.rpow_le_rpow_of_exponent_le hTone
    nlinarith
  have hInv : T ^ (-1 : ℝ) ≤ 1 / 8 := by
    rw [Real.rpow_neg_one]
    simpa only [one_div] using
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 8) hT
  exact hPower.trans_lt (hInv.trans_lt (by norm_num))

/-- Exact-beta removal for the actual sharp zeta--Möbius tail. The hypotheses
`hMass` and `hLarge` are concrete inequalities about that tail; subsequent
lemmas discharge them from the support bound and sharp zeta truncation. -/
theorem sharpMollifiedTail_beta_removal :
    ∀ δ : ℝ, 0 < δ → ∀ B : ℝ, 0 ≤ B →
      ∃ T₀ : ℝ, 8 ≤ T₀ ∧
        ∀ (σ T : ℝ) (ρ : ℂ) (A X : ℕ),
          1 / 2 ≤ σ → σ ≤ 1 → T₀ ≤ T →
          ρ ∈ zerosInRect σ 1 T (2 * T) → A = ⌊sharpZetaCutoff T⌋₊ →
          finiteDirichletMass (sharpMollifiedTailSupport A X)
              (sharpMollifiedCoeff A X) ≤ T ^ B →
          1 / 2 ≤ ‖sharpMollifiedTail A X ρ‖ →
          ∃ t : ℝ, |t - ρ.im| ≤ T ^ δ ∧
            3 / 8 ≤ ‖sharpMollifiedTail A X ((σ : ℂ) + I * (t : ℂ))‖ := by
  intro δ hδ B hB
  obtain ⟨k, hk⟩ := exists_nat_gt (2 * (B + 1) / δ)
  have hExponent : 2 * (B + 1) < δ * (k : ℝ) := by
    rw [div_lt_iff₀ hδ] at hk
    simpa only [mul_comm] using hk
  have hPowTendsto : Tendsto (fun T : ℝ => T ^ (δ / 2)) atTop atTop :=
    tendsto_rpow_atTop (by positivity)
  have hEventually : ∀ᶠ T : ℝ in atTop, 4 * (k : ℝ) < T ^ (δ / 2) :=
    hPowTendsto.eventually (eventually_gt_atTop (4 * (k : ℝ)))
  rw [eventually_atTop] at hEventually
  obtain ⟨Tfactor, hTfactor⟩ := hEventually
  let T₀ := max 8 Tfactor
  refine ⟨T₀, le_max_left _ _, ?_⟩
  intro σ T ρ A X hσLower hσUpper hT hρmem hA hMass hLarge
  have hTEight : 8 ≤ T := (le_max_left _ _).trans hT
  have hTFactor : Tfactor ≤ T := (le_max_right _ _).trans hT
  have hTpos : 0 < T := by linarith
  have hHpos : 0 < T ^ (δ / 2) := Real.rpow_pos_of_pos hTpos _
  have hRpos : 0 < T ^ δ := Real.rpow_pos_of_pos hTpos _
  have hRect := hρmem
  rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff,
    mem_ZeroRectangle] at hRect
  let displacement : ℝ := ρ.re - σ
  let z : ℂ := (σ : ℂ) + I * (ρ.im : ℂ)
  have hDisplacement : 0 ≤ displacement := by
    dsimp [displacement]
    linarith [hRect.1.1]
  have hDisplacementOne : displacement ≤ 1 := by
    dsimp [displacement]
    linarith [hRect.1.2, hσLower]
  have hz : 0 ≤ z.re := by
    dsimp [z]
    simp
    linarith
  have hza : z + (displacement : ℂ) = ρ := by
    apply Complex.ext
    · simp [z, displacement]
    · simp [z, displacement]
  have hFactor : 3 / 4 <
      ‖(((T ^ (δ / 2) : ℝ) : ℂ) /
        (((T ^ (δ / 2) : ℝ) : ℂ) + (displacement : ℂ))) ^ k‖ :=
    localizer_factor_gt_three_fourths k (T ^ (δ / 2)) displacement
      hHpos hDisplacement hDisplacementOne (hTfactor T hTFactor)
  have hExterior :
      finiteDirichletMass (sharpMollifiedTailSupport A X)
          (sharpMollifiedCoeff A X) *
        (T ^ (δ / 2) / T ^ δ) ^ k < (3 / 4) * (1 / 2) := by
    have hDecay := rpow_mass_mul_localizer_lt_three_eighths
      B δ T k hTEight hExponent.le
    have hRatioNonneg : 0 ≤ (T ^ (δ / 2) / T ^ δ) ^ k := by positivity
    calc
      finiteDirichletMass (sharpMollifiedTailSupport A X)
            (sharpMollifiedCoeff A X) * (T ^ (δ / 2) / T ^ δ) ^ k
          ≤ T ^ B * (T ^ (δ / 2) / T ^ δ) ^ k :=
        mul_le_mul_of_nonneg_right hMass hRatioNonneg
      _ < 3 / 8 := hDecay
      _ = (3 / 4) * (1 / 2) := by norm_num
  obtain ⟨y, hy, hyLarge⟩ := exists_nearby_large_value_finiteDirichlet
    (sharpMollifiedTailSupport A X) (sharpMollifiedCoeff A X) k z
    (T ^ (δ / 2)) (T ^ δ) (1 / 2) displacement
    (sharpMollifiedTailSupport_pos A X) hHpos hRpos (by norm_num) hz
    hDisplacement (by simpa only [sharpMollifiedTail, hza] using hLarge)
    hFactor hExterior
  refine ⟨ρ.im + y, ?_, ?_⟩
  · have hSub : ρ.im + y - ρ.im = y := by ring
    rw [hSub]
    exact hy
  · have hPoint : z + (y : ℂ) * I =
        (σ : ℂ) + I * ((ρ.im + y : ℝ) : ℂ) := by
      dsimp [z]
      rw [ofReal_add]
      ring
    rw [← hPoint]
    norm_num at hyLarge
    simpa only [sharpMollifiedTail] using hyLarge

/-- For every mollifier length at most `T`, the actual sharp-tail coefficient
mass is bounded by `T⁶`. -/
theorem sharpMollifiedTail_mass_le_pow_six (T : ℝ) (X : ℕ) (hT : 8 ≤ T)
    (hXT : (X : ℝ) ≤ T) :
    finiteDirichletMass
        (sharpMollifiedTailSupport ⌊sharpZetaCutoff T⌋₊ X)
        (sharpMollifiedCoeff ⌊sharpZetaCutoff T⌋₊ X) ≤ T ^ (6 : ℝ) := by
  have hTthreequarters : 3 / 4 ≤ T := by linarith
  have hTnonneg : 0 ≤ T := by linarith
  have hCut := sharpZetaCutoff_le_six_mul hTthreequarters
  have hFloor : (⌊sharpZetaCutoff T⌋₊ : ℝ) ≤ sharpZetaCutoff T :=
    Nat.floor_le (by
      have hTpos : 0 < T := by linarith
      exact (four_mul_lt_sharpZetaCutoff T).le.trans'
        (mul_nonneg (by norm_num) hTpos.le))
  have hAX : ((⌊sharpZetaCutoff T⌋₊ * X : ℕ) : ℝ) ≤ 6 * T ^ 2 := by
    push_cast
    calc
      (⌊sharpZetaCutoff T⌋₊ : ℝ) * (X : ℝ) ≤ sharpZetaCutoff T * T :=
        mul_le_mul hFloor hXT (Nat.cast_nonneg X)
          (by linarith [four_mul_lt_sharpZetaCutoff T])
      _ ≤ (6 * T) * T := mul_le_mul_of_nonneg_right hCut hTnonneg
      _ = 6 * T ^ 2 := by ring
  calc
    finiteDirichletMass
          (sharpMollifiedTailSupport ⌊sharpZetaCutoff T⌋₊ X)
          (sharpMollifiedCoeff ⌊sharpZetaCutoff T⌋₊ X)
        ≤ ((⌊sharpZetaCutoff T⌋₊ * X : ℕ) : ℝ) ^ 2 :=
      by simpa only [Nat.cast_mul] using
        sharpMollifiedTail_mass_le_sq ⌊sharpZetaCutoff T⌋₊ X
    _ ≤ (6 * T ^ 2) ^ 2 := by
      nlinarith [sq_nonneg (6 * T ^ 2 - ((⌊sharpZetaCutoff T⌋₊ * X : ℕ) : ℝ))]
    _ ≤ T ^ 6 := by nlinarith [show (8 : ℝ) ^ 2 ≤ T ^ 2 by nlinarith]
    _ = T ^ (6 : ℝ) := by norm_num

/-- Exact-beta removal with the mass estimate discharged. The only numerical
input is the explicit sharp-truncation error being at most one half. -/
theorem sharpMollifiedTail_beta_removal_of_error :
    ∀ δ : ℝ, 0 < δ → ∃ T₀ : ℝ, 8 ≤ T₀ ∧
      ∀ (σ T : ℝ) (ρ : ℂ) (X : ℕ),
        1 / 2 ≤ σ → σ ≤ 1 → T₀ ≤ T →
        ρ ∈ zerosInRect σ 1 T (2 * T) →
        1 ≤ X → X ≤ ⌊sharpZetaCutoff T⌋₊ → (X : ℝ) ≤ T →
        149 * sharpZetaCutoff T ^ (-ρ.re) *
            (∑ n ∈ Icc 1 X, (n : ℝ) ^ (-ρ.re)) ≤ 1 / 2 →
        ∃ t : ℝ, |t - ρ.im| ≤ T ^ δ ∧
          3 / 8 ≤ ‖sharpMollifiedTail ⌊sharpZetaCutoff T⌋₊ X
            ((σ : ℂ) + I * (t : ℂ))‖ := by
  intro δ hδ
  obtain ⟨T₀, hT₀, hShift⟩ := sharpMollifiedTail_beta_removal δ hδ 6 (by norm_num)
  refine ⟨T₀, hT₀, ?_⟩
  intro σ T ρ X hσLower hσUpper hT hρmem hX hXA hXT hError
  have hLarge : 1 / 2 ≤
      ‖sharpMollifiedTail ⌊sharpZetaCutoff T⌋₊ X ρ‖ := by
    have hWitness := norm_sharpMollifiedTail_finiteSeries_ge X
      (by linarith) hρmem (by linarith) hX hXA
    linarith
  exact hShift σ T ρ ⌊sharpZetaCutoff T⌋₊ X hσLower hσUpper hT hρmem rfl
    (sharpMollifiedTail_mass_le_pow_six T X (hT₀.trans hT) hXT) hLarge

/-- Cauchy--Schwarz bounds a partial `β`-harmonic sum by the square root of
the ordinary harmonic sum, uniformly for `β ≥ 1/2`. -/
theorem sum_rpow_neg_le_sqrt_mul_sqrt_harmonic (X : ℕ) (β : ℝ)
    (hβ : 1 / 2 ≤ β) :
    (∑ n ∈ Icc 1 X, (n : ℝ) ^ (-β)) ≤
      Real.sqrt X * Real.sqrt (harmonic X : ℝ) := by
  let S := Finset.Icc 1 X
  have hCS := Real.sum_mul_le_sqrt_mul_sqrt S
    (fun _n : ℕ => (1 : ℝ)) (fun n : ℕ => (n : ℝ) ^ (-β))
  have hCard : (S.card : ℝ) = X := by
    dsimp [S]
    simp
  have hSq : (∑ n ∈ S, ((n : ℝ) ^ (-β)) ^ 2) ≤ (harmonic X : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    dsimp [S]
    apply Finset.sum_le_sum
    intro n hn
    have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    calc
      ((n : ℝ) ^ (-β)) ^ 2 = (n : ℝ) ^ (-2 * β) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        ring_nf
      _ ≤ (n : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hnOne (by linarith)
      _ = ((n : ℝ) : ℝ)⁻¹ := Real.rpow_neg_one _
  have hSqrt := Real.sqrt_le_sqrt hSq
  calc
    (∑ n ∈ Icc 1 X, (n : ℝ) ^ (-β)) =
        ∑ n ∈ S, (1 : ℝ) * (n : ℝ) ^ (-β) := by simp [S]
    _ ≤ Real.sqrt (∑ _n ∈ S, (1 : ℝ) ^ 2) *
          Real.sqrt (∑ n ∈ S, ((n : ℝ) ^ (-β)) ^ 2) := hCS
    _ = Real.sqrt X * Real.sqrt (∑ n ∈ S, ((n : ℝ) ^ (-β)) ^ 2) := by
      rw [show (∑ _n ∈ S, (1 : ℝ) ^ 2) = X by simpa using hCard]
    _ ≤ Real.sqrt X * Real.sqrt (harmonic X : ℝ) :=
      mul_le_mul_of_nonneg_left hSqrt (Real.sqrt_nonneg _)

/-- Uniform elementary majorant for the sharp-truncation error after
Cauchy--Schwarz on the mollifier. -/
theorem sharpMollified_error_le_majorant {σ T : ℝ} {ρ : ℂ} (X : ℕ)
    (hσ : 1 / 2 ≤ σ) (hT : 1 ≤ T) (hX : 1 ≤ X)
    (hρmem : ρ ∈ zerosInRect σ 1 T (2 * T)) (hXT : (X : ℝ) ≤ T) :
    149 * sharpZetaCutoff T ^ (-ρ.re) *
        (∑ n ∈ Icc 1 X, (n : ℝ) ^ (-ρ.re)) ≤
      149 * (4 * T) ^ (-σ) * Real.sqrt T * (1 + Real.log T) := by
  have hTpos : 0 < T := by linarith
  have hRect := hρmem
  rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff,
    mem_ZeroRectangle] at hRect
  have hβ : σ ≤ ρ.re := hRect.1.1
  have hCutOne : 1 ≤ sharpZetaCutoff T := by
    linarith [four_mul_lt_sharpZetaCutoff T]
  have hCutPower : sharpZetaCutoff T ^ (-ρ.re) ≤ (4 * T) ^ (-σ) := by
    calc
      sharpZetaCutoff T ^ (-ρ.re) ≤ sharpZetaCutoff T ^ (-σ) :=
        Real.rpow_le_rpow_of_exponent_le hCutOne (by linarith)
      _ ≤ (4 * T) ^ (-σ) :=
        Real.rpow_le_rpow_of_nonpos (by positivity)
          (four_mul_lt_sharpZetaCutoff T).le (by linarith)
  have hSum := sum_rpow_neg_le_sqrt_mul_sqrt_harmonic X ρ.re
    (hσ.trans hβ)
  have hSqrtX : Real.sqrt X ≤ Real.sqrt T := Real.sqrt_le_sqrt hXT
  have hHarmonic : ((harmonic X : ℚ) : ℝ) ≤ 1 + Real.log T := by
    calc
      ((harmonic X : ℚ) : ℝ) ≤ 1 + Real.log X := harmonic_le_one_add_log X
      _ ≤ 1 + Real.log T := by
        simpa only [add_comm] using add_le_add_left
          (Real.log_le_log
            (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hX)) hXT) 1
  have hLogNonneg : 0 ≤ Real.log T := Real.log_nonneg hT
  have hSqrtH : Real.sqrt (harmonic X : ℝ) ≤ 1 + Real.log T := by
    have hsqrtMono := Real.sqrt_le_sqrt hHarmonic
    have hSelf : Real.sqrt (1 + Real.log T) ≤ 1 + Real.log T := by
      have hOne : 1 ≤ 1 + Real.log T := by linarith
      have hSq := Real.sq_sqrt (by linarith : 0 ≤ 1 + Real.log T)
      nlinarith [Real.sqrt_nonneg (1 + Real.log T)]
    exact hsqrtMono.trans hSelf
  have hSumBound :
      (∑ n ∈ Icc 1 X, (n : ℝ) ^ (-ρ.re)) ≤
        Real.sqrt T * (1 + Real.log T) := by
    exact hSum.trans <| mul_le_mul hSqrtX hSqrtH
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hRightNonneg : 0 ≤ (4 * T) ^ (-σ) := Real.rpow_nonneg (by positivity) _
  calc
    149 * sharpZetaCutoff T ^ (-ρ.re) *
          (∑ n ∈ Icc 1 X, (n : ℝ) ^ (-ρ.re))
        ≤ 149 * (4 * T) ^ (-σ) *
          (∑ n ∈ Icc 1 X, (n : ℝ) ^ (-ρ.re)) := by
      gcongr
    _ ≤ 149 * (4 * T) ^ (-σ) *
          (Real.sqrt T * (1 + Real.log T)) := by
      exact mul_le_mul_of_nonneg_left hSumBound (mul_nonneg (by norm_num) hRightNonneg)
    _ = 149 * (4 * T) ^ (-σ) * Real.sqrt T * (1 + Real.log T) := by ring

theorem tendsto_sharpMollified_error_majorant (σ : ℝ) (hσ : 1 / 2 < σ) :
    Tendsto
      (fun T : ℝ => 149 * (4 * T) ^ (-σ) * Real.sqrt T * (1 + Real.log T))
      atTop (𝓝 0) := by
  let d := σ - 1 / 2
  have hd : 0 < d := by dsimp [d]; linarith
  have hPow : Tendsto (fun T : ℝ => T ^ (-d)) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop hd
  have hLog : Tendsto (fun T : ℝ => Real.log T * T ^ (-d)) atTop (𝓝 0) :=
    by
      have hDiv := (isLittleO_log_rpow_atTop hd).tendsto_div_nhds_zero
      apply hDiv.congr'
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
      rw [Real.rpow_neg hT.le, div_eq_mul_inv]
  have hCore : Tendsto
      (fun T : ℝ => T ^ (-d) * (1 + Real.log T)) atTop (𝓝 0) := by
    have hAdd := hPow.add hLog
    convert hAdd using 1
    · funext T
      ring
    · norm_num
  have hScaled : Tendsto
      (fun T : ℝ => (149 * (4 : ℝ) ^ (-σ)) *
        (T ^ (-d) * (1 + Real.log T))) atTop (𝓝 0) := by
    simpa using hCore.const_mul (149 * (4 : ℝ) ^ (-σ))
  apply Tendsto.congr' _ hScaled
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hT.le,
    Real.sqrt_eq_rpow]
  have hPowCombine : T ^ (-σ) * T ^ (1 / 2 : ℝ) = T ^ (-d) := by
    rw [← Real.rpow_add hT]
    congr 1
    dsimp [d]
    ring
  rw [← hPowCombine]
  ring

theorem eventually_sharpMollified_error_majorant_le_half
    (σ : ℝ) (hσ : 1 / 2 < σ) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      149 * (4 * T) ^ (-σ) * Real.sqrt T * (1 + Real.log T) ≤ 1 / 2 := by
  have hEventually : ∀ᶠ T : ℝ in atTop,
      149 * (4 * T) ^ (-σ) * Real.sqrt T * (1 + Real.log T) < 1 / 2 :=
    (tendsto_order.1 (tendsto_sharpMollified_error_majorant σ hσ)).2
      (1 / 2) (by norm_num)
  rw [eventually_atTop] at hEventually
  obtain ⟨T₀, hT₀⟩ := hEventually
  exact ⟨T₀, fun T hT => (hT₀ T hT).le⟩

/-- Unconditional exact-beta removal for every admissible mollifier length.
The cutoff error, coefficient mass, and rational-localizer decay are all
discharged by preceding theorems. -/
theorem sharpMollifiedTail_beta_removal_native :
    ∀ (σ δ : ℝ), 1 / 2 < σ → σ ≤ 1 → 0 < δ →
      ∃ T₀ : ℝ, 8 ≤ T₀ ∧
        ∀ (T : ℝ) (ρ : ℂ) (X : ℕ), T₀ ≤ T →
          ρ ∈ zerosInRect σ 1 T (2 * T) →
          1 ≤ X → X ≤ ⌊sharpZetaCutoff T⌋₊ → (X : ℝ) ≤ T →
          ∃ t : ℝ, |t - ρ.im| ≤ T ^ δ ∧
            3 / 8 ≤ ‖sharpMollifiedTail ⌊sharpZetaCutoff T⌋₊ X
              ((σ : ℂ) + I * (t : ℂ))‖ := by
  intro σ δ hσ hσUpper hδ
  obtain ⟨Tshift, hTshift, hShift⟩ :=
    sharpMollifiedTail_beta_removal_of_error δ hδ
  obtain ⟨Terror, hError⟩ :=
    eventually_sharpMollified_error_majorant_le_half σ hσ
  let T₀ := max Tshift Terror
  refine ⟨T₀, hTshift.trans (le_max_left _ _), ?_⟩
  intro T ρ X hT hρmem hX hXA hXT
  have hTshift' : Tshift ≤ T := (le_max_left _ _).trans hT
  have hTerror' : Terror ≤ T := (le_max_right _ _).trans hT
  have hMajorant := sharpMollified_error_le_majorant X hσ.le
    (by linarith [hTshift.trans hTshift']) hX hρmem hXT
  have hExplicitError :
      149 * sharpZetaCutoff T ^ (-ρ.re) *
          (∑ n ∈ Icc 1 X, (n : ℝ) ^ (-ρ.re)) ≤ 1 / 2 :=
    hMajorant.trans (hError T hTerror')
  exact hShift σ T ρ X hσ.le hσUpper hTshift' hρmem hX hXA hXT hExplicitError

/-- Fixed-line coefficients of the sharp mollified tail. -/
noncomputable def sharpMollifiedLineCoeff
    (A X : ℕ) (σ : ℝ) (n : ℕ) : ℂ :=
  sharpMollifiedCoeff A X n * (n : ℂ) ^ (-(σ : ℂ))

theorem sharpMollifiedLineCoeff_term (A X n : ℕ) (σ t : ℝ) (hn : 0 < n) :
    sharpMollifiedLineCoeff A X σ n * (n : ℂ) ^ (-(t : ℂ) * I) =
      sharpMollifiedCoeff A X n *
        (n : ℂ) ^ (-((σ : ℂ) + I * (t : ℂ))) := by
  rw [sharpMollifiedLineCoeff, mul_assoc,
    ← Complex.cpow_add _ _ (by exact_mod_cast hn.ne')]
  congr 2
  ring

theorem sharpMollifiedTail_eq_wideDirichletPoly
    (A X : ℕ) (σ t : ℝ) :
    sharpMollifiedTail A X ((σ : ℂ) + I * (t : ℂ)) =
      wideDirichletPoly X (Nat.clog 2 A) (sharpMollifiedLineCoeff A X σ) t := by
  have hCover : A ≤ 2 ^ Nat.clog 2 A :=
    (Nat.clog_le_iff_le_pow Nat.one_lt_two).mp le_rfl
  have hSubset : Finset.Ioc X (A * X) ⊆
      Finset.Ioc X (2 ^ Nat.clog 2 A * X) := by
    intro n hn
    rw [Finset.mem_Ioc] at hn ⊢
    exact ⟨hn.1, hn.2.trans (Nat.mul_le_mul_right X hCover)⟩
  rw [sharpMollifiedTail_apply, wideDirichletPoly]
  have hExtend :
      (∑ n ∈ Finset.Ioc X (A * X),
          sharpMollifiedLineCoeff A X σ n * (n : ℂ) ^ (-(t : ℂ) * I)) =
        ∑ n ∈ Finset.Ioc X (2 ^ Nat.clog 2 A * X),
          sharpMollifiedLineCoeff A X σ n * (n : ℂ) ^ (-(t : ℂ) * I) := by
    apply Finset.sum_subset hSubset
    intro n hnBig hnSmall
    have hnAX : A * X < n := by
      rw [Finset.mem_Ioc] at hnBig
      by_contra h
      exact hnSmall (Finset.mem_Ioc.mpr ⟨hnBig.1, Nat.le_of_not_gt h⟩)
    rw [sharpMollifiedLineCoeff,
      sharpMollifiedCoeff_eq_zero_of_mul_lt A X n hnAX]
    simp
  rw [← hExtend]
  apply Finset.sum_congr rfl
  intro n hn
  exact (sharpMollifiedLineCoeff_term A X n σ t
    (lt_of_le_of_lt (Nat.zero_le X) (Finset.mem_Ioc.mp hn).1)).symm

/-- One dyadic block of the fixed-line sharp tail carries at least its average
share. The block count is the genuine ceiling base-two logarithm of `A`. -/
theorem exists_sharpMollified_large_dyadic_block
    (A X : ℕ) (σ t V : ℝ) (hA : 1 < A)
    (hLarge : V ≤ ‖sharpMollifiedTail A X ((σ : ℂ) + I * (t : ℂ))‖) :
    ∃ r ∈ Finset.range (Nat.clog 2 A),
      V / Nat.clog 2 A ≤
        ‖dirichletPoly (2 ^ r * X) (sharpMollifiedLineCoeff A X σ) t‖ := by
  have hk : 0 < Nat.clog 2 A := Nat.clog_pos Nat.one_lt_two hA
  apply exists_large_dyadic_block X (Nat.clog 2 A)
    (sharpMollifiedLineCoeff A X σ) t V hk
  rw [← sharpMollifiedTail_eq_wideDirichletPoly A X σ t]
  exact hLarge

/-- Simultaneous selection of one beta-shifted dyadic witness, preserving the
full multiplicity weight up to the explicit scale and local-bin factors. -/
theorem finite_shifted_dyadic_witness_extraction {α : Type*} [DecidableEq α]
    (S : Finset α) (weight : α → ℕ) (ordinate : α → ℝ)
    (k L : ℕ) (H : ℝ) (large : ℕ → ℝ → Prop) (inInterval : ℝ → Prop)
    (hS : S.Nonempty)
    (hEach : ∀ x ∈ S, ∃ t : ℝ, |ordinate x - t| ≤ H ∧
      inInterval t ∧ ∃ r ∈ Finset.range k, large r t)
    (hLocal : ∀ z : ℤ,
      ∑ x ∈ S.filter
        (fun y => (z : ℝ) ≤ ordinate y ∧ ordinate y < (z : ℝ) + 1),
        weight x ≤ L) :
    ∃ r ∈ Finset.range k, ∃ W : Finset ℝ,
      IsSeparated 1 W ∧
      (∀ t ∈ W, large r t) ∧
      (∀ t ∈ W, inInterval t) ∧
      ∑ x ∈ S, weight x ≤
        2 * k * ((2 * ⌈H⌉₊ + 1) * L) * W.card := by
  classical
  let shift (x : α) : ℝ :=
    if hx : x ∈ S then Classical.choose (hEach x hx) else ordinate x
  have hShiftSpec : ∀ x ∈ S,
      |ordinate x - shift x| ≤ H ∧ inInterval (shift x) ∧
        ∃ r ∈ Finset.range k, large r (shift x) := by
    intro x hx
    dsimp [shift]
    rw [dif_pos hx]
    exact Classical.choose_spec (hEach x hx)
  let scale (x : α) : ℕ :=
    if hx : x ∈ S then Classical.choose (hShiftSpec x hx).2.2 else 0
  have hScaleSpec : ∀ x ∈ S,
      scale x ∈ Finset.range k ∧ large (scale x) (shift x) := by
    intro x hx
    dsimp [scale]
    rw [dif_pos hx]
    exact Classical.choose_spec (hShiftSpec x hx).2.2
  have hFiberLocal : ∀ r ∈ Finset.range k, ∀ z : ℤ,
      ∑ t ∈ ((S.filter (fun x => scale x = r)).image shift).filter
          (fun u => (z : ℝ) ≤ u ∧ u < (z : ℝ) + 1),
        ∑ x ∈ (S.filter (fun y => scale y = r)).filter
          (fun y => shift y = t), weight x ≤ (2 * ⌈H⌉₊ + 1) * L := by
    intro r hr z
    apply shifted_bin_weight_le_of_unit_bin_weight
      (S.filter (fun x => scale x = r)) weight ordinate shift H L
    · intro x hx
      exact (hShiftSpec x (Finset.mem_filter.mp hx).1).1
    · intro q
      apply le_trans (Finset.sum_le_sum_of_subset ?_) (hLocal q)
      intro x hx
      rw [Finset.mem_filter] at hx ⊢
      exact ⟨(Finset.mem_filter.mp hx.1).1, hx.2⟩
  obtain ⟨r, hr, W, hSep, hLarge, hInterval, hWeight⟩ :=
    finite_weighted_extract_separated S (Finset.range k) weight scale
      (fun _r x => shift x) large inInterval ((2 * ⌈H⌉₊ + 1) * L)
      hS (fun x hx => (hScaleSpec x hx).1) hFiberLocal
      (fun r hr x hx hxr => by simpa [hxr] using (hScaleSpec x hx).2)
      (fun r hr x hx hxr => by simpa using (hShiftSpec x hx).2.1)
  refine ⟨r, hr, W, hSep, hLarge, hInterval, ?_⟩
  simpa using hWeight

/-- Natural-number cap for the Jensen unit-bin multiplicity estimate. -/
noncomputable def classicalLocalMultiplicityCap (T : ℝ) : ℕ :=
  ⌈Real.log ((100 * T ^ (3 : ℝ)) / (0.6 : ℝ)) /
      Real.log ((7 / 4 : ℝ) / (8 / 5 : ℝ))⌉₊

theorem zeroUnitBin_multiplicity_le_cap (σ T : ℝ) (z : ℤ)
    (hσ : 1 / 2 ≤ σ) (hT : 8 ≤ T) :
    ∑ ρ ∈ zeroUnitBin σ T z, analyticVanishingOrder riemannZeta ρ ≤
      classicalLocalMultiplicityCap T := by
  have hJensen := zeroUnitBin_multiplicity_le_jensen σ T z hσ hT
  have hCeil :
      Real.log ((100 * T ^ (3 : ℝ)) / (0.6 : ℝ)) /
          Real.log ((7 / 4 : ℝ) / (8 / 5 : ℝ)) ≤
        (classicalLocalMultiplicityCap T : ℝ) := by
    exact Nat.le_ceil _
  exact_mod_cast hJensen.trans hCeil

/-- From every zero in a positive dyadic slab, select one common fixed-line
dyadic polynomial and a separated ordinate set while retaining the complete
analytic multiplicity weight. -/
theorem extract_sharpMollified_dyadic_witness_native :
    ∀ (σ δ : ℝ), 1 / 2 < σ → σ ≤ 1 → 0 < δ →
      ∃ T₀ : ℝ, 8 ≤ T₀ ∧
        ∀ (T : ℝ) (X : ℕ), T₀ ≤ T →
          1 ≤ X → X ≤ ⌊sharpZetaCutoff T⌋₊ → (X : ℝ) ≤ T →
          (zerosInRect σ 1 T (2 * T)).Nonempty →
          ∃ r ∈ Finset.range (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊),
            ∃ W : Finset ℝ,
              IsSeparated 1 W ∧
              (∀ t ∈ W,
                (3 / 8) / Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ ≤
                  ‖dirichletPoly (2 ^ r * X)
                    (sharpMollifiedLineCoeff ⌊sharpZetaCutoff T⌋₊ X σ) t‖) ∧
              (∀ t ∈ W, T - T ^ δ ≤ t ∧ t ≤ 2 * T + T ^ δ) ∧
              zeroCountRect σ 1 T (2 * T) ≤
                2 * Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ *
                  ((2 * ⌈T ^ δ⌉₊ + 1) * classicalLocalMultiplicityCap T) * W.card := by
  intro σ δ hσ hσUpper hδ
  obtain ⟨T₀, hT₀, hBeta⟩ :=
    sharpMollifiedTail_beta_removal_native σ δ hσ hσUpper hδ
  refine ⟨T₀, hT₀, ?_⟩
  intro T X hT hX hXA hXT hZeros
  let A := ⌊sharpZetaCutoff T⌋₊
  let k := Nat.clog 2 A
  let S := zerosInRect σ 1 T (2 * T)
  have hA : 1 < A := by
    have hCutNonneg : 0 ≤ sharpZetaCutoff T := by
      have hTpos : 0 < T := by linarith [hT₀.trans hT]
      exact (four_mul_lt_sharpZetaCutoff T).le.trans'
        (mul_nonneg (by norm_num) hTpos.le)
    have hTwo : (2 : ℝ) ≤ sharpZetaCutoff T := by
      linarith [four_mul_lt_sharpZetaCutoff T, hT₀.trans hT]
    have hTwoNat : 2 ≤ A := (Nat.le_floor_iff hCutNonneg).mpr hTwo
    omega
  have hEach : ∀ ρ ∈ S, ∃ t : ℝ, |ρ.im - t| ≤ T ^ δ ∧
      (T - T ^ δ ≤ t ∧ t ≤ 2 * T + T ^ δ) ∧
      ∃ r ∈ Finset.range k,
        (3 / 8) / k ≤
          ‖dirichletPoly (2 ^ r * X) (sharpMollifiedLineCoeff A X σ) t‖ := by
    intro ρ hρ
    obtain ⟨t, htShift, htLarge⟩ := hBeta T ρ X hT hρ hX hXA hXT
    have hRect := hρ
    dsimp [S] at hRect
    rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff,
      mem_ZeroRectangle] at hRect
    have htInterval : T - T ^ δ ≤ t ∧ t ≤ 2 * T + T ^ δ := by
      rw [abs_le] at htShift
      constructor <;> linarith [hRect.1.2.1, hRect.1.2.2]
    obtain ⟨r, hr, hrLarge⟩ := exists_sharpMollified_large_dyadic_block
      A X σ t (3 / 8) hA htLarge
    exact ⟨t, by simpa [abs_sub_comm] using (show |t - ρ.im| ≤ T ^ δ from
      (by simpa [abs_sub_comm] using htShift)), htInterval, r, hr, hrLarge⟩
  have hLocal : ∀ z : ℤ,
      ∑ ρ ∈ S.filter
        (fun y => (z : ℝ) ≤ y.im ∧ y.im < (z : ℝ) + 1),
        analyticVanishingOrder riemannZeta ρ ≤ classicalLocalMultiplicityCap T := by
    intro z
    simpa only [S, zeroUnitBin] using
      zeroUnitBin_multiplicity_le_cap σ T z hσ.le (hT₀.trans hT)
  obtain ⟨r, hr, W, hSep, hLarge, hInterval, hWeight⟩ :=
    finite_shifted_dyadic_witness_extraction S
      (analyticVanishingOrder riemannZeta) Complex.im k
      (classicalLocalMultiplicityCap T) (T ^ δ)
      (fun r t => (3 / 8) / k ≤
        ‖dirichletPoly (2 ^ r * X) (sharpMollifiedLineCoeff A X σ) t‖)
      (fun t => T - T ^ δ ≤ t ∧ t ≤ 2 * T + T ^ δ)
      hZeros hEach hLocal
  refine ⟨r, ?_, W, hSep, ?_, hInterval, ?_⟩
  · simpa only [k, A] using hr
  · simpa only [k, A] using hLarge
  · simpa only [zeroCountRect, S, k, A] using hWeight

/-- Coefficients normalized to unit size on one chosen dyadic block. -/
noncomputable def normalizedSharpMollifiedLineCoeff
    (A X N : ℕ) (σ ε C : ℝ) (n : ℕ) : ℂ :=
  sharpMollifiedLineCoeff A X σ n /
    ((C * (2 * N : ℝ) ^ ε * (N : ℝ) ^ (-σ) : ℝ) : ℂ)

theorem norm_normalizedSharpMollifiedLineCoeff_le_one
    (A X N n : ℕ) (σ ε C : ℝ) (hN : 0 < N) (hσ : 0 ≤ σ)
    (hε : 0 ≤ ε) (hC : 0 < C)
    (hCoeff : ∀ m : ℕ, 0 < m →
      ‖sharpMollifiedCoeff A X m‖ ≤ C * (m : ℝ) ^ ε)
    (hn : n ∈ dyadicInterval N) :
    ‖normalizedSharpMollifiedLineCoeff A X N σ ε C n‖ ≤ 1 := by
  have hnData := Finset.mem_Ioc.mp hn
  have hnPos : 0 < n := lt_of_le_of_lt (Nat.zero_le N) hnData.1
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hnUpper : (n : ℝ) ≤ 2 * N := by exact_mod_cast hnData.2
  have hnLower : (N : ℝ) ≤ n := by exact_mod_cast hnData.1.le
  have hPowCoeff : (n : ℝ) ^ ε ≤ (2 * N : ℝ) ^ ε :=
    Real.rpow_le_rpow (by positivity) hnUpper hε
  have hWeight : (n : ℝ) ^ (-σ) ≤ (N : ℝ) ^ (-σ) :=
    Real.rpow_le_rpow_of_nonpos hNreal hnLower (by linarith)
  have hLine : ‖sharpMollifiedLineCoeff A X σ n‖ ≤
      C * (2 * N : ℝ) ^ ε * (N : ℝ) ^ (-σ) := by
    rw [sharpMollifiedLineCoeff, norm_mul,
      Complex.norm_natCast_cpow_of_pos hnPos]
    exact mul_le_mul (hCoeff n hnPos) hWeight
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      (mul_nonneg hC.le (Real.rpow_nonneg (by positivity) _)) |>.trans <| by
        gcongr
  have hScalePos : 0 < C * (2 * N : ℝ) ^ ε * (N : ℝ) ^ (-σ) := by positivity
  rw [normalizedSharpMollifiedLineCoeff, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hScalePos]
  exact (div_le_one hScalePos).mpr hLine

theorem dirichletPoly_normalizedSharpMollifiedLineCoeff
    (A X N : ℕ) (σ ε C t : ℝ) :
    dirichletPoly N (normalizedSharpMollifiedLineCoeff A X N σ ε C) t =
      dirichletPoly N (sharpMollifiedLineCoeff A X σ) t /
        ((C * (2 * N : ℝ) ^ ε * (N : ℝ) ^ (-σ) : ℝ) : ℂ) := by
  unfold dirichletPoly normalizedSharpMollifiedLineCoeff
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n _
  rw [div_mul_eq_mul_div]

/-- The extracted fixed-line detector block satisfies the complete finite
Montgomery--Halász--Huxley estimate after coefficient normalization.  This is
the quantitative bridge from the multiplicity-preserving zero extraction to
the classical large-values theorem; no asymptotic notation occurs here. -/
theorem extracted_sharpMollified_block_card_bound
    (σ δ η C : ℝ)
    (hσ : 1 / 2 < σ) (hσUpper : σ ≤ 1) (hδ : 0 < δ)
    (hη : 0 ≤ η) (hC : 0 < C)
    (hCoeff : ∀ (A X n : ℕ), 0 < n →
      ‖sharpMollifiedCoeff A X n‖ ≤ C * (n : ℝ) ^ η) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧
      ∀ (T : ℝ) (X : ℕ), T₀ ≤ T → T ^ δ ≤ T →
        1 ≤ X → X ≤ ⌊sharpZetaCutoff T⌋₊ → (X : ℝ) ≤ T →
        (zerosInRect σ 1 T (2 * T)).Nonempty →
        ∃ r ∈ Finset.range (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊),
          ∃ W : Finset ℝ,
            let N := 2 ^ r * X
            let D := C * (2 * N : ℝ) ^ η * (N : ℝ) ^ (-σ)
            let V := ((3 / 8) / Nat.clog 2 ⌊sharpZetaCutoff T⌋₊) / D
            IsSeparated 1 W ∧
            InBaseInterval (3 * T) W ∧
            (∀ t ∈ W, V ≤
              ‖dirichletPoly N
                (normalizedSharpMollifiedLineCoeff
                  ⌊sharpZetaCutoff T⌋₊ X N σ η C) t‖) ∧
            zeroCountRect σ 1 T (2 * T) ≤
              2 * Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ *
                ((2 * ⌈T ^ δ⌉₊ + 1) * classicalLocalMultiplicityCap T) * W.card ∧
            ∃ K : ℝ, 0 < K ∧
              (W.card : ℝ) ≤
                K * (1 + (((harmonic N : ℚ) : ℝ))) *
                  ((N : ℝ) ^ 2 / V ^ 2 +
                    (3 * T) * min ((N : ℝ) / V ^ 2)
                      ((N : ℝ) ^ 4 / V ^ 6)) := by
  obtain ⟨T₀, hT₀Eight, hExtract⟩ :=
    extract_sharpMollified_dyadic_witness_native σ δ hσ hσUpper hδ
  refine ⟨T₀, hT₀Eight, ?_⟩
  intro T X hT hShift hX hXA hXT hZeros
  have hTEight : 8 ≤ T := hT₀Eight.trans hT
  obtain ⟨r, hr, W, hSep, hLarge, hInterval, hCount⟩ :=
    hExtract T X hT hX hXA hXT hZeros
  let A := ⌊sharpZetaCutoff T⌋₊
  let N := 2 ^ r * X
  let D : ℝ := C * (2 * N : ℝ) ^ η * (N : ℝ) ^ (-σ)
  let V : ℝ := ((3 / 8) / Nat.clog 2 A) / D
  have hN : 0 < N := mul_pos (pow_pos (by omega) r) hX
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hA : 1 < A := by
    have hCutNonneg : 0 ≤ sharpZetaCutoff T := by
      have hTpos : 0 < T := by linarith
      exact (four_mul_lt_sharpZetaCutoff T).le.trans'
        (mul_nonneg (by norm_num) hTpos.le)
    have hTwo : (2 : ℝ) ≤ sharpZetaCutoff T := by
      linarith [four_mul_lt_sharpZetaCutoff T]
    exact lt_of_lt_of_le (by omega : 1 < 2)
      ((Nat.le_floor_iff hCutNonneg).mpr hTwo)
  have hk : 0 < Nat.clog 2 A := Nat.clog_pos (by omega) hA
  have hkReal : (0 : ℝ) < Nat.clog 2 A := by exact_mod_cast hk
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have hV : 0 < V := by
    dsimp [V]
    positivity
  have hNorm : ∀ n ∈ dyadicInterval N,
      ‖normalizedSharpMollifiedLineCoeff A X N σ η C n‖ ≤ 1 := by
    intro n hn
    exact norm_normalizedSharpMollifiedLineCoeff_le_one A X N n σ η C
      hN (by linarith) hη hC (hCoeff A X) hn
  have hBase : InBaseInterval (3 * T) W := by
    intro t ht
    rw [Set.mem_Icc]
    have htData := hInterval t ht
    constructor <;> linarith
  have hLargeNorm : ∀ t ∈ W, V ≤
      ‖dirichletPoly N
        (normalizedSharpMollifiedLineCoeff A X N σ η C) t‖ := by
    intro t ht
    rw [dirichletPoly_normalizedSharpMollifiedLineCoeff, norm_div,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hD]
    exact div_le_div_of_nonneg_right (by simpa [A, N] using hLarge t ht) hD.le
  obtain ⟨K, hK, hMHH⟩ := classical_large_values_with_harmonic_unrestricted
  have hCard := hMHH N (3 * T) V W
    (normalizedSharpMollifiedLineCoeff A X N σ η C)
    hN (by linarith) hV hNorm hSep hBase hLargeNorm
  refine ⟨r, hr, W, ?_⟩
  dsimp only
  refine ⟨hSep, hBase, ?_, hCount, K, hK, ?_⟩
  · simpa only [A, N, D, V] using hLargeNorm
  · simpa only [N, D, V] using hCard

end RiemannZeta.GuthMaynard

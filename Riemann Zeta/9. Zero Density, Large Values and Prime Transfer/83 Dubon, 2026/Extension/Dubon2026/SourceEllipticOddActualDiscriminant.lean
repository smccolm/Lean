import Dubon2026.SourceEllipticOddCubicRoots
import Dubon2026.SourceEllipticOddGoodAbscissae
import Dubon2026.SourceEllipticOddOrbitInvariance
import Dubon2026.SourceEllipticOddOrbitDistinctness
import Dubon2026.SourceEllipticOddCubicPipeline
import Dubon2026.SourceEllipticOddDiscriminantProduct
import Dubon2026.SourceEllipticOddDoublingPackets
import Dubon2026.SourceEllipticOddSummingFold

/-! Discriminant of the actual odd quotient on a split short model.
All finite norm, translation, root-coordinate, doubling and usable-coordinate
premises are derived from the actual curve and its odd-order point. The
coefficient normalization and descent to general fields, including the
characteristic-two cases, remain separate obligations. This serves odd
quotient ellipticity and products, cyclic-subgroup roots, inertia census,
reverse genus and good reduction for DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2.
Adapted from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2, reusing the pinned native
cubic formulas, proved torsion cardinality and division-polynomial formula. -/
namespace Dubon2026.SourceEllipticVelu.OddDiscriminant
open WeierstrassCurve Polynomial
open Algebra
noncomputable section

theorem odd_quotient_discriminant_of_split_short_model {K : Type*} [Field K] [DecidableEq K] [IsAlgClosed K] (h2K : (2 : K) ≠ 0)
    (V : WeierstrassCurve K) (ha₁ : V.a₁ = 0) (ha₃ : V.a₃ = 0) [V.IsElliptic]
    (e₁ e₂ e₃ : K)
    (hroots : (Cubic.map (RingHom.id K) V.twoTorsionPolynomial).roots = {e₁, e₂, e₃})
    {n : ℕ} (Q : V.toAffine.Point) (hQ : addOrderOf Q = 2 * n + 1) :
    (veluQuotient V (oddOrderSummingSet V Q n)).Δ *
        (∏ P ∈ oddOrderSummingSet V Q n, veluU V P.1 P.2) ^ 4
      = V.Δ ^ (2 * n + 1) := by
  classical
  have hΔlemma : ∀ (W' : WeierstrassCurve K) (r₁ r₂ r₃ : K),
      (Cubic.map (RingHom.id K) W'.twoTorsionPolynomial).roots = {r₁, r₂, r₃} →
      W'.Δ = 16 * ((r₁ - r₂) * (r₁ - r₃) * (r₂ - r₃)) ^ 2 :=
    fun W' _ _ _ h => delta_eq_prod_two_torsion_roots W' h2K h
  have hσ1 : e₁ + e₂ + e₃ = -V.a₂ :=
    (two_torsion_root_symmetric_sums V ha₁ ha₃ h2K hroots).1
  have hσ2 : e₁ * e₂ + e₁ * e₃ + e₂ * e₃ = V.a₄ :=
    (two_torsion_root_symmetric_sums V ha₁ ha₃ h2K hroots).2.1
  have hσ3 : e₁ * e₂ * e₃ = -V.a₆ :=
    (two_torsion_root_symmetric_sums V ha₁ ha₃ h2K hroots).2.2
  have hsumS : ∀ g : K × K → K, ∑ P ∈ oddOrderSummingSet V Q n, g P
      = ∑ k ∈ Finset.Icc 1 n, g ((coordsOrZero (k • Q))) :=
    fun g => sum_oddOrderSummingSet_eq hQ g
  have hprodS : ∀ g : K × K → K, ∏ P ∈ oddOrderSummingSet V Q n, g P
      = ∏ k ∈ Finset.Icc 1 n, g ((coordsOrZero (k • Q))) :=
    fun g => prod_oddOrderSummingSet_eq hQ g
  have hperm : (Finset.Icc 1 n).val.map (fun k => (coordsOrZero ((2 : ℕ) • (k • Q))).1)
      = (Finset.Icc 1 n).val.map (fun k => (coordsOrZero ((k : ℕ) • Q)).1) :=
    multiset_map_double hQ
  have hC1 : ∀ (P : V.toAffine.Point), (∀ j : ℕ, P + j • Q ≠ 0) →
      (∀ j : ℕ, ∀ k, 1 ≤ k → k ≤ n → ((coordsOrZero (P + j • Q))).1 ≠ ((coordsOrZero (k • Q))).1) →
      ∀ m : ℕ, Xv (Finset.Icc 1 n) (fun k => ((coordsOrZero (k • Q))).1)
          (fun k => veluT V ((coordsOrZero (k • Q))).1 ((coordsOrZero (k • Q))).2)
          (fun k => veluU V ((coordsOrZero (k • Q))).1 ((coordsOrZero (k • Q))).2)
          (((coordsOrZero (P + m • Q))).1)
        = Xv (Finset.Icc 1 n) (fun k => ((coordsOrZero (k • Q))).1)
          (fun k => veluT V ((coordsOrZero (k • Q))).1 ((coordsOrZero (k • Q))).2)
          (fun k => veluU V ((coordsOrZero (k • Q))).1 ((coordsOrZero (k • Q))).2)
          (((coordsOrZero P)).1) :=
    fun _ haff hx m => xvSum_orbit_const' hQ haff hx m
  have hpack : ∀ (xq yq d : K), V.toAffine.Equation xq yq → xq ≠ e₁ → xq ≠ e₂ → xq ≠ e₃ →
      d * (4 * xq ^ 3 + V.b₂ * xq ^ 2 + 2 * V.b₄ * xq + V.b₆)
        = xq ^ 4 - V.b₄ * xq ^ 2 - 2 * V.b₆ * xq - V.b₈ →
      (V.toAffine.addX e₁ xq (V.toAffine.slope e₁ xq 0 yq)
          + V.toAffine.addX e₂ xq (V.toAffine.slope e₂ xq 0 yq)
          + V.toAffine.addX e₃ xq (V.toAffine.slope e₃ xq 0 yq) + xq = 4 * d)
      ∧ (V.toAffine.addX e₁ xq (V.toAffine.slope e₁ xq 0 yq)
            * V.toAffine.addX e₂ xq (V.toAffine.slope e₂ xq 0 yq)
          + V.toAffine.addX e₁ xq (V.toAffine.slope e₁ xq 0 yq)
            * V.toAffine.addX e₃ xq (V.toAffine.slope e₃ xq 0 yq)
          + V.toAffine.addX e₂ xq (V.toAffine.slope e₂ xq 0 yq)
            * V.toAffine.addX e₃ xq (V.toAffine.slope e₃ xq 0 yq)
          + xq * (V.toAffine.addX e₁ xq (V.toAffine.slope e₁ xq 0 yq)
            + V.toAffine.addX e₂ xq (V.toAffine.slope e₂ xq 0 yq)
            + V.toAffine.addX e₃ xq (V.toAffine.slope e₃ xq 0 yq))
          = -(V.b₄ + V.b₂ * d))
      ∧ (V.toAffine.addX e₁ xq (V.toAffine.slope e₁ xq 0 yq)
            * V.toAffine.addX e₂ xq (V.toAffine.slope e₂ xq 0 yq)
            * V.toAffine.addX e₃ xq (V.toAffine.slope e₃ xq 0 yq)
          + xq * (V.toAffine.addX e₁ xq (V.toAffine.slope e₁ xq 0 yq)
              * V.toAffine.addX e₂ xq (V.toAffine.slope e₂ xq 0 yq)
            + V.toAffine.addX e₁ xq (V.toAffine.slope e₁ xq 0 yq)
              * V.toAffine.addX e₃ xq (V.toAffine.slope e₃ xq 0 yq)
            + V.toAffine.addX e₂ xq (V.toAffine.slope e₂ xq 0 yq)
              * V.toAffine.addX e₃ xq (V.toAffine.slope e₃ xq 0 yq))
          = 2 * V.b₆ + 2 * V.b₄ * d)
      ∧ (V.toAffine.addX e₁ xq (V.toAffine.slope e₁ xq 0 yq)
            * V.toAffine.addX e₂ xq (V.toAffine.slope e₂ xq 0 yq)
            * V.toAffine.addX e₃ xq (V.toAffine.slope e₃ xq 0 yq) * xq = -(V.b₈ + V.b₆ * d)) :=
    fun _ _ _ hq h1 h2 h3 hd =>
      ⟨pack_esymm1 ha₁ ha₃ hσ1 hσ2 hσ3 hq h1 h2 h3 hd,
       pack_esymm2 ha₁ ha₃ hσ1 hσ2 hσ3 hq h1 h2 h3 hd,
       pack_esymm3 ha₁ ha₃ hσ1 hσ2 hσ3 hq h1 h2 h3 hd,
       pack_esymm4 ha₁ ha₃ hσ1 hσ2 hσ3 hq h1 h2 h3 hd⟩
  have hdbl : ∀ (x y : K), V.toAffine.Equation x y → y ≠ V.toAffine.negY x y →
      V.toAffine.addX x x (V.toAffine.slope x x y y)
          * (4 * x ^ 3 + V.b₂ * x ^ 2 + 2 * V.b₄ * x + V.b₆)
        = x ^ 4 - V.b₄ * x ^ 2 - 2 * V.b₆ * x - V.b₈ :=
    fun _ _ h hy => double_x_mul_psi2Sq V h hy
  have hL : ∀ (f₁ f₂ f₃ xT yT : K), f₁ + f₂ + f₃ = -V.a₂ → f₁ * f₂ + f₁ * f₃ + f₂ * f₃ = V.a₄ →
      f₁ * f₂ * f₃ = -V.a₆ → V.toAffine.Equation xT yT → xT ≠ f₁ →
      V.toAffine.addX f₁ xT (V.toAffine.slope f₁ xT 0 yT) - f₂ = (f₁ - f₂) * (xT - f₃) / (xT - f₁) :=
    fun _ _ _ _ _ h1 h2 h3 hT hne => addX_two_torsion_sub_root ha₁ ha₃ h1 h2 h3 hT hne
  have hC3 : Set.Infinite {x₀ : K | ∃ z : V.toAffine.Point,
      (∀ j : ℕ, 2 • z + j • Q ≠ 0) ∧ ((coordsOrZero z)).1 = x₀} :=
    good_abscissae_infinite h2K hQ
  obtain ⟨hb2, hb4, hb6, hb8⟩ := b_model ha₁ ha₃
  have h4 : (4 : K) ≠ 0 := by
    intro h; apply h2K
    have : (2 : K) ^ 2 = 0 := by linear_combination h
    exact pow_eq_zero_iff two_ne_zero |>.mp this

  set S : Finset ℕ := Finset.Icc 1 n with hS
  obtain ⟨x, hx⟩ : ∃ f : ℕ → K, f = fun k => ((coordsOrZero (k • Q))).1 := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ f : ℕ → K, f = fun k => ((coordsOrZero (k • Q))).2 := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ f : ℕ → K,
    f = fun k => veluT V ((coordsOrZero (k • Q))).1 ((coordsOrZero (k • Q))).2 := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ f : ℕ → K,
    f = fun k => veluU V ((coordsOrZero (k • Q))).1 ((coordsOrZero (k • Q))).2 := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ f : ℕ → K, f = fun k => ((coordsOrZero ((2 : ℕ) • (k • Q)))).1 := ⟨_, rfl⟩
  have hxk : ∀ k, x k = ((coordsOrZero (k • Q))).1 := fun k => by rw [hx]
  have hyk : ∀ k, y k = ((coordsOrZero (k • Q))).2 := fun k => by rw [hy]
  have htk : ∀ k, t k = veluT V (x k) (y k) := fun k => by rw [ht, hx, hy]
  have huk : ∀ k, u k = veluU V (x k) (y k) := fun k => by rw [hu, hx, hy]
  have hdk : ∀ k, d k = ((coordsOrZero ((2 : ℕ) • (k • Q)))).1 := fun k => by rw [hd]
  rw [← hx, ← hd] at hperm
  rw [← hx, ← ht, ← hu] at hC1
  have hcardS : S.card = n := by simp [hS]
  have hSmem : ∀ {k}, k ∈ S → 1 ≤ k ∧ k ≤ n := fun hk => by simpa [hS] using hk
  have hmemS : ∀ {k}, 1 ≤ k → k ≤ n → k ∈ S := fun h1 h2 => by
    rw [hS]; exact Finset.mem_Icc.mpr ⟨h1, h2⟩

  have hk0 : ∀ k ∈ S, k • Q ≠ 0 := fun k hk =>
    kernel_ne_zero hQ (hSmem hk).1 (by have := (hSmem hk).2; omega)
  have h2k0 : ∀ k ∈ S, (2 : ℕ) • (k • Q) ≠ 0 := fun k hk h => by
    have := hSmem hk
    refine kernel_ne_zero hQ (k := 2 * k) (by omega) (by omega) ?_
    rwa [mul_comm, mul_nsmul]
  have hkpt : ∀ k ∈ S, ∃ h : V.toAffine.Nonsingular (x k) (y k),
      k • Q = .some (x k) (y k) h := by
    intro k hk
    rw [hxk, hyk]
    exact affine_decomp (k • Q) (hk0 k hk)
  have hkeq : ∀ k ∈ S, V.toAffine.Equation (x k) (y k) := fun k hk => by
    obtain ⟨h, -⟩ := hkpt k hk
    exact h.1
  have hkny : ∀ k ∈ S, y k ≠ V.toAffine.negY (x k) (y k) := by
    intro k hk hyy
    obtain ⟨h, hke⟩ := hkpt k hk
    apply h2k0 k hk
    rw [two_nsmul, hke]
    exact Affine.Point.add_self_of_Y_eq hyy
  have hdk' : ∀ k ∈ S, d k
      = V.toAffine.addX (x k) (x k) (V.toAffine.slope (x k) (x k) (y k) (y k)) := by
    intro k hk
    obtain ⟨h, hke⟩ := hkpt k hk
    rw [hdk, two_nsmul, hke, Affine.Point.add_self_of_Y_ne (hkny k hk)]
    rfl
  have ht' : ∀ k ∈ S, t k = 6 * x k ^ 2 + 4 * V.a₂ * x k + 2 * V.a₄ := fun k _ => by
    rw [htk, veluT_eq, hb2, hb4]
  have hu' : ∀ k ∈ S, u k
      = 4 * x k ^ 3 + 4 * V.a₂ * x k ^ 2 + 2 * (2 * V.a₄) * x k + 4 * V.a₆ := fun k hk => by
    rw [huk, veluU_eq_Ψ₂Sq_eval V (hkeq k hk), Ψ₂Sq_b_model ha₁ ha₃, fP]
    simp only [eval_add, eval_mul, eval_pow, eval_C, eval_X]

  have hP4 : V.twoTorsionPolynomial.toPoly ≠ 0 :=
    Cubic.ne_zero_of_a_ne_zero (show V.twoTorsionPolynomial.a ≠ 0 from h4)
  have hΨV : V.Ψ₂Sq = C 4 * ((X - C e₁) * (X - C e₂) * (X - C e₃)) := by
    have e := Cubic.eq_prod_three_roots (φ := RingHom.id K) (P := V.twoTorsionPolynomial)
      (show V.twoTorsionPolynomial.a ≠ 0 from h4) hroots
    rw [Cubic.map_toPoly, Polynomial.map_id, ← Ψ₂Sq_eq] at e
    rw [e, show V.twoTorsionPolynomial.a = 4 from rfl, RingHom.id_apply]
    ring
  have heroot : ∀ e ∈ ({e₁, e₂, e₃} : Multiset K), V.toAffine.Equation e 0 := by
    intro e he
    have hmem : e ∈ (Cubic.map (RingHom.id K) V.twoTorsionPolynomial).roots := by
      rw [hroots]; exact he
    rw [Cubic.map_roots, Polynomial.map_id, Polynomial.mem_roots hP4, IsRoot.def, ← Ψ₂Sq_eq,
      hΨV] at hmem
    simp only [eval_mul, eval_C, eval_sub, eval_X] at hmem
    have h' : (e - e₁) * (e - e₂) * (e - e₃) = 0 := (mul_eq_zero.mp hmem).resolve_left h4
    rw [Affine.equation_iff, ha₁, ha₃]
    linear_combination -h' - e ^ 2 * hσ1 + e * hσ2 - hσ3
  have he₁eq : V.toAffine.Equation e₁ 0 := heroot e₁ (by simp)
  have he₂eq : V.toAffine.Equation e₂ 0 := heroot e₂ (by simp)
  have he₃eq : V.toAffine.Equation e₃ 0 := heroot e₃ (by simp)
  have hens : ∀ e, V.toAffine.Equation e 0 → V.toAffine.Nonsingular e 0 := fun e he =>
    (Affine.equation_iff_nonsingular (W := V)).mp he
  have he_ne : ∀ e, V.toAffine.Equation e 0 → ∀ k ∈ S, e ≠ x k := by
    intro e he k hk hex
    have hT : V.toAffine.Nonsingular e 0 := hens e he
    obtain ⟨h, hke⟩ := hkpt k hk
    have hx' : xco (Affine.Point.some e 0 hT) = xco (k • Q) := by rw [hke]; exact hex
    have hT2 : (Affine.Point.some e 0 hT : V.toAffine.Point) + Affine.Point.some e 0 hT = 0 :=
      Affine.Point.add_self_of_Y_eq (by simp [Affine.negY, toAffine, ha₁, ha₃])
    rcases eq_or_eq_neg_of_xco_eq (Affine.Point.some_ne_zero hT) (hk0 k hk) hx' with ek | ek
    · apply h2k0 k hk
      rw [two_nsmul, ← ek, hT2]
    · apply h2k0 k hk
      rw [two_nsmul, show k • Q = -(Affine.Point.some e 0 hT) by rw [ek, neg_neg], ← neg_add,
        hT2, neg_zero]

  have hMP : MM S x t u V.a₂ V.a₄ V.a₆ = PP S x t u := by
    refine MM_eq_PP_of_infinite S x t u V.a₂ V.a₄ V.a₆ (hC3.mono ?_)
    rintro x₀ ⟨z, hz, rfl⟩
    simp only [Set.mem_setOf_eq]
    have hz0 : z ≠ 0 := fun h => hz 0 (by rw [h, nsmul_zero, zero_nsmul, add_zero])
    obtain ⟨h₀, hzeq⟩ := affine_decomp z hz0
    set x₀ := ((coordsOrZero z)).1 with hx₀
    set y₀ := ((coordsOrZero z)).2 with hy₀
    have hxne : ∀ j : ℕ, ∀ k ∈ S, ((coordsOrZero (z + j • Q))).1 ≠ x k := by
      intro j k hk
      rw [hxk]
      exact good_xco_ne_kernel hQ hz j k (hSmem hk).1 (by have := (hSmem hk).2; omega)
    have hx0ne : ∀ k ∈ S, x₀ ≠ x k := by
      intro k hk
      have := hxne 0 k hk
      rwa [zero_nsmul, add_zero] at this
    set τp : ℕ → K := fun k => ((coordsOrZero (z + k • Q))).1 with hτp
    set τm : ℕ → K := fun k => ((coordsOrZero (z + (2 * n + 1 - k) • Q))).1 with hτm
    have hτp' : ∀ k ∈ S, τp k
        = V.toAffine.addX x₀ (x k) (V.toAffine.slope x₀ (x k) y₀ (y k)) := by
      intro k hk
      obtain ⟨h, hke⟩ := hkpt k hk
      simp only [hτp]
      rw [hzeq, hke, Affine.Point.add_of_X_ne (hx0ne k hk)]
      rfl
    have hτm' : ∀ k ∈ S, τm k = V.toAffine.addX x₀ (x k)
        (V.toAffine.slope x₀ (x k) y₀ (V.toAffine.negY (x k) (y k))) := by
      intro k hk
      obtain ⟨h, hke⟩ := hkpt k hk
      simp only [hτm]
      rw [sub_smul_eq_neg_smul hQ (by have := (hSmem hk).2; omega), hzeq, hke,
        Affine.Point.neg_some, Affine.Point.add_of_X_ne (hx0ne k hk)]
      rfl
    have hsum : ∀ k ∈ S, τp k + τm k = 2 * x k + t k / (x₀ - x k) + u k / (x₀ - x k) ^ 2 := by
      intro k hk
      rw [hτp' k hk, hτm' k hk, htk, huk]
      exact chord_sum' V h₀.1 (hkeq k hk) (hx0ne k hk)
    have hprod : ∀ k ∈ S, τp k * τm k
        = ((x₀ * x k - V.a₄) ^ 2 - 4 * V.a₆ * (x₀ + x k + V.a₂)) / (x₀ - x k) ^ 2 := by
      intro k hk
      rw [hτp' k hk, hτm' k hk]
      exact chord_prod V ha₁ ha₃ h₀.1 (hkeq k hk) (hx0ne k hk)

    set c := Xv S x t u x₀ with hc
    have hzj : ∀ j : ℕ, z + j • Q ≠ 0 := good_add_nsmul_ne_zero hz
    have hC1z := hC1 z hzj (fun j k hk1 hkn =>
      good_xco_ne_kernel hQ hz j k hk1 (by omega))
    have hAv : ∀ v, (∀ k ∈ S, v ≠ x k) → Xv S x t u v = c →
        (AP S x t u).eval v = c * (hP S x).eval v ^ 2 := by
      intro v hv hXv
      rw [AP_eval S x t u v hv, hXv, mul_comm]
    have hr0 : (AP S x t u).eval x₀ = c * (hP S x).eval x₀ ^ 2 := hAv x₀ hx0ne rfl
    have hrp : ∀ k ∈ S, (AP S x t u).eval (τp k) = c * (hP S x).eval (τp k) ^ 2 :=
      fun k _ => hAv (τp k) (hxne k) (hC1z k)
    have hrm : ∀ k ∈ S, (AP S x t u).eval (τm k) = c * (hP S x).eval (τm k) ^ 2 :=
      fun k _ => hAv (τm k) (hxne (2 * n + 1 - k)) (hC1z (2 * n + 1 - k))
    obtain ⟨hd0p, hd0m, hinjp, hinjm, hpm⟩ := good_distinct (V := V) hQ hz
    have hnorm := norm_identity' S x t u x₀ c τp τm hd0p hd0m hinjp hinjm hpm hr0 hrp hrm
    exact spec_MM_eq_spec_PP_at S x t u V.a₂ V.a₄ V.a₆ x₀ c τp τm hx0ne hsum hprod hnorm hr0.symm

  obtain ⟨ξ₁, hξ₁⟩ : ∃ f : ℕ → K,
    f = fun k => V.toAffine.addX e₁ (x k) (V.toAffine.slope e₁ (x k) 0 (y k)) := ⟨_, rfl⟩
  obtain ⟨ξ₂, hξ₂⟩ : ∃ f : ℕ → K,
    f = fun k => V.toAffine.addX e₂ (x k) (V.toAffine.slope e₂ (x k) 0 (y k)) := ⟨_, rfl⟩
  obtain ⟨ξ₃, hξ₃⟩ : ∃ f : ℕ → K,
    f = fun k => V.toAffine.addX e₃ (x k) (V.toAffine.slope e₃ (x k) 0 (y k)) := ⟨_, rfl⟩
  have hξ₁k : ∀ k, ξ₁ k = V.toAffine.addX e₁ (x k) (V.toAffine.slope e₁ (x k) 0 (y k)) :=
    fun k => by rw [hξ₁]
  have hξ₂k : ∀ k, ξ₂ k = V.toAffine.addX e₂ (x k) (V.toAffine.slope e₂ (x k) 0 (y k)) :=
    fun k => by rw [hξ₂]
  have hξ₃k : ∀ k, ξ₃ k = V.toAffine.addX e₃ (x k) (V.toAffine.slope e₃ (x k) 0 (y k)) :=
    fun k => by rw [hξ₃]
  have hfac : ∀ e, V.toAffine.Equation e 0 → ∀ k ∈ S,
      C ((e - x k) ^ 2) * X ^ 2 - C ((SqP x t u k).eval e) * X + C ((PqP x V.a₂ V.a₄ V.a₆ k).eval e)
        = C ((e - x k) ^ 2)
          * (X - C (V.toAffine.addX e (x k) (V.toAffine.slope e (x k) 0 (y k)))) ^ 2 := by
    intro e he k hk
    rw [eval_SqP, eval_PqP, htk, huk]
    exact two_torsion_chord_factor ha₁ ha₃ he (hkeq k hk) (he_ne e he k hk)
  have hfac₁ : ∀ k ∈ S, C ((e₁ - x k) ^ 2) * X ^ 2 - C ((SqP x t u k).eval e₁) * X
      + C ((PqP x V.a₂ V.a₄ V.a₆ k).eval e₁) = C ((e₁ - x k) ^ 2) * (X - C (ξ₁ k)) ^ 2 :=
    fun k hk => by rw [hξ₁k]; exact hfac e₁ he₁eq k hk
  have hfac₂ : ∀ k ∈ S, C ((e₂ - x k) ^ 2) * X ^ 2 - C ((SqP x t u k).eval e₂) * X
      + C ((PqP x V.a₂ V.a₄ V.a₆ k).eval e₂) = C ((e₂ - x k) ^ 2) * (X - C (ξ₂ k)) ^ 2 :=
    fun k hk => by rw [hξ₂k]; exact hfac e₂ he₂eq k hk
  have hfac₃ : ∀ k ∈ S, C ((e₃ - x k) ^ 2) * X ^ 2 - C ((SqP x t u k).eval e₃) * X
      + C ((PqP x V.a₂ V.a₄ V.a₆ k).eval e₃) = C ((e₃ - x k) ^ 2) * (X - C (ξ₃ k)) ^ 2 :=
    fun k hk => by rw [hξ₃k]; exact hfac e₃ he₃eq k hk
  have fib₁ := fiber S x t u V.a₂ V.a₄ V.a₆ hMP e₁ ξ₁ (he_ne e₁ he₁eq) hfac₁
  have fib₂ := fiber S x t u V.a₂ V.a₄ V.a₆ hMP e₂ ξ₂ (he_ne e₂ he₂eq) hfac₂
  have hvieta : fP (4 * V.a₂) (2 * V.a₄) (4 * V.a₆) = C 4 * ((X - C e₁) * (X - C e₂) * (X - C e₃)) := by
    rw [← Ψ₂Sq_b_model ha₁ ha₃, hΨV]

  have hpk : ∀ k ∈ S, (X - C (ξ₁ k)) * (X - C (ξ₂ k)) * (X - C (ξ₃ k)) * (X - C (x k))
      = φP (2 * V.a₄) (4 * V.a₆) (4 * V.a₂ * V.a₆ - V.a₄ ^ 2)
        - C (d k) * fP (4 * V.a₂) (2 * V.a₄) (4 * V.a₆) := by
    intro k hk
    have hne : ∀ e, V.toAffine.Equation e 0 → x k ≠ e := fun e he => (he_ne e he k hk).symm
    have hdd : d k * (4 * x k ^ 3 + V.b₂ * x k ^ 2 + 2 * V.b₄ * x k + V.b₆)
        = x k ^ 4 - V.b₄ * x k ^ 2 - 2 * V.b₆ * x k - V.b₈ := by
      rw [hdk' k hk]; exact hdbl (x k) (y k) (hkeq k hk) (hkny k hk)
    obtain ⟨s1, s2, s3, s4⟩ := hpack (x k) (y k) (d k) (hkeq k hk) (hne e₁ he₁eq) (hne e₂ he₂eq)
      (hne e₃ he₃eq) hdd
    rw [hξ₁k, hξ₂k, hξ₃k]
    generalize V.toAffine.addX e₁ (x k) (V.toAffine.slope e₁ (x k) 0 (y k)) = A₁ at s1 s2 s3 s4 ⊢
    generalize V.toAffine.addX e₂ (x k) (V.toAffine.slope e₂ (x k) 0 (y k)) = A₂ at s1 s2 s3 s4 ⊢
    generalize V.toAffine.addX e₃ (x k) (V.toAffine.slope e₃ (x k) 0 (y k)) = A₃ at s1 s2 s3 s4 ⊢
    simp only [hb2, hb4, hb6, hb8] at s2 s3 s4
    have eL : (X - C A₁) * (X - C A₂) * (X - C A₃) * (X - C (x k))
        = X ^ 4 - C (A₁ + A₂ + A₃ + x k) * X ^ 3
          + C (A₁ * A₂ + A₁ * A₃ + A₂ * A₃ + x k * (A₁ + A₂ + A₃)) * X ^ 2
          - C (A₁ * A₂ * A₃ + x k * (A₁ * A₂ + A₁ * A₃ + A₂ * A₃)) * X
          + C (A₁ * A₂ * A₃ * x k) := by
      simp only [map_add, map_mul]
      ring
    rw [eL, s1, s2, s3, s4, φP, fP]
    simp only [map_add, map_mul, map_sub, map_neg, map_pow, map_ofNat]
    ring

  have hcubic := pipeline S x d t u ξ₁ ξ₂ ξ₃ V.a₂ V.a₄ V.a₆ e₁ e₂ e₃ hMP (he_ne e₁ he₁eq)
    (he_ne e₂ he₂eq) (he_ne e₃ he₃eq) hfac₁ hfac₂ hfac₃ hvieta ht' hu' hperm hpk
  have htS : veluTSum V (oddOrderSummingSet V Q n) = ∑ k ∈ S, t k := by
    rw [veluTSum, hsumS]
    exact Finset.sum_congr rfl fun k _ => by rw [htk, hxk, hyk]
  have hwS : veluWSum V (oddOrderSummingSet V Q n) = ∑ k ∈ S, (u k + x k * t k) := by
    rw [veluWSum, hsumS]
    exact Finset.sum_congr rfl fun k _ => by rw [huk, htk, hxk, hyk]; rfl
  have hΨ' : (veluQuotient V (oddOrderSummingSet V Q n)).Ψ₂Sq
      = C 4 * ((X - C (Xv S x t u e₁)) * (X - C (Xv S x t u e₂)) * (X - C (Xv S x t u e₃))) := by
    rw [Ψ₂Sq, veluQuotient_b₂, veluQuotient_b₄, veluQuotient_b₆, htS, hwS, hb2, hb4, hb6]
    exact hcubic.symm
  have hroots' : (Cubic.map (RingHom.id K)
      (veluQuotient V (oddOrderSummingSet V Q n)).twoTorsionPolynomial).roots
        = {Xv S x t u e₁, Xv S x t u e₂, Xv S x t u e₃} := by
    rw [Cubic.map_roots, Polynomial.map_id, ← Ψ₂Sq_eq, hΨ', roots_cubic _ _ _ h4]
  have hΔ' := hΔlemma _ _ _ _ hroots'
  have hΔ := hΔlemma _ _ _ _ hroots

  have hA : ∀ e, V.toAffine.Equation e 0 →
      (AP S x t u).eval e = (hP S x).eval e ^ 2 * Xv S x t u e :=
    fun e he => AP_eval S x t u e (he_ne e he)
  have hFev : ∀ (e e' X₀ : K) (ξ : ℕ → K),
      AP S x t u - C X₀ * hP S x ^ 2 = (X - C e) * (∏ q ∈ S, (X - C (ξ q))) ^ 2 →
      (AP S x t u).eval e' - X₀ * (hP S x).eval e' ^ 2 = (e' - e) * (∏ q ∈ S, (e' - ξ q)) ^ 2 := by
    intro e e' X₀ ξ hF
    have := congrArg (Polynomial.eval e') hF
    simpa only [eval_sub, eval_mul, eval_C, eval_pow, eval_X, eval_prod] using this
  have hL' : ∀ (f₁ f₂ f₃ : K), f₁ + f₂ + f₃ = -V.a₂ → f₁ * f₂ + f₁ * f₃ + f₂ * f₃ = V.a₄ →
      f₁ * f₂ * f₃ = -V.a₆ → V.toAffine.Equation f₁ 0 → ∀ k ∈ S,
      (f₂ - V.toAffine.addX f₁ (x k) (V.toAffine.slope f₁ (x k) 0 (y k))) * (x k - f₁)
        = -((f₁ - f₂) * (x k - f₃)) := by
    intro f₁ f₂ f₃ h1 h2 h3 hf₁ k hk
    have hne : x k ≠ f₁ := (he_ne f₁ hf₁ k hk).symm
    have hsub : x k - f₁ ≠ 0 := sub_ne_zero.mpr hne
    have e := hL f₁ f₂ f₃ (x k) (y k) h1 h2 h3 (hkeq k hk) hne
    have e' : (V.toAffine.addX f₁ (x k) (V.toAffine.slope f₁ (x k) 0 (y k)) - f₂) * (x k - f₁)
        = (f₁ - f₂) * (x k - f₃) := by
      rw [e, div_mul_cancel₀ _ hsub]
    linear_combination -e'
  have hL₁₂ := hL' e₁ e₂ e₃ hσ1 hσ2 hσ3 he₁eq
  have hL₁₃ := hL' e₁ e₃ e₂ (by linear_combination hσ1) (by linear_combination hσ2)
    (by linear_combination hσ3) he₁eq
  have hL₂₃ := hL' e₂ e₃ e₁ (by linear_combination hσ1) (by linear_combination hσ2)
    (by linear_combination hσ3) he₂eq
  have hu4 : ∀ k ∈ S, u k = 4 * ((x k - e₁) * (x k - e₂) * (x k - e₃)) := fun k hk => by
    rw [huk, veluU_eq_Ψ₂Sq_eval V (hkeq k hk), hΨV]
    simp only [eval_mul, eval_C, eval_sub, eval_X]
  have key := delta_identity S x t u ξ₁ ξ₂ e₁ e₂ e₃ (Xv S x t u e₁) (Xv S x t u e₂)
    (Xv S x t u e₃) V.Δ (veluQuotient V (oddOrderSummingSet V Q n)).Δ (hA e₂ he₂eq)
    (hA e₃ he₃eq) (hFev e₁ e₂ _ ξ₁ fib₁) (hFev e₁ e₃ _ ξ₁ fib₁) (hFev e₂ e₃ _ ξ₂ fib₂)
    (fun k hk => by rw [hξ₁k]; exact hL₁₂ k hk) (fun k hk => by rw [hξ₁k]; exact hL₁₃ k hk)
    (fun k hk => by rw [hξ₂k]; exact hL₂₃ k hk)
    (he_ne e₁ he₁eq) (he_ne e₂ he₂eq) (he_ne e₃ he₃eq) hu4 hΔ hΔ'
  have hU : ∏ P ∈ oddOrderSummingSet V Q n, veluU V P.1 P.2 = ∏ k ∈ S, u k := by
    rw [hprodS]
    exact Finset.prod_congr rfl fun k _ => by rw [huk, hxk, hyk]
  rw [hcardS] at key
  rw [hU]
  exact key


end
end Dubon2026.SourceEllipticVelu.OddDiscriminant

import GuthMaynard.MediumTypeIEndpoint

/-!
# Reflected source families at genuine positive ordinates

The negative Poisson half is reflected by the actual isometry v -> 3*T-v.
The retained family stays one-separated with exactly the same cardinality.
Its coefficients are the literal real normalized reflected coefficients.
-/

noncomputable section
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

theorem extract_positive_ordinate_reflected_block
    {M : ℕ} {sigma T D H S : ℝ} (W : Finset ℝ)
    (hM : 1 < M) (hH : 0 ≤ H) (hT : 0 ≤ T)
    (hDH : D + H ≤ T / 2)
    (hSeparated : IsSeparated 1 W)
    (hRange : ∀ t ∈ W, T - D ≤ t ∧ t ≤ 2 * T + D)
    (hEach : ∀ t ∈ W,
      (∃ u ∈ Set.Icc (-H) H,
        S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
          (normalizedTypeIReflectedCoeff sigma M) (-(t + u))‖) ∨
      (∃ u ∈ Set.Icc (-H) H,
        S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
          (normalizedTypeIReflectedCoeff sigma M) (t - u)‖)) :
    ∃ j ∈ Finset.range (Nat.clog 2 M), ∃ U : Finset ℝ,
      IsSeparated 1 U ∧
      (∀ v ∈ U, T / 2 ≤ v ∧ v ≤ 5 * T / 2) ∧
      W.card ≤ 2 * (2 * (2 * ⌈H⌉₊ + 1)) * (Nat.clog 2 M) * U.card ∧
      (∀ v ∈ U, S / Nat.clog 2 M ≤
        ‖dirichletPoly (2 ^ j) (normalizedTypeIReflectedCoeff sigma M) v‖) := by
  classical
  rcases select_common_signed_reflected_family W hEach with
    ⟨Wsign, hWsign, hSignCard, hNegative⟩ |
      ⟨Wsign, hWsign, hSignCard, hPositive⟩
  · have hSepSign : IsSeparated 1 Wsign := by
      intro x hx y hy hxy
      exact hSeparated x (hWsign hx) y (hWsign hy) hxy
    have hRangeSign : ∀ t ∈ Wsign, T - D ≤ t ∧ t ≤ 2 * T + D :=
      fun t ht => hRange t (hWsign ht)
    obtain ⟨j, hj, U, hSepU, _, hURange, hCardU, hLargeU⟩ :=
      extract_common_reflected_mhh_block Wsign hM hH hT hDH
        hSepSign hRangeSign hNegative
    let V := U.image (fun v => 3*T-v)
    have hInjective : Function.Injective (fun v : ℝ => 3*T-v) := by
      intro a b hab
      linarith
    have hCardV : V.card = U.card := Finset.card_image_of_injective _ hInjective
    refine ⟨j, hj, V, ?_, ?_, ?_, ?_⟩
    · intro x hx y hy hxy
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
      have hab : a ≠ b := by intro hab; apply hxy; rw [hab]
      have h := hSepU a ha b hb hab
      have hdiff : 3*T-a-(3*T-b) = -(a-b) := by ring
      rw [Real.dist_eq, hdiff, abs_neg]
      simpa only [Real.dist_eq] using h
    · intro v hv
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv
      rcases hURange a ha with ⟨hl,hu⟩
      constructor <;> linarith
    · calc
        W.card ≤ 2 * Wsign.card := hSignCard
        _ ≤ 2 * ((2 * (2 * ⌈H⌉₊ + 1)) * (Nat.clog 2 M) * U.card) :=
          Nat.mul_le_mul_left 2 hCardU
        _ = _ := by rw [hCardV]; ring
    · intro v hv
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv
      simpa only [norm_phaseShifted_normalized_reflected_eq] using hLargeU a ha
  · have hSepSign : IsSeparated 1 Wsign := by
      intro x hx y hy hxy
      exact hSeparated x (hWsign hx) y (hWsign hy) hxy
    have hRangeSign : ∀ t ∈ Wsign, T - D ≤ t ∧ t ≤ 2 * T + D :=
      fun t ht => hRange t (hWsign ht)
    obtain ⟨j, hj, U, hSepU, _, hURange, hCardU, hLargeU⟩ :=
      extract_common_positive_reflected_mhh_block Wsign hM hH hT hDH
        hSepSign hRangeSign hPositive
    refine ⟨j, hj, U, hSepU, hURange, ?_, hLargeU⟩
    calc
      W.card ≤ 2 * Wsign.card := hSignCard
      _ ≤ 2 * ((2 * (2 * ⌈H⌉₊ + 1)) * (Nat.clog 2 M) * U.card) :=
        Nat.mul_le_mul_left 2 hCardU
      _ = _ := by ring

end TaoTrudgianYang2025

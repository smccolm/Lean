import GafniTao.WooleyLemma63
import GafniTao.WooleyThreeFactorHolder

/-!
# Wooley's initial conditioning argument

This file formalizes Lemma 6.1 of nested efficient congruencing.  The
diagonal and separated residue-pair contributions are kept as literal finite
sums, so that equations (6.6)--(6.9) can be audited against the source.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- The pointwise monomial identity behind the three-factor interpolation
in (6.8). -/
theorem wooley_critical_interpolation_term
    {s : ℕ} (hs : 2 ≤ s) {w u v : ℝ}
    (hw : 0 ≤ w) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    w ^ (((s : ℝ) - 2) / (s : ℝ)) *
        (w * u ^ 2 * v ^ (2 * (s - 1))) ^ (1 / (s : ℝ)) *
          (w * v ^ 2 * u ^ (2 * (s - 1))) ^ (1 / (s : ℝ)) =
      w * (u * u) * (v * v) := by
  have hsReal : (0 : ℝ) < s := by
    exact_mod_cast (by omega : 0 < s)
  have hroot : 0 < 1 / (s : ℝ) := by positivity
  by_cases hw0 : w = 0
  · calc
      w ^ (((s : ℝ) - 2) / (s : ℝ)) *
          (w * u ^ 2 * v ^ (2 * (s - 1))) ^ (1 / (s : ℝ)) *
            (w * v ^ 2 * u ^ (2 * (s - 1))) ^ (1 / (s : ℝ)) = 0 := by
        rw [show w * u ^ 2 * v ^ (2 * (s - 1)) = 0 by simp [hw0],
          Real.zero_rpow hroot.ne']
        ring
      _ = w * (u * u) * (v * v) := by simp [hw0]
  by_cases hu0 : u = 0
  · calc
      w ^ (((s : ℝ) - 2) / (s : ℝ)) *
          (w * u ^ 2 * v ^ (2 * (s - 1))) ^ (1 / (s : ℝ)) *
            (w * v ^ 2 * u ^ (2 * (s - 1))) ^ (1 / (s : ℝ)) = 0 := by
        rw [show w * u ^ 2 * v ^ (2 * (s - 1)) = 0 by simp [hu0],
          Real.zero_rpow hroot.ne']
        ring
      _ = w * (u * u) * (v * v) := by simp [hu0]
  by_cases hv0 : v = 0
  · calc
      w ^ (((s : ℝ) - 2) / (s : ℝ)) *
          (w * u ^ 2 * v ^ (2 * (s - 1))) ^ (1 / (s : ℝ)) *
            (w * v ^ 2 * u ^ (2 * (s - 1))) ^ (1 / (s : ℝ)) = 0 := by
        rw [show w * v ^ 2 * u ^ (2 * (s - 1)) = 0 by simp [hv0],
          Real.zero_rpow hroot.ne']
        ring
      _ = w * (u * u) * (v * v) := by simp [hv0]
  have hwpos : 0 < w := lt_of_le_of_ne hw (Ne.symm hw0)
  have hupos : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
  have hvpos : 0 < v := lt_of_le_of_ne hv (Ne.symm hv0)
  rw [Real.mul_rpow (mul_nonneg hw (sq_nonneg u))
      (pow_nonneg hv _),
    Real.mul_rpow hw (sq_nonneg u),
    Real.mul_rpow (mul_nonneg hw (sq_nonneg v))
      (pow_nonneg hu _),
    Real.mul_rpow hw (sq_nonneg v)]
  simp only [← Real.rpow_natCast]
  rw [← Real.rpow_mul hu, ← Real.rpow_mul hv,
    ← Real.rpow_mul hv, ← Real.rpow_mul hu]
  have hwexp : ((s : ℝ) - 2) / (s : ℝ) + 1 / (s : ℝ) +
      1 / (s : ℝ) = 1 := by field_simp; ring
  have huexp : (2 : ℝ) * (1 / (s : ℝ)) +
      2 * (s - 1 : ℕ) * (1 / (s : ℝ)) = 2 := by
    rw [Nat.cast_sub (by omega : 1 ≤ s)]
    field_simp
    ring
  have hvexp : 2 * (s - 1 : ℕ) * (1 / (s : ℝ)) +
      (2 : ℝ) * (1 / (s : ℝ)) = 2 := by
    rw [Nat.cast_sub (by omega : 1 ≤ s)]
    field_simp
    ring
  have hcast : ((2 * (s - 1) : ℕ) : ℝ) = 2 * (s - 1 : ℕ) := by
    norm_num
  have huTwo : u ^ (2 : ℝ) = u * u := by
    rw [Real.rpow_two, pow_two]
  have hvTwo : v ^ (2 : ℝ) = v * v := by
    rw [Real.rpow_two, pow_two]
  calc
    w ^ (((s : ℝ) - 2) / (s : ℝ)) *
          (w ^ (1 / (s : ℝ)) * u ^ ((2 : ℝ) * (1 / (s : ℝ))) *
            v ^ ((2 * (s - 1) : ℕ) * (1 / (s : ℝ)))) *
          (w ^ (1 / (s : ℝ)) * v ^ ((2 : ℝ) * (1 / (s : ℝ))) *
            u ^ ((2 * (s - 1) : ℕ) * (1 / (s : ℝ)))) =
        (w ^ (((s : ℝ) - 2) / (s : ℝ)) * w ^ (1 / (s : ℝ)) *
          w ^ (1 / (s : ℝ))) *
        (u ^ ((2 : ℝ) * (1 / (s : ℝ))) *
          u ^ ((2 * (s - 1) : ℕ) * (1 / (s : ℝ)))) *
        (v ^ ((2 * (s - 1) : ℕ) * (1 / (s : ℝ))) *
          v ^ ((2 : ℝ) * (1 / (s : ℝ)))) := by ring
    _ = w ^ ((((s : ℝ) - 2) / (s : ℝ)) + 1 / (s : ℝ) +
          1 / (s : ℝ)) *
        u ^ ((2 : ℝ) * (1 / (s : ℝ)) +
          (2 * (s - 1) : ℕ) * (1 / (s : ℝ))) *
        v ^ ((2 * (s - 1) : ℕ) * (1 / (s : ℝ)) +
          (2 : ℝ) * (1 / (s : ℝ))) := by
      rw [Real.rpow_add hwpos, Real.rpow_add hwpos,
        Real.rpow_add hupos, Real.rpow_add hvpos]
    _ = w * (u * u) * (v * v) := by
      rw [hcast, hwexp, huexp, hvexp, Real.rpow_one]
      rw [huTwo, hvTwo]

/-- The exact three-factor Hölder inequality used before (6.8).  The two
last factors retain opposite orientations; their later equality is a
separate symmetry statement. -/
theorem wooley_pair_mixed_holder
    {ι : Type*} (t : Finset ι) (w u v : ι → ℝ)
    (hw : ∀ i ∈ t, 0 ≤ w i)
    (hu : ∀ i ∈ t, 0 ≤ u i)
    (hv : ∀ i ∈ t, 0 ≤ v i)
    {s : ℕ} (hs : 2 ≤ s) :
    (∑ i ∈ t, w i * u i ^ 2 * v i ^ 2) ^ s ≤
      (∑ i ∈ t, w i) ^ (s - 2) *
        (∑ i ∈ t, w i * u i ^ 2 * v i ^ (2 * (s - 1))) *
          (∑ i ∈ t, w i * v i ^ 2 * u i ^ (2 * (s - 1))) := by
  let f₀ : ι → ℝ := w
  let f₁ : ι → ℝ := fun i =>
    w i * u i ^ 2 * v i ^ (2 * (s - 1))
  let f₂ : ι → ℝ := fun i =>
    w i * v i ^ 2 * u i ^ (2 * (s - 1))
  have hf₀ : ∀ i ∈ t, 0 ≤ f₀ i := by
    intro i hi
    exact hw i hi
  have hf₁ : ∀ i ∈ t, 0 ≤ f₁ i := by
    intro i hi
    exact mul_nonneg (mul_nonneg (hw i hi) (sq_nonneg _)) (pow_nonneg (hv i hi) _)
  have hf₂ : ∀ i ∈ t, 0 ≤ f₂ i := by
    intro i hi
    exact mul_nonneg (mul_nonneg (hw i hi) (sq_nonneg _)) (pow_nonneg (hu i hi) _)
  have hholder := wooley_three_factor_holder_critical_real
    t f₀ f₁ f₂ hf₀ hf₁ hf₂ hs
  have hterm (i : ι) (hi : i ∈ t) :
      f₀ i ^ (((s : ℝ) - 2) / (s : ℝ)) *
          f₁ i ^ (1 / (s : ℝ)) * f₂ i ^ (1 / (s : ℝ)) =
        w i * u i ^ 2 * v i ^ 2 := by
    dsimp [f₀, f₁, f₂]
    simpa only [pow_two] using
      (wooley_critical_interpolation_term hs
        (hw i hi) (hu i hi) (hv i hi))
  have hsumTerm :
      (∑ i ∈ t,
        f₀ i ^ (((s : ℝ) - 2) / (s : ℝ)) *
          f₁ i ^ (1 / (s : ℝ)) * f₂ i ^ (1 / (s : ℝ))) =
        ∑ i ∈ t, w i * u i ^ 2 * v i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hterm i hi
  have hsub : (s : ℝ) - 2 = ((s - 2 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hs]
    norm_num
  calc
    (∑ i ∈ t, w i * u i ^ 2 * v i ^ 2) ^ s =
        (∑ i ∈ t,
          f₀ i ^ (((s : ℝ) - 2) / (s : ℝ)) *
            f₁ i ^ (1 / (s : ℝ)) * f₂ i ^ (1 / (s : ℝ))) ^
              (s : ℝ) := by
      rw [Real.rpow_natCast, hsumTerm]
    _ ≤ (∑ i ∈ t, f₀ i) ^ ((s : ℝ) - 2) *
        (∑ i ∈ t, f₁ i) * (∑ i ∈ t, f₂ i) := hholder
    _ = (∑ i ∈ t, w i) ^ (s - 2) *
        (∑ i ∈ t, w i * u i ^ 2 * v i ^ (2 * (s - 1))) *
          (∑ i ∈ t, w i * v i ^ 2 * u i ^ (2 * (s - 1))) := by
      dsimp [f₀, f₁, f₂]
      rw [hsub, Real.rpow_natCast]

/-- For residues at depth `nu`, Wooley's separation predicate is precisely
inequality of the residue classes. -/
theorem wooleyResiduesSeparated_same_iff_ne
    {p nu : ℕ} [NeZero p] (xi eta : ZMod (p ^ nu)) :
    wooleyResiduesSeparated nu xi eta ↔ xi ≠ eta := by
  unfold wooleyResiduesSeparated
  rw [Nat.mod_eq_of_lt (ZMod.val_lt xi),
    Nat.mod_eq_of_lt (ZMod.val_lt eta)]
  constructor
  · intro hval heq
    exact hval (congrArg ZMod.val heq)
  · intro hne hval
    apply hne
    apply ZMod.val_injective
    exact hval

/-- The literal ordered separated residue-pair set at depth `nu`. -/
def wooleySeparatedResiduePairs (p nu : ℕ) [NeZero p] :
    Finset (ZMod (p ^ nu) × ZMod (p ^ nu)) :=
  (Finset.univ.product Finset.univ).filter fun xy =>
    wooleyResiduesSeparated nu xy.1 xy.2

theorem wooley_sum_separatedResiduePairs
    {p nu : ℕ} [NeZero p]
    (F : ZMod (p ^ nu) → ZMod (p ^ nu) → ℝ) :
    ∑ xy ∈ wooleySeparatedResiduePairs p nu, F xy.1 xy.2 =
      ∑ xi : ZMod (p ^ nu),
        ∑ eta : ZMod (p ^ nu) with
          wooleyResiduesSeparated nu xi eta, F xi eta := by
  unfold wooleySeparatedResiduePairs
  simp only [Finset.sum_filter]
  simpa using
    (Finset.sum_product
      (Finset.univ : Finset (ZMod (p ^ nu)))
      (Finset.univ : Finset (ZMod (p ^ nu)))
      (fun xy => if wooleyResiduesSeparated nu xy.1 xy.2 then
        F xy.1 xy.2 else 0))

theorem wooley_sum_separatedResiduePairs_apply
    {p nu : ℕ} [NeZero p]
    (F : ZMod (p ^ nu) × ZMod (p ^ nu) → ℝ) :
    ∑ xy ∈ wooleySeparatedResiduePairs p nu, F xy =
      ∑ xi : ZMod (p ^ nu),
        ∑ eta : ZMod (p ^ nu) with
          wooleyResiduesSeparated nu xi eta, F (xi, eta) := by
  simpa using wooley_sum_separatedResiduePairs
    (p := p) (nu := nu) (fun xi eta => F (xi, eta))

theorem wooleySeparatedResiduePairs_card_le (p nu : ℕ) [NeZero p] :
    #(wooleySeparatedResiduePairs p nu) ≤ (p ^ nu) ^ 2 := by
  calc
    #(wooleySeparatedResiduePairs p nu) ≤
        #((Finset.univ : Finset (ZMod (p ^ nu))).product Finset.univ) :=
      by
        unfold wooleySeparatedResiduePairs
        exact Finset.card_le_card (Finset.filter_subset _ _)
    _ = (p ^ nu) ^ 2 := by
      simp [pow_two]

/-- The two orientations of Wooley's mixed residue sum agree by swapping
the ordered separated pair. -/
theorem wooley_mixed_pair_orientation_symmetry
    {p nu : ℕ} [NeZero p]
    (w u v : ZMod (p ^ nu) → ℝ) :
    (∑ xi : ZMod (p ^ nu),
      ∑ eta : ZMod (p ^ nu) with wooleyResiduesSeparated nu xi eta,
        w xi * w eta * v xi ^ 2 * u eta ^ 2) =
      ∑ xi : ZMod (p ^ nu),
        ∑ eta : ZMod (p ^ nu) with wooleyResiduesSeparated nu xi eta,
          w xi * w eta * u xi ^ 2 * v eta ^ 2 := by
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro xi hxi
  apply Finset.sum_congr rfl
  intro eta heta
  have hsep : wooleyResiduesSeparated nu eta xi ↔
      wooleyResiduesSeparated nu xi eta := by
    rw [wooleyResiduesSeparated_same_iff_ne,
      wooleyResiduesSeparated_same_iff_ne]
    exact ne_comm
  by_cases h : wooleyResiduesSeparated nu eta xi
  · have h' := hsep.mp h
    rw [if_pos h, if_pos h']
    ring
  · have h' : ¬ wooleyResiduesSeparated nu xi eta := by
      exact fun hxiEta => h (hsep.mpr hxiEta)
    rw [if_neg h, if_neg h']

/-- Cauchy followed by the exact critical three-factor Hölder inequality.
This is the abstract finite inequality underlying (6.8), including the
square-root descent used after the two orientations are identified. -/
theorem wooley_cauchy_three_factor_symmetric
    {ι : Type*} (t : Finset ι) (w u v : ι → ℝ)
    (q M : ℝ) (hq : 0 ≤ q) (hM : 0 ≤ M)
    (hw : ∀ i ∈ t, 0 ≤ w i)
    (hu : ∀ i ∈ t, 0 ≤ u i)
    (hv : ∀ i ∈ t, 0 ≤ v i)
    {s : ℕ} (hs : 2 ≤ s)
    (hcard : (#t : ℝ) ≤ q ^ 2)
    (hmass : (∑ i ∈ t, w i) ≤ M ^ 2)
    (hsymmetry :
      (∑ i ∈ t, w i * v i ^ 2 * u i ^ (2 * (s - 1))) =
        ∑ i ∈ t, w i * u i ^ 2 * v i ^ (2 * (s - 1))) :
    (∑ i ∈ t, Real.sqrt (w i) * u i * v i) ^ s ≤
      q ^ s * M ^ (s - 2) *
        ∑ i ∈ t, w i * u i ^ 2 * v i ^ (2 * (s - 1)) := by
  let S : ℝ := ∑ i ∈ t, Real.sqrt (w i) * u i * v i
  let W : ℝ := ∑ i ∈ t, w i
  let A : ℝ := ∑ i ∈ t, w i * u i ^ 2 * v i ^ 2
  let F : ℝ := ∑ i ∈ t,
    w i * u i ^ 2 * v i ^ (2 * (s - 1))
  let G : ℝ := ∑ i ∈ t,
    w i * v i ^ 2 * u i ^ (2 * (s - 1))
  have hS : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg fun i hi =>
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hu i hi)) (hv i hi)
  have hW : 0 ≤ W := by
    dsimp [W]
    exact Finset.sum_nonneg fun i hi => hw i hi
  have hA : 0 ≤ A := by
    dsimp [A]
    exact Finset.sum_nonneg fun i hi =>
      mul_nonneg (mul_nonneg (hw i hi) (sq_nonneg _)) (sq_nonneg _)
  have hF : 0 ≤ F := by
    dsimp [F]
    exact Finset.sum_nonneg fun i hi =>
      mul_nonneg (mul_nonneg (hw i hi) (sq_nonneg _))
        (pow_nonneg (hv i hi) _)
  have hG : 0 ≤ G := by
    dsimp [G]
    exact Finset.sum_nonneg fun i hi =>
      mul_nonneg (mul_nonneg (hw i hi) (sq_nonneg _))
        (pow_nonneg (hu i hi) _)
  have hCauchy : S ^ 2 ≤ (#t : ℝ) * A := by
    have h := sum_mul_sq_le_sq_mul_sq (R := ℝ) t
      (fun _ : ι => 1)
      (fun i => Real.sqrt (w i) * u i * v i)
    have hsquares :
        (∑ i ∈ t, (Real.sqrt (w i) * u i * v i) ^ 2) = A := by
      dsimp [A]
      apply Finset.sum_congr rfl
      intro i hi
      rw [mul_pow, mul_pow, Real.sq_sqrt (hw i hi)]
    dsimp [S]
    calc
      (∑ i ∈ t, Real.sqrt (w i) * u i * v i) ^ 2 ≤
          (#t : ℝ) *
            ∑ i ∈ t, (Real.sqrt (w i) * u i * v i) ^ 2 := by
        simpa only [one_mul, one_pow, sum_const, nsmul_eq_mul,
          Nat.cast_ofNat, Nat.cast_card, mul_one] using h
      _ = (#t : ℝ) * A := by rw [hsquares]
  have hHolder : A ^ s ≤ W ^ (s - 2) * F * G := by
    simpa only [A, W, F, G] using
      (wooley_pair_mixed_holder t w u v hw hu hv hs)
  have hRaised := pow_le_pow_left₀ (sq_nonneg S) hCauchy s
  have hcardPow : (#t : ℝ) ^ s ≤ (q ^ 2) ^ s :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hcard s
  have hmassPow : W ^ (s - 2) ≤ (M ^ 2) ^ (s - 2) :=
    pow_le_pow_left₀ hW hmass (s - 2)
  have hSquare : (S ^ s) ^ 2 ≤
      (q ^ s * M ^ (s - 2) * F) ^ 2 := by
    calc
      (S ^ s) ^ 2 = (S ^ 2) ^ s := by
        calc
          (S ^ s) ^ 2 = S ^ (s * 2) := (pow_mul S s 2).symm
          _ = S ^ (2 * s) := by rw [Nat.mul_comm]
          _ = (S ^ 2) ^ s := pow_mul S 2 s
      _ ≤ ((#t : ℝ) * A) ^ s := hRaised
      _ = (#t : ℝ) ^ s * A ^ s := by rw [mul_pow]
      _ ≤ (#t : ℝ) ^ s * (W ^ (s - 2) * F * G) := by
        gcongr
      _ ≤ (q ^ 2) ^ s * ((M ^ 2) ^ (s - 2) * F * G) := by
        gcongr
      _ = (q ^ 2) ^ s * ((M ^ 2) ^ (s - 2) * F * F) := by
        rw [show G = F by simpa [G, F] using hsymmetry]
      _ = (q ^ s * M ^ (s - 2) * F) ^ 2 := by
        have hqpow : (q ^ 2) ^ s = (q ^ s) ^ 2 := by
          calc
            (q ^ 2) ^ s = q ^ (2 * s) := (pow_mul q 2 s).symm
            _ = q ^ (s * 2) := by rw [Nat.mul_comm]
            _ = (q ^ s) ^ 2 := pow_mul q s 2
        have hMpow : (M ^ 2) ^ (s - 2) =
            (M ^ (s - 2)) ^ 2 := by
          calc
            (M ^ 2) ^ (s - 2) = M ^ (2 * (s - 2)) :=
              (pow_mul M 2 (s - 2)).symm
            _ = M ^ ((s - 2) * 2) := by rw [Nat.mul_comm]
            _ = (M ^ (s - 2)) ^ 2 := pow_mul M (s - 2) 2
        rw [hqpow, hMpow, mul_pow, mul_pow]
        ring
  have hRight : 0 ≤ q ^ s * M ^ (s - 2) * F :=
    mul_nonneg (mul_nonneg (pow_nonneg hq _) (pow_nonneg hM _)) hF
  exact (sq_le_sq₀ (pow_nonneg hS s) hRight).mp hSquare

/-- Squaring the triangle inequality and separating the diagonal from the
ordered off-diagonal pairs.  This is the finite algebra used in (6.6). -/
theorem wooley_norm_sum_sq_le_diagonal_add_offDiagonal
    {ι : Type*} [DecidableEq ι] (t : Finset ι) (z : ι → ℂ) :
    ‖∑ i ∈ t, z i‖ ^ 2 ≤
      (∑ i ∈ t, ‖z i‖ ^ 2) +
        ∑ i ∈ t, ∑ j ∈ t with j ≠ i, ‖z i‖ * ‖z j‖ := by
  have hnorm : ‖∑ i ∈ t, z i‖ ≤ ∑ i ∈ t, ‖z i‖ :=
    norm_sum_le _ _
  have hnonneg : 0 ≤ ∑ i ∈ t, ‖z i‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  calc
    ‖∑ i ∈ t, z i‖ ^ 2 ≤ (∑ i ∈ t, ‖z i‖) ^ 2 := hsq
    _ = ∑ i ∈ t, ∑ j ∈ t, ‖z i‖ * ‖z j‖ := by
      rw [pow_two, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
    _ = (∑ i ∈ t, ‖z i‖ ^ 2) +
        ∑ i ∈ t, ∑ j ∈ t with j ≠ i, ‖z i‖ * ‖z j‖ := by
      have hinner (i : ι) (hi : i ∈ t) :
          (∑ j ∈ t, ‖z i‖ * ‖z j‖) =
            ‖z i‖ ^ 2 + ∑ j ∈ t with j ≠ i, ‖z i‖ * ‖z j‖ := by
        rw [Finset.sum_eq_add_sum_diff_singleton_of_mem hi]
        congr 1
        · ring
        · apply Finset.sum_congr
          · ext j
            simp [and_comm]
          · intro j hj
            rfl
      calc
        (∑ i ∈ t, ∑ j ∈ t, ‖z i‖ * ‖z j‖) =
            ∑ i ∈ t,
              (‖z i‖ ^ 2 +
                ∑ j ∈ t with j ≠ i, ‖z i‖ * ‖z j‖) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hinner i hi
        _ = (∑ i ∈ t, ‖z i‖ ^ 2) +
            ∑ i ∈ t, ∑ j ∈ t with j ≠ i, ‖z i‖ * ‖z j‖ := by
          rw [Finset.sum_add_distrib]

/-- The diagonal term `T₁(alpha)` from (6.6). -/
def wooleyInitialDiagonal {Q : ℕ}
    (p B nu k : ℕ) [NeZero p] [NeZero (p ^ B)]
    (gamma : Fin Q → ℂ) (alpha : Fin k → ZMod (p ^ B)) : ℝ :=
  (wooleyWeightedMassSq gamma)⁻¹ *
    ∑ xi : ZMod (p ^ nu),
      wooleyWeightedResidueMassSq gamma xi *
        ‖wooleyWeightedNormalizedResidueGridSum
          (p ^ B) k gamma alpha xi‖ ^ 2

/-- The ordered, separated off-diagonal term `T₂(alpha)` from (6.6). -/
def wooleyInitialOffDiagonal {Q : ℕ}
    (p B nu k : ℕ) [NeZero p] [NeZero (p ^ B)]
    (gamma : Fin Q → ℂ) (alpha : Fin k → ZMod (p ^ B)) : ℝ :=
  (wooleyWeightedMassSq gamma)⁻¹ *
    ∑ xi : ZMod (p ^ nu),
      ∑ eta : ZMod (p ^ nu) with wooleyResiduesSeparated nu xi eta,
        Real.sqrt (wooleyWeightedResidueMassSq gamma xi) *
          Real.sqrt (wooleyWeightedResidueMassSq gamma eta) *
          ‖wooleyWeightedNormalizedResidueGridSum
            (p ^ B) k gamma alpha xi‖ *
          ‖wooleyWeightedNormalizedResidueGridSum
            (p ^ B) k gamma alpha eta‖

theorem wooleyInitialDiagonal_nonneg {Q : ℕ}
    (p B nu k : ℕ) [NeZero p] [NeZero (p ^ B)]
    (gamma : Fin Q → ℂ) (alpha : Fin k → ZMod (p ^ B)) :
    0 ≤ wooleyInitialDiagonal p B nu k gamma alpha := by
  unfold wooleyInitialDiagonal
  exact mul_nonneg
    (inv_nonneg.mpr (wooleyWeightedMassSq_nonneg gamma))
    (Finset.sum_nonneg fun xi hxi =>
      mul_nonneg (wooleyWeightedResidueMassSq_nonneg gamma xi)
        (sq_nonneg _))

theorem wooleyInitialOffDiagonal_nonneg {Q : ℕ}
    (p B nu k : ℕ) [NeZero p] [NeZero (p ^ B)]
    (gamma : Fin Q → ℂ) (alpha : Fin k → ZMod (p ^ B)) :
    0 ≤ wooleyInitialOffDiagonal p B nu k gamma alpha := by
  unfold wooleyInitialOffDiagonal
  exact mul_nonneg
    (inv_nonneg.mpr (wooleyWeightedMassSq_nonneg gamma))
    (Finset.sum_nonneg fun xi hxi =>
      Finset.sum_nonneg fun eta heta => by positivity)

/-- The first oriented mixed sum (`T₅`) occurring in (6.8). -/
def wooleyInitialMixedForward {Q : ℕ}
    (p B nu k s : ℕ) [NeZero p] [NeZero (p ^ B)]
    (gamma : Fin Q → ℂ) (alpha : Fin k → ZMod (p ^ B)) : ℝ :=
  ∑ xi : ZMod (p ^ nu),
    ∑ eta : ZMod (p ^ nu) with wooleyResiduesSeparated nu xi eta,
      wooleyWeightedResidueMassSq gamma xi *
        wooleyWeightedResidueMassSq gamma eta *
        ‖wooleyWeightedNormalizedResidueGridSum
          (p ^ B) k gamma alpha xi‖ ^ 2 *
        ‖wooleyWeightedNormalizedResidueGridSum
          (p ^ B) k gamma alpha eta‖ ^ (2 * (s - 1))

theorem wooleyInitialMixedForward_nonneg {Q : ℕ}
    (p B nu k s : ℕ) [NeZero p] [NeZero (p ^ B)]
    (gamma : Fin Q → ℂ) (alpha : Fin k → ZMod (p ^ B)) :
    0 ≤ wooleyInitialMixedForward p B nu k s gamma alpha := by
  unfold wooleyInitialMixedForward
  exact Finset.sum_nonneg fun xi hxi =>
    Finset.sum_nonneg fun eta heta =>
      mul_nonneg
        (mul_nonneg
          (mul_nonneg (wooleyWeightedResidueMassSq_nonneg gamma xi)
            (wooleyWeightedResidueMassSq_nonneg gamma eta))
          (sq_nonneg _))
        (pow_nonneg (norm_nonneg _) _)

/-- Swapping the ordered separated residue pair identifies `T₆` with
`T₅`, exactly as in the sentence preceding (6.8). -/
theorem wooleyInitialMixedReverse_eq_forward {Q : ℕ}
    (p B nu k s : ℕ) [NeZero p] [NeZero (p ^ B)]
    (gamma : Fin Q → ℂ) (alpha : Fin k → ZMod (p ^ B)) :
    (∑ xi : ZMod (p ^ nu),
      ∑ eta : ZMod (p ^ nu) with wooleyResiduesSeparated nu xi eta,
        wooleyWeightedResidueMassSq gamma xi *
          wooleyWeightedResidueMassSq gamma eta *
          ‖wooleyWeightedNormalizedResidueGridSum
            (p ^ B) k gamma alpha eta‖ ^ 2 *
          ‖wooleyWeightedNormalizedResidueGridSum
            (p ^ B) k gamma alpha xi‖ ^ (2 * (s - 1))) =
      wooleyInitialMixedForward p B nu k s gamma alpha := by
  unfold wooleyInitialMixedForward
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro xi hxi
  apply Finset.sum_congr rfl
  intro eta heta
  have hsep : wooleyResiduesSeparated nu eta xi ↔
      wooleyResiduesSeparated nu xi eta := by
    rw [wooleyResiduesSeparated_same_iff_ne,
      wooleyResiduesSeparated_same_iff_ne]
    exact ne_comm
  by_cases h : wooleyResiduesSeparated nu eta xi
  · have h' := hsep.mp h
    rw [if_pos h, if_pos h']
    ring
  · have h' : ¬ wooleyResiduesSeparated nu xi eta := by
      exact fun hxiEta => h (hsep.mpr hxiEta)
    rw [if_neg h, if_neg h']

/-- The separated pair mass is bounded by the square of the total mass;
the omitted diagonal has nonnegative weight. -/
theorem wooley_separated_pair_mass_le_square {Q : ℕ}
    (p nu : ℕ) [NeZero p] (gamma : Fin Q → ℂ) :
    (∑ xi : ZMod (p ^ nu),
      ∑ eta : ZMod (p ^ nu) with wooleyResiduesSeparated nu xi eta,
        wooleyWeightedResidueMassSq gamma xi *
          wooleyWeightedResidueMassSq gamma eta) ≤
      wooleyWeightedMassSq gamma ^ 2 := by
  let w : ZMod (p ^ nu) → ℝ := fun xi =>
    wooleyWeightedResidueMassSq gamma xi
  have hfilter (xi : ZMod (p ^ nu)) :
      (∑ eta : ZMod (p ^ nu) with wooleyResiduesSeparated nu xi eta,
          w xi * w eta) ≤
        ∑ eta : ZMod (p ^ nu), w xi * w eta := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro eta heta hnot
    exact mul_nonneg (wooleyWeightedResidueMassSq_nonneg gamma xi)
      (wooleyWeightedResidueMassSq_nonneg gamma eta)
  calc
    (∑ xi : ZMod (p ^ nu),
      ∑ eta : ZMod (p ^ nu) with wooleyResiduesSeparated nu xi eta,
        wooleyWeightedResidueMassSq gamma xi *
          wooleyWeightedResidueMassSq gamma eta) ≤
        ∑ xi : ZMod (p ^ nu),
          ∑ eta : ZMod (p ^ nu), w xi * w eta := by
      apply Finset.sum_le_sum
      intro xi hxi
      simpa [w] using hfilter xi
    _ = (∑ xi : ZMod (p ^ nu), w xi) ^ 2 := by
      rw [pow_two, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro xi hxi
      rw [Finset.mul_sum]
    _ = wooleyWeightedMassSq gamma ^ 2 := by
      rw [show (∑ xi : ZMod (p ^ nu), w xi) =
          wooleyWeightedMassSq gamma by
        simpa [w] using wooley_sum_weightedResidueMassSq
          (q := p ^ nu) gamma]

theorem wooley_inv_pow_mul_pow_pred
    {M : ℝ} {s : ℕ} (hM : 0 < M) (hs : 1 ≤ s) :
    M⁻¹ ^ s * M ^ (s - 1) = M⁻¹ := by
  have hpow : M ^ s = M ^ (s - 1) * M := by
    conv_lhs => rw [← Nat.sub_add_cancel hs, pow_add, pow_one]
  rw [inv_pow, hpow]
  field_simp

theorem wooley_inv_pow_mul_pow_sub_two
    {M : ℝ} {s : ℕ} (hM : 0 < M) (hs : 2 ≤ s) :
    M⁻¹ ^ s * M ^ (s - 2) = M⁻¹ ^ 2 := by
  have hpow : M ^ s = M ^ (s - 2) * M ^ 2 := by
    conv_lhs => rw [← Nat.sub_add_cancel hs, pow_add]
  rw [inv_pow, hpow]
  field_simp

/-- Equation (6.7), retaining the exact inverse global mass. -/
theorem wooley_equation_6_7 {Q : ℕ}
    (p B nu k s : ℕ) [NeZero p] [NeZero (p ^ B)]
    (gamma : Fin Q → ℂ) (alpha : Fin k → ZMod (p ^ B))
    (hs : 1 ≤ s) :
    wooleyInitialDiagonal p B nu k gamma alpha ^ s ≤
      (wooleyWeightedMassSq gamma)⁻¹ *
        ∑ xi : ZMod (p ^ nu),
          wooleyWeightedResidueMassSq gamma xi *
            ‖wooleyWeightedNormalizedResidueGridSum
              (p ^ B) k gamma alpha xi‖ ^ (2 * s) := by
  by_cases hmass : wooleyWeightedMassSq gamma = 0
  · have hs0 : s ≠ 0 := by omega
    simp [wooleyInitialDiagonal, hmass, hs0]
  · let M : ℝ := wooleyWeightedMassSq gamma
    let w : ZMod (p ^ nu) → ℝ := fun xi =>
      wooleyWeightedResidueMassSq gamma xi
    let f : ZMod (p ^ nu) → ℝ := fun xi =>
      ‖wooleyWeightedNormalizedResidueGridSum
        (p ^ B) k gamma alpha xi‖ ^ 2
    let R : ℝ := ∑ xi : ZMod (p ^ nu),
      w xi * ‖wooleyWeightedNormalizedResidueGridSum
        (p ^ B) k gamma alpha xi‖ ^ (2 * s)
    have hM : 0 < M := lt_of_le_of_ne
      (wooleyWeightedMassSq_nonneg gamma) (Ne.symm hmass)
    have hholder := wooley_weighted_rpow_sum_le
      (Finset.univ : Finset (ZMod (p ^ nu))) w f
      (p := (s : ℝ)) (by exact_mod_cast hs)
      (fun xi => wooleyWeightedResidueMassSq_nonneg gamma xi)
      (fun xi => sq_nonneg _)
    have hsub : (s : ℝ) - 1 = ((s - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hs]
      norm_num
    have hholderNat :
        (∑ xi : ZMod (p ^ nu), w xi * f xi) ^ s ≤
          M ^ (s - 1) * R := by
      rw [← Real.rpow_natCast] at ⊢
      calc
        (∑ xi : ZMod (p ^ nu), w xi * f xi) ^ (s : ℝ) ≤
            (∑ xi : ZMod (p ^ nu), w xi) ^ ((s : ℝ) - 1) *
              ∑ xi : ZMod (p ^ nu), w xi * f xi ^ (s : ℝ) := hholder
        _ = M ^ (s - 1) * R := by
          dsimp [w, f, M, R]
          rw [wooley_sum_weightedResidueMassSq, hsub,
            Real.rpow_natCast]
          apply congrArg (wooleyWeightedMassSq gamma ^ (s - 1) * ·)
          apply Finset.sum_congr rfl
          intro xi hxi
          rw [Real.rpow_natCast, ← pow_mul]
    unfold wooleyInitialDiagonal
    change (M⁻¹ * ∑ xi : ZMod (p ^ nu), w xi * f xi) ^ s ≤ M⁻¹ * R
    calc
      (M⁻¹ * ∑ xi : ZMod (p ^ nu), w xi * f xi) ^ s =
          M⁻¹ ^ s * (∑ xi : ZMod (p ^ nu), w xi * f xi) ^ s := by
        rw [mul_pow]
      _ ≤ M⁻¹ ^ s * (M ^ (s - 1) * R) := by
        gcongr
      _ = M⁻¹ * R := by
        rw [← mul_assoc, wooley_inv_pow_mul_pow_pred hM hs]

/-- Equation (6.8), obtained from Cauchy, critical three-factor Hölder,
the exact pair count, total residue mass, and swap symmetry. -/
theorem wooley_equation_6_8 {Q : ℕ}
    (p B nu k s : ℕ) [NeZero p] [NeZero (p ^ B)]
    (gamma : Fin Q → ℂ) (alpha : Fin k → ZMod (p ^ B))
    (hs : 2 ≤ s) :
    wooleyInitialOffDiagonal p B nu k gamma alpha ^ s ≤
      (wooleyWeightedMassSq gamma)⁻¹ ^ 2 *
        (p ^ nu : ℝ) ^ s *
          wooleyInitialMixedForward p B nu k s gamma alpha := by
  by_cases hmass : wooleyWeightedMassSq gamma = 0
  · have hs0 : s ≠ 0 := by omega
    simp [wooleyInitialOffDiagonal, hmass, hs0]
  · let M : ℝ := wooleyWeightedMassSq gamma
    let q : ℝ := (p ^ nu : ℕ)
    let t : Finset (ZMod (p ^ nu) × ZMod (p ^ nu)) :=
      wooleySeparatedResiduePairs p nu
    let w : (ZMod (p ^ nu) × ZMod (p ^ nu)) → ℝ := fun xy =>
      wooleyWeightedResidueMassSq gamma xy.1 *
        wooleyWeightedResidueMassSq gamma xy.2
    let u : (ZMod (p ^ nu) × ZMod (p ^ nu)) → ℝ := fun xy =>
      ‖wooleyWeightedNormalizedResidueGridSum
        (p ^ B) k gamma alpha xy.1‖
    let v : (ZMod (p ^ nu) × ZMod (p ^ nu)) → ℝ := fun xy =>
      ‖wooleyWeightedNormalizedResidueGridSum
        (p ^ B) k gamma alpha xy.2‖
    let S : ℝ := ∑ xy ∈ t, Real.sqrt (w xy) * u xy * v xy
    let F : ℝ := ∑ xy ∈ t,
      w xy * u xy ^ 2 * v xy ^ (2 * (s - 1))
    have hMpos : 0 < M := lt_of_le_of_ne
      (wooleyWeightedMassSq_nonneg gamma) (Ne.symm hmass)
    have hq : 0 ≤ q := by positivity
    have hw : ∀ xy ∈ t, 0 ≤ w xy := by
      intro xy hxy
      exact mul_nonneg
        (wooleyWeightedResidueMassSq_nonneg gamma xy.1)
        (wooleyWeightedResidueMassSq_nonneg gamma xy.2)
    have hu : ∀ xy ∈ t, 0 ≤ u xy := by
      intro xy hxy
      exact norm_nonneg _
    have hv : ∀ xy ∈ t, 0 ≤ v xy := by
      intro xy hxy
      exact norm_nonneg _
    have hcard : (#t : ℝ) ≤ q ^ 2 := by
      dsimp [t, q]
      exact_mod_cast wooleySeparatedResiduePairs_card_le p nu
    have hpairMass : (∑ xy ∈ t, w xy) ≤ M ^ 2 := by
      dsimp [t, w, M]
      rw [wooley_sum_separatedResiduePairs_apply]
      exact wooley_separated_pair_mass_le_square p nu gamma
    have hF : F = wooleyInitialMixedForward
        p B nu k s gamma alpha := by
      dsimp [F, t, w, u, v]
      rw [wooley_sum_separatedResiduePairs_apply]
      rfl
    have hsym :
        (∑ xy ∈ t,
          w xy * v xy ^ 2 * u xy ^ (2 * (s - 1))) = F := by
      dsimp [t, w, u, v]
      rw [wooley_sum_separatedResiduePairs_apply]
      calc
        (∑ xi : ZMod (p ^ nu),
          ∑ eta : ZMod (p ^ nu) with
            wooleyResiduesSeparated nu xi eta,
              wooleyWeightedResidueMassSq gamma xi *
                wooleyWeightedResidueMassSq gamma eta *
                ‖wooleyWeightedNormalizedResidueGridSum
                  (p ^ B) k gamma alpha eta‖ ^ 2 *
                ‖wooleyWeightedNormalizedResidueGridSum
                  (p ^ B) k gamma alpha xi‖ ^ (2 * (s - 1))) =
            wooleyInitialMixedForward p B nu k s gamma alpha :=
          wooleyInitialMixedReverse_eq_forward
            p B nu k s gamma alpha
        _ = F := hF.symm
    have hcore : S ^ s ≤ q ^ s * M ^ (s - 2) * F := by
      exact wooley_cauchy_three_factor_symmetric
        t w u v q M hq hMpos.le hw hu hv hs hcard hpairMass
          (by simpa [F] using hsym)
    have hS : S =
        ∑ xi : ZMod (p ^ nu),
          ∑ eta : ZMod (p ^ nu) with wooleyResiduesSeparated nu xi eta,
            Real.sqrt (wooleyWeightedResidueMassSq gamma xi) *
              Real.sqrt (wooleyWeightedResidueMassSq gamma eta) *
              ‖wooleyWeightedNormalizedResidueGridSum
                (p ^ B) k gamma alpha xi‖ *
              ‖wooleyWeightedNormalizedResidueGridSum
                (p ^ B) k gamma alpha eta‖ := by
      dsimp [S, t, w, u, v]
      rw [wooley_sum_separatedResiduePairs_apply]
      apply Finset.sum_congr rfl
      intro xi hxi
      apply Finset.sum_congr rfl
      intro eta heta
      rw [Real.sqrt_mul
        (wooleyWeightedResidueMassSq_nonneg gamma xi)]
    have hT2 : wooleyInitialOffDiagonal p B nu k gamma alpha =
        M⁻¹ * S := by
      unfold wooleyInitialOffDiagonal
      dsimp [M]
      rw [hS]
    have hqEq : q = (p : ℝ) ^ nu := by
      dsimp [q]
      norm_cast
    rw [hT2, ← hqEq]
    calc
      (M⁻¹ * S) ^ s = M⁻¹ ^ s * S ^ s := by
        rw [mul_pow]
      _ ≤ M⁻¹ ^ s * (q ^ s * M ^ (s - 2) * F) := by
        gcongr
      _ = M⁻¹ ^ 2 * q ^ s *
          wooleyInitialMixedForward p B nu k s gamma alpha := by
        rw [hF]
        calc
          M⁻¹ ^ s *
              (q ^ s * M ^ (s - 2) *
                wooleyInitialMixedForward p B nu k s gamma alpha) =
              (M⁻¹ ^ s * M ^ (s - 2)) * q ^ s *
                wooleyInitialMixedForward p B nu k s gamma alpha := by ring
          _ = M⁻¹ ^ 2 * q ^ s *
                wooleyInitialMixedForward p B nu k s gamma alpha := by
            rw [wooley_inv_pow_mul_pow_sub_two hMpos hs]

/-- Wooley equation (6.6), with the exact normalized diagonal and ordered
separated off-diagonal terms. -/
theorem wooley_equation_6_6 {Q : ℕ}
    (p B nu k : ℕ) [NeZero p] [NeZero (p ^ B)]
    (gamma : Fin Q → ℂ) (alpha : Fin k → ZMod (p ^ B)) :
    ‖wooleyWeightedNormalizedGridSum (p ^ B) k gamma alpha‖ ^ 2 ≤
      wooleyInitialDiagonal p B nu k gamma alpha +
        wooleyInitialOffDiagonal p B nu k gamma alpha := by
  by_cases hmass : wooleyWeightedMassSq gamma = 0
  · simp [wooleyWeightedNormalizedGridSum, hmass,
      wooleyInitialDiagonal, wooleyInitialOffDiagonal]
  · let M : ℝ := wooleyWeightedMassSq gamma
    let a : ZMod (p ^ nu) → ℂ := fun xi =>
      (Real.sqrt (wooleyWeightedResidueMassSq gamma xi) : ℂ) *
        wooleyWeightedNormalizedResidueGridSum
          (p ^ B) k gamma alpha xi
    have hM : 0 < M := lt_of_le_of_ne
      (wooleyWeightedMassSq_nonneg gamma) (Ne.symm hmass)
    have hdecomp := wooley_weighted_normalizedGridSum_decomposition
      (qH := p ^ nu) gamma alpha hmass
    have hraw := wooley_norm_sum_sq_le_diagonal_add_offDiagonal
      (Finset.univ : Finset (ZMod (p ^ nu))) a
    have hscale :
        ‖((Real.sqrt M : ℝ) : ℂ)⁻¹‖ ^ 2 = M⁻¹ := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _), inv_pow,
        Real.sq_sqrt hM.le]
    rw [hdecomp, norm_mul, mul_pow, hscale]
    calc
      M⁻¹ * ‖∑ xi : ZMod (p ^ nu), a xi‖ ^ 2 ≤
          M⁻¹ * ((∑ xi : ZMod (p ^ nu), ‖a xi‖ ^ 2) +
            ∑ xi : ZMod (p ^ nu),
              ∑ eta : ZMod (p ^ nu) with eta ≠ xi,
                ‖a xi‖ * ‖a eta‖) := by
        gcongr
      _ = wooleyInitialDiagonal p B nu k gamma alpha +
          wooleyInitialOffDiagonal p B nu k gamma alpha := by
        have hnormA (xi : ZMod (p ^ nu)) :
            ‖a xi‖ =
              Real.sqrt (wooleyWeightedResidueMassSq gamma xi) *
                ‖wooleyWeightedNormalizedResidueGridSum
                  (p ^ B) k gamma alpha xi‖ := by
          simp [a, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (Real.sqrt_nonneg _)]
        simp_rw [hnormA]
        unfold wooleyInitialDiagonal wooleyInitialOffDiagonal
        rw [mul_add]
        congr 1
        · apply congrArg (M⁻¹ * ·)
          apply Finset.sum_congr rfl
          intro xi hxi
          rw [mul_pow, Real.sq_sqrt
            (wooleyWeightedResidueMassSq_nonneg gamma xi)]
        · apply congrArg (M⁻¹ * ·)
          apply Finset.sum_congr rfl
          intro xi hxi
          apply Finset.sum_congr
          · ext eta
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            rw [wooleyResiduesSeparated_same_iff_ne]
            exact ne_comm
          · intro eta heta
            ring

/-- The elementary convexity estimate used when equation (6.6) is raised
to the `s`-th power.  The constant is retained explicitly. -/
theorem wooley_add_pow_le_two_pow_pred_mul
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    {s : ℕ} (hs : 1 ≤ s) :
    (a + b) ^ s ≤ 2 ^ (s - 1) * (a ^ s + b ^ s) := by
  let aa : NNReal := ⟨a, ha⟩
  let bb : NNReal := ⟨b, hb⟩
  have h := NNReal.rpow_add_le_mul_rpow_add_rpow aa bb
    (p := (s : ℝ)) (by exact_mod_cast hs)
  norm_cast at h
  simpa [aa, bb, Real.rpow_natCast] using h

/-- The pointwise estimate integrated in Wooley equation (6.9).  Both
terms on the right are the literal normalized diagonal and mixed sums. -/
theorem wooley_equation_6_9_pointwise {Q : ℕ}
    (p B nu k s : ℕ) [NeZero p] [NeZero (p ^ B)]
    (gamma : Fin Q → ℂ) (alpha : Fin k → ZMod (p ^ B))
    (hs : 2 ≤ s) :
    ‖wooleyWeightedNormalizedGridSum (p ^ B) k gamma alpha‖ ^ (2 * s) ≤
      2 ^ (s - 1) *
        ((wooleyWeightedMassSq gamma)⁻¹ *
            ∑ xi : ZMod (p ^ nu),
              wooleyWeightedResidueMassSq gamma xi *
                ‖wooleyWeightedNormalizedResidueGridSum
                  (p ^ B) k gamma alpha xi‖ ^ (2 * s) +
          (wooleyWeightedMassSq gamma)⁻¹ ^ 2 *
            (p ^ nu : ℝ) ^ s *
              wooleyInitialMixedForward p B nu k s gamma alpha) := by
  let D := wooleyInitialDiagonal p B nu k gamma alpha
  let O := wooleyInitialOffDiagonal p B nu k gamma alpha
  have hsplit := wooley_equation_6_6 p B nu k gamma alpha
  have hpow :
      (‖wooleyWeightedNormalizedGridSum (p ^ B) k gamma alpha‖ ^ 2) ^ s ≤
        (D + O) ^ s := by
    exact pow_le_pow_left₀ (sq_nonneg _) hsplit s
  have hconv : (D + O) ^ s ≤
      2 ^ (s - 1) * (D ^ s + O ^ s) :=
    wooley_add_pow_le_two_pow_pred_mul
      (wooleyInitialDiagonal_nonneg p B nu k gamma alpha)
      (wooleyInitialOffDiagonal_nonneg p B nu k gamma alpha)
      (by omega)
  have hdiag := wooley_equation_6_7 p B nu k s gamma alpha (by omega)
  have hoff := wooley_equation_6_8 p B nu k s gamma alpha hs
  calc
    ‖wooleyWeightedNormalizedGridSum (p ^ B) k gamma alpha‖ ^ (2 * s) =
        (‖wooleyWeightedNormalizedGridSum (p ^ B) k gamma alpha‖ ^ 2) ^ s := by
      rw [pow_mul]
    _ ≤ (D + O) ^ s := hpow
    _ ≤ 2 ^ (s - 1) * (D ^ s + O ^ s) := hconv
    _ ≤ 2 ^ (s - 1) *
        ((wooleyWeightedMassSq gamma)⁻¹ *
            ∑ xi : ZMod (p ^ nu),
              wooleyWeightedResidueMassSq gamma xi *
                ‖wooleyWeightedNormalizedResidueGridSum
                  (p ^ B) k gamma alpha xi‖ ^ (2 * s) +
          (wooleyWeightedMassSq gamma)⁻¹ ^ 2 *
            (p ^ nu : ℝ) ^ s *
              wooleyInitialMixedForward p B nu k s gamma alpha) := by
      gcongr

/-- Averaging the literal diagonal integrand gives exactly the conditioned
mean in equation (3.8). -/
theorem wooley_initial_diagonal_average {Q : ℕ}
    (p B nu k s : ℕ) [NeZero p] [NeZero (p ^ B)] [NeZero (p ^ nu)]
    (gamma : Fin Q → ℂ) :
    ((((p ^ B) ^ k : ℕ) : ℝ))⁻¹ *
        ∑ alpha : Fin k → ZMod (p ^ B),
          (wooleyWeightedMassSq gamma)⁻¹ *
            ∑ xi : ZMod (p ^ nu),
              wooleyWeightedResidueMassSq gamma xi *
                ‖wooleyWeightedNormalizedResidueGridSum
                  (p ^ B) k gamma alpha xi‖ ^ (2 * s) =
      wooleyWeightedConditionedGridMean
        s k (p ^ B) (p ^ nu) gamma := by
  unfold wooleyWeightedConditionedGridMean
  split_ifs with hmass
  · simp [hmass]
  · simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro xi hxi
    apply Finset.sum_congr rfl
    intro alpha halpha
    ac_rfl

/-- Averaging the literal mixed integrand in (6.8) gives exactly
`K^1_{nu,nu}` with the normalization from (3.19)--(3.20). -/
theorem wooley_initial_mixed_average {Q : ℕ}
    (p B nu k s : ℕ) [NeZero p] [NeZero (p ^ B)]
    (gamma : Fin Q → ℂ) :
    ((((p ^ B) ^ k : ℕ) : ℝ))⁻¹ *
        ∑ alpha : Fin k → ZMod (p ^ B),
          (wooleyWeightedMassSq gamma)⁻¹ ^ 2 *
            wooleyInitialMixedForward p B nu k s gamma alpha =
      wooleyMixedGridMean s k 1 p B nu nu nu gamma := by
  unfold wooleyMixedGridMean
  split_ifs with hmass
  · simp [hmass]
  · simp only [wooleyMixedResidueGridMoment,
      wooleyTriangular_one, Nat.mul_one]
    unfold wooleyInitialMixedForward
    simp_rw [Finset.mul_sum]
    rw [show
      (∑ alpha : Fin k → ZMod (p ^ B),
        ∑ xi : ZMod (p ^ nu),
          ∑ eta : ZMod (p ^ nu) with wooleyResiduesSeparated nu xi eta,
            ((((p ^ B) ^ k : ℕ) : ℝ))⁻¹ *
              ((wooleyWeightedMassSq gamma)⁻¹ ^ 2 *
                (wooleyWeightedResidueMassSq gamma xi *
                  wooleyWeightedResidueMassSq gamma eta *
                  ‖wooleyWeightedNormalizedResidueGridSum
                    (p ^ B) k gamma alpha xi‖ ^ 2 *
                  ‖wooleyWeightedNormalizedResidueGridSum
                    (p ^ B) k gamma alpha eta‖ ^ (2 * (s - 1))))) =
        ∑ xi : ZMod (p ^ nu),
          ∑ eta : ZMod (p ^ nu) with wooleyResiduesSeparated nu xi eta,
            ∑ alpha : Fin k → ZMod (p ^ B),
              ((((p ^ B) ^ k : ℕ) : ℝ))⁻¹ *
                ((wooleyWeightedMassSq gamma)⁻¹ ^ 2 *
                  (wooleyWeightedResidueMassSq gamma xi *
                    wooleyWeightedResidueMassSq gamma eta *
                    ‖wooleyWeightedNormalizedResidueGridSum
                      (p ^ B) k gamma alpha xi‖ ^ 2 *
                    ‖wooleyWeightedNormalizedResidueGridSum
                      (p ^ B) k gamma alpha eta‖ ^ (2 * (s - 1)))) by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro xi hxi
        rw [Finset.sum_comm]]
    apply Finset.sum_congr rfl
    intro xi hxi
    apply Finset.sum_congr rfl
    intro eta heta
    apply Finset.sum_congr rfl
    intro alpha halpha
    ac_rfl

/-- Wooley equation (6.9), as an exact finite-grid inequality.  Its
implicit Vinogradov constant is displayed here as `2^(s-1)`. -/
theorem wooley_equation_6_9 {Q : ℕ}
    (p B nu k s : ℕ) [NeZero p] [NeZero (p ^ B)] [NeZero (p ^ nu)]
    (gamma : Fin Q → ℂ) (hs : 2 ≤ s) :
    wooleyWeightedGridMean s k (p ^ B) gamma ≤
      2 ^ (s - 1) *
        (wooleyWeightedConditionedGridMean
            s k (p ^ B) (p ^ nu) gamma +
          (p ^ nu : ℝ) ^ s *
            wooleyMixedGridMean s k 1 p B nu nu nu gamma) := by
  let c : ℝ := 2 ^ (s - 1)
  let scale : ℝ := ((((p ^ B) ^ k : ℕ) : ℝ))⁻¹
  have hscale : 0 ≤ scale := by positivity
  have hsum :
      scale *
          ∑ alpha : Fin k → ZMod (p ^ B),
            ‖wooleyWeightedNormalizedGridSum
              (p ^ B) k gamma alpha‖ ^ (2 * s) ≤
        scale *
          ∑ alpha : Fin k → ZMod (p ^ B),
            c *
              ((wooleyWeightedMassSq gamma)⁻¹ *
                  ∑ xi : ZMod (p ^ nu),
                    wooleyWeightedResidueMassSq gamma xi *
                      ‖wooleyWeightedNormalizedResidueGridSum
                        (p ^ B) k gamma alpha xi‖ ^ (2 * s) +
                (wooleyWeightedMassSq gamma)⁻¹ ^ 2 *
                  (p ^ nu : ℝ) ^ s *
                    wooleyInitialMixedForward
                      p B nu k s gamma alpha) := by
    apply mul_le_mul_of_nonneg_left _ hscale
    apply Finset.sum_le_sum
    intro alpha halpha
    exact wooley_equation_6_9_pointwise p B nu k s gamma alpha hs
  unfold wooleyWeightedGridMean
  change scale *
      ∑ alpha : Fin k → ZMod (p ^ B),
        ‖wooleyWeightedNormalizedGridSum
          (p ^ B) k gamma alpha‖ ^ (2 * s) ≤ _
  calc
    scale *
        ∑ alpha : Fin k → ZMod (p ^ B),
          ‖wooleyWeightedNormalizedGridSum
            (p ^ B) k gamma alpha‖ ^ (2 * s) ≤
      scale *
        ∑ alpha : Fin k → ZMod (p ^ B),
          c *
            ((wooleyWeightedMassSq gamma)⁻¹ *
                ∑ xi : ZMod (p ^ nu),
                  wooleyWeightedResidueMassSq gamma xi *
                    ‖wooleyWeightedNormalizedResidueGridSum
                      (p ^ B) k gamma alpha xi‖ ^ (2 * s) +
              (wooleyWeightedMassSq gamma)⁻¹ ^ 2 *
                (p ^ nu : ℝ) ^ s *
                  wooleyInitialMixedForward
                    p B nu k s gamma alpha) := hsum
    _ = c *
        (wooleyWeightedConditionedGridMean
            s k (p ^ B) (p ^ nu) gamma +
          (p ^ nu : ℝ) ^ s *
            wooleyMixedGridMean s k 1 p B nu nu nu gamma) := by
      let A : (Fin k → ZMod (p ^ B)) → ℝ := fun alpha =>
        (wooleyWeightedMassSq gamma)⁻¹ *
          ∑ xi : ZMod (p ^ nu),
            wooleyWeightedResidueMassSq gamma xi *
              ‖wooleyWeightedNormalizedResidueGridSum
                (p ^ B) k gamma alpha xi‖ ^ (2 * s)
      let F : (Fin k → ZMod (p ^ B)) → ℝ := fun alpha =>
        (wooleyWeightedMassSq gamma)⁻¹ ^ 2 *
          wooleyInitialMixedForward p B nu k s gamma alpha
      have hA : scale * ∑ alpha, A alpha =
          wooleyWeightedConditionedGridMean
            s k (p ^ B) (p ^ nu) gamma := by
        exact wooley_initial_diagonal_average p B nu k s gamma
      have hF : scale * ∑ alpha, F alpha =
          wooleyMixedGridMean s k 1 p B nu nu nu gamma := by
        exact wooley_initial_mixed_average p B nu k s gamma
      have hsumF :
          (∑ alpha, (p ^ nu : ℝ) ^ s * F alpha) =
            (p ^ nu : ℝ) ^ s * ∑ alpha, F alpha := by
        rw [Finset.mul_sum]
      have hbody (alpha : Fin k → ZMod (p ^ B)) :
          (wooleyWeightedMassSq gamma)⁻¹ *
                ∑ xi : ZMod (p ^ nu),
                  wooleyWeightedResidueMassSq gamma xi *
                    ‖wooleyWeightedNormalizedResidueGridSum
                      (p ^ B) k gamma alpha xi‖ ^ (2 * s) +
              (wooleyWeightedMassSq gamma)⁻¹ ^ 2 *
                (p ^ nu : ℝ) ^ s *
                  wooleyInitialMixedForward p B nu k s gamma alpha =
            A alpha + (p ^ nu : ℝ) ^ s * F alpha := by
        dsimp [A, F]
        ring
      simp_rw [hbody]
      change scale * ∑ alpha, c *
          (A alpha + (p ^ nu : ℝ) ^ s * F alpha) = _
      rw [← Finset.mul_sum, Finset.sum_add_distrib, hsumF]
      rw [mul_add]
      calc
        scale * (c * (∑ x, A x) +
            c * ((p ^ nu : ℝ) ^ s * ∑ x, F x)) =
            c * (scale * ∑ x, A x) +
              c * ((p ^ nu : ℝ) ^ s * (scale * ∑ x, F x)) := by
          ring
        _ = _ := by rw [hA, hF]; ring
    _ = _ := by rfl

/-- Wooley's choice (6.5), using the natural ceiling convention. -/
def wooleyInitialNu (epsilon Lambda : ℝ) (H : ℕ) : ℕ :=
  ⌈4 * epsilon * (H : ℝ) / Lambda⌉₊

theorem wooley_initialNu_lower
    {epsilon Lambda : ℝ} {H : ℕ} :
    4 * epsilon * (H : ℝ) / Lambda ≤
      (wooleyInitialNu epsilon Lambda H : ℝ) := by
  exact Nat.le_ceil _

/-- The displayed exponent calculation following (6.9).  The natural
subtraction `H - nu` is justified by the source hierarchy `nu ≤ H`. -/
theorem wooley_initial_conditioning_exponent
    {epsilon Lambda : ℝ} {H nu : ℕ}
    (hepsilon : 0 < epsilon) (hLambda : 0 < Lambda)
    (hnuH : nu ≤ H)
    (hnu : 4 * epsilon * (H : ℝ) / Lambda ≤ (nu : ℝ)) :
    (Lambda + epsilon) * ((H - nu : ℕ) : ℝ) -
        (Lambda - epsilon) * (H : ℝ) ≤
      -2 * epsilon * (H : ℝ) := by
  rw [Nat.cast_sub hnuH]
  have hLambdaNu : 4 * epsilon * (H : ℝ) ≤
      Lambda * (nu : ℝ) := by
    rw [div_le_iff₀ hLambda] at hnu
    simpa [mul_assoc, mul_comm] using hnu
  have hnuNonneg : (0 : ℝ) ≤ nu := by positivity
  nlinarith

/-- Equations (6.3) and (6.4), together with the exponent comparison,
give the exact contraction used in Lemma 6.1. -/
theorem wooley_conditioned_mean_le_decay {Q : ℕ}
    (p B nu H k s : ℕ) [NeZero p] [NeZero (p ^ B)] [NeZero (p ^ nu)]
    (gamma : Fin Q → ℂ) {epsilon Lambda : ℝ}
    (hp : 2 ≤ p) (hepsilon : 0 < epsilon) (hLambda : 0 < Lambda)
    (hnuH : nu ≤ H)
    (hnu : 4 * epsilon * (H : ℝ) / Lambda ≤ (nu : ℝ))
    (hlower :
      (p : ℝ) ^ ((H : ℝ) * (Lambda - epsilon)) *
          wooleyWeightedConditionedGridMean
            s k (p ^ B) (p ^ H) gamma ≤
        wooleyWeightedGridMean s k (p ^ B) gamma)
    (hupper :
      wooleyWeightedConditionedGridMean
          s k (p ^ B) (p ^ nu) gamma ≤
        (p : ℝ) ^ (((H - nu : ℕ) : ℝ) * (Lambda + epsilon)) *
          wooleyWeightedConditionedGridMean
            s k (p ^ B) (p ^ H) gamma) :
    wooleyWeightedConditionedGridMean
        s k (p ^ B) (p ^ nu) gamma ≤
      (p : ℝ) ^ (-2 * epsilon * (H : ℝ)) *
        wooleyWeightedGridMean s k (p ^ B) gamma := by
  let VH := wooleyWeightedConditionedGridMean
    s k (p ^ B) (p ^ H) gamma
  have hVH : 0 ≤ VH := by
    unfold VH wooleyWeightedConditionedGridMean
    split_ifs with hmass
    · exact le_rfl
    · apply mul_nonneg
      · exact inv_nonneg.mpr (wooleyWeightedMassSq_nonneg gamma)
      · apply Finset.sum_nonneg
        intro xi hxi
        apply mul_nonneg (wooleyWeightedResidueMassSq_nonneg gamma xi)
        apply mul_nonneg
        · positivity
        · exact Finset.sum_nonneg fun alpha halpha => pow_nonneg (norm_nonneg _) _
  have hpReal : (1 : ℝ) ≤ p := by exact_mod_cast (by omega : 1 ≤ p)
  have hexp := wooley_initial_conditioning_exponent
    hepsilon hLambda hnuH hnu
  have hpow :
      (p : ℝ) ^ (((H - nu : ℕ) : ℝ) * (Lambda + epsilon)) ≤
        (p : ℝ) ^
          ((H : ℝ) * (Lambda - epsilon) +
            (-2 * epsilon * (H : ℝ))) := by
    apply Real.rpow_le_rpow_of_exponent_le hpReal
    nlinarith
  calc
    wooleyWeightedConditionedGridMean
        s k (p ^ B) (p ^ nu) gamma ≤
      (p : ℝ) ^ (((H - nu : ℕ) : ℝ) * (Lambda + epsilon)) * VH :=
        hupper
    _ ≤ (p : ℝ) ^
          ((H : ℝ) * (Lambda - epsilon) +
            (-2 * epsilon * (H : ℝ))) * VH := by
      gcongr
    _ = (p : ℝ) ^ (-2 * epsilon * (H : ℝ)) *
          ((p : ℝ) ^ ((H : ℝ) * (Lambda - epsilon)) * VH) := by
      rw [Real.rpow_add (by positivity : (0 : ℝ) < p)]
      ring
    _ ≤ (p : ℝ) ^ (-2 * epsilon * (H : ℝ)) *
          wooleyWeightedGridMean s k (p ^ B) gamma := by
      gcongr

/-- Quantitative absorption of the contracted copy of `U`. -/
theorem wooley_absorb_contraction
    {U K c a : ℝ} (hU : 0 ≤ U)
    (hmain : U ≤ c * (a * U + K))
    (hsmall : 2 * c * a ≤ 1) :
    U ≤ 2 * c * K := by
  have hca : c * a ≤ (1 : ℝ) / 2 := by nlinarith
  have hcontract : c * a * U ≤ ((1 : ℝ) / 2) * U :=
    mul_le_mul_of_nonneg_right hca hU
  have hmain' : U ≤ c * a * U + c * K := by
    calc
      U ≤ c * (a * U + K) := hmain
      _ = c * a * U + c * K := by ring
  nlinarith

/-- A concrete sufficient-size condition implying the absorption inequality
used after (6.9).  Thus the source phrase "epsilon H sufficiently large"
can be discharged by an ordinary scale comparison. -/
theorem wooley_initial_absorption_of_scale
    {p s H : ℕ} {epsilon : ℝ}
    (hp : 2 ≤ p) (hs : 1 ≤ s)
    (hscale : (s : ℝ) ≤ 2 * epsilon * (H : ℝ)) :
    2 * 2 ^ (s - 1) *
        (p : ℝ) ^ (-2 * epsilon * (H : ℝ)) ≤ 1 := by
  have hx : 0 ≤ 2 * epsilon * (H : ℝ) :=
    le_trans (by positivity : (0 : ℝ) ≤ s) hscale
  have hpReal : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have htwo : (2 : ℝ) * 2 ^ (s - 1) = 2 ^ s := by
    rw [← pow_succ']
    congr
    omega
  have hbound : (2 : ℝ) ^ s ≤
      (p : ℝ) ^ (2 * epsilon * (H : ℝ)) := by
    calc
      (2 : ℝ) ^ s = (2 : ℝ) ^ (s : ℝ) := by
        rw [Real.rpow_natCast]
      _ ≤ (2 : ℝ) ^ (2 * epsilon * (H : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hscale
      _ ≤ (p : ℝ) ^ (2 * epsilon * (H : ℝ)) :=
        Real.rpow_le_rpow (by norm_num) hpReal hx
  have hpPow : 0 < (p : ℝ) ^ (2 * epsilon * (H : ℝ)) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hneg : -2 * epsilon * (H : ℝ) =
      -(2 * epsilon * (H : ℝ)) := by ring
  rw [htwo]
  rw [hneg]
  rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ p),
    ← div_eq_mul_inv, div_le_one hpPow]
  exact hbound

/-- Wooley Lemma 6.1 with every source hypothesis and the sufficiently-large
absorption inequality displayed. -/
theorem wooley_lemma_6_1 {Q : ℕ}
    (p B nu H k s : ℕ) [NeZero p] [NeZero (p ^ B)] [NeZero (p ^ nu)]
    (gamma : Fin Q → ℂ) {epsilon Lambda : ℝ}
    (hp : 2 ≤ p) (hs : 2 ≤ s)
    (hepsilon : 0 < epsilon) (hLambda : 0 < Lambda)
    (hnuH : nu ≤ H)
    (hnu : 4 * epsilon * (H : ℝ) / Lambda ≤ (nu : ℝ))
    (hlower :
      (p : ℝ) ^ ((H : ℝ) * (Lambda - epsilon)) *
          wooleyWeightedConditionedGridMean
            s k (p ^ B) (p ^ H) gamma ≤
        wooleyWeightedGridMean s k (p ^ B) gamma)
    (hupper :
      wooleyWeightedConditionedGridMean
          s k (p ^ B) (p ^ nu) gamma ≤
        (p : ℝ) ^ (((H - nu : ℕ) : ℝ) * (Lambda + epsilon)) *
          wooleyWeightedConditionedGridMean
            s k (p ^ B) (p ^ H) gamma)
    (hlarge :
      2 * 2 ^ (s - 1) *
          (p : ℝ) ^ (-2 * epsilon * (H : ℝ)) ≤ 1) :
    wooleyWeightedGridMean s k (p ^ B) gamma ≤
      (2 * 2 ^ (s - 1)) * (p ^ nu : ℝ) ^ s *
        wooleyMixedGridMean s k 1 p B nu nu nu gamma := by
  have h69 := wooley_equation_6_9 p B nu k s gamma hs
  have hdecay := wooley_conditioned_mean_le_decay
    p B nu H k s gamma hp hepsilon hLambda hnuH hnu hlower hupper
  have hU : 0 ≤ wooleyWeightedGridMean s k (p ^ B) gamma := by
    unfold wooleyWeightedGridMean
    positivity
  have hmain :
      wooleyWeightedGridMean s k (p ^ B) gamma ≤
        2 ^ (s - 1) *
          ((p : ℝ) ^ (-2 * epsilon * (H : ℝ)) *
              wooleyWeightedGridMean s k (p ^ B) gamma +
            (p ^ nu : ℝ) ^ s *
              wooleyMixedGridMean s k 1 p B nu nu nu gamma) := by
    calc
      wooleyWeightedGridMean s k (p ^ B) gamma ≤
        2 ^ (s - 1) *
          (wooleyWeightedConditionedGridMean
              s k (p ^ B) (p ^ nu) gamma +
            (p ^ nu : ℝ) ^ s *
              wooleyMixedGridMean s k 1 p B nu nu nu gamma) := h69
      _ ≤ 2 ^ (s - 1) *
          ((p : ℝ) ^ (-2 * epsilon * (H : ℝ)) *
              wooleyWeightedGridMean s k (p ^ B) gamma +
            (p ^ nu : ℝ) ^ s *
              wooleyMixedGridMean s k 1 p B nu nu nu gamma) := by
        gcongr
  have habs := wooley_absorb_contraction
    (U := wooleyWeightedGridMean s k (p ^ B) gamma)
    (K := (p ^ nu : ℝ) ^ s *
      wooleyMixedGridMean s k 1 p B nu nu nu gamma)
    hU hmain hlarge
  simpa [mul_assoc] using habs

/-- Wooley Lemma 6.3, now discharged from the exact Lemma 6.1 proof and
the residue-refinement estimate rather than an assumed initial bound. -/
theorem wooley_lemma_6_3 {Q : ℕ}
    (p B nu theta H k s : ℕ)
    [NeZero p] [NeZero (p ^ B)] [NeZero (p ^ nu)]
    (gamma : Fin Q → ℂ) {epsilon Lambda : ℝ}
    (hp : 2 ≤ p) (hs : 2 ≤ s)
    (hepsilon : 0 < epsilon) (hLambda : 0 < Lambda)
    (hnuH : nu ≤ H) (hnuTheta : nu ≤ theta)
    (hnu : 4 * epsilon * (H : ℝ) / Lambda ≤ (nu : ℝ))
    (hlower :
      (p : ℝ) ^ ((H : ℝ) * (Lambda - epsilon)) *
          wooleyWeightedConditionedGridMean
            s k (p ^ B) (p ^ H) gamma ≤
        wooleyWeightedGridMean s k (p ^ B) gamma)
    (hupper :
      wooleyWeightedConditionedGridMean
          s k (p ^ B) (p ^ nu) gamma ≤
        (p : ℝ) ^ (((H - nu : ℕ) : ℝ) * (Lambda + epsilon)) *
          wooleyWeightedConditionedGridMean
            s k (p ^ B) (p ^ H) gamma)
    (hlarge :
      2 * 2 ^ (s - 1) *
          (p : ℝ) ^ (-2 * epsilon * (H : ℝ)) ≤ 1) :
    wooleyWeightedGridMean s k (p ^ B) gamma ≤
      (2 * 2 ^ (s - 1)) * (p ^ theta : ℝ) ^ s *
        wooleyMixedGridMean s k 1 p B theta theta nu gamma := by
  have hinitial := wooley_lemma_6_1 p B nu H k s gamma hp hs
    hepsilon hLambda hnuH hnu hlower hupper hlarge
  exact wooley_lemma_6_3_of_initial_conditioning
    (C := 2 * 2 ^ (s - 1)) (by positivity) hnuTheta hs gamma hinitial

#print axioms wooley_critical_interpolation_term
#print axioms wooley_pair_mixed_holder
#print axioms wooleyResiduesSeparated_same_iff_ne
#print axioms wooley_norm_sum_sq_le_diagonal_add_offDiagonal
#print axioms wooley_equation_6_6
#print axioms wooley_equation_6_7
#print axioms wooley_equation_6_8
#print axioms wooley_add_pow_le_two_pow_pred_mul
#print axioms wooley_equation_6_9_pointwise
#print axioms wooley_initial_diagonal_average
#print axioms wooley_initial_mixed_average
#print axioms wooley_equation_6_9
#print axioms wooley_initialNu_lower
#print axioms wooley_initial_conditioning_exponent
#print axioms wooley_conditioned_mean_le_decay
#print axioms wooley_absorb_contraction
#print axioms wooley_initial_absorption_of_scale
#print axioms wooley_lemma_6_1
#print axioms wooley_lemma_6_3

end

end GafniTao

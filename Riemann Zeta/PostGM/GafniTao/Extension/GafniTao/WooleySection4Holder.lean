import GafniTao.WooleySourceMixed
import GafniTao.WooleySection8

/-!
# Wooley equation (4.15)

This file proves the finite Hölder estimate used in Lemma 4.2 directly for
the source's finitely supported integer coefficient sequences.  The
separation condition in `K` is first enlarged to all residue pairs; Hölder
is then applied on the literal finite product of the two residue spaces and
the Fourier grid.  Thus no implicit integral, measure normalization, or
Vinogradov constant is hidden in the statement.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- The pointwise exponent identity in the Hölder step (4.15). -/
theorem wooley_equation_4_15_integrand
    {R s : ℕ} (hs : 1 ≤ s) (hRs : R ≤ s)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x ^ (2 * s)) ^ ((R : ℝ) / (s : ℝ)) *
        (y ^ (2 * s)) ^ (1 - (R : ℝ) / (s : ℝ)) =
      x ^ (2 * R) * y ^ (2 * (s - R)) := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hxid :
      (x ^ (2 * s)) ^ ((R : ℝ) / (s : ℝ)) = x ^ (2 * R) := by
    rw [← Real.rpow_natCast x (2 * s), ← Real.rpow_natCast x (2 * R),
      ← Real.rpow_mul hx]
    congr 1
    push_cast
    field_simp
  have hyid :
      (y ^ (2 * s)) ^ (1 - (R : ℝ) / (s : ℝ)) =
        y ^ (2 * (s - R)) := by
    rw [← Real.rpow_natCast y (2 * s),
      ← Real.rpow_natCast y (2 * (s - R)), ← Real.rpow_mul hy]
    congr 1
    push_cast
    rw [Nat.cast_sub hRs]
    field_simp
  rw [hxid, hyid]

/-- Factor a three-fold finite sum when the final factor is independent of
the middle coordinate. -/
theorem wooley_sum_prod_prod_independent_middle
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (wa : A → ℝ) (wb : B → ℝ) (F : A → C → ℝ) :
    (∑ z : A × B × C, wa z.1 * wb z.2.1 * F z.1 z.2.2) =
      (∑ b, wb b) * (∑ a, wa a * ∑ c, F a c) := by
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro b hb
  ring

/-- Factor a three-fold finite sum when the final factor is independent of
the first coordinate. -/
theorem wooley_sum_prod_prod_independent_first
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (wa : A → ℝ) (wb : B → ℝ) (G : B → C → ℝ) :
    (∑ z : A × B × C, wa z.1 * wb z.2.1 * G z.2.1 z.2.2) =
      (∑ a, wa a) * (∑ b, wb b * ∑ c, G b c) := by
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro a ha
  ring

/-- Wooley equation (4.15), with the separated mixed mean on the left and
the two literal conditioned means on the right. -/
theorem wooleySourcePolynomial_equation_4_15
    {k : ℕ} (phi : WooleyPolynomialSystem k)
    (p B a b nu r : ℕ) [NeZero p] [NeZero (p ^ B)]
    (hk : 1 ≤ k) (hrk : r ≤ k)
    (gamma : WooleySourceSequence) :
    wooleySourcePolynomialMixedMean
        phi (wooleyTriangular k) r p B a b nu gamma ≤
      (wooleySourcePolynomialConditionedMean
          (wooleyTriangular k) (p ^ B) (p ^ a) phi gamma) ^
        (((wooleyTriangular r : ℕ) : ℝ) /
          (wooleyTriangular k : ℕ)) *
      (wooleySourcePolynomialConditionedMean
          (wooleyTriangular k) (p ^ B) (p ^ b) phi gamma) ^
        (1 - ((wooleyTriangular r : ℕ) : ℝ) /
          (wooleyTriangular k : ℕ)) := by
  classical
  let s := wooleyTriangular k
  let R := wooleyTriangular r
  let q := p ^ B
  let M := wooleySourceMassSq gamma
  let I := ZMod (p ^ a) × ZMod (p ^ b) × (Fin k → ZMod q)
  let t : Finset I := Finset.univ
  let w : I → ℝ := fun z =>
    wooleySourceResidueMassSq gamma (p ^ a) z.1 *
      wooleySourceResidueMassSq gamma (p ^ b) z.2.1
  let f : I → ℝ := fun z =>
    ‖wooleySourceNormalizedPolynomialResidueSum
      phi gamma z.2.2 z.1‖ ^ (2 * s)
  let g : I → ℝ := fun z =>
    ‖wooleySourceNormalizedPolynomialResidueSum
      phi gamma z.2.2 z.2.1‖ ^ (2 * s)
  let h : I → ℝ := fun z =>
    ‖wooleySourceNormalizedPolynomialResidueSum
      phi gamma z.2.2 z.1‖ ^ (2 * R) *
    ‖wooleySourceNormalizedPolynomialResidueSum
      phi gamma z.2.2 z.2.1‖ ^ (2 * (s - R))
  let u : ℝ := (R : ℝ) / (s : ℝ)
  by_cases hmass : M = 0
  · have hmass' : wooleySourceMassSq gamma = 0 := by
      simpa only [M] using hmass
    unfold wooleySourcePolynomialMixedMean
      wooleySourcePolynomialConditionedMean
    simp only [hmass', if_pos]
    exact mul_nonneg (Real.rpow_nonneg le_rfl _)
      (Real.rpow_nonneg le_rfl _)
  · have hs : 1 ≤ s := by
      dsimp [s]
      unfold wooleyTriangular
      have hkpos : 0 < k := by omega
      have htwo : 2 ≤ k * (k + 1) := by nlinarith
      omega
    have hRs : R ≤ s := by
      dsimp [R, s]
      exact wooleyTriangular_mono hrk
    have hMpos : 0 < M :=
      lt_of_le_of_ne (wooleySourceMassSq_nonneg gamma) (Ne.symm hmass)
    have hqNat : 0 < q := by
      dsimp [q]
      exact Nat.pos_of_ne_zero (NeZero.ne (p ^ B))
    have hqpos : (0 : ℝ) < ((q ^ k : ℕ) : ℝ) := by
      exact_mod_cast pow_pos hqNat k
    have hcpos : 0 < M⁻¹ ^ 2 * (((q ^ k : ℕ) : ℝ)⁻¹) :=
      mul_pos (sq_pos_of_pos (inv_pos.mpr hMpos)) (inv_pos.mpr hqpos)
    have hu0 : 0 ≤ u := by
      dsimp [u]
      exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hu1 : u ≤ 1 := by
      dsimp [u]
      rw [div_le_one (by exact_mod_cast (show 0 < s by omega))]
      exact_mod_cast hRs
    have hw : ∀ z ∈ t, 0 ≤ w z := by
      intro z hz
      exact mul_nonneg
        (wooleySourceResidueMassSq_nonneg gamma _ z.1)
        (wooleySourceResidueMassSq_nonneg gamma _ z.2.1)
    have hf : ∀ z ∈ t, 0 ≤ f z := by
      intro z hz
      dsimp [f]
      positivity
    have hg : ∀ z ∈ t, 0 ≤ g z := by
      intro z hz
      dsimp [g]
      positivity
    have hpoint : ∀ z ∈ t, h z = f z ^ u * g z ^ (1 - u) := by
      intro z hz
      dsimp [h, f, g, u, R, s]
      symm
      exact wooley_equation_4_15_integrand hs hRs
        (norm_nonneg _) (norm_nonneg _)
    have hholder := wooley_scaled_weighted_two_factor_holder_real
      t w f g h hw hf hg hu0 hu1 hcpos
      (fun z hz => (hpoint z hz).le)
    have hsumA :
        (M⁻¹ ^ 2 * (((q ^ k : ℕ) : ℝ)⁻¹) *
            ∑ z ∈ t, w z * f z) =
          wooleySourcePolynomialConditionedMean
            s q (p ^ a) phi gamma := by
      have htriple := wooley_sum_prod_prod_independent_middle
        (fun xi : ZMod (p ^ a) =>
          wooleySourceResidueMassSq gamma (p ^ a) xi)
        (fun eta : ZMod (p ^ b) =>
          wooleySourceResidueMassSq gamma (p ^ b) eta)
        (fun xi (alpha : Fin k → ZMod q) =>
          ‖wooleySourceNormalizedPolynomialResidueSum
            phi gamma alpha xi‖ ^ (2 * s))
      have hsumMass := wooleySource_sum_residueMassSq gamma (p ^ b)
      simp only [t, I, w, f]
      rw [htriple, hsumMass]
      unfold wooleySourcePolynomialConditionedMean
      rw [if_neg (by simpa only [M] using hmass)]
      simp only [M, q]
      field_simp [hmass]
      simp only [Nat.mul_comm]
      simp_rw [div_eq_mul_inv]
      rw [← Finset.sum_mul]
      ring
    have hsumB :
        (M⁻¹ ^ 2 * (((q ^ k : ℕ) : ℝ)⁻¹) *
            ∑ z ∈ t, w z * g z) =
          wooleySourcePolynomialConditionedMean
            s q (p ^ b) phi gamma := by
      have htriple := wooley_sum_prod_prod_independent_first
        (fun xi : ZMod (p ^ a) =>
          wooleySourceResidueMassSq gamma (p ^ a) xi)
        (fun eta : ZMod (p ^ b) =>
          wooleySourceResidueMassSq gamma (p ^ b) eta)
        (fun eta (alpha : Fin k → ZMod q) =>
          ‖wooleySourceNormalizedPolynomialResidueSum
            phi gamma alpha eta‖ ^ (2 * s))
      have hsumMass := wooleySource_sum_residueMassSq gamma (p ^ a)
      simp only [t, I, w, g]
      rw [htriple, hsumMass]
      unfold wooleySourcePolynomialConditionedMean
      rw [if_neg (by simpa only [M] using hmass)]
      simp only [M, q]
      field_simp [hmass]
      simp only [Nat.mul_comm]
      simp_rw [div_eq_mul_inv]
      rw [← Finset.sum_mul]
      ring
    have hleft :
        wooleySourcePolynomialMixedMean phi s r p B a b nu gamma ≤
          M⁻¹ ^ 2 * (((q ^ k : ℕ) : ℝ)⁻¹) *
            ∑ z ∈ t, w z * h z := by
      unfold wooleySourcePolynomialMixedMean
      rw [if_neg hmass]
      dsimp [M, q, s, R, t, I, w, h,
        wooleySourcePolynomialMixedResidueMoment]
      rw [mul_assoc]
      gcongr
      rw [Fintype.sum_prod_type]
      simp_rw [Fintype.sum_prod_type]
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro xi hxi
      calc
        ∑ eta with wooleyResiduesSeparated nu xi eta,
            wooleySourceResidueMassSq gamma (p ^ a) xi *
              wooleySourceResidueMassSq gamma (p ^ b) eta *
                (((((p ^ B) ^ k : ℕ) : ℝ))⁻¹ *
                  ∑ alpha,
                    ‖wooleySourceNormalizedPolynomialResidueSum
                        phi gamma alpha xi‖ ^ (2 * wooleyTriangular r) *
                      ‖wooleySourceNormalizedPolynomialResidueSum
                        phi gamma alpha eta‖ ^
                          (2 * (wooleyTriangular k - wooleyTriangular r))) ≤
            ∑ eta,
              wooleySourceResidueMassSq gamma (p ^ a) xi *
                wooleySourceResidueMassSq gamma (p ^ b) eta *
                  (((((p ^ B) ^ k : ℕ) : ℝ))⁻¹ *
                    ∑ alpha,
                      ‖wooleySourceNormalizedPolynomialResidueSum
                          phi gamma alpha xi‖ ^ (2 * wooleyTriangular r) *
                        ‖wooleySourceNormalizedPolynomialResidueSum
                          phi gamma alpha eta‖ ^
                            (2 * (wooleyTriangular k - wooleyTriangular r))) := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · exact Finset.filter_subset _ _
              · intro eta heta hnot
                apply mul_nonneg
                · exact mul_nonneg
                    (wooleySourceResidueMassSq_nonneg gamma _ xi)
                    (wooleySourceResidueMassSq_nonneg gamma _ eta)
                · apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
                  exact Finset.sum_nonneg fun alpha halpha =>
                    mul_nonneg (pow_nonneg (norm_nonneg _) _)
                      (pow_nonneg (norm_nonneg _) _)
        _ = _ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro eta heta
          rw [Finset.mul_sum]
          rw [Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro alpha halpha
          ring
    calc
      wooleySourcePolynomialMixedMean phi s r p B a b nu gamma ≤
          M⁻¹ ^ 2 * (((q ^ k : ℕ) : ℝ)⁻¹) *
            ∑ z ∈ t, w z * h z := hleft
      _ ≤
          (M⁻¹ ^ 2 * (((q ^ k : ℕ) : ℝ)⁻¹) *
            ∑ z ∈ t, w z * f z) ^ u *
          (M⁻¹ ^ 2 * (((q ^ k : ℕ) : ℝ)⁻¹) *
            ∑ z ∈ t, w z * g z) ^ (1 - u) := hholder
      _ = _ := by
        rw [hsumA, hsumB]

#print axioms wooley_equation_4_15_integrand
#print axioms wooleySourcePolynomial_equation_4_15

end

end GafniTao

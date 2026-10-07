import Dubon2026.RectangularLatticeMajorant

/-! # Integrability of the actual regularized lattice continuation against cusp forms -/

namespace Dubon2026

open UpperHalfPlane MeasureTheory CongruenceSubgroup Matrix.SpecialLinearGroup

noncomputable section

/-- The regularized lattice kernel at every complex parameter is integrable against the true cusp density. -/
theorem integrableOn_rectangular_lattice_regular_petersson {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (s : ℂ) :
    IntegrableOn (fun z : ℍ =>
      latticeCompletedMellinRegular (rectangularLatticePoint a b ha hb z) s * petersson k f f z)
      (gamma0FundamentalDomain Q) := by
  let σ : ℝ := |s.re| + 2
  have hσ : 1 < σ := by dsimp [σ]; linarith [abs_nonneg s.re]
  have hs : s.re ≤ σ := by dsimp [σ]; linarith [le_abs_self s.re]
  have hs' : 1 - s.re ≤ σ := by dsimp [σ]; linarith [neg_le_abs s.re]
  have hm := ((measurable_latticeCompletedMellinRegular s).comp
    (continuous_rectangularLatticePoint a b ha hb).measurable).mul
      (petersson_continuous k (ModularFormClass.continuous f) (ModularFormClass.continuous f)).measurable
  apply ((integrableOn_norm_rectangular_lattice_petersson f a b ha hb hσ).const_mul 2).mono'
    hm.aestronglyMeasurable.restrict
  apply ae_of_all
  intro z
  rw [norm_mul, ← mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact (norm_latticeCompletedMellinRegular_le _ hσ hs hs').trans
    (mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (by norm_num))

/-- At every fixed parameter the actual meromorphic lattice kernel is integrable against the true cusp density. -/
theorem integrableOn_rectangular_lattice_completed_petersson {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (s : ℂ) :
    IntegrableOn (fun z : ℍ =>
      latticeCompletedMellin (rectangularLatticePoint a b ha hb z) s * petersson k f f z)
      (gamma0FundamentalDomain Q) := by
  have hR := integrableOn_rectangular_lattice_regular_petersson f a b ha hb s
  have hP := integrableOn_petersson_gamma0Domain Q f f
  apply ((hR.sub (hP.const_mul (1 / (2 * s)))).add
    (hP.const_mul (1 / (2 * (s - 1))))).congr
  apply ae_of_all
  intro z
  dsimp only [Pi.add_apply, Pi.sub_apply]
  rw [latticeCompletedMellin_eq_regular]
  ring

/-- The literal regularized lattice-cusp integral, using the actual Gamma0 fundamental domain. -/
def rectangularLatticeCuspRegular {Q : ℕ} {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (s : ℂ) : ℂ :=
  ∫ z : ℍ in gamma0FundamentalDomain Q,
    latticeCompletedMellinRegular (rectangularLatticePoint a b ha hb z) s * petersson k f f z

/-- Integrating the exact lattice polar splitting gives the true Petersson pairing as both pole coefficients. -/
theorem rectangular_lattice_cusp_integral_eq_regular {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (s : ℂ) :
    (∫ z : ℍ in gamma0FundamentalDomain Q,
      latticeCompletedMellin (rectangularLatticePoint a b ha hb z) s * petersson k f f z) =
        rectangularLatticeCuspRegular f a b ha hb s - (1 / (2 * s)) * cuspPetersson f f +
          (1 / (2 * (s - 1))) * cuspPetersson f f := by
  have hR := integrableOn_rectangular_lattice_regular_petersson f a b ha hb s
  have hP := integrableOn_petersson_gamma0Domain Q f f
  have he : (fun z : ℍ =>
      latticeCompletedMellin (rectangularLatticePoint a b ha hb z) s * petersson k f f z) =
      (fun z : ℍ =>
        (latticeCompletedMellinRegular (rectangularLatticePoint a b ha hb z) s * petersson k f f z -
          (1 / (2 * s)) * petersson k f f z) + (1 / (2 * (s - 1))) * petersson k f f z) := by
    funext z
    rw [latticeCompletedMellin_eq_regular]
    ring
  have hsub : IntegrableOn (fun z : ℍ =>
      latticeCompletedMellinRegular (rectangularLatticePoint a b ha hb z) s * petersson k f f z -
        (1 / (2 * s)) * petersson k f f z) (gamma0FundamentalDomain Q) :=
    hR.sub (hP.const_mul _)
  rw [he, integral_add hsub (hP.const_mul _),
    integral_sub hR (hP.const_mul _), integral_const_mul, integral_const_mul,
    ← cuspPetersson_eq_gamma0Domain_integral Q]
  rfl

end
end Dubon2026

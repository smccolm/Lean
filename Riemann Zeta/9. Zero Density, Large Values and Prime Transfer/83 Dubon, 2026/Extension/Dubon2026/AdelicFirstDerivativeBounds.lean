import Dubon2026.RealLiftJetBounds
import Dubon2026.AdelicOrbitDerivatives

/-! # Uniform original adelic derivative and orbit-increment bounds -/

namespace Dubon2026

noncomputable section
open UpperHalfPlane Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

/-- The actual holomorphic derivative selected by any full adelic point has a uniform bound from the original cusp form. -/
theorem canonicalAdelicHolomorphicDerivative_bounded (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : RationalAdelicGL2,
      ‖canonicalAdelicHolomorphicDerivative N k f g‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := realWeightLift_slash_jets_bounded f
  refine ⟨2 * C, by positivity, fun g => ?_⟩
  have hi := hC 1 (canonicalAdelicRealBase N g)
  simpa [canonicalAdelicHolomorphicDerivative, div_eq_mul_inv, mul_comm] using hi

/-- Both actual first derivative expressions are bounded uniformly over the original full adelic group. -/
theorem canonicalAdelicGL2CuspLift_first_derivatives_bounded (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : RationalAdelicGL2,
      ‖canonicalAdelicHolomorphicDerivative N k f g‖ ≤ C ∧
      ‖(k : ℂ) / 2 * canonicalAdelicGL2CuspLift N k f g +
        Complex.I * canonicalAdelicHolomorphicDerivative N k f g‖ ≤ C := by
  obtain ⟨A, hA0, hA⟩ := canonicalAdelicGL2CuspLift_bounded N f
  obtain ⟨B, hB0, hB⟩ := canonicalAdelicHolomorphicDerivative_bounded N f
  refine ⟨‖(k : ℂ) / 2‖ * A + B, by positivity, fun g => ⟨?_, ?_⟩⟩
  · exact (hB g).trans (le_add_of_nonneg_left (mul_nonneg (norm_nonneg _) hA0))
  · calc
      _ ≤ ‖(k : ℂ) / 2 * canonicalAdelicGL2CuspLift N k f g‖ +
          ‖Complex.I * canonicalAdelicHolomorphicDerivative N k f g‖ := norm_add_le _ _
      _ = ‖(k : ℂ) / 2‖ * ‖canonicalAdelicGL2CuspLift N k f g‖ +
          ‖canonicalAdelicHolomorphicDerivative N k f g‖ := by
        rw [norm_mul, norm_mul, Complex.norm_I, one_mul]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (hA g) (norm_nonneg _)) (hB g)

/-- The original unipotent and geodesic orbits have a common Lipschitz bound, uniform in the actual adelic point and both real parameters. -/
theorem canonicalAdelicGL2CuspLift_real_orbits_lipschitz (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : RationalAdelicGL2, ∀ s t : ℝ,
      ‖canonicalAdelicGL2CuspLift N k f (g * adelicRealSL2Embedding (realUpperUnipotent s)) -
        canonicalAdelicGL2CuspLift N k f (g * adelicRealSL2Embedding (realUpperUnipotent t))‖ ≤
          C * |s - t| ∧
      ‖canonicalAdelicGL2CuspLift N k f (g * adelicRealSL2Embedding (realGeodesicCurve s)) -
        canonicalAdelicGL2CuspLift N k f (g * adelicRealSL2Embedding (realGeodesicCurve t))‖ ≤
          C * |s - t| := by
  obtain ⟨C, hC0, hC⟩ := canonicalAdelicGL2CuspLift_first_derivatives_bounded N f
  refine ⟨C, hC0, fun g s t => ⟨?_, ?_⟩⟩
  · have hd := fun u => canonicalAdelicGL2CuspLift_unipotent_hasDerivAt_all N f g u
    have hb (u : ℝ) : ‖deriv (fun v : ℝ => canonicalAdelicGL2CuspLift N k f
        (g * adelicRealSL2Embedding (realUpperUnipotent v))) u‖ ≤ C := by
      rw [(hd u).deriv]
      exact (hC _).1
    simpa only [Real.norm_eq_abs] using
      Convex.norm_image_sub_le_of_norm_deriv_le
        (fun u (_ : u ∈ Set.univ) => (hd u).differentiableAt)
        (fun u (_ : u ∈ Set.univ) => hb u) convex_univ (Set.mem_univ t) (Set.mem_univ s)
  · have hd := fun u => canonicalAdelicGL2CuspLift_geodesic_hasDerivAt_all N f g u
    have hb (u : ℝ) : ‖deriv (fun v : ℝ => canonicalAdelicGL2CuspLift N k f
        (g * adelicRealSL2Embedding (realGeodesicCurve v))) u‖ ≤ C := by
      rw [(hd u).deriv]
      exact (hC _).2
    simpa only [Real.norm_eq_abs] using
      Convex.norm_image_sub_le_of_norm_deriv_le
        (fun u (_ : u ∈ Set.univ) => (hd u).differentiableAt)
        (fun u (_ : u ∈ Set.univ) => hb u) convex_univ (Set.mem_univ t) (Set.mem_univ s)

end
end Dubon2026

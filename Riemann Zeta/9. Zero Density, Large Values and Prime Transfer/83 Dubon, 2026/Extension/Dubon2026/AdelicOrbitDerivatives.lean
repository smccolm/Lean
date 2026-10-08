import Dubon2026.AdelicLiftCasimir

/-! # Exact original one-parameter derivatives at every real parameter -/

namespace Dubon2026

noncomputable section
open UpperHalfPlane Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

/-- An actual one-parameter group law transports a proved derivative at zero to every original orbit parameter. -/
theorem hasDerivAt_oneParameter_orbit {G : Type*} [Group G]
    (c : ℝ → G) (hc : ∀ s t, c (s + t) = c s * c t)
    (F D : G → ℂ) (hD : ∀ g, HasDerivAt (fun t : ℝ => F (g * c t)) (D g) 0)
    (g : G) (t : ℝ) :
    HasDerivAt (fun u : ℝ => F (g * c u)) (D (g * c t)) t := by
  have hd := (hD (g * c t)).scomp_of_eq t ((hasDerivAt_id t).sub_const t) (by simp)
  have he : (fun u : ℝ => F ((g * c t) * c (u - t))) = fun u => F (g * c u) := by
    funext u
    rw [mul_assoc, ← hc, show t + (u - t) = u by ring]
  simpa only [Function.comp_def, id_eq, he, one_smul] using hd

/-- The actual original adelic unipotent orbit has the derivative selected by its genuine translated base at every parameter. -/
theorem canonicalAdelicGL2CuspLift_unipotent_hasDerivAt_all (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (g : RationalAdelicGL2) (t : ℝ) :
    HasDerivAt (fun u : ℝ => canonicalAdelicGL2CuspLift N k f
      (g * adelicRealSL2Embedding (realUpperUnipotent u)))
      (canonicalAdelicHolomorphicDerivative N k f
        (g * adelicRealSL2Embedding (realUpperUnipotent t))) t := by
  apply hasDerivAt_oneParameter_orbit
    (fun u => adelicRealSL2Embedding (realUpperUnipotent u))
    (fun s u => by dsimp only; rw [realUpperUnipotent_add, map_mul])
    (canonicalAdelicGL2CuspLift N k f) (canonicalAdelicHolomorphicDerivative N k f)
  exact canonicalAdelicGL2CuspLift_unipotent_hasDerivAt N f

/-- Every parameter of the original adelic geodesic orbit has the exact original weight and holomorphic derivative terms. -/
theorem canonicalAdelicGL2CuspLift_geodesic_hasDerivAt_all (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (g : RationalAdelicGL2) (t : ℝ) :
    HasDerivAt (fun u : ℝ => canonicalAdelicGL2CuspLift N k f
      (g * adelicRealSL2Embedding (realGeodesicCurve u)))
      ((k : ℂ) / 2 * canonicalAdelicGL2CuspLift N k f
        (g * adelicRealSL2Embedding (realGeodesicCurve t)) +
        Complex.I * canonicalAdelicHolomorphicDerivative N k f
          (g * adelicRealSL2Embedding (realGeodesicCurve t))) t := by
  apply hasDerivAt_oneParameter_orbit
    (fun u => adelicRealSL2Embedding (realGeodesicCurve u))
    (fun s u => by dsimp only; rw [realGeodesicCurve_add, map_mul])
    (canonicalAdelicGL2CuspLift N k f)
    (fun h => (k : ℂ) / 2 * canonicalAdelicGL2CuspLift N k f h +
      Complex.I * canonicalAdelicHolomorphicDerivative N k f h)
  exact canonicalAdelicGL2CuspLift_geodesic_hasDerivAt N f

end
end Dubon2026

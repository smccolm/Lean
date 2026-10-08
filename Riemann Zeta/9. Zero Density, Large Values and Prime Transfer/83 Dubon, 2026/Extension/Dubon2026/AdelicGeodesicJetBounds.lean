import Dubon2026.WeightedExponentialJets

/-! # Every genuine original adelic geodesic derivative and its uniform bound -/

namespace Dubon2026

noncomputable section
open UpperHalfPlane Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups ModularForm

/-- The actual full adelic geodesic orbit is the original weighted holomorphic curve at its genuine real base. -/
theorem canonicalAdelicGL2CuspLift_geodesic_weighted (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (g : RationalAdelicGL2) :
    (fun t : ℝ => canonicalAdelicGL2CuspLift N k f
      (g * adelicRealSL2Embedding (realGeodesicCurve t))) =
      holomorphicWeightedExponential ((k : ℝ) / 2)
        (((f : ℍ → ℂ) ∣[k] (mapGL ℝ (canonicalAdelicRealBase N g))) ∘ ofComplex) := by
  funext t
  rw [canonicalAdelicGL2CuspLift_real_orbit, realWeightLift_right_geodesic_formula]
  simp only [holomorphicWeightedExponential, mul_comm]

/-- Every successive original adelic geodesic jet has its actual real derivative at every parameter. -/
theorem canonicalAdelicGL2CuspLift_geodesic_jet_hasDerivAt (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (g : RationalAdelicGL2) (n : ℕ) (t : ℝ) :
    HasDerivAt (iteratedDeriv n (fun u : ℝ => canonicalAdelicGL2CuspLift N k f
      (g * adelicRealSL2Embedding (realGeodesicCurve u))))
      (iteratedDeriv (n + 1) (fun u : ℝ => canonicalAdelicGL2CuspLift N k f
        (g * adelicRealSL2Embedding (realGeodesicCurve u))) t) t := by
  rw [canonicalAdelicGL2CuspLift_geodesic_weighted]
  exact holomorphicWeightedExponential_jet_hasDerivAt ((k : ℝ) / 2)
    (UpperHalfPlane.mdifferentiable_iff.mp
      ((ModularFormClass.holo f).slash k (mapGL ℝ (canonicalAdelicRealBase N g)))) n t

/-- The original adelic geodesic orbit has a proved uniform bound for every derivative order over all adelic points and all real parameters. -/
theorem canonicalAdelicGL2CuspLift_geodesic_jets_bounded (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    ∃ B : ℕ → ℝ, (∀ n, 0 ≤ B n) ∧ ∀ n : ℕ, ∀ g : RationalAdelicGL2, ∀ t : ℝ,
      ‖iteratedDeriv n (fun u : ℝ => canonicalAdelicGL2CuspLift N k f
        (g * adelicRealSL2Embedding (realGeodesicCurve u))) t‖ ≤ B n := by
  obtain ⟨C, hC0, hC⟩ := realWeightLift_slash_jets_bounded f
  let J : ℕ → ℝ := fun m => (m.factorial : ℝ) * C / (1 / 2 : ℝ) ^ m
  have hJ (m : ℕ) : 0 ≤ J m := by dsimp [J]; positivity
  refine ⟨fun n => holomorphicEulerJetBound (((k : ℝ) / 2 : ℝ) : ℂ) J n 0,
    fun n => holomorphicEulerJetBound_nonneg _ J hJ n 0, fun n g t => ?_⟩
  rw [oneParameter_iteratedDeriv_shift
    (fun u => adelicRealSL2Embedding (realGeodesicCurve u))
    (fun s u => by dsimp only; rw [realGeodesicCurve_add, map_mul])]
  rw [canonicalAdelicGL2CuspLift_geodesic_weighted]
  have hF := UpperHalfPlane.mdifferentiable_iff.mp
    ((ModularFormClass.holo f).slash k (mapGL ℝ (canonicalAdelicRealBase N
      (g * adelicRealSL2Embedding (realGeodesicCurve t)))))
  rw [holomorphicWeightedExponential_iteratedDeriv_zero _ hF]
  simpa only [iteratedDeriv_zero] using
    holomorphicEulerIterate_jet_bound (((k : ℝ) / 2 : ℝ) : ℂ) hF J
      (fun m => hC m _) n 0

end
end Dubon2026

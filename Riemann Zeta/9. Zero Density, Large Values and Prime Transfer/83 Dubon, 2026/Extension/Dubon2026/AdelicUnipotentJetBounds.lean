import Dubon2026.HolomorphicCurveJets
import Dubon2026.RealLiftJetBounds
import Dubon2026.AdelicOrbitDerivatives
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! # All original unipotent orbit derivatives and their uniform bounds -/

namespace Dubon2026

noncomputable section
open UpperHalfPlane Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold

/-- Every actual holomorphic derivative remains holomorphic on the original upper half-plane. -/
theorem holomorphic_iteratedDeriv_upper {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F upperHalfPlaneSet) (n : ℕ) :
    DifferentiableOn ℂ (iteratedDeriv n F) upperHalfPlaneSet := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using hF
  | succ n ih => simpa only [iteratedDeriv_succ] using ih.deriv isOpen_upperHalfPlaneSet

/-- The actual horizontal restriction retains every original complex derivative, at every real parameter. -/
theorem holomorphic_horizontal_iteratedDeriv {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F upperHalfPlaneSet) (n : ℕ) :
    iteratedDeriv n (fun t : ℝ => F ((t : ℂ) + Complex.I)) =
      fun t : ℝ => iteratedDeriv n F ((t : ℂ) + Complex.I) := by
  induction n with
  | zero => simp only [iteratedDeriv_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    simpa only [iteratedDeriv_succ] using
      (holomorphic_horizontal_hasDerivAt (holomorphic_iteratedDeriv_upper hF n) t).deriv

/-- Every original real unipotent orbit jet is the literal original holomorphic slash jet. -/
theorem realWeightLift_unipotent_iteratedDeriv (k : ℤ) {f : ℍ → ℂ}
    (hf : MDiff f) (g : SL(2, ℝ)) (n : ℕ) :
    iteratedDeriv n (fun t : ℝ => realWeightLift k f (g * realUpperUnipotent t)) 0 =
      iteratedDeriv n ((f ∣[k] (mapGL ℝ g)) ∘ ofComplex) Complex.I := by
  simp_rw [realWeightLift_right_unipotent_formula]
  rw [holomorphic_horizontal_iteratedDeriv
    (UpperHalfPlane.mdifferentiable_iff.mp (hf.slash k (mapGL ℝ g)))]
  simp

/-- One-parameter translation identifies every actual orbit jet with the original zero-parameter jet at the translated point. -/
theorem oneParameter_iteratedDeriv_shift {G : Type*} [Group G]
    (c : ℝ → G) (hc : ∀ s t, c (s + t) = c s * c t)
    (F : G → ℂ) (g : G) (n : ℕ) (t : ℝ) :
    iteratedDeriv n (fun u : ℝ => F (g * c u)) t =
      iteratedDeriv n (fun u : ℝ => F ((g * c t) * c u)) 0 := by
  simp_rw [mul_assoc, ← hc]
  simpa only [add_zero] using
    (congrFun (iteratedDeriv_comp_const_add n (fun u : ℝ => F (g * c u)) t) 0).symm

/-- The original full adelic unipotent orbit has successive genuine derivatives of every order. -/
theorem canonicalAdelicGL2CuspLift_unipotent_jet_hasDerivAt (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (g : RationalAdelicGL2) (n : ℕ) (t : ℝ) :
    HasDerivAt (iteratedDeriv n (fun u : ℝ => canonicalAdelicGL2CuspLift N k f
      (g * adelicRealSL2Embedding (realUpperUnipotent u))))
      (iteratedDeriv (n + 1) (fun u : ℝ => canonicalAdelicGL2CuspLift N k f
        (g * adelicRealSL2Embedding (realUpperUnipotent u))) t) t := by
  simp_rw [canonicalAdelicGL2CuspLift_real_orbit, realWeightLift_right_unipotent_formula]
  have hF := UpperHalfPlane.mdifferentiable_iff.mp
    ((ModularFormClass.holo f).slash k (mapGL ℝ (canonicalAdelicRealBase N g)))
  rw [holomorphic_horizontal_iteratedDeriv hF n,
    holomorphic_horizontal_iteratedDeriv hF (n + 1)]
  simpa only [iteratedDeriv_succ] using
    holomorphic_horizontal_hasDerivAt (holomorphic_iteratedDeriv_upper hF n) t

/-- The original full adelic unipotent orbit has uniformly bounded jets of every order, with the genuine Cauchy factorial and radius. -/
theorem canonicalAdelicGL2CuspLift_unipotent_jets_bounded (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ g : RationalAdelicGL2, ∀ t : ℝ,
      ‖iteratedDeriv n (fun u : ℝ => canonicalAdelicGL2CuspLift N k f
        (g * adelicRealSL2Embedding (realUpperUnipotent u))) t‖ ≤
        (n.factorial : ℝ) * C / (1 / 2 : ℝ) ^ n := by
  obtain ⟨C, hC0, hC⟩ := realWeightLift_slash_jets_bounded f
  refine ⟨C, hC0, fun n g t => ?_⟩
  rw [oneParameter_iteratedDeriv_shift
    (fun u => adelicRealSL2Embedding (realUpperUnipotent u))
    (fun s u => by dsimp only; rw [realUpperUnipotent_add, map_mul])]
  simp_rw [canonicalAdelicGL2CuspLift_real_orbit]
  rw [realWeightLift_unipotent_iteratedDeriv k (ModularFormClass.holo f)]
  exact hC n _

end
end Dubon2026

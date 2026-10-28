import Dubon2026.SourceParabolicIntegralCoordinateSpan
import Dubon2026.SourceOriginalBinaryCuspWitnesses

/-! DUB17/18 -> original all-weight association -> original integral
parabolic Hecke character. The original period cocycle is reconstructed
from finitely many actual rational coordinates. Their whole-cusp witnesses
give integral parabolic denominators. Reconstruction helpers are reused
verbatim from the already checked local rational-span proof. -/
namespace Dubon2026
noncomputable section
open MvPolynomial Matrix.SpecialLinearGroup CongruenceSubgroup groupCohomology
open scoped MatrixGroups

private theorem cocycle_ext_generators {G : Type} [Group G] (A : Rep ℂ G)
    (c d : groupCohomology.cocycles₁ A) (s : Set G) (hs : Subgroup.closure s = ⊤)
    (h : ∀ g ∈ s, c g = d g) : c = d := by
  let z := c - d
  have hz (g : G) (hg : g ∈ Subgroup.closure s) : z g = 0 := by
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      change c g - d g = 0
      exact sub_eq_zero.mpr (h g hg)
    | one => exact groupCohomology.cocycles₁_map_one z
    | mul g t _ _ hg ht =>
      rw [(groupCohomology.mem_cocycles₁_iff z).mp z.property, hg, ht, map_zero, add_zero]
    | inv g _ hg =>
      have hi := congrArg (A.ρ g⁻¹) (groupCohomology.cocycles₁_map_inv z g)
      simpa only [hg, neg_zero, map_zero, ← Module.End.mul_apply,
        ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] using hi
  apply groupCohomology.cocycles₁_ext
  intro g
  exact sub_eq_zero.mp (hz g (by rw [hs]; trivial))

private theorem coordinate_sum {I : Finset (Module.Basis.ofVectorSpaceIndex ℚ ℂ)}
    (z : ℂ) (hI : ((Module.Basis.ofVectorSpace ℚ ℂ).repr z).support ⊆ I) :
    ∑ i ∈ I, (Module.Basis.ofVectorSpace ℚ ℂ) i *
      algebraMap ℚ ℂ ((Module.Basis.ofVectorSpace ℚ ℂ).repr z i) = z := by
  classical
  let b := Module.Basis.ofVectorSpace ℚ ℂ
  calc
    _ = ∑ i ∈ I, b.repr z i • b i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Algebra.smul_def, mul_comm]
    _ = (b.repr z).sum (fun i q => q • b i) := by
      apply (Finset.sum_subset hI ?_).symm
      intro i _ hi
      rw [Finsupp.notMem_support_iff.mp hi, zero_smul]
    _ = z := b.linearCombination_repr z

private def coefficientEval (Q w : ℕ) (g : Gamma0 Q) (m : Fin 2 →₀ ℕ) :
    groupCohomology.cocycles₁ (sourceBinaryCoefficientRep ℂ Q w) →ₗ[ℂ] ℂ where
  toFun c := coeff m (c g).val
  map_add' c d := coeff_add m (c g).val (d g).val
  map_smul' a c := coeff_smul m a (c g).val

theorem sourceComplexCuspBinaryCocycle_mem_integralParabolic_span
    (Q w : ℕ) [NeZero Q]
    (c : cocycles₁ (sourceBinaryCoefficientRep ℂ Q w))
    (hc : ∀ β : OnePoint ℚ, ∃ v : sourceBinaryCoefficientRep ℂ Q w,
      ∀ γ : Gamma0 Q, mapGL ℚ γ.val • β = β →
        c γ = (sourceBinaryCoefficientRep ℂ Q w).ρ γ v - v) :
    c ∈ Submodule.span ℂ (sourceBinaryCocyclesChange (Int.castRingHom ℂ) Q w ''
      (sourceParabolicCocycles (Gamma0 Q) (sourceBinaryCoefficientRep ℤ Q w) :
        Set (cocycles₁ (sourceBinaryCoefficientRep ℤ Q w)))) := by
  classical
  letI : Group.FG SL(2, ℤ) :=
    Group.fg_iff.mpr ⟨{ModularGroup.S, ModularGroup.T},
      SpecialLinearGroup.SL2Z_generators, Set.toFinite _⟩
  obtain ⟨s, hs⟩ := (inferInstance : Group.FG (Gamma0 Q)).out
  let b := Module.Basis.ofVectorSpace ℚ ℂ
  let I : Finset (Module.Basis.ofVectorSpaceIndex ℚ ℂ) := s.biUnion fun g =>
    (c g).val.support.biUnion fun m => (b.repr (coeff m (c g).val)).support
  let y (i : Module.Basis.ofVectorSpaceIndex ℚ ℂ) :=
    sourceBinaryCocyclesChange (algebraMap ℚ ℂ) Q w
      (sourceComplexBinaryCocycleCoordinate Q w i c)
  have heq : c = ∑ i ∈ I, b i • y i := by
    apply cocycle_ext_generators _ c _ s hs
    intro g hg
    apply Subtype.ext
    ext m
    change coefficientEval Q w g m c = coefficientEval Q w g m (∑ i ∈ I, b i • y i)
    rw [map_sum]
    simp only [map_smul]
    change coeff m (c g).val = ∑ i ∈ I, b i * coeff m (y i g).val
    have hy (i : Module.Basis.ofVectorSpaceIndex ℚ ℂ) :
        coeff m (y i g).val = algebraMap ℚ ℂ (b.repr (coeff m (c g).val) i) := by
      rw [sourceBinaryCocyclesChange_apply, coeff_map,
        sourceComplexBinaryCocycleCoordinate_coeff]
    simp only [hy]
    apply (coordinate_sum _ ?_).symm
    intro i hi
    have hm : coeff m (c g).val ≠ 0 := by
      intro hz
      simp only [hz, map_zero, Finsupp.support_zero, Finset.notMem_empty] at hi
    exact Finset.mem_biUnion.mpr ⟨g, hg, Finset.mem_biUnion.mpr
      ⟨m, mem_support_iff.mpr hm, hi⟩⟩
  rw [heq]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (sourceRationalCuspBinaryCocycle_mem_integralParabolic_span Q w _
      (sourceBinaryAdditiveCocycles_cusp_witnesses (sourceComplexRationalCoordinate i) Q w c hc))

theorem sourceOriginalBinaryPeriodCocycle_mem_integralParabolic_span
    (Q : ℕ) [NeZero Q] (k : ℤ) (hk : 2 ≤ k)
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) :
    sourceOriginalBinaryPeriodCocycle Q k hk f ∈
      Submodule.span ℂ (sourceBinaryCocyclesChange (Int.castRingHom ℂ) Q (k - 2).toNat ''
        (sourceParabolicCocycles (Gamma0 Q) (sourceBinaryCoefficientRep ℤ Q (k - 2).toNat) :
          Set (cocycles₁ (sourceBinaryCoefficientRep ℤ Q (k - 2).toNat)))) :=
  sourceComplexCuspBinaryCocycle_mem_integralParabolic_span Q (k - 2).toNat _
    (sourceOriginalBinaryPeriodCocycle_cusp_witnesses Q k hk f)

end
end Dubon2026

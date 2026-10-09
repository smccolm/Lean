import Dubon2026.FiniteAdelicLocalTopology
import Dubon2026.FiniteAdelicLocalIntegral
import Dubon2026.AdelicHilbertCentralLevel
import Dubon2026.AdelicRealFiniteCommute

/-! # Genuine local actions and spherical vectors in the original adelic cusp representation -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- Restriction of the original full adelic Hilbert action along the actual local-place embedding. -/
def adelicCyclicLocalRepresentation (v : HeightOneSpectrum ℤ) :
    Representation ℂ (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) (AdelicCyclicHilbert f) :=
  (adelicCyclicHilbertRepresentation f).comp
    (rationalAdelicFiniteGL2Embedding.comp (finiteAdelicLocalGL2Hom v))

/-- The local action is exactly the original full adelic action of the actual local matrix insertion. -/
theorem adelicCyclicLocalRepresentation_apply (v : HeightOneSpectrum ℤ)
    (g : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) (x : AdelicCyclicHilbert f) :
    adelicCyclicLocalRepresentation f v g x = adelicCyclicHilbertRepresentation f
      (rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 v g)) x := rfl

/-- Every genuine restricted local action is strongly continuous in the original Hilbert topology. -/
theorem adelicCyclicLocalRepresentation_stronglyContinuous (v : HeightOneSpectrum ℤ)
    (x : AdelicCyclicHilbert f) : Continuous (fun g => adelicCyclicLocalRepresentation f v g x) := by
  exact (adelicCyclicHilbertRepresentation_stronglyContinuous f x).comp
    (rationalAdelicGL2RealFiniteEquiv_symm_continuous.comp
      (continuous_const.prodMk (finiteAdelicLocalGL2_continuous v)))

/-- Restriction retains the original genuine unitary inner product at every finite place. -/
theorem adelicCyclicLocalRepresentation_inner (v : HeightOneSpectrum ℤ)
    (g : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) (x y : AdelicCyclicHilbert f) :
    inner ℂ (adelicCyclicLocalRepresentation f v g x) (adelicCyclicLocalRepresentation f v g y) =
      inner ℂ x y := adelicCyclicHilbertRepresentation_inner f _ x y

/-- The actual full adelic cusp generator is fixed by the original integral local GL2 group at every place away from its level. -/
theorem adelicCyclicLocal_generator_integral_fixed (v : HeightOneSpectrum ℤ)
    (hN : (N : ℤ) ∉ v.asIdeal) (g : GeneralLinearGroup (Fin 2) (v.adicCompletionIntegers ℚ)) :
    adelicCyclicLocalRepresentation f v (GeneralLinearGroup.map (v.adicCompletionIntegers ℚ).subtype g)
      (adelicCyclicHilbertGenerator f) = adelicCyclicHilbertGenerator f :=
  adelicCyclicHilbertGenerator_finite_level f ⟨_, finiteAdelicLocalIntegral_mem_level N v hN g⟩

/-- Every nonzero original cusp form supplies a genuine nonzero spherical vector for each local action away from its original level. -/
theorem adelicCyclicLocal_has_spherical_vector (hf : f ≠ 0) (v : HeightOneSpectrum ℤ)
    (hN : (N : ℤ) ∉ v.asIdeal) :
    ∃ x : AdelicCyclicHilbert f, x ≠ 0 ∧
      ∀ g : GeneralLinearGroup (Fin 2) (v.adicCompletionIntegers ℚ),
        adelicCyclicLocalRepresentation f v (GeneralLinearGroup.map (v.adicCompletionIntegers ℚ).subtype g) x = x :=
  ⟨adelicCyclicHilbertGenerator f, adelicCyclicHilbertGenerator_ne_zero f hf,
    adelicCyclicLocal_generator_integral_fixed f v hN⟩

/-- Distinct genuine local-place actions commute on the original full adelic Hilbert space. -/
theorem adelicCyclicLocalRepresentation_commute (v w : HeightOneSpectrum ℤ) (hne : v ≠ w)
    (g : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (h : GeneralLinearGroup (Fin 2) (w.adicCompletion ℚ)) (x : AdelicCyclicHilbert f) :
    adelicCyclicLocalRepresentation f v g (adelicCyclicLocalRepresentation f w h x) =
      adelicCyclicLocalRepresentation f w h (adelicCyclicLocalRepresentation f v g x) := by
  have he := ((finiteAdelicLocalGL2_commute v w hne g h).map rationalAdelicFiniteGL2Embedding).map
    (adelicCyclicHilbertRepresentation f)
  exact LinearMap.congr_fun he.eq x

end
end Dubon2026

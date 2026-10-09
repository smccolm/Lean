import Dubon2026.AdelicLocalFullAwayTensorRange
import Dubon2026.AdelicLocalAwayTensorAction
import Dubon2026.AdelicLocalFullAwayProduct
import Dubon2026.AdelicLocalSmoothRepresentation

/-! # Genuine product actions and equivariance of the original local/full-complement tensor map -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups TensorProduct

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- Every genuine real-plus-away action preserves the original algebraic real-plus-away orbit core. -/
theorem adelicFullAwayCyclicCore_invariant (v : HeightOneSpectrum ℤ) (a : AdelicFullAwayGroup v)
    (x : AdelicCyclicHilbert f) (hx : x ∈ adelicFullAwayCyclicCore f v) :
    adelicCyclicFullAwayRepresentation f v a x ∈ adelicFullAwayCyclicCore f v :=
  @representationOrbitSpan_invariant (AdelicFullAwayGroup v) ℂ (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance inferInstance (adelicCyclicFullAwayRepresentation f v)
    (adelicCyclicHilbertGenerator f) a x hx

/-- The original cusp generator belongs to the genuine real-plus-away algebraic orbit core. -/
theorem adelicFullAwayCyclicCore_generator_mem (v : HeightOneSpectrum ℤ) :
    adelicCyclicHilbertGenerator f ∈ adelicFullAwayCyclicCore f v := by
  apply Submodule.subset_span
  exact ⟨1, by simp⟩

/-- The actual real-plus-away action restricted to its original algebraic orbit core. -/
def adelicFullAwayCoreRepresentation (v : HeightOneSpectrum ℤ) :
    Representation ℂ (AdelicFullAwayGroup v) (adelicFullAwayCyclicCore f v) :=
  Representation.subrepresentation (adelicCyclicFullAwayRepresentation f v) (adelicFullAwayCyclicCore f v)
    (fun a x hx => adelicFullAwayCyclicCore_invariant f v a x hx)

/-- The actual external tensor product of the original local and real-plus-away algebraic representations. -/
def adelicLocalFullAwayTensorRepresentation (v : HeightOneSpectrum ℤ) :
    Representation ℂ (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ) × AdelicFullAwayGroup v)
      (adelicLocalCyclicCore f v ⊗[ℂ] adelicFullAwayCyclicCore f v) :=
  Representation.tprod ((adelicLocalSmoothRepresentation f v).comp (MonoidHom.fst _ _))
    ((adelicFullAwayCoreRepresentation f v).comp (MonoidHom.snd _ _))

/-- The original full adelic representation restricted along the genuine local/full-complement adelic group equivalence. -/
def adelicLocalFullAwayJointRepresentation (v : HeightOneSpectrum ℤ) :
    Representation ℂ (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ) × AdelicFullAwayGroup v)
      (AdelicCyclicHilbert f) :=
  (adelicCyclicHilbertRepresentation f).comp
    (adelicLocalFullAwayEquiv v).toMonoidHom

/-- The original joint action is precisely the actual local action followed by the actual real-plus-away action. -/
theorem adelicLocalFullAwayJointRepresentation_apply (v : HeightOneSpectrum ℤ)
    (a : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ) × AdelicFullAwayGroup v)
    (x : AdelicCyclicHilbert f) :
    adelicLocalFullAwayJointRepresentation f v a x =
      adelicCyclicLocalRepresentation f v a.1 (adelicCyclicFullAwayRepresentation f v a.2 x) := by
  have he := @representation_hom_mul_apply RationalAdelicGL2 RationalAdelicGL2 (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance inferInstance (adelicCyclicHilbertRepresentation f)
    (MonoidHom.id _) (rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 v a.1))
    (adelicFullAwayEmbedding v a.2) x
  rw [← adelicLocalFullAwayEquiv_factor] at he
  exact he

/-- The genuine tensor product action has exactly the original orbit-family multiplication. -/
theorem adelicLocalFullAwayTensorFamily_action (v : HeightOneSpectrum ℤ)
    (b a : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ) × AdelicFullAwayGroup v) :
    adelicLocalFullAwayTensorRepresentation f v b (adelicLocalFullAwayTensorFamily f v a) =
      adelicLocalFullAwayTensorFamily f v (b * a) :=
  @tensorRepresentation_orbit_action
    (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) (AdelicFullAwayGroup v)
    (adelicLocalCyclicCore f v) (adelicFullAwayCyclicCore f v)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (adelicLocalSmoothRepresentation f v) (adelicFullAwayCoreRepresentation f v)
    ⟨adelicCyclicHilbertGenerator f, adelicLocalCyclicCore_generator_mem f v⟩
    ⟨adelicCyclicHilbertGenerator f, adelicFullAwayCyclicCore_generator_mem f v⟩ b a

/-- The actual mixed family is the original joint representation orbit with its proved genuine norm normalization. -/
theorem adelicLocalFullAwayMixedFamily_eq_joint (v : HeightOneSpectrum ℤ)
    (a : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ) × AdelicFullAwayGroup v) :
    adelicLocalFullAwayMixedFamily f v a = (‖adelicCyclicHilbertGenerator f‖ : ℂ) •
      adelicLocalFullAwayJointRepresentation f v a (adelicCyclicHilbertGenerator f) :=
  congrArg (fun x : AdelicCyclicHilbert f => (‖adelicCyclicHilbertGenerator f‖ : ℂ) • x)
    (adelicLocalFullAwayJointRepresentation_apply f v a (adelicCyclicHilbertGenerator f)).symm

/-- The original joint adelic action has exactly the genuine mixed-family multiplication. -/
theorem adelicLocalFullAwayMixedFamily_action (v : HeightOneSpectrum ℤ)
    (b a : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ) × AdelicFullAwayGroup v) :
    adelicLocalFullAwayJointRepresentation f v b (adelicLocalFullAwayMixedFamily f v a) =
      adelicLocalFullAwayMixedFamily f v (b * a) := by
  rw [adelicLocalFullAwayMixedFamily_eq_joint, adelicLocalFullAwayMixedFamily_eq_joint]
  exact @representation_scaled_orbit_action
    (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ) × AdelicFullAwayGroup v)
    (AdelicCyclicHilbert f) inferInstance inferInstance inferInstance
    (adelicLocalFullAwayJointRepresentation f v) _ _ b a

/-- The genuine local/full-complement tensor isometry intertwines the actual external tensor product and the original full adelic action at every good prime. -/
theorem adelicLocalFullAwayTensorIsometry_intertwines {p : ℕ} [NeZero p] [Fact p.Prime]
    (F : PrimitiveCuspForm N k) (hpN : p.Coprime N)
    (b : GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ) ×
      AdelicFullAwayGroup (rationalPrimePlace p (Fact.out : p.Prime)))
    (x : adelicLocalCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) ⊗[ℂ]
      adelicFullAwayCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) :
    adelicLocalFullAwayTensorIsometry F hpN
      (adelicLocalFullAwayTensorRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) b x) =
      adelicLocalFullAwayJointRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) b
        (adelicLocalFullAwayTensorIsometry F hpN x) :=
  @linearMap_intertwines_of_spanning_family
    (GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ) ×
      AdelicFullAwayGroup (rationalPrimePlace p (Fact.out : p.Prime)))
    (adelicLocalCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) ⊗[ℂ]
      adelicFullAwayCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
    (AdelicCyclicHilbert F.toCuspForm)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (adelicLocalFullAwayTensorRepresentation F.toCuspForm _) (adelicLocalFullAwayJointRepresentation F.toCuspForm _)
    (adelicLocalFullAwayTensorIsometry F hpN).toLinearMap
    (adelicLocalFullAwayTensorFamily F.toCuspForm _) (adelicLocalFullAwayMixedFamily F.toCuspForm _)
    (adelicLocalFullAwayTensorFamily_span F.toCuspForm _) (adelicLocalFullAwayTensorIsometry_family F hpN)
    (adelicLocalFullAwayTensorFamily_action F.toCuspForm _) (adelicLocalFullAwayMixedFamily_action F.toCuspForm _) b x

end
end Dubon2026

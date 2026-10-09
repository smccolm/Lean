import Dubon2026.AdelicLocalAwayTensorRange
import Dubon2026.FiniteAdelicLocalAwayProduct
import Dubon2026.AdelicLocalSmoothRepresentation

/-! # Genuine product actions and equivariance of the original local-away tensor map -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups TensorProduct

/-- The actual external tensor action sends each original pure orbit tensor to the corresponding product orbit tensor. -/
theorem tensorRepresentation_orbit_action {G H V W : Type*} [Group G] [Group H]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ H W) (x : V) (y : W) (b a : G × H) :
    (Representation.tprod (ρ.comp (MonoidHom.fst G H)) (σ.comp (MonoidHom.snd G H))) b
      (ρ a.1 x ⊗ₜ[ℂ] σ a.2 y) = ρ (b.1 * a.1) x ⊗ₜ[ℂ] σ (b.2 * a.2) y := by
  change TensorProduct.map (ρ b.1) (σ b.2) (ρ a.1 x ⊗ₜ[ℂ] σ a.2 y) = _
  rw [TensorProduct.map_tmul, ← Module.End.mul_apply, ← map_mul,
    ← Module.End.mul_apply, ← map_mul]

/-- Original scaled orbit vectors retain the literal multiplication law of a genuine representation. -/
theorem representation_scaled_orbit_action {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (c : ℂ) (x : V) (b a : G) :
    ρ b (c • ρ a x) = c • ρ (b * a) x := by
  rw [map_smul, ← Module.End.mul_apply, ← map_mul]

/-- A linear map carrying a genuine spanning orbit family to a second orbit family intertwines the actual actions. -/
theorem linearMap_intertwines_of_spanning_family {G V W : Type*} [Group G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (T : V →ₗ[ℂ] W)
    (u : G → V) (w : G → W) (hu : Submodule.span ℂ (Set.range u) = ⊤)
    (hT : ∀ a, T (u a) = w a) (hρ : ∀ b a, ρ b (u a) = u (b * a))
    (hσ : ∀ b a, σ b (w a) = w (b * a)) (b : G) (x : V) :
    T (ρ b x) = σ b (T x) := by
  have he : T.comp (ρ b) = (σ b).comp T := by
    apply (Submodule.linearMap_eq_iff_of_span_eq_top _ _ hu).mpr
    rintro ⟨_, a, rfl⟩
    change T (ρ b (u a)) = σ b (T (u a))
    rw [hρ, hT, hT, hσ]
  exact LinearMap.congr_fun he x

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- Every genuine away-place action preserves the original algebraic away-place orbit core. -/
theorem adelicAwayCyclicCore_invariant (v : HeightOneSpectrum ℤ) (a : finiteAdelicAwayGroup v)
    (x : AdelicCyclicHilbert f) (hx : x ∈ adelicAwayCyclicCore f v) :
    adelicCyclicAwayRepresentation f v a x ∈ adelicAwayCyclicCore f v :=
  @representationOrbitSpan_invariant (finiteAdelicAwayGroup v) ℂ (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance inferInstance (adelicCyclicAwayRepresentation f v)
    (adelicCyclicHilbertGenerator f) a x hx

/-- The original cusp generator belongs to the genuine away-place algebraic orbit core. -/
theorem adelicAwayCyclicCore_generator_mem (v : HeightOneSpectrum ℤ) :
    adelicCyclicHilbertGenerator f ∈ adelicAwayCyclicCore f v := by
  apply Submodule.subset_span
  exact ⟨1, by simp⟩

/-- The actual away-place action restricted to its original algebraic orbit core. -/
def adelicAwaySmoothRepresentation (v : HeightOneSpectrum ℤ) :
    Representation ℂ (finiteAdelicAwayGroup v) (adelicAwayCyclicCore f v) :=
  Representation.subrepresentation (adelicCyclicAwayRepresentation f v) (adelicAwayCyclicCore f v)
    (fun a x hx => adelicAwayCyclicCore_invariant f v a x hx)

/-- The actual external tensor product of the original local and away-place algebraic representations. -/
def adelicLocalAwayTensorRepresentation (v : HeightOneSpectrum ℤ) :
    Representation ℂ (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ) × finiteAdelicAwayGroup v)
      (adelicLocalCyclicCore f v ⊗[ℂ] adelicAwayCyclicCore f v) :=
  Representation.tprod ((adelicLocalSmoothRepresentation f v).comp (MonoidHom.fst _ _))
    ((adelicAwaySmoothRepresentation f v).comp (MonoidHom.snd _ _))

/-- The original full adelic representation restricted along the genuine local-away finite group equivalence. -/
def adelicLocalAwayJointRepresentation (v : HeightOneSpectrum ℤ) :
    Representation ℂ (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ) × finiteAdelicAwayGroup v)
      (AdelicCyclicHilbert f) :=
  (adelicCyclicHilbertRepresentation f).comp
    (rationalAdelicFiniteGL2Embedding.comp (finiteAdelicLocalAwayEquiv v).toMonoidHom)

/-- The original joint action is precisely the actual local action followed by the actual away-place action. -/
theorem adelicLocalAwayJointRepresentation_apply (v : HeightOneSpectrum ℤ)
    (a : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ) × finiteAdelicAwayGroup v)
    (x : AdelicCyclicHilbert f) :
    adelicLocalAwayJointRepresentation f v a x =
      adelicCyclicLocalRepresentation f v a.1 (adelicCyclicAwayRepresentation f v a.2 x) :=
  @representation_hom_mul_apply
    (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) RationalAdelicGL2 (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance inferInstance (adelicCyclicHilbertRepresentation f)
    rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 v a.1) a.2.val x

/-- The genuine tensor product action has exactly the original orbit-family multiplication. -/
theorem adelicLocalAwayTensorFamily_action (v : HeightOneSpectrum ℤ)
    (b a : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ) × finiteAdelicAwayGroup v) :
    adelicLocalAwayTensorRepresentation f v b (adelicLocalAwayTensorFamily f v a) =
      adelicLocalAwayTensorFamily f v (b * a) :=
  @tensorRepresentation_orbit_action
    (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) (finiteAdelicAwayGroup v)
    (adelicLocalCyclicCore f v) (adelicAwayCyclicCore f v)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (adelicLocalSmoothRepresentation f v) (adelicAwaySmoothRepresentation f v)
    ⟨adelicCyclicHilbertGenerator f, adelicLocalCyclicCore_generator_mem f v⟩
    ⟨adelicCyclicHilbertGenerator f, adelicAwayCyclicCore_generator_mem f v⟩ b a

/-- The actual mixed family is the original joint representation orbit with its proved genuine norm normalization. -/
theorem adelicLocalAwayMixedFamily_eq_joint (v : HeightOneSpectrum ℤ)
    (a : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ) × finiteAdelicAwayGroup v) :
    adelicLocalAwayMixedFamily f v a = (‖adelicCyclicHilbertGenerator f‖ : ℂ) •
      adelicLocalAwayJointRepresentation f v a (adelicCyclicHilbertGenerator f) :=
  congrArg (fun x : AdelicCyclicHilbert f => (‖adelicCyclicHilbertGenerator f‖ : ℂ) • x)
    (adelicLocalAwayJointRepresentation_apply f v a (adelicCyclicHilbertGenerator f)).symm

/-- The original joint adelic action has exactly the genuine mixed-family multiplication. -/
theorem adelicLocalAwayMixedFamily_action (v : HeightOneSpectrum ℤ)
    (b a : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ) × finiteAdelicAwayGroup v) :
    adelicLocalAwayJointRepresentation f v b (adelicLocalAwayMixedFamily f v a) =
      adelicLocalAwayMixedFamily f v (b * a) := by
  rw [adelicLocalAwayMixedFamily_eq_joint, adelicLocalAwayMixedFamily_eq_joint]
  exact @representation_scaled_orbit_action
    (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ) × finiteAdelicAwayGroup v)
    (AdelicCyclicHilbert f) inferInstance inferInstance inferInstance
    (adelicLocalAwayJointRepresentation f v) _ _ b a

/-- The genuine local-away tensor isometry intertwines the actual external tensor product and the original full finite-adelic action at every good prime. -/
theorem adelicLocalAwayTensorIsometry_intertwines {p : ℕ} [NeZero p] [Fact p.Prime]
    (F : PrimitiveCuspForm N k) (hpN : p.Coprime N)
    (b : GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ) ×
      finiteAdelicAwayGroup (rationalPrimePlace p (Fact.out : p.Prime)))
    (x : adelicLocalCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) ⊗[ℂ]
      adelicAwayCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) :
    adelicLocalAwayTensorIsometry F hpN
      (adelicLocalAwayTensorRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) b x) =
      adelicLocalAwayJointRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) b
        (adelicLocalAwayTensorIsometry F hpN x) :=
  @linearMap_intertwines_of_spanning_family
    (GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ) ×
      finiteAdelicAwayGroup (rationalPrimePlace p (Fact.out : p.Prime)))
    (adelicLocalCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) ⊗[ℂ]
      adelicAwayCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
    (AdelicCyclicHilbert F.toCuspForm)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (adelicLocalAwayTensorRepresentation F.toCuspForm _) (adelicLocalAwayJointRepresentation F.toCuspForm _)
    (adelicLocalAwayTensorIsometry F hpN).toLinearMap
    (adelicLocalAwayTensorFamily F.toCuspForm _) (adelicLocalAwayMixedFamily F.toCuspForm _)
    (adelicLocalAwayTensorFamily_span F.toCuspForm _) (adelicLocalAwayTensorIsometry_family F hpN)
    (adelicLocalAwayTensorFamily_action F.toCuspForm _) (adelicLocalAwayMixedFamily_action F.toCuspForm _) b x

end
end Dubon2026

import Dubon2026

/-! Exact original finite-flat geometry, local arithmetic restriction and deformation consumers. -/

namespace Dubon2026.SemanticRegression

open Filter MeasureTheory Asymptotics
open scoped BigOperators Topology



section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {R A B : Type*} [CommRing R] [CommRing A] [HopfAlgebra R A] [Module.Free R A]
  [CommRing B] [Algebra R B]

/-- Exact original-object consumer of `freeHopfCoordinateTransfer_antipode`. -/
theorem actual_free_hopf_coordinate_transfer_freeHopfCoordinateTransfer_antipode_source (e : B ≃ₐ[R] A) (b : B) :
    letI := freeHopfCoordinateTransfer e
    e (HopfAlgebra.antipode R b) = HopfAlgebra.antipode R (e b) :=
  freeHopfCoordinateTransfer_antipode e b

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {R A B K : Type*} [CommRing R]
  [CommRing A] [HopfAlgebra R A] [CommRing B] [HopfAlgebra R B]
  [CommRing K] [Algebra R K]

/-- Exact original-object consumer of `hopfCoordinateEquivPoints_coefficient`. -/
theorem actual_hopf_coordinate_equiv_points_hopfCoordinateEquivPoints_coefficient_source (e : B ≃ₐc[R] A)
    (g : K ≃ₐ[R] K) (p : WithConv (A →ₐ[R] K)) :
    hopfCoordinateEquivPoints e (commutativeHopfPointsAutomorphism g p) =
      commutativeHopfPointsAutomorphism g (hopfCoordinateEquivPoints e p) :=
  hopfCoordinateEquivPoints_coefficient e g p

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors

universe uR uF uK uV uC

variable {R : Type uR} {F : Type uF} {K : Type uK} {V : Type uV}
  [CommRing R] [Field F] [Field K] [Algebra R F] [Algebra F K] [Algebra R K]
  [IsScalarTower R F K] [CommGroup V] {ρ : (K ≃ₐ[F] K) →* MulAut V}

/-- Exact original-object consumer of `finiteFreeHopfPointModel_resize_exists`. -/
theorem actual_finite_free_hopf_model_coordinate_resize_finiteFreeHopfPointModel_resize_exists_source
    (m : FiniteFreeHopfPointModel.{uR, uF, uK, uV, uC} R F K V ρ) :
    Nonempty (FiniteFreeHopfPointModel.{uR, uF, uK, uV, uR} R F K V ρ) :=
  finiteFreeHopfPointModel_resize_exists m

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors

universe uC

variable {R F K V W : Type*} [CommRing R] [Field F] [Field K]
  [Algebra R F] [Algebra F K] [Algebra R K] [IsScalarTower R F K]
  [CommGroup V] [CommGroup W]
  {ρ : (K ≃ₐ[F] K) →* MulAut V} {τ : (K ≃ₐ[F] K) →* MulAut W}

/-- Exact original-object consumer of `finiteFreeHopfPointModel_equiv_points`. -/
theorem actual_finite_free_hopf_point_model_equiv_finiteFreeHopfPointModel_equiv_points_source
    (m : FiniteFreeHopfPointModel.{_, _, _, _, uC} R F K V ρ) (e : V ≃* W)
    (he : ∀ (g : K ≃ₐ[F] K) (v : V), e (ρ g v) = τ g (e v)) :
    (finiteFreeHopfPointModelEquiv m e he).pointEquiv = m.pointEquiv.trans e :=
  finiteFreeHopfPointModel_equiv_points m e he

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors

universe uC

variable {R F K V W : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]
  [CommGroup V] [CommGroup W]
  {ρ : (K ≃ₐ[F] K) →* MulAut V} {τ : (K ≃ₐ[F] K) →* MulAut W}

/-- Exact original-object consumer of `finiteFreeHopfPointModel_of_injective_exists`. -/
theorem actual_finite_free_hopf_point_model_embedding_finiteFreeHopfPointModel_of_injective_exists_source
    (m : FiniteFreeHopfPointModel.{_, _, _, _, uC} R F K W τ) (f : V →* W)
    (hf : Function.Injective f)
    (he : ∀ (g : K ≃ₐ[F] K) (v : V), f (ρ g v) = τ g (f v)) :
    Nonempty (FiniteFreeHopfPointModel.{_, _, _, _, uC} R F K V ρ) :=
  finiteFreeHopfPointModel_of_injective_exists m f hf he

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors

universe uC

variable {R F K V W : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]
  [Module.Flat R K] [CommGroup V] [CommGroup W]
  {ρ : (K ≃ₐ[F] K) →* MulAut V} {τ : (K ≃ₐ[F] K) →* MulAut W}

/-- Exact original-object consumer of `finiteFreeHopfPointModel_of_surjective_exists`. -/
theorem actual_finite_free_hopf_point_model_surjection_finiteFreeHopfPointModel_of_surjective_exists_source
    (m : FiniteFreeHopfPointModel.{_, _, _, _, uC} R F K V ρ) (f : V →* W)
    (hf : Function.Surjective f)
    (he : ∀ (g : K ≃ₐ[F] K) (v : V), f (ρ g v) = τ g (f v)) :
    Nonempty (FiniteFreeHopfPointModel.{_, _, _, _, uC} R F K W τ) :=
  finiteFreeHopfPointModel_of_surjective_exists m f hf he

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {O G V W : Type*} [CommRing O] [Group G]
  [AddCommGroup V] [Module O V] [AddCommGroup W] [Module O W]

/-- Exact original-object consumer of `representationUnderlyingGroupAction_intertwining`. -/
theorem actual_representation_underlying_group_action_representationUnderlyingGroupAction_intertwining_source
    (ρ : Representation O G V) (τ : Representation O G W) (f : V →ₗ[O] W)
    (hf : ∀ (g : G) (v : V), f (ρ g v) = τ g (f v))
    (g : G) (v : Multiplicative V) :
    f.toAddMonoidHom.toMultiplicative (representationUnderlyingGroupAction ρ g v) =
      representationUnderlyingGroupAction τ g (f.toAddMonoidHom.toMultiplicative v) :=
  representationUnderlyingGroupAction_intertwining ρ τ f hf g v

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors

universe uC

variable {R F K O V W : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]
  [CommRing O] [AddCommGroup V] [Module O V] [AddCommGroup W] [Module O W]

/-- Exact original-object consumer of `representationHopfModel_of_surjective_exists`. -/
theorem actual_representation_hopf_model_maps_representationHopfModel_of_surjective_exists_source [Module.Flat R K]
    (ρ : Representation O (K ≃ₐ[F] K) V) (τ : Representation O (K ≃ₐ[F] K) W)
    (m : FiniteFreeHopfPointModel.{_, _, _, _, uC} R F K (Multiplicative V)
      (representationUnderlyingGroupAction ρ))
    (f : V →ₗ[O] W) (hf : Function.Surjective f)
    (he : ∀ (g : K ≃ₐ[F] K) (v : V), f (ρ g v) = τ g (f v)) :
    Nonempty (FiniteFreeHopfPointModel.{_, _, _, _, uC} R F K (Multiplicative W)
      (representationUnderlyingGroupAction τ)) :=
  representationHopfModel_of_surjective_exists ρ τ m f hf he

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι A B : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing A] [CommRing B]

/-- Exact original-object consumer of `matrixCoefficientVectorMap_equivariant`. -/
theorem actual_matrix_coefficient_point_actions_matrixCoefficientVectorMap_equivariant_source (f : A →+* B)
    (ρ : G →* GeneralLinearGroup ι A) (g : G) (v : Multiplicative (ι → A)) :
    matrixCoefficientVectorMap f (matrixUnderlyingGroupAction ρ g v) =
      matrixUnderlyingGroupAction ((GeneralLinearGroup.map f).comp ρ) g
        (matrixCoefficientVectorMap f v) :=
  matrixCoefficientVectorMap_equivariant f ρ g v

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors

universe uC

variable {R F K ι A B : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]
  [Fintype ι] [DecidableEq ι] [CommRing A] [CommRing B]

/-- Exact original-object consumer of `matrixCoefficientHopfModel_of_surjective_exists`. -/
theorem actual_matrix_coefficient_hopf_models_matrixCoefficientHopfModel_of_surjective_exists_source [Module.Flat R K]
    (f : A →+* B) (hf : Function.Surjective f)
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι A)
    (m : FiniteFreeHopfPointModel.{_, _, _, _, uC} R F K (Multiplicative (ι → A))
      (matrixUnderlyingGroupAction ρ)) :
    Nonempty (FiniteFreeHopfPointModel.{_, _, _, _, uC} R F K (Multiplicative (ι → B))
      (matrixUnderlyingGroupAction ((GeneralLinearGroup.map f).comp ρ))) :=
  matrixCoefficientHopfModel_of_surjective_exists f hf ρ m

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {F K ι A B C : Type*} [Field F] [Field K] [Algebra F K]
  [Fintype ι] [DecidableEq ι] [CommRing A] [CommRing B] [CommRing C]

/-- Exact original-object consumer of `matrixFiberProductVectorMap_equivariant`. -/
theorem actual_matrix_fiber_product_point_embedding_matrixFiberProductVectorMap_equivariant_source (f : A →+* C) (g : B →+* C)
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι (CoefficientFiberProduct f g))
    (s : K ≃ₐ[F] K) (v : Multiplicative (ι → CoefficientFiberProduct f g)) :
    matrixFiberProductVectorMap f g (matrixUnderlyingGroupAction ρ s v) =
      galoisModuleProductAction
        (matrixUnderlyingGroupAction ((GeneralLinearGroup.map
          (coefficientFiberProductFst f g)).comp ρ))
        (matrixUnderlyingGroupAction ((GeneralLinearGroup.map
          (coefficientFiberProductSnd f g)).comp ρ)) s
        (matrixFiberProductVectorMap f g v) :=
  matrixFiberProductVectorMap_equivariant f g ρ s v

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors

universe uC uD

variable {R F K ι A B C : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]
  [Fintype ι] [DecidableEq ι] [CommRing A] [CommRing B] [CommRing C]

/-- Exact original-object consumer of `matrixFiberProductHopfModel_exists`. -/
theorem actual_matrix_fiber_product_hopf_model_matrixFiberProductHopfModel_exists_source (f : A →+* C) (g : B →+* C)
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι (CoefficientFiberProduct f g))
    (mA : FiniteFreeHopfPointModel.{_, _, _, _, uC} R F K (Multiplicative (ι → A))
      (matrixUnderlyingGroupAction ((GeneralLinearGroup.map
        (coefficientFiberProductFst f g)).comp ρ)))
    (mB : FiniteFreeHopfPointModel.{_, _, _, _, uD} R F K (Multiplicative (ι → B))
      (matrixUnderlyingGroupAction ((GeneralLinearGroup.map
        (coefficientFiberProductSnd f g)).comp ρ))) :
    Nonempty (FiniteFreeHopfPointModel.{_, _, _, _, max uC uD} R F K (Multiplicative (ι → CoefficientFiberProduct f g))
      (matrixUnderlyingGroupAction ρ)) :=
  matrixFiberProductHopfModel_exists f g ρ mA mB

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι A : Type*} [Group G] [Fintype ι] [DecidableEq ι] [CommRing A]

/-- Exact original-object consumer of `matrixConjugacyVectorEquiv_equivariant`. -/
theorem actual_matrix_conjugacy_vector_equiv_matrixConjugacyVectorEquiv_equivariant_source
    (ρ τ : G →* GeneralLinearGroup ι A) (U : GeneralLinearGroup ι A)
    (hc : ∀ g, τ g = U * ρ g * U⁻¹) (g : G) (v : Multiplicative (ι → A)) :
    matrixConjugacyVectorEquiv U (matrixUnderlyingGroupAction ρ g v) =
      matrixUnderlyingGroupAction τ g (matrixConjugacyVectorEquiv U v) :=
  matrixConjugacyVectorEquiv_equivariant ρ τ U hc g v

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors

universe uC

variable {R F K ι A : Type*} [CommRing R] [Field F] [Field K]
  [Algebra R F] [Algebra F K] [Algebra R K] [IsScalarTower R F K]
  [Fintype ι] [DecidableEq ι] [CommRing A]

/-- Exact original-object consumer of `matrixHopfModel_strictConjugacy_iff`. -/
theorem actual_matrix_conjugacy_hopf_models_matrixHopfModel_strictConjugacy_iff_source {k : Type*} [CommRing k]
    (r : A →+* k) (ρ τ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι A)
    (h : MatrixStrictlyConjugate r ρ τ) :
    Nonempty (FiniteFreeHopfPointModel.{_, _, _, _, uC} R F K (Multiplicative (ι → A))
      (matrixUnderlyingGroupAction ρ)) ↔
    Nonempty (FiniteFreeHopfPointModel.{_, _, _, _, uC} R F K (Multiplicative (ι → A))
      (matrixUnderlyingGroupAction τ)) :=
  matrixHopfModel_strictConjugacy_iff r ρ τ h

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors

universe uC uD

variable {R F K ι A B C k : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]
  [Fintype ι] [DecidableEq ι] [CommRing A] [CommRing B] [CommRing C] [CommRing k]
  [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing B]

/-- Exact original-object consumer of `continuousCoefficientFiberProductHopfModel_exists`. -/
theorem actual_continuous_fiber_product_hopf_models_continuousCoefficientFiberProductHopfModel_exists_source
    (f : A →+* C) (g : B →+* C) (hg : Function.Surjective g) [IsLocalHom g]
    (rC : C →+* k)
    (ρA : (K ≃ₐ[F] K) →ₜ* GeneralLinearGroup ι A)
    (ρB : (K ≃ₐ[F] K) →ₜ* GeneralLinearGroup ι B)
    (h : MatrixStrictlyConjugate rC
      ((GeneralLinearGroup.map g).comp ρB.toMonoidHom)
      ((GeneralLinearGroup.map f).comp ρA.toMonoidHom))
    (mA : FiniteFreeHopfPointModel.{_, _, _, _, uC} R F K (Multiplicative (ι → A))
      (matrixUnderlyingGroupAction ρA.toMonoidHom))
    (mB : FiniteFreeHopfPointModel.{_, _, _, _, uD} R F K (Multiplicative (ι → B))
      (matrixUnderlyingGroupAction ρB.toMonoidHom)) :
    ∃ ρ : (K ≃ₐ[F] K) →ₜ* GeneralLinearGroup ι (CoefficientFiberProduct f g),
      (GeneralLinearGroup.map (coefficientFiberProductFst f g)).comp ρ.toMonoidHom =
        ρA.toMonoidHom ∧
      MatrixStrictlyConjugate (rC.comp g) ρB.toMonoidHom
        ((GeneralLinearGroup.map (coefficientFiberProductSnd f g)).comp ρ.toMonoidHom) ∧
      Nonempty (FiniteFreeHopfPointModel.{_, _, _, _, max uC uD} R F K (Multiplicative (ι → CoefficientFiberProduct f g))
        (matrixUnderlyingGroupAction ρ.toMonoidHom)) :=
  continuousCoefficientFiberProductHopfModel_exists f g hg rC ρA ρB h mA mB

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors

universe uC

variable {G ι A : Type*} [Group G] [Fintype ι] [DecidableEq ι] [CommRing A]

variable {R F K : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]

/-- Exact original-object consumer of `matrixIdealQuotientHopfModel_transition_exists`. -/
theorem actual_matrix_ideal_quotient_hopf_models_matrixIdealQuotientHopfModel_transition_exists_source (I J : Ideal A) (hIJ : I ≤ J)
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι A)
    (m : FiniteFreeHopfPointModel.{_, _, _, _, uC} R F K (Multiplicative (ι → A ⧸ I))
      (matrixUnderlyingGroupAction (matrixIdealQuotientRepresentation I ρ))) :
    Nonempty (FiniteFreeHopfPointModel.{_, _, _, _, uC} R F K (Multiplicative (ι → A ⧸ J))
      (matrixUnderlyingGroupAction (matrixIdealQuotientRepresentation J ρ))) :=
  matrixIdealQuotientHopfModel_transition_exists I J hIJ ρ m

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors

universe u

variable (R F K : Type u) {ι A : Type u}
  [CommRing R] [Field F] [Field K] [Algebra R F] [Algebra F K] [Algebra R K]
  [IsScalarTower R F K] [Fintype ι] [DecidableEq ι] [CommRing A] [IsLocalRing A]

variable {R F K}

variable [IsDomain R] [IsPrincipalIdealRing R] [PerfectField F] [IsFractionRing R F]
  [Normal F K] [IsAlgClosed K]

/-- Exact original-object consumer of `matrixAdicHopfFlat_of_cofinal`. -/
theorem actual_matrix_adic_hopf_flat_condition_matrixAdicHopfFlat_of_cofinal_source
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι A)
    (levels : Set ℕ)
    (hlevels : ∀ n : ℕ, 0 < n → ∃ m ∈ levels, n ≤ m)
    (hmodels : ∀ m ∈ levels,
      Nonempty (FiniteFreeHopfPointModel.{u,u,u,u,u} R F K
        (Multiplicative (ι → A ⧸ IsLocalRing.maximalIdeal A ^ m))
        (matrixUnderlyingGroupAction
          (matrixIdealQuotientRepresentation (IsLocalRing.maximalIdeal A ^ m) ρ)))) :
    MatrixAdicHopfFlat R F K ρ :=
  matrixAdicHopfFlat_of_cofinal ρ levels hlevels hmodels

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι A B : Type*} [Group G] [CommRing A] [CommRing B]
  [Fintype B]

variable [Fintype ι] [DecidableEq ι]

/-- Exact original-object consumer of `finiteCoefficientVectorSpanningMap_equivariant`. -/
theorem actual_finite_coefficient_vector_spanning_finiteCoefficientVectorSpanningMap_equivariant_source (f : A →+* B)
    (ρ : G →* GeneralLinearGroup ι A) (g : G) (v : B → Multiplicative (ι → A)) :
    finiteCoefficientVectorSpanningMap f (fun b => matrixUnderlyingGroupAction ρ g (v b)) =
      matrixUnderlyingGroupAction ((GeneralLinearGroup.map f).comp ρ) g
        (finiteCoefficientVectorSpanningMap f v) :=
  finiteCoefficientVectorSpanningMap_equivariant f ρ g v

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors

universe u

variable {G V : Type*} [Group G] [CommGroup V]

variable {R F K W : Type u} [CommRing R] [Field F] [Field K]
  [Algebra R F] [Algebra F K] [Algebra R K] [IsScalarTower R F K] [CommGroup W]
  {τ : (K ≃ₐ[F] K) →* MulAut W}

/-- Exact original-object consumer of `finiteFreeHopfPointModel_finitePi_exists`. -/
theorem actual_finite_free_hopf_point_model_finite_power_finiteFreeHopfPointModel_finitePi_exists_source (J : Type u) [Fintype J] [Nonempty J]
    (m : FiniteFreeHopfPointModel.{u,u,u,u,u} R F K W τ) :
    Nonempty (FiniteFreeHopfPointModel.{u,u,u,u,u} R F K (J → W) (galoisModulePiAction J τ)) :=
  finiteFreeHopfPointModel_finitePi_exists J m

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors

universe u

variable {R F K ι A B : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]
  [Fintype ι] [DecidableEq ι] [CommRing A] [CommRing B] [Fintype B]

/-- Exact original-object consumer of `finiteCoefficientExtensionHopfModel_exists`. -/
theorem actual_finite_coefficient_extension_hopf_model_finiteCoefficientExtensionHopfModel_exists_source (f : A →+* B)
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι A)
    (m : FiniteFreeHopfPointModel.{u,u,u,u,u} R F K (Multiplicative (ι → A))
      (matrixUnderlyingGroupAction ρ)) :
    Nonempty (FiniteFreeHopfPointModel.{u,u,u,u,u} R F K (Multiplicative (ι → B))
      (matrixUnderlyingGroupAction ((GeneralLinearGroup.map f).comp ρ))) :=
  finiteCoefficientExtensionHopfModel_exists f ρ m

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors

universe u

variable {A B : Type u} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]

variable {G ι : Type u} [Group G] [Fintype ι] [DecidableEq ι]

variable {R F K : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]
  [IsNoetherianRing B] [Finite (IsLocalRing.ResidueField B)]

/-- Exact original-object consumer of `matrixAdicHopfFlat_coefficientChange`. -/
theorem actual_matrix_adic_hopf_flat_coefficient_change_matrixAdicHopfFlat_coefficientChange_source (f : A →+* B) [IsLocalHom f]
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι A)
    (hρ : MatrixAdicHopfFlat R F K ρ) :
    MatrixAdicHopfFlat R F K ((GeneralLinearGroup.map f).comp ρ) :=
  matrixAdicHopfFlat_coefficientChange f ρ hρ

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors

universe u

variable {R F K ι A : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]
  [Fintype ι] [DecidableEq ι] [CommRing A] [IsLocalRing A]

/-- Exact original-object consumer of `matrixAdicHopfFlat_finite_iff`. -/
theorem actual_matrix_adic_hopf_flat_finite_coefficients_matrixAdicHopfFlat_finite_iff_source [Finite A]
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι A) :
    MatrixAdicHopfFlat R F K ρ ↔
      Nonempty (FiniteFreeHopfPointModel.{u,u,u,u,u} R F K (Multiplicative (ι → A))
        (matrixUnderlyingGroupAction ρ)) :=
  matrixAdicHopfFlat_finite_iff ρ

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {R F K ι A B C k : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]
  [Fintype ι] [DecidableEq ι] [CommRing A] [CommRing B] [CommRing C] [CommRing k]
  [IsLocalRing A] [IsLocalRing B] [Finite A] [Finite B]
  [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing B]

/-- Exact original-object consumer of `matrixAdicHopfFlat_finite_continuous_gluing`. -/
theorem actual_matrix_adic_hopf_flat_finite_gluing_matrixAdicHopfFlat_finite_continuous_gluing_source
    (f : A →+* C) (g : B →+* C) (hg : Function.Surjective g) [IsLocalHom g]
    (rC : C →+* k)
    (ρA : (K ≃ₐ[F] K) →ₜ* GeneralLinearGroup ι A)
    (ρB : (K ≃ₐ[F] K) →ₜ* GeneralLinearGroup ι B)
    (h : MatrixStrictlyConjugate rC
      ((GeneralLinearGroup.map g).comp ρB.toMonoidHom)
      ((GeneralLinearGroup.map f).comp ρA.toMonoidHom))
    (hA : MatrixAdicHopfFlat R F K ρA.toMonoidHom)
    (hB : MatrixAdicHopfFlat R F K ρB.toMonoidHom) :
    letI := coefficientFiberProduct_isLocalRing f g
    ∃ ρ : (K ≃ₐ[F] K) →ₜ* GeneralLinearGroup ι (CoefficientFiberProduct f g),
      (GeneralLinearGroup.map (coefficientFiberProductFst f g)).comp ρ.toMonoidHom =
        ρA.toMonoidHom ∧
      MatrixStrictlyConjugate (rC.comp g) ρB.toMonoidHom
        ((GeneralLinearGroup.map (coefficientFiberProductSnd f g)).comp ρ.toMonoidHom) ∧
      MatrixAdicHopfFlat R F K ρ.toMonoidHom :=
  matrixAdicHopfFlat_finite_continuous_gluing f g hg rC ρA ρB h hA hB

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors

universe u

variable (R F K : Type u) {ι O A : Type u} [CommRing R] [Field F] [Field K]
  [Algebra R F] [Algebra F K] [Algebra R K] [IsScalarTower R F K]
  [Fintype ι] [DecidableEq ι] [CommRing O] [IsLocalRing O]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A]

variable {R F K}

variable [IsDomain R] [IsPrincipalIdealRing R] [PerfectField F] [IsFractionRing R F]
  [Normal F K] [IsAlgClosed K] [Finite A]

/-- Exact original-object consumer of `originalUnframedHopfFlat_finite_class_iff`. -/
theorem actual_original_unframed_hopf_flat_condition_originalUnframedHopfFlat_finite_class_iff_source
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u}) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (j : (K ≃ₐ[F] K) →* H) (ρ : OriginalContinuousFramedFiber eA H σ) :
    originalUnframedHopfFlat R F K eA H σ j (originalUnframedClass eA H σ ρ) ↔
      Nonempty (FiniteFreeHopfPointModel.{u,u,u,u,u} R F K (Multiplicative (ι → A))
        (matrixUnderlyingGroupAction (ρ.val.toMonoidHom.comp j))) :=
  originalUnframedHopfFlat_finite_class_iff eA H σ j ρ

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors

universe u

variable {R F K ι O A B : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]
  [Fintype ι] [DecidableEq ι] [CommRing O] [IsLocalRing O]
  [Finite (IsLocalRing.ResidueField O)]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A]
  [CommRing B] [IsLocalRing B] [Algebra O B] [WithIdeal B] [IsNoetherianRing B]

/-- Exact original-object consumer of `originalUnframedHopfFlat_postcomp`. -/
theorem actual_original_unframed_hopf_flat_naturality_originalUnframedHopfFlat_postcomp_source
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (eB : IsLocalRing.ResidueField B ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u}) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (j : (K ≃ₐ[F] K) →* H)
    (f : A →ₐ[O] B) (hf : Continuous f)
    (hres : (localCoefficientReduction eB).comp f = localCoefficientReduction eA)
    (q : OriginalUnframedDeformationClass eA H σ)
    (hq : originalUnframedHopfFlat R F K eA H σ j q) :
    originalUnframedHopfFlat R F K eB H σ j
      (originalUnframedPostcomp eA eB H σ f hf hres q) :=
  originalUnframedHopfFlat_postcomp eA eB H σ j f hf hres q hq

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors

universe uC uD

variable {A ι : Type*} [CommRing A]

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [Fintype ι] [DecidableEq ι]

variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [PerfectField F] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]

/-- Exact original-object consumer of `matrixIdealIntersectionHopfModel_exists`. -/
theorem actual_matrix_ideal_intersection_hopf_models_matrixIdealIntersectionHopfModel_exists_source (I J : Ideal A)
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι A)
    (mI : FiniteFreeHopfPointModel.{_, _, _, _, uC} R F K (Multiplicative (ι → A ⧸ I))
      (matrixUnderlyingGroupAction (matrixIdealQuotientRepresentation I ρ)))
    (mJ : FiniteFreeHopfPointModel.{_, _, _, _, uD} R F K (Multiplicative (ι → A ⧸ J))
      (matrixUnderlyingGroupAction (matrixIdealQuotientRepresentation J ρ))) :
    Nonempty (FiniteFreeHopfPointModel.{_, _, _, _, max uC uD} R F K (Multiplicative (ι → A ⧸ (I ⊓ J)))
      (matrixUnderlyingGroupAction (matrixIdealQuotientRepresentation (I ⊓ J) ρ))) :=
  matrixIdealIntersectionHopfModel_exists I J ρ mI mJ

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {A ι : Type*} [CommRing A] [TopologicalSpace A] [CompactSpace A]

/-- Exact original-object consumer of `compactClosedIdeals_finiteIntersection_le`. -/
theorem actual_compact_closed_ideal_finite_intersection_compactClosedIdeals_finiteIntersection_le_source
    (I : ι → Ideal A) (hI : ∀ i, IsClosed (I i : Set A))
    (U : Ideal A) (hU : IsOpen (U : Set A)) (hsub : (⨅ i, I i) ≤ U) (i₀ : ι) :
    ∃ s : Finset ι, i₀ ∈ s ∧ (⨅ i ∈ s, I i) ≤ U :=
  compactClosedIdeals_finiteIntersection_le I hI U hU hsub i₀

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors

universe u

variable {R F K A ι η : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]
  [CommRing A] [Fintype ι] [DecidableEq ι]

/-- Exact original-object consumer of `matrixFiniteIdealIntersectionHopfModel_exists`. -/
theorem actual_matrix_finite_ideal_intersection_hopf_models_matrixFiniteIdealIntersectionHopfModel_exists_source
    (I : η → Ideal A) (s : Finset η) (hs : s.Nonempty)
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι A)
    (hmodels : ∀ i ∈ s,
      Nonempty (FiniteFreeHopfPointModel.{u,u,u,u,u} R F K (Multiplicative (ι → A ⧸ I i))
        (matrixUnderlyingGroupAction (matrixIdealQuotientRepresentation (I i) ρ)))) :
    Nonempty (FiniteFreeHopfPointModel.{u,u,u,u,u} R F K
      (Multiplicative (ι → A ⧸ (⨅ i ∈ s, I i)))
      (matrixUnderlyingGroupAction (matrixIdealQuotientRepresentation (⨅ i ∈ s, I i) ρ))) :=
  matrixFiniteIdealIntersectionHopfModel_exists I s hs ρ hmodels

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors

universe u

variable {R F K A ι η : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]
  [CommRing A] [TopologicalSpace A] [CompactSpace A] [Fintype ι] [DecidableEq ι]

/-- Exact original-object consumer of `matrixOpenIdealHopfModel_of_closedFamily`. -/
theorem actual_matrix_open_ideal_hopf_model_from_closed_family_matrixOpenIdealHopfModel_of_closedFamily_source
    (I : η → Ideal A) (hI : ∀ i, IsClosed (I i : Set A)) (i₀ : η)
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι A)
    (hmodels : ∀ i,
      Nonempty (FiniteFreeHopfPointModel.{u,u,u,u,u} R F K (Multiplicative (ι → A ⧸ I i))
        (matrixUnderlyingGroupAction (matrixIdealQuotientRepresentation (I i) ρ))))
    (U : Ideal A) (hU : IsOpen (U : Set A)) (hsub : (⨅ i, I i) ≤ U) :
    Nonempty (FiniteFreeHopfPointModel.{u,u,u,u,u} R F K (Multiplicative (ι → A ⧸ U))
      (matrixUnderlyingGroupAction (matrixIdealQuotientRepresentation U ρ))) :=
  matrixOpenIdealHopfModel_of_closedFamily I hI i₀ ρ hmodels U hU hsub

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors

universe u

variable {R F K A ι : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]
  [CommRing A] [IsLocalRing A] [WithIdeal A] [Fintype ι] [DecidableEq ι]

/-- Exact original-object consumer of `matrixAdicHopfFlat_iff_openQuotients`. -/
theorem actual_matrix_adic_hopf_flat_open_quotients_matrixAdicHopfFlat_iff_openQuotients_source
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι A) :
    MatrixAdicHopfFlat R F K ρ ↔
      ∀ U : Ideal A, IsOpen (U : Set A) →
        Nonempty (FiniteFreeHopfPointModel.{u,u,u,u,u} R F K (Multiplicative (ι → A ⧸ U))
          (matrixUnderlyingGroupAction (matrixIdealQuotientRepresentation U ρ))) :=
  matrixAdicHopfFlat_iff_openQuotients hA ρ

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors

universe u

variable {R F K A B ι : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]
  [CommRing A] [CommRing B] [Fintype B] [Fintype ι] [DecidableEq ι]

variable [IsLocalRing A] [IsLocalRing B]

/-- Exact original-object consumer of `matrixAdicHopfFlat_finiteCoefficient_injective_iff`. -/
theorem actual_matrix_finite_coefficient_model_invariance_matrixAdicHopfFlat_finiteCoefficient_injective_iff_source
    (f : A →+* B) (hf : Function.Injective f)
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι A) :
    MatrixAdicHopfFlat R F K ρ ↔
      MatrixAdicHopfFlat R F K ((GeneralLinearGroup.map f).comp ρ) :=
  matrixAdicHopfFlat_finiteCoefficient_injective_iff f hf ρ

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors

universe u

variable (R F K : Type u) {A ι : Type u} [CommRing R] [Field F] [Field K]
  [Algebra R F] [Algebra F K] [Algebra R K] [IsScalarTower R F K]
  [CommRing A] [TopologicalSpace A] [Fintype ι] [DecidableEq ι]

variable {R F K} [IsTopologicalRing A]

variable [IsDomain R] [IsPrincipalIdealRing R] [PerfectField F] [IsFractionRing R F]
  [Normal F K] [IsAlgClosed K] [CompactSpace A]

/-- Exact original-object consumer of `matrixHopfModelCoefficientIdeal_le_iff`. -/
theorem actual_matrix_hopf_model_coefficient_ideal_matrixHopfModelCoefficientIdeal_le_iff_source
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι A)
    (I₀ : Ideal A) (hI₀ : IsOpen (I₀ : Set A))
    (m₀ : FiniteFreeHopfPointModel.{u,u,u,u,u} R F K (Multiplicative (ι → A ⧸ I₀))
      (matrixUnderlyingGroupAction (matrixIdealQuotientRepresentation I₀ ρ)))
    (U : Ideal A) (hU : IsOpen (U : Set A)) :
    matrixHopfModelCoefficientIdeal R F K ρ ≤ U ↔
      Nonempty (FiniteFreeHopfPointModel.{u,u,u,u,u} R F K (Multiplicative (ι → A ⧸ U))
        (matrixUnderlyingGroupAction (matrixIdealQuotientRepresentation U ρ))) :=
  matrixHopfModelCoefficientIdeal_le_iff ρ I₀ hI₀ m₀ U hU

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors

universe u

variable {R F K A ι : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]
  [CommRing A] [IsLocalRing A] [WithIdeal A] [CompactSpace A] [T2Space A]
  [Fintype ι] [DecidableEq ι]

/-- Exact original-object consumer of `matrixAdicHopfFlat_iff_modelCoefficientIdeal_eq_bot`. -/
theorem actual_matrix_adic_hopf_flat_coefficient_ideal_matrixAdicHopfFlat_iff_modelCoefficientIdeal_eq_bot_source
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι A)
    (I₀ : Ideal A) (hI₀ : IsOpen (I₀ : Set A))
    (m₀ : FiniteFreeHopfPointModel.{u,u,u,u,u} R F K (Multiplicative (ι → A ⧸ I₀))
      (matrixUnderlyingGroupAction (matrixIdealQuotientRepresentation I₀ ρ))) :
    MatrixAdicHopfFlat R F K ρ ↔ matrixHopfModelCoefficientIdeal R F K ρ = ⊥ :=
  matrixAdicHopfFlat_iff_modelCoefficientIdeal_eq_bot hA ρ I₀ hI₀ m₀

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {A B : Type*} [CommRing A] [CommRing B]

variable {G ι : Type*} [Group G] [Fintype ι] [DecidableEq ι]

/-- Exact original-object consumer of `matrixIdealQuotientRepresentation_comap`. -/
theorem actual_coefficient_comap_quotient_representation_matrixIdealQuotientRepresentation_comap_source (f : A →+* B) (J : Ideal B)
    (ρ : G →* GeneralLinearGroup ι A) :
    (GeneralLinearGroup.map (coefficientComapQuotientMap f J)).comp
      (matrixIdealQuotientRepresentation (J.comap f) ρ) =
    matrixIdealQuotientRepresentation J ((GeneralLinearGroup.map f).comp ρ) :=
  matrixIdealQuotientRepresentation_comap f J ρ

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors

universe u

variable {R F K A B ι : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]
  [CommRing A] [CommRing B] [Fintype ι] [DecidableEq ι]

/-- Exact original-object consumer of `matrixComapQuotientHopfModel_iff`. -/
theorem actual_matrix_comap_quotient_hopf_model_matrixComapQuotientHopfModel_iff_source
    (f : A →+* B) (J : Ideal B) [Finite (B ⧸ J)]
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι A) :
    Nonempty (FiniteFreeHopfPointModel.{u,u,u,u,u} R F K
      (Multiplicative (ι → A ⧸ J.comap f))
      (matrixUnderlyingGroupAction (matrixIdealQuotientRepresentation (J.comap f) ρ))) ↔
    Nonempty (FiniteFreeHopfPointModel.{u,u,u,u,u} R F K
      (Multiplicative (ι → B ⧸ J))
      (matrixUnderlyingGroupAction
        (matrixIdealQuotientRepresentation J ((GeneralLinearGroup.map f).comp ρ)))) :=
  matrixComapQuotientHopfModel_iff f J ρ

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors

universe u

variable {R F K A B ι : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]
  [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [CompactSpace A]
  [CommRing B] [IsLocalRing B] [WithIdeal B] [IsNoetherianRing B]
  [Finite (IsLocalRing.ResidueField B)] [T2Space B] [Fintype ι] [DecidableEq ι]

/-- Exact original-object consumer of `matrixAdicHopfFlat_coefficient_iff_modelIdeal_le_ker`. -/
theorem actual_matrix_hopf_model_coefficient_kernel_matrixAdicHopfFlat_coefficient_iff_modelIdeal_le_ker_source
    (hB : (WithIdeal.i : Ideal B) = IsLocalRing.maximalIdeal B)
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι A)
    (I₀ : Ideal A) (hI₀ : IsOpen (I₀ : Set A))
    (m₀ : FiniteFreeHopfPointModel.{u,u,u,u,u} R F K (Multiplicative (ι → A ⧸ I₀))
      (matrixUnderlyingGroupAction (matrixIdealQuotientRepresentation I₀ ρ)))
    (f : A →+* B) (hf : Continuous f) :
    MatrixAdicHopfFlat R F K ((GeneralLinearGroup.map f).comp ρ) ↔
      matrixHopfModelCoefficientIdeal R F K ρ ≤ RingHom.ker f :=
  matrixAdicHopfFlat_coefficient_iff_modelIdeal_le_ker hB ρ I₀ hI₀ m₀ f hf

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors

universe u

variable {R F K A ι : Type u} [CommRing R] [Field F] [Field K]
  [Algebra R F] [Algebra F K] [Algebra R K] [IsScalarTower R F K]
  [CommRing A] [IsLocalRing A] [TopologicalSpace A] [Fintype ι] [DecidableEq ι]

/-- Exact original-object consumer of `matrixHopfModelCoefficientQuotient_isLocal`. -/
theorem actual_matrix_hopf_model_coefficient_ideal_local_matrixHopfModelCoefficientQuotient_isLocal_source
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι A)
    (hopen : IsOpen (IsLocalRing.maximalIdeal A : Set A))
    (m : FiniteFreeHopfPointModel.{u,u,u,u,u} R F K
      (Multiplicative (ι → A ⧸ IsLocalRing.maximalIdeal A))
      (matrixUnderlyingGroupAction (matrixIdealQuotientRepresentation (IsLocalRing.maximalIdeal A) ρ))) :
    IsLocalRing (A ⧸ matrixHopfModelCoefficientIdeal R F K ρ) :=
  matrixHopfModelCoefficientQuotient_isLocal ρ hopen m

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors

universe u

variable {R F K ι O A B : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]
  [Fintype ι] [DecidableEq ι] [CommRing O] [IsLocalRing O]
  [Finite (IsLocalRing.ResidueField O)]
  [CommRing A] [IsLocalRing A] [Algebra O A] [TopologicalSpace A]
  [IsTopologicalRing A] [CompactSpace A]
  [CommRing B] [IsLocalRing B] [Algebra O B] [WithIdeal B] [IsNoetherianRing B] [T2Space B]

/-- Exact original-object consumer of `originalUnframedHopfFlat_coefficient_iff`. -/
theorem actual_original_unframed_hopf_flat_coefficient_ideal_originalUnframedHopfFlat_coefficient_iff_source
    (hB : (WithIdeal.i : Ideal B) = IsLocalRing.maximalIdeal B)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (eB : IsLocalRing.ResidueField B ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u}) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (τ : H →ₜ* GeneralLinearGroup ι A)
    (hτ : (GeneralLinearGroup.map (localCoefficientReduction eA).toRingHom).comp
      τ.toMonoidHom = σ)
    (j : (K ≃ₐ[F] K) →* H)
    (I₀ : Ideal A) (hI₀ : IsOpen (I₀ : Set A))
    (m₀ : FiniteFreeHopfPointModel.{u,u,u,u,u} R F K (Multiplicative (ι → A ⧸ I₀))
      (matrixUnderlyingGroupAction (matrixIdealQuotientRepresentation I₀ (τ.toMonoidHom.comp j))))
    (f : OriginalContinuousCoefficientFiber eA eB) :
    originalUnframedHopfFlat R F K eB H σ j
        (originalCoefficientRepresentationClass eA eB H σ τ hτ f) ↔
      matrixHopfModelCoefficientIdeal R F K (τ.toMonoidHom.comp j) ≤
        RingHom.ker f.val.toRingHom :=
  originalUnframedHopfFlat_coefficient_iff hB eA eB H σ τ hτ j I₀ hI₀ m₀ f

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors

universe u

variable {R F K ι O A B : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]
  [Fintype ι] [DecidableEq ι] [CommRing O] [IsLocalRing O]
  [Finite (IsLocalRing.ResidueField O)]
  [CommRing A] [IsLocalRing A] [Algebra O A] [TopologicalSpace A]
  [IsTopologicalRing A] [CompactSpace A]
  [CommRing B] [IsLocalRing B] [Algebra O B] [WithIdeal B] [IsNoetherianRing B] [T2Space B]

/-- Exact original-object consumer of `originalUnframedHopfFlatQuotientEquiv_evaluation`. -/
theorem actual_original_unframed_hopf_flat_quotient_equivalence_originalUnframedHopfFlatQuotientEquiv_evaluation_source
    (hB : (WithIdeal.i : Ideal B) = IsLocalRing.maximalIdeal B)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (eB : IsLocalRing.ResidueField B ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u}) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (τ : H →ₜ* GeneralLinearGroup ι A)
    (hτ : (GeneralLinearGroup.map (localCoefficientReduction eA).toRingHom).comp
      τ.toMonoidHom = σ)
    (j : (K ≃ₐ[F] K) →* H)
    (I₀ : Ideal A) (hI₀ : IsOpen (I₀ : Set A))
    (m₀ : FiniteFreeHopfPointModel.{u,u,u,u,u} R F K (Multiplicative (ι → A ⧸ I₀))
      (matrixUnderlyingGroupAction (matrixIdealQuotientRepresentation I₀ (τ.toMonoidHom.comp j))))
    [IsLocalRing (A ⧸ matrixHopfModelCoefficientIdeal R F K (τ.toMonoidHom.comp j))]
    (hbij : Function.Bijective (originalCoefficientRepresentationClass eA eB H σ τ hτ))
    (f : OriginalContinuousCoefficientFiber (originalLocalQuotientResidueEquiv eA
      (matrixHopfModelCoefficientIdeal R F K (τ.toMonoidHom.comp j))) eB) :
    (originalUnframedHopfFlatQuotientEquiv hB eA eB H σ τ hτ j I₀ hI₀ m₀ hbij f).val =
      originalCoefficientRepresentationClass eA eB H σ τ hτ
        (originalQuotientCoefficientRestriction eA eB
          (matrixHopfModelCoefficientIdeal R F K (τ.toMonoidHom.comp j)) f).val :=
  originalUnframedHopfFlatQuotientEquiv_evaluation hB eA eB H σ τ hτ j I₀ hI₀ m₀ hbij f

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors

universe u

variable {R F K ι O A H : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]
  [Fintype ι] [DecidableEq ι] [CommRing O] [IsLocalRing O]
  [CommRing A] [IsLocalRing A] [Algebra O A] [Group H]

/-- Exact original-object consumer of `originalResidualHopfModel_exists`. -/
theorem actual_original_residual_hopf_model_originalResidualHopfModel_exists_source
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (τ : H →* GeneralLinearGroup ι A)
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hτ : (GeneralLinearGroup.map (localCoefficientReduction eA).toRingHom).comp τ = σ)
    (j : (K ≃ₐ[F] K) →* H)
    (m : FiniteFreeHopfPointModel.{u,u,u,u,u} R F K
      (Multiplicative (ι → IsLocalRing.ResidueField O))
      (matrixUnderlyingGroupAction (σ.comp j))) :
    Nonempty (FiniteFreeHopfPointModel.{u,u,u,u,u} R F K
      (Multiplicative (ι → A ⧸ IsLocalRing.maximalIdeal A))
      (matrixUnderlyingGroupAction
        (matrixIdealQuotientRepresentation (IsLocalRing.maximalIdeal A) (τ.comp j)))) :=
  originalResidualHopfModel_exists eA τ σ hτ j m

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors

universe u

variable {R F K A ι : Type u} [CommRing R] [Field F] [Field K]
  [Algebra R F] [Algebra F K] [Algebra R K] [IsScalarTower R F K]
  [CommRing A] [IsLocalRing A] [TopologicalSpace A] [IsTopologicalRing A] [Fintype ι] [DecidableEq ι]

variable [IsNoetherianRing A] [Finite (IsLocalRing.ResidueField A)]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]

/-- Exact original-object consumer of `matrixHopfModelCoefficientQuotient_localData`. -/
theorem actual_matrix_hopf_model_coefficient_quotient_local_data_matrixHopfModelCoefficientQuotient_localData_source
    (hA : IsAdic (IsLocalRing.maximalIdeal A))
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι A)
    (m : FiniteFreeHopfPointModel.{u,u,u,u,u} R F K
      (Multiplicative (ι → A ⧸ IsLocalRing.maximalIdeal A))
      (matrixUnderlyingGroupAction (matrixIdealQuotientRepresentation (IsLocalRing.maximalIdeal A) ρ))) :
    let J := matrixHopfModelCoefficientIdeal R F K ρ
    letI := matrixHopfModelCoefficientQuotient_isLocal_of_isAdic hA ρ m
    IsNoetherianRing (A ⧸ J) ∧ IsAdic (IsLocalRing.maximalIdeal (A ⧸ J)) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal (A ⧸ J)) (A ⧸ J) :=
  matrixHopfModelCoefficientQuotient_localData hA ρ m

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {R F K ι : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]
  [Fintype ι] [DecidableEq ι]

variable {O L : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]
  [Field L] [Algebra (IsLocalRing.ResidueField O) L] [IsAlgClosed L]

/-- Exact original-object consumer of `arithmeticUnframedHopfFlatUniversality_exists`. -/
theorem actual_arithmetic_unframed_hopf_flat_universality_arithmeticUnframedHopfFlatUniversality_exists_source
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ)
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L) σ))] (i₀ : ι)
    (j : (K ≃ₐ[F] K) →* rationalArithmeticGaloisGroup a)
    (m : FiniteFreeHopfPointModel.{0,0,0,0,0} R F K
      (Multiplicative (ι → IsLocalRing.ResidueField O))
      (matrixUnderlyingGroupAction (σ.comp j))) :
    ∃ T : Subalgebra O (ArithmeticFramedUniversalRing a ha p hp hpa σ hσ),
      T = ArithmeticTraceCoefficientRing a ha p hp hpa σ hσ ∧
      (letI : IsTopologicalRing T := inferInstanceAs (IsTopologicalRing T.toSubring)
    ∃ hlocal : IsLocalRing T,
      letI := hlocal
      IsNoetherianRing T ∧ IsAdic (IsLocalRing.maximalIdeal T) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal T) T ∧
      ∃ (eT : IsLocalRing.ResidueField T ≃ₐ[O] IsLocalRing.ResidueField O)
        (τ : rationalArithmeticGaloisGroup a →ₜ* GeneralLinearGroup ι T)
        (hτ : (GeneralLinearGroup.map (localCoefficientReduction eT).toRingHom).comp
          τ.toMonoidHom = σ),
        let J := matrixHopfModelCoefficientIdeal R F K (τ.toMonoidHom.comp j)
        ∃ hquot : IsLocalRing (T ⧸ J),
          letI := hquot
          IsNoetherianRing (T ⧸ J) ∧ IsAdic (IsLocalRing.maximalIdeal (T ⧸ J)) ∧
          IsAdicComplete (IsLocalRing.maximalIdeal (T ⧸ J)) (T ⧸ J) ∧
          ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
            [Algebra O A] [WithIdeal A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
            (_hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
            (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O),
            ∃ e : OriginalContinuousCoefficientFiber (originalLocalQuotientResidueEquiv eT J) eA ≃
              {c : OriginalUnframedDeformationClass eA (rationalArithmeticGaloisGroup a) σ //
                originalUnframedHopfFlat R F K eA (rationalArithmeticGaloisGroup a) σ j c},
              ∀ f, (e f).val = originalCoefficientRepresentationClass eT eA
                (rationalArithmeticGaloisGroup a) σ τ hτ
                (originalQuotientCoefficientRestriction eT eA J f).val) :=
  arithmeticUnframedHopfFlatUniversality_exists (L := L) a ha p hp hpa σ hσ i₀ j m

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory Opposite AlgebraicGeometry MonObj MonoidalCategory
open scoped TensorProduct NumberField nonZeroDivisors CategoryTheory.MonObj CategoryTheory.Obj

universe u

variable {R : Type u} [CommRing R]

variable (G : (CommAlgCat.{u} R)ᵒᵖ) [GrpObj G]

/-- Exact original-object consumer of `coordinateGroupObjectHopfAlgebra_isCocomm`. -/
theorem actual_coordinate_group_object_hopf_algebra_coordinateGroupObjectHopfAlgebra_isCocomm_source [IsCommMonObj G] :
    letI := coordinateGroupObjectHopfAlgebra G
    Coalgebra.IsCocomm R G.unop :=
  coordinateGroupObjectHopfAlgebra_isCocomm G

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory Opposite AlgebraicGeometry MonObj MonoidalCategory
open scoped TensorProduct NumberField nonZeroDivisors CategoryTheory.MonObj CategoryTheory.Obj

universe u

variable {R : Type u} [CommRing R]

variable {A : Type u} [CommRing A] [Algebra R A]

/-- The original scheme fiber products in this exact consumer. -/
noncomputable local instance reverseSchemeCartesianSource1920 : CartesianMonoidalCategory (Over (Spec (CommRingCat.of R))) :=
  Over.cartesianMonoidalCategory _

/-- Retain the same original monoidal structure under the complete import graph. -/
noncomputable local instance reverseSchemeMonoidalSource1920 : MonoidalCategory (Over (Spec (CommRingCat.of R))) :=
  reverseSchemeCartesianSource1920.toSemiCartesianMonoidalCategory.toMonoidalCategory

/-- The same original scheme fiber-product symmetry. -/
noncomputable local instance reverseSchemeBraidedSource1920 : BraidedCategory (Over (Spec (CommRingCat.of R))) :=
  Over.braidedCategory _

/-- Exact original-object consumer of `affineSchemeCoordinateGroupObject_exists`. -/
theorem actual_affine_scheme_coordinate_group_object_affineSchemeCoordinateGroupObject_exists_source
    (G : CommGrp (Over (Spec (CommRingCat.of R))))
    (e : (coordinateRelativeSpec (R := R)).obj (op (CommAlgCat.of R A)) ≅ G.X) :
    Nonempty (CommGrpObj (op (CommAlgCat.of R A))) :=
  affineSchemeCoordinateGroupObject_exists G e

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory Opposite AlgebraicGeometry MonObj MonoidalCategory
open scoped TensorProduct NumberField nonZeroDivisors CategoryTheory.MonObj CategoryTheory.Obj

universe u

variable {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

/-- Exact original-object consumer of `finiteFlatScheme_exists_freeAffineCoordinates`. -/
theorem actual_finite_flat_scheme_affine_coordinates_finiteFlatScheme_exists_freeAffineCoordinates_source
    (X : Over (Spec (CommRingCat.of R))) [IsFinite X.hom] [AlgebraicGeometry.Flat X.hom] :
    ∃ A : CommAlgCat.{u} R, Module.Finite R A ∧ Module.Free R A ∧
      Nonempty ((coordinateRelativeSpec (R := R)).obj (op A) ≅ X) :=
  finiteFlatScheme_exists_freeAffineCoordinates X

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory Opposite AlgebraicGeometry MonObj MonoidalCategory
open scoped TensorProduct NumberField nonZeroDivisors CategoryTheory.MonObj CategoryTheory.Obj

universe u

variable {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

/-- The original scheme fiber products in this exact consumer. -/
noncomputable local instance reverseSchemeCartesianSource1922 : CartesianMonoidalCategory (Over (Spec (CommRingCat.of R))) :=
  Over.cartesianMonoidalCategory _

/-- Retain the same original monoidal structure under the complete import graph. -/
noncomputable local instance reverseSchemeMonoidalSource1922 : MonoidalCategory (Over (Spec (CommRingCat.of R))) :=
  reverseSchemeCartesianSource1922.toSemiCartesianMonoidalCategory.toMonoidalCategory

/-- The same original scheme fiber-product symmetry. -/
noncomputable local instance reverseSchemeBraidedSource1922 : BraidedCategory (Over (Spec (CommRingCat.of R))) :=
  Over.braidedCategory _

/-- Exact original-object consumer of `finiteFlatGroupScheme_exists_hopfCoordinates`. -/
theorem actual_finite_flat_group_scheme_hopf_coordinates_finiteFlatGroupScheme_exists_hopfCoordinates_source
    (G : CommGrp (Over (Spec (CommRingCat.of R))))
    [IsFinite G.X.hom] [AlgebraicGeometry.Flat G.X.hom] :
    ∃ A : CommAlgCat.{u} R, ∃ h : HopfAlgebra R A,
      h.toAlgebra = (inferInstance : Algebra R A) ∧
      (letI : Algebra R A := h.toAlgebra
       letI := h
       Coalgebra.IsCocomm R A ∧ Module.Finite R A ∧ Module.Free R A ∧
         Nonempty ((coordinateRelativeSpec (R := R)).obj (op A) ≅ G.X)) :=
  finiteFlatGroupScheme_exists_hopfCoordinates G

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory Opposite AlgebraicGeometry MonObj MonoidalCategory
open scoped TensorProduct NumberField nonZeroDivisors CategoryTheory.MonObj CategoryTheory.Obj

universe u

variable {R : Type u} [CommRing R]
variable (G : (CommAlgCat.{u} R)ᵒᵖ) [GrpObj G]

/-- Exact original-object consumer of `coordinateGroupObjectPointEquiv_coefficient`. -/
theorem actual_coordinate_group_object_point_equiv_coordinateGroupObjectPointEquiv_coefficient_source (B C : CommAlgCat.{u} R) (f : B ⟶ C) :
    letI := coordinateGroupObjectHopfAlgebra G
    ∀ p : WithConv (G.unop →ₐ[R] B),
      coordinateGroupObjectPointEquiv G C (commutativeHopfPointsMap f.hom p) =
        f.op ≫ coordinateGroupObjectPointEquiv G B p :=
  coordinateGroupObjectPointEquiv_coefficient G B C f

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory Opposite AlgebraicGeometry MonObj MonoidalCategory
open scoped TensorProduct NumberField nonZeroDivisors CategoryTheory.MonObj CategoryTheory.Obj

universe u

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- The original scheme fiber products in this exact consumer. -/
noncomputable local instance reverseSchemeCartesianSource1924 : CartesianMonoidalCategory (Over (Spec (CommRingCat.of R))) :=
  Over.cartesianMonoidalCategory _

/-- Retain the same original monoidal structure under the complete import graph. -/
noncomputable local instance reverseSchemeMonoidalSource1924 : MonoidalCategory (Over (Spec (CommRingCat.of R))) :=
  reverseSchemeCartesianSource1924.toSemiCartesianMonoidalCategory.toMonoidalCategory

/-- The same original scheme fiber-product symmetry. -/
noncomputable local instance reverseSchemeBraidedSource1924 : BraidedCategory (Over (Spec (CommRingCat.of R))) :=
  Over.braidedCategory _

/-- Exact original-object consumer of `affineSchemeRecoveredHopfPointEquiv_coefficient`. -/
theorem actual_affine_scheme_recovered_hopf_points_affineSchemeRecoveredHopfPointEquiv_coefficient_source
    (G : CommGrp (Over (Spec (CommRingCat.of R))))
    (e : (coordinateRelativeSpec (R := R)).obj (op (CommAlgCat.of R A)) ≅ G.X)
    (B C : CommAlgCat.{u} R) (f : B ⟶ C) :
    letI := affineSchemeCoordinateGroupObject G e
    letI := coordinateGroupObjectHopfAlgebra (op (CommAlgCat.of R A))
    ∀ p : WithConv (A →ₐ[R] B),
      affineSchemeRecoveredHopfPointEquiv G e C (commutativeHopfPointsMap f.hom p) =
        (coordinateRelativeSpec (R := R)).map f.op ≫ affineSchemeRecoveredHopfPointEquiv G e B p :=
  affineSchemeRecoveredHopfPointEquiv_coefficient G e B C f

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory Opposite AlgebraicGeometry MonObj MonoidalCategory
open scoped TensorProduct NumberField nonZeroDivisors CategoryTheory.MonObj CategoryTheory.Obj

universe u

variable {R F K V : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [Field K] [Algebra R F] [Algebra F K] [Algebra R K]
  [IsScalarTower R F K] [CommGroup V] {ρ : (K ≃ₐ[F] K) →* MulAut V}

/-- The original scheme fiber products in this exact consumer. -/
noncomputable local instance reverseSchemeCartesianSource1925 : CartesianMonoidalCategory (Over (Spec (CommRingCat.of R))) :=
  Over.cartesianMonoidalCategory _

/-- Retain the same original monoidal structure under the complete import graph. -/
noncomputable local instance reverseSchemeMonoidalSource1925 : MonoidalCategory (Over (Spec (CommRingCat.of R))) :=
  reverseSchemeCartesianSource1925.toSemiCartesianMonoidalCategory.toMonoidalCategory

/-- The same original scheme fiber-product symmetry. -/
noncomputable local instance reverseSchemeBraidedSource1925 : BraidedCategory (Over (Spec (CommRingCat.of R))) :=
  Over.braidedCategory _

/-- Exact original-object consumer of `finiteFlatSchemePointModel_exists`. -/
theorem actual_finite_flat_scheme_point_model_finiteFlatSchemePointModel_exists_source
    (G : CommGrp (Over (Spec (CommRingCat.of R))))
    [IsFinite G.X.hom] [AlgebraicGeometry.Flat G.X.hom]
    (E : ((coordinateRelativeSpec (R := R)).obj (op (CommAlgCat.of R K)) ⟶ G.X) ≃* V)
    (hE : ∀ (g : K ≃ₐ[F] K)
      (p : (coordinateRelativeSpec (R := R)).obj (op (CommAlgCat.of R K)) ⟶ G.X),
      E ((coordinateRelativeSpec (R := R)).map
        (CommAlgCat.ofHom (g.restrictScalars R).toAlgHom).op ≫ p) = ρ g (E p)) :
    Nonempty (FiniteFreeHopfPointModel.{u,u,u,u,u} R F K V ρ) :=
  finiteFlatSchemePointModel_exists G E hE

end

section

open IsDedekindDomain Matrix Module WithConv CategoryTheory Opposite AlgebraicGeometry MonObj MonoidalCategory
open scoped TensorProduct NumberField nonZeroDivisors CategoryTheory.MonObj CategoryTheory.Obj

universe u

variable {R F K V : Type u} [CommRing R] [Field F] [Field K]
  [Algebra R F] [Algebra F K] [Algebra R K] [IsScalarTower R F K] [CommGroup V]

/-- Exact original-object consumer of `finiteFreeHopfPointModel_iff_schemeRealization`. -/
theorem actual_finite_flat_scheme_model_equivalence_finiteFreeHopfPointModel_iff_schemeRealization_source [IsDomain R] [IsPrincipalIdealRing R]
    (ρ : (K ≃ₐ[F] K) →* MulAut V) :
    Nonempty (FiniteFreeHopfPointModel.{u,u,u,u,u} R F K V ρ) ↔
      FiniteFlatSchemePointRealization (R := R) (F := F) (K := K) (V := V) ρ :=
  finiteFreeHopfPointModel_iff_schemeRealization ρ

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors

universe u

variable (R F K : Type u) {ι A : Type u}
  [CommRing R] [Field F] [Field K] [Algebra R F] [Algebra F K] [Algebra R K]
  [IsScalarTower R F K] [Fintype ι] [DecidableEq ι] [CommRing A] [IsLocalRing A]

variable {R F K} [IsDomain R] [IsPrincipalIdealRing R]

/-- Exact original-object consumer of `matrixAdicHopfFlat_iff_finiteFlatScheme`. -/
theorem actual_matrix_adic_finite_flat_scheme_condition_matrixAdicHopfFlat_iff_finiteFlatScheme_source
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι A) :
    MatrixAdicHopfFlat R F K ρ ↔ MatrixAdicFiniteFlatScheme R F K ρ :=
  matrixAdicHopfFlat_iff_finiteFlatScheme ρ

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors

universe u

variable (R F K : Type u) {ι O A : Type u}
  [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [Field F] [Field K]
  [Algebra R F] [Algebra F K] [Algebra R K] [IsScalarTower R F K]
  [Fintype ι] [DecidableEq ι] [CommRing O] [IsLocalRing O]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A]

variable {R F K}

/-- Exact original-object consumer of `originalUnframedHopfFlat_iff_finiteFlatScheme`. -/
theorem actual_original_unframed_finite_flat_scheme_condition_originalUnframedHopfFlat_iff_finiteFlatScheme_source
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u}) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (j : (K ≃ₐ[F] K) →* H) (c : OriginalUnframedDeformationClass eA H σ) :
    originalUnframedHopfFlat R F K eA H σ j c ↔
      originalUnframedFiniteFlatScheme R F K eA H σ j c :=
  originalUnframedHopfFlat_iff_finiteFlatScheme eA H σ j c

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors

universe u

variable {R F K ι O A B : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]
  [Fintype ι] [DecidableEq ι] [CommRing O] [IsLocalRing O]
  [Finite (IsLocalRing.ResidueField O)]
  [CommRing A] [IsLocalRing A] [Algebra O A] [TopologicalSpace A]
  [IsTopologicalRing A] [CompactSpace A]
  [CommRing B] [IsLocalRing B] [Algebra O B] [WithIdeal B] [IsNoetherianRing B] [T2Space B]

/-- Exact original-object consumer of `originalUnframedFiniteFlatSchemeQuotientEquiv_evaluation`. -/
theorem actual_original_unframed_finite_flat_scheme_quotient_equivalence_originalUnframedFiniteFlatSchemeQuotientEquiv_evaluation_source
    (hB : (WithIdeal.i : Ideal B) = IsLocalRing.maximalIdeal B)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (eB : IsLocalRing.ResidueField B ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u}) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (τ : H →ₜ* GeneralLinearGroup ι A)
    (hτ : (GeneralLinearGroup.map (localCoefficientReduction eA).toRingHom).comp
      τ.toMonoidHom = σ)
    (j : (K ≃ₐ[F] K) →* H)
    (I₀ : Ideal A) (hI₀ : IsOpen (I₀ : Set A))
    (m₀ : FiniteFreeHopfPointModel.{u,u,u,u,u} R F K (Multiplicative (ι → A ⧸ I₀))
      (matrixUnderlyingGroupAction (matrixIdealQuotientRepresentation I₀ (τ.toMonoidHom.comp j))))
    [IsLocalRing (A ⧸ matrixHopfModelCoefficientIdeal R F K (τ.toMonoidHom.comp j))]
    (hbij : Function.Bijective (originalCoefficientRepresentationClass eA eB H σ τ hτ))
    (f : OriginalContinuousCoefficientFiber (originalLocalQuotientResidueEquiv eA
      (matrixHopfModelCoefficientIdeal R F K (τ.toMonoidHom.comp j))) eB) :
    (originalUnframedFiniteFlatSchemeQuotientEquiv hB eA eB H σ τ hτ j I₀ hI₀ m₀ hbij f).val =
      originalCoefficientRepresentationClass eA eB H σ τ hτ
        (originalQuotientCoefficientRestriction eA eB
          (matrixHopfModelCoefficientIdeal R F K (τ.toMonoidHom.comp j)) f).val :=
  originalUnframedFiniteFlatSchemeQuotientEquiv_evaluation hB eA eB H σ τ hτ j I₀ hI₀ m₀ hbij f

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {R F K ι : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]
  [Fintype ι] [DecidableEq ι]

variable {O L : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]
  [Field L] [Algebra (IsLocalRing.ResidueField O) L] [IsAlgClosed L]

/-- Exact original-object consumer of `arithmeticUnframedFiniteFlatSchemeUniversality_exists`. -/
theorem actual_arithmetic_unframed_finite_flat_scheme_universality_arithmeticUnframedFiniteFlatSchemeUniversality_exists_source
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ)
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L) σ))] (i₀ : ι)
    (j : (K ≃ₐ[F] K) →* rationalArithmeticGaloisGroup a)
    (m : FiniteFreeHopfPointModel.{0,0,0,0,0} R F K
      (Multiplicative (ι → IsLocalRing.ResidueField O))
      (matrixUnderlyingGroupAction (σ.comp j))) :
    ∃ T : Subalgebra O (ArithmeticFramedUniversalRing a ha p hp hpa σ hσ),
      T = ArithmeticTraceCoefficientRing a ha p hp hpa σ hσ ∧
      (letI : IsTopologicalRing T := inferInstanceAs (IsTopologicalRing T.toSubring)
    ∃ hlocal : IsLocalRing T,
      letI := hlocal
      IsNoetherianRing T ∧ IsAdic (IsLocalRing.maximalIdeal T) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal T) T ∧
      ∃ (eT : IsLocalRing.ResidueField T ≃ₐ[O] IsLocalRing.ResidueField O)
        (τ : rationalArithmeticGaloisGroup a →ₜ* GeneralLinearGroup ι T)
        (hτ : (GeneralLinearGroup.map (localCoefficientReduction eT).toRingHom).comp
          τ.toMonoidHom = σ),
        let J := matrixHopfModelCoefficientIdeal R F K (τ.toMonoidHom.comp j)
        ∃ hquot : IsLocalRing (T ⧸ J),
          letI := hquot
          IsNoetherianRing (T ⧸ J) ∧ IsAdic (IsLocalRing.maximalIdeal (T ⧸ J)) ∧
          IsAdicComplete (IsLocalRing.maximalIdeal (T ⧸ J)) (T ⧸ J) ∧
          ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
            [Algebra O A] [WithIdeal A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
            (_hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
            (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O),
            ∃ e : OriginalContinuousCoefficientFiber (originalLocalQuotientResidueEquiv eT J) eA ≃
              {c : OriginalUnframedDeformationClass eA (rationalArithmeticGaloisGroup a) σ //
                originalUnframedFiniteFlatScheme R F K eA (rationalArithmeticGaloisGroup a) σ j c},
              ∀ f, (e f).val = originalCoefficientRepresentationClass eT eA
                (rationalArithmeticGaloisGroup a) σ τ hτ
                (originalQuotientCoefficientRestriction eT eA J f).val) :=
  arithmeticUnframedFiniteFlatSchemeUniversality_exists (L := L) a ha p hp hpa σ hσ i₀ j m

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {k E F K : Type*} [Field k] [Field E] [Field F] [Field K]
  [Algebra k E] [Normal k E] [Algebra k F] [Algebra F K] [Algebra k K]
  [IsScalarTower k F K]

/-- Exact original-object consumer of `embeddedNormalGaloisRestriction_commutes`. -/
theorem actual_embedded_normal_galois_restriction_embeddedNormalGaloisRestriction_commutes_source (e : E →ₐ[k] K)
    (g : K ≃ₐ[F] K) (x : E) :
    e (embeddedNormalGaloisRestriction e g x) = g (e x) :=
  embeddedNormalGaloisRestriction_commutes e g x

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {F K : Type} [Field F] [Field K] [Algebra ℚ F]
  [Algebra F K] [Algebra ℚ K] [IsScalarTower ℚ F K] [IsAlgClosed K]

/-- Exact original-object consumer of `rationalArithmeticLocalRestriction_commutes`. -/
theorem actual_rational_arithmetic_local_restriction_rationalArithmeticLocalRestriction_commutes_source
    (a : 𝓞 ℚ) (g : K ≃ₐ[F] K) (x : rationalUnramifiedExtension a) :
    let U := rationalUnramifiedExtension a
    letI : Algebra ℚ U := U.algebra'
    rationalArithmeticLocalEmbedding (K := K) a
        ((show U ≃ₐ[ℚ] U from rationalArithmeticLocalRestriction a g) x) =
      g (rationalArithmeticLocalEmbedding (K := K) a x) :=
  rationalArithmeticLocalRestriction_commutes a g x

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {k E F K : Type*} [Field k] [Field E] [Field F] [Field K]
  [Algebra k E] [Normal k E] [Algebra k F] [Algebra F K] [Algebra k K]
  [IsScalarTower k F K] [Algebra.IsAlgebraic F K]

/-- Exact original-object consumer of `embeddedNormalGaloisRestriction_continuous`. -/
theorem actual_embedded_normal_galois_restriction_continuity_embeddedNormalGaloisRestriction_continuous_source (e : E →ₐ[k] K) :
    Continuous (embeddedNormalGaloisRestriction (F := F) e) :=
  embeddedNormalGaloisRestriction_continuous e

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {F K : Type} [Field F] [Field K] [Algebra ℚ F]
  [Algebra F K] [Algebra ℚ K] [IsScalarTower ℚ F K] [IsAlgClosed K]
  [Algebra.IsAlgebraic F K]

/-- Exact original-object consumer of `rationalArithmeticLocalRestriction_continuous`. -/
theorem actual_rational_arithmetic_local_restriction_continuity_rationalArithmeticLocalRestriction_continuous_source (a : 𝓞 ℚ) :
    Continuous (rationalArithmeticLocalRestriction (F := F) (K := K) a) :=
  rationalArithmeticLocalRestriction_continuous (F := F) (K := K) a

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors




/-- Exact original-object consumer of `rationalPrimeArithmeticRestriction_commutes`. -/
theorem actual_rational_prime_arithmetic_restriction_rationalPrimeArithmeticRestriction_commutes_source
    (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)
    (g : rationalPrimeLocalClosure p hp ≃ₐ[rationalPrimeLocalField p hp]
      rationalPrimeLocalClosure p hp) (x : rationalUnramifiedExtension a) :
    let U := rationalUnramifiedExtension a
    letI : Algebra ℚ U := U.algebra'
    rationalArithmeticLocalEmbedding (K := rationalPrimeLocalClosure p hp) a
        ((show U ≃ₐ[ℚ] U from rationalPrimeArithmeticRestriction a p hp g) x) =
      g (rationalArithmeticLocalEmbedding (K := rationalPrimeLocalClosure p hp) a x) :=
  rationalPrimeArithmeticRestriction_commutes a p hp g x

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι : Type} [Fintype ι] [DecidableEq ι]

variable {O L : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]
  [Field L] [Algebra (IsLocalRing.ResidueField O) L] [IsAlgClosed L]

/-- Exact original-object consumer of `arithmeticPrimeFiniteFlatSchemeUniversality_exists`. -/
theorem actual_arithmetic_prime_finite_flat_scheme_universality_arithmeticPrimeFiniteFlatSchemeUniversality_exists_source
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ)
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L) σ))] (i₀ : ι)

    (m : FiniteFreeHopfPointModel.{0,0,0,0,0} (rationalPrimeLocalIntegerRing p hp) (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)
      (Multiplicative (ι → IsLocalRing.ResidueField O))
      (matrixUnderlyingGroupAction (σ.comp (rationalPrimeArithmeticRestriction a p hp).toMonoidHom))) :
    ∃ T : Subalgebra O (ArithmeticFramedUniversalRing a ha p hp hpa σ hσ),
      T = ArithmeticTraceCoefficientRing a ha p hp hpa σ hσ ∧
      (letI : IsTopologicalRing T := inferInstanceAs (IsTopologicalRing T.toSubring)
    ∃ hlocal : IsLocalRing T,
      letI := hlocal
      IsNoetherianRing T ∧ IsAdic (IsLocalRing.maximalIdeal T) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal T) T ∧
      ∃ (eT : IsLocalRing.ResidueField T ≃ₐ[O] IsLocalRing.ResidueField O)
        (τ : rationalArithmeticGaloisGroup a →ₜ* GeneralLinearGroup ι T)
        (hτ : (GeneralLinearGroup.map (localCoefficientReduction eT).toRingHom).comp
          τ.toMonoidHom = σ),
        let J := matrixHopfModelCoefficientIdeal (rationalPrimeLocalIntegerRing p hp) (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp) (τ.toMonoidHom.comp (rationalPrimeArithmeticRestriction a p hp).toMonoidHom)
        ∃ hquot : IsLocalRing (T ⧸ J),
          letI := hquot
          IsNoetherianRing (T ⧸ J) ∧ IsAdic (IsLocalRing.maximalIdeal (T ⧸ J)) ∧
          IsAdicComplete (IsLocalRing.maximalIdeal (T ⧸ J)) (T ⧸ J) ∧
          ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
            [Algebra O A] [WithIdeal A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
            (_hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
            (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O),
            ∃ e : OriginalContinuousCoefficientFiber (originalLocalQuotientResidueEquiv eT J) eA ≃
              {c : OriginalUnframedDeformationClass eA (rationalArithmeticGaloisGroup a) σ //
                originalUnframedFiniteFlatScheme (rationalPrimeLocalIntegerRing p hp) (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp) eA (rationalArithmeticGaloisGroup a) σ (rationalPrimeArithmeticRestriction a p hp).toMonoidHom c},
              ∀ f, (e f).val = originalCoefficientRepresentationClass eT eA
                (rationalArithmeticGaloisGroup a) σ τ hτ
                (originalQuotientCoefficientRestriction eT eA J f).val) :=
  arithmeticPrimeFiniteFlatSchemeUniversality_exists (L := L) a ha p hp hpa σ hσ i₀ m

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors

universe u

variable {R F K ι O A B : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]
  [Fintype ι] [DecidableEq ι] [CommRing O] [IsLocalRing O]
  [Finite (IsLocalRing.ResidueField O)]
  [CommRing A] [IsLocalRing A] [Algebra O A] [TopologicalSpace A]
  [IsTopologicalRing A] [CompactSpace A]
  [CommRing B] [IsLocalRing B] [Algebra O B] [WithIdeal B] [IsNoetherianRing B] [T2Space B]

/-- Exact original-object consumer of `originalUnframedDeterminantFiniteFlat_coefficient_iff`. -/
theorem actual_original_unframed_determinant_finite_flat_coefficient_ideal_originalUnframedDeterminantFiniteFlat_coefficient_iff_source
    (hB : (WithIdeal.i : Ideal B) = IsLocalRing.maximalIdeal B)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (eB : IsLocalRing.ResidueField B ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u}) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (τ : H →ₜ* GeneralLinearGroup ι A)
    (hτ : (GeneralLinearGroup.map (localCoefficientReduction eA).toRingHom).comp
      τ.toMonoidHom = σ)
    (j : (K ≃ₐ[F] K) →* H)
    (I₀ : Ideal A) (hI₀ : IsOpen (I₀ : Set A))
    (m₀ : FiniteFreeHopfPointModel.{u,u,u,u,u} R F K (Multiplicative (ι → A ⧸ I₀))
      (matrixUnderlyingGroupAction (matrixIdealQuotientRepresentation I₀ (τ.toMonoidHom.comp j))))
    (δ : H →* Oˣ) (f : OriginalContinuousCoefficientFiber eA eB) :
    (originalUnframedHasDeterminant eB H σ δ
        (originalCoefficientRepresentationClass eA eB H σ τ hτ f) ∧
      originalUnframedFiniteFlatScheme R F K eB H σ j
        (originalCoefficientRepresentationClass eA eB H σ τ hτ f)) ↔
      representationDeterminantIdeal τ.toMonoidHom δ ⊔
        matrixHopfModelCoefficientIdeal R F K (τ.toMonoidHom.comp j) ≤
        RingHom.ker f.val.toRingHom :=
  originalUnframedDeterminantFiniteFlat_coefficient_iff hB eA eB H σ τ hτ j I₀ hI₀ m₀ δ f

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors

universe u

variable {R F K O A H ι : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]
  [CommRing O] [IsLocalRing O] [CommRing A] [IsLocalRing A] [Algebra O A]
  [TopologicalSpace A] [IsTopologicalRing A] [Group H] [Fintype ι] [DecidableEq ι]

/-- Exact original-object consumer of `representationDeterminantHopfFlatQuotient_localData`. -/
theorem actual_residual_determinant_hopf_flat_quotient_representationDeterminantHopfFlatQuotient_localData_source
    [IsNoetherianRing A] [Finite (IsLocalRing.ResidueField O)]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (hA : IsAdic (IsLocalRing.maximalIdeal A))
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (τ : H →* GeneralLinearGroup ι A)
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hτ : (GeneralLinearGroup.map (localCoefficientReduction eA).toRingHom).comp τ = σ)
    (δ : H →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (j : (K ≃ₐ[F] K) →* H)
    (m : FiniteFreeHopfPointModel.{u,u,u,u,u} R F K
      (Multiplicative (ι → IsLocalRing.ResidueField O))
      (matrixUnderlyingGroupAction (σ.comp j))) :
    let J := representationDeterminantIdeal τ δ ⊔
      matrixHopfModelCoefficientIdeal R F K (τ.comp j)
    letI := representationDeterminantHopfFlatQuotient_isLocal hA eA τ σ hτ δ hδ j m
    IsNoetherianRing (A ⧸ J) ∧ IsAdic (IsLocalRing.maximalIdeal (A ⧸ J)) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal (A ⧸ J)) (A ⧸ J) :=
  representationDeterminantHopfFlatQuotient_localData hA eA τ σ hτ δ hδ j m

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors

universe u

variable {R F K ι O A B : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]
  [Fintype ι] [DecidableEq ι] [CommRing O] [IsLocalRing O]
  [Finite (IsLocalRing.ResidueField O)]
  [CommRing A] [IsLocalRing A] [Algebra O A] [TopologicalSpace A]
  [IsTopologicalRing A] [CompactSpace A]
  [CommRing B] [IsLocalRing B] [Algebra O B] [WithIdeal B] [IsNoetherianRing B] [T2Space B]

/-- Exact original-object consumer of `originalUnframedDeterminantFiniteFlatQuotientEquiv_evaluation`. -/
theorem actual_original_unframed_determinant_finite_flat_quotient_equivalence_originalUnframedDeterminantFiniteFlatQuotientEquiv_evaluation_source
    (hB : (WithIdeal.i : Ideal B) = IsLocalRing.maximalIdeal B)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (eB : IsLocalRing.ResidueField B ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u}) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (τ : H →ₜ* GeneralLinearGroup ι A)
    (hτ : (GeneralLinearGroup.map (localCoefficientReduction eA).toRingHom).comp
      τ.toMonoidHom = σ)
    (j : (K ≃ₐ[F] K) →* H)
    (I₀ : Ideal A) (hI₀ : IsOpen (I₀ : Set A))
    (m₀ : FiniteFreeHopfPointModel.{u,u,u,u,u} R F K (Multiplicative (ι → A ⧸ I₀))
      (matrixUnderlyingGroupAction (matrixIdealQuotientRepresentation I₀ (τ.toMonoidHom.comp j))))
    (δ : H →* Oˣ)
    [IsLocalRing (A ⧸ (representationDeterminantIdeal τ.toMonoidHom δ ⊔ matrixHopfModelCoefficientIdeal R F K (τ.toMonoidHom.comp j)))]
    (hbij : Function.Bijective (originalCoefficientRepresentationClass eA eB H σ τ hτ))
    (f : OriginalContinuousCoefficientFiber (originalLocalQuotientResidueEquiv eA
      ((representationDeterminantIdeal τ.toMonoidHom δ ⊔ matrixHopfModelCoefficientIdeal R F K (τ.toMonoidHom.comp j)))) eB) :
    (originalUnframedDeterminantFiniteFlatQuotientEquiv hB eA eB H σ τ hτ j I₀ hI₀ m₀ δ hbij f).val =
      originalCoefficientRepresentationClass eA eB H σ τ hτ
        (originalQuotientCoefficientRestriction eA eB
          ((representationDeterminantIdeal τ.toMonoidHom δ ⊔ matrixHopfModelCoefficientIdeal R F K (τ.toMonoidHom.comp j))) f).val :=
  originalUnframedDeterminantFiniteFlatQuotientEquiv_evaluation hB eA eB H σ τ hτ j I₀ hI₀ m₀ δ hbij f

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {R F K ι : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]
  [Fintype ι] [DecidableEq ι]

variable {O L : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]
  [Field L] [Algebra (IsLocalRing.ResidueField O) L] [IsAlgClosed L]

/-- Exact original-object consumer of `arithmeticUnframedDeterminantFiniteFlatUniversality_exists`. -/
theorem actual_arithmetic_unframed_determinant_finite_flat_universality_arithmeticUnframedDeterminantFiniteFlatUniversality_exists_source
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ)
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L) σ))] (i₀ : ι)
    (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (j : (K ≃ₐ[F] K) →* rationalArithmeticGaloisGroup a)
    (m : FiniteFreeHopfPointModel.{0,0,0,0,0} R F K
      (Multiplicative (ι → IsLocalRing.ResidueField O))
      (matrixUnderlyingGroupAction (σ.comp j))) :
    ∃ T : Subalgebra O (ArithmeticFramedUniversalRing a ha p hp hpa σ hσ),
      T = ArithmeticTraceCoefficientRing a ha p hp hpa σ hσ ∧
      (letI : IsTopologicalRing T := inferInstanceAs (IsTopologicalRing T.toSubring)
    ∃ hlocal : IsLocalRing T,
      letI := hlocal
      IsNoetherianRing T ∧ IsAdic (IsLocalRing.maximalIdeal T) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal T) T ∧
      ∃ (eT : IsLocalRing.ResidueField T ≃ₐ[O] IsLocalRing.ResidueField O)
        (τ : rationalArithmeticGaloisGroup a →ₜ* GeneralLinearGroup ι T)
        (hτ : (GeneralLinearGroup.map (localCoefficientReduction eT).toRingHom).comp
          τ.toMonoidHom = σ),
        let J := representationDeterminantIdeal τ.toMonoidHom δ ⊔
          matrixHopfModelCoefficientIdeal R F K (τ.toMonoidHom.comp j)
        ∃ hquot : IsLocalRing (T ⧸ J),
          letI := hquot
          IsNoetherianRing (T ⧸ J) ∧ IsAdic (IsLocalRing.maximalIdeal (T ⧸ J)) ∧
          IsAdicComplete (IsLocalRing.maximalIdeal (T ⧸ J)) (T ⧸ J) ∧
          ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
            [Algebra O A] [WithIdeal A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
            (_hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
            (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O),
            ∃ e : OriginalContinuousCoefficientFiber (originalLocalQuotientResidueEquiv eT J) eA ≃
              {c : OriginalUnframedDeformationClass eA (rationalArithmeticGaloisGroup a) σ //
                originalUnframedHasDeterminant eA (rationalArithmeticGaloisGroup a) σ δ c ∧
                  originalUnframedFiniteFlatScheme R F K eA (rationalArithmeticGaloisGroup a) σ j c},
              ∀ f, (e f).val = originalCoefficientRepresentationClass eT eA
                (rationalArithmeticGaloisGroup a) σ τ hτ
                (originalQuotientCoefficientRestriction eT eA J f).val) :=
  arithmeticUnframedDeterminantFiniteFlatUniversality_exists (L := L) a ha p hp hpa σ hσ i₀ δ hδ j m

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι : Type} [Fintype ι] [DecidableEq ι]

variable {O L : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]
  [Field L] [Algebra (IsLocalRing.ResidueField O) L] [IsAlgClosed L]

/-- Exact original-object consumer of `arithmeticPrimeDeterminantFiniteFlatUniversality_exists`. -/
theorem actual_arithmetic_prime_determinant_finite_flat_universality_arithmeticPrimeDeterminantFiniteFlatUniversality_exists_source
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ)
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L) σ))] (i₀ : ι)

    (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (m : FiniteFreeHopfPointModel.{0,0,0,0,0} (rationalPrimeLocalIntegerRing p hp) (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)
      (Multiplicative (ι → IsLocalRing.ResidueField O))
      (matrixUnderlyingGroupAction (σ.comp (rationalPrimeArithmeticRestriction a p hp).toMonoidHom))) :
    ∃ T : Subalgebra O (ArithmeticFramedUniversalRing a ha p hp hpa σ hσ),
      T = ArithmeticTraceCoefficientRing a ha p hp hpa σ hσ ∧
      (letI : IsTopologicalRing T := inferInstanceAs (IsTopologicalRing T.toSubring)
    ∃ hlocal : IsLocalRing T,
      letI := hlocal
      IsNoetherianRing T ∧ IsAdic (IsLocalRing.maximalIdeal T) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal T) T ∧
      ∃ (eT : IsLocalRing.ResidueField T ≃ₐ[O] IsLocalRing.ResidueField O)
        (τ : rationalArithmeticGaloisGroup a →ₜ* GeneralLinearGroup ι T)
        (hτ : (GeneralLinearGroup.map (localCoefficientReduction eT).toRingHom).comp
          τ.toMonoidHom = σ),
        let J := representationDeterminantIdeal τ.toMonoidHom δ ⊔
          matrixHopfModelCoefficientIdeal (rationalPrimeLocalIntegerRing p hp) (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp) (τ.toMonoidHom.comp (rationalPrimeArithmeticRestriction a p hp).toMonoidHom)
        ∃ hquot : IsLocalRing (T ⧸ J),
          letI := hquot
          IsNoetherianRing (T ⧸ J) ∧ IsAdic (IsLocalRing.maximalIdeal (T ⧸ J)) ∧
          IsAdicComplete (IsLocalRing.maximalIdeal (T ⧸ J)) (T ⧸ J) ∧
          ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
            [Algebra O A] [WithIdeal A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
            (_hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
            (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O),
            ∃ e : OriginalContinuousCoefficientFiber (originalLocalQuotientResidueEquiv eT J) eA ≃
              {c : OriginalUnframedDeformationClass eA (rationalArithmeticGaloisGroup a) σ //
                originalUnframedHasDeterminant eA (rationalArithmeticGaloisGroup a) σ δ c ∧
                  originalUnframedFiniteFlatScheme (rationalPrimeLocalIntegerRing p hp) (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp) eA (rationalArithmeticGaloisGroup a) σ (rationalPrimeArithmeticRestriction a p hp).toMonoidHom c},
              ∀ f, (e f).val = originalCoefficientRepresentationClass eT eA
                (rationalArithmeticGaloisGroup a) σ τ hτ
                (originalQuotientCoefficientRestriction eT eA J f).val) :=
  arithmeticPrimeDeterminantFiniteFlatUniversality_exists (L := L) a ha p hp hpa σ hσ i₀ δ hδ m

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι O : Type} [Fintype ι] [DecidableEq ι] [CommRing O] [IsLocalRing O]
  [TopologicalSpace (IsLocalRing.ResidueField O)] [DiscreteTopology (IsLocalRing.ResidueField O)]

/-- Exact original-object consumer of `relativeDualNumberFramedClass_eq_iff_cohomology`. -/
theorem actual_relative_dual_number_class_cohomology_relativeDualNumberFramedClass_eq_iff_cohomology_source
    (H : ProfiniteGrp) (ρ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hρ : Continuous ρ)
    (τ υ : {τ : MatrixFirstOrderLift ρ // Continuous τ.val}) :
    letI : WithIdeal (DualNumber (IsLocalRing.ResidueField O)) :=
      ⟨IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O))⟩
    originalUnframedClass (relativeDualNumberResidueEquiv O) H ρ
        (relativeDualNumberFramedFiberEquiv H ρ τ) =
      originalUnframedClass (relativeDualNumberResidueEquiv O) H ρ
        (relativeDualNumberFramedFiberEquiv H ρ υ) ↔
      continuousMatrixFirstOrderClass ρ hρ τ.val τ.property =
        continuousMatrixFirstOrderClass ρ hρ υ.val υ.property :=
  relativeDualNumberFramedClass_eq_iff_cohomology H ρ hρ τ υ

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι O : Type} [Fintype ι] [DecidableEq ι] [CommRing O] [IsLocalRing O]
  [TopologicalSpace (IsLocalRing.ResidueField O)] [DiscreteTopology (IsLocalRing.ResidueField O)]

/-- Exact original-object consumer of `relativeDualNumberUnframedCohomologyMap_bijective`. -/
theorem actual_relative_dual_number_unframed_cohomology_equiv_relativeDualNumberUnframedCohomologyMap_bijective_source
    (H : ProfiniteGrp) (ρ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hρ : Continuous ρ) :
    Function.Bijective (relativeDualNumberUnframedCohomologyMap H ρ hρ) :=
  relativeDualNumberUnframedCohomologyMap_bijective H ρ hρ

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι O A : Type} [Fintype ι] [DecidableEq ι] [CommRing O] [IsLocalRing O]
  [CommRing A] [IsLocalRing A] [Algebra O A] [TopologicalSpace A] [IsTopologicalRing A]
  [TopologicalSpace (IsLocalRing.ResidueField O)] [DiscreteTopology (IsLocalRing.ResidueField O)]

omit [IsTopologicalRing A] in
/-- Exact original-object consumer of `originalCotangentCohomologyClassLinearMap_coefficient`. -/
theorem actual_original_cotangent_cohomology_class_originalCotangentCohomologyClassLinearMap_coefficient_source
    (hA : (inferInstance : TopologicalSpace A) = (IsLocalRing.maximalIdeal A).adicTopology)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (τ : H →ₜ* GeneralLinearGroup ι A)
    (hτ : (GeneralLinearGroup.map (localCoefficientReduction eA).toRingHom).comp
      τ.toMonoidHom = σ) (d : OriginalResidueCotangentMaps eA) :
    letI : WithIdeal (DualNumber (IsLocalRing.ResidueField O)) :=
      ⟨IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O))⟩
    originalCotangentCohomologyClassLinearMap hA eA H σ hσ τ hτ d =
      relativeDualNumberUnframedCohomologyMap H σ hσ
        (originalCoefficientRepresentationClass eA (relativeDualNumberResidueEquiv O)
          H σ τ hτ (originalResidueCotangentContinuousFiberEquiv hA eA d)) :=
  originalCotangentCohomologyClassLinearMap_coefficient hA eA H σ hσ τ hτ d

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors

universe u

variable {ι O A : Type u} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [CommRing A] [IsLocalRing A] [Algebra O A]
  [TopologicalSpace A] [IsTopologicalRing A]

variable {B : Type u} [CommRing B] [IsLocalRing B] [Algebra O B] [WithIdeal B]

/-- Exact original-object consumer of `originalCoefficientQuotientRepresentation_class`. -/
theorem actual_original_coefficient_quotient_representation_originalCoefficientQuotientRepresentation_class_source
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (eB : IsLocalRing.ResidueField B ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u}) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (τ : H →ₜ* GeneralLinearGroup ι A)
    (hτ : (GeneralLinearGroup.map (localCoefficientReduction eA).toRingHom).comp
      τ.toMonoidHom = σ) (J : Ideal A) [IsLocalRing (A ⧸ J)]
    (f : OriginalContinuousCoefficientFiber (originalLocalQuotientResidueEquiv eA J) eB) :
    originalCoefficientRepresentationClass (originalLocalQuotientResidueEquiv eA J) eB H σ
        (originalCoefficientQuotientRepresentation H τ J)
        (originalCoefficientQuotientRepresentation_residue eA H σ τ hτ J) f =
      originalCoefficientRepresentationClass eA eB H σ τ hτ
        (originalQuotientCoefficientRestriction eA eB J f).val :=
  originalCoefficientQuotientRepresentation_class eA eB H σ τ hτ J f

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι O A : Type} [Fintype ι] [DecidableEq ι] [CommRing O] [IsLocalRing O]
  [CommRing A] [IsLocalRing A] [Algebra O A] [TopologicalSpace A] [IsTopologicalRing A]
  [TopologicalSpace (IsLocalRing.ResidueField O)] [DiscreteTopology (IsLocalRing.ResidueField O)]

omit [IsTopologicalRing A] in
/-- Exact original-object consumer of `originalCotangentCohomologyClassLinearMap_bijective`. -/
theorem actual_original_cotangent_cohomology_classification_originalCotangentCohomologyClassLinearMap_bijective_source
    [Finite (IsLocalRing.ResidueField O)]
    (hA : (inferInstance : TopologicalSpace A) = (IsLocalRing.maximalIdeal A).adicTopology)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (τ : H →ₜ* GeneralLinearGroup ι A)
    (hτ : (GeneralLinearGroup.map (localCoefficientReduction eA).toRingHom).comp
      τ.toMonoidHom = σ)
    (hbij : ∀ (B : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
      [Algebra O B] [WithIdeal B] [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
      (_hB : (WithIdeal.i : Ideal B) = IsLocalRing.maximalIdeal B)
      (eB : IsLocalRing.ResidueField B ≃ₐ[O] IsLocalRing.ResidueField O),
      Function.Bijective (originalCoefficientRepresentationClass eA eB H σ τ hτ)) :
    Function.Bijective (originalCotangentCohomologyClassLinearMap hA eA H σ hσ τ hτ) :=
  originalCotangentCohomologyClassLinearMap_bijective hA eA H σ hσ τ hτ hbij

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι : Type} [Fintype ι] [DecidableEq ι]

variable {O L : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]
  [Field L] [Algebra (IsLocalRing.ResidueField O) L] [IsAlgClosed L]

/-- Exact original-object consumer of `arithmeticTraceCotangentCohomology_exists`. -/
theorem actual_arithmetic_trace_cotangent_cohomology_arithmeticTraceCotangentCohomology_exists_source
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ)
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L) σ))] (i₀ : ι) :
    ∃ T : Subalgebra O (ArithmeticFramedUniversalRing a ha p hp hpa σ hσ),
      T = ArithmeticTraceCoefficientRing a ha p hp hpa σ hσ ∧
      (letI : IsTopologicalRing T := inferInstanceAs (IsTopologicalRing T.toSubring)
       ∃ hlocal : IsLocalRing T,
         letI := hlocal
         IsNoetherianRing T ∧ ∃ htop : IsAdic (IsLocalRing.maximalIdeal T),
         IsAdicComplete (IsLocalRing.maximalIdeal T) T ∧
         ∃ (eT : IsLocalRing.ResidueField T ≃ₐ[O] IsLocalRing.ResidueField O)
           (τ : rationalArithmeticGaloisGroup a →ₜ* GeneralLinearGroup ι T)
           (hτ : (GeneralLinearGroup.map (localCoefficientReduction eT).toRingHom).comp
             τ.toMonoidHom = σ),
           Function.Bijective (originalCotangentCohomologyClassLinearMap htop eT
             (rationalArithmeticGaloisGroup a) σ hσ τ hτ)) :=
  arithmeticTraceCotangentCohomology_exists (L := L) a ha p hp hpa σ hσ i₀

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {R F K ι O A : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]
  [Fintype ι] [DecidableEq ι] [CommRing O] [IsLocalRing O]
  [Finite (IsLocalRing.ResidueField O)]
  [TopologicalSpace (IsLocalRing.ResidueField O)] [DiscreteTopology (IsLocalRing.ResidueField O)]
  [CommRing A] [IsLocalRing A] [Algebra O A] [TopologicalSpace A]
  [IsTopologicalRing A]

/-- Exact original-object consumer of `originalResidualDeterminantFiniteFlatCotangent_classification`. -/
theorem actual_original_determinant_finite_flat_cotangent_image_originalResidualDeterminantFiniteFlatCotangent_classification_source
    [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (hA : IsAdic (IsLocalRing.maximalIdeal A))
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (τ : H →ₜ* GeneralLinearGroup ι A)
    (hτ : (GeneralLinearGroup.map (localCoefficientReduction eA).toRingHom).comp
      τ.toMonoidHom = σ)
    (δ : H →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (j : (K ≃ₐ[F] K) →* H)
    (m : FiniteFreeHopfPointModel.{0,0,0,0,0} R F K
      (Multiplicative (ι → IsLocalRing.ResidueField O))
      (matrixUnderlyingGroupAction (σ.comp j)))
    (hwhole : ∀ (B : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
      [Algebra O B] [WithIdeal B] [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
      (_hB : (WithIdeal.i : Ideal B) = IsLocalRing.maximalIdeal B)
      (eB : IsLocalRing.ResidueField B ≃ₐ[O] IsLocalRing.ResidueField O),
      Function.Bijective (originalCoefficientRepresentationClass eA eB H σ τ hτ)) :
    let J := representationDeterminantIdeal τ.toMonoidHom δ ⊔
      matrixHopfModelCoefficientIdeal R F K (τ.toMonoidHom.comp j)
    ∃ hquot : IsLocalRing (A ⧸ J),
      letI := hquot
      IsNoetherianRing (A ⧸ J) ∧ ∃ hQ : IsAdic (IsLocalRing.maximalIdeal (A ⧸ J)),
        IsAdicComplete (IsLocalRing.maximalIdeal (A ⧸ J)) (A ⧸ J) ∧
        (let eQ := originalLocalQuotientResidueEquiv eA J
         let τQ := originalCoefficientQuotientRepresentation H τ J
         let hτQ := originalCoefficientQuotientRepresentation_residue eA H σ τ hτ J
         let LQ := originalCotangentCohomologyClassLinearMap hQ eQ H σ hσ τQ hτQ
         Function.Injective LQ ∧ ∀ x : ContinuousMatrixAdjointH1 σ hσ,
           x ∈ LinearMap.range LQ ↔
             (letI : WithIdeal (DualNumber (IsLocalRing.ResidueField O)) :=
                ⟨IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O))⟩
              ∃ c : OriginalUnframedDeformationClass (relativeDualNumberResidueEquiv O) H σ,
                (originalUnframedHasDeterminant (relativeDualNumberResidueEquiv O) H σ δ c ∧
                  originalUnframedFiniteFlatScheme R F K
                    (relativeDualNumberResidueEquiv O) H σ j c) ∧
                relativeDualNumberUnframedCohomologyMap H σ hσ c = x)) :=
  originalResidualDeterminantFiniteFlatCotangent_classification hA eA H σ hσ τ hτ δ hδ j m hwhole

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {R F K : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]

variable {ι : Type} [Fintype ι] [DecidableEq ι]

variable {O L : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]
  [Field L] [Algebra (IsLocalRing.ResidueField O) L] [IsAlgClosed L]

/-- Exact original-object consumer of `arithmeticDeterminantFiniteFlatCotangent_exists`. -/
theorem actual_arithmetic_determinant_finite_flat_cotangent_arithmeticDeterminantFiniteFlatCotangent_exists_source
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ)
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L) σ))] (i₀ : ι)
    (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (j : (K ≃ₐ[F] K) →* rationalArithmeticGaloisGroup a)
    (m : FiniteFreeHopfPointModel.{0,0,0,0,0} R F K
      (Multiplicative (ι → IsLocalRing.ResidueField O))
      (matrixUnderlyingGroupAction (σ.comp j)))
    :
    ∃ T : Subalgebra O (ArithmeticFramedUniversalRing a ha p hp hpa σ hσ),
      T = ArithmeticTraceCoefficientRing a ha p hp hpa σ hσ ∧
      (letI : IsTopologicalRing T := inferInstanceAs (IsTopologicalRing T.toSubring)
       ∃ hlocal : IsLocalRing T,
         letI := hlocal
         IsNoetherianRing T ∧ ∃ _htop : IsAdic (IsLocalRing.maximalIdeal T),
         IsAdicComplete (IsLocalRing.maximalIdeal T) T ∧
         ∃ (eT : IsLocalRing.ResidueField T ≃ₐ[O] IsLocalRing.ResidueField O)
           (τ : rationalArithmeticGaloisGroup a →ₜ* GeneralLinearGroup ι T)
           (hτ : (GeneralLinearGroup.map (localCoefficientReduction eT).toRingHom).comp
             τ.toMonoidHom = σ),
           (let J := representationDeterminantIdeal τ.toMonoidHom δ ⊔
              matrixHopfModelCoefficientIdeal R F K (τ.toMonoidHom.comp j)
            ∃ hquot : IsLocalRing (T ⧸ J),
              letI := hquot
              IsNoetherianRing (T ⧸ J) ∧ ∃ hQ : IsAdic (IsLocalRing.maximalIdeal (T ⧸ J)),
                IsAdicComplete (IsLocalRing.maximalIdeal (T ⧸ J)) (T ⧸ J) ∧
                (let eQ := originalLocalQuotientResidueEquiv eT J
                 let τQ := originalCoefficientQuotientRepresentation (rationalArithmeticGaloisGroup a) τ J
                 let hτQ := originalCoefficientQuotientRepresentation_residue eT (rationalArithmeticGaloisGroup a) σ τ hτ J
                 let LQ := originalCotangentCohomologyClassLinearMap hQ eQ (rationalArithmeticGaloisGroup a) σ hσ τQ hτQ
                 Function.Injective LQ ∧ ∀ x : ContinuousMatrixAdjointH1 σ hσ,
                   x ∈ LinearMap.range LQ ↔
                     (letI : WithIdeal (DualNumber (IsLocalRing.ResidueField O)) :=
                        ⟨IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O))⟩
                      ∃ c : OriginalUnframedDeformationClass (relativeDualNumberResidueEquiv O) (rationalArithmeticGaloisGroup a) σ,
                        (originalUnframedHasDeterminant (relativeDualNumberResidueEquiv O) (rationalArithmeticGaloisGroup a) σ δ c ∧
                          originalUnframedFiniteFlatScheme R F K
                            (relativeDualNumberResidueEquiv O) (rationalArithmeticGaloisGroup a) σ j c) ∧
                        relativeDualNumberUnframedCohomologyMap (rationalArithmeticGaloisGroup a) σ hσ c = x)))) :=
  arithmeticDeterminantFiniteFlatCotangent_exists (L := L) a ha p hp hpa σ hσ i₀ δ hδ j m

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι : Type} [Fintype ι] [DecidableEq ι]

variable {O L : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]
  [Field L] [Algebra (IsLocalRing.ResidueField O) L] [IsAlgClosed L]

/-- Exact original-object consumer of `arithmeticPrimeDeterminantFiniteFlatCotangent_exists`. -/
theorem actual_arithmetic_prime_determinant_finite_flat_cotangent_arithmeticPrimeDeterminantFiniteFlatCotangent_exists_source
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ)
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L) σ))] (i₀ : ι)
    (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (m : FiniteFreeHopfPointModel.{0,0,0,0,0} (rationalPrimeLocalIntegerRing p hp) (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)
      (Multiplicative (ι → IsLocalRing.ResidueField O))
      (matrixUnderlyingGroupAction (σ.comp (rationalPrimeArithmeticRestriction a p hp).toMonoidHom)))
    :
    ∃ T : Subalgebra O (ArithmeticFramedUniversalRing a ha p hp hpa σ hσ),
      T = ArithmeticTraceCoefficientRing a ha p hp hpa σ hσ ∧
      (letI : IsTopologicalRing T := inferInstanceAs (IsTopologicalRing T.toSubring)
       ∃ hlocal : IsLocalRing T,
         letI := hlocal
         IsNoetherianRing T ∧ ∃ _htop : IsAdic (IsLocalRing.maximalIdeal T),
         IsAdicComplete (IsLocalRing.maximalIdeal T) T ∧
         ∃ (eT : IsLocalRing.ResidueField T ≃ₐ[O] IsLocalRing.ResidueField O)
           (τ : rationalArithmeticGaloisGroup a →ₜ* GeneralLinearGroup ι T)
           (hτ : (GeneralLinearGroup.map (localCoefficientReduction eT).toRingHom).comp
             τ.toMonoidHom = σ),
           (let J := representationDeterminantIdeal τ.toMonoidHom δ ⊔
              matrixHopfModelCoefficientIdeal (rationalPrimeLocalIntegerRing p hp) (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp) (τ.toMonoidHom.comp (rationalPrimeArithmeticRestriction a p hp).toMonoidHom)
            ∃ hquot : IsLocalRing (T ⧸ J),
              letI := hquot
              IsNoetherianRing (T ⧸ J) ∧ ∃ hQ : IsAdic (IsLocalRing.maximalIdeal (T ⧸ J)),
                IsAdicComplete (IsLocalRing.maximalIdeal (T ⧸ J)) (T ⧸ J) ∧
                (let eQ := originalLocalQuotientResidueEquiv eT J
                 let τQ := originalCoefficientQuotientRepresentation (rationalArithmeticGaloisGroup a) τ J
                 let hτQ := originalCoefficientQuotientRepresentation_residue eT (rationalArithmeticGaloisGroup a) σ τ hτ J
                 let LQ := originalCotangentCohomologyClassLinearMap hQ eQ (rationalArithmeticGaloisGroup a) σ hσ τQ hτQ
                 Function.Injective LQ ∧ ∀ x : ContinuousMatrixAdjointH1 σ hσ,
                   x ∈ LinearMap.range LQ ↔
                     (letI : WithIdeal (DualNumber (IsLocalRing.ResidueField O)) :=
                        ⟨IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O))⟩
                      ∃ c : OriginalUnframedDeformationClass (relativeDualNumberResidueEquiv O) (rationalArithmeticGaloisGroup a) σ,
                        (originalUnframedHasDeterminant (relativeDualNumberResidueEquiv O) (rationalArithmeticGaloisGroup a) σ δ c ∧
                          originalUnframedFiniteFlatScheme (rationalPrimeLocalIntegerRing p hp) (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)
                            (relativeDualNumberResidueEquiv O) (rationalArithmeticGaloisGroup a) σ (rationalPrimeArithmeticRestriction a p hp).toMonoidHom c) ∧
                        relativeDualNumberUnframedCohomologyMap (rationalArithmeticGaloisGroup a) σ hσ c = x)))) :=
  arithmeticPrimeDeterminantFiniteFlatCotangent_exists (L := L) a ha p hp hpa σ hσ i₀ δ hδ m

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {R F K ι O A : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]
  [Fintype ι] [DecidableEq ι] [CommRing O] [IsLocalRing O]
  [Finite (IsLocalRing.ResidueField O)]
  [TopologicalSpace (IsLocalRing.ResidueField O)] [DiscreteTopology (IsLocalRing.ResidueField O)]
  [CommRing A] [IsLocalRing A] [Algebra O A] [TopologicalSpace A]
  [IsTopologicalRing A]

/-- Exact original-object consumer of `originalGeometricFiniteFlatCohomologySubmodule_existsUnique`. -/
theorem actual_original_geometric_finite_flat_cohomology_submodule_originalGeometricFiniteFlatCohomologySubmodule_existsUnique_source
    [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (hA : IsAdic (IsLocalRing.maximalIdeal A))
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (τ : H →ₜ* GeneralLinearGroup ι A)
    (hτ : (GeneralLinearGroup.map (localCoefficientReduction eA).toRingHom).comp
      τ.toMonoidHom = σ)
    (δ : H →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (j : (K ≃ₐ[F] K) →* H)
    (m : FiniteFreeHopfPointModel.{0,0,0,0,0} R F K
      (Multiplicative (ι → IsLocalRing.ResidueField O))
      (matrixUnderlyingGroupAction (σ.comp j)))
    (hwhole : ∀ (B : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
      [Algebra O B] [WithIdeal B] [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
      (_hB : (WithIdeal.i : Ideal B) = IsLocalRing.maximalIdeal B)
      (eB : IsLocalRing.ResidueField B ≃ₐ[O] IsLocalRing.ResidueField O),
      Function.Bijective (originalCoefficientRepresentationClass eA eB H σ τ hτ)) :
    ∃! S : Submodule (IsLocalRing.ResidueField O) (ContinuousMatrixAdjointH1 σ hσ),
      ∀ x, x ∈ S ↔ x ∈ originalGeometricFiniteFlatCohomologyCondition
        (R := R) H σ hσ δ j :=
  originalGeometricFiniteFlatCohomologySubmodule_existsUnique hA eA H σ hσ τ hτ δ hδ j m hwhole

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι : Type} [Fintype ι] [DecidableEq ι]

variable {O L : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]
  [Field L] [Algebra (IsLocalRing.ResidueField O) L] [IsAlgClosed L]

/-- Exact original-object consumer of `arithmeticPrimeGeometricFiniteFlatCohomology_existsUnique`. -/
theorem actual_arithmetic_prime_geometric_finite_flat_cohomology_arithmeticPrimeGeometricFiniteFlatCohomology_existsUnique_source
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ)
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L) σ))] (i₀ : ι)
    (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (m : FiniteFreeHopfPointModel.{0,0,0,0,0} (rationalPrimeLocalIntegerRing p hp) (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)
      (Multiplicative (ι → IsLocalRing.ResidueField O))
      (matrixUnderlyingGroupAction (σ.comp (rationalPrimeArithmeticRestriction a p hp).toMonoidHom)))
    :
    ∃! S : Submodule (IsLocalRing.ResidueField O) (ContinuousMatrixAdjointH1 σ hσ),
      (∀ x, x ∈ S ↔ x ∈ originalGeometricFiniteFlatCohomologyCondition
        (R := rationalPrimeLocalIntegerRing p hp) (rationalArithmeticGaloisGroup a) σ hσ δ
        (rationalPrimeArithmeticRestriction a p hp).toMonoidHom) ∧
      Module.Finite (IsLocalRing.ResidueField O) S :=
  arithmeticPrimeGeometricFiniteFlatCohomology_existsUnique (L := L) a ha p hp hpa σ hσ i₀ δ hδ m

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι O : Type} [Fintype ι] [DecidableEq ι] [CommRing O] [IsLocalRing O]
  [TopologicalSpace (IsLocalRing.ResidueField O)] [DiscreteTopology (IsLocalRing.ResidueField O)]

/-- Exact original-object consumer of `relativeDualNumberUnframedHasDeterminant_iff`. -/
theorem actual_relative_dual_number_determinant_cohomology_relativeDualNumberUnframedHasDeterminant_iff_source
    (H : ProfiniteGrp) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : H →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g)) :
    letI : WithIdeal (DualNumber (IsLocalRing.ResidueField O)) :=
      ⟨IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O))⟩
    ∀ c : OriginalUnframedDeformationClass (relativeDualNumberResidueEquiv O) H σ,
      originalUnframedHasDeterminant (relativeDualNumberResidueEquiv O) H σ δ c ↔
        relativeDualNumberUnframedCohomologyMap H σ hσ c ∈
          continuousFixedDeterminantClasses σ hσ :=
  relativeDualNumberUnframedHasDeterminant_iff H σ hσ δ hδ

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι : Type} [Fintype ι] [DecidableEq ι]

variable {O L : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]
  [Field L] [Algebra (IsLocalRing.ResidueField O) L] [IsAlgClosed L]

variable (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ)
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L) σ))] (i₀ : ι)
    (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (m : FiniteFreeHopfPointModel.{0,0,0,0,0} (rationalPrimeLocalIntegerRing p hp) (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)
      (Multiplicative (ι → IsLocalRing.ResidueField O))
      (matrixUnderlyingGroupAction (σ.comp (rationalPrimeArithmeticRestriction a p hp).toMonoidHom)))

/-- Exact original-object consumer of `arithmeticPrimeGeometricFiniteFlatClasses_le_fixedDeterminant`. -/
theorem actual_arithmetic_prime_geometric_cohomology_submodule_arithmeticPrimeGeometricFiniteFlatClasses_le_fixedDeterminant_source :
    (arithmeticPrimeGeometricFiniteFlatClasses (L := L) a ha p hp hpa σ hσ i₀ δ hδ m) ≤ continuousFixedDeterminantClasses σ hσ :=
  arithmeticPrimeGeometricFiniteFlatClasses_le_fixedDeterminant (L := L) a ha p hp hpa σ hσ i₀ δ hδ m

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι : Type} [Fintype ι] [DecidableEq ι]

variable {O L : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]
  [Field L] [Algebra (IsLocalRing.ResidueField O) L] [IsAlgClosed L]

variable (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ)
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L) σ))] (i₀ : ι)
    (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (m : FiniteFreeHopfPointModel.{0,0,0,0,0} (rationalPrimeLocalIntegerRing p hp) (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)
      (Multiplicative (ι → IsLocalRing.ResidueField O))
      (matrixUnderlyingGroupAction (σ.comp (rationalPrimeArithmeticRestriction a p hp).toMonoidHom)))

/-- Exact original-object consumer of `arithmeticPrimeGeometricTraceZeroClasses_finrank`. -/
theorem actual_arithmetic_prime_geometric_trace_zero_cohomology_arithmeticPrimeGeometricTraceZeroClasses_finrank_source
    (hn : (Fintype.card ι : IsLocalRing.ResidueField O) ≠ 0) :
    Module.finrank (IsLocalRing.ResidueField O) (arithmeticPrimeGeometricTraceZeroClasses (L := L) a ha p hp hpa σ hσ i₀ δ hδ m) =
      Module.finrank (IsLocalRing.ResidueField O) (arithmeticPrimeGeometricFiniteFlatClasses (L := L) a ha p hp hpa σ hσ i₀ δ hδ m) :=
  arithmeticPrimeGeometricTraceZeroClasses_finrank (L := L) a ha p hp hpa σ hσ i₀ δ hδ m hn

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable (R F K : Type) {ι k : Type}
  [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [Field F] [Field K]
  [Algebra R F] [Algebra F K] [Algebra R K] [IsScalarTower R F K]
  [Fintype ι] [DecidableEq ι] [Field k] [TopologicalSpace k] [IsTopologicalRing k]

variable {R F K}

/-- Exact original-object consumer of `localGeometricFiniteFlatCohomologyCondition_class_iff`. -/
theorem actual_local_geometric_finite_flat_cohomology_localGeometricFiniteFlatCohomologyCondition_class_iff_source
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι k) (hρ : Continuous ρ)
    (τ : MatrixFirstOrderLift ρ) (hτ : Continuous τ.val) :
    continuousMatrixFirstOrderClass ρ hρ τ hτ ∈
        localGeometricFiniteFlatCohomologyCondition R F K ρ hρ ↔
      MatrixAdicFiniteFlatScheme R F K τ.val :=
  localGeometricFiniteFlatCohomologyCondition_class_iff (R := R) ρ hρ τ hτ

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {R F K ι O : Type}
  [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [Field F] [Field K]
  [Algebra R F] [Algebra F K] [Algebra R K] [IsScalarTower R F K]
  [Fintype ι] [DecidableEq ι] [CommRing O] [IsLocalRing O]
  [TopologicalSpace (IsLocalRing.ResidueField O)] [DiscreteTopology (IsLocalRing.ResidueField O)]

/-- Exact original-object consumer of `originalGeometricFiniteFlatCohomologyCondition_restriction_iff`. -/
theorem actual_original_geometric_cohomology_restriction_originalGeometricFiniteFlatCohomologyCondition_restriction_iff_source
    (H : ProfiniteGrp) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : H →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (j : (K ≃ₐ[F] K) →* H) (hj : Continuous j)
    (x : ContinuousMatrixAdjointH1 σ hσ) :
    x ∈ originalGeometricFiniteFlatCohomologyCondition (R := R) H σ hσ δ j ↔
      x ∈ continuousFixedDeterminantClasses σ hσ ∧
        continuousMatrixAdjointH1Restriction σ hσ j hj x ∈
          localGeometricFiniteFlatCohomologyCondition R F K (σ.comp j) (hσ.comp hj) :=
  originalGeometricFiniteFlatCohomologyCondition_restriction_iff (R := R) H σ hσ δ hδ j hj x

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι : Type} [Fintype ι] [DecidableEq ι]

variable {O L : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]
  [Field L] [Algebra (IsLocalRing.ResidueField O) L] [IsAlgClosed L]

variable (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ)
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L) σ))] (i₀ : ι)
    (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (m : FiniteFreeHopfPointModel.{0,0,0,0,0} (rationalPrimeLocalIntegerRing p hp) (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)
      (Multiplicative (ι → IsLocalRing.ResidueField O))
      (matrixUnderlyingGroupAction (σ.comp (rationalPrimeArithmeticRestriction a p hp).toMonoidHom)))

/-- Exact original-object consumer of `arithmeticPrimeGeometricFiniteFlatClasses_restriction_iff`. -/
theorem actual_arithmetic_prime_geometric_cohomology_restriction_arithmeticPrimeGeometricFiniteFlatClasses_restriction_iff_source
    (x : ContinuousMatrixAdjointH1 σ hσ) :
    x ∈ arithmeticPrimeGeometricFiniteFlatClasses (L := L) a ha p hp hpa σ hσ i₀ δ hδ m ↔
      x ∈ continuousFixedDeterminantClasses σ hσ ∧
        continuousMatrixAdjointH1Restriction σ hσ
          (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
          (rationalPrimeArithmeticRestriction a p hp).continuous x ∈
            localGeometricFiniteFlatCohomologyCondition
              (rationalPrimeLocalIntegerRing p hp) (rationalPrimeLocalField p hp)
              (rationalPrimeLocalClosure p hp)
              (σ.comp (rationalPrimeArithmeticRestriction a p hp).toMonoidHom)
              (hσ.comp (rationalPrimeArithmeticRestriction a p hp).continuous) :=
  arithmeticPrimeGeometricFiniteFlatClasses_restriction_iff (L := L) a ha p hp hpa σ hσ i₀ δ hδ m x

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι : Type} [Fintype ι] [DecidableEq ι]

variable {O L : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]
  [Field L] [Algebra (IsLocalRing.ResidueField O) L] [IsAlgClosed L]

variable (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ)
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L) σ))] (i₀ : ι)
    (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (m : FiniteFreeHopfPointModel.{0,0,0,0,0} (rationalPrimeLocalIntegerRing p hp) (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)
      (Multiplicative (ι → IsLocalRing.ResidueField O))
      (matrixUnderlyingGroupAction (σ.comp (rationalPrimeArithmeticRestriction a p hp).toMonoidHom)))

/-- Exact original-object consumer of `arithmeticPrimeGeometricTraceZeroClasses_restriction_iff`. -/
theorem actual_arithmetic_prime_geometric_trace_zero_restriction_arithmeticPrimeGeometricTraceZeroClasses_restriction_iff_source
    (x : ContinuousTraceZeroAdjointH1 σ hσ) :
    x ∈ arithmeticPrimeGeometricTraceZeroClasses (L := L) a ha p hp hpa σ hσ i₀ δ hδ m ↔
      continuousTraceZeroH1Inclusion
        (σ.comp (rationalPrimeArithmeticRestriction a p hp).toMonoidHom)
        (hσ.comp (rationalPrimeArithmeticRestriction a p hp).continuous)
        (continuousTraceZeroH1Restriction σ hσ
          (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
          (rationalPrimeArithmeticRestriction a p hp).continuous x) ∈
        localGeometricFiniteFlatCohomologyCondition
          (rationalPrimeLocalIntegerRing p hp) (rationalPrimeLocalField p hp)
          (rationalPrimeLocalClosure p hp)
          (σ.comp (rationalPrimeArithmeticRestriction a p hp).toMonoidHom)
          (hσ.comp (rationalPrimeArithmeticRestriction a p hp).continuous) :=
  arithmeticPrimeGeometricTraceZeroClasses_restriction_iff (L := L) a ha p hp hpa σ hσ i₀ δ hδ m x

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable (k : Type) [CommRing k]

/-- Exact original-object consumer of `dualNumberCompatibleAddition_components`. -/
theorem actual_dual_number_coefficient_operations_dualNumberCompatibleAddition_components_source
    (x : CoefficientFiberProduct (TrivSqZeroExt.fstHom k k k).toRingHom
      (TrivSqZeroExt.fstHom k k k).toRingHom) :
    (dualNumberCompatibleAddition k x).fst = x.val.1.fst ∧
      (dualNumberCompatibleAddition k x).snd = x.val.1.snd + x.val.2.snd :=
  dualNumberCompatibleAddition_components k x

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι k : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing k]

/-- Exact original-object consumer of `matrixFirstOrderSum_cocycle`. -/
theorem actual_first_order_coefficient_addition_matrixFirstOrderSum_cocycle_source (ρ : G →* GeneralLinearGroup ι k)
    (τ υ : MatrixFirstOrderLift ρ) :
    matrixFirstOrderCocycle ρ (matrixFirstOrderSum ρ τ υ) =
      matrixFirstOrderCocycle ρ τ + matrixFirstOrderCocycle ρ υ :=
  matrixFirstOrderSum_cocycle ρ τ υ

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {R F K ι k : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]
  [Fintype ι] [DecidableEq ι] [Field k] [Finite k]

/-- Exact original-object consumer of `matrixFirstOrderSum_finiteFlatScheme`. -/
theorem actual_first_order_addition_finite_flat_model_matrixFirstOrderSum_finiteFlatScheme_source
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι k)
    (τ υ : MatrixFirstOrderLift ρ)
    (hτ : MatrixAdicFiniteFlatScheme R F K τ.val)
    (hυ : MatrixAdicFiniteFlatScheme R F K υ.val) :
    MatrixAdicFiniteFlatScheme R F K (matrixFirstOrderSum ρ τ υ).val :=
  matrixFirstOrderSum_finiteFlatScheme (R := R) ρ τ υ hτ hυ

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι k : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing k]

/-- Exact original-object consumer of `matrixFirstOrderScale_cocycle`. -/
theorem actual_first_order_coefficient_scaling_matrixFirstOrderScale_cocycle_source (ρ : G →* GeneralLinearGroup ι k)
    (c : k) (τ : MatrixFirstOrderLift ρ) :
    matrixFirstOrderCocycle ρ (matrixFirstOrderScale ρ c τ) =
      c • matrixFirstOrderCocycle ρ τ :=
  matrixFirstOrderScale_cocycle ρ c τ

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {R F K ι k : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]
  [Fintype ι] [DecidableEq ι] [Field k] [Finite k]

/-- Exact original-object consumer of `matrixFirstOrderZero_finiteFlatScheme`. -/
theorem actual_first_order_scaling_finite_flat_model_matrixFirstOrderZero_finiteFlatScheme_source
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι k)
    (m : FiniteFreeHopfPointModel.{0,0,0,0,0} R F K (Multiplicative (ι → k))
      (matrixUnderlyingGroupAction ρ)) :
    MatrixAdicFiniteFlatScheme R F K (firstOrderLiftFromCocycle ρ 0).val :=
  matrixFirstOrderZero_finiteFlatScheme (R := R) ρ m

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι k : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing k]
  [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace k] [IsTopologicalRing k]

/-- Exact original-object consumer of `continuousMatrixFirstOrderClass_sum`. -/
theorem actual_first_order_coefficient_class_operations_continuousMatrixFirstOrderClass_sum_source
    (ρ : G →* GeneralLinearGroup ι k) (hρ : Continuous ρ)
    (τ υ : MatrixFirstOrderLift ρ) (hτ : Continuous τ.val) (hυ : Continuous υ.val) :
    continuousMatrixFirstOrderClass ρ hρ (matrixFirstOrderSum ρ τ υ)
        (matrixFirstOrderSum_continuous ρ hρ τ υ hτ hυ) =
      continuousMatrixFirstOrderClass ρ hρ τ hτ + continuousMatrixFirstOrderClass ρ hρ υ hυ :=
  continuousMatrixFirstOrderClass_sum ρ hρ τ υ hτ hυ

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {R F K ι k : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]
  [Fintype ι] [DecidableEq ι] [Field k] [Finite k]
  [TopologicalSpace k] [IsTopologicalRing k]

/-- Exact original-object consumer of `localGeometricFiniteFlatCohomologySubmodule_existsUnique`. -/
theorem actual_local_geometric_finite_flat_linearity_localGeometricFiniteFlatCohomologySubmodule_existsUnique_source
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι k) (hρ : Continuous ρ)
    (m : FiniteFreeHopfPointModel.{0,0,0,0,0} R F K (Multiplicative (ι → k))
      (matrixUnderlyingGroupAction ρ)) :
    ∃! S : Submodule k (ContinuousMatrixAdjointH1 ρ hρ),
      ∀ x, x ∈ S ↔ x ∈ localGeometricFiniteFlatCohomologyCondition R F K ρ hρ :=
  localGeometricFiniteFlatCohomologySubmodule_existsUnique (R := R) ρ hρ m

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι : Type} [Fintype ι] [DecidableEq ι]

variable {O L : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]
  [Field L] [Algebra (IsLocalRing.ResidueField O) L] [IsAlgClosed L]

variable (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ)
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L) σ))] (i₀ : ι)
    (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (m : FiniteFreeHopfPointModel.{0,0,0,0,0} (rationalPrimeLocalIntegerRing p hp) (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)
      (Multiplicative (ι → IsLocalRing.ResidueField O))
      (matrixUnderlyingGroupAction (σ.comp (rationalPrimeArithmeticRestriction a p hp).toMonoidHom)))

/-- Exact original-object consumer of `arithmeticPrimeGeometricClasses_localization`. -/
theorem actual_arithmetic_prime_geometric_localization_arithmeticPrimeGeometricClasses_localization_source
    :
    letI : CharZero (rationalPrimeLocalField p hp) :=
      Algebra.charZero_of_charZero (R := ℚ) (A := rationalPrimeLocalField p hp)
    let j := rationalPrimeArithmeticRestriction a p hp
    let S := localGeometricFiniteFlatCohomologySubmodule (σ.comp j.toMonoidHom)
      (hσ.comp j.continuous) m
    arithmeticPrimeGeometricFiniteFlatClasses (L := L) a ha p hp hpa σ hσ i₀ δ hδ m =
        continuousFixedDeterminantLocalPreimage σ hσ j.toMonoidHom j.continuous S ∧
      arithmeticPrimeGeometricTraceZeroClasses (L := L) a ha p hp hpa σ hσ i₀ δ hδ m =
        continuousTraceZeroLocalPreimage σ hσ j.toMonoidHom j.continuous S :=
  arithmeticPrimeGeometricClasses_localization (L := L) a ha p hp hpa σ hσ i₀ δ hδ m

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι R : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]

/-- Exact original-object consumer of `fullMatrixTracePairing_adjoint`. -/
theorem actual_full_adjoint_trace_duality_fullMatrixTracePairing_adjoint_source
    (ρ : G →* GeneralLinearGroup ι R) (g : G) (X : Matrix ι ι R) :
    fullMatrixTracePairing (matrixAdjointRepresentation ρ g X) =
      (matrixAdjointRepresentation ρ).dual g (fullMatrixTracePairing X) :=
  fullMatrixTracePairing_adjoint ρ g X

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι K : Type} [Group G] [Fintype ι] [DecidableEq ι] [Field K]

/-- Exact original-object consumer of `matrixTraceZeroTracePairing_bijective`. -/
theorem actual_trace_zero_adjoint_duality_matrixTraceZeroTracePairing_bijective_source (hn : (Fintype.card ι : K) ≠ 0) :
    Function.Bijective (matrixTraceZeroTracePairing (ι := ι) (K := K)) :=
  matrixTraceZeroTracePairing_bijective hn

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable {n : ℕ} [NeZero n] {μ : K}

/-- Exact original-object consumer of `primitiveRootCyclotomicCharacter_continuous`. -/
theorem actual_primitive_root_cyclotomic_continuity_primitiveRootCyclotomicCharacter_continuous_source [Algebra.IsIntegral F K]
    (hμ : IsPrimitiveRoot μ n) : Continuous (hμ.autToPow F) :=
  primitiveRootCyclotomicCharacter_continuous hμ

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors




/-- Exact original-object consumer of `rationalArithmeticCyclotomicCharacter_apply_root`. -/
theorem actual_rational_arithmetic_cyclotomic_character_rationalArithmeticCyclotomicCharacter_apply_root_source
    (a : 𝓞 ℚ) (n : ℕ) [NeZero n] (hna : (n : 𝓞 ℚ) ∣ a)
    (g : rationalArithmeticGaloisGroup a)
    {ζ : rationalUnramifiedExtension a} (hζ : IsPrimitiveRoot ζ n) :
    (let U := rationalUnramifiedExtension a
     letI : Algebra ℚ U := U.algebra'
     (show U ≃ₐ[ℚ] U from g) ζ) =
      ζ ^ (rationalArithmeticCyclotomicCharacter a n hna g : ZMod n).val :=
  rationalArithmeticCyclotomicCharacter_apply_root a n hna g hζ

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {R G V W : Type} [CommRing R] [Group G]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/-- Exact original-object consumer of `coefficientCharacterTwist_dual_eq_linHom`. -/
theorem actual_coefficient_character_twist_coefficientCharacterTwist_dual_eq_linHom_source
    (ρ : Representation R G V) (χ : G →* R) :
    coefficientCharacterTwist ρ.dual χ =
      Representation.linHom ρ (coefficientCharacterTwist (1 : Representation R G R) χ) :=
  coefficientCharacterTwist_dual_eq_linHom ρ χ

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι K : Type} [Group G] [Fintype ι] [DecidableEq ι] [Field K]

/-- Exact original-object consumer of `matrixTraceZeroCharacterPairing_equivariant`. -/
theorem actual_trace_zero_twisted_duality_matrixTraceZeroCharacterPairing_equivariant_source
    (ρ : G →* GeneralLinearGroup ι K) (χ : G →* K) (g : G)
    (X Y : matrixTraceZeroSubmodule ι K) :
    Matrix.trace ((coefficientCharacterTwist (matrixTraceZeroAdjointRepresentation ρ) χ g X).val *
        (matrixTraceZeroAdjointRepresentation ρ g Y).val) =
      χ g * Matrix.trace (X.val * Y.val) :=
  matrixTraceZeroCharacterPairing_equivariant ρ χ g X Y

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors




/-- Exact original-object consumer of `rationalPrimeCyclotomicCharacter_apply_root`. -/
theorem actual_rational_prime_cyclotomic_character_rationalPrimeCyclotomicCharacter_apply_root_source
    (p : ℕ) (hp : p.Prime) (n : ℕ) [NeZero n]
    (g : rationalPrimeLocalClosure p hp ≃ₐ[rationalPrimeLocalField p hp]
      rationalPrimeLocalClosure p hp)
    {ζ : rationalPrimeLocalClosure p hp} (hζ : IsPrimitiveRoot ζ n) :
    g ζ = ζ ^ (rationalPrimeCyclotomicCharacter p hp n g : ZMod n).val :=
  rationalPrimeCyclotomicCharacter_apply_root p hp n g hζ

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors




/-- Exact original-object consumer of `rationalArithmeticCyclotomicCharacter_restriction`. -/
theorem actual_arithmetic_cyclotomic_restriction_rationalArithmeticCyclotomicCharacter_restriction_source
    (a : 𝓞 ℚ) (n : ℕ) [NeZero n] (hna : (n : 𝓞 ℚ) ∣ a)
    (p : ℕ) (hp : p.Prime) :
    (rationalArithmeticCyclotomicCharacter a n hna).comp
        (rationalPrimeArithmeticRestriction a p hp) =
      rationalPrimeCyclotomicCharacter p hp n :=
  rationalArithmeticCyclotomicCharacter_restriction a n hna p hp

end

section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors




/-- Exact original-object consumer of `rationalArithmeticCyclotomicCoefficientCharacter_restriction`. -/
theorem actual_arithmetic_cyclotomic_coefficient_character_rationalArithmeticCyclotomicCoefficientCharacter_restriction_source
    (a : 𝓞 ℚ) (n : ℕ) [NeZero n] (hna : (n : 𝓞 ℚ) ∣ a)
    (p : ℕ) (hp : p.Prime)
    (k : Type) [CommRing k] [CharP k n] [TopologicalSpace k] :
    (rationalArithmeticCyclotomicCoefficientCharacter a n hna k).comp
        (rationalPrimeArithmeticRestriction a p hp) =
      rationalPrimeCyclotomicCoefficientCharacter p hp n k :=
  rationalArithmeticCyclotomicCoefficientCharacter_restriction a n hna p hp k

end

end Dubon2026.SemanticRegression

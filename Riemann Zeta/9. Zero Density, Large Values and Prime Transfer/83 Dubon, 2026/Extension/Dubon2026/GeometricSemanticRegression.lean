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


section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι k : Type} [Fintype ι] [DecidableEq ι] [Field k] [TopologicalSpace k]
variable (a : 𝓞 ℚ) (n : ℕ) [NeZero n] [CharP k n] (hna : (n : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι k)

/-- Exact original-object consumer of `rationalArithmeticTraceZeroCyclotomicTwist_restriction`. -/
theorem actual_arithmetic_trace_zero_cyclotomic_duality_rationalArithmeticTraceZeroCyclotomicTwist_restriction_source
    (p : ℕ) (hp : p.Prime) :
    (rationalArithmeticTraceZeroCyclotomicTwist a n hna σ).comp
        (rationalPrimeArithmeticRestriction a p hp).toMonoidHom =
      coefficientCharacterTwist
        (matrixTraceZeroAdjointRepresentation
          (σ.comp (rationalPrimeArithmeticRestriction a p hp).toMonoidHom))
        (rationalPrimeCyclotomicCoefficientCharacter p hp n k).toMonoidHom :=
  rationalArithmeticTraceZeroCyclotomicTwist_restriction a n hna σ p hp

end


section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι R : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]
    [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace R] [IsTopologicalRing R]

/-- Exact original-object consumer of `matrixTraceZeroCharacterAction_continuous`. -/
theorem actual_trace_zero_twisted_action_continuity_matrixTraceZeroCharacterAction_continuous_source
    (ρ : G →* GeneralLinearGroup ι R) (hρ : Continuous ρ)
    (χ : G →* R) (hχ : Continuous χ) :
    Continuous (fun z : G × matrixTraceZeroSubmodule ι R =>
      coefficientCharacterTwist (matrixTraceZeroAdjointRepresentation ρ) χ z.1 z.2) :=
  matrixTraceZeroCharacterAction_continuous ρ hρ χ hχ

end


section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep R G) [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]

omit [TopologicalSpace R] [ContinuousSMul R A] in
/-- Exact original-object consumer of `representationOneDifferential_continuous`. -/
theorem actual_continuous_representation_cocycles_representationOneDifferential_continuous_source
    (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
    (f : G → A) (hf : Continuous f) :
    Continuous (fun z => groupCohomology.d₁₂ A f z) :=
  representationOneDifferential_continuous A hA f hf

end


section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep R G) [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))

/-- Exact original-object consumer of `continuousRepresentationH2_eq_iff`. -/
theorem actual_continuous_representation_cohomology_continuousRepresentationH2_eq_iff_source
    (c d : continuousRepresentationCocyclesTwo A) :
    (Submodule.Quotient.mk c : ContinuousRepresentationH2 A hA) =
        Submodule.Quotient.mk d ↔
      ∃ f : C(G, A), continuousRepresentationCoboundaryTwo A hA f = c - d :=
  continuousRepresentationH2_eq_iff A hA c d

end


section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι R : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]
    [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace R] [IsTopologicalRing R]

variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k]

/-- Exact original-object consumer of `continuousTraceZeroH1GeneralEquiv_mk`. -/
theorem actual_continuous_adjoint_general_comparison_continuousTraceZeroH1GeneralEquiv_mk_source
    (ρ : G →* GeneralLinearGroup ι k) (hρ : Continuous ρ)
    (c : continuousTraceZeroAdjointCocycles ρ) :
    continuousTraceZeroH1GeneralEquiv ρ hρ (Submodule.Quotient.mk c) =
      (Submodule.Quotient.mk (⟨c.val, c.property⟩ :
        continuousRepresentationCocyclesOne (matrixTraceZeroAdjointRep ρ)) :
        ContinuousRepresentationH1 (matrixTraceZeroAdjointRep ρ)
          (matrixTraceZeroAdjointAction_continuous ρ hρ)) :=
  continuousTraceZeroH1GeneralEquiv_mk ρ hρ c

end


section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {R G : Type} [CommRing R] [Group G] (A B C : Rep R G)
    (β : A →ₗ[R] B →ₗ[R] C)
    (hβ : ∀ g x y, β (A.ρ g x) (B.ρ g y) = C.ρ g (β x y))

include hβ in
/-- Exact original-object consumer of `equivariantOneCocycleCup_mem`. -/
theorem actual_equivariant_cocycle_cup_equivariantOneCocycleCup_mem_source
    (f : groupCohomology.cocycles₁ A) (u : groupCohomology.cocycles₁ B) :
    (fun z : G × G => β (f z.1) (B.ρ z.1 (u z.2))) ∈ groupCohomology.cocycles₂ C :=
  equivariantOneCocycleCup_mem A B C β hβ f u

end


section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {R G : Type} [CommRing R] [Group G] (A B C : Rep R G)
    (β : A →ₗ[R] B →ₗ[R] C)
    (hβ : ∀ g x y, β (A.ρ g x) (B.ρ g y) = C.ρ g (β x y))

/-- Exact original-object consumer of `equivariantOneCocycleCup_coboundary_right`. -/
theorem actual_equivariant_cup_coboundaries_equivariantOneCocycleCup_coboundary_right_source
    (f : groupCohomology.cocycles₁ A) (b : B) :
    (equivariantOneCocycleCup A B C β hβ f
      ⟨groupCohomology.d₀₁ B b, groupCohomology.d₀₁_apply_mem_cocycles₁ (A := B) b⟩ :
        G × G → C) =
      groupCohomology.d₁₂ C (fun g => -β (f g) (B.ρ g b)) :=
  equivariantOneCocycleCup_coboundary_right A B C β hβ f b

end


section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  (A B C : Rep R G)
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [IsTopologicalAddGroup B] [ContinuousSMul R B]
  [TopologicalSpace C] [IsTopologicalAddGroup C] [ContinuousSMul R C]
  (β : A →ₗ[R] B →ₗ[R] C)
  (hβ : ∀ g x y, β (A.ρ g x) (B.ρ g y) = C.ρ g (β x y))
  (hcβ : Continuous (fun z : A × B => β z.1 z.2))
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))

omit [IsTopologicalGroup G] in
/-- Exact original-object consumer of `continuousOneCocycleCupBilinear_apply`. -/
theorem actual_continuous_equivariant_cup_continuousOneCocycleCupBilinear_apply_source
    (f : continuousRepresentationCocyclesOne A) (u : continuousRepresentationCocyclesOne B)
    (g h : G) :
    (continuousOneCocycleCupBilinear A B C β hβ hcβ hB f u).val (g, h) =
      β (f.val g) (B.ρ g (u.val h)) :=
  continuousOneCocycleCupBilinear_apply A B C β hβ hcβ hB f u g h

end


section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  (A B C : Rep R G)
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [IsTopologicalAddGroup B] [ContinuousSMul R B]
  [TopologicalSpace C] [IsTopologicalAddGroup C] [ContinuousSMul R C]
  (β : A →ₗ[R] B →ₗ[R] C)
  (hβ : ∀ g x y, β (A.ρ g x) (B.ρ g y) = C.ρ g (β x y))
  (hcβ : Continuous (fun z : A × B => β z.1 z.2))
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))
  (hC : Continuous (fun z : G × C => C.ρ z.1 z.2))

/-- Exact original-object consumer of `continuousH1Cup_mk`. -/
theorem actual_continuous_cohomology_cup_continuousH1Cup_mk_source
    (f : continuousRepresentationCocyclesOne A) (u : continuousRepresentationCocyclesOne B) :
    continuousH1Cup A B C β hβ hcβ hA hB hC
        (Submodule.Quotient.mk f) (Submodule.Quotient.mk u) =
      (Submodule.Quotient.mk (continuousOneCocycleCup A B C β hβ hcβ hB f u) :
        ContinuousRepresentationH2 C hC) :=
  continuousH1Cup_mk A B C β hβ hcβ hA hB hC f u

end


section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι k : Type} [Group G] [Fintype ι] [DecidableEq ι] [Field k]
  [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace k] [IsTopologicalRing k]

omit [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace k] [IsTopologicalRing k] in
/-- Exact original-object consumer of `matrixTraceZeroTracePairing_character_equivariant`. -/
theorem actual_trace_zero_continuous_character_pairing_matrixTraceZeroTracePairing_character_equivariant_source
    (ρ : G →* GeneralLinearGroup ι k) (χ : G →* k) (g : G)
    (X Y : matrixTraceZeroSubmodule ι k) :
    matrixTraceZeroTracePairing ((matrixTraceZeroCharacterRep ρ χ).ρ g X)
        ((matrixTraceZeroAdjointRep ρ).ρ g Y) =
      (coefficientCharacterRep χ).ρ g (matrixTraceZeroTracePairing X Y) :=
  matrixTraceZeroTracePairing_character_equivariant ρ χ g X Y

end


section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {G ι k : Type} [Group G] [Fintype ι] [DecidableEq ι] [Field k]
  [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace k] [IsTopologicalRing k]
  (ρ : G →* GeneralLinearGroup ι k) (hρ : Continuous ρ)
  (χ : G →* k) (hχ : Continuous χ)

/-- Exact original-object consumer of `matrixTraceZeroCharacterH1Cup_mk`. -/
theorem actual_trace_zero_character_cohomology_cup_matrixTraceZeroCharacterH1Cup_mk_source
    (f : continuousRepresentationCocyclesOne (matrixTraceZeroCharacterRep ρ χ))
    (u : continuousTraceZeroAdjointCocycles ρ) :
    matrixTraceZeroCharacterH1Cup ρ hρ χ hχ
        (Submodule.Quotient.mk f) (Submodule.Quotient.mk u) =
      (Submodule.Quotient.mk
        (continuousOneCocycleCup (matrixTraceZeroCharacterRep ρ χ) (matrixTraceZeroAdjointRep ρ)
          (coefficientCharacterRep χ) matrixTraceZeroTracePairing
          (matrixTraceZeroTracePairing_character_equivariant ρ χ)
          matrixTraceZeroTracePairing_continuous (matrixTraceZeroAdjointAction_continuous ρ hρ)
          f (⟨u.val, u.property⟩ : continuousRepresentationCocyclesOne (matrixTraceZeroAdjointRep ρ))) :
        ContinuousRepresentationH2 (coefficientCharacterRep χ)
          (coefficientCharacterAction_continuous χ hχ)) :=
  matrixTraceZeroCharacterH1Cup_mk ρ hρ χ hχ f u

end


section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι k : Type} [Fintype ι] [DecidableEq ι] [Field k]
  [TopologicalSpace k] [IsTopologicalRing k]
  (a : 𝓞 ℚ) (n : ℕ) [NeZero n] [CharP k n] (hna : (n : 𝓞 ℚ) ∣ a)
  (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι k) (hσ : Continuous σ)

/-- Exact original-object consumer of `rationalArithmeticTraceZeroH1Cup_mk`. -/
theorem actual_arithmetic_trace_zero_cohomology_cup_rationalArithmeticTraceZeroH1Cup_mk_source
    (f : continuousRepresentationCocyclesOne
      (matrixTraceZeroCharacterRep σ
        (rationalArithmeticCyclotomicCoefficientCharacter a n hna k).toMonoidHom))
    (u : continuousTraceZeroAdjointCocycles σ) :
    let χ := rationalArithmeticCyclotomicCoefficientCharacter a n hna k
    rationalArithmeticTraceZeroH1Cup a n hna σ hσ
        (Submodule.Quotient.mk f) (Submodule.Quotient.mk u) =
      (Submodule.Quotient.mk
        (continuousOneCocycleCup (matrixTraceZeroCharacterRep σ χ.toMonoidHom)
          (matrixTraceZeroAdjointRep σ) (coefficientCharacterRep χ.toMonoidHom)
          matrixTraceZeroTracePairing
          (matrixTraceZeroTracePairing_character_equivariant σ χ.toMonoidHom)
          matrixTraceZeroTracePairing_continuous (matrixTraceZeroAdjointAction_continuous σ hσ)
          f (⟨u.val, u.property⟩ : continuousRepresentationCocyclesOne (matrixTraceZeroAdjointRep σ))) :
        ContinuousRepresentationH2 (coefficientCharacterRep χ.toMonoidHom)
          (coefficientCharacterAction_continuous χ.toMonoidHom χ.continuous)) :=
  rationalArithmeticTraceZeroH1Cup_mk a n hna σ hσ f u

end


section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {R G H : Type} [CommRing R] [Group G] [Group H]
  [TopologicalSpace R] [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalGroup G] [IsTopologicalGroup H]
  (A : Rep R G) [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  (j : H →* G) (hj : Continuous j)

/-- Exact original-object consumer of `continuousRepresentationCocycleTwoRestriction_coboundary`. -/
theorem actual_continuous_representation_restriction_continuousRepresentationCocycleTwoRestriction_coboundary_source
    (hA : Continuous (fun z : G × A => A.ρ z.1 z.2)) (f : C(G, A)) :
    continuousRepresentationCocycleTwoRestriction A j hj
        (continuousRepresentationCoboundaryTwo A hA f) =
      continuousRepresentationCoboundaryTwo (restrictedCoefficientRep A j)
        (restrictedCoefficientAction_continuous A j hj hA) (f.comp ⟨j, hj⟩) :=
  continuousRepresentationCocycleTwoRestriction_coboundary A j hj hA f

end


section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {R G H : Type} [CommRing R] [Group G] [Group H]
  [TopologicalSpace R] [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalGroup G] [IsTopologicalGroup H]
  (A : Rep R G) [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (j : H →* G) (hj : Continuous j)

/-- Exact original-object consumer of `continuousRepresentationH2Restriction_mk`. -/
theorem actual_continuous_cohomology_restriction_continuousRepresentationH2Restriction_mk_source
    (c : continuousRepresentationCocyclesTwo A) :
    continuousRepresentationH2Restriction A hA j hj (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (continuousRepresentationCocycleTwoRestriction A j hj c) :=
  continuousRepresentationH2Restriction_mk A hA j hj c

end


section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {R G H : Type} [CommRing R] [Group G] [Group H]
  [TopologicalSpace R] [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalGroup G] [IsTopologicalGroup H]
  (A B C : Rep R G)
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [IsTopologicalAddGroup B] [ContinuousSMul R B]
  [TopologicalSpace C] [IsTopologicalAddGroup C] [ContinuousSMul R C]
  (β : A →ₗ[R] B →ₗ[R] C)
  (hβ : ∀ g x y, β (A.ρ g x) (B.ρ g y) = C.ρ g (β x y))
  (hcβ : Continuous (fun z : A × B => β z.1 z.2))
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))
  (hC : Continuous (fun z : G × C => C.ρ z.1 z.2))
  (j : H →* G) (hj : Continuous j)

/-- Exact original-object consumer of `continuousH1Cup_restriction`. -/
theorem actual_continuous_cup_restriction_continuousH1Cup_restriction_source
    (x : ContinuousRepresentationH1 A hA) (y : ContinuousRepresentationH1 B hB) :
    continuousRepresentationH2Restriction C hC j hj
        (continuousH1Cup A B C β hβ hcβ hA hB hC x y) =
      continuousH1Cup (restrictedCoefficientRep A j) (restrictedCoefficientRep B j)
        (restrictedCoefficientRep C j) β (fun h v w => hβ (j h) v w) hcβ
        (restrictedCoefficientAction_continuous A j hj hA)
        (restrictedCoefficientAction_continuous B j hj hB)
        (restrictedCoefficientAction_continuous C j hj hC)
        (continuousRepresentationH1Restriction A hA j hj x)
        (continuousRepresentationH1Restriction B hB j hj y) :=
  continuousH1Cup_restriction A B C β hβ hcβ hA hB hC j hj x y

end


section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {G H ι R : Type} [Group G] [Group H] [Fintype ι] [DecidableEq ι] [CommRing R]

/-- Exact original-object consumer of `matrixTraceZeroAdjointRepresentation_comp`. -/
theorem actual_adjoint_representation_restriction_matrixTraceZeroAdjointRepresentation_comp_source
    (ρ : G →* GeneralLinearGroup ι R) (j : H →* G) :
    (matrixTraceZeroAdjointRepresentation ρ).comp j =
      matrixTraceZeroAdjointRepresentation (ρ.comp j) :=
  matrixTraceZeroAdjointRepresentation_comp ρ j

end


section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {R G V : Type} [CommRing R] [Group G] [AddCommGroup V] [Module R V]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul R V]
  {ρ σ : Representation R G V} (h : ρ = σ)

variable (hρ : Continuous (fun z : G × V => ρ z.1 z.2))
  (hσ : Continuous (fun z : G × V => σ z.1 z.2))

/-- Exact original-object consumer of `continuousH2CoefficientCongr_mk`. -/
theorem actual_continuous_cohomology_coefficient_congr_continuousH2CoefficientCongr_mk_source
    (c : continuousRepresentationCocyclesTwo (Rep.of ρ)) :
    continuousH2CoefficientCongr h hρ hσ (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (continuousCocycleTwoCoefficientCongr h c) :=
  continuousH2CoefficientCongr_mk h hρ hσ c

end


section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {G H ι R : Type} [Group G] [Group H] [Fintype ι] [DecidableEq ι] [CommRing R]
  [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace H] [IsTopologicalGroup H]
  [TopologicalSpace R] [IsTopologicalRing R]

variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k]

/-- Exact original-object consumer of `continuousTraceZeroH1GeneralEquiv_restriction`. -/
theorem actual_continuous_adjoint_restriction_comparison_continuousTraceZeroH1GeneralEquiv_restriction_source
    (ρ : G →* GeneralLinearGroup ι k) (hρ : Continuous ρ)
    (j : H →* G) (hj : Continuous j) (x : ContinuousTraceZeroAdjointH1 ρ hρ) :
    continuousH1CoefficientCongr (matrixTraceZeroAdjointRepresentation_comp ρ j)
      (restrictedCoefficientAction_continuous (matrixTraceZeroAdjointRep ρ) j hj
        (matrixTraceZeroAdjointAction_continuous ρ hρ))
      (matrixTraceZeroAdjointAction_continuous (ρ.comp j) (hρ.comp hj))
      (continuousRepresentationH1Restriction (matrixTraceZeroAdjointRep ρ)
        (matrixTraceZeroAdjointAction_continuous ρ hρ) j hj
        (continuousTraceZeroH1GeneralEquiv ρ hρ x)) =
      continuousTraceZeroH1GeneralEquiv (ρ.comp j) (hρ.comp hj)
        (continuousTraceZeroH1Restriction ρ hρ j hj x) :=
  continuousTraceZeroH1GeneralEquiv_restriction ρ hρ j hj x

end


section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {F K : Type} [Field F] [Field K] [Algebra F K]
  {n : ℕ} [NeZero n] {μ : K}

/-- Exact original-object consumer of `primitiveRootAdditiveEquiv_galois`. -/
theorem actual_cyclotomic_root_additive_equiv_primitiveRootAdditiveEquiv_galois_source
    (hμ : IsPrimitiveRoot μ n) (g : K ≃ₐ[F] K) (x : ZMod n) :
    restrictRootsOfUnity g n (Additive.toMul (primitiveRootAdditiveEquiv hμ x)) =
      Additive.toMul (primitiveRootAdditiveEquiv hμ ((hμ.autToPow F g : ZMod n) * x)) :=
  primitiveRootAdditiveEquiv_galois hμ g x

end


section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {R G : Type} [CommRing R] [Group G] (A B C : Rep R G)
  (β : A →ₗ[R] B →ₗ[R] C)
  (hβ : ∀ g x y, β (A.ρ g x) (B.ρ g y) = C.ρ g (β x y))

variable [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [IsTopologicalAddGroup B] [ContinuousSMul R B]
  [TopologicalSpace C] [IsTopologicalAddGroup C] [ContinuousSMul R C]
  (hcβ : Continuous (fun z : A × B => β z.1 z.2))
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))
  (hC : Continuous (fun z : G × C => C.ρ z.1 z.2))

/-- Exact original-object consumer of `continuousH1Cup_skew`. -/
theorem actual_continuous_cup_skew_symmetry_continuousH1Cup_skew_source
    (x : ContinuousRepresentationH1 A hA) (y : ContinuousRepresentationH1 B hB) :
    continuousH1Cup A B C β hβ hcβ hA hB hC x y =
      -continuousH1Cup B A C β.flip (fun g v w => hβ g w v)
        (hcβ.comp continuous_swap) hB hA hC y x :=
  continuousH1Cup_skew A B C β hβ hcβ hA hB hC x y

end


section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {K G : Type} [Field K] [Group G] [Fintype G] (A : Rep K G)

/-- Exact original-object consumer of `finiteTwoCocycle_average_coboundary`. -/
theorem actual_finite_coefficient_cocycle_averaging_finiteTwoCocycle_average_coboundary_source
    (hn : (Fintype.card G : K) ≠ 0) (c : groupCohomology.cocycles₂ A) :
    groupCohomology.d₁₂ A (fun g => (Fintype.card G : K)⁻¹ • ∑ t, c (g, t)) = c.val :=
  finiteTwoCocycle_average_coboundary A hn c

end


section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {K G : Type} [Field K] [Group G] [Fintype G]
  [TopologicalSpace K] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep K G) [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul K A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))

/-- Exact original-object consumer of `continuousFiniteH2_eq_zero`. -/
theorem actual_continuous_finite_cohomology_vanishing_continuousFiniteH2_eq_zero_source
    (hn : (Fintype.card G : K) ≠ 0) (x : ContinuousRepresentationH2 A hA) : x = 0 :=
  continuousFiniteH2_eq_zero A hA hn x

end


section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {G A : Type} [Group G]

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TopologicalSpace A] [DiscreteTopology A]

/-- Exact original-object consumer of `compactDiscreteFunction_exists_openNormalPeriods`. -/
theorem actual_compact_discrete_function_periods_compactDiscreteFunction_exists_openNormalPeriods_source (f : C(G, A)) :
    ∃ U : OpenNormalSubgroup G, ∀ g u, u ∈ U → f (g * u) = f g :=
  compactDiscreteFunction_exists_openNormalPeriods f

end


section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {G A : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace A] [DiscreteTopology A]

/-- Exact original-object consumer of `compactDiscreteTwoFunction_exists_commonPeriods`. -/
theorem actual_compact_discrete_finite_quotient_compactDiscreteTwoFunction_exists_commonPeriods_source [CompactSpace G] (f : C(G × G, A)) :
    ∃ V : OpenNormalSubgroup G, ∀ g h u v, u ∈ V → v ∈ V → f (g * u, h * v) = f (g, h) :=
  compactDiscreteTwoFunction_exists_commonPeriods f

end


section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {G A : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace A] [DiscreteTopology A]

/-- Exact original-object consumer of `compactDiscreteTwoFunction_exists_finiteQuotient`. -/
theorem actual_compact_discrete_two_quotient_function_compactDiscreteTwoFunction_exists_finiteQuotient_source [CompactSpace G]
    (f : C(G × G, A)) :
    ∃ U : OpenNormalSubgroup G, Finite (G ⧸ U.toSubgroup) ∧
      ∃ q : C((G ⧸ U.toSubgroup) × (G ⧸ U.toSubgroup), A),
        ∀ g h, q (QuotientGroup.mk' U.toSubgroup g, QuotientGroup.mk' U.toSubgroup h) = f (g, h) :=
  compactDiscreteTwoFunction_exists_finiteQuotient f

end


section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {R G V : Type} [CommRing R] [Group G] [AddCommGroup V] [Module R V]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace V] [DiscreteTopology V] [ContinuousSMul R V]

/-- Exact original-object consumer of `continuousTrivialTwoCocycle_exists_finiteQuotient`. -/
theorem actual_continuous_trivial_cocycle_finite_quotient_continuousTrivialTwoCocycle_exists_finiteQuotient_source [CompactSpace G]
    (c : continuousRepresentationCocyclesTwo (Rep.of (1 : Representation R G V))) :
    ∃ U : OpenNormalSubgroup G, Finite (G ⧸ U.toSubgroup) ∧
      ∃ d : continuousRepresentationCocyclesTwo
          (Rep.of (1 : Representation R (G ⧸ U.toSubgroup) V)),
        ∀ g h, d.val (QuotientGroup.mk' U.toSubgroup g, QuotientGroup.mk' U.toSubgroup h) =
          c.val (g, h) :=
  continuousTrivialTwoCocycle_exists_finiteQuotient c

end


section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {K G V : Type} [Field K] [CharZero K] [Group G] [AddCommGroup V] [Module K V]
  [TopologicalSpace K] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TopologicalSpace V] [DiscreteTopology V] [ContinuousSMul K V]

/-- Exact original-object consumer of `continuousCompactTrivialH2_eq_zero`. -/
theorem actual_continuous_compact_trivial_h2_vanishing_continuousCompactTrivialH2_eq_zero_source
    (x : ContinuousRepresentationH2 (Rep.of (1 : Representation K G V)) continuous_snd) :
    x = 0 :=
  continuousCompactTrivialH2_eq_zero x

end


section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {R G A B C : Type} [CommRing R] [Group G]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [IsTopologicalAddGroup B] [ContinuousSMul R B]
  [TopologicalSpace C] [IsTopologicalAddGroup C] [ContinuousSMul R C]
  {ρA σA : Representation R G A} {ρB σB : Representation R G B}
  {ρC σC : Representation R G C}

/-- Exact original-object consumer of `continuousH1Cup_coefficientCongr`. -/
theorem actual_continuous_cup_coefficient_congr_continuousH1Cup_coefficientCongr_source
    (eA : ρA = σA) (eB : ρB = σB) (eC : ρC = σC)
    (β : A →ₗ[R] B →ₗ[R] C)
    (hβρ : ∀ g x y, β (ρA g x) (ρB g y) = ρC g (β x y))
    (hβσ : ∀ g x y, β (σA g x) (σB g y) = σC g (β x y))
    (hcβ : Continuous (fun z : A × B => β z.1 z.2))
    (hρA : Continuous (fun z : G × A => ρA z.1 z.2))
    (hρB : Continuous (fun z : G × B => ρB z.1 z.2))
    (hρC : Continuous (fun z : G × C => ρC z.1 z.2))
    (hσA : Continuous (fun z : G × A => σA z.1 z.2))
    (hσB : Continuous (fun z : G × B => σB z.1 z.2))
    (hσC : Continuous (fun z : G × C => σC z.1 z.2))
    (x : ContinuousRepresentationH1 (Rep.of ρA) hρA)
    (y : ContinuousRepresentationH1 (Rep.of ρB) hρB) :
    continuousH2CoefficientCongr eC hρC hσC
        (continuousH1Cup (Rep.of ρA) (Rep.of ρB) (Rep.of ρC)
          β hβρ hcβ hρA hρB hρC x y) =
      continuousH1Cup (Rep.of σA) (Rep.of σB) (Rep.of σC)
        β hβσ hcβ hσA hσB hσC
        (continuousH1CoefficientCongr eA hρA hσA x)
        (continuousH1CoefficientCongr eB hρB hσB y) :=
  continuousH1Cup_coefficientCongr eA eB eC β hβρ hβσ hcβ hρA hρB hρC hσA hσB hσC x y

end


section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {G H ι k : Type} [Group G] [Group H] [Fintype ι] [DecidableEq ι] [Field k]

variable [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace H] [IsTopologicalGroup H] [TopologicalSpace k] [IsTopologicalRing k]
  (ρ : G →* GeneralLinearGroup ι k) (hρ : Continuous ρ)
  (χ : G →* k) (hχ : Continuous χ) (j : H →* G) (hj : Continuous j)

/-- Exact original-object consumer of `matrixTraceZeroCharacterH1Restriction_mk`. -/
theorem actual_trace_zero_character_cohomology_restriction_matrixTraceZeroCharacterH1Restriction_mk_source
    (c : continuousRepresentationCocyclesOne (matrixTraceZeroCharacterRep ρ χ)) :
    matrixTraceZeroCharacterH1Restriction ρ hρ χ hχ j hj (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (matrixTraceZeroCharacterCocycleRestriction ρ χ j hj c) :=
  matrixTraceZeroCharacterH1Restriction_mk ρ hρ χ hχ j hj c

end


section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {G H ι k : Type} [Group G] [Group H] [Fintype ι] [DecidableEq ι] [Field k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace H] [IsTopologicalGroup H] [TopologicalSpace k] [IsTopologicalRing k]
  (ρ : G →* GeneralLinearGroup ι k) (hρ : Continuous ρ)
  (χ : G →* k) (hχ : Continuous χ) (j : H →* G) (hj : Continuous j)

/-- Exact original-object consumer of `matrixTraceZeroCharacterH1Cup_restriction`. -/
theorem actual_trace_zero_character_cup_restriction_matrixTraceZeroCharacterH1Cup_restriction_source
    (x : ContinuousRepresentationH1 (matrixTraceZeroCharacterRep ρ χ)
      (matrixTraceZeroCharacterAction_continuous ρ hρ χ hχ))
    (y : ContinuousTraceZeroAdjointH1 ρ hρ) :
    coefficientCharacterH2Restriction χ hχ j hj
        (matrixTraceZeroCharacterH1Cup ρ hρ χ hχ x y) =
      matrixTraceZeroCharacterH1Cup (ρ.comp j) (hρ.comp hj) (χ.comp j) (hχ.comp hj)
        (matrixTraceZeroCharacterH1Restriction ρ hρ χ hχ j hj x)
        (continuousTraceZeroH1Restriction ρ hρ j hj y) :=
  matrixTraceZeroCharacterH1Cup_restriction ρ hρ χ hχ j hj x y

end


section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep R G) [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))

/-- Exact original-object consumer of `continuousDiscreteH2Equiv_mk`. -/
theorem actual_continuous_discrete_h2_comparison_continuousDiscreteH2Equiv_mk_source [DiscreteTopology G]
    (c : continuousRepresentationCocyclesTwo A) :
    continuousDiscreteH2Equiv A hA (Submodule.Quotient.mk c) =
      groupCohomology.H2π A c.val :=
  continuousDiscreteH2Equiv_mk A hA c

end


section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {K G V : Type} [Field K] [Group G] [AddCommGroup V] [Module K V]
  [TopologicalSpace K] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace V] [DiscreteTopology V] [ContinuousSMul K V]

variable [CompactSpace G] [CharZero K]

/-- Exact original-object consumer of `continuousCompactTrivialH1_eq_zero`. -/
theorem actual_continuous_compact_trivial_h1_vanishing_continuousCompactTrivialH1_eq_zero_source
    (x : ContinuousRepresentationH1 (Rep.of (1 : Representation K G V)) continuous_snd) :
    x = 0 :=
  continuousCompactTrivialH1_eq_zero x

end


section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι k : Type} [Fintype ι] [DecidableEq ι] [Field k] [TopologicalSpace k]
  (a : 𝓞 ℚ) (n : ℕ) [NeZero n] [CharP k n] (hna : (n : 𝓞 ℚ) ∣ a)
  (p : ℕ) (hp : p.Prime)

variable [IsTopologicalRing k]
  (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι k) (hσ : Continuous σ)

/-- Exact original-object consumer of `rationalPrimeCyclotomicAdjointH1Restriction_mk`. -/
theorem actual_arithmetic_cyclotomic_cohomology_restriction_rationalPrimeCyclotomicAdjointH1Restriction_mk_source
    (c : continuousRepresentationCocyclesOne (matrixTraceZeroCharacterRep σ
      (rationalArithmeticCyclotomicCoefficientCharacter a n hna k).toMonoidHom)) :
    rationalPrimeCyclotomicAdjointH1Restriction a n hna p hp σ hσ (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk
        (continuousCocycleOneCoefficientCongr
          (rationalArithmeticTraceZeroCyclotomicTwist_restriction a n hna σ p hp)
          (continuousRepresentationCocycleOneRestriction (matrixTraceZeroCharacterRep σ
            (rationalArithmeticCyclotomicCoefficientCharacter a n hna k).toMonoidHom)
            (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
            (rationalPrimeArithmeticRestriction a p hp).continuous c)) :=
  rationalPrimeCyclotomicAdjointH1Restriction_mk a n hna p hp σ hσ c

end


section

open IsDedekindDomain Matrix Module WithConv
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι k : Type} [Fintype ι] [DecidableEq ι] [Field k]
  [TopologicalSpace k] [IsTopologicalRing k]
  (a : 𝓞 ℚ) (n : ℕ) [NeZero n] [CharP k n] (hna : (n : 𝓞 ℚ) ∣ a)
  (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι k) (hσ : Continuous σ)
  (p : ℕ) (hp : p.Prime)

/-- Exact original-object consumer of `rationalArithmeticTraceZeroH1Cup_prime_restriction`. -/
theorem actual_arithmetic_cyclotomic_cup_restriction_rationalArithmeticTraceZeroH1Cup_prime_restriction_source
    (x : ContinuousRepresentationH1 (matrixTraceZeroCharacterRep σ
      (rationalArithmeticCyclotomicCoefficientCharacter a n hna k).toMonoidHom)
      (matrixTraceZeroCharacterAction_continuous σ hσ
        (rationalArithmeticCyclotomicCoefficientCharacter a n hna k).toMonoidHom
        (rationalArithmeticCyclotomicCoefficientCharacter a n hna k).continuous))
    (y : ContinuousTraceZeroAdjointH1 σ hσ) :
    let χP := rationalPrimeCyclotomicCoefficientCharacter p hp n k
    let j := rationalPrimeArithmeticRestriction a p hp
    rationalPrimeCyclotomicH2Restriction a n hna p hp
        (rationalArithmeticTraceZeroH1Cup a n hna σ hσ x y) =
      matrixTraceZeroCharacterH1Cup (σ.comp j.toMonoidHom) (hσ.comp j.continuous)
        χP.toMonoidHom χP.continuous
        (rationalPrimeCyclotomicAdjointH1Restriction a n hna p hp σ hσ x)
        (continuousTraceZeroH1Restriction σ hσ j.toMonoidHom j.continuous y) :=
  rationalArithmeticTraceZeroH1Cup_prime_restriction a n hna σ hσ p hp x y

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {R G : Type} [CommRing R] [CommGroup G] [Fintype G]
  [TopologicalSpace R] [TopologicalSpace G] [DiscreteTopology G]
  (A : Rep R G) [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)

/-- Exact original-object consumer of `continuousFiniteCyclicH2Pi_eq_iff`. -/
theorem actual_continuous_finite_cyclic_h2_continuousFiniteCyclicH2Pi_eq_iff_source
    (x y : LinearMap.ker (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap) :
    continuousFiniteCyclicH2Pi A hA g hg x = continuousFiniteCyclicH2Pi A hA g hg y ↔
      x.val - y.val ∈ LinearMap.range A.norm.hom.toLinearMap :=
  continuousFiniteCyclicH2Pi_eq_iff A hA g hg x y

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {K L : Type} [Field K] [Field L] [Algebra K L]

variable [FiniteDimensional K L] [IsGalois K L]

/-- Exact original-object consumer of `finiteFieldGaloisUnit_invariant_mem_normRange`. -/
theorem actual_finite_galois_unit_norm_range_finiteFieldGaloisUnit_invariant_mem_normRange_source [Finite L]
    (x : Rep.ofAlgebraAutOnUnits K L)
    (hx : x ∈ (Rep.ofAlgebraAutOnUnits K L).ρ.invariants) :
    x ∈ LinearMap.range (Rep.ofAlgebraAutOnUnits K L).norm.hom.toLinearMap :=
  finiteFieldGaloisUnit_invariant_mem_normRange x hx

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]

variable [Finite L] [FiniteDimensional K L] [IsGalois K L]
  [TopologicalSpace Gal(L/K)] [DiscreteTopology Gal(L/K)]

/-- Exact original-object consumer of `continuousFiniteFieldGaloisUnitH2_eq_zero`. -/
theorem actual_continuous_finite_field_galois_unit_h2_continuousFiniteFieldGaloisUnitH2_eq_zero_source
    (x : ContinuousRepresentationH2 (Rep.ofAlgebraAutOnUnits K L)
      (finiteFieldGaloisUnitAction_continuous (K := K) (L := L))) : x = 0 :=
  continuousFiniteFieldGaloisUnitH2_eq_zero x

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [TopologicalSpace Gal(L/K)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [IsTopologicalAddGroup (Rep.ofAlgebraAutOnUnits K L)]
  [@ContinuousSMul ℤ (Rep.ofAlgebraAutOnUnits K L)
    (Rep.ofAlgebraAutOnUnits K L).hV2.toSMul inferInstance inferInstance]
  (hA : Continuous (fun z : Gal(L/K) × Rep.ofAlgebraAutOnUnits K L =>
    (Rep.ofAlgebraAutOnUnits K L).ρ z.1 z.2))

/-- Exact original-object consumer of `continuousGaloisUnitH1_eq_zero`. -/
theorem actual_continuous_galois_unit_h1_vanishing_continuousGaloisUnitH1_eq_zero_source
    (x : ContinuousRepresentationH1 (Rep.ofAlgebraAutOnUnits K L) hA) : x = 0 :=
  continuousGaloisUnitH1_eq_zero hA x

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  (A B : Rep R G)
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [IsTopologicalAddGroup B] [ContinuousSMul R B]
  (φ : A →ₗ[R] B) (hφ : Continuous φ)
  (hφρ : ∀ g a, φ (A.ρ g a) = B.ρ g (φ a))

variable (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))

/-- Exact original-object consumer of `continuousCoefficientCocycleTwoMap_coboundary`. -/
theorem actual_continuous_equivariant_coefficient_map_continuousCoefficientCocycleTwoMap_coboundary_source (f : C(G, A)) :
    continuousCoefficientCocycleTwoMap A B φ hφ hφρ
      (continuousRepresentationCoboundaryTwo A hA f) =
        continuousRepresentationCoboundaryTwo B hB
          ⟨fun g => φ (f g), hφ.comp f.continuous⟩ :=
  continuousCoefficientCocycleTwoMap_coboundary A B φ hφ hφρ hA hB f

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  (A B : Rep R G)
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [IsTopologicalAddGroup B] [ContinuousSMul R B]
  (φ : A →ₗ[R] B) (hφ : Continuous φ)
  (hφρ : ∀ g a, φ (A.ρ g a) = B.ρ g (φ a))
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))

/-- Exact original-object consumer of `continuousCoefficientH2Map_mk`. -/
theorem actual_continuous_cohomology_coefficient_map_continuousCoefficientH2Map_mk_source (c : continuousRepresentationCocyclesTwo A) :
    continuousCoefficientH2Map A B φ hφ hφρ hA hB (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (continuousCoefficientCocycleTwoMap A B φ hφ hφρ c) :=
  continuousCoefficientH2Map_mk A B φ hφ hφρ hA hB c

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {R A B C : Type} [CommRing R]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]

/-- Exact original-object consumer of `exactCoefficientPreimage_map`. -/
theorem actual_continuous_exact_coefficient_lifts_exactCoefficientPreimage_map_source (φ : A →ₗ[R] B) (hφ : Function.Injective φ)
    (b : B) (hb : b ∈ LinearMap.range φ) : φ (exactCoefficientPreimage φ hφ b) = b :=
  exactCoefficientPreimage_map φ hφ b hb

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  (A B C : Rep R G)
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul R B]
  [TopologicalSpace C] [DiscreteTopology C] [ContinuousSMul R C]
  (φ : A →ₗ[R] B) (ψ : B →ₗ[R] C) (hψ : Function.Surjective ψ)
  (hψρ : ∀ g b, ψ (B.ρ g b) = C.ρ g (ψ b))
  (hExact : LinearMap.range φ = LinearMap.ker ψ)
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))

omit [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A] in
include hψρ hExact in
/-- Exact original-object consumer of `coefficientConnectingBoundary_mem_range`. -/
theorem actual_continuous_coefficient_connecting_lift_coefficientConnectingBoundary_mem_range_source
    (c : continuousRepresentationCocyclesOne C) (z : G × G) :
    (continuousRepresentationCoboundaryTwo B hB
      (coefficientConnectingOneLift B C ψ hψ c)).val z ∈ LinearMap.range φ :=
  coefficientConnectingBoundary_mem_range A B C φ ψ hψ hψρ hExact hB c z

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  (A B C : Rep R G)
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul R B]
  [TopologicalSpace C] [DiscreteTopology C] [ContinuousSMul R C]
  (φ : A →ₗ[R] B) (hφ : Function.Injective φ)
  (hφρ : ∀ g a, φ (A.ρ g a) = B.ρ g (φ a))
  (ψ : B →ₗ[R] C) (hψ : Function.Surjective ψ)
  (hψρ : ∀ g b, ψ (B.ρ g b) = C.ρ g (ψ b))
  (hExact : LinearMap.range φ = LinearMap.ker ψ)
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))

/-- Exact original-object consumer of `coefficientConnectingTwoCocycle_image_class_zero`. -/
theorem actual_continuous_coefficient_connecting_cocycle_coefficientConnectingTwoCocycle_image_class_zero_source
    (hA : Continuous (fun z : G × A => A.ρ z.1 z.2)) (hcφ : Continuous φ)
    (c : continuousRepresentationCocyclesOne C) :
    continuousCoefficientH2Map A B φ hcφ hφρ hA hB
      (Submodule.Quotient.mk
        (coefficientConnectingTwoCocycle A B C φ hφ hφρ ψ hψ hψρ hExact hB c)) = 0 :=
  coefficientConnectingTwoCocycle_image_class_zero A B C φ hφ hφρ ψ hψ hψρ hExact hB hA hcφ c

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  (A B C : Rep R G)
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul R B]
  [TopologicalSpace C] [DiscreteTopology C] [ContinuousSMul R C]
  (φ : A →ₗ[R] B) (hφ : Function.Injective φ)
  (hφρ : ∀ g a, φ (A.ρ g a) = B.ρ g (φ a))
  (ψ : B →ₗ[R] C) (hψ : Function.Surjective ψ)
  (hψρ : ∀ g b, ψ (B.ρ g b) = C.ρ g (ψ b))
  (hExact : LinearMap.range φ = LinearMap.ker ψ)
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))

/-- Exact original-object consumer of `coefficientConnectingClass_eq_of_lift`. -/
theorem actual_continuous_connecting_lift_independence_coefficientConnectingClass_eq_of_lift_source
    (c : continuousRepresentationCocyclesOne C)
    (a : continuousRepresentationCocyclesTwo A) (b : C(G, B))
    (hb : ∀ g, ψ (b g) = c.val g)
    (ha : ∀ z, φ (a.val z) = (continuousRepresentationCoboundaryTwo B hB b).val z) :
    (Submodule.Quotient.mk
      (coefficientConnectingTwoCocycle A B C φ hφ hφρ ψ hψ hψρ hExact hB c) :
      ContinuousRepresentationH2 A hA) = Submodule.Quotient.mk a :=
  coefficientConnectingClass_eq_of_lift A B C φ hφ hφρ ψ hψ hψρ hExact hA hB c a b hb ha

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  (A B C : Rep R G)
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul R B]
  [TopologicalSpace C] [DiscreteTopology C] [ContinuousSMul R C]
  (φ : A →ₗ[R] B) (hφ : Function.Injective φ)
  (hφρ : ∀ g a, φ (A.ρ g a) = B.ρ g (φ a))
  (ψ : B →ₗ[R] C) (hψ : Function.Surjective ψ)
  (hψρ : ∀ g b, ψ (B.ρ g b) = C.ρ g (ψ b))
  (hExact : LinearMap.range φ = LinearMap.ker ψ)
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))

/-- Exact original-object consumer of `continuousConnectingCocycleClass_apply`. -/
theorem actual_continuous_connecting_cocycle_class_continuousConnectingCocycleClass_apply_source (c : continuousRepresentationCocyclesOne C) :
    continuousConnectingCocycleClass A B C φ hφ hφρ ψ hψ hψρ hExact hA hB c =
      (Submodule.Quotient.mk
        (coefficientConnectingTwoCocycle A B C φ hφ hφρ ψ hψ hψρ hExact hB c) :
        ContinuousRepresentationH2 A hA) :=
  continuousConnectingCocycleClass_apply A B C φ hφ hφρ ψ hψ hψρ hExact hA hB c

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  (A B C : Rep R G)
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul R B]
  [TopologicalSpace C] [DiscreteTopology C] [ContinuousSMul R C]
  (φ : A →ₗ[R] B) (hφ : Function.Injective φ)
  (hφρ : ∀ g a, φ (A.ρ g a) = B.ρ g (φ a))
  (ψ : B →ₗ[R] C) (hψ : Function.Surjective ψ)
  (hψρ : ∀ g b, ψ (B.ρ g b) = C.ρ g (ψ b))
  (hExact : LinearMap.range φ = LinearMap.ker ψ)
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))
  (hC : Continuous (fun z : G × C => C.ρ z.1 z.2))

/-- Exact original-object consumer of `continuousCoefficientConnectingMap_image_zero`. -/
theorem actual_continuous_coefficient_connecting_map_continuousCoefficientConnectingMap_image_zero_source (hcφ : Continuous φ)
    (x : ContinuousRepresentationH1 C hC) :
    continuousCoefficientH2Map A B φ hcφ hφρ hA hB
      (continuousCoefficientConnectingMap A B C φ hφ hφρ ψ hψ hψρ hExact hA hB hC x) = 0 :=
  continuousCoefficientConnectingMap_image_zero A B C φ hφ hφρ ψ hψ hψρ hExact hA hB hC hcφ x

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  (A B C : Rep R G)
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul R B]
  [TopologicalSpace C] [DiscreteTopology C] [ContinuousSMul R C]
  (φ : A →ₗ[R] B) (hφ : Function.Injective φ) (hcφ : Continuous φ)
  (hφρ : ∀ g a, φ (A.ρ g a) = B.ρ g (φ a))
  (ψ : B →ₗ[R] C) (hψ : Function.Surjective ψ)
  (hψρ : ∀ g b, ψ (B.ρ g b) = C.ρ g (ψ b))
  (hExact : LinearMap.range φ = LinearMap.ker ψ)
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))
  (hC : Continuous (fun z : G × C => C.ρ z.1 z.2))

/-- Exact original-object consumer of `continuousConnectingH2_range_eq_ker`. -/
theorem actual_continuous_connecting_h2_exactness_continuousConnectingH2_range_eq_ker_source :
    LinearMap.range
      (continuousCoefficientConnectingMap A B C φ hφ hφρ ψ hψ hψρ hExact hA hB hC) =
        LinearMap.ker (continuousCoefficientH2Map A B φ hcφ hφρ hA hB) :=
  continuousConnectingH2_range_eq_ker A B C φ hφ hcφ hφρ ψ hψ hψρ hExact hA hB hC

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  (A B C : Rep R G)
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul R B]
  [TopologicalSpace C] [DiscreteTopology C] [ContinuousSMul R C]
  (φ : A →ₗ[R] B) (hφ : Function.Injective φ) (hcφ : Continuous φ)
  (hφρ : ∀ g a, φ (A.ρ g a) = B.ρ g (φ a))
  (ψ : B →ₗ[R] C) (hψ : Function.Surjective ψ)
  (hψρ : ∀ g b, ψ (B.ρ g b) = C.ρ g (ψ b))
  (hExact : LinearMap.range φ = LinearMap.ker ψ)
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))
  (hC : Continuous (fun z : G × C => C.ρ z.1 z.2))

include hcφ in
/-- Exact original-object consumer of `continuousConnectingH1_range_eq_ker`. -/
theorem actual_continuous_connecting_h1_exactness_continuousConnectingH1_range_eq_ker_source :
    LinearMap.range (continuousCoefficientH1Map B C ψ continuous_of_discreteTopology hψρ hB hC) =
      LinearMap.ker
        (continuousCoefficientConnectingMap A B C φ hφ hφρ ψ hψ hψρ hExact hA hB hC) :=
  continuousConnectingH1_range_eq_ker A B C φ hφ hcφ hφρ ψ hψ hψρ hExact hA hB hC

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {R G : Type} [CommRing R] [Group G] (A : Rep.{0} R G)

variable [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul R A]

/-- Exact original-object consumer of `continuousCocycle_exists_openNormal_periods_and_fixed`. -/
theorem actual_continuous_cocycle_period_invariants_continuousCocycle_exists_openNormal_periods_and_fixed_source
    (c : continuousRepresentationCocyclesOne A) :
    ∃ U : OpenNormalSubgroup G,
      (∀ g u, u ∈ U → c.val (g * u) = c.val g) ∧
      (∀ u, u ∈ U → ∀ g, A.ρ u (c.val g) = c.val g) :=
  continuousCocycle_exists_openNormal_periods_and_fixed A c

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Exact original-object consumer of `continuousGaloisUnitCocycle_exists_finiteField`. -/
theorem actual_continuous_galois_cocycle_finite_field_continuousGaloisUnitCocycle_exists_finiteField_source
    (c : continuousRepresentationCocyclesOne (Rep.ofAlgebraAutOnUnits K Ω)) :
    ∃ F : FiniteGaloisIntermediateField K Ω,
      (∀ g : Gal(Ω/K), ((Additive.toMul (Rep.toAdditive (c.val g)) : Ωˣ) : Ω) ∈
        F.toIntermediateField) ∧
      (∀ g u : Gal(Ω/K), AlgEquiv.restrictNormalHom F u = 1 →
        c.val (g * u) = c.val g) :=
  continuousGaloisUnitCocycle_exists_finiteField c

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (F : FiniteGaloisIntermediateField K Ω)
  (c : groupCohomology.cocycles₁ (Rep.ofAlgebraAutOnUnits K Ω))
  (hvalues : ∀ g : Gal(Ω/K), ((Additive.toMul (Rep.toAdditive (c g)) : Ωˣ) : Ω) ∈ F.toIntermediateField)
  (hperiod : ∀ g u : Gal(Ω/K), AlgEquiv.restrictNormalHom F u = 1 → c (g * u) = c g)

/-- Select the pinned original Galois unit action for this exact consumer. -/
noncomputable local instance galoisUnitFiniteDescentSourceAction : SMul Gal(F/K) Fˣ :=
  AlgEquiv.instMulDistribMulActionUnits.toSMul

include hvalues hperiod in
/-- Exact original-object consumer of `galoisUnitCocycle_exists_finite_descent`. -/
theorem actual_galois_unit_cocycle_finite_descent_galoisUnitCocycle_exists_finite_descent_source :
    ∃ f : Gal(F/K) → Fˣ, groupCohomology.IsMulCocycle₁ f ∧
      ∀ g : Gal(Ω/K), Units.map F.toIntermediateField.val.toMonoidHom
        (f (AlgEquiv.restrictNormalHom F g)) = Additive.toMul (Rep.toAdditive (c g)) :=
  galoisUnitCocycle_exists_finite_descent F c hvalues hperiod

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

variable (hA : Continuous (fun z : Gal(Ω/K) × Rep.ofAlgebraAutOnUnits K Ω =>
  (Rep.ofAlgebraAutOnUnits K Ω).ρ z.1 z.2))

/-- Exact original-object consumer of `continuousInfiniteGaloisUnitH1_eq_zero`. -/
theorem actual_continuous_infinite_galois_unit_h1_continuousInfiniteGaloisUnitH1_eq_zero_source
    (x : ContinuousRepresentationH1 (Rep.ofAlgebraAutOnUnits K Ω) hA) : x = 0 :=
  continuousInfiniteGaloisUnitH1_eq_zero hA x

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Exact original-object consumer of `discreteInfiniteGaloisUnitH1_eq_zero`. -/
theorem actual_discrete_galois_unit_action_continuity_discreteInfiniteGaloisUnitH1_eq_zero_source [IsGalois K Ω]
    (x : ContinuousRepresentationH1 (Rep.ofAlgebraAutOnUnits K Ω)
      (discreteGaloisUnitAction_continuous (K := K) (Ω := Ω))) : x = 0 :=
  discreteInfiniteGaloisUnitH1_eq_zero x

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {Ω : Type} [Field Ω]

/-- Exact original-object consumer of `algebraicallyClosedUnitPower_surjective`. -/
theorem actual_algebraically_closed_unit_power_sequence_algebraicallyClosedUnitPower_surjective_source [IsAlgClosed Ω]
    (n : ℕ) (hn : 0 < n) : Function.Surjective (powMonoidHom n : Ωˣ →* Ωˣ) :=
  algebraicallyClosedUnitPower_surjective n hn

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G]
  (A B C : Rep R G)
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul R B]
  (φ : A →ₗ[R] B) (hφ : Function.Injective φ)
  (hφρ : ∀ g a, φ (A.ρ g a) = B.ρ g (φ a))
  (ψ : B →ₗ[R] C) (hExact : LinearMap.range φ = LinearMap.ker ψ)

/-- Exact original-object consumer of `coefficientKernelTwoCocycle_coefficient_map`. -/
theorem actual_continuous_coefficient_kernel_two_cocycle_coefficientKernelTwoCocycle_coefficient_map_source (hcφ : Continuous φ)
    (b : continuousRepresentationCocyclesTwo B) (hb : ∀ z, ψ (b.val z) = 0) :
    continuousCoefficientCocycleTwoMap A B φ hcφ hφρ
      (coefficientKernelTwoCocycle A B C φ hφ hφρ ψ hExact b hb) = b :=
  coefficientKernelTwoCocycle_coefficient_map A B C φ hφ hφρ ψ hExact hcφ b hb

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  (A B C : Rep R G)
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul R B]
  [TopologicalSpace C] [DiscreteTopology C] [ContinuousSMul R C]
  (φ : A →ₗ[R] B) (hφ : Function.Injective φ) (hcφ : Continuous φ)
  (hφρ : ∀ g a, φ (A.ρ g a) = B.ρ g (φ a))
  (ψ : B →ₗ[R] C) (hψ : Function.Surjective ψ)
  (hψρ : ∀ g b, ψ (B.ρ g b) = C.ρ g (ψ b))
  (hExact : LinearMap.range φ = LinearMap.ker ψ)
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))
  (hC : Continuous (fun z : G × C => C.ρ z.1 z.2))

include hφ hψ hExact in
/-- Exact original-object consumer of `continuousCoefficientH2_middle_range_eq_ker`. -/
theorem actual_continuous_coefficient_h2_middle_exactness_continuousCoefficientH2_middle_range_eq_ker_source :
    LinearMap.range (continuousCoefficientH2Map A B φ hcφ hφρ hA hB) =
      LinearMap.ker (continuousCoefficientH2Map B C ψ continuous_of_discreteTopology hψρ hB hC) :=
  continuousCoefficientH2_middle_range_eq_ker A B C φ hφ hcφ hφρ ψ hψ hψρ hExact hA hB hC

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (n : ℕ)

/-- Exact original-object consumer of `galoisRootOfUnityRepresentation_apply`. -/
theorem actual_galois_root_of_unity_representation_galoisRootOfUnityRepresentation_apply_source (g : Gal(Ω/K))
    (x : galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n) :
    (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n).ρ g x =
      Rep.toAdditive.symm (Additive.ofMul (g • Additive.toMul (Rep.toAdditive x))) :=
  galoisRootOfUnityRepresentation_apply n g x

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (n : ℕ)

/-- Exact original-object consumer of `galoisKummerCoefficient_exact`. -/
theorem actual_galois_kummer_coefficient_sequence_galoisKummerCoefficient_exact_source :
    LinearMap.range (galoisKummerInclusion (K := K) (Ω := Ω) n).hom.toLinearMap =
      LinearMap.ker (galoisKummerPower (K := K) (Ω := Ω) n).hom.toLinearMap :=
  galoisKummerCoefficient_exact (K := K) (Ω := Ω) n

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (n : ℕ)
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Exact original-object consumer of `discreteGaloisRootAction_continuous`. -/
theorem actual_discrete_kummer_coefficient_continuity_discreteGaloisRootAction_continuous_source [Algebra.IsIntegral K Ω] :
    Continuous (fun z : Gal(Ω/K) × galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n =>
      (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n).ρ z.1 z.2) :=
  discreteGaloisRootAction_continuous (K := K) (Ω := Ω) n

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] (n : ℕ)
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

omit [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)] [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)] in
/-- Exact original-object consumer of `galoisKummerH2Power_eq_nsmul`. -/
theorem actual_continuous_kummer_h2_maps_galoisKummerH2Power_eq_nsmul_source (x : GaloisUnitContinuousH2 (K := K) (Ω := Ω)) :
    galoisKummerH2Power (K := K) (Ω := Ω) n x = n • x :=
  galoisKummerH2Power_eq_nsmul n x

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
  [IsGalois K Ω] [IsAlgClosed Ω] (n : ℕ) (hn : 0 < n)
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Exact original-object consumer of `galoisKummerH2KernelEquiv_apply`. -/
theorem actual_continuous_kummer_h2_torsion_galoisKummerH2KernelEquiv_apply_source
    (x : GaloisRootContinuousH2 (K := K) (Ω := Ω) n) :
    (galoisKummerH2KernelEquiv (K := K) (Ω := Ω) n hn x).val =
      galoisKummerH2Inclusion (K := K) (Ω := Ω) n x :=
  galoisKummerH2KernelEquiv_apply n hn x

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {R G : Type} [CommRing R] [Group G] (A : Rep.{0} R G)

variable [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul R A]

/-- Exact original-object consumer of `continuousTwoCocycle_exists_openNormal_periods_and_fixed`. -/
theorem actual_continuous_two_cocycle_period_invariants_continuousTwoCocycle_exists_openNormal_periods_and_fixed_source
    (c : continuousRepresentationCocyclesTwo A) :
    ∃ U : OpenNormalSubgroup G,
      (∀ g h u v, u ∈ U → v ∈ U → c.val (g * u, h * v) = c.val (g, h)) ∧
      (∀ u, u ∈ U → ∀ g h, A.ρ u (c.val (g, h)) = c.val (g, h)) :=
  continuousTwoCocycle_exists_openNormal_periods_and_fixed A c

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Exact original-object consumer of `continuousGaloisUnitTwoCocycle_exists_finiteField`. -/
theorem actual_continuous_galois_two_cocycle_finite_field_continuousGaloisUnitTwoCocycle_exists_finiteField_source
    (c : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits K Ω)) :
    ∃ F : FiniteGaloisIntermediateField K Ω,
      (∀ g h : Gal(Ω/K), ((Additive.toMul (Rep.toAdditive (c.val (g, h))) : Ωˣ) : Ω) ∈ F.toIntermediateField) ∧
      (∀ g h u v : Gal(Ω/K), AlgEquiv.restrictNormalHom F u = 1 →
        AlgEquiv.restrictNormalHom F v = 1 → c.val (g * u, h * v) = c.val (g, h)) :=
  continuousGaloisUnitTwoCocycle_exists_finiteField c

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (F : FiniteGaloisIntermediateField K Ω)
  (c : groupCohomology.cocycles₂ (Rep.ofAlgebraAutOnUnits K Ω))
  (hvalues : ∀ g h : Gal(Ω/K),
    ((Additive.toMul (Rep.toAdditive (c (g, h))) : Ωˣ) : Ω) ∈ F.toIntermediateField)
  (hperiod : ∀ g h u v : Gal(Ω/K), AlgEquiv.restrictNormalHom F u = 1 →
    AlgEquiv.restrictNormalHom F v = 1 → c (g * u, h * v) = c (g, h))

/-- Select the pinned original finite-field Galois unit action. -/
noncomputable local instance galoisUnitTwoCocycleFiniteDescentSourceAction : SMul Gal(F/K) Fˣ :=
  AlgEquiv.instMulDistribMulActionUnits.toSMul

include hvalues hperiod in
/-- Exact original-object consumer of `galoisUnitTwoCocycle_exists_finite_descent`. -/
theorem actual_galois_unit_two_cocycle_finite_descent_galoisUnitTwoCocycle_exists_finite_descent_source :
    ∃ f : Gal(F/K) × Gal(F/K) → Fˣ, groupCohomology.IsMulCocycle₂ f ∧
      ∀ g h : Gal(Ω/K), Units.map F.toIntermediateField.val.toMonoidHom
        (f (AlgEquiv.restrictNormalHom F g, AlgEquiv.restrictNormalHom F h)) =
        Additive.toMul (Rep.toAdditive (c (g, h))) :=
  galoisUnitTwoCocycle_exists_finite_descent F c hvalues hperiod

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [Finite K]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Exact original-object consumer of `continuousFiniteBaseGaloisUnitH2_eq_zero`. -/
theorem actual_continuous_finite_base_galois_unit_h2_continuousFiniteBaseGaloisUnitH2_eq_zero_source
    (x : ContinuousRepresentationH2 (Rep.ofAlgebraAutOnUnits K Ω)
      (discreteGaloisUnitAction_continuous (K := K) (Ω := Ω))) : x = 0 :=
  continuousFiniteBaseGaloisUnitH2_eq_zero x

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Exact original-object consumer of `continuousGaloisUnitCochain_exists_finiteField`. -/
theorem actual_continuous_galois_cochain_finite_field_continuousGaloisUnitCochain_exists_finiteField_source
    (E : FiniteGaloisIntermediateField K Ω)
    (b : C(Gal(Ω/K), Rep.ofAlgebraAutOnUnits K Ω)) :
    ∃ F : FiniteGaloisIntermediateField K Ω, E ≤ F ∧
      (∀ g : Gal(Ω/K), ((Additive.toMul (Rep.toAdditive (b g)) : Ωˣ) : Ω) ∈ F.toIntermediateField) ∧
      (∀ g u : Gal(Ω/K), AlgEquiv.restrictNormalHom F u = 1 → b (g * u) = b g) :=
  continuousGaloisUnitCochain_exists_finiteField E b

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
  [IsGalois K Ω] [IsAlgClosed Ω] [Finite K] (n : ℕ) (hn : 0 < n)
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

include hn in
/-- Exact original-object consumer of `continuousFiniteBaseRootH2_eq_zero`. -/
theorem actual_continuous_finite_base_root_h2_continuousFiniteBaseRootH2_eq_zero_source
    (x : GaloisRootContinuousH2 (K := K) (Ω := Ω) n) : x = 0 :=
  continuousFiniteBaseRootH2_eq_zero n hn x

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (F : FiniteGaloisIntermediateField K Ω)

variable [TopologicalSpace (Rep.ofAlgebraAutOnUnits K F)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K F)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Exact original-object consumer of `galoisUnitFiniteStageH2Inflation_mk`. -/
theorem actual_galois_unit_finite_stage_inflation_galoisUnitFiniteStageH2Inflation_mk_source
    (c : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits K F)) :
    galoisUnitFiniteStageH2Inflation F (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (continuousCoefficientCocycleTwoMap
        (restrictedCoefficientRep (Rep.ofAlgebraAutOnUnits K F)
          (AlgEquiv.restrictNormalHom F : Gal(Ω/K) →* Gal(F/K)))
        (Rep.ofAlgebraAutOnUnits K Ω) (galoisUnitFiniteStageInclusion F).hom.toLinearMap
        continuous_of_discreteTopology (Rep.hom_comm_apply (galoisUnitFiniteStageInclusion F))
        (continuousRepresentationCocycleTwoRestriction (Rep.ofAlgebraAutOnUnits K F)
          (AlgEquiv.restrictNormalHom F : Gal(Ω/K) →* Gal(F/K))
          (InfiniteGalois.restrictNormalHom_continuous F.toIntermediateField) c)) :=
  galoisUnitFiniteStageH2Inflation_mk F c

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Exact original-object consumer of `continuousGaloisUnitH2_exists_finite_stage`. -/
theorem actual_continuous_galois_unit_h2_finite_stage_continuousGaloisUnitH2_exists_finite_stage_source
    (x : GaloisUnitContinuousH2 (K := K) (Ω := Ω)) :
    ∃ F : FiniteGaloisIntermediateField K Ω,
      letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K F) := ⊥
      letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K F) := ⟨rfl⟩
      ∃ y : GaloisUnitContinuousH2 (K := K) (Ω := F),
        galoisUnitFiniteStageH2Inflation F y = x :=
  continuousGaloisUnitH2_exists_finite_stage x

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {R G : Type} [CommRing R] [Group G] [Fintype G] (A : Rep R G)

variable [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))

/-- Exact original-object consumer of `continuousFiniteH2_card_nsmul_eq_zero`. -/
theorem actual_continuous_finite_h2_card_annihilation_continuousFiniteH2_card_nsmul_eq_zero_source
    (x : ContinuousRepresentationH2 A hA) : Fintype.card G • x = 0 :=
  continuousFiniteH2_card_nsmul_eq_zero A hA x

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Exact original-object consumer of `continuousGaloisUnitH2_is_torsion`. -/
theorem actual_continuous_galois_unit_h2_torsion_continuousGaloisUnitH2_is_torsion_source
    (x : GaloisUnitContinuousH2 (K := K) (Ω := Ω)) :
    ∃ n : ℕ, 0 < n ∧ n • x = 0 :=
  continuousGaloisUnitH2_is_torsion x

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {K L : Type} [Field K] [Field L] [Algebra K L]

variable [FiniteDimensional K L] [IsGalois K L]

/-- Exact original-object consumer of `galoisUnitsBaseCoefficient_mem_normRange_iff`. -/
theorem actual_galois_unit_invariant_base_descent_galoisUnitsBaseCoefficient_mem_normRange_iff_source (u : Kˣ) :
    galoisUnitsBaseCoefficient (L := L) u ∈
        LinearMap.range (Rep.ofAlgebraAutOnUnits K L).norm.hom.toLinearMap ↔
      ∃ v : Lˣ, Units.map (Algebra.norm K (S := L)) v = u :=
  galoisUnitsBaseCoefficient_mem_normRange_iff u

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]

variable (g : Gal(L/K))

variable [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
  (hg : ∀ x, x ∈ Subgroup.zpowers g)

/-- Exact original-object consumer of `continuousCyclicGaloisUnitH2Class_eq_iff`. -/
theorem actual_continuous_cyclic_galois_unit_h2_classes_continuousCyclicGaloisUnitH2Class_eq_iff_source (u v : Kˣ) :
    continuousCyclicGaloisUnitH2Class g hg (Additive.ofMul u) =
        continuousCyclicGaloisUnitH2Class g hg (Additive.ofMul v) ↔
      ∃ w : Lˣ, Units.map (Algebra.norm K (S := L)) w = u / v :=
  continuousCyclicGaloisUnitH2Class_eq_iff g hg u v

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]

variable (g : Gal(L/K)) (hg : ∀ x, x ∈ Subgroup.zpowers g)

/-- Exact original-object consumer of `continuousCyclicGaloisNormQuotientEquiv_mk`. -/
theorem actual_continuous_cyclic_galois_norm_quotient_continuousCyclicGaloisNormQuotientEquiv_mk_source (u : Additive Kˣ) :
    continuousCyclicGaloisNormQuotientEquiv g hg (Submodule.Quotient.mk u) =
      continuousCyclicGaloisUnitH2Class g hg u :=
  continuousCyclicGaloisNormQuotientEquiv_mk g hg u

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {K L Γ₀ : Type} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [LinearOrderedCommMonoidWithZero Γ₀]
  (v : Valuation L Γ₀)
  (hv : ∀ (g : Gal(L/K)) (x : L), v (g x) = v x)

include hv in
/-- Exact original-object consumer of `galoisInvariantValuation_norm`. -/
theorem actual_galois_invariant_valuation_norm_galoisInvariantValuation_norm_source (x : L) :
    v (algebraMap K L (Algebra.norm K x)) = v x ^ Module.finrank K L :=
  galoisInvariantValuation_norm v hv x

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory
open scoped TensorProduct NumberField nonZeroDivisors


variable {K L : Type} [NontriviallyNormedField K] [NormedField L]
  [NormedAlgebra K L] [IsUltrametricDist K] [CompleteSpace K]

/-- Exact original-object consumer of `completeNonarchimedeanGalois_norm_fieldNorm`. -/
theorem actual_complete_nonarchimedean_galois_norm_completeNonarchimedeanGalois_norm_fieldNorm_source
    [FiniteDimensional K L] [IsGalois K L] (x : L) :
    ‖Algebra.norm K x‖ = ‖x‖ ^ Module.finrank K L :=
  completeNonarchimedeanGalois_norm_fieldNorm x

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring


variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Exact original-object consumer of `localFieldUnitOrder_nonneg_iff`. -/
theorem actual_local_field_normalized_unit_order_localFieldUnitOrder_nonneg_iff_source (u : Kˣ) :
    0 ≤ localFieldUnitOrder K (Additive.ofMul u) ↔ ValuativeRel.valuation K u.val ≤ 1 :=
  localFieldUnitOrder_nonneg_iff K u

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring


variable {R S ι : Type} [CommRing R] [CommRing S] [Algebra R S]
  [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R S) (x : S)

/-- Exact original-object consumer of `finiteFreeNormLinePolynomial_derivative_zero`. -/
theorem actual_finite_free_norm_line_polynomial_finiteFreeNormLinePolynomial_derivative_zero_source :
    (finiteFreeNormLinePolynomial b x).derivative.eval 0 = Algebra.trace R S x :=
  finiteFreeNormLinePolynomial_derivative_zero b x

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring




/-- Exact original-object consumer of `adicComplete_polynomial_simple_root`. -/
theorem actual_adic_complete_simple_root_adicComplete_polynomial_simple_root_source
    {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (f : R[X]) (a₀ : R) (h₁ : f.eval a₀ ∈ I)
    (h₂ : IsUnit (Ideal.Quotient.mk I (f.derivative.eval a₀))) :
    ∃ a : R, f.IsRoot a ∧ a - a₀ ∈ I :=
  adicComplete_polynomial_simple_root I f a₀ h₁ h₂

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring


variable {R S ι : Type} [CommRing R] [CommRing S] [Algebra R S]
  [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R S)
  (I : Ideal R) [IsAdicComplete I R]

include b in
/-- Exact original-object consumer of `adicComplete_exists_principal_unit_norm`. -/
theorem actual_adic_complete_principal_norm_lifting_adicComplete_exists_principal_unit_norm_source
    (x : S) (hx : IsUnit (Ideal.Quotient.mk I (Algebra.trace R S x)))
    (u : Rˣ) (hu : 1 - u.val ∈ I) :
    ∃ v : Sˣ, Units.map (Algebra.norm R (S := S)) v = u :=
  adicComplete_exists_principal_unit_norm b I x hx u hu

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring


variable {R S ι : Type} [CommRing R] [CommRing S] [Algebra R S]
  [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R S)
  (I : Ideal R) [IsAdicComplete I R]

include b in
/-- Exact original-object consumer of `adicComplete_unit_norm_surjective`. -/
theorem actual_adic_complete_unit_norm_lifting_adicComplete_unit_norm_surjective_source
    (x : S) (hx : IsUnit (Ideal.Quotient.mk I (Algebra.trace R S x)))
    (hres : ∀ u : Rˣ, ∃ a : Sˣ,
      Ideal.Quotient.mk I (Algebra.norm R a.val) = Ideal.Quotient.mk I u.val) :
    Function.Surjective (Units.map (Algebra.norm R (S := S))) :=
  adicComplete_unit_norm_surjective b I x hx hres

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring


variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
  [IsLocalRing R] [Module.Free R S] [Module.Finite R S]

/-- Exact original-object consumer of `localRingNorm_quotient_mk`. -/
theorem actual_local_ring_norm_reduction_localRingNorm_quotient_mk_source (x : S) :
    Algebra.norm (R ⧸ maximalIdeal R)
      (Ideal.Quotient.mk (Ideal.map (algebraMap R S) (maximalIdeal R)) x) =
      Ideal.Quotient.mk (maximalIdeal R) (Algebra.norm R x) :=
  localRingNorm_quotient_mk x

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring


variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
  [IsLocalRing R] [IsLocalRing S] [Module.Free R S] [Module.Finite R S]
  [IsAdicComplete (maximalIdeal R) R]
  [Finite (R ⧸ maximalIdeal R)]
  [(Ideal.map (algebraMap R S) (maximalIdeal R)).IsMaximal]

/-- Exact original-object consumer of `completeLocalFiniteResidue_unit_norm_surjective`. -/
theorem actual_complete_local_finite_residue_norm_completeLocalFiniteResidue_unit_norm_surjective_source :
    Function.Surjective (Units.map (Algebra.norm R (S := S))) :=
  completeLocalFiniteResidue_unit_norm_surjective (R := R) (S := S)

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring


variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
  [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
  [Module.Free R S] [Module.Finite R S] [Algebra.FormallyUnramified R S]
  [IsAdicComplete (maximalIdeal R) R] [Finite (R ⧸ maximalIdeal R)]

/-- Exact original-object consumer of `unramifiedCompleteLocal_unit_norm_surjective`. -/
theorem actual_unramified_complete_local_unit_norm_unramifiedCompleteLocal_unit_norm_surjective_source :
    Function.Surjective (Units.map (Algebra.norm R (S := S))) :=
  unramifiedCompleteLocal_unit_norm_surjective (R := R) (S := S)

end

end Dubon2026.SemanticRegression

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


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel


variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Exact original-object consumer of `localFieldUnitOrder_eq_zero_iff_integer_unit`. -/
theorem actual_local_field_integer_unit_order_kernel_localFieldUnitOrder_eq_zero_iff_integer_unit_source (u : Kˣ) :
    localFieldUnitOrder K (Additive.ofMul u) = 0 ↔
      ∃ a : 𝒪[K]ˣ, Units.map (algebraMap 𝒪[K] K).toMonoidHom a = u :=
  localFieldUnitOrder_eq_zero_iff_integer_unit K u

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel


variable {R S K L : Type} [CommRing R] [CommRing S] [IsDomain S]
  [Field K] [Field L] [Algebra R S] [FaithfulSMul R S]
  [Algebra R K] [Algebra S L] [Algebra K L] [Algebra R L]
  [IsFractionRing R K] [IsFractionRing S L]
  [IsScalarTower R K L] [IsScalarTower R S L]
  [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
  [Module.Free R S] [Module.Finite R S] [Algebra.FormallyUnramified R S]
  [IsAdicComplete (maximalIdeal R) R] [Finite (R ⧸ maximalIdeal R)]

/-- Exact original-object consumer of `unramifiedLocal_exists_fraction_field_unit_norm`. -/
theorem actual_unramified_local_fraction_field_norm_unramifiedLocal_exists_fraction_field_unit_norm_source (u : Rˣ) :
    ∃ v : Sˣ,
      Units.map (Algebra.norm K (S := L)) (Units.map (algebraMap S L).toMonoidHom v) =
        Units.map (algebraMap R K).toMonoidHom u :=
  unramifiedLocal_exists_fraction_field_unit_norm u

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel


variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [Module.Finite 𝒪[K] 𝒪[L]] [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]

/-- Exact original-object consumer of `unramifiedLocalField_exists_norm_of_order_zero`. -/
theorem actual_unramified_local_field_zero_order_norm_unramifiedLocalField_exists_norm_of_order_zero_source (u : Kˣ)
    (hu : localFieldUnitOrder K (Additive.ofMul u) = 0) :
    ∃ v : Lˣ, Units.map (Algebra.norm K (S := L)) v = u :=
  unramifiedLocalField_exists_norm_of_order_zero u hu

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel


variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Exact original-object consumer of `localFieldUnit_eq_integer_unit_mul_order_power`. -/
theorem actual_local_field_uniformizer_order_localFieldUnit_eq_integer_unit_mul_order_power_source (q : 𝒪[K])
    (hq : Irreducible q) (x : Kˣ) :
    ∃ a : 𝒪[K]ˣ, x = Units.map (algebraMap 𝒪[K] K).toMonoidHom a *
      (Units.mk0 (algebraMap 𝒪[K] K q) (by simpa using hq.ne_zero)) ^
        (localFieldUnitOrder K (Additive.ofMul x)) :=
  localFieldUnit_eq_integer_unit_mul_order_power K q hq x

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel


variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [Module.Finite 𝒪[K] 𝒪[L]]

/-- Exact original-object consumer of `localField_norm_integer_unit_order_zero`. -/
theorem actual_local_field_integer_unit_norm_localField_norm_integer_unit_order_zero_source (a : 𝒪[L]ˣ) :
    localFieldUnitOrder K (Additive.ofMul
      (Units.map (Algebra.norm K (S := L))
        (Units.map (algebraMap 𝒪[L] L).toMonoidHom a))) = 0 :=
  localField_norm_integer_unit_order_zero a

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel


variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [Module.Finite 𝒪[K] 𝒪[L]] [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]

/-- Exact original-object consumer of `unramifiedLocalField_irreducible_algebraMap`. -/
theorem actual_unramified_local_field_uniformizer_unramifiedLocalField_irreducible_algebraMap_source (q : 𝒪[K])
    (hq : Irreducible q) : Irreducible (algebraMap 𝒪[K] 𝒪[L] q) :=
  unramifiedLocalField_irreducible_algebraMap q hq

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel


variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [Module.Finite 𝒪[K] 𝒪[L]] [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]

/-- Exact original-object consumer of `unramifiedLocalField_norm_order`. -/
theorem actual_unramified_local_field_norm_order_unramifiedLocalField_norm_order_source (v : Lˣ) :
    localFieldUnitOrder K (Additive.ofMul (Units.map (Algebra.norm K (S := L)) v)) =
      (Module.finrank K L : ℤ) * localFieldUnitOrder L (Additive.ofMul v) :=
  unramifiedLocalField_norm_order v

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel


variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]

/-- Exact original-object consumer of `localFieldUnit_mem_normRange_iff_order_dvd`. -/
theorem actual_local_field_norm_order_criterion_localFieldUnit_mem_normRange_iff_order_dvd_source
    (hnorm : ∀ v : Lˣ,
      localFieldUnitOrder K (Additive.ofMul (Units.map (Algebra.norm K (S := L)) v)) =
        (Module.finrank K L : ℤ) * localFieldUnitOrder L (Additive.ofMul v))
    (hzero : ∀ u : Kˣ, localFieldUnitOrder K (Additive.ofMul u) = 0 →
      ∃ v : Lˣ, Units.map (Algebra.norm K (S := L)) v = u)
    (u : Kˣ) :
    (∃ v : Lˣ, Units.map (Algebra.norm K (S := L)) v = u) ↔
      (Module.finrank K L : ℤ) ∣ localFieldUnitOrder K (Additive.ofMul u) :=
  localFieldUnit_mem_normRange_iff_order_dvd hnorm hzero u

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel


variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [Module.Finite 𝒪[K] 𝒪[L]] [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]

/-- Exact original-object consumer of `unramifiedLocalField_mem_normRange_iff_order_dvd`. -/
theorem actual_unramified_local_field_norm_image_unramifiedLocalField_mem_normRange_iff_order_dvd_source (u : Kˣ) :
    (∃ v : Lˣ, Units.map (Algebra.norm K (S := L)) v = u) ↔
      (Module.finrank K L : ℤ) ∣ localFieldUnitOrder K (Additive.ofMul u) :=
  unramifiedLocalField_mem_normRange_iff_order_dvd u

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel


variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

variable {K} {L : Type} [Field L] [Algebra K L] [FiniteDimensional K L]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [Module.Finite 𝒪[K] 𝒪[L]] [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]

/-- Exact original-object consumer of `unramifiedLocalNormQuotientEquiv_mk`. -/
theorem actual_unramified_local_norm_quotient_unramifiedLocalNormQuotientEquiv_mk_source (u : Additive Kˣ) :
    unramifiedLocalNormQuotientEquiv (L := L) (Submodule.Quotient.mk u) =
      (localFieldUnitOrder K u : ZMod (Module.finrank K L)) :=
  unramifiedLocalNormQuotientEquiv_mk u

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel


variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [IsGalois K L] [IsCyclic Gal(L/K)]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [Module.Finite 𝒪[K] 𝒪[L]] [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]

variable (g : Gal(L/K)) (hg : ∀ x, x ∈ Subgroup.zpowers g)

/-- Exact original-object consumer of `continuousUnramifiedCyclicGaloisH2OrderEquiv_class`. -/
theorem actual_continuous_unramified_cyclic_galois_h2_order_continuousUnramifiedCyclicGaloisH2OrderEquiv_class_source (u : Additive Kˣ) :
    continuousUnramifiedCyclicGaloisH2OrderEquiv g hg
      (continuousCyclicGaloisUnitH2Class g hg u) =
        (localFieldUnitOrder K u : ZMod (Module.finrank K L)) :=
  continuousUnramifiedCyclicGaloisH2OrderEquiv_class g hg u

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel


variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CompactSpace R] [T2Space R] [IsLocalRing R] [IsNoetherianRing R]
  [IsHausdorff (maximalIdeal R) R]

variable {S : Type} [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
  [CompactSpace S] [T2Space S] [IsLocalRing S] [IsNoetherianRing S]
  [IsHausdorff (maximalIdeal S) S]

/-- Exact original-object consumer of `compactSeparatedLocalRingHom_continuous`. -/
theorem actual_compact_separated_local_adic_topology_compactSeparatedLocalRingHom_continuous_source (f : R →+* S) [IsLocalHom f] :
    Continuous f :=
  compactSeparatedLocalRingHom_continuous f

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel


variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
  [TopologicalSpace R] [TopologicalSpace S] [IsTopologicalRing S]
  [CompactSpace R] [CompactSpace S] [T2Space S] [ContinuousSMul R S]
  [IsNoetherianRing S]

/-- Exact original-object consumer of `compactFiniteResidue_module_finite`. -/
theorem actual_compact_finite_residue_module_compactFiniteResidue_module_finite_source (I : Ideal S) [IsHausdorff I S]
    (π : R) (hπ : algebraMap R S π ∈ I)
    [Finite (S ⧸ Ideal.span {algebraMap R S π})] : Module.Finite R S :=
  compactFiniteResidue_module_finite I π hπ

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel


variable {R S : Type} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
  [IsDiscreteValuationRing R] [IsDiscreteValuationRing S]
  [Algebra R S] [FaithfulSMul R S] [IsLocalHom (algebraMap R S)]
  [TopologicalSpace R] [TopologicalSpace S] [IsTopologicalRing R] [IsTopologicalRing S]
  [CompactSpace R] [CompactSpace S] [T2Space R] [T2Space S]
  [IsHausdorff (maximalIdeal R) R] [IsHausdorff (maximalIdeal S) S]

/-- Exact original-object consumer of `compactDVRLocalAlgebra_module_finite`. -/
theorem actual_compact_d_v_r_local_algebra_finite_compactDVRLocalAlgebra_module_finite_source : Module.Finite R S :=
  compactDVRLocalAlgebra_module_finite (R := R) (S := S)

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel


variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]

/-- Exact original-object consumer of `localField_field_module_finite`. -/
theorem actual_local_field_integer_algebra_finite_localField_field_module_finite_source : FiniteDimensional K L :=
  localField_field_module_finite (K := K) (L := L)

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel


variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]

variable [IsGalois K L] [IsCyclic Gal(L/K)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]

variable (g : Gal(L/K)) (hg : ∀ x, x ∈ Subgroup.zpowers g)

/-- Exact original-object consumer of `unramifiedLocalFieldArithmeticH2Equiv_class`. -/
theorem actual_unramified_local_field_arithmetic_h2_unramifiedLocalFieldArithmeticH2Equiv_class_source (u : Additive Kˣ) :
    unramifiedLocalFieldArithmeticH2Equiv g hg
      (continuousCyclicGaloisUnitH2Class g hg u) =
        (localFieldUnitOrder K u : ZMod (Module.finrank K L)) :=
  unramifiedLocalFieldArithmeticH2Equiv_class g hg u

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]

/-- Exact original-object consumer of `localField_integer_isIntegralClosure`. -/
theorem actual_local_field_integer_integral_closure_localField_integer_isIntegralClosure_source : IsIntegralClosure 𝒪[L] 𝒪[K] L :=
  localField_integer_isIntegralClosure (K := K) (L := L)

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]

/-- Exact original-object consumer of `localFieldIntegerGaloisEquiv_apply`. -/
theorem actual_local_field_integer_galois_restriction_localFieldIntegerGaloisEquiv_apply_source (g : Gal(L/K)) (x : 𝒪[L]) :
    algebraMap 𝒪[L] L (localFieldIntegerGaloisEquiv K L g x) =
      g (algebraMap 𝒪[L] L x) :=
  localFieldIntegerGaloisEquiv_apply K L g x

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing S]
  [Algebra.FormallyUnramified R S] [IsHausdorff (maximalIdeal S) S]

/-- Exact original-object consumer of `unramifiedSeparated_algEquiv_eq_of_residue`. -/
theorem actual_unramified_separated_residue_faithfulness_unramifiedSeparated_algEquiv_eq_of_residue_source (f g : S ≃ₐ[R] S)
    (h : ∀ x, residue S (f x) = residue S (g x)) : f = g :=
  unramifiedSeparated_algEquiv_eq_of_residue f g h

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing S]

/-- Exact original-object consumer of `localAlgebraAut_maximalIdeal_fixed`. -/
theorem actual_local_algebra_aut_maximal_stabilizer_localAlgebraAut_maximalIdeal_fixed_source (g : S ≃ₐ[R] S) :
    g • maximalIdeal S = maximalIdeal S :=
  localAlgebraAut_maximalIdeal_fixed g

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
  [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]

/-- Exact original-object consumer of `localAlgebraAutResidueHom_apply`. -/
theorem actual_local_algebra_aut_residue_hom_localAlgebraAutResidueHom_apply_source (g : S ≃ₐ[R] S) (x : S) :
    localAlgebraAutResidueHom g (residue S x) = residue S (g x) :=
  localAlgebraAutResidueHom_apply g x

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
  [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
  [Algebra.FormallyUnramified R S] [IsHausdorff (maximalIdeal S) S]

variable [Finite (S ≃ₐ[R] S)] [Algebra.IsInvariant R S (S ≃ₐ[R] S)]

/-- Exact original-object consumer of `unramifiedLocalResidueAutEquiv_apply`. -/
theorem actual_unramified_local_residue_aut_equiv_unramifiedLocalResidueAutEquiv_apply_source (g : S ≃ₐ[R] S) (x : S) :
    unramifiedLocalResidueAutEquiv g (residue S x) = residue S (g x) :=
  unramifiedLocalResidueAutEquiv_apply g x

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]

/-- Exact original-object consumer of `unramifiedLocalFieldResidueGaloisEquiv_apply`. -/
theorem actual_unramified_local_field_residue_galois_unramifiedLocalFieldResidueGaloisEquiv_apply_source (g : Gal(L/K)) (x : 𝒪[L]) :
    unramifiedLocalFieldResidueGaloisEquiv K L g (IsLocalRing.residue 𝒪[L] x) =
      IsLocalRing.residue 𝒪[L] (localFieldIntegerGaloisEquiv K L g x) :=
  unramifiedLocalFieldResidueGaloisEquiv_apply K L g x

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]

/-- Exact original-object consumer of `localFieldArithmeticFrobenius_generates`. -/
theorem actual_local_field_arithmetic_frobenius_localFieldArithmeticFrobenius_generates_source (g : Gal(L/K)) :
    g ∈ Subgroup.zpowers (localFieldArithmeticFrobenius K L) :=
  localFieldArithmeticFrobenius_generates K L g

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]

/-- Exact original-object consumer of `localFieldArithmeticH2Equiv_class`. -/
theorem actual_local_field_arithmetic_h2_normalization_localFieldArithmeticH2Equiv_class_source (u : Additive Kˣ) :
    localFieldArithmeticH2Equiv K L (localFieldArithmeticH2Class K L u) =
      (localFieldUnitOrder K u : ZMod (Module.finrank K L)) :=
  localFieldArithmeticH2Equiv_class K L u

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (n : ℕ) [NeZero n]

/-- Exact original-object consumer of `rationalCyclicInvariant_mem_range_iff`. -/
theorem actual_rational_cyclic_invariant_rationalCyclicInvariant_mem_range_iff_source (x : AddCircle (1 : ℚ)) :
    x ∈ (rationalCyclicInvariant n).range ↔ n • x = 0 :=
  rationalCyclicInvariant_mem_range_iff n x

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]

/-- Exact original-object consumer of `unramifiedLocalRationalH2Invariant_class`. -/
theorem actual_unramified_local_rational_h2_invariant_unramifiedLocalRationalH2Invariant_class_source (u : Additive Kˣ) :
    unramifiedLocalRationalH2Invariant K L (localFieldArithmeticH2Class K L u) =
      ↑((localFieldUnitOrder K u : ℚ) / Module.finrank K L) :=
  unramifiedLocalRationalH2Invariant_class K L u

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]

/-- Exact original-object consumer of `localFieldArithmeticFrobenius_eq_of_residue`. -/
theorem actual_local_field_arithmetic_frobenius_uniqueness_localFieldArithmeticFrobenius_eq_of_residue_source (g : Gal(L/K))
    (hg : ∀ x : 𝒪[L], IsLocalRing.residue 𝒪[L] (localFieldIntegerGaloisEquiv K L g x) =
      IsLocalRing.residue 𝒪[L] x ^ Nat.card 𝓀[K]) :
    g = localFieldArithmeticFrobenius K L :=
  localFieldArithmeticFrobenius_eq_of_residue K L g hg

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L M : Type) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M] [Normal K L]
  [ValuativeRel K] [ValuativeRel L] [ValuativeRel M]
  [TopologicalSpace K] [TopologicalSpace L] [TopologicalSpace M]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [IsNonarchimedeanLocalField M]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [(ValuativeRel.valuation L).HasExtension (ValuativeRel.valuation M)]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation M)]

/-- Exact original-object consumer of `localFieldIntegerGaloisEquiv_restrict`. -/
theorem actual_local_field_integer_galois_tower_localFieldIntegerGaloisEquiv_restrict_source (g : Gal(M/K)) (x : 𝒪[L]) :
    algebraMap 𝒪[L] 𝒪[M]
        (localFieldIntegerGaloisEquiv K L (AlgEquiv.restrictNormalHom L g) x) =
      localFieldIntegerGaloisEquiv K M g (algebraMap 𝒪[L] 𝒪[M] x) :=
  localFieldIntegerGaloisEquiv_restrict K L M g x

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L M : Type) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [IsGalois K L] [IsGalois K M]
  [ValuativeRel K] [ValuativeRel L] [ValuativeRel M]
  [TopologicalSpace K] [TopologicalSpace L] [TopologicalSpace M]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [IsNonarchimedeanLocalField M]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [(ValuativeRel.valuation L).HasExtension (ValuativeRel.valuation M)]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation M)]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[M]]

/-- Exact original-object consumer of `localFieldArithmeticFrobenius_restrict`. -/
theorem actual_local_field_arithmetic_frobenius_restriction_localFieldArithmeticFrobenius_restrict_source :
    AlgEquiv.restrictNormalHom L (localFieldArithmeticFrobenius K M) =
      localFieldArithmeticFrobenius K L :=
  localFieldArithmeticFrobenius_restrict K L M

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (F : FiniteGaloisIntermediateField K Ω) (b : Gal(Ω/K) → Ωˣ)
  (hvalues : ∀ g, (b g).val ∈ F.toIntermediateField)
  (hperiod : ∀ g u, AlgEquiv.restrictNormalHom F u = 1 → b (g * u) = b g)

include hvalues hperiod in
/-- Exact original-object consumer of `galoisUnitCochain_exists_finite_descent`. -/
theorem actual_galois_unit_cochain_finite_descent_galoisUnitCochain_exists_finite_descent_source :
    ∃ f : Gal(F/K) → Fˣ, ∀ g : Gal(Ω/K),
      Units.map F.toIntermediateField.val.toMonoidHom
        (f (AlgEquiv.restrictNormalHom F g)) = b g :=
  galoisUnitCochain_exists_finite_descent F b hvalues hperiod

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (F : FiniteGaloisIntermediateField K Ω)

/-- Exact original-object consumer of `galoisUnitFiniteCocycle_eq_coboundary_of_inflated_eq`. -/
theorem actual_galois_unit_finite_coboundary_reflection_galoisUnitFiniteCocycle_eq_coboundary_of_inflated_eq_source
    (c : Gal(F/K) × Gal(F/K) → Fˣ) (b : Gal(Ω/K) → Ωˣ)
    (hvalues : ∀ g, (b g).val ∈ F.toIntermediateField)
    (hperiod : ∀ g u, AlgEquiv.restrictNormalHom F u = 1 → b (g * u) = b g)
    (hc : ∀ g h : Gal(Ω/K),
      Units.map F.toIntermediateField.val.toMonoidHom
        (c (AlgEquiv.restrictNormalHom F g, AlgEquiv.restrictNormalHom F h)) =
          g • b h / b (g * h) * b g) :
    ∃ f : Gal(F/K) → Fˣ, ∀ σ τ : Gal(F/K),
      c (σ, τ) = Units.map σ (f τ) / f (σ * τ) * f σ :=
  galoisUnitFiniteCocycle_eq_coboundary_of_inflated_eq F c b hvalues hperiod hc

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L M : Type) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [FiniteDimensional K M] [IsGalois K L] [IsGalois K M]

variable [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K M)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K M)]

/-- Exact original-object consumer of `finiteGaloisUnitTowerH2Inflation_mk`. -/
theorem actual_finite_galois_unit_tower_inflation_finiteGaloisUnitTowerH2Inflation_mk_source
    (c : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits K L)) :
    finiteGaloisUnitTowerH2Inflation K L M (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (finiteGaloisUnitTowerCocycleInflation K L M c) :=
  finiteGaloisUnitTowerH2Inflation_mk K L M c

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (E F : FiniteGaloisIntermediateField K Ω) (hEF : E ≤ F)
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K E)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K E)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K F)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K F)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Exact original-object consumer of `galoisUnitFiniteStageH2Inflation_tower`. -/
theorem actual_galois_unit_finite_stage_tower_galoisUnitFiniteStageH2Inflation_tower_source
    (x : GaloisUnitContinuousH2 (K := K) (Ω := E)) :
    letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
    galoisUnitFiniteStageH2Inflation E x =
      galoisUnitFiniteStageH2Inflation F (finiteGaloisUnitTowerH2Inflation K E F x) :=
  galoisUnitFiniteStageH2Inflation_tower E F hEF x

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (E : FiniteGaloisIntermediateField K Ω)
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K E)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K E)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Exact original-object consumer of `continuousGaloisUnitH2_zero_detected_at_finite_stage`. -/
theorem actual_continuous_galois_unit_h2_finite_zero_detection_continuousGaloisUnitH2_zero_detected_at_finite_stage_source
    (x : GaloisUnitContinuousH2 (K := K) (Ω := E))
    (hx : galoisUnitFiniteStageH2Inflation E x = 0) :
    ∃ F : FiniteGaloisIntermediateField K Ω, ∃ hEF : E ≤ F,
      letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
      letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K F) := ⊥
      letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K F) := ⟨rfl⟩
      finiteGaloisUnitTowerH2Inflation K E F x = 0 :=
  continuousGaloisUnitH2_zero_detected_at_finite_stage E x hx

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L M N : Type) [Field K] [Field L] [Field M] [Field N]
  [Algebra K L] [Algebra K M] [Algebra K N]
  [Algebra L M] [Algebra L N] [Algebra M N]
  [IsScalarTower K L M] [IsScalarTower K L N]
  [IsScalarTower K M N] [IsScalarTower L M N]
  [FiniteDimensional K M] [FiniteDimensional K N]
  [IsGalois K L] [IsGalois K M] [IsGalois K N]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K M)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K M)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K N)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K N)]

/-- Exact original-object consumer of `finiteGaloisUnitTowerH2Inflation_comp`. -/
theorem actual_finite_galois_unit_tower_composition_finiteGaloisUnitTowerH2Inflation_comp_source
    (x : GaloisUnitContinuousH2 (K := K) (Ω := L)) :
    finiteGaloisUnitTowerH2Inflation K M N (finiteGaloisUnitTowerH2Inflation K L M x) =
      finiteGaloisUnitTowerH2Inflation K L N x :=
  finiteGaloisUnitTowerH2Inflation_comp K L M N x

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]

/-- Exact original-object consumer of `galoisUnitH2FiniteTransition_comp`. -/
theorem actual_galois_unit_h2_finite_directed_system_galoisUnitH2FiniteTransition_comp_source (E F H : FiniteGaloisIntermediateField K Ω)
    (hEF : E ≤ F) (hFH : F ≤ H) (x : GaloisUnitH2FiniteStage K Ω E) :
    galoisUnitH2FiniteTransition K Ω F H hFH
        (galoisUnitH2FiniteTransition K Ω E F hEF x) =
      galoisUnitH2FiniteTransition K Ω E H (hEF.trans hFH) x :=
  galoisUnitH2FiniteTransition_comp K Ω E F H hEF hFH x

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
  [DecidableEq (FiniteGaloisIntermediateField K Ω)]

variable [IsGalois K Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Exact original-object consumer of `galoisUnitH2FiniteColimitToH2_of`. -/
theorem actual_galois_unit_h2_finite_colimit_map_galoisUnitH2FiniteColimitToH2_of_source (F : FiniteGaloisIntermediateField K Ω)
    (x : GaloisUnitH2FiniteStage K Ω F) :
    galoisUnitH2FiniteColimitToH2 K Ω
      (Module.DirectLimit.of ℤ (FiniteGaloisIntermediateField K Ω)
        (GaloisUnitH2FiniteStage K Ω) (galoisUnitH2FiniteTransition K Ω) F x) =
      galoisUnitH2FiniteStageMap K Ω F x :=
  galoisUnitH2FiniteColimitToH2_of K Ω F x

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  [DecidableEq (FiniteGaloisIntermediateField K Ω)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Exact original-object consumer of `galoisUnitH2FiniteColimitEquiv_of`. -/
theorem actual_galois_unit_h2_finite_colimit_equiv_galoisUnitH2FiniteColimitEquiv_of_source (F : FiniteGaloisIntermediateField K Ω)
    (x : GaloisUnitH2FiniteStage K Ω F) :
    galoisUnitH2FiniteColimitEquiv K Ω
      (Module.DirectLimit.of ℤ (FiniteGaloisIntermediateField K Ω)
        (GaloisUnitH2FiniteStage K Ω) (galoisUnitH2FiniteTransition K Ω) F x) =
      galoisUnitH2FiniteStageMap K Ω F x :=
  galoisUnitH2FiniteColimitEquiv_of K Ω F x

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {R G : Type} [CommRing R] [Group G] (A : Rep R G) (g : G) (n : ℕ)

/-- Exact original-object consumer of `representationCyclicTwoCochainPeriodSum_coboundary`. -/
theorem actual_cyclic_two_cocycle_period_sum_representationCyclicTwoCochainPeriodSum_coboundary_source (hn : g ^ n = 1)
    (b : G → A) :
    representationCyclicTwoCochainPeriodSum A g n (groupCohomology.d₁₂ A b) =
      ∑ i ∈ Finset.range n, A.ρ (g ^ i) (b g) :=
  representationCyclicTwoCochainPeriodSum_coboundary A g n hn b

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {R G : Type} [CommRing R] [Group G] [Fintype G]
  (A : Rep R G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)

include hg

/-- Exact original-object consumer of `representationCyclicPeriodSum_coboundary_eq_norm`. -/
theorem actual_cyclic_generator_norm_sum_representationCyclicPeriodSum_coboundary_eq_norm_source (b : G → A) :
    representationCyclicTwoCochainPeriodSum A g (orderOf g) (groupCohomology.d₁₂ A b) =
      A.ρ.norm (b g) :=
  representationCyclicPeriodSum_coboundary_eq_norm A g hg b

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]

variable (g : Gal(L/K)) (hg : ∀ x, x ∈ Subgroup.zpowers g)

attribute [local instance] IsCyclic.commGroup

/-- Exact original-object consumer of `galoisGeneratorInvariantBaseEquiv_symm_coefficient`. -/
theorem actual_galois_generator_invariant_base_equiv_galoisGeneratorInvariantBaseEquiv_symm_coefficient_source
    (x : LinearMap.ker (Rep.applyAsHom (Rep.ofAlgebraAutOnUnits K L) g -
      𝟙 (Rep.ofAlgebraAutOnUnits K L)).hom.toLinearMap) :
    galoisUnitsBaseCoefficient (L := L)
      ((galoisGeneratorInvariantBaseEquiv g hg).symm x).toMul = x.val :=
  galoisGeneratorInvariantBaseEquiv_symm_coefficient g hg x

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]

variable (g : Gal(L/K)) (hg : ∀ x, x ∈ Subgroup.zpowers g)

/-- Exact original-object consumer of `galoisUnitCyclicPeriodBase_coboundary`. -/
theorem actual_galois_unit_cyclic_period_base_galoisUnitCyclicPeriodBase_coboundary_source
    (b : C(Gal(L/K), Rep.ofAlgebraAutOnUnits K L)) :
    galoisUnitCyclicPeriodBase g hg
        (continuousRepresentationCoboundaryTwo (Rep.ofAlgebraAutOnUnits K L)
          (discreteGaloisUnitAction_continuous (K := K) (Ω := L)) b) =
      Additive.ofMul (Units.map (Algebra.norm K (S := L))
        (Additive.toMul (Rep.toAdditive (b g)))) :=
  galoisUnitCyclicPeriodBase_coboundary g hg b

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]

variable (g : Gal(L/K)) (hg : ∀ x, x ∈ Subgroup.zpowers g)

/-- Exact original-object consumer of `cyclicGaloisH2PeriodNormMap_mk`. -/
theorem actual_cyclic_galois_h2_period_norm_map_cyclicGaloisH2PeriodNormMap_mk_source
    (c : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits K L)) :
    cyclicGaloisH2PeriodNormMap g hg (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (galoisUnitCyclicPeriodBase g hg c) :=
  cyclicGaloisH2PeriodNormMap_mk g hg c

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `zmodAdditionCarry_sum_one`. -/
theorem actual_z_mod_addition_carry_zmodAdditionCarry_sum_one_source {n : ℕ} (hn : 1 < n) :
    ∑ i ∈ Finset.range n, zmodAdditionCarry (i : ZMod n) 1 = 1 :=
  zmodAdditionCarry_sum_one hn

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {R G : Type} [CommRing R] [Group G] (A : Rep R G)
  {n : ℕ} [NeZero n] (χ : G →* Multiplicative (ZMod n))
  (a : A) (ha : ∀ x, A.ρ x a = a)

/-- Exact original-object consumer of `representationCarryCocycle_apply`. -/
theorem actual_representation_carry_cocycle_representationCarryCocycle_apply_source (x y : G) :
    representationCarryCocycle A χ a ha (x, y) =
      zmodAdditionCarry (χ x).toAdd (χ y).toAdd • a :=
  representationCarryCocycle_apply A χ a ha x y

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {R G : Type} [CommRing R] [Group G] (A : Rep R G)
  {n : ℕ} [NeZero n] (χ : G →* Multiplicative (ZMod n))
  (a : A) (ha : ∀ x, A.ρ x a = a)

/-- Exact original-object consumer of `representationCarryCocycle_period`. -/
theorem actual_representation_carry_period_representationCarryCocycle_period_source (g : G)
    (hχ : χ g = Multiplicative.ofAdd 1) (hn : 1 < n) :
    representationCyclicTwoCochainPeriodSum A g n
      (representationCarryCocycle A χ a ha) = a :=
  representationCarryCocycle_period A χ a ha g hχ hn

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]

variable (g : Gal(L/K)) (hg : ∀ x, x ∈ Subgroup.zpowers g)

/-- Exact original-object consumer of `galoisUnitCarryCocycle_period`. -/
theorem actual_galois_unit_carry_cocycle_galoisUnitCarryCocycle_period_source (u : Kˣ) (hn : 1 < Nat.card Gal(L/K)) :
    galoisUnitCyclicPeriodBase g hg (galoisUnitCarryCocycle g hg u) = Additive.ofMul u :=
  galoisUnitCarryCocycle_period g hg u hn

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]

variable (g : Gal(L/K)) (hg : ∀ x, x ∈ Subgroup.zpowers g)

/-- Exact original-object consumer of `cyclicGaloisH2PeriodNormMap_bijective`. -/
theorem actual_cyclic_galois_h2_period_surjective_cyclicGaloisH2PeriodNormMap_bijective_source
    [Finite (Additive Kˣ ⧸ LinearMap.range (galoisUnitFieldNormLinear (K := K) (L := L)))] :
    Function.Bijective (cyclicGaloisH2PeriodNormMap g hg) :=
  cyclicGaloisH2PeriodNormMap_bijective g hg

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `representationCyclicTwoCochainPeriodSum_repeat`. -/
theorem actual_cyclic_generator_repeated_period_representationCyclicTwoCochainPeriodSum_repeat_source
    {R G : Type} [CommRing R] [Group G] (A : Rep R G)
    (g : G) (n : ℕ) (hn : g ^ n = 1) (k : ℕ) (c : G × G → A) :
    representationCyclicTwoCochainPeriodSum A g (n * k) c =
      k • representationCyclicTwoCochainPeriodSum A g n c :=
  representationCyclicTwoCochainPeriodSum_repeat A g n hn k c

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]

/-- Exact original-object consumer of `localFieldPeriodH2Equiv_mk`. -/
theorem actual_local_field_period_h2_equiv_localFieldPeriodH2Equiv_mk_source
    (c : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits K L)) :
    letI : FiniteDimensional K L := localField_field_module_finite
    letI : IsCyclic Gal(L/K) :=
      (unramifiedLocalFieldResidueGaloisEquiv K L).isCyclic.mpr inferInstance
    localFieldPeriodH2Equiv K L (Submodule.Quotient.mk c) =
      (localFieldUnitOrder K (galoisUnitCyclicPeriodBase
        (localFieldArithmeticFrobenius K L) (localFieldArithmeticFrobenius_generates K L) c) :
          ZMod (Module.finrank K L)) :=
  localFieldPeriodH2Equiv_mk K L c

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]

/-- Exact original-object consumer of `localFieldPeriodRationalInvariant_mk`. -/
theorem actual_local_field_period_rational_invariant_localFieldPeriodRationalInvariant_mk_source
    (c : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits K L)) :
    letI : FiniteDimensional K L := localField_field_module_finite
    letI : IsCyclic Gal(L/K) :=
      (unramifiedLocalFieldResidueGaloisEquiv K L).isCyclic.mpr inferInstance
    localFieldPeriodRationalInvariant K L (Submodule.Quotient.mk c) =
      ↑((localFieldUnitOrder K (galoisUnitCyclicPeriodBase
        (localFieldArithmeticFrobenius K L) (localFieldArithmeticFrobenius_generates K L) c) : ℚ) /
          Module.finrank K L) :=
  localFieldPeriodRationalInvariant_mk K L c

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `representationCyclicPeriod_inflation`. -/
theorem actual_representation_period_inflation_representationCyclicPeriod_inflation_source
    {R G H : Type} [CommRing R] [Group G] [Group H]
    (A : Rep R G) (B : Rep R H) (φ : H →* G) (j : A →ₗ[R] B)
    (g : G) (h : H) (hφ : φ h = g) (n : ℕ) (hn : g ^ n = 1)
    (k : ℕ) (c : G × G → A) :
    representationCyclicTwoCochainPeriodSum B h (n * k)
        (fun p => j (c (φ p.1, φ p.2))) =
      k • j (representationCyclicTwoCochainPeriodSum A g n c) :=
  representationCyclicPeriod_inflation A B φ j g h hφ n hn k c

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L M : Type) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [FiniteDimensional K L] [FiniteDimensional K M] [FiniteDimensional L M]
  [IsGalois K L] [IsGalois K M] [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K M)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K M)]

variable (g : Gal(L/K)) (hg : ∀ x, x ∈ Subgroup.zpowers g)
  (h : Gal(M/K)) (hh : ∀ x, x ∈ Subgroup.zpowers h)

/-- Exact original-object consumer of `galoisUnitCyclicPeriodBase_tower`. -/
theorem actual_galois_unit_period_tower_galoisUnitCyclicPeriodBase_tower_source
    (hrestrict : AlgEquiv.restrictNormalHom L h = g)
    (c : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits K L)) :
    galoisUnitCyclicPeriodBase h hh (finiteGaloisUnitTowerCocycleInflation K L M c) =
      Module.finrank L M • galoisUnitCyclicPeriodBase g hg c :=
  galoisUnitCyclicPeriodBase_tower K L M g hg h hh hrestrict c

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L M : Type) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [IsGalois K L] [IsGalois K M]
  [ValuativeRel K] [ValuativeRel L] [ValuativeRel M]
  [TopologicalSpace K] [TopologicalSpace L] [TopologicalSpace M]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [IsNonarchimedeanLocalField M]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [(ValuativeRel.valuation L).HasExtension (ValuativeRel.valuation M)]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation M)]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[M]]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K M)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K M)]

/-- Exact original-object consumer of `localFieldPeriodRationalInvariant_inflation`. -/
theorem actual_local_field_period_invariant_inflation_localFieldPeriodRationalInvariant_inflation_source
    (x : GaloisUnitContinuousH2 (K := K) (Ω := L)) :
    letI : FiniteDimensional K L := localField_field_module_finite
    letI : FiniteDimensional K M := localField_field_module_finite
    localFieldPeriodRationalInvariant K M (finiteGaloisUnitTowerH2Inflation K L M x) =
      localFieldPeriodRationalInvariant K L x :=
  localFieldPeriodRationalInvariant_inflation K L M x

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `localField_exists_integral_residue_extension_polynomial`. -/
theorem actual_local_field_residue_extension_polynomial_localField_exists_integral_residue_extension_polynomial_source
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) [NeZero n] :
    ∃ F : 𝒪[K][X], F.Monic ∧ F.natDegree = n ∧
      (F.map (IsLocalRing.residue 𝒪[K])).natDegree = n ∧
      Irreducible (F.map (IsLocalRing.residue 𝒪[K])) ∧
      (F.map (IsLocalRing.residue 𝒪[K])).Separable ∧
      Irreducible (F.map (algebraMap 𝒪[K] K)) :=
  localField_exists_integral_residue_extension_polynomial K n

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `local_monic_separable_of_residue`. -/
theorem actual_local_monic_separable_reduction_local_monic_separable_of_residue_source {R : Type} [CommRing R]
    [IsLocalRing R] (f : R[X]) (hf : f.Monic)
    (hs : (f.map (IsLocalRing.residue R)).Separable) : f.Separable :=
  local_monic_separable_of_residue f hf hs

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `monic_separable_adjoinRoot_etale`. -/
theorem actual_monic_separable_adjoin_root_etale_monic_separable_adjoinRoot_etale_source {R : Type} [CommRing R]
    (f : R[X]) (hf : f.Monic) (hs : f.Separable) :
    Algebra.Etale R (AdjoinRoot f) :=
  monic_separable_adjoinRoot_etale f hf hs

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `monic_residue_irreducible_adjoinRoot_local`. -/
theorem actual_monic_residue_irreducible_local_algebra_monic_residue_irreducible_adjoinRoot_local_source
    {R : Type} [CommRing R] [IsLocalRing R] (f : R[X]) (hf : f.Monic)
    (hi : Irreducible (f.map (IsLocalRing.residue R))) :
    IsLocalRing (AdjoinRoot f) :=
  monic_residue_irreducible_adjoinRoot_local f hf hi

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `monic_residue_irreducible_adjoinRoot_dvr`. -/
theorem actual_monic_residue_irreducible_d_v_r_monic_residue_irreducible_adjoinRoot_dvr_source
    {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (f : R[X]) (hf : f.Monic)
    (hi : Irreducible (f.map (IsLocalRing.residue R))) :
    letI : IsDomain (AdjoinRoot f) := AdjoinRoot.isDomain_of_prime
      ((Polynomial.Monic.irreducible_of_irreducible_map
        (IsLocalRing.residue R) f hf hi).prime)
    IsDiscreteValuationRing (AdjoinRoot f) :=
  monic_residue_irreducible_adjoinRoot_dvr f hf hi

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `monic_adjoinRoot_isAdicComplete`. -/
theorem actual_finite_basis_adic_completeness_monic_adjoinRoot_isAdicComplete_source
    {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (f : Polynomial R) (hf : f.Monic) :
    IsAdicComplete (I.map (algebraMap R (AdjoinRoot f))) (AdjoinRoot f) :=
  monic_adjoinRoot_isAdicComplete I f hf

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `monicRootResidue_natCard`. -/
theorem actual_monic_root_residue_cardinality_monicRootResidue_natCard_source
    {R : Type} [CommRing R] [IsLocalRing R] [Finite (IsLocalRing.ResidueField R)]
    (f : R[X]) (hf : f.Monic) (hi : Irreducible (f.map (IsLocalRing.residue R))) :
    letI : IsLocalRing (AdjoinRoot f) := monic_residue_irreducible_adjoinRoot_local f hf hi
    Nat.card (IsLocalRing.ResidueField (AdjoinRoot f)) =
      Nat.card (IsLocalRing.ResidueField R) ^ f.natDegree :=
  monicRootResidue_natCard f hf hi

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `spectralFiniteExtension_isNonarchimedeanLocalField`. -/
theorem actual_spectral_finite_extension_local_field_spectralFiniteExtension_isNonarchimedeanLocalField_source
    (K L : Type) [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [LocallyCompactSpace K] [Field L] [Algebra K L]
    [FiniteDimensional K L] :
    letI : NontriviallyNormedField L := spectralNorm.nontriviallyNormedField K L
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel L := ValuativeRel.ofValuation (NormedField.valuation (K := L))
    IsNonarchimedeanLocalField L :=
  spectralFiniteExtension_isNonarchimedeanLocalField K L

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K : Type) [Field K] [ValuativeRel K]
  [UniformSpace K] [IsUniformAddGroup K] [IsNonarchimedeanLocalField K]

/-- Exact original-object consumer of `localFieldOriginalNorm_compatible`. -/
theorem actual_local_field_original_norm_localFieldOriginalNorm_compatible_source :
    letI : NontriviallyNormedField K := localFieldOriginalNorm K
    letI : IsUltrametricDist K := localFieldOriginalNorm_isUltrametric K
    (NormedField.valuation (K := K)).Compatible :=
  localFieldOriginalNorm_compatible K

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `spectralValuation_hasExtension`. -/
theorem actual_spectral_valuation_extension_spectralValuation_hasExtension_source
    (K L : Type) [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [ValuativeRel K] [(NormedField.valuation (K := K)).Compatible]
    [Field L] [Algebra K L] [FiniteDimensional K L] :
    letI : NontriviallyNormedField L := spectralNorm.nontriviallyNormedField K L
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel L := ValuativeRel.ofValuation (NormedField.valuation (K := L))
    (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L) :=
  spectralValuation_hasExtension K L

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `adicComplete_polynomial_splits_of_residue`. -/
theorem actual_adic_complete_residue_splitting_adicComplete_polynomial_splits_of_residue_source
    {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R]
    (f : R[X]) (hf : f.Monic)
    (hs : (f.map (residue R)).Separable)
    (hsp : (f.map (residue R)).Splits) : f.Splits :=
  adicComplete_polynomial_splits_of_residue f hf hs hsp

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `finiteResidue_complete_algebra_polynomial_splits`. -/
theorem actual_finite_residue_complete_algebra_splitting_finiteResidue_complete_algebra_polynomial_splits_source
    {R S : Type} [CommRing R] [CommRing S] [IsDomain S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [Module.Finite R S]
    [Finite (ResidueField R)] [IsAdicComplete (maximalIdeal S) S]
    (f : R[X]) (hf : f.Monic) (hi : Irreducible (f.map (residue R)))
    (hs : (f.map (residue R)).Separable)
    (a : S) (ha : aeval a f = 0) :
    (f.map (algebraMap R S)).Splits :=
  finiteResidue_complete_algebra_polynomial_splits f hf hi hs a ha

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (R K L : Type) [CommRing R] [Field K] [Field L]
  [Algebra R K] [IsFractionRing R K] [Algebra R L] [FaithfulSMul R L]

/-- Exact original-object consumer of `originalFractionScalarAlgebra_tower`. -/
theorem actual_original_fraction_scalar_algebra_originalFractionScalarAlgebra_tower_source :
    letI : Algebra K L := originalFractionScalarAlgebra R K L
    IsScalarTower R K L :=
  originalFractionScalarAlgebra_tower R K L

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `monicRootFraction_finrank_and_finite`. -/
theorem actual_monic_root_fraction_degree_monicRootFraction_finrank_and_finite_source
    (R K L : Type) [CommRing R] [IsDomain R] [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K] [Algebra R L] [Algebra K L]
    [IsScalarTower R K L] (f : R[X]) [IsDomain (AdjoinRoot f)]
    [Algebra (AdjoinRoot f) L] [IsFractionRing (AdjoinRoot f) L]
    [IsScalarTower R (AdjoinRoot f) L]
    (hf : f.Monic) (hd : 0 < f.natDegree) :
    Module.finrank K L = f.natDegree ∧ FiniteDimensional K L :=
  monicRootFraction_finrank_and_finite R K L f hf hd

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (R K L : Type) [CommRing R] [Field K] [Field L]
  [Algebra R K] [Algebra R L] [Algebra K L] [IsScalarTower R K L]
  (f : R[X]) [Algebra (AdjoinRoot f) L]
  [IsScalarTower R (AdjoinRoot f) L] [IsFractionRing (AdjoinRoot f) L]

/-- Exact original-object consumer of `adjoinRootFraction_isSplittingField`. -/
theorem actual_adjoin_root_fraction_generation_adjoinRootFraction_isSplittingField_source
    [Algebra.IsAlgebraic K L] (hf : f.Monic)
    (hs : ((f.map (algebraMap R K)).map (algebraMap K L)).Splits) :
    (f.map (algebraMap R K)).IsSplittingField K L :=
  adjoinRootFraction_isSplittingField R K L f hf hs

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  (f : Polynomial 𝒪[K]) (hf : f.Monic)
  [IsDomain (AdjoinRoot f)] [IsIntegrallyClosed (AdjoinRoot f)]
  [Algebra (AdjoinRoot f) L] [IsFractionRing (AdjoinRoot f) L]
  [IsScalarTower 𝒪[K] (AdjoinRoot f) L]

include hf in
omit [IsDomain (AdjoinRoot f)] in
/-- Exact original-object consumer of `localFieldMonicRootInteger_etale`. -/
theorem actual_local_field_monic_root_integer_equiv_localFieldMonicRootInteger_etale_source
    (hs : (f.map (IsLocalRing.residue 𝒪[K])).Separable) :
    Algebra.Etale 𝒪[K] 𝒪[L] :=
  localFieldMonicRootInteger_etale K L f hf hs

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `localField_exists_unramified_galois_extension`. -/
theorem actual_local_field_unramified_extension_existence_localField_exists_unramified_galois_extension_source
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) [NeZero n] :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L)
      (_ : ValuativeRel L) (_ : TopologicalSpace L)
      (_ : IsNonarchimedeanLocalField L)
      (_ : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)),
      FiniteDimensional K L ∧ IsGalois K L ∧
        Algebra.FormallyUnramified 𝒪[K] 𝒪[L] ∧ Module.finrank K L = n :=
  localField_exists_unramified_galois_extension K n

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {K L Ω : Type} [Field K] [Field L] [Field Ω]
  [Algebra K L] [Algebra K Ω] [FiniteDimensional K L] [IsGalois K L]

/-- Exact original-object consumer of `finiteGalois_exists_original_stage`. -/
theorem actual_finite_galois_embedding_stage_finiteGalois_exists_original_stage_source [IsSepClosed Ω] :
    ∃ E : FiniteGaloisIntermediateField K Ω,
      Nonempty (L ≃ₐ[K] E) ∧ Module.finrank K E = Module.finrank K L :=
  finiteGalois_exists_original_stage (K := K) (L := L) (Ω := Ω)

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L M : Type) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M]
  [ValuativeRel K] [ValuativeRel L] [ValuativeRel M]
  [TopologicalSpace K] [TopologicalSpace L] [TopologicalSpace M]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [IsNonarchimedeanLocalField M]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation M)]

/-- Exact original-object consumer of `localFieldIntegerAlgEquiv_coefficient`. -/
theorem actual_local_field_integer_alg_equiv_localFieldIntegerAlgEquiv_coefficient_source (e : L ≃ₐ[K] M) (x : 𝒪[L]) :
    algebraMap 𝒪[M] M (localFieldIntegerAlgEquiv K L M e x) =
      e (algebraMap 𝒪[L] L x) :=
  localFieldIntegerAlgEquiv_coefficient K L M e x

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `localField_exists_original_unramified_stage`. -/
theorem actual_local_field_original_unramified_stage_existence_localField_exists_original_unramified_stage_source
    (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosed Ω]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (n : ℕ) [NeZero n] :
    ∃ E : FiniteGaloisIntermediateField K Ω,
      ∃ (_ : ValuativeRel E) (_ : TopologicalSpace E)
        (_ : IsNonarchimedeanLocalField E)
        (_ : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)),
        Algebra.FormallyUnramified 𝒪[K] 𝒪[E] ∧ Module.finrank K E = n :=
  localField_exists_original_unramified_stage K Ω n

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (R K L : Type) [CommRing R] [IsDomain R] [Field K] [Field L]
  [Algebra R K] [IsFractionRing R K] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [FiniteDimensional K L] [IsGalois K L]

/-- Exact original-object consumer of `exists_integral_normal_basis`. -/
theorem actual_integral_normal_basis_lattice_exists_integral_normal_basis_source :
    ∃ b : Module.Basis Gal(L/K) K L,
      (∀ σ, b σ = σ (b 1)) ∧ ∀ σ, IsIntegral R (b σ) :=
  exists_integral_normal_basis R K L

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {R G : Type} [CommRing R] [Group G] [Fintype G]
  (A : Rep.{0} R G) (b : Module.Basis G R A)

/-- Exact original-object consumer of `regularBasis_groupCohomology_isZero`. -/
theorem actual_regular_basis_cohomology_regularBasis_groupCohomology_isZero_source
    (hb : ∀ g h, A.ρ g (b h) = b (g * h)) (n : ℕ) :
    Limits.IsZero (groupCohomology A (n + 1)) :=
  regularBasis_groupCohomology_isZero A b hb n

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {R G : Type} [CommRing R] [Group G] [Fintype G]
  (A : Rep.{0} R G) (b : Module.Basis G R A)
  (hb : ∀ g h, A.ρ g (b h) = b (g * h))

include hb in
/-- Exact original-object consumer of `regularBasis_invariant_mem_norm`. -/
theorem actual_regular_basis_norm_regularBasis_invariant_mem_norm_source
    (a : A) (ha : ∀ g, A.ρ g a = a) :
    ∃ x : A, ∑ g : G, A.ρ g x = a :=
  regularBasis_invariant_mem_norm A b hb a ha

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (R K L : Type) [CommRing R] [IsDomain R] [Field K] [Field L]
  [Algebra R K] [IsFractionRing R K] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [FiniteDimensional K L] [IsGalois K L]
  (b : Module.Basis Gal(L/K) K L) (hb : ∀ σ, b σ = σ (b 1))

omit [IsGalois K L] in
/-- Exact original-object consumer of `normalBasisLattice_invariant_mem_norm`. -/
theorem actual_normal_basis_lattice_cohomology_normalBasisLattice_invariant_mem_norm_source
    (a : Submodule.span R (Set.range b))
    (ha : ∀ σ, (normalBasisLatticeRep R K L b hb).ρ σ a = a) :
    ∃ x : Submodule.span R (Set.range b),
      ∑ σ : Gal(L/K), (normalBasisLatticeRep R K L b hb).ρ σ x = a :=
  normalBasisLattice_invariant_mem_norm R K L b hb a ha

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {R K V ι : Type} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [AddCommGroup V]
  [Module K V] [Module R V] [IsScalarTower R K V] [Finite ι]

/-- Exact original-object consumer of `fullBasis_span_absorbs_uniformizer_power`. -/
theorem actual_full_basis_lattice_bounds_fullBasis_span_absorbs_uniformizer_power_source
    [IsDiscreteValuationRing R] (b : Module.Basis ι K V)
    (N : Submodule R V) (hN : N.FG) (π : R) (hπ : Irreducible π) :
    ∃ n : ℕ, ∀ x ∈ N, π ^ n • x ∈ Submodule.span R (Set.range b) :=
  fullBasis_span_absorbs_uniformizer_power b N hN π hπ

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `smallLattice_scaled_product`. -/
theorem actual_small_lattice_product_smallLattice_scaled_product_source
    {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    (A : Submodule R S) (π : R) (n : ℕ)
    (hA : ∀ z : S, π ^ n • z ∈ A) (x y : S) :
    ∃ z : S, z ∈ A ∧
      (π ^ (n + 1) • x) * (π ^ (n + 1) • y) = π ^ (n + 2) • z :=
  smallLattice_scaled_product A π n hA x y

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `localField_exists_integral_normal_lattice`. -/
theorem actual_local_field_integral_normal_lattice_localField_exists_integral_normal_lattice_source
    (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
    (π : 𝒪[K]) (hπ : Irreducible π) :
    ∃ (b : Module.Basis Gal(L/K) K L) (n : ℕ),
      (∀ σ, b σ = σ (b 1)) ∧
      (∀ x ∈ Submodule.span 𝒪[K] (Set.range b),
        x ∈ (ValuativeRel.valuation L).integer) ∧
      ∀ x : 𝒪[L], π ^ n • (x : L) ∈ Submodule.span 𝒪[K] (Set.range b) :=
  localField_exists_integral_normal_lattice K L π hπ

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `localField_exists_complete_normal_lattice`. -/
theorem actual_local_field_complete_normal_lattice_localField_exists_complete_normal_lattice_source
    (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
    (π : 𝒪[K]) (hπ : Irreducible π) :
    letI : FiniteDimensional K L := localField_field_module_finite
    ∃ (b : Module.Basis Gal(L/K) K L) (hb : ∀ σ, b σ = σ (b 1)) (n : ℕ),
      (∀ x ∈ Submodule.span 𝒪[K] (Set.range b),
        x ∈ (ValuativeRel.valuation L).integer) ∧
      (∀ x : 𝒪[L], π ^ n • (x : L) ∈ Submodule.span 𝒪[K] (Set.range b)) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal 𝒪[K])
        (Submodule.span 𝒪[K] (Set.range b)) ∧
      (∀ m : ℕ, CategoryTheory.Limits.IsZero
        (groupCohomology (normalBasisLatticeRep 𝒪[K] K L b hb) (m + 1))) ∧
      ∀ a : Submodule.span 𝒪[K] (Set.range b),
        (∀ σ, (normalBasisLatticeRep 𝒪[K] K L b hb).ρ σ a = a) →
        ∃ x : Submodule.span 𝒪[K] (Set.range b),
          ∑ σ : Gal(L/K), (normalBasisLatticeRep 𝒪[K] K L b hb).ρ σ x = a :=
  localField_exists_complete_normal_lattice K L π hπ

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `compactSubmonoid_inv_mem`. -/
theorem actual_compact_submonoid_inverse_compactSubmonoid_inv_mem_source
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    (M : Submonoid G) (hM : IsCompact (M : Set G)) {u : G} (hu : u ∈ M) :
    u⁻¹ ∈ M :=
  compactSubmonoid_inv_mem M hM hu

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {L : Type*} [Field L] [TopologicalSpace L]
  [IsTopologicalDivisionRing L] [T2Space L]
  (A : AddSubgroup L) (hmul : ∀ x ∈ A, ∀ y ∈ A, x * y ∈ A)

include hmul in
/-- Exact original-object consumer of `latticeUnitSubmonoid_inverse_sub_one_mem`. -/
theorem actual_compact_lattice_unit_subgroup_latticeUnitSubmonoid_inverse_sub_one_mem_source
    (hA : IsCompact (A : Set L)) (hunit : ∀ x ∈ A, (1 : L) + x ≠ 0)
    (u : Lˣ) (hu : (u : L) - 1 ∈ A) :
    ((u⁻¹ : Lˣ) : L) - 1 ∈ A :=
  latticeUnitSubmonoid_inverse_sub_one_mem A hmul hA hunit u hu

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]

/-- Exact original-object consumer of `localField_finite_lattice_isCompact`. -/
theorem actual_local_field_compact_lattice_localField_finite_lattice_isCompact_source
    (A : Submodule 𝒪[K] L) (hA : A.FG) : IsCompact (A : Set L) :=
  localField_finite_lattice_isCompact K L A hA

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `compact_exists_of_additive_filtered_approximations`. -/
theorem actual_compact_filtered_exactness_compact_exists_of_additive_filtered_approximations_source
    {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
    [AddCommGroup Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
    (f : X → Y) (hf : Continuous f) (F : ℕ → AddSubgroup Y)
    (hF : ∀ n, IsClosed (F n : Set Y)) (hmono : ∀ n, F (n + 1) ≤ F n)
    (hsep : ∀ z : Y, (∀ n, z ∈ F n) → z = 0)
    (y : Y) (happrox : ∀ n, ∃ x, f x - y ∈ F n) : ∃ x, f x = y :=
  compact_exists_of_additive_filtered_approximations f hf F hF hmono hsep y happrox

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]

/-- Exact original-object consumer of `scalarLatticeImage_product_gain`. -/
theorem actual_scaled_lattice_products_scalarLatticeImage_product_gain_source
    (A : Submodule R S) (B : Subring S) (π : R) (n : ℕ)
    (hupper : ∀ x ∈ A, x ∈ B) (hlower : ∀ x ∈ B, π ^ n • x ∈ A)
    {x y : S} (hx : x ∈ scalarLatticeImage A (π ^ (n + 1)))
    (hy : y ∈ scalarLatticeImage A (π ^ (n + 1))) :
    ∃ z ∈ scalarLatticeImage A (π ^ (n + 1)), x * y = π • z :=
  scalarLatticeImage_product_gain A B π n hupper hlower hx hy

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]

/-- Exact original-object consumer of `localField_exists_compact_small_unit_subgroup`. -/
theorem actual_local_field_small_lattice_units_localField_exists_compact_small_unit_subgroup_source
    (A : Submodule 𝒪[K] L) (hA : A.FG)
    (π : 𝒪[K]) (hπ : ¬ IsUnit π) (n : ℕ)
    (hupper : ∀ x ∈ A, x ∈ (ValuativeRel.valuation L).integer)
    (hlower : ∀ x ∈ (ValuativeRel.valuation L).integer, π ^ n • x ∈ A) :
    ∃ U : Subgroup Lˣ, IsCompact (U : Set Lˣ) ∧
      ∀ u : Lˣ, u ∈ U ↔ (u : L) - 1 ∈ scalarLatticeImage A (π ^ (n + 1)) :=
  localField_exists_compact_small_unit_subgroup K L A hA π hπ n hupper hlower

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `galoisNorm_small_lattice_error`. -/
theorem actual_small_lattice_norm_error_galoisNorm_small_lattice_error_source
    (R K L : Type) [CommRing R] [Field K] [Field L]
    [Algebra R K] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L] [IsGalois K L]
    (A : Submodule R L) (B : Subring L) (π : R) (n : ℕ)
    (hupper : ∀ x ∈ A, x ∈ B) (hlower : ∀ x ∈ B, π ^ n • x ∈ A)
    (hstable : ∀ σ : Gal(L/K), ∀ x ∈ A, σ x ∈ A)
    {x : L} (hx : x ∈ scalarLatticeImage A (π ^ (n + 1))) :
    algebraMap K L (Algebra.norm K (1 + x)) - 1 -
        algebraMap K L (Algebra.trace K L x) ∈
      scalarLatticeImage (scalarLatticeImage A (π ^ (n + 1))) π :=
  galoisNorm_small_lattice_error R K L A B π n hupper hlower hstable hx

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `localField_exists_normal_lattice_unit_subgroup`. -/
theorem actual_local_field_normal_lattice_units_localField_exists_normal_lattice_unit_subgroup_source
    (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
    (π : 𝒪[K]) (hπ : Irreducible π) :
    ∃ (b : Module.Basis Gal(L/K) K L) (n : ℕ) (U : Subgroup Lˣ),
      (∀ σ, b σ = σ (b 1)) ∧
      (∀ x ∈ Submodule.span 𝒪[K] (Set.range b),
        x ∈ (ValuativeRel.valuation L).integer) ∧
      (∀ x : 𝒪[L], π ^ n • (x : L) ∈ Submodule.span 𝒪[K] (Set.range b)) ∧
      IsCompact (U : Set Lˣ) ∧
      (∀ u : Lˣ, u ∈ U ↔ (u : L) - 1 ∈
        scalarLatticeImage (Submodule.span 𝒪[K] (Set.range b)) (π ^ (n + 1))) ∧
      ∀ (σ : Gal(L/K)) (u : Lˣ), u ∈ U →
        Units.map (σ : L →+* L).toMonoidHom u ∈ U :=
  localField_exists_normal_lattice_unit_subgroup K L π hπ

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)] in
/-- Exact original-object consumer of `localField_scaled_lattice_isOpen`. -/
theorem actual_local_field_open_lattice_localField_scaled_lattice_isOpen_source
    (A : Submodule 𝒪[K] L) (π : 𝒪[K]) (hπ : π ≠ 0) (n : ℕ)
    (hbound : ∀ x : 𝒪[L], π ^ n • (x : L) ∈ A) :
    IsOpen (scalarLatticeImage A (π ^ (n + 1)) : Set L) :=
  localField_scaled_lattice_isOpen K L A π hπ n hbound

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]

/-- Exact original-object consumer of `localField_exists_open_normal_lattice_unit_subgroup`. -/
theorem actual_local_field_open_small_units_localField_exists_open_normal_lattice_unit_subgroup_source [IsGalois K L]
    (π : 𝒪[K]) (hπ : Irreducible π) :
    ∃ (b : Module.Basis Gal(L/K) K L) (n : ℕ) (U : Subgroup Lˣ),
      (∀ σ, b σ = σ (b 1)) ∧
      (∀ x ∈ Submodule.span 𝒪[K] (Set.range b),
        x ∈ (ValuativeRel.valuation L).integer) ∧
      (∀ x : 𝒪[L], π ^ n • (x : L) ∈ Submodule.span 𝒪[K] (Set.range b)) ∧
      IsCompact (U : Set Lˣ) ∧ IsOpen (U : Set Lˣ) ∧
      Finite (𝒪[L]ˣ ⧸ U.comap (Units.map (algebraMap 𝒪[L] L).toMonoidHom)) ∧
      (∀ u : Lˣ, u ∈ U ↔ (u : L) - 1 ∈
        scalarLatticeImage (Submodule.span 𝒪[K] (Set.range b)) (π ^ (n + 1))) ∧
      ∀ (σ : Gal(L/K)) (u : Lˣ), u ∈ U →
        Units.map (σ : L →+* L).toMonoidHom u ∈ U :=
  localField_exists_open_normal_lattice_unit_subgroup K L π hπ

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {L : Type*} [Field L] (B : Subring L) (U : Subgroup Lˣ)
  (hU : ∀ u ∈ U, (u : L) ∈ B)

/-- Exact original-object consumer of `subringUnitSubgroupEquiv_coefficient`. -/
theorem actual_subring_unit_subgroup_equiv_subringUnitSubgroupEquiv_coefficient_source
    (v : U.comap (Units.map B.subtype.toMonoidHom)) :
    (((subringUnitSubgroupEquiv B U hU v : U) : Lˣ) : L) =
      (((v : Bˣ) : B) : L) :=
  subringUnitSubgroupEquiv_coefficient B U hU v

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]

omit [TopologicalSpace K] [TopologicalSpace L] [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L] in
/-- Exact original-object consumer of `localFieldSmallUnitIntegerEquiv_coefficient`. -/
theorem actual_local_field_integral_small_units_localFieldSmallUnitIntegerEquiv_coefficient_source
    (A : Submodule 𝒪[K] L) (r : 𝒪[K])
    (hupper : ∀ x ∈ A, x ∈ (ValuativeRel.valuation L).integer)
    (U : Subgroup Lˣ)
    (hU : ∀ u : Lˣ, u ∈ U ↔ (u : L) - 1 ∈ scalarLatticeImage A r)
    (v : U.comap (Units.map (algebraMap 𝒪[L] L).toMonoidHom)) :
    (((localFieldSmallUnitIntegerEquiv K L A r hupper U hU v : U) : Lˣ) : L) =
      (((v : 𝒪[L]ˣ) : 𝒪[L]) : L) :=
  localFieldSmallUnitIntegerEquiv_coefficient K L A r hupper U hU v

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {R L : Type} [CommRing R] [Field L] [Algebra R L]
  (A B : Submodule R L) (U : Subgroup Lˣ)
  (hU : ∀ u : Lˣ, u ∈ U ↔ (u : L) - 1 ∈ A)

/-- Exact original-object consumer of `smallUnitGradedMap_surjective`. -/
theorem actual_small_unit_graded_quotient_smallUnitGradedMap_surjective_source
    (hmul : ∀ x ∈ A, ∀ y ∈ A, x * y ∈ B)
    (hunit : ∀ a ∈ A, (1 : L) + a ≠ 0) :
    Function.Surjective (smallUnitGradedMap A B U hU hmul) :=
  smallUnitGradedMap_surjective A B U hU hmul hunit

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (R K L : Type) [CommRing R] [IsDomain R] [Field K] [Field L]
  [Algebra R K] [IsFractionRing R K] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [FiniteDimensional K L] [IsGalois K L]
  (b : Module.Basis Gal(L/K) K L) (hb : ∀ σ, b σ = σ (b 1)) (r : R)

omit [IsGalois K L] in
/-- Exact original-object consumer of `scalarNormalLattice_invariant_mem_norm`. -/
theorem actual_scalar_normal_lattice_cohomology_scalarNormalLattice_invariant_mem_norm_source (hr : r ≠ 0)
    (a : scalarNormalLatticeRep R K L b hb r)
    (ha : ∀ σ, (scalarNormalLatticeRep R K L b hb r).ρ σ a = a) :
    ∃ x : scalarNormalLatticeRep R K L b hb r,
      ∑ σ : Gal(L/K), (scalarNormalLatticeRep R K L b hb r).ρ σ x = a :=
  scalarNormalLattice_invariant_mem_norm R K L b hb r hr a ha

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {R G : Type} [CommRing R] [Group G] (A : Rep R G) (r : R)

/-- Exact original-object consumer of `repScalarQuotient_groupCohomology_isZero`. -/
theorem actual_scalar_representation_quotient_repScalarQuotient_groupCohomology_isZero_source
    (hinj : Function.Injective (fun x : A => r • x)) (n : ℕ)
    (hn : Limits.IsZero (groupCohomology A n))
    (hs : Limits.IsZero (groupCohomology A (n + 1))) :
    Limits.IsZero (groupCohomology (repScalarQuotient A r) n) :=
  repScalarQuotient_groupCohomology_isZero A r hinj n hn hs

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {R G : Type} [CommRing R] [Group G] (A : Rep R G)

/-- Exact original-object consumer of `repScalarQuotient_invariant_mem_norm`. -/
theorem actual_scalar_quotient_invariant_lift_repScalarQuotient_invariant_mem_norm_source [Fintype G] (r : R)
    (hinj : Function.Injective (fun x : A => r • x))
    (hA : Limits.IsZero (groupCohomology A 1))
    (hNorm : ∀ a : A, (∀ g, A.ρ g a = a) → ∃ x : A, ∑ g : G, A.ρ g x = a)
    (q : repScalarQuotient A r)
    (hq : ∀ g, (repScalarQuotient A r).ρ g q = q) :
    ∃ x : repScalarQuotient A r, ∑ g : G, (repScalarQuotient A r).ρ g x = q :=
  repScalarQuotient_invariant_mem_norm A r hinj hA hNorm q hq

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (R K L : Type) [CommRing R] [IsDomain R] [Field K] [Field L]
  [Algebra R K] [IsFractionRing R K] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [FiniteDimensional K L] [IsGalois K L]
  (b : Module.Basis Gal(L/K) K L) (hb : ∀ σ, b σ = σ (b 1))
  (r s : R)

omit [IsGalois K L] in
/-- Exact original-object consumer of `scalarNormalLatticeQuotient_invariant_mem_norm`. -/
theorem actual_scalar_normal_lattice_quotient_scalarNormalLatticeQuotient_invariant_mem_norm_source
    (hr : r ≠ 0) (hs : s ≠ 0)
    (q : repScalarQuotient (scalarNormalLatticeRep R K L b hb r) s)
    (hq : ∀ σ,
      (repScalarQuotient (scalarNormalLatticeRep R K L b hb r) s).ρ σ q = q) :
    ∃ x : repScalarQuotient (scalarNormalLatticeRep R K L b hb r) s,
      ∑ σ : Gal(L/K),
        (repScalarQuotient (scalarNormalLatticeRep R K L b hb r) s).ρ σ x = q :=
  scalarNormalLatticeQuotient_invariant_mem_norm R K L b hb r s hr hs q hq

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L : Type) [Field K] [Field L] [Algebra K L]
  (U : Subgroup Lˣ)
  (hstable : ∀ (σ : Gal(L/K)) (u : Lˣ), u ∈ U →
    Units.map (σ : L →+* L).toMonoidHom u ∈ U)

variable (R : Type) [CommRing R] [IsDomain R]
  [Algebra R K] [IsFractionRing R K] [Algebra R L]
  [IsScalarTower R K L] [FiniteDimensional K L] [IsGalois K L]
  (b : Module.Basis Gal(L/K) K L) (hb : ∀ σ, b σ = σ (b 1)) (r s : R)
  (hU : ∀ u : Lˣ, u ∈ U ↔ (u : L) - 1 ∈
    scalarLatticeImage (Submodule.span R (Set.range b)) r)
  (hmul : ∀ x ∈ scalarLatticeImage (Submodule.span R (Set.range b)) r,
    ∀ y ∈ scalarLatticeImage (Submodule.span R (Set.range b)) r,
    x * y ∈ scalarLatticeImage
      (scalarLatticeImage (Submodule.span R (Set.range b)) r) s)

omit [IsDomain R] [IsFractionRing R K] [FiniteDimensional K L] [IsGalois K L] in
/-- Exact original-object consumer of `normalLatticeUnitGradedMap_equivariant`. -/
theorem actual_normal_lattice_unit_graded_map_normalLatticeUnitGradedMap_equivariant_source (σ : Gal(L/K)) (u : Additive U) :
    normalLatticeUnitGradedMap K L U R b hb r s hU hmul
        ((galoisUnitSubgroupMap K L U hstable σ).toAdditive u) =
      (repScalarQuotient (scalarNormalLatticeRep R K L b hb r) s).ρ σ
        (normalLatticeUnitGradedMap K L U R b hb r s hU hmul u) :=
  normalLatticeUnitGradedMap_equivariant K L U hstable R b hb r s hU hmul σ u

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {R G U : Type} [CommRing R] [Group G] [CommGroup U]
  [MulDistribMulAction G U] (A : Rep R G) (f : Additive U →+ A)
  (hf : ∀ (g : G) (u : U), f (Additive.ofMul (g • u)) = A.ρ g (f (Additive.ofMul u)))

include hf in
/-- Exact original-object consumer of `unitGraded_cocycle_correction`. -/
theorem actual_unit_graded_correction_unitGraded_cocycle_correction_source (hsurj : Function.Surjective f)
    (hA : Limits.IsZero (groupCohomology A 1)) (c : G → U)
    (hc : ∀ g h, c (g * h) = (g • c h) * c g) :
    ∃ u : U, ∀ g, f (Additive.ofMul (c g / ((g • u) / u))) = 0 :=
  unitGraded_cocycle_correction A f hf hsurj hA c hc

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (R K L : Type) [CommRing R] [IsDomain R] [Field K] [Field L]
  [Algebra R K] [IsFractionRing R K] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [FiniteDimensional K L] [IsGalois K L]
  (b : Module.Basis Gal(L/K) K L) (hb : ∀ σ, b σ = σ (b 1))
  (r s : R) (hr : r ≠ 0) (hs : s ≠ 0) (U : Subgroup Lˣ)
  (hstable : ∀ (σ : Gal(L/K)) (u : Lˣ), u ∈ U →
    Units.map (σ : L →+* L).toMonoidHom u ∈ U)
  (hU : ∀ u : Lˣ, u ∈ U ↔ (u : L) - 1 ∈
    scalarLatticeImage (Submodule.span R (Set.range b)) r)
  (hmul : ∀ x ∈ scalarLatticeImage (Submodule.span R (Set.range b)) r,
    ∀ y ∈ scalarLatticeImage (Submodule.span R (Set.range b)) r,
    x * y ∈ scalarLatticeImage
      (scalarLatticeImage (Submodule.span R (Set.range b)) r) s)
  (hunit : ∀ a ∈ scalarLatticeImage (Submodule.span R (Set.range b)) r,
    (1 : L) + a ≠ 0)

include hb hr hs hU hmul hunit in
omit [IsGalois K L] in
/-- Exact original-object consumer of `normalLatticeUnit_norm_correction`. -/
theorem actual_normal_lattice_unit_correction_normalLatticeUnit_norm_correction_source (u : U)
    (hu : ∀ σ : Gal(L/K), galoisUnitSubgroupMap K L U hstable σ u = u) :
    ∃ v : U,
      ((((u / ∏ σ : Gal(L/K), galoisUnitSubgroupMap K L U hstable σ v) : U) : Lˣ) : L) - 1 ∈
        scalarLatticeImage (scalarLatticeImage (Submodule.span R (Set.range b)) r) s :=
  normalLatticeUnit_norm_correction R K L b hb r s hr hs U hstable hU hmul hunit u hu

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]

/-- Exact original-object consumer of `scalarLatticeImage_level_product_gain`. -/
theorem actual_scalar_lattice_filtration_scalarLatticeImage_level_product_gain_source (A : Submodule R S) (π : R)
    (hmul : ∀ a ∈ A, ∀ b ∈ A, a * b ∈ scalarLatticeImage A π)
    (j : ℕ) {x y : S}
    (hx : x ∈ scalarLatticeImage A (π ^ j))
    (hy : y ∈ scalarLatticeImage A (π ^ j)) :
    x * y ∈ scalarLatticeImage (scalarLatticeImage A (π ^ j)) π :=
  scalarLatticeImage_level_product_gain A π hmul j hx hy

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `scalarLatticeImage_separated_of_isHausdorff`. -/
theorem actual_scalar_lattice_filtration_separation_scalarLatticeImage_separated_of_isHausdorff_source
    {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    (A : Submodule R S) (I : Ideal R) [IsHausdorff I A]
    (π : R) (hπ : π ∈ I) (x : S)
    (hx : ∀ j : ℕ, x ∈ scalarLatticeImage A (π ^ j)) : x = 0 :=
  scalarLatticeImage_separated_of_isHausdorff A I π hπ x hx

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `localField_exists_scalar_unit_filtration`. -/
theorem actual_local_field_scalar_unit_filtration_localField_exists_scalar_unit_filtration_source
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
    (A : Submodule 𝒪[K] L) (hA : A.FG) (π : 𝒪[K])
    (hmul : ∀ x ∈ A, ∀ y ∈ A, x * y ∈ scalarLatticeImage A π)
    (hunit : ∀ x ∈ A, (1 : L) + x ≠ 0)
    (hstable : ∀ σ : Gal(L/K), ∀ x ∈ A, σ x ∈ A) :
    ∃ U : ℕ → Subgroup Lˣ, ∀ j,
      IsCompact (U j : Set Lˣ) ∧
      (∀ u : Lˣ, u ∈ U j ↔ (u : L) - 1 ∈ scalarLatticeImage A (π ^ j)) ∧
      (∀ (σ : Gal(L/K)) (u : Lˣ), u ∈ U j →
        Units.map (σ : L →+* L).toMonoidHom u ∈ U j) ∧
      U (j + 1) ≤ U j :=
  localField_exists_scalar_unit_filtration K L A hA π hmul hunit hstable

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `localField_exists_separated_normal_unit_filtration`. -/
theorem actual_local_field_separated_normal_unit_filtration_localField_exists_separated_normal_unit_filtration_source
    (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
    (π : 𝒪[K]) (hπ : Irreducible π) :
    ∃ (b : Module.Basis Gal(L/K) K L) (n : ℕ) (U : ℕ → Subgroup Lˣ),
      (∀ σ, b σ = σ (b 1)) ∧
      (∀ x ∈ Submodule.span 𝒪[K] (Set.range b),
        x ∈ (ValuativeRel.valuation L).integer) ∧
      (∀ x : 𝒪[L], π ^ n • (x : L) ∈ Submodule.span 𝒪[K] (Set.range b)) ∧
      (∀ j, IsCompact (U j : Set Lˣ) ∧
        (∀ u : Lˣ, u ∈ U j ↔ (u : L) - 1 ∈
          scalarLatticeImage
            (scalarLatticeImage (Submodule.span 𝒪[K] (Set.range b)) (π ^ (n + 1)))
            (π ^ j)) ∧
        (∀ (σ : Gal(L/K)) (u : Lˣ), u ∈ U j →
          Units.map (σ : L →+* L).toMonoidHom u ∈ U j) ∧
        U (j + 1) ≤ U j) ∧
      ∀ u : Lˣ, (∀ j, u ∈ U j) → u = 1 :=
  localField_exists_separated_normal_unit_filtration K L π hπ

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (G U : Type) [Group G] [Fintype G] [CommGroup U] [MulDistribMulAction G U]

/-- Exact original-object consumer of `finiteActionUnitNorm_continuous`. -/
theorem actual_finite_action_unit_norm_finiteActionUnitNorm_continuous_source [TopologicalSpace U] [IsTopologicalGroup U]
    (hcont : ∀ g : G, Continuous (fun u : U => g • u)) :
    Continuous (finiteActionUnitNorm G U) :=
  finiteActionUnitNorm_continuous G U hcont

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (G U : Type) [Group G] [Fintype G] [CommGroup U] [MulDistribMulAction G U]
  (S : ℕ → Subgroup U) (hmono : ∀ j, S (j + 1) ≤ S j)

include hmono in
/-- Exact original-object consumer of `finiteActionUnitNorm_surjective_on_invariants_of_compact_filtration`. -/
theorem actual_compact_filtered_unit_norm_finiteActionUnitNorm_surjective_on_invariants_of_compact_filtration_source
    [TopologicalSpace U] [IsTopologicalGroup U]
    (hcompact : IsCompact (S 0 : Set U))
    (hclosed : ∀ j, IsClosed (S j : Set U))
    (hsep : ∀ u : U, (∀ j, u ∈ S j) → u = 1)
    (hcont : ∀ g : G, Continuous (fun u : U => g • u))
    (hcorrect : ∀ j (u : U), u ∈ S j → (∀ g : G, g • u = u) →
      ∃ v : U, v ∈ S j ∧ u / finiteActionUnitNorm G U v ∈ S (j + 1))
    (u : U) (hu : u ∈ S 0) (hinv : ∀ g : G, g • u = u) :
    ∃ v : U, v ∈ S 0 ∧ finiteActionUnitNorm G U v = u :=
  finiteActionUnitNorm_surjective_on_invariants_of_compact_filtration G U S hmono hcompact hclosed hsep hcont hcorrect u hu hinv

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L M : Type) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M]
  [ValuativeRel K] [ValuativeRel L] [ValuativeRel M]
  [TopologicalSpace K] [TopologicalSpace L] [TopologicalSpace M]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [IsNonarchimedeanLocalField M]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation M)]

/-- Exact original-object consumer of `localField_algEquiv_units_continuous`. -/
theorem actual_local_field_alg_equiv_continuity_localField_algEquiv_units_continuous_source (e : L ≃ₐ[K] M) :
    Continuous (Units.map (e : L →+* M).toMonoidHom) :=
  localField_algEquiv_units_continuous K L M e

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `localField_normal_unit_level_norm_correction`. -/
theorem actual_local_field_normal_unit_level_norm_localField_normal_unit_level_norm_correction_source
    (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L]
    [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
    (b : Module.Basis Gal(L/K) K L) (hb : ∀ σ, b σ = σ (b 1))
    (π : 𝒪[K]) (hπ : Irreducible π) (n : ℕ)
    (hupper : ∀ x ∈ Submodule.span 𝒪[K] (Set.range b),
      x ∈ (ValuativeRel.valuation L).integer)
    (hlower : ∀ x : 𝒪[L], π ^ n • (x : L) ∈ Submodule.span 𝒪[K] (Set.range b))
    (U : ℕ → Subgroup Lˣ)
    (hU : ∀ j (u : Lˣ), u ∈ U j ↔ (u : L) - 1 ∈
      scalarLatticeImage
        (scalarLatticeImage (Submodule.span 𝒪[K] (Set.range b)) (π ^ (n + 1))) (π ^ j))
    (hstable : ∀ j (σ : Gal(L/K)) (u : Lˣ), u ∈ U j →
      Units.map (σ : L →+* L).toMonoidHom u ∈ U j)
    (j : ℕ) (u : Lˣ) (hu : u ∈ U j) (hinv : ∀ σ : Gal(L/K), σ • u = u) :
    ∃ v : Lˣ, v ∈ U j ∧ u / finiteActionUnitNorm Gal(L/K) Lˣ v ∈ U (j + 1) :=
  localField_normal_unit_level_norm_correction K L b hb π hπ n hupper hlower U hU hstable j u hu hinv

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `localField_exists_small_unit_norm_surjective`. -/
theorem actual_local_field_small_unit_norm_surjectivity_localField_exists_small_unit_norm_surjective_source
    (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
    (π : 𝒪[K]) (hπ : Irreducible π) :
    letI : FiniteDimensional K L := localField_field_module_finite
    ∃ (b : Module.Basis Gal(L/K) K L) (n : ℕ) (U : Subgroup Lˣ),
      (∀ σ, b σ = σ (b 1)) ∧
      (∀ x ∈ Submodule.span 𝒪[K] (Set.range b),
        x ∈ (ValuativeRel.valuation L).integer) ∧
      (∀ x : 𝒪[L], π ^ n • (x : L) ∈ Submodule.span 𝒪[K] (Set.range b)) ∧
      IsCompact (U : Set Lˣ) ∧ IsOpen (U : Set Lˣ) ∧
      Finite (𝒪[L]ˣ ⧸ U.comap (Units.map (algebraMap 𝒪[L] L).toMonoidHom)) ∧
      (∀ u : Lˣ, u ∈ U ↔ (u : L) - 1 ∈
        scalarLatticeImage (Submodule.span 𝒪[K] (Set.range b)) (π ^ (n + 1))) ∧
      (∀ (σ : Gal(L/K)) (u : Lˣ), u ∈ U →
        Units.map (σ : L →+* L).toMonoidHom u ∈ U) ∧
      (∀ u : Lˣ, u ∈ U → (∀ σ : Gal(L/K), σ • u = u) →
        ∃ v : Lˣ, v ∈ U ∧ finiteActionUnitNorm Gal(L/K) Lˣ v = u) ∧
      ∃ F : ℕ → Subgroup Lˣ, F 0 = U ∧
        (∀ j, IsCompact (F j : Set Lˣ) ∧
          (∀ u : Lˣ, u ∈ F j ↔ (u : L) - 1 ∈
            scalarLatticeImage
              (scalarLatticeImage (Submodule.span 𝒪[K] (Set.range b)) (π ^ (n + 1)))
              (π ^ j)) ∧
          (∀ (σ : Gal(L/K)) (u : Lˣ), u ∈ F j →
            Units.map (σ : L →+* L).toMonoidHom u ∈ F j) ∧
          F (j + 1) ≤ F j) ∧
        ∀ u : Lˣ, (∀ j, u ∈ F j) → u = 1 :=
  localField_exists_small_unit_norm_surjective K L π hπ

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {G U : Type} [Group G] [CommGroup U] [MulDistribMulAction G U]

/-- Exact original-object consumer of `unit_cocycle_filtered_approximations`. -/
theorem actual_unit_cocycle_corrections_unit_cocycle_filtered_approximations_source
    (S : ℕ → Subgroup U) (hmono : ∀ j, S (j + 1) ≤ S j)
    (hcorrect : ∀ j (c : G → U),
      (∀ g h, c (g * h) = (g • c h) * c g) → (∀ g, c g ∈ S j) →
        ∃ u : U, u ∈ S j ∧ ∀ g, c g / ((g • u) / u) ∈ S (j + 1))
    (c : G → U) (hc : ∀ g h, c (g * h) = (g • c h) * c g)
    (hc0 : ∀ g, c g ∈ S 0) :
    ∀ j, ∃ u : U, u ∈ S 0 ∧ ∀ g, c g / ((g • u) / u) ∈ S j :=
  unit_cocycle_filtered_approximations S hmono hcorrect c hc hc0

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `unit_cocycle_coboundary_of_compact_filtration`. -/
theorem actual_compact_filtered_unit_cocycles_unit_cocycle_coboundary_of_compact_filtration_source
    {G U : Type} [Group G] [CommGroup U] [MulDistribMulAction G U]
    [TopologicalSpace U] [IsTopologicalGroup U]
    (S : ℕ → Subgroup U) (hmono : ∀ j, S (j + 1) ≤ S j)
    (hcompact : IsCompact (S 0 : Set U))
    (hclosed : ∀ j, IsClosed (S j : Set U))
    (hsep : ∀ u : U, (∀ j, u ∈ S j) → u = 1)
    (hcont : ∀ g : G, Continuous (fun u : U => g • u))
    (hcorrect : ∀ j (c : G → U),
      (∀ g h, c (g * h) = (g • c h) * c g) → (∀ g, c g ∈ S j) →
        ∃ u : U, u ∈ S j ∧ ∀ g, c g / ((g • u) / u) ∈ S (j + 1))
    (c : G → U) (hc : ∀ g h, c (g * h) = (g • c h) * c g)
    (hc0 : ∀ g, c g ∈ S 0) :
    ∃ u : U, u ∈ S 0 ∧ ∀ g, (g • u) / u = c g :=
  unit_cocycle_coboundary_of_compact_filtration S hmono hcompact hclosed hsep hcont hcorrect c hc hc0

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `localField_normal_unit_level_cocycle_correction`. -/
theorem actual_local_field_normal_unit_level_cocycle_localField_normal_unit_level_cocycle_correction_source
    (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L]
    [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
    (b : Module.Basis Gal(L/K) K L) (hb : ∀ σ, b σ = σ (b 1))
    (π : 𝒪[K]) (hπ : Irreducible π) (n : ℕ)
    (hupper : ∀ x ∈ Submodule.span 𝒪[K] (Set.range b),
      x ∈ (ValuativeRel.valuation L).integer)
    (hlower : ∀ x : 𝒪[L], π ^ n • (x : L) ∈ Submodule.span 𝒪[K] (Set.range b))
    (U : ℕ → Subgroup Lˣ)
    (hU : ∀ j (u : Lˣ), u ∈ U j ↔ (u : L) - 1 ∈
      scalarLatticeImage
        (scalarLatticeImage (Submodule.span 𝒪[K] (Set.range b)) (π ^ (n + 1))) (π ^ j))
    (hstable : ∀ j (σ : Gal(L/K)) (u : Lˣ), u ∈ U j →
      Units.map (σ : L →+* L).toMonoidHom u ∈ U j)
    (j : ℕ) (c : Gal(L/K) → Lˣ)
    (hc : ∀ σ τ, c (σ * τ) = (σ • c τ) * c σ) (hcj : ∀ σ, c σ ∈ U j) :
    ∃ v : Lˣ, v ∈ U j ∧ ∀ σ : Gal(L/K),
      c σ / ((σ • v) / v) ∈ U (j + 1) :=
  localField_normal_unit_level_cocycle_correction K L b hb π hπ n hupper hlower U hU hstable j c hc hcj

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `localField_exists_small_unit_norm_and_coboundary`. -/
theorem actual_local_field_small_unit_cohomology_localField_exists_small_unit_norm_and_coboundary_source
    (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
    (π : 𝒪[K]) (hπ : Irreducible π) :
    letI : FiniteDimensional K L := localField_field_module_finite
    ∃ (b : Module.Basis Gal(L/K) K L) (n : ℕ) (U : Subgroup Lˣ),
      (∀ σ, b σ = σ (b 1)) ∧
      (∀ x ∈ Submodule.span 𝒪[K] (Set.range b),
        x ∈ (ValuativeRel.valuation L).integer) ∧
      (∀ x : 𝒪[L], π ^ n • (x : L) ∈ Submodule.span 𝒪[K] (Set.range b)) ∧
      IsCompact (U : Set Lˣ) ∧ IsOpen (U : Set Lˣ) ∧
      Finite (𝒪[L]ˣ ⧸ U.comap (Units.map (algebraMap 𝒪[L] L).toMonoidHom)) ∧
      (∀ u : Lˣ, u ∈ U ↔ (u : L) - 1 ∈
        scalarLatticeImage (Submodule.span 𝒪[K] (Set.range b)) (π ^ (n + 1))) ∧
      (∀ (σ : Gal(L/K)) (u : Lˣ), u ∈ U →
        Units.map (σ : L →+* L).toMonoidHom u ∈ U) ∧
      (∀ u : Lˣ, u ∈ U → (∀ σ : Gal(L/K), σ • u = u) →
        ∃ v : Lˣ, v ∈ U ∧ finiteActionUnitNorm Gal(L/K) Lˣ v = u) ∧
      ∀ c : Gal(L/K) → Lˣ,
        (∀ σ τ, c (σ * τ) = (σ • c τ) * c σ) → (∀ σ, c σ ∈ U) →
          ∃ v : Lˣ, v ∈ U ∧ ∀ σ : Gal(L/K), (σ • v) / v = c σ :=
  localField_exists_small_unit_norm_and_coboundary K L π hπ

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]

/-- Exact original-object consumer of `localFieldIntegerUnit_inclusion_equivariant`. -/
theorem actual_local_field_integer_unit_action_localFieldIntegerUnit_inclusion_equivariant_source (σ : Gal(L/K)) (u : 𝒪[L]ˣ) :
    letI := localFieldIntegerUnitMulDistribMulAction K L
    Units.map (algebraMap 𝒪[L] L).toMonoidHom (σ • u) =
      σ • Units.map (algebraMap 𝒪[L] L).toMonoidHom u :=
  localFieldIntegerUnit_inclusion_equivariant K L σ u

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {G V U : Type} [Group G] [CommGroup V] [CommGroup U]
  [MulDistribMulAction G V] [MulDistribMulAction G U]
  (j : V →* U) (hj : Function.Injective j)
  (heq : ∀ (g : G) (v : V), j (g • v) = g • j v)

include hj heq in
/-- Exact original-object consumer of `injective_unit_cocycle_preimages`. -/
theorem actual_injective_unit_cohomology_transfer_injective_unit_cocycle_preimages_source
    (T : Subgroup V) (S : Subgroup U)
    (hmem : ∀ v : V, v ∈ T ↔ j v ∈ S)
    (honto : ∀ u : U, u ∈ S → ∃ v : V, v ∈ T ∧ j v = u)
    (hcob : ∀ c : G → U,
      (∀ g h, c (g * h) = (g • c h) * c g) → (∀ g, c g ∈ S) →
        ∃ v : U, v ∈ S ∧ ∀ g, (g • v) / v = c g)
    (c : G → V) (hc : ∀ g h, c (g * h) = (g • c h) * c g)
    (hcT : ∀ g, c g ∈ T) :
    ∃ v : V, v ∈ T ∧ ∀ g, (g • v) / v = c g :=
  injective_unit_cocycle_preimages j hj heq T S hmem honto hcob c hc hcT

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `localField_exists_integral_small_unit_norm_and_coboundary`. -/
theorem actual_local_field_integral_small_unit_cohomology_localField_exists_integral_small_unit_norm_and_coboundary_source
    (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
    (π : 𝒪[K]) (hπ : Irreducible π) :
    letI : FiniteDimensional K L := localField_field_module_finite
    letI := localFieldIntegerUnitMulDistribMulAction K L
    ∃ V : Subgroup 𝒪[L]ˣ,
      IsOpen (V : Set 𝒪[L]ˣ) ∧ Finite (𝒪[L]ˣ ⧸ V) ∧
      (∀ (σ : Gal(L/K)) (v : 𝒪[L]ˣ), v ∈ V → σ • v ∈ V) ∧
      (∀ u : 𝒪[L]ˣ, u ∈ V → (∀ σ : Gal(L/K), σ • u = u) →
        ∃ v : 𝒪[L]ˣ, v ∈ V ∧ finiteActionUnitNorm Gal(L/K) 𝒪[L]ˣ v = u) ∧
      ∀ c : Gal(L/K) → 𝒪[L]ˣ,
        (∀ σ τ, c (σ * τ) = (σ • c τ) * c σ) → (∀ σ, c σ ∈ V) →
          ∃ v : 𝒪[L]ˣ, v ∈ V ∧ ∀ σ : Gal(L/K), (σ • v) / v = c σ :=
  localField_exists_integral_small_unit_norm_and_coboundary K L π hπ

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (G U : Type) [Group G] [CommGroup U] [MulDistribMulAction G U]
  (S : Subgroup U) (hS : ∀ (g : G) (u : U), u ∈ S → g • u ∈ S)

/-- Exact original-object consumer of `stableSubgroup_firstCohomology_zero`. -/
theorem actual_stable_subgroup_cohomology_stableSubgroup_firstCohomology_zero_source
    (hcob : ∀ c : G → U,
      (∀ g h, c (g * h) = (g • c h) * c g) → (∀ g, c g ∈ S) →
        ∃ v : U, v ∈ S ∧ ∀ g, (g • v) / v = c g) :
    letI := stableSubgroupMulDistribMulAction G U S hS
    Limits.IsZero (groupCohomology (Rep.ofMulDistribMulAction G S) 1) :=
  stableSubgroup_firstCohomology_zero G U S hS hcob

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {k G : Type} [CommRing k] [CommGroup G] [Fintype G]
  (A : Rep k G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)

include g hg in
/-- Exact original-object consumer of `cyclic_positiveCohomology_zero`. -/
theorem actual_cyclic_positive_cohomology_vanishing_cyclic_positiveCohomology_zero_source
    (hnorm : ∀ x : A, x ∈ A.ρ.invariants → ∃ y : A, A.norm.hom y = x)
    (hfirst : Limits.IsZero (groupCohomology A 1)) (n : ℕ) (hn : 0 < n) :
    Limits.IsZero (groupCohomology A n) :=
  cyclic_positiveCohomology_zero A g hg hnorm hfirst n hn

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `localField_exists_cyclic_small_unit_acyclic`. -/
theorem actual_local_field_cyclic_small_unit_acyclicity_localField_exists_cyclic_small_unit_acyclic_source
    (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [IsCyclic Gal(L/K)]
    [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
    (π : 𝒪[K]) (hπ : Irreducible π) :
    letI := localFieldIntegerUnitMulDistribMulAction K L
    ∃ V : Subgroup 𝒪[L]ˣ,
      IsOpen (V : Set 𝒪[L]ˣ) ∧ Finite (𝒪[L]ˣ ⧸ V) ∧
      ∃ hstable : ∀ (σ : Gal(L/K)) (v : 𝒪[L]ˣ), v ∈ V → σ • v ∈ V,
        letI := stableSubgroupMulDistribMulAction Gal(L/K) 𝒪[L]ˣ V hstable
        ∀ n : ℕ, 0 < n →
          Limits.IsZero (groupCohomology (Rep.ofMulDistribMulAction Gal(L/K) V) n) :=
  localField_exists_cyclic_small_unit_acyclic K L π hπ

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- Exact original-object consumer of `finite_periodic_homology_card_eq`. -/
theorem actual_finite_periodic_homology_cardinality_finite_periodic_homology_card_eq_source [Finite M]
    (f g : M →ₗ[R] M) (hgf : g.comp f = 0) (hfg : f.comp g = 0) :
    Nat.card (linearPeriodicHomology f g hgf) =
      Nat.card (linearPeriodicHomology g f hfg) :=
  finite_periodic_homology_card_eq f g hgf hfg

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `finite_cyclic_first_second_cohomology_card_eq`. -/
theorem actual_finite_cyclic_cohomology_cardinality_finite_cyclic_first_second_cohomology_card_eq_source
    {R G : Type} [CommRing R] [CommGroup G] [Fintype G]
    (A : Rep R G) [Finite A] (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    Nat.card (groupCohomology A 1) = Nat.card (groupCohomology A 2) :=
  finite_cyclic_first_second_cohomology_card_eq A g hg

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (G U : Type) [Group G] [CommGroup U] [MulDistribMulAction G U]
  (S : Subgroup U) (hS : ∀ (g : G) (u : U), u ∈ S → g • u ∈ S)

/-- Exact original-object consumer of `stableSubgroupQuotient_cohomology_isIso`. -/
theorem actual_stable_subgroup_quotient_cohomology_stableSubgroupQuotient_cohomology_isIso_source (n : ℕ)
    (hn : letI := stableSubgroupMulDistribMulAction G U S hS
      Limits.IsZero (groupCohomology (Rep.ofMulDistribMulAction G S) n))
    (hs : letI := stableSubgroupMulDistribMulAction G U S hS
      Limits.IsZero (groupCohomology (Rep.ofMulDistribMulAction G S) (n + 1))) :
    IsIso ((groupCohomology.functor ℤ G n).map
      (stableSubgroupShortComplex G U S hS).g) :=
  stableSubgroupQuotient_cohomology_isIso G U S hS n hn hs

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `localField_integer_unit_first_second_cohomology_orders`. -/
theorem actual_local_field_integer_unit_cohomology_orders_localField_integer_unit_first_second_cohomology_orders_source
    (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [IsCyclic Gal(L/K)]
    [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
    (π : 𝒪[K]) (hπ : Irreducible π) :
    letI := localFieldIntegerUnitMulDistribMulAction K L
    let A := Rep.ofMulDistribMulAction Gal(L/K) 𝒪[L]ˣ
    Finite (groupCohomology A 1) ∧ Finite (groupCohomology A 2) ∧
      Nat.card (groupCohomology A 1) = Nat.card (groupCohomology A 2) :=
  localField_integer_unit_first_second_cohomology_orders K L π hπ

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `localFieldUnitOrder_galois_invariant`. -/
theorem actual_local_field_galois_unit_order_localFieldUnitOrder_galois_invariant_source
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
    (σ : Gal(L/K)) (x : Lˣ) :
    localFieldUnitOrder L (Additive.ofMul (σ • x)) = localFieldUnitOrder L (Additive.ofMul x) :=
  localFieldUnitOrder_galois_invariant K L σ x

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]

/-- Exact original-object consumer of `localFieldUnitValuationShortComplex_shortExact`. -/
theorem actual_local_field_unit_valuation_sequence_localFieldUnitValuationShortComplex_shortExact_source :
    (localFieldUnitValuationShortComplex K L).ShortExact :=
  localFieldUnitValuationShortComplex_shortExact K L

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `cyclic_trivial_integer_odd_cohomology_zero`. -/
theorem actual_cyclic_trivial_integer_cohomology_cyclic_trivial_integer_odd_cohomology_zero_source
    (G : Type) [CommGroup G] [Fintype G] (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) (n : ℕ) (hn : Odd n) :
    Limits.IsZero (groupCohomology (Rep.trivial ℤ G ℤ) n) :=
  cyclic_trivial_integer_odd_cohomology_zero G g hg n hn

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {R A B C D : Type} [CommRing R]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C] [AddCommGroup D] [Module R D]

/-- Exact original-object consumer of `exact_four_module_cardinality`. -/
theorem actual_finite_exact_module_cardinality_exact_four_module_cardinality_source
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (h : C →ₗ[R] D)
    (hf : Function.Injective f) (hh : Function.Surjective h)
    (hfg : f.range = g.ker) (hgh : g.range = h.ker) :
    Nat.card B * Nat.card D = Nat.card A * Nat.card C :=
  exact_four_module_cardinality f g h hf hh hfg hgh

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `cyclic_trivial_integer_even_cohomology_order`. -/
theorem actual_cyclic_integer_even_cohomology_cyclic_trivial_integer_even_cohomology_order_source
    (G : Type) [CommGroup G] [Fintype G] (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) (n : ℕ) [NeZero n] (hn : Even n) :
    Finite (groupCohomology (Rep.trivial ℤ G ℤ) n) ∧
      Nat.card (groupCohomology (Rep.trivial ℤ G ℤ) n) = Fintype.card G :=
  cyclic_trivial_integer_even_cohomology_order G g hg n hn

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `exact_cohomology_four_term_cardinality`. -/
theorem actual_exact_cohomology_cardinality_exact_cohomology_four_term_cardinality_source
    {k G : Type} [CommRing k] [Group G]
    (X : ShortComplex (Rep k G)) (hX : X.ShortExact) (n : ℕ)
    (hprev : Limits.IsZero (groupCohomology X.X₃ n))
    (hnext : Limits.IsZero (groupCohomology X.X₂ (n + 1 + 1)))
    [Finite (groupCohomology X.X₁ (n + 1))]
    [Finite (groupCohomology X.X₃ (n + 1))] :
    Finite (groupCohomology X.X₂ (n + 1)) ∧
      Nat.card (groupCohomology X.X₂ (n + 1)) *
          Nat.card (groupCohomology X.X₁ (n + 1 + 1)) =
        Nat.card (groupCohomology X.X₁ (n + 1)) *
          Nat.card (groupCohomology X.X₃ (n + 1)) :=
  exact_cohomology_four_term_cardinality X hX n hprev hnext

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `localField_cyclic_second_cohomology_order`. -/
theorem actual_local_field_cyclic_second_cohomology_order_localField_cyclic_second_cohomology_order_source
    (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [IsCyclic Gal(L/K)]
    [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)] :
    Finite (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) ∧
      Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) = Nat.card Gal(L/K) :=
  localField_cyclic_second_cohomology_order K L

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `localField_cyclic_norm_index`. -/
theorem actual_local_field_cyclic_norm_index_localField_cyclic_norm_index_source
    (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [IsCyclic Gal(L/K)]
    [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)] :
    Nat.card (Additive Kˣ ⧸ (galoisUnitFieldNormLinear (K := K) (L := L)).range) =
      Module.finrank K L :=
  localField_cyclic_norm_index K L

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {k G : Type} [CommRing k] [Group G] (A : Rep k G) (S : Subgroup G)

/-- Exact original-object consumer of `coinducedCosetValues_action`. -/
theorem actual_coinduced_coset_values_coinducedCosetValues_action_source
    (f : Rep.coind S.subtype (Rep.res S.subtype A)) (h : G) (q : G ⧸ S) :
    coinducedCosetValues A S ((Rep.coind S.subtype (Rep.res S.subtype A)).ρ h f) q =
      A.ρ h (coinducedCosetValues A S f (h⁻¹ • q)) :=
  coinducedCosetValues_action A S f h q

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {k G : Type} [CommRing k] [Group G] (A : Rep k G) (S : Subgroup G)
  [Fintype (G ⧸ S)]

/-- Exact original-object consumer of `coinducedCosetTrace_comp_unit`. -/
theorem actual_coinduced_coset_trace_coinducedCosetTrace_comp_unit_source :
    Rep.resCoindToHom S.subtype A (Rep.res S.subtype A) (𝟙 _) ≫
      coinducedCosetTrace A S = Fintype.card (G ⧸ S) • 𝟙 A :=
  coinducedCosetTrace_comp_unit A S

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {k G : Type} [CommRing k] [Group G] (A : Rep k G) (S : Subgroup G)

variable [Fintype (G ⧸ S)]

/-- Exact original-object consumer of `subgroupCohomologyComparison_trace`. -/
theorem actual_coinduced_cohomology_trace_subgroupCohomologyComparison_trace_source (n : ℕ) :
    subgroupCohomologyComparison A S n ≫ subgroupCohomologyTrace A S n =
      Fintype.card (G ⧸ S) • 𝟙 (groupCohomology A n) :=
  subgroupCohomologyComparison_trace A S n

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {k G : Type} [CommRing k] [Group G] (A : Rep k G) (S : Subgroup G)

/-- Exact original-object consumer of `sylowCohomologyComparison_primary_injective`. -/
theorem actual_subgroup_cohomology_coprime_detection_sylowCohomologyComparison_primary_injective_source [Finite G]
    (n p : ℕ) [Fact p.Prime] (P : Sylow p G) :
    Function.Injective (fun x : AddCommGroup.primaryComponent (groupCohomology A n) p =>
      subgroupCohomologyComparison A (P : Subgroup G) n x.val) :=
  sylowCohomologyComparison_primary_injective A n p P

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {k G : Type} [CommRing k] [Group G] [Fintype G] (A : Rep k G)

/-- Exact original-object consumer of `finiteSecondCohomology_sylow_zero`. -/
theorem actual_finite_second_cohomology_sylow_detection_finiteSecondCohomology_sylow_zero_source
    (x : groupCohomology A 2)
    (hx : ∀ p : ℕ, p.Prime → p ∣ Fintype.card G → ∃ P : Sylow p G,
      subgroupCohomologyComparison A (P : Subgroup G) 2 x = 0) : x = 0 :=
  finiteSecondCohomology_sylow_zero A x hx

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `finite_second_cohomology_of_sylows`. -/
theorem actual_finite_second_cohomology_from_sylows_finite_second_cohomology_of_sylows_source
    {k G : Type} [CommRing k] [Group G] [Fintype G] (A : Rep k G)
    (hfinite : ∀ p : ℕ, p.Prime → p ∣ Fintype.card G → ∀ P : Sylow p G,
      Finite (groupCohomology (Rep.res (P : Subgroup G).subtype A) 2)) :
    Finite (groupCohomology A 2) :=
  finite_second_cohomology_of_sylows A hfinite

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {G : Type} [Group G] (S : Subgroup G)

/-- Exact original-object consumer of `subgroupCosetRemainder_mul`. -/
theorem actual_original_subgroup_coset_coordinates_subgroupCosetRemainder_mul_source (g : G) (h : S) :
    subgroupCosetRemainder S (g * h) = subgroupCosetRemainder S g * h :=
  subgroupCosetRemainder_mul S g h

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {k G : Type} [CommRing k] [Group G] (A : Rep k G)

/-- Exact original-object consumer of `originalCoinducedFunctionRep_action`. -/
theorem actual_original_coinduced_function_coefficients_originalCoinducedFunctionRep_action_source
    (f : originalCoinducedFunctionRep A) (h g : G) :
    ((originalCoinducedFunctionRep A).ρ h f).val g = f.val (g * h) :=
  originalCoinducedFunctionRep_action A f h g

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {k G : Type} [CommRing k] [Group G] (A : Rep k G) (S : Subgroup G)

/-- Exact original-object consumer of `originalCoinducedSubgroup_second_zero`. -/
theorem actual_original_coinduced_subgroup_acyclicity_originalCoinducedSubgroup_second_zero_source :
    Limits.IsZero (groupCohomology (Rep.res S.subtype (originalCoinducedFunctionRep A)) 2) :=
  originalCoinducedSubgroup_second_zero A S

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {k G : Type} [CommRing k] [Group G] (A : Rep k G)

/-- Exact original-object consumer of `originalCoinducedDimensionShift_isIso`. -/
theorem actual_original_coinduced_dimension_shift_originalCoinducedDimensionShift_isIso_source (S : Subgroup G) :
    IsIso (groupCohomology.δ (originalCoinducedShortComplex_restrict_shortExact A S) 1 2 rfl) :=
  originalCoinducedDimensionShift_isIso A S

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {k G : Type} [CommRing k] [Group G] (A : Rep.{0} k G)
  (S : Subgroup G) [S.Normal]

/-- Exact original-object consumer of `originalCoinducedInvariantQuotient_isomorphic`. -/
theorem actual_original_coinduced_invariant_quotient_originalCoinducedInvariantQuotient_isomorphic_source :
    Nonempty ((originalCoinducedFunctionRep A).quotientToInvariants S ≅
      originalCoinducedFunctionRep (Rep.trivial k (G ⧸ S) A)) :=
  originalCoinducedInvariantQuotient_isomorphic A S

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `originalCoinducedInvariant_positive_zero`. -/
theorem actual_original_coinduced_invariant_acyclicity_originalCoinducedInvariant_positive_zero_source
    {k G : Type} [CommRing k] [Group G] (A : Rep.{0} k G)
    (S : Subgroup G) [S.Normal] (n : ℕ) :
    Limits.IsZero (groupCohomology
      ((originalCoinducedFunctionRep A).quotientToInvariants S) (n + 1)) :=
  originalCoinducedInvariant_positive_zero A S n

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `invariantCoefficientSequence_shortExact_of_first_zero`. -/
theorem actual_invariant_coefficient_exactness_invariantCoefficientSequence_shortExact_of_first_zero_source
    {k G : Type} [CommRing k] [Group G]
    (X : ShortComplex (Rep.{0} k G)) (hX : X.ShortExact)
    (hzero : Limits.IsZero (groupCohomology X.X₁ 1)) :
    (X.map (Rep.invariantsFunctor k G)).ShortExact :=
  invariantCoefficientSequence_shortExact_of_first_zero X hX hzero

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {k G : Type} [CommRing k] [Group G]
  (X : ShortComplex (Rep.{0} k G)) (S : Subgroup G) [S.Normal]

/-- Exact original-object consumer of `normalInvariantCoefficientSequence_shortExact`. -/
theorem actual_normal_invariant_coefficient_sequence_normalInvariantCoefficientSequence_shortExact_source
    (hX : (X.map (Rep.resFunctor S.subtype)).ShortExact)
    (hzero : Limits.IsZero (groupCohomology (Rep.res S.subtype X.X₁) 1)) :
    (normalInvariantCoefficientSequence X S).ShortExact :=
  normalInvariantCoefficientSequence_shortExact X S hX hzero

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {k G : Type} [CommRing k] [Group G] (A : Rep.{0} k G)

/-- Exact original-object consumer of `originalCoinducedInvariantDimensionShift_isIso`. -/
theorem actual_original_coinduced_global_dimension_shift_originalCoinducedInvariantDimensionShift_isIso_source (S : Subgroup G) [S.Normal]
    (hfirst : Limits.IsZero (groupCohomology (Rep.res S.subtype A) 1)) :
    IsIso (groupCohomology.δ (originalCoinducedInvariantSequence_shortExact A S hfirst) 1 2 rfl) :=
  originalCoinducedInvariantDimensionShift_isIso A S hfirst

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `finite_exact_three_module_card_dvd`. -/
theorem actual_finite_exact_module_divisibility_finite_exact_three_module_card_dvd_source
    {R A B C : Type} [CommRing R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] [Finite A] [Finite C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (hf : Function.Injective f)
    (hfg : f.range = g.ker) :
    Finite B ∧ Nat.card B ∣ Nat.card A * Nat.card C :=
  finite_exact_three_module_card_dvd f g hf hfg

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `secondCohomology_normal_subgroup_card_dvd`. -/
theorem actual_second_cohomology_normal_subgroup_cardinality_secondCohomology_normal_subgroup_card_dvd_source
    {k G : Type} [CommRing k] [Group G] (A : Rep.{0} k G)
    (S : Subgroup G) [S.Normal]
    (hfirst : Limits.IsZero (groupCohomology (Rep.res S.subtype A) 1))
    [Finite (groupCohomology (A.quotientToInvariants S) 2)]
    [Finite (groupCohomology (Rep.res S.subtype A) 2)] :
    Finite (groupCohomology A 2) ∧
      Nat.card (groupCohomology A 2) ∣
        Nat.card (groupCohomology (A.quotientToInvariants S) 2) *
          Nat.card (groupCohomology (Rep.res S.subtype A) 2) :=
  secondCohomology_normal_subgroup_card_dvd A S hfirst

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `originalCohomologyReindex_isIso`. -/
theorem actual_original_group_cohomology_reindex_originalCohomologyReindex_isIso_source
    {k G H : Type} [CommRing k] [Group G] [Group H]
    (A : Rep.{0} k H) (e : G ≃* H) (n : ℕ) :
    IsIso (groupCohomology.map e.toMonoidHom (𝟙 (Rep.res e.toMonoidHom A)) n) :=
  originalCohomologyReindex_isIso A e n

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] (S : Subgroup Gal(L/K))

/-- Exact original-object consumer of `galoisSubgroupUnit_first_cohomology_zero`. -/
theorem actual_galois_subgroup_unit_cohomology_galoisSubgroupUnit_first_cohomology_zero_source :
    Limits.IsZero (groupCohomology (Rep.res S.subtype (Rep.ofAlgebraAutOnUnits K L)) 1) :=
  galoisSubgroupUnit_first_cohomology_zero S

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  (S : Subgroup Gal(L/K)) [S.Normal]

/-- Exact original-object consumer of `galoisNormalInvariantUnitInclusion_bijective`. -/
theorem actual_galois_normal_invariant_unit_coefficients_galoisNormalInvariantUnitInclusion_bijective_source :
    Function.Bijective (galoisNormalInvariantUnitInclusion S).hom :=
  galoisNormalInvariantUnitInclusion_bijective S

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  (S : Subgroup Gal(L/K)) [S.Normal]

/-- Exact original-object consumer of `galoisUnit_second_cohomology_fixedField_card_dvd`. -/
theorem actual_galois_fixed_field_second_cohomology_galoisUnit_second_cohomology_fixedField_card_dvd_source
    [Finite (groupCohomology (Rep.ofAlgebraAutOnUnits K (IntermediateField.fixedField S)) 2)]
    [Finite (groupCohomology (Rep.ofAlgebraAutOnUnits (IntermediateField.fixedField S) L) 2)] :
    Finite (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) ∧
      Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) ∣
        Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits K (IntermediateField.fixedField S)) 2) *
          Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits (IntermediateField.fixedField S) L) 2) :=
  galoisUnit_second_cohomology_fixedField_card_dvd S

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `pGroup_exists_central_cyclic_reduction`. -/
theorem actual_p_group_central_cyclic_reduction_pGroup_exists_central_cyclic_reduction_source
    {G : Type} [Group G] [Finite G] [Nontrivial G]
    {p : ℕ} [Fact p.Prime] (hG : IsPGroup p G) :
    ∃ S : Subgroup G, S.Normal ∧ IsCyclic S ∧
      1 < Nat.card S ∧ S.index < Nat.card G :=
  pGroup_exists_central_cyclic_reduction hG

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `normedLocalField_cyclic_second_cohomology_order`. -/
theorem actual_normed_local_field_cyclic_cohomology_normedLocalField_cyclic_second_cohomology_order_source
    (K L : Type) [NontriviallyNormedField K] [NontriviallyNormedField L]
    [IsUltrametricDist K] [IsUltrametricDist L] [NormedAlgebra K L]
    [LocallyCompactSpace K] [LocallyCompactSpace L]
    [IsGalois K L] [IsCyclic Gal(L/K)] :
    Finite (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) ∧
      Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) = Nat.card Gal(L/K) :=
  normedLocalField_cyclic_second_cohomology_order K L

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `normedLocalField_pGroup_second_cohomology_card_dvd`. -/
theorem actual_normed_local_field_p_group_second_cohomology_normedLocalField_pGroup_second_cohomology_card_dvd_source
    (p : ℕ) [Fact p.Prime]
    (K L : Type) [NontriviallyNormedField K] [NontriviallyNormedField L]
    [IsUltrametricDist K] [IsUltrametricDist L] [NormedAlgebra K L]
    [LocallyCompactSpace K] [LocallyCompactSpace L]
    [FiniteDimensional K L] [IsGalois K L] (hG : IsPGroup p Gal(L/K)) :
    Finite (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) ∧
      Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) ∣ Nat.card Gal(L/K) :=
  normedLocalField_pGroup_second_cohomology_card_dvd p K L hG

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `secondCohomology_card_dvd_of_sylows`. -/
theorem actual_second_cohomology_sylow_cardinality_secondCohomology_card_dvd_of_sylows_source
    {k G : Type} [CommRing k] [Group G] [Fintype G] (A : Rep.{0} k G)
    (hSylow : ∀ p : ℕ, p.Prime → ∀ P : Sylow p G,
      Finite (groupCohomology (Rep.res (P : Subgroup G).subtype A) 2) ∧
        Nat.card (groupCohomology (Rep.res (P : Subgroup G).subtype A) 2) ∣ Nat.card P) :
    Finite (groupCohomology A 2) ∧ Nat.card (groupCohomology A 2) ∣ Nat.card G :=
  secondCohomology_card_dvd_of_sylows A hSylow

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `normedLocalField_second_cohomology_card_dvd`. -/
theorem actual_normed_local_field_second_cohomology_bound_normedLocalField_second_cohomology_card_dvd_source
    (K L : Type) [NontriviallyNormedField K] [NontriviallyNormedField L]
    [IsUltrametricDist K] [IsUltrametricDist L] [NormedAlgebra K L]
    [LocallyCompactSpace K] [LocallyCompactSpace L]
    [FiniteDimensional K L] [IsGalois K L] :
    Finite (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) ∧
      Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) ∣ Nat.card Gal(L/K) :=
  normedLocalField_second_cohomology_card_dvd K L

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `localField_finite_galois_second_cohomology_card_dvd`. -/
theorem actual_local_field_finite_galois_second_cohomology_bound_localField_finite_galois_second_cohomology_card_dvd_source
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [FiniteDimensional K L] [IsGalois K L] :
    Finite (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) ∧
      Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) ∣ Nat.card Gal(L/K) :=
  localField_finite_galois_second_cohomology_card_dvd K L

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `localField_finite_continuous_h2_card_dvd`. -/
theorem actual_local_field_finite_continuous_h2_bound_localField_finite_continuous_h2_card_dvd_source
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [FiniteDimensional K L] [IsGalois K L]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)] :
    Finite (GaloisUnitContinuousH2 (K := K) (Ω := L)) ∧
      Nat.card (GaloisUnitContinuousH2 (K := K) (Ω := L)) ∣ Module.finrank K L :=
  localField_finite_continuous_h2_card_dvd K L

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {k G H : Type} [CommRing k] [Group G] [Group H]
  {X : ShortComplex (Rep.{0} k H)} {Y : ShortComplex (Rep.{0} k G)}
  (f : G →* H) (φ : X.map (Rep.resFunctor f) ⟶ Y)

/-- Exact original-object consumer of `originalCohomologyGroupChange_delta_naturality`. -/
theorem actual_original_cohomology_group_change_naturality_originalCohomologyGroupChange_delta_naturality_source
    (hX : X.ShortExact) (hY : Y.ShortExact) (i j : ℕ) (hij : i + 1 = j) :
    groupCohomology.δ hX i j hij ≫ groupCohomology.map f φ.τ₁ j =
      groupCohomology.map f φ.τ₃ i ≫ groupCohomology.δ hY i j hij :=
  originalCohomologyGroupChange_delta_naturality f φ hX hY i j hij

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {k G : Type} [CommRing k] [Group G]

/-- Exact original-object consumer of `originalCoinduced_delta_inflation`. -/
theorem actual_original_normal_sequence_cohomology_maps_originalCoinduced_delta_inflation_source
    (A : Rep.{0} k G) (S : Subgroup G) [S.Normal]
    (hfirst : Limits.IsZero (groupCohomology (Rep.res S.subtype A) 1)) :
    groupCohomology.δ (originalCoinducedInvariantSequence_shortExact A S hfirst) 1 2 rfl ≫
        groupCohomology.map (QuotientGroup.mk' S) (Rep.ofHom (A.ρ.quotientToInvariants_lift S)) 2 =
      (groupCohomology.H1InfRes (originalCoinducedQuotient A) S).f ≫
        groupCohomology.δ (originalCoinducedShortComplex_shortExact A) 1 2 rfl :=
  originalCoinduced_delta_inflation A S hfirst

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {k G : Type} [CommRing k] [Group G]
  (A : Rep.{0} k G) (S : Subgroup G) [S.Normal]
  (hfirst : Limits.IsZero (groupCohomology (Rep.res S.subtype A) 1))

/-- Exact original-object consumer of `originalSecondCohomology_inflation_restriction_exact`. -/
theorem actual_original_second_cohomology_inflation_restriction_originalSecondCohomology_inflation_restriction_exact_source :
    (originalSecondCohomologyInfRes A S hfirst).Exact :=
  originalSecondCohomology_inflation_restriction_exact A S hfirst

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `originalGroupChangeCohomology_isIso`. -/
theorem actual_original_group_change_cohomology_isomorphism_originalGroupChangeCohomology_isIso_source
    {k G H : Type} [CommRing k] [Group G] [Group H]
    (A : Rep.{0} k H) (B : Rep.{0} k G) (e : G ≃* H)
    (φ : Rep.res e.toMonoidHom A ⟶ B) [IsIso φ] (n : ℕ) :
    IsIso (groupCohomology.map e.toMonoidHom φ n) :=
  originalGroupChangeCohomology_isIso A B e φ n

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  (S : Subgroup Gal(L/K)) [S.Normal]

/-- Exact original-object consumer of `galoisFixedFieldH2Inflation_mono`. -/
theorem actual_galois_fixed_field_h2_inflation_injection_galoisFixedFieldH2Inflation_mono_source :
    Mono (groupCohomology.map (AlgEquiv.restrictNormalHom (IntermediateField.fixedField S))
      (finiteGaloisUnitTowerInclusion K (IntermediateField.fixedField S) L) 2) :=
  galoisFixedFieldH2Inflation_mono S

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise




/-- Exact original-object consumer of `galoisIntermediateFieldH2Inflation_mono`. -/
theorem actual_galois_intermediate_field_h2_inflation_injection_galoisIntermediateFieldH2Inflation_mono_source
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (F : IntermediateField K L) [IsGalois K F] :
    Mono (groupCohomology.map (AlgEquiv.restrictNormalHom F)
      (finiteGaloisUnitTowerInclusion K F L) 2) :=
  galoisIntermediateFieldH2Inflation_mono F

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L M : Type) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M] [Normal K L]



/-- Exact original-object consumer of `galoisTowerKernelUnit_first_zero`. -/
theorem actual_full_local_invariant_2229_galoisTowerKernelUnit_first_zero_source [FiniteDimensional L M] :
    Limits.IsZero (groupCohomology
      (Rep.res (AlgEquiv.restrictNormalHom L : Gal(M/K) →* Gal(L/K)).ker.subtype
        (Rep.ofAlgebraAutOnUnits K M)) 1) :=
  galoisTowerKernelUnit_first_zero K L M

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L M : Type) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [FiniteDimensional K M] [IsGalois K L] [IsGalois K M]



/-- Exact original-object consumer of `galoisTowerQuotientUnitInclusion_bijective`. -/
theorem actual_full_local_invariant_2230_galoisTowerQuotientUnitInclusion_bijective_source :
    Function.Bijective (galoisTowerQuotientUnitInclusion K L M).hom :=
  galoisTowerQuotientUnitInclusion_bijective K L M

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L M : Type) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [FiniteDimensional K M] [FiniteDimensional L M] [IsGalois K L] [IsGalois K M]



/-- Exact original-object consumer of `finiteGaloisUnitH2Inflation_mono`. -/
theorem actual_full_local_invariant_2231_finiteGaloisUnitH2Inflation_mono_source :
    Mono (groupCohomology.map (AlgEquiv.restrictNormalHom L)
      (finiteGaloisUnitTowerInclusion K L M) 2) :=
  finiteGaloisUnitH2Inflation_mono K L M

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L M : Type) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [FiniteDimensional K L] [FiniteDimensional K M] [IsGalois K L] [IsGalois K M]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K M)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K M)]



/-- Exact original-object consumer of `finiteGaloisUnitTowerH2Inflation_injective`. -/
theorem actual_full_local_invariant_2232_finiteGaloisUnitTowerH2Inflation_injective_source :
    Function.Injective (finiteGaloisUnitTowerH2Inflation K L M) :=
  finiteGaloisUnitTowerH2Inflation_injective K L M

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (E : FiniteGaloisIntermediateField K Ω)
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K E)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K E)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]



/-- Exact original-object consumer of `galoisUnitFiniteStageH2Inflation_injective`. -/
theorem actual_full_local_invariant_2233_galoisUnitFiniteStageH2Inflation_injective_source :
    Function.Injective (galoisUnitFiniteStageH2Inflation E) :=
  galoisUnitFiniteStageH2Inflation_injective E

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise






/-- Exact original-object consumer of `zmodAdditionCarry_sum_period`. -/
theorem actual_full_local_invariant_2234_zmodAdditionCarry_sum_period_source {n : ℕ} [NeZero n] (a : ZMod n)
    (N : ℕ) (hN : N • a = 0) :
    n * (∑ i ∈ Finset.range N, zmodAdditionCarry (i • a) a) = N * a.val :=
  zmodAdditionCarry_sum_period a N hN

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {R G : Type} [CommRing R] [Group G] (A : Rep R G)
  {n : ℕ} [NeZero n] (χ : G →* Multiplicative (ZMod n))
  (a : A) (ha : ∀ x, A.ρ x a = a)



/-- Exact original-object consumer of `representationCarryCocycle_period_mul`. -/
theorem actual_full_local_invariant_2235_representationCarryCocycle_period_mul_source (g : G) (N : ℕ) (hN : g ^ N = 1) :
    n • representationCyclicTwoCochainPeriodSum A g N
        (representationCarryCocycle A χ a ha) =
      (N * (χ g).toAdd.val) • a :=
  representationCarryCocycle_period_mul A χ a ha g N hN

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]



/-- Exact original-object consumer of `localField_ramification_mul_residue_degree`. -/
theorem actual_full_local_invariant_2236_localField_ramification_mul_residue_degree_source :
    (IsLocalRing.maximalIdeal 𝒪[K]).ramificationIdx (IsLocalRing.maximalIdeal 𝒪[L]) *
      Module.finrank 𝓀[K] 𝓀[L] = Module.finrank K L :=
  localField_ramification_mul_residue_degree K L

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]



/-- Exact original-object consumer of `localFieldUnitOrder_algebraMap`. -/
theorem actual_full_local_invariant_2237_localFieldUnitOrder_algebraMap_source (u : Kˣ) :
    localFieldUnitOrder L (Additive.ofMul (Units.map (algebraMap K L).toMonoidHom u)) =
      ((IsLocalRing.maximalIdeal 𝒪[K]).ramificationIdx
        (IsLocalRing.maximalIdeal 𝒪[L]) : ℤ) * localFieldUnitOrder K (Additive.ofMul u) :=
  localFieldUnitOrder_algebraMap K L u

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K E L M : Type) [Field K] [Field E] [Field L] [Field M]
  [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
  [IsScalarTower K E M] [IsScalarTower K L M] [Normal K L]

variable [FiniteDimensional E M] [IsGalois K L] [IsGalois E M]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits E M)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits E M)]



/-- Exact original-object consumer of `finiteGaloisUnitBaseChangeH2_mk`. -/
theorem actual_full_local_invariant_2238_finiteGaloisUnitBaseChangeH2_mk_source
    (c : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits K L)) :
    finiteGaloisUnitBaseChangeH2 K E L M (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (finiteGaloisUnitBaseChangeCocycle K E L M c) :=
  finiteGaloisUnitBaseChangeH2_mk K E L M c

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]



/-- Exact original-object consumer of `localFieldArithmeticFrobenius_eq_pow_of_residue`. -/
theorem actual_full_local_invariant_2239_localFieldArithmeticFrobenius_eq_pow_of_residue_source (g : Gal(L/K)) (n : ℕ)
    (hg : ∀ x : 𝒪[L], IsLocalRing.residue 𝒪[L] (localFieldIntegerGaloisEquiv K L g x) =
      IsLocalRing.residue 𝒪[L] x ^ (Nat.card 𝓀[K] ^ n)) :
    g = localFieldArithmeticFrobenius K L ^ n :=
  localFieldArithmeticFrobenius_eq_pow_of_residue K L g n hg

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K E L M : Type) [Field K] [Field E] [Field L] [Field M]
  [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
  [IsScalarTower K E M] [IsScalarTower K L M] [Normal K L]
  [ValuativeRel K] [ValuativeRel E] [ValuativeRel L] [ValuativeRel M]
  [TopologicalSpace K] [TopologicalSpace E] [TopologicalSpace L] [TopologicalSpace M]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField E]
  [IsNonarchimedeanLocalField L] [IsNonarchimedeanLocalField M]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [(ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation M)]
  [(ValuativeRel.valuation L).HasExtension (ValuativeRel.valuation M)]

variable [IsGalois K L] [IsGalois E M]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]
  [Algebra.FormallyUnramified 𝒪[E] 𝒪[M]]



/-- Exact original-object consumer of `localFieldArithmeticFrobenius_baseChange`. -/
theorem actual_full_local_invariant_2240_localFieldArithmeticFrobenius_baseChange_source :
    galoisBaseChangeRestriction K E L M (localFieldArithmeticFrobenius E M) =
      localFieldArithmeticFrobenius K L ^ Module.finrank 𝓀[K] 𝓀[E] :=
  localFieldArithmeticFrobenius_baseChange K E L M

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
  {n : ℕ} [NeZero n] (χ : Gal(L/K) →* Multiplicative (ZMod n)) (u : Kˣ)

variable [IsCyclic Gal(L/K)] (g : Gal(L/K)) (hg : ∀ x, x ∈ Subgroup.zpowers g)
attribute [local instance] IsCyclic.commGroup

attribute [local instance] IsCyclic.commGroup


/-- Exact original-object consumer of `galoisUnitCharacterCarryCocycle_period_mul`. -/
theorem actual_full_local_invariant_2241_galoisUnitCharacterCarryCocycle_period_mul_source :
    n • galoisUnitCyclicPeriodBase g hg (galoisUnitCharacterCarryCocycle χ u) =
      (orderOf g * (χ g).toAdd.val) • Additive.ofMul u :=
  galoisUnitCharacterCarryCocycle_period_mul χ u g hg

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]

attribute [local instance] IsCyclic.commGroup


/-- Exact original-object consumer of `localFieldPeriodRationalInvariant_characterCarry_smul`. -/
theorem actual_full_local_invariant_2242_localFieldPeriodRationalInvariant_characterCarry_smul_source
    {n : ℕ} [NeZero n] (χ : Gal(L/K) →* Multiplicative (ZMod n)) (u : Kˣ) :
    letI : FiniteDimensional K L := localField_field_module_finite
    localFieldPeriodRationalInvariant K L
      (Submodule.Quotient.mk (galoisUnitCharacterCarryCocycle χ u)) =
        localFieldUnitOrder K (Additive.ofMul u) •
          rationalCyclicInvariant n (χ (localFieldArithmeticFrobenius K L)).toAdd :=
  localFieldPeriodRationalInvariant_characterCarry_smul K L χ u

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K E L M : Type) [Field K] [Field E] [Field L] [Field M]
  [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
  [IsScalarTower K E M] [IsScalarTower K L M]
  [FiniteDimensional K L] [FiniteDimensional E M] [IsGalois K L] [IsGalois E M]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits E M)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits E M)]



/-- Exact original-object consumer of `finiteGaloisUnitBaseChangeH2_characterCarry`. -/
theorem actual_full_local_invariant_2243_finiteGaloisUnitBaseChangeH2_characterCarry_source
    {n : ℕ} [NeZero n] (χ : Gal(L/K) →* Multiplicative (ZMod n)) (u : Kˣ) :
    finiteGaloisUnitBaseChangeH2 K E L M
      (Submodule.Quotient.mk (galoisUnitCharacterCarryCocycle χ u)) =
        Submodule.Quotient.mk (galoisUnitCharacterCarryCocycle
          (χ.comp (galoisBaseChangeRestriction K E L M))
          (Units.map (algebraMap K E).toMonoidHom u)) :=
  finiteGaloisUnitBaseChangeH2_characterCarry K E L M χ u

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K E L M : Type) [Field K] [Field E] [Field L] [Field M]
  [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
  [IsScalarTower K E M] [IsScalarTower K L M] [IsGalois K L] [IsGalois E M]
  [ValuativeRel K] [ValuativeRel E] [ValuativeRel L] [ValuativeRel M]
  [TopologicalSpace K] [TopologicalSpace E] [TopologicalSpace L] [TopologicalSpace M]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField E]
  [IsNonarchimedeanLocalField L] [IsNonarchimedeanLocalField M]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [(ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation M)]
  [(ValuativeRel.valuation L).HasExtension (ValuativeRel.valuation M)]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]
  [Algebra.FormallyUnramified 𝒪[E] 𝒪[M]]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits E M)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits E M)]



/-- Exact original-object consumer of `localFieldPeriodRationalInvariant_baseChange_characterCarry`. -/
theorem actual_full_local_invariant_2244_localFieldPeriodRationalInvariant_baseChange_characterCarry_source
    {n : ℕ} [NeZero n] (χ : Gal(L/K) →* Multiplicative (ZMod n)) (u : Kˣ) :
    letI : FiniteDimensional K L := localField_field_module_finite
    letI : FiniteDimensional E M := localField_field_module_finite
    localFieldPeriodRationalInvariant E M
      (finiteGaloisUnitBaseChangeH2 K E L M
        (Submodule.Quotient.mk (galoisUnitCharacterCarryCocycle χ u))) =
          Module.finrank K E • localFieldPeriodRationalInvariant K L
            (Submodule.Quotient.mk (galoisUnitCharacterCarryCocycle χ u)) :=
  localFieldPeriodRationalInvariant_baseChange_characterCarry K E L M χ u

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]

attribute [local instance] IsCyclic.commGroup


/-- Exact original-object consumer of `localFieldH2_exists_carry_representative`. -/
theorem actual_full_local_invariant_2245_localFieldH2_exists_carry_representative_source
    (x : GaloisUnitContinuousH2 (K := K) (Ω := L)) :
    letI : FiniteDimensional K L := localField_field_module_finite
    letI : IsCyclic Gal(L/K) :=
      (unramifiedLocalFieldResidueGaloisEquiv K L).isCyclic.mpr inferInstance
    ∃ u : Kˣ, Submodule.Quotient.mk (galoisUnitCarryCocycle
      (localFieldArithmeticFrobenius K L) (localFieldArithmeticFrobenius_generates K L) u) = x :=
  localFieldH2_exists_carry_representative K L x

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K E L M : Type) [Field K] [Field E] [Field L] [Field M]
  [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
  [IsScalarTower K E M] [IsScalarTower K L M] [IsGalois K L] [IsGalois E M]
  [ValuativeRel K] [ValuativeRel E] [ValuativeRel L] [ValuativeRel M]
  [TopologicalSpace K] [TopologicalSpace E] [TopologicalSpace L] [TopologicalSpace M]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField E]
  [IsNonarchimedeanLocalField L] [IsNonarchimedeanLocalField M]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [(ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation M)]
  [(ValuativeRel.valuation L).HasExtension (ValuativeRel.valuation M)]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]
  [Algebra.FormallyUnramified 𝒪[E] 𝒪[M]]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits E M)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits E M)]

attribute [local instance] IsCyclic.commGroup


/-- Exact original-object consumer of `localFieldPeriodRationalInvariant_baseChange`. -/
theorem actual_full_local_invariant_2246_localFieldPeriodRationalInvariant_baseChange_source
    (x : GaloisUnitContinuousH2 (K := K) (Ω := L)) :
    letI : FiniteDimensional E M := localField_field_module_finite
    localFieldPeriodRationalInvariant E M (finiteGaloisUnitBaseChangeH2 K E L M x) =
      Module.finrank K E • localFieldPeriodRationalInvariant K L x :=
  localFieldPeriodRationalInvariant_baseChange K E L M x

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {R A B Ω : Type*} [CommRing R] [CommRing A] [CommRing B] [Field Ω]
  [Algebra R A] [Algebra R B] [Algebra R Ω] [Algebra B Ω] [IsScalarTower R B Ω]



/-- Exact original-object consumer of `baseChangedTensorFractionEmbedding_compositum`. -/
theorem actual_full_local_invariant_2247_baseChangedTensorFractionEmbedding_compositum_source
    {E L : Type*} [Field E] [Field L]
    [Algebra B E] [IsFractionRing B E] [Algebra A L] [IsFractionRing A L]
    (f : A →ₐ[R] Ω) (i : E →+* Ω) (j : L →+* Ω)
    (hi : i.comp (algebraMap B E) = algebraMap B Ω)
    (hj : j.comp (algebraMap A L) = f.toRingHom) :
    (baseChangedTensorFractionEmbedding (B := B) f).toRingHom.fieldRange =
      i.fieldRange ⊔ j.fieldRange :=
  baseChangedTensorFractionEmbedding_compositum f i j hi hj

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {R A B Ω : Type*} [CommRing R] [CommRing A] [CommRing B] [Field Ω]
  [Algebra R A] [Algebra R B] [Algebra R Ω] [Algebra B Ω] [IsScalarTower R B Ω]
  {E L : Type*} [Field E] [Field L]
  [Algebra B E] [IsFractionRing B E] [Algebra A L] [IsFractionRing A L]
  (f : A →ₐ[R] Ω) (i : E →+* Ω) (j : L →+* Ω)
  (hi : i.comp (algebraMap B E) = algebraMap B Ω)
  (hj : j.comp (algebraMap A L) = f.toRingHom)
  (htop : i.fieldRange ⊔ j.fieldRange = ⊤)

variable [IsDedekindDomain B] [Module.Finite R A] [Algebra.FormallyUnramified R A]


include hi hj htop

/-- Exact original-object consumer of `integralClosure_formallyUnramified_of_baseChange_compositum_top`. -/
theorem actual_full_local_invariant_2248_integralClosure_formallyUnramified_of_baseChange_compositum_top_source
    (C : Type*) [CommRing C] [Algebra B C] [Algebra C Ω]
    [IsScalarTower B C Ω] [IsIntegralClosure C B Ω] :
    Algebra.FormallyUnramified B C :=
  integralClosure_formallyUnramified_of_baseChange_compositum_top f i j hi hj htop C

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K E L M : Type) [Field K] [Field E] [Field L] [Field M]
  [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
  [IsScalarTower K E M] [IsScalarTower K L M]
  [ValuativeRel K] [ValuativeRel E] [ValuativeRel L] [ValuativeRel M]
  [TopologicalSpace K] [TopologicalSpace E] [TopologicalSpace L] [TopologicalSpace M]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField E]
  [IsNonarchimedeanLocalField L] [IsNonarchimedeanLocalField M]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [(ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation M)]
  [(ValuativeRel.valuation L).HasExtension (ValuativeRel.valuation M)]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]



include K in
omit [(ValuativeRel.valuation L).HasExtension (ValuativeRel.valuation M)] in
/-- Exact original-object consumer of `localField_integer_unramified_of_compositum`. -/
theorem actual_full_local_invariant_2249_localField_integer_unramified_of_compositum_source
    (htop : (algebraMap E M).fieldRange ⊔ (algebraMap L M).fieldRange = ⊤) :
    Algebra.FormallyUnramified 𝒪[E] 𝒪[M] :=
  localField_integer_unramified_of_compositum K E L M htop

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise






/-- Exact original-object consumer of `spectralIntegerExtension_formallyUnramified`. -/
theorem actual_full_local_invariant_2250_spectralIntegerExtension_formallyUnramified_source
    (K L : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [ValuativeRel K] [(NormedField.valuation (K := K)).Compatible]
    [IsNonarchimedeanLocalField K]
    [Field L] [Algebra K L] [FiniteDimensional K L]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
    [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]] :
    letI : NontriviallyNormedField L := spectralNorm.nontriviallyNormedField K L
    letI : TopologicalSpace L := (spectralNorm.uniformSpace K L).toTopologicalSpace
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel L := ValuativeRel.ofValuation (NormedField.valuation (K := L))
    letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L) :=
      spectralValuation_hasExtension K L
    Algebra.FormallyUnramified 𝒪[K] 𝒪[L] :=
  spectralIntegerExtension_formallyUnramified K L

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise






/-- Exact original-object consumer of `localField_exists_spectral_original_unramified_stage`. -/
theorem actual_full_local_invariant_2251_localField_exists_spectral_original_unramified_stage_source
    (K Ω : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [ValuativeRel K] [(NormedField.valuation (K := K)).Compatible]
    [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [IsSepClosed Ω]
    (n : ℕ) [NeZero n] :
    ∃ F : FiniteGaloisIntermediateField K Ω, Module.finrank K F = n ∧
      letI : NontriviallyNormedField F := spectralNorm.nontriviallyNormedField K F
      letI : NormedAlgebra K F := spectralNorm.normedAlgebra K F
      letI : IsUltrametricDist F := IsUltrametricDist.of_normedAlgebra K
      letI : ValuativeRel F := ValuativeRel.ofValuation (NormedField.valuation (K := F))
      letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation F) :=
        spectralValuation_hasExtension K F
      Algebra.FormallyUnramified 𝒪[K] 𝒪[F] :=
  localField_exists_spectral_original_unramified_stage K Ω n

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {K Ω : Type} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [ValuativeRel K] [(NormedField.valuation (K := K)).Compatible]
  [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω]



/-- Exact original-object consumer of `spectralFiniteGalois_sup_unramified`. -/
theorem actual_full_local_invariant_2252_spectralFiniteGalois_sup_unramified_source (E F : FiniteGaloisIntermediateField K Ω)
    (hF :
      letI : NontriviallyNormedField F := spectralNorm.nontriviallyNormedField K F
      letI : NormedAlgebra K F := spectralNorm.normedAlgebra K F
      letI : IsUltrametricDist F := IsUltrametricDist.of_normedAlgebra K
      letI : ValuativeRel F := ValuativeRel.ofValuation (NormedField.valuation (K := F))
      letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation F) :=
        spectralValuation_hasExtension K F
      Algebra.FormallyUnramified 𝒪[K] 𝒪[F]) :
    let H := E ⊔ F
    letI : Algebra E H :=
      (IntermediateField.inclusion (show E.toIntermediateField ≤ H.toIntermediateField
        from le_sup_left)).toAlgebra
    letI : IsScalarTower K E H := IsScalarTower.of_algHom
      (IntermediateField.inclusion (show E.toIntermediateField ≤ H.toIntermediateField
        from le_sup_left))
    letI : NontriviallyNormedField E := spectralNorm.nontriviallyNormedField K E
    letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
    letI : NontriviallyNormedField H := spectralNorm.nontriviallyNormedField K H
    letI : NormedAlgebra E H := spectralNorm.normedAlgebra' K E H
    letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
    letI : NormedAlgebra K H := spectralNorm.normedAlgebra K H
    letI : IsUltrametricDist H := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel E := ValuativeRel.ofValuation (NormedField.valuation (K := E))
    letI : ValuativeRel H := ValuativeRel.ofValuation (NormedField.valuation (K := H))
    letI : (ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation H) :=
      normedFieldValuation_hasExtension E H
    Algebra.FormallyUnramified 𝒪[E] 𝒪[H] :=
  spectralFiniteGalois_sup_unramified E F hF

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L M : Type) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]



/-- Exact original-object consumer of `galoisUnitTowerH2Restriction_kernel_composition`. -/
theorem actual_full_local_invariant_2253_galoisUnitTowerH2Restriction_kernel_composition_source [Normal K L] :
    galoisUnitTowerH2Restriction K L M ≫
      groupCohomology.map (galoisTowerKernelEquiv K L M).toMonoidHom
        (galoisTowerKernelUnitCoefficientIso K L M).hom 2 =
      groupCohomology.map (A := Rep.ofAlgebraAutOnUnits K M)
        (B := Rep.res (AlgEquiv.restrictNormalHom L : Gal(M/K) →* Gal(L/K)).ker.subtype
          (Rep.ofAlgebraAutOnUnits K M))
        (AlgEquiv.restrictNormalHom L : Gal(M/K) →* Gal(L/K)).ker.subtype
        (𝟙 _) 2 :=
  galoisUnitTowerH2Restriction_kernel_composition K L M

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K L M : Type) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [FiniteDimensional K M] [FiniteDimensional L M] [IsGalois K L] [IsGalois K M]



/-- Exact original-object consumer of `finiteGaloisUnitH2_inflation_exists_iff_restriction_zero`. -/
theorem actual_full_local_invariant_2254_finiteGaloisUnitH2_inflation_exists_iff_restriction_zero_source
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K M) 2) :
    (∃ y : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2,
      groupCohomology.map (AlgEquiv.restrictNormalHom L)
        (finiteGaloisUnitTowerInclusion K L M) 2 y = x) ↔
      galoisUnitTowerH2Restriction K L M x = 0 :=
  finiteGaloisUnitH2_inflation_exists_iff_restriction_zero K L M x

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K E L M : Type) [Field K] [Field E] [Field L] [Field M]
  [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
  [IsScalarTower K E M] [IsScalarTower K L M] [IsGalois K L]

variable [FiniteDimensional K L] [FiniteDimensional E M] [IsGalois E M]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits E M)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits E M)]



/-- Exact original-object consumer of `continuousDiscreteH2Equiv_finiteGaloisBaseChange`. -/
theorem actual_full_local_invariant_2255_continuousDiscreteH2Equiv_finiteGaloisBaseChange_source
    (x : GaloisUnitContinuousH2 (K := K) (Ω := L)) :
    continuousDiscreteH2Equiv (Rep.ofAlgebraAutOnUnits E M)
      (discreteGaloisUnitAction_continuous (K := E) (Ω := M))
      (finiteGaloisUnitBaseChangeH2 K E L M x) =
        groupCohomology.map (galoisBaseChangeRestriction K E L M)
          (galoisUnitBaseChangeInclusion K E L M) 2
          (continuousDiscreteH2Equiv (Rep.ofAlgebraAutOnUnits K L)
            (discreteGaloisUnitAction_continuous (K := K) (Ω := L)) x) :=
  continuousDiscreteH2Equiv_finiteGaloisBaseChange K E L M x

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K E L M : Type) [Field K] [Field E] [Field L] [Field M]
  [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
  [IsScalarTower K E M] [IsScalarTower K L M]
  [FiniteDimensional K E] [FiniteDimensional K L] [FiniteDimensional K M]
  [FiniteDimensional E M] [IsGalois K E] [IsGalois K L] [IsGalois K M] [IsGalois E M]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K E)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K E)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K M)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K M)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits E M)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits E M)]



/-- Exact original-object consumer of `finiteGaloisH2_exists_inflation_eq_iff_baseChange_zero`. -/
theorem actual_full_local_invariant_2256_finiteGaloisH2_exists_inflation_eq_iff_baseChange_zero_source
    (x : GaloisUnitContinuousH2 (K := K) (Ω := L)) :
    (∃ y : GaloisUnitContinuousH2 (K := K) (Ω := E),
      finiteGaloisUnitTowerH2Inflation K E M y = finiteGaloisUnitTowerH2Inflation K L M x) ↔
        finiteGaloisUnitBaseChangeH2 K E L M x = 0 :=
  finiteGaloisH2_exists_inflation_eq_iff_baseChange_zero K E L M x

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K E L M : Type) [Field K] [Field E] [Field L] [Field M]
  [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
  [IsScalarTower K E M] [IsScalarTower K L M]
  [IsGalois K E] [IsGalois K L] [IsGalois K M]
  [ValuativeRel K] [ValuativeRel E] [ValuativeRel L] [ValuativeRel M]
  [TopologicalSpace K] [TopologicalSpace E] [TopologicalSpace L] [TopologicalSpace M]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField E]
  [IsNonarchimedeanLocalField L] [IsNonarchimedeanLocalField M]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation M)]
  [(ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation M)]
  [(ValuativeRel.valuation L).HasExtension (ValuativeRel.valuation M)]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K E)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K E)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K M)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K M)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits E M)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits E M)]



/-- Exact original-object consumer of `localFieldH2_exists_unramified_compositum_representative`. -/
theorem actual_full_local_invariant_2257_localFieldH2_exists_unramified_compositum_representative_source
    (htop : (algebraMap E M).fieldRange ⊔ (algebraMap L M).fieldRange = ⊤)
    (hdegree : Module.finrank K L = Module.finrank K E)
    (x : GaloisUnitContinuousH2 (K := K) (Ω := E)) :
    letI : FiniteDimensional K M := localField_field_module_finite
    ∃ y : GaloisUnitContinuousH2 (K := K) (Ω := L),
      finiteGaloisUnitTowerH2Inflation K E M x = finiteGaloisUnitTowerH2Inflation K L M y :=
  localFieldH2_exists_unramified_compositum_representative K E L M htop hdegree x

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {K Ω : Type} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [ValuativeRel K] [(NormedField.valuation (K := K)).Compatible]
  [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]



/-- Exact original-object consumer of `spectralFiniteStageH2_exists_unramified_representative`. -/
theorem actual_full_local_invariant_2258_spectralFiniteStageH2_exists_unramified_representative_source
    (E : FiniteGaloisIntermediateField K Ω)
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits K E)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits K E)]
    (x : GaloisUnitContinuousH2 (K := K) (Ω := E)) :
    ∃ F : FiniteGaloisIntermediateField K Ω, Module.finrank K F = Module.finrank K E ∧
      letI : NontriviallyNormedField F := spectralNorm.nontriviallyNormedField K F
      letI : NormedAlgebra K F := spectralNorm.normedAlgebra K F
      letI : IsUltrametricDist F := IsUltrametricDist.of_normedAlgebra K
      letI : ValuativeRel F := ValuativeRel.ofValuation (NormedField.valuation (K := F))
      letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation F) :=
        spectralValuation_hasExtension K F
      Algebra.FormallyUnramified 𝒪[K] 𝒪[F] ∧
        letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K F) := ⊥
        letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K F) := ⟨rfl⟩
        ∃ y : GaloisUnitContinuousH2 (K := K) (Ω := F),
          galoisUnitFiniteStageH2Inflation E x = galoisUnitFiniteStageH2Inflation F y :=
  spectralFiniteStageH2_exists_unramified_representative E x

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise






/-- Exact original-object consumer of `localField_continuousH2_exists_unramified_stage`. -/
theorem actual_full_local_invariant_2259_localField_continuousH2_exists_unramified_stage_source
    (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
    (x : GaloisUnitContinuousH2 (K := K) (Ω := Ω)) :
    ∃ F : FiniteGaloisIntermediateField K Ω,
      ∃ (_ : ValuativeRel F) (_ : TopologicalSpace F)
        (_ : IsNonarchimedeanLocalField F)
        (_ : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation F)),
        Algebra.FormallyUnramified 𝒪[K] 𝒪[F] ∧
          letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K F) := ⊥
          letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K F) := ⟨rfl⟩
          ∃ y : GaloisUnitContinuousH2 (K := K) (Ω := F),
            galoisUnitFiniteStageH2Inflation F y = x :=
  localField_continuousH2_exists_unramified_stage K Ω x

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K Ω : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [ValuativeRel K] [(NormedField.valuation (K := K)).Compatible]
  [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω]



/-- Exact original-object consumer of `spectralUnramifiedStageInvariant_mem_range_iff`. -/
theorem actual_full_local_invariant_2260_spectralUnramifiedStageInvariant_mem_range_iff_source (F : FiniteGaloisIntermediateField K Ω)
    (hF : SpectralStageUnramified K Ω F) (q : AddCircle (1 : ℚ)) :
    q ∈ (spectralUnramifiedStageInvariant K Ω F hF).range ↔ Module.finrank K F • q = 0 :=
  spectralUnramifiedStageInvariant_mem_range_iff K Ω F hF q

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K Ω : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [ValuativeRel K] [(NormedField.valuation (K := K)).Compatible]
  [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω]

variable [IsGalois K Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]



/-- Exact original-object consumer of `spectralUnramifiedStageInvariant_eq_of_inflation_eq`. -/
theorem actual_full_local_invariant_2261_spectralUnramifiedStageInvariant_eq_of_inflation_eq_source
    (E F : FiniteGaloisIntermediateField K Ω)
    (hE : SpectralStageUnramified K Ω E) (hF : SpectralStageUnramified K Ω F)
    (x : GaloisUnitH2FiniteStage K Ω E) (y : GaloisUnitH2FiniteStage K Ω F)
    (hxy : galoisUnitH2FiniteStageMap K Ω E x = galoisUnitH2FiniteStageMap K Ω F y) :
    spectralUnramifiedStageInvariant K Ω E hE x =
      spectralUnramifiedStageInvariant K Ω F hF y :=
  spectralUnramifiedStageInvariant_eq_of_inflation_eq K Ω E F hE hF x y hxy

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K Ω : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [ValuativeRel K] [(NormedField.valuation (K := K)).Compatible]
  [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]



/-- Exact original-object consumer of `spectralContinuousH2Invariant_existsUnique`. -/
theorem actual_full_local_invariant_2262_spectralContinuousH2Invariant_existsUnique_source
    (x : GaloisUnitContinuousH2 (K := K) (Ω := Ω)) :
    ∃! q : AddCircle (1 : ℚ),
      ∃ F : FiniteGaloisIntermediateField K Ω, ∃ hF : SpectralStageUnramified K Ω F,
        ∃ y : GaloisUnitH2FiniteStage K Ω F,
          galoisUnitH2FiniteStageMap K Ω F y = x ∧ spectralUnramifiedStageInvariant K Ω F hF y = q :=
  spectralContinuousH2Invariant_existsUnique K Ω x

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K Ω : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [ValuativeRel K] [(NormedField.valuation (K := K)).Compatible]
  [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]



/-- Exact original-object consumer of `spectralContinuousH2InvariantEquiv_stage`. -/
theorem actual_full_local_invariant_2263_spectralContinuousH2InvariantEquiv_stage_source
    (F : FiniteGaloisIntermediateField K Ω) (hF : SpectralStageUnramified K Ω F)
    (y : GaloisUnitH2FiniteStage K Ω F) :
    spectralContinuousH2InvariantEquiv K Ω (galoisUnitH2FiniteStageMap K Ω F y) =
      spectralUnramifiedStageInvariant K Ω F hF y :=
  spectralContinuousH2InvariantEquiv_stage K Ω F hF y

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]



/-- Exact original-object consumer of `localField_continuousH2_equivalent_rationalCircle`. -/
theorem actual_full_local_invariant_2264_localField_continuousH2_equivalent_rationalCircle_source :
    Nonempty (GaloisUnitContinuousH2 (K := K) (Ω := Ω) ≃ₗ[ℤ] AddCircle (1 : ℚ)) :=
  localField_continuousH2_equivalent_rationalCircle K Ω

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise






/-- Exact original-object consumer of `localField_valuative_extension_unique`. -/
theorem actual_local_invariant_functoriality_2265_localField_valuative_extension_unique_source
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (v w : ValuativeRel L) (t u : TopologicalSpace L)
    (hv : letI := v; letI := t; IsNonarchimedeanLocalField L)
    (hw : letI := w; letI := u; IsNonarchimedeanLocalField L)
    (hvext : letI := v;
      (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L))
    (hwext : letI := w;
      (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)) : v = w :=
  localField_valuative_extension_unique K L v w t u hv hw hvext hwext

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise






/-- Exact original-object consumer of `localField_local_structures_eq_spectral`. -/
theorem actual_local_invariant_functoriality_2266_localField_local_structures_eq_spectral_source
    (K L : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [ValuativeRel K] [(NormedField.valuation (K := K)).Compatible]
    [IsNonarchimedeanLocalField K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [v : ValuativeRel L] [t : TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)] :
    letI : NontriviallyNormedField L := spectralNorm.nontriviallyNormedField K L
    letI : TopologicalSpace L := (spectralNorm.uniformSpace K L).toTopologicalSpace
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
    v = ValuativeRel.ofValuation (NormedField.valuation (K := L)) ∧
      t = (spectralNorm.uniformSpace K L).toTopologicalSpace :=
  localField_local_structures_eq_spectral K L

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K Ω : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [ValuativeRel K] [(NormedField.valuation (K := K)).Compatible]
  [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω]



/-- Exact original-object consumer of `spectralUnramifiedStageInvariant_eq_original_period`. -/
theorem actual_local_invariant_functoriality_2267_spectralUnramifiedStageInvariant_eq_original_period_source
    (F : FiniteGaloisIntermediateField K Ω) (hF : SpectralStageUnramified K Ω F)
    [v : ValuativeRel F] [t : TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation F)]
    [Algebra.FormallyUnramified 𝒪[K] 𝒪[F]] (x : GaloisUnitH2FiniteStage K Ω F) :
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K F) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K F) := ⟨rfl⟩
    spectralUnramifiedStageInvariant K Ω F hF x = localFieldPeriodRationalInvariant K F x :=
  spectralUnramifiedStageInvariant_eq_original_period K Ω F hF x

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]



/-- Exact original-object consumer of `localFieldContinuousH2InvariantEquiv_stage`. -/
theorem actual_local_invariant_functoriality_2268_localFieldContinuousH2InvariantEquiv_stage_source
    (F : FiniteGaloisIntermediateField K Ω)
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation F)]
    [Algebra.FormallyUnramified 𝒪[K] 𝒪[F]] (x : GaloisUnitH2FiniteStage K Ω F) :
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K F) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K F) := ⟨rfl⟩
    localFieldContinuousH2InvariantEquiv K Ω (galoisUnitH2FiniteStageMap K Ω F x) =
      localFieldPeriodRationalInvariant K F x :=
  localFieldContinuousH2InvariantEquiv_stage K Ω F x

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K E L M : Type) [Field K] [Field E] [Field L] [Field M]
  [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
  [IsScalarTower K E M] [IsScalarTower K L M] [Normal K L]



/-- Exact original-object consumer of `galoisBaseChangeRestriction_continuous`. -/
theorem actual_local_invariant_functoriality_2269_galoisBaseChangeRestriction_continuous_source [Algebra.IsAlgebraic E M] :
    Continuous (galoisBaseChangeRestriction K E L M) :=
  galoisBaseChangeRestriction_continuous K E L M

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K E L M : Type) [Field K] [Field E] [Field L] [Field M]
  [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
  [IsScalarTower K E M] [IsScalarTower K L M]

variable [IsGalois K L] [IsGalois E M]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits E M)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits E M)]



/-- Exact original-object consumer of `continuousGaloisUnitBaseChangeH2_mk`. -/
theorem actual_local_invariant_functoriality_2270_continuousGaloisUnitBaseChangeH2_mk_source
    (c : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits K L)) :
    continuousGaloisUnitBaseChangeH2 K E L M (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (continuousGaloisUnitBaseChangeCocycle K E L M c) :=
  continuousGaloisUnitBaseChangeH2_mk K E L M c

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K E F L M N : Type) [Field K] [Field E] [Field F] [Field L] [Field M] [Field N]
  [Algebra K E] [Algebra E F] [Algebra K F]
  [Algebra K L] [Algebra K M] [Algebra K N]
  [Algebra E M] [Algebra E N] [Algebra F N]
  [Algebra L M] [Algebra M N] [Algebra L N]
  [IsScalarTower K E M] [IsScalarTower K L M]
  [IsScalarTower E F N] [IsScalarTower E M N]
  [IsScalarTower K F N] [IsScalarTower K L N] [IsScalarTower L M N]
  [Normal K L] [Normal E M]

variable [IsGalois K L] [IsGalois E M] [IsGalois F N]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits E M)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits E M)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits F N)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits F N)]



/-- Exact original-object consumer of `continuousGaloisUnitBaseChangeH2_comp`. -/
theorem actual_local_invariant_functoriality_2271_continuousGaloisUnitBaseChangeH2_comp_source
    (x : GaloisUnitContinuousH2 (K := K) (Ω := L)) :
    continuousGaloisUnitBaseChangeH2 E F M N (continuousGaloisUnitBaseChangeH2 K E L M x) =
      continuousGaloisUnitBaseChangeH2 K F L N x :=
  continuousGaloisUnitBaseChangeH2_comp K E F L M N x

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]



/-- Exact original-object consumer of `continuousGaloisUnitBaseChangeH2_eq_finiteStage`. -/
theorem actual_local_invariant_functoriality_2272_continuousGaloisUnitBaseChangeH2_eq_finiteStage_source
    (F : FiniteGaloisIntermediateField K Ω) (x : GaloisUnitH2FiniteStage K Ω F) :
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K F) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K F) := ⟨rfl⟩
    continuousGaloisUnitBaseChangeH2 K K F Ω x = galoisUnitH2FiniteStageMap K Ω F x :=
  continuousGaloisUnitBaseChangeH2_eq_finiteStage K Ω F x

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]



/-- Exact original-object consumer of `finiteGaloisStageExtendScalars_coe`. -/
theorem actual_local_invariant_functoriality_2273_finiteGaloisStageExtendScalars_coe_source
    (E H : FiniteGaloisIntermediateField K Ω) (hEH : E ≤ H) :
    ((finiteGaloisStageExtendScalars E H hEH).toIntermediateField : Set Ω) =
      (H.toIntermediateField : Set Ω) :=
  finiteGaloisStageExtendScalars_coe E H hEH

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]



/-- Exact original-object consumer of `continuousGaloisUnitRestriction_finite_compositum`. -/
theorem actual_local_invariant_functoriality_2274_continuousGaloisUnitRestriction_finite_compositum_source
    (E F H : FiniteGaloisIntermediateField K Ω) (hEH : E ≤ H) (hFH : F ≤ H)
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω)]
    (x : GaloisUnitH2FiniteStage K Ω F) :
    letI : Algebra E H := (IntermediateField.inclusion hEH).toAlgebra
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    letI : IsScalarTower K E H := IsScalarTower.of_algHom (IntermediateField.inclusion hEH)
    letI : IsScalarTower K F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
    letI : IsScalarTower E H Ω := .of_algebraMap_eq' rfl
    letI : FiniteDimensional E H := FiniteDimensional.right K E H
    letI : IsGalois E H := IsGalois.tower_top_of_isGalois K E H
    letI : IsGalois E Ω := IsGalois.tower_top_of_isGalois K E Ω
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K F) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K F) := ⟨rfl⟩
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits E H) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits E H) := ⟨rfl⟩
    continuousGaloisUnitBaseChangeH2 K E Ω Ω (galoisUnitH2FiniteStageMap K Ω F x) =
      continuousGaloisUnitBaseChangeH2 E E H Ω
        (finiteGaloisUnitBaseChangeH2 K E F H x) :=
  continuousGaloisUnitRestriction_finite_compositum E F H hEH hFH x

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
  (E H : FiniteGaloisIntermediateField K Ω) (hEH : E ≤ H)



/-- Exact original-object consumer of `finiteGaloisStageExtendScalars_algebra_eq`. -/
theorem actual_local_invariant_functoriality_2275_finiteGaloisStageExtendScalars_algebra_eq_source :
    letI : Algebra E H := (IntermediateField.inclusion hEH).toAlgebra
    (inferInstance : Algebra E H) =
      (inferInstance : Algebra E (finiteGaloisStageExtendScalars E H hEH)) :=
  finiteGaloisStageExtendScalars_algebra_eq E H hEH

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise






/-- Exact original-object consumer of `galoisUnitH2AlgebraCongruence_bijective`. -/
theorem actual_local_invariant_functoriality_2276_galoisUnitH2AlgebraCongruence_bijective_source
    {K L : Type} [Field K] [Field L] (a b : Algebra K L) (hab : a = b)
    (ha : letI := a; IsGalois K L) (hb : letI := b; IsGalois K L) :
    Function.Bijective (galoisUnitH2AlgebraCongruence a b hab ha hb) :=
  galoisUnitH2AlgebraCongruence_bijective a b hab ha hb

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
  (E H : FiniteGaloisIntermediateField K Ω) (hEH : E ≤ H)



/-- Exact original-object consumer of `finiteGaloisStageRebasedH2Equiv_bijective`. -/
theorem actual_local_invariant_functoriality_2277_finiteGaloisStageRebasedH2Equiv_bijective_source :
    letI : Algebra E H := (IntermediateField.inclusion hEH).toAlgebra
    letI : IsScalarTower K E H := IsScalarTower.of_algHom (IntermediateField.inclusion hEH)
    letI : IsGalois E H := IsGalois.tower_top_of_isGalois K E H
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits E H) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits E H) := ⟨rfl⟩
    Function.Bijective (finiteGaloisStageRebasedH2Equiv E H hEH) :=
  finiteGaloisStageRebasedH2Equiv_bijective E H hEH

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]



/-- Exact original-object consumer of `continuousGaloisUnitRestriction_rebased_stage`. -/
theorem actual_local_invariant_functoriality_2278_continuousGaloisUnitRestriction_rebased_stage_source
    (E F H : FiniteGaloisIntermediateField K Ω) (hEH : E ≤ H) (hFH : F ≤ H)
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω)]
    (x : GaloisUnitH2FiniteStage K Ω F) :
    letI : Algebra E H := inferInstanceAs (Algebra E (finiteGaloisStageExtendScalars E H hEH))
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    letI : IsScalarTower K E H := .of_algebraMap_eq' rfl
    letI : IsScalarTower K F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
    letI : IsScalarTower E H Ω := .of_algebraMap_eq' rfl
    letI : FiniteDimensional E H := FiniteDimensional.right K E H
    letI : IsGalois E H := IsGalois.tower_top_of_isGalois K E H
    letI : IsGalois E Ω := IsGalois.tower_top_of_isGalois K E Ω
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K F) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K F) := ⟨rfl⟩
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits E H) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits E H) := ⟨rfl⟩
    continuousGaloisUnitBaseChangeH2 K E Ω Ω (galoisUnitH2FiniteStageMap K Ω F x) =
      galoisUnitH2FiniteStageMap E Ω (finiteGaloisStageExtendScalars E H hEH)
        (finiteGaloisUnitBaseChangeH2 K E F H x) :=
  continuousGaloisUnitRestriction_rebased_stage E F H hEH hFH x

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {K Ω : Type} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [ValuativeRel K] [(NormedField.valuation (K := K)).Compatible]
  [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω]



/-- Exact original-object consumer of `spectralFiniteGalois_sup_rebased_unramified`. -/
theorem actual_local_invariant_functoriality_2279_spectralFiniteGalois_sup_rebased_unramified_source (E F : FiniteGaloisIntermediateField K Ω)
    (hF :
      letI : NontriviallyNormedField F := spectralNorm.nontriviallyNormedField K F
      letI : NormedAlgebra K F := spectralNorm.normedAlgebra K F
      letI : IsUltrametricDist F := IsUltrametricDist.of_normedAlgebra K
      letI : ValuativeRel F := ValuativeRel.ofValuation (NormedField.valuation (K := F))
      letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation F) :=
        spectralValuation_hasExtension K F
      Algebra.FormallyUnramified 𝒪[K] 𝒪[F]) :
    let H := E ⊔ F
    letI : Algebra E H := inferInstanceAs
      (Algebra E (finiteGaloisStageExtendScalars E H le_sup_left))
    letI : IsScalarTower K E H := .of_algebraMap_eq' rfl
    letI : NontriviallyNormedField E := spectralNorm.nontriviallyNormedField K E
    letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
    letI : NontriviallyNormedField H := spectralNorm.nontriviallyNormedField K H
    letI : NormedAlgebra E H := spectralNorm.normedAlgebra' K E H
    letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
    letI : NormedAlgebra K H := spectralNorm.normedAlgebra K H
    letI : IsUltrametricDist H := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel E := ValuativeRel.ofValuation (NormedField.valuation (K := E))
    letI : ValuativeRel H := ValuativeRel.ofValuation (NormedField.valuation (K := H))
    letI : (ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation H) :=
      normedFieldValuation_hasExtension E H
    Algebra.FormallyUnramified 𝒪[E] 𝒪[H] :=
  spectralFiniteGalois_sup_rebased_unramified E F hF

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]



/-- Exact original-object consumer of `localFieldContinuousInvariant_restriction_on_stage`. -/
theorem actual_local_invariant_functoriality_2280_localFieldContinuousInvariant_restriction_on_stage_source
    (E F H : FiniteGaloisIntermediateField K Ω) (hEH : E ≤ H) (hFH : F ≤ H)
    [ValuativeRel E] [ValuativeRel F] [ValuativeRel H]
    [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace H]
    [IsNonarchimedeanLocalField E] [IsNonarchimedeanLocalField F]
    [IsNonarchimedeanLocalField H]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation F)]
    [Algebra.FormallyUnramified 𝒪[K] 𝒪[F]]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω)] :
    letI : Algebra E H := inferInstanceAs (Algebra E (finiteGaloisStageExtendScalars E H hEH))
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    letI : IsScalarTower K E H := .of_algebraMap_eq' rfl
    letI : IsScalarTower K F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
    letI : IsScalarTower E H Ω := .of_algebraMap_eq' rfl
    letI : FiniteDimensional E H := FiniteDimensional.right K E H
    letI : IsGalois E H := IsGalois.tower_top_of_isGalois K E H
    letI : IsGalois E Ω := IsGalois.tower_top_of_isGalois K E Ω
    ∀ [_hextEH : (ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation H)]
      [_hextFH : (ValuativeRel.valuation F).HasExtension (ValuativeRel.valuation H)]
      [_hunram : Algebra.FormallyUnramified 𝒪[E] 𝒪[H]] (y : GaloisUnitH2FiniteStage K Ω F),
      localFieldContinuousH2InvariantEquiv E Ω
        (continuousGaloisUnitBaseChangeH2 K E Ω Ω (galoisUnitH2FiniteStageMap K Ω F y)) =
      Module.finrank K E • localFieldContinuousH2InvariantEquiv K Ω
        (galoisUnitH2FiniteStageMap K Ω F y) := by
  letI : Algebra E H := inferInstanceAs (Algebra E (finiteGaloisStageExtendScalars E H hEH))
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  haveI : IsScalarTower K E H := .of_algebraMap_eq' rfl
  haveI : IsScalarTower K F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  haveI : IsScalarTower E H Ω := .of_algebraMap_eq' rfl
  haveI : FiniteDimensional E H := FiniteDimensional.right K E H
  haveI : IsGalois E H := IsGalois.tower_top_of_isGalois K E H
  haveI : IsGalois E Ω := IsGalois.tower_top_of_isGalois K E Ω
  intro hextEH hextFH hunram y
  exact localFieldContinuousInvariant_restriction_on_stage K Ω E F H hEH hFH
    (_hextEH := hextEH) (_hextFH := hextFH) (_hunram := hunram) y

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise






/-- Exact original-object consumer of `localFieldContinuousH2InvariantEquiv_restriction`. -/
theorem actual_local_invariant_functoriality_2281_localFieldContinuousH2InvariantEquiv_restriction_source
    (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
    (E : FiniteGaloisIntermediateField K Ω)
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω)]
    (x : GaloisUnitContinuousH2 (K := K) (Ω := Ω)) :
    letI : IsGalois E Ω := IsGalois.tower_top_of_isGalois K E Ω
    localFieldContinuousH2InvariantEquiv E Ω (continuousGaloisUnitBaseChangeH2 K E Ω Ω x) =
      Module.finrank K E • localFieldContinuousH2InvariantEquiv K Ω x :=
  localFieldContinuousH2InvariantEquiv_restriction K Ω E x

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  (E : IntermediateField K Ω) (F : FiniteGaloisIntermediateField K Ω)
  (G : FiniteGaloisIntermediateField E Ω)
  [Algebra F G] [IsScalarTower K F G] [IsScalarTower F G Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω)]



/-- Exact original-object consumer of `continuousGaloisUnitRestriction_general_stage`. -/
theorem actual_local_invariant_functoriality_2282_continuousGaloisUnitRestriction_general_stage_source
    (x : GaloisUnitH2FiniteStage K Ω F) :
    letI : IsGalois E Ω := IsGalois.tower_top_of_isGalois K E Ω
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K F) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K F) := ⟨rfl⟩
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits E G) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits E G) := ⟨rfl⟩
    continuousGaloisUnitBaseChangeH2 K E Ω Ω (galoisUnitH2FiniteStageMap K Ω F x) =
      galoisUnitH2FiniteStageMap E Ω G (finiteGaloisUnitBaseChangeH2 K E F G x) :=
  continuousGaloisUnitRestriction_general_stage E F G x

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]



/-- Exact original-object consumer of `intermediateField_compositum_splitting_polynomial`. -/
theorem actual_local_invariant_functoriality_2283_intermediateField_compositum_splitting_polynomial_source
    (E : IntermediateField K Ω) (F : FiniteGaloisIntermediateField K Ω) :
    ∃ q : Polynomial E, q.Separable ∧
      q.IsSplittingField E (IntermediateField.adjoin E (F.toIntermediateField : Set Ω)) :=
  intermediateField_compositum_splitting_polynomial E F

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]



/-- Exact original-object consumer of `localFieldContinuousInvariant_restriction_general_stage`. -/
theorem actual_local_invariant_functoriality_2284_localFieldContinuousInvariant_restriction_general_stage_source
    (E : IntermediateField K Ω) (F : FiniteGaloisIntermediateField K Ω)
    (G : FiniteGaloisIntermediateField E Ω)
    [Algebra F G] [IsScalarTower K F G] [IsScalarTower F G Ω]
    [ValuativeRel E] [ValuativeRel F] [ValuativeRel G]
    [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace G]
    [IsNonarchimedeanLocalField E] [IsNonarchimedeanLocalField F]
    [IsNonarchimedeanLocalField G]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation F)]
    [(ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation G)]
    [(ValuativeRel.valuation F).HasExtension (ValuativeRel.valuation G)]
    [Algebra.FormallyUnramified 𝒪[K] 𝒪[F]]
    [Algebra.FormallyUnramified 𝒪[E] 𝒪[G]]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω)]
    (y : GaloisUnitH2FiniteStage K Ω F) :
    letI : IsGalois E Ω := IsGalois.tower_top_of_isGalois K E Ω
    localFieldContinuousH2InvariantEquiv E Ω
        (continuousGaloisUnitBaseChangeH2 K E Ω Ω (galoisUnitH2FiniteStageMap K Ω F y)) =
      Module.finrank K E • localFieldContinuousH2InvariantEquiv K Ω
        (galoisUnitH2FiniteStageMap K Ω F y) :=
  localFieldContinuousInvariant_restriction_general_stage K Ω E F G y

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise






/-- Exact original-object consumer of `localFieldContinuousH2InvariantEquiv_finite_restriction`. -/
theorem actual_local_invariant_functoriality_2285_localFieldContinuousH2InvariantEquiv_finite_restriction_source
    (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
    (E : IntermediateField K Ω) [FiniteDimensional K E]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω)]
    (x : GaloisUnitContinuousH2 (K := K) (Ω := Ω)) :
    letI : IsGalois E Ω := IsGalois.tower_top_of_isGalois K E Ω
    localFieldContinuousH2InvariantEquiv E Ω (continuousGaloisUnitBaseChangeH2 K E Ω Ω x) =
      Module.finrank K E • localFieldContinuousH2InvariantEquiv K Ω x :=
  localFieldContinuousH2InvariantEquiv_finite_restriction K Ω E x

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {G : Type} [Group G] (S : Subgroup G)



/-- Exact original-object consumer of `cosetTransition_mul`. -/
theorem actual_local_invariant_functoriality_2286_cosetTransition_mul_source (g h : G) (q : G ⧸ S) :
    cosetTransition S (g * h) q = cosetTransition S g (h • q) * cosetTransition S h q :=
  cosetTransition_mul S g h q

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {R G : Type} [CommRing R] [Group G] (A : Rep R G) (S : Subgroup G)

variable [Fintype (G ⧸ S)]



/-- Exact original-object consumer of `cosetTraceTwo_mem_cocycles`. -/
theorem actual_local_invariant_functoriality_2287_cosetTraceTwo_mem_cocycles_source
    (c : groupCohomology.cocycles₂ (restrictedCoefficientRep A S.subtype)) :
    cosetTraceTwo A S c ∈ groupCohomology.cocycles₂ A :=
  cosetTraceTwo_mem_cocycles A S c

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {R G : Type} [CommRing R] [Group G] (A : Rep R G) (S : Subgroup G)



/-- Exact original-object consumer of `cosetTraceTwo_differential`. -/
theorem actual_local_invariant_functoriality_2288_cosetTraceTwo_differential_source [Fintype (G ⧸ S)] (f : S → A) :
    cosetTraceTwo A S (groupCohomology.d₁₂ (restrictedCoefficientRep A S.subtype) f) =
      groupCohomology.d₁₂ A (cosetTraceOne A S f) :=
  cosetTraceTwo_differential A S f

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep R G) [TopologicalSpace A] [IsTopologicalAddGroup A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (S : Subgroup G) [Fintype (G ⧸ S)] (hS : IsOpen (S : Set G))

variable [TopologicalSpace R] [ContinuousSMul R A]


include hA hS

/-- Exact original-object consumer of `continuousCosetTraceTwo_coboundary`. -/
theorem actual_local_invariant_functoriality_2289_continuousCosetTraceTwo_coboundary_source (f : C(S, A)) :
    continuousCosetTraceTwo A hA S hS
      (continuousRepresentationCoboundaryTwo (restrictedCoefficientRep A S.subtype)
        (restrictedCoefficientAction_continuous A S.subtype continuous_subtype_val hA) f) =
      continuousRepresentationCoboundaryTwo A hA (continuousCosetTraceOne A hA S hS f) :=
  continuousCosetTraceTwo_coboundary A hA S hS f

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {R G : Type} [CommRing R] [Group G] (A : Rep R G) (S : Subgroup G)



/-- Exact original-object consumer of `cosetRestrictionHomotopy_differential`. -/
theorem actual_local_invariant_functoriality_2290_cosetRestrictionHomotopy_differential_source [Fintype (G ⧸ S)]
    (c : groupCohomology.cocycles₂ A) :
    groupCohomology.d₁₂ A (cosetRestrictionHomotopy A S c) =
      Fintype.card (G ⧸ S) • c.val - cosetTraceTwo A S (fun z => c (z.1, z.2)) :=
  cosetRestrictionHomotopy_differential A S c

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep R G) [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (S : Subgroup G) [Fintype (G ⧸ S)] (hS : IsOpen (S : Set G))



/-- Exact original-object consumer of `continuousRepresentationH2Corestriction_restriction`. -/
theorem actual_local_invariant_functoriality_2291_continuousRepresentationH2Corestriction_restriction_source
    (x : ContinuousRepresentationH2 A hA) :
    continuousRepresentationH2Corestriction A hA S hS
      (continuousRepresentationH2Restriction A hA S.subtype continuous_subtype_val x) =
        Fintype.card (G ⧸ S) • x :=
  continuousRepresentationH2Corestriction_restriction A hA S hS x

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (E : IntermediateField K Ω)

variable [FiniteDimensional K E]



omit [FiniteDimensional K E] in
/-- Exact original-object consumer of `galoisFixingCosets_card`. -/
theorem actual_local_invariant_functoriality_2292_galoisFixingCosets_card_source [Fintype (Gal(Ω/K) ⧸ E.fixingSubgroup)] :
    Fintype.card (Gal(Ω/K) ⧸ E.fixingSubgroup) = Module.finrank K E :=
  galoisFixingCosets_card K Ω E

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (E : IntermediateField K Ω) [IsGalois E Ω]
  [tK : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  [tE : TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω)]



omit [IsGalois E Ω] in
/-- Exact original-object consumer of `galoisFixingUnitCocycle_coboundary`. -/
theorem actual_local_invariant_functoriality_2293_galoisFixingUnitCocycle_coboundary_source
    (f : C(Gal(Ω/E), Rep.ofAlgebraAutOnUnits E Ω)) :
    galoisFixingUnitCocycle K Ω E
      (continuousRepresentationCoboundaryTwo (Rep.ofAlgebraAutOnUnits E Ω)
        (discreteGaloisUnitAction_continuous (K := E) (Ω := Ω)) f) =
      continuousRepresentationCoboundaryTwo
        (restrictedCoefficientRep (Rep.ofAlgebraAutOnUnits K Ω) E.fixingSubgroup.subtype)
        (restrictedCoefficientAction_continuous (Rep.ofAlgebraAutOnUnits K Ω)
          E.fixingSubgroup.subtype continuous_subtype_val
          (discreteGaloisUnitAction_continuous (K := K) (Ω := Ω)))
        (galoisFixingUnitCochain K Ω E f) :=
  galoisFixingUnitCocycle_coboundary K Ω E f

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (E : IntermediateField K Ω) [IsGalois E Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω)]



/-- Exact original-object consumer of `galoisFixingUnitH2_baseChange`. -/
theorem actual_local_invariant_functoriality_2294_galoisFixingUnitH2_baseChange_source (x : GaloisUnitContinuousH2 (K := K) (Ω := Ω)) :
    galoisFixingUnitH2 K Ω E (continuousGaloisUnitBaseChangeH2 K E Ω Ω x) =
      continuousRepresentationH2Restriction (Rep.ofAlgebraAutOnUnits K Ω)
        (discreteGaloisUnitAction_continuous (K := K) (Ω := Ω))
        E.fixingSubgroup.subtype continuous_subtype_val x :=
  galoisFixingUnitH2_baseChange K Ω E x

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (E : IntermediateField K Ω) [FiniteDimensional K E] [IsGalois E Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω)]



/-- Exact original-object consumer of `galoisUnitContinuousCorestriction_restriction`. -/
theorem actual_local_invariant_functoriality_2295_galoisUnitContinuousCorestriction_restriction_source
    (x : GaloisUnitContinuousH2 (K := K) (Ω := Ω)) :
    galoisUnitContinuousCorestriction K Ω E (continuousGaloisUnitBaseChangeH2 K E Ω Ω x) =
      Module.finrank K E • x :=
  galoisUnitContinuousCorestriction_restriction K Ω E x

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  (E : IntermediateField K Ω) [FiniteDimensional K E]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω)]



/-- Exact original-object consumer of `localFieldContinuousH2_restriction_surjective`. -/
theorem actual_local_invariant_functoriality_2296_localFieldContinuousH2_restriction_surjective_source :
    letI : IsGalois E Ω := IsGalois.tower_top_of_isGalois K E Ω
    Function.Surjective (continuousGaloisUnitBaseChangeH2 K E Ω Ω) :=
  localFieldContinuousH2_restriction_surjective K Ω E

end


section

open IsDedekindDomain Matrix Module WithConv CategoryTheory IsLocalRing Polynomial Filter Topology
open scoped BigOperators TensorProduct NumberField nonZeroDivisors WithZero Ring ValuativeRel Pointwise


variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  (E : IntermediateField K Ω) [FiniteDimensional K E]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω)]



/-- Exact original-object consumer of `localFieldContinuousH2InvariantEquiv_corestriction`. -/
theorem actual_local_invariant_functoriality_2297_localFieldContinuousH2InvariantEquiv_corestriction_source :
    letI : IsGalois E Ω := IsGalois.tower_top_of_isGalois K E Ω
    ∀ y : GaloisUnitContinuousH2 (K := E) (Ω := Ω),
      localFieldContinuousH2InvariantEquiv K Ω (galoisUnitContinuousCorestriction K Ω E y) =
        localFieldContinuousH2InvariantEquiv E Ω y :=
  localFieldContinuousH2InvariantEquiv_corestriction K Ω E

end

end Dubon2026.SemanticRegression

import Dubon2026.SourceCurveAdelicIndex

/-! DUB-17/18 -> actual cusp-form dimension -> regular differential
dimension -> Riemann--Roch -> residue duality. The proved global index
formula forces any two bounded global-annihilating functionals to be
function-field multiples. This is the necessary rank-one step for the
residue pairing; constructing the canonical residue functional remains
separate. Selected source: Def_AlgebraicCurve_AdelicIndex and
S_AlgebraicCurve_omegaSpace_finite_of_genusReached, anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceCurve
noncomputable section
open Module
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

variable (K F) in
/-- The union of bounded global-annihilating functionals. -/
def weilDifferentialModule : Submodule K (Module.Dual K (adeleSpace K F)) :=
  ⨆ D : Divisor K F, omegaSpace D

theorem omegaSpace_le_weilDifferentialModule (D : Divisor K F) :
    omegaSpace D ≤ weilDifferentialModule K F := le_iSup omegaSpace D

theorem omegaSpace_directed :
    Directed (· ≤ ·) (omegaSpace (K := K) (F := F)) := fun D E =>
  ⟨D ⊓ E, omegaSpace_antitone inf_le_left, omegaSpace_antitone inf_le_right⟩

theorem mem_weilDifferentialModule_iff {φ : Module.Dual K (adeleSpace K F)} :
    φ ∈ weilDifferentialModule K F ↔ ∃ D : Divisor K F, φ ∈ omegaSpace D := by
  unfold weilDifferentialModule
  exact Submodule.mem_iSup_of_directed _ omegaSpace_directed

variable (K) in

/-- Pointwise multiplication of repartitions by a function. -/
def mulAdele (f : F) : (Place K F → F) →ₗ[K] (Place K F → F) where
  toFun α := fun v => f * α v
  map_add' α β := funext fun v => mul_add f (α v) (β v)
  map_smul' c α := funext fun v => by
    simp only [Pi.smul_apply, Algebra.smul_def, RingHom.id_apply]; ring

@[simp]
theorem mulAdele_apply (f : F) (α : Place K F → F) (v : Place K F) :
    mulAdele K f α v = f * α v := rfl

@[simp]
theorem mulAdele_one : mulAdele K (1 : F) = LinearMap.id :=
  LinearMap.ext fun α => funext fun v => one_mul (α v)

theorem mulAdele_mul (f g : F) :
    mulAdele K (f * g) = (mulAdele K f).comp (mulAdele K g) :=
  LinearMap.ext fun α => funext fun v => mul_assoc f g (α v)

theorem mulAdele_mem_adeleBdd_sub {f : F} (hf : f ≠ 0) {P : Divisor K F}
    (hP : ∀ v, P v = v.ord f) {D : Divisor K F} {α : Place K F → F}
    (hα : α ∈ adeleBdd D) : mulAdele K f α ∈ adeleBdd (D - P) := by
  intro v
  rw [mulAdele_apply, Valuation.map_mul, Finsupp.sub_apply, hP v,
    show v.adicValuation f = WithZero.exp (-v.ord f) by
      rw [Place.ord, neg_neg, WithZero.exp_log (v.adicValuation_ne_zero hf)]]
  calc WithZero.exp (-v.ord f) * v.adicValuation (α v)
      ≤ WithZero.exp (-v.ord f) * WithZero.exp (D v) := by gcongr; exact hα v
    _ = WithZero.exp (D v - v.ord f) := by rw [← WithZero.exp_add]; ring_nf

theorem mulAdele_globalSub_le (f : F) :
    (globalSub K F).map (mulAdele K f) ≤ globalSub K F := by
  rintro _ ⟨α, ⟨g, rfl⟩, rfl⟩
  exact ⟨f * g, funext fun v => by rfl⟩

theorem mulAdele_mem_adeleSpace [HasPrincipalDivisors K F] (f : F) {α : Place K F → F}
    (hα : α ∈ adeleSpace K F) : mulAdele K f α ∈ adeleSpace K F := by
  rcases eq_or_ne f 0 with rfl | hf
  · have h0 : mulAdele K (0 : F) α = 0 := funext fun v => by simp
    rw [h0]; exact (adeleSpace K F).zero_mem
  · obtain ⟨D, hD⟩ := mem_adeleSpace_iff.mp hα
    obtain ⟨P, hP, _⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf
    exact adeleBdd_le_adeleSpace (D := D - P) (mulAdele_mem_adeleBdd_sub hf hP hD)

variable (K F) in

/-- Multiplication restricted to actual repartitions. -/
def adeleSpaceMul [HasPrincipalDivisors K F] (f : F) :
    adeleSpace K F →ₗ[K] adeleSpace K F :=
  (mulAdele K f).restrict fun _ => mulAdele_mem_adeleSpace f

@[simp]
theorem adeleSpaceMul_coe [HasPrincipalDivisors K F] (f : F) (α : adeleSpace K F) :
    (adeleSpaceMul K F f α : Place K F → F) = mulAdele K f (α : Place K F → F) := rfl

variable (K F) in

/-- The induced action on linear functionals. -/
def weilSmul [HasPrincipalDivisors K F] (f : F) :
    Module.Dual K (adeleSpace K F) →ₗ[K] Module.Dual K (adeleSpace K F) :=
  (adeleSpaceMul K F f).dualMap

@[simp]
theorem weilSmul_apply [HasPrincipalDivisors K F] (f : F)
    (φ : Module.Dual K (adeleSpace K F)) (α : adeleSpace K F) :
    weilSmul K F f φ α = φ (adeleSpaceMul K F f α) := rfl

theorem adeleSpaceMul_one [HasPrincipalDivisors K F] :
    adeleSpaceMul K F (1 : F) = LinearMap.id := by
  refine LinearMap.ext fun α => Subtype.ext ?_
  show mulAdele K (1 : F) (α : Place K F → F) = (α : Place K F → F)
  rw [mulAdele_one, LinearMap.id_apply]

theorem adeleSpaceMul_mul [HasPrincipalDivisors K F] (f g : F) :
    adeleSpaceMul K F (f * g) = (adeleSpaceMul K F f).comp (adeleSpaceMul K F g) := by
  refine LinearMap.ext fun α => Subtype.ext ?_
  show mulAdele K (f * g) (α : Place K F → F) = mulAdele K f (mulAdele K g (α : Place K F → F))
  rw [mulAdele_mul, LinearMap.comp_apply]

@[simp]
theorem weilSmul_one [HasPrincipalDivisors K F] :
    weilSmul K F (1 : F) = LinearMap.id := by
  unfold weilSmul; rw [adeleSpaceMul_one]; ext; simp

theorem weilSmul_mul [HasPrincipalDivisors K F] (f g : F) :
    weilSmul K F (f * g) = (weilSmul K F g).comp (weilSmul K F f) := by
  unfold weilSmul; rw [adeleSpaceMul_mul, LinearMap.dualMap_comp_dualMap]

theorem weilSmul_injective [HasPrincipalDivisors K F] {f : F} (hf : f ≠ 0) :
    Function.Injective (weilSmul K F f) := by
  apply Function.LeftInverse.injective (g := weilSmul K F f⁻¹)
  intro φ
  rw [← LinearMap.comp_apply, ← weilSmul_mul, mul_inv_cancel₀ hf, weilSmul_one,
    LinearMap.id_apply]

theorem weilSmul_mem_omegaSpace_add [HasPrincipalDivisors K F] {f : F} (hf : f ≠ 0)
    {P : Divisor K F} (hP : ∀ v, P v = v.ord f) {D : Divisor K F}
    {φ : Module.Dual K (adeleSpace K F)} (hφ : φ ∈ omegaSpace D) :
    weilSmul K F f φ ∈ omegaSpace (D + P) := by
  rw [omegaSpace, Submodule.mem_dualAnnihilator]

  intro α hα
  obtain ⟨β, hβ, γ, hγ, rfl⟩ := Submodule.mem_sup.mp hα
  rw [map_add, weilSmul_apply, weilSmul_apply]

  have hβ' : (adeleSpaceMul K F f β : Place K F → F) ∈ adeleBdd D := by
    rw [adeleSpaceMul_coe]
    have h := mulAdele_mem_adeleBdd_sub hf hP (D := D + P) (Submodule.mem_comap.mp hβ)
    rwa [add_sub_cancel_right] at h

  have hγ' : (adeleSpaceMul K F f γ : Place K F → F) ∈ globalSub K F :=
    mulAdele_globalSub_le f ⟨_, Submodule.mem_comap.mp hγ, rfl⟩
  rw [omegaSpace_vanishBdd hφ hβ', omegaSpace_vanishGlobal hφ hγ', add_zero]

theorem weilSmul_mem_omegaSpace_of_mem_lSpace [HasPrincipalDivisors K F]
    {W D : Divisor K F} {φ : Module.Dual K (adeleSpace K F)} (hφ : φ ∈ omegaSpace W)
    {g : F} (hg : g ∈ LSpace (W - D)) :
    weilSmul K F g φ ∈ omegaSpace D := by
  rcases eq_or_ne g 0 with rfl | hg0
  ·
    have h0 : weilSmul K F (0 : F) φ = 0 := by
      ext α; simp only [weilSmul_apply]
      refine omegaSpace_vanishBdd hφ ?_
      intro v
      simp only [adeleSpaceMul_coe, mulAdele_apply, zero_mul, Valuation.map_zero]
      exact zero_le'
    rw [h0]; exact (omegaSpace D).zero_mem
  ·
    obtain ⟨P, hPord, _⟩ := HasPrincipalDivisors.exists_divisor (K := K) g hg0
    refine omegaSpace_antitone ?_ (weilSmul_mem_omegaSpace_add hg0 hPord hφ)

    intro v
    rw [Finsupp.add_apply, hPord v]
    have hgL := (mem_lSpace_iff_ord.mp hg).resolve_left hg0 v
    rw [Finsupp.sub_apply] at hgL
    linarith

end
end Dubon2026.SourceCurve

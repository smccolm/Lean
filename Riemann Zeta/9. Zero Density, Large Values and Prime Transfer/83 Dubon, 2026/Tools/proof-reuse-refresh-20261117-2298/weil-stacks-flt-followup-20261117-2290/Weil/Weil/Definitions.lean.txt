module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FieldValuedPointCount
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicTraceFormulaFinal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.ConstantSystem
public import Mathlib.Algebra.Field.ULift
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.Finite.Extension
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Topology.KrullDimension
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Spec
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Topology.Sheaves.Sheaf
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.Basic

/-!
# The definitions in the statements of the Weil conjectures

The definitions entering the statements of the main theorems:
the point counts and the zeta series of a scheme over a finite field, the rational ℓ-adic
cohomology of a proper scheme with its Frobenius, `P_ν`, the Weil estimate, the Euler
characteristic, the sign of the functional equation, the complex points of a scheme over `ℂ` with
the analytic topology, its Betti numbers, and good reduction. The development takes them from here.
-/

@[expose] public noncomputable section

universe u

namespace AlgebraicGeometry

section PointCount

open CategoryTheory Stacks.EtaleCohomology

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The number `#X(K)` of `K`-valued points of a scheme `X` over `k`, i.e. of morphisms
`Spec K ⟶ X` over `Spec k`; it is `0` when there are infinitely many. -/
@[weil "def_fk0_point_count"]
def pointCount (K : Type u) [Field K] [Algebra k K] : ℕ :=
  Nat.card (fieldValuedPoints f K)

variable [Finite k]

/-- The `n`-th point count `A_n = #X(k_n)` of `X` over the finite field `k`, `k_n` an extension
of `k` of degree `n ≥ 1` (Mathlib's chosen one, lifted to the universe of `X`); `0` when `X(k_n)`
is infinite. -/
@[weil "def_fk0_point_count"]
def pointCountOfDegree (n : ℕ) [NeZero n] : ℕ :=
  haveI : Fact (ringChar k).Prime := ⟨CharP.char_is_prime k _⟩
  pointCount f (ULift.{u} (FiniteField.Extension k (ringChar k) n))

end PointCount

section ZetaSeries

open CategoryTheory

variable {k : Type u} [Field k] [Finite k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The series `u = ∑_{n ≥ 1} (A_n / n) tⁿ ∈ ℚ⟦t⟧` of the point counts `A_n` of `X`. -/
@[weil "def_fk0_zeta_series_from_point_counts"]
def pointCountLogSeries : PowerSeries ℚ :=
  PowerSeries.mk fun n => if h : n = 0 then 0 else
    haveI : NeZero n := ⟨h⟩
    (pointCountOfDegree f n : ℚ) / n

/-- The zeta series `f_X = exp u = ∑_{m ≥ 0} uᵐ / m!` of a scheme `X` over a finite field. -/
@[weil "def_fk0_zeta_series_from_point_counts"]
def zetaSeries : PowerSeries ℚ :=
  (PowerSeries.exp ℚ).subst (pointCountLogSeries f)

end ZetaSeries

end AlgebraicGeometry

namespace Weil

open CategoryTheory AlgebraicGeometry Stacks.EtaleCohomology

section RationalCohomology

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] [Fintype k]
  (f : X.1 ⟶ Spec (.of k)) [IsProper f] (ℓ : ℕ) [Fact ℓ.Prime]

/-- `H^ν(X_k̄, ℚ_ℓ) = H^ν_c(X_k̄, ℤ_ℓ) ⊗ ℚ_ℓ` for `X` proper over the finite field `k`, computed
with the compactification `id_X` and the algebraic closure `AlgebraicClosure k`. A scheme proper
over a field is noetherian, hence quasi-separated. -/
@[weil "def_fk401_frobenius_on_rational_cohomology"]
noncomputable abbrev rationalCohomology (ν : ℕ) : ModuleCat.{u + 1} ℚ_[ℓ] :=
  haveI hN : IsNoetherian X.1 := by
    have := LocallyOfFiniteType.isLocallyNoetherian f
    have : CompactSpace X.1 :=
      ⟨by simpa using (quasiCompact_iff f).mp inferInstance _ isOpen_univ isCompact_univ⟩
    exact ⟨⟩
  haveI : QuasiSeparatedSpace X.1 :=
    @IsLocallyNoetherian.quasiSeparatedSpace X.1 hN.toIsLocallyNoetherian
  LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f (CompactificationOf.ofProper f)
    (AlgebraicClosure k) (LAdicSheaf.constantSystem B X ℓ) ν

/-- The Frobenius endomorphism `F_ν` of `H^ν(X_k̄, ℚ_ℓ)`: the geometric Frobenius, with the
characteristic `p` and the exponent of `#k = pᵉ` read off from `k`. -/
@[weil "def_fk401_frobenius_on_rational_cohomology"]
noncomputable def rationalFrobenius (ν : ℕ) : Module.End ℚ_[ℓ] (rationalCohomology B X f ℓ ν) :=
  haveI hN : IsNoetherian X.1 := by
    have := LocallyOfFiniteType.isLocallyNoetherian f
    have : CompactSpace X.1 :=
      ⟨by simpa using (quasiCompact_iff f).mp inferInstance _ isOpen_univ isCompact_univ⟩
    exact ⟨⟩
  haveI : QuasiSeparatedSpace X.1 :=
    @IsLocallyNoetherian.quasiSeparatedSpace X.1 hN.toIsLocallyNoetherian
  haveI : Fact (ringChar k).Prime := ⟨CharP.char_is_prime k _⟩
  (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f (CompactificationOf.ofProper f)
    (AlgebraicClosure k) (ringChar k) (FiniteField.card k (ringChar k)).choose
    (FiniteField.card k (ringChar k)).choose_spec.2 (LAdicSheaf.constantSystem B X ℓ) ν).hom

omit [Fintype k] in
/-- `H^ν(X_k̄, ℚ_ℓ)` is finite dimensional over `ℚ_ℓ` when `ℓ ≠ char k` (Stacks, Tag 03V2). -/
instance [Finite k] [Fact (ℓ ≠ ringChar k)] (ν : ℕ) :
    FiniteDimensional ℚ_[ℓ] (rationalCohomology B X f ℓ ν) := by
  have := Fintype.ofFinite k
  have hN : IsNoetherian X.1 := by
    have := LocallyOfFiniteType.isLocallyNoetherian f
    have : CompactSpace X.1 :=
      ⟨by simpa using (quasiCompact_iff f).mp inferInstance _ isOpen_univ isCompact_univ⟩
    exact ⟨⟩
  have : QuasiSeparatedSpace X.1 :=
    @IsLocallyNoetherian.quasiSeparatedSpace X.1 hN.toIsLocallyNoetherian
  have : Fact (ringChar k).Prime := ⟨CharP.char_is_prime k _⟩
  exact (LAdicSheaf.traceFormula B X ℓ f (CompactificationOf.ofProper f) (AlgebraicClosure k)
    (ringChar k) (FiniteField.card k (ringChar k)).choose
    (FiniteField.card k (ringChar k)).choose_spec.2 Fact.out (LAdicSheaf.constantSystem B X ℓ)).1 ν

/-- `P_ν(t) = det(1 - t F_ν | H^ν(X_k̄, ℚ_ℓ))`, the reverse of the characteristic polynomial of
`F_ν`. -/
@[weil "def_fk401_frobenius_char_poly_cohomology"]
noncomputable def rationalFrobeniusCharpolyReverse [Fact (ℓ ≠ ringChar k)] (ν : ℕ) :
    Polynomial ℚ_[ℓ] :=
  (rationalFrobenius B X f ℓ ν).charpoly.reverse

/-- The Weil estimate `W(X/k)`: every eigenvalue `λ ∈ ℚ̄_ℓ` of every `F_ν` is algebraic over `ℚ`
and `|ι λ| = q ^ (ν / 2)` for every field embedding `ι : ℚ(λ) → ℂ`, where `q = #k`. -/
@[weil "def_fk401_weil_estimate_property"]
def SatisfiesWeilEstimate [Fact (ℓ ≠ ringChar k)] : Prop :=
  ∀ (ν : ℕ) (μ : AlgebraicClosure ℚ_[ℓ]),
    Polynomial.aeval μ (rationalFrobenius B X f ℓ ν).charpoly = 0 →
      IsAlgebraic ℚ μ ∧ ∀ ι : IntermediateField.adjoin ℚ {μ} →+* ℂ,
        ‖ι (IntermediateField.AdjoinSimple.gen ℚ μ)‖ = (Fintype.card k : ℝ) ^ ((ν : ℝ) / 2)

end RationalCohomology

section EulerCharacteristic

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k]
  (f : X.1 ⟶ Spec (.of k)) [IsProper f] (ℓ : ℕ) [Fact ℓ.Prime]

/-- The Krull dimension of the scheme `X` as a natural number (`0` for the empty scheme and for a
scheme of infinite dimension). -/
noncomputable def schemeDimension : ℕ :=
  ((topologicalKrullDim X.1).unbotD 0).toNat

/-- The ℓ-adic Betti number `b_ν = dim_{ℚ_ℓ} H^ν(X_k̄, ℚ_ℓ)`. -/
noncomputable abbrev bettiNumber (ν : ℕ) : ℕ :=
  Module.finrank ℚ_[ℓ] (rationalCohomology B X f ℓ ν)

/-- The Euler characteristic `χ(X) = ∑_{ν = 0}^{2n} (-1)^ν b_ν`, `n` the dimension of `X`. -/
@[weil "def_fk401_euler_characteristic"]
noncomputable def eulerCharacteristic : ℤ :=
  ∑ ν ∈ Finset.range (2 * schemeDimension B X + 1), (-1) ^ ν * (bettiNumber B X f ℓ ν : ℤ)

end EulerCharacteristic

section FunctionalEquationSign

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] [Fintype k]
  (f : X.1 ⟶ Spec (.of k)) [IsProper f] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ℓ ≠ ringChar k)]

/-- The sign `ε` of the functional equation in dimension `n`: `1` if `n` is odd, and `(-1) ^ N`
if `n` is even, `N` the multiplicity of `q ^ (n / 2)` as an eigenvalue of `F_n`. -/
@[weil "def_fk401_functional_equation_sign"]
noncomputable def functionalEquationSign (n : ℕ) : ℤ :=
  if Odd n then 1 else
    (-1) ^ Polynomial.rootMultiplicity ((Fintype.card k : ℚ_[ℓ]) ^ (n / 2))
      (rationalFrobenius B X f ℓ n).charpoly

end FunctionalEquationSign

end Weil

namespace AlgebraicGeometry.Scheme

section ComplexPoints

open CategoryTheory TopologicalSpace

/-- The complex points `Y(ℂ)` of a scheme `Y` over `ℂ` with structure morphism `y`: the
sections `p : Spec ℂ ⟶ Y` of `y`. -/
def ComplexPoints {Y : Scheme.{0}} (y : Y ⟶ Spec (.of ℂ)) : Type :=
  {p : Spec (.of ℂ) ⟶ Y // p ≫ y = 𝟙 _}

namespace ComplexPoints

variable {Y : Scheme.{0}} {y : Y ⟶ Spec (.of ℂ)}

/-- The underlying morphism `Spec ℂ ⟶ Y` of a complex point. -/
def hom (p : ComplexPoints y) : Spec (.of ℂ) ⟶ Y := p.1

/-- The point `p ∈ Y(ℂ)` lies in `U(ℂ)`: the preimage of `U` under `p` is all of `Spec ℂ`. -/
def Mem (p : ComplexPoints y) (U : Y.Opens) : Prop := p.hom ⁻¹ᵁ U = ⊤

/-- The value `g(p) ∈ ℂ` of a regular function `g ∈ Γ(Y, U)` at a point `p ∈ U(ℂ)`: the image of
`g` under `p^* : Γ(Y, U) → Γ(Spec ℂ, ⊤) ≅ ℂ`. -/
noncomputable def eval {U : Y.Opens} (g : Γ(Y, U)) (p : ComplexPoints y) (hp : p.Mem U) : ℂ :=
  (Scheme.ΓSpecIso (.of ℂ)).hom (p.hom.appLE U ⊤ hp.ge g)

/-- The generating sets of the analytic topology: `{p ∈ U(ℂ) | g(p) ∈ V}`. -/
def basicSet (U : Y.Opens) (g : Γ(Y, U)) (V : Set ℂ) : Set (ComplexPoints y) :=
  {p | ∃ hp : p.Mem U, eval g p hp ∈ V}

/-- The family of generating sets of the analytic topology: `basicSet U g V` for `U` an affine
open of `Y`, `g ∈ Γ(Y, U)` and `V ⊆ ℂ` open. -/
def basicSets (y : Y ⟶ Spec (.of ℂ)) : Set (Set (ComplexPoints y)) :=
  {s | ∃ (U : Y.Opens) (_ : IsAffineOpen U) (g : Γ(Y, U)) (V : Set ℂ) (_ : IsOpen V),
    s = basicSet U g V}

/-- The analytic topology on `Y(ℂ)`: the coarsest topology for which `U(ℂ)` is open and every
`g ∈ Γ(Y, U)` is continuous on `U(ℂ)`, for every affine open `U` of `Y`. -/
instance instTopologicalSpace : TopologicalSpace (ComplexPoints y) :=
  TopologicalSpace.generateFrom (basicSets y)

end ComplexPoints

end ComplexPoints

section BettiNumber

open CategoryTheory TopologicalSpace

variable {Y : Scheme.{0}}

/-- The constant sheaf `ℂ` of `ℂ`-vector spaces on the complex points `Y(ℂ)`. -/
noncomputable abbrev complexConstantSheaf (y : Y ⟶ Spec (.of ℂ)) :
    Sheaf (Opens.grothendieckTopology (TopCat.of (ComplexPoints y))) (ModuleCat.{0} ℂ) :=
  (constantSheaf (Opens.grothendieckTopology (TopCat.of (ComplexPoints y))) (ModuleCat.{0} ℂ)).obj
    (ModuleCat.of ℂ ℂ)

/-- The complex cohomology `H^ν(Y(ℂ), ℂ)`: the sheaf cohomology `Ext^ν(ℂ, ℂ)` of the constant
sheaf `ℂ` among sheaves of `ℂ`-vector spaces on `Y(ℂ)` with the analytic topology. -/
noncomputable def complexCohomology (y : Y ⟶ Spec (.of ℂ)) (ν : ℕ) : Type :=
  letI := IsGrothendieckAbelian.hasExt.{0}
    (Sheaf (Opens.grothendieckTopology (TopCat.of (ComplexPoints y))) (ModuleCat.{0} ℂ))
  Abelian.Ext (complexConstantSheaf y) (complexConstantSheaf y) ν

noncomputable instance (y : Y ⟶ Spec (.of ℂ)) (ν : ℕ) :
    AddCommGroup (complexCohomology y ν) :=
  letI := IsGrothendieckAbelian.hasExt.{0}
    (Sheaf (Opens.grothendieckTopology (TopCat.of (ComplexPoints y))) (ModuleCat.{0} ℂ))
  inferInstanceAs (AddCommGroup (Abelian.Ext (complexConstantSheaf y) (complexConstantSheaf y) ν))

noncomputable instance (y : Y ⟶ Spec (.of ℂ)) (ν : ℕ) : Module ℂ (complexCohomology y ν) :=
  letI := IsGrothendieckAbelian.hasExt.{0}
    (Sheaf (Opens.grothendieckTopology (TopCat.of (ComplexPoints y))) (ModuleCat.{0} ℂ))
  inferInstanceAs (Module ℂ (Abelian.Ext (complexConstantSheaf y) (complexConstantSheaf y) ν))

/-- The Betti number `b_ν(Y) = dim_ℂ H^ν(Y(ℂ), ℂ)` of a scheme `Y` over `ℂ`. -/
@[weil "def_fk401_betti_number"]
noncomputable def bettiNumber (y : Y ⟶ Spec (.of ℂ)) (ν : ℕ) : ℕ :=
  Module.finrank ℂ (complexCohomology y ν)

end BettiNumber

section GoodReduction

open CategoryTheory Limits

/-- `S₀` over the field `κ` arises by good reduction of `Y` over `ℂ`: there are an integral
domain `R` of finite type over `ℤ`, a smooth projective `f : X ⟶ Spec R`, ring homomorphisms
`φ : R →+* ℂ` and `ψ : R →+* κ`, and isomorphisms `X ×_{Spec R} Spec ℂ ≅ Y` over `Spec ℂ` and
`X ×_{Spec R} Spec κ ≅ S₀` over `Spec κ`. -/
@[weil "def_fk401_good_reduction"]
def ArisesByGoodReduction {κ : Type} [Field κ] {S₀ : Scheme.{0}} (s₀ : S₀ ⟶ Spec (.of κ))
    {Y : Scheme.{0}} (y : Y ⟶ Spec (.of ℂ)) : Prop :=
  ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : Algebra.FiniteType ℤ R)
    (X : Scheme.{0}) (f : X ⟶ Spec (.of R)) (_ : Smooth f) (_ : IsProjective f)
    (φ : R →+* ℂ) (ψ : R →+* κ),
    (∃ e : pullback f (Spec.map (CommRingCat.ofHom φ)) ≅ Y, e.hom ≫ y = pullback.snd _ _) ∧
    (∃ e : pullback f (Spec.map (CommRingCat.ofHom ψ)) ≅ S₀, e.hom ≫ s₀ = pullback.snd _ _)

end GoodReduction

end AlgebraicGeometry.Scheme

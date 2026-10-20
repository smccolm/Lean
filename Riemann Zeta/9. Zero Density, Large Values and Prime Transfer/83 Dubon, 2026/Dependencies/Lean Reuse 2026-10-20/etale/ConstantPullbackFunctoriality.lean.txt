/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Classical.ConstantCoefficientsComparison
import Nyll.EtaleCohomology.Classical.EndomorphismPullbackComposition
import Nyll.EtaleCohomology.Classical.PullbackIdentity

/-!
# Functoriality of native constant-module cohomology

The actual constant-coefficient comparison transfers identity and composition
from abelian pullback to the original coefficient-linear maps. It also identifies
powers of an endomorphism's pullback with pullback along its actual scheme powers.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace EtaleCohomology

variable {X : Scheme.{u}} (R : Type u) [CommRing R]

/-- Pullback by the scheme identity is the identity on the native constant-module
cohomology, in every degree. -/
theorem etaleConstantCohomologyPullbackMap_id (M : ModuleCat.{u} R) (n : ℕ) :
    etaleConstantCohomologyPullbackMap (𝟙 X) R M n = 1 := by
  apply LinearMap.ext
  intro x
  let d := etaleConstantCohomologyForgetEquiv R (X := X) M n
  apply d.injective
  change d (etaleConstantCohomologyPullbackMap (𝟙 X) R M n x) = d x
  exact (etaleConstantCohomologyPullbackMap_forget R (𝟙 X) M n x).trans
    (etaleAbelianConstantCohomologyPullbackMap_id X
      ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj M) n (d x))

/-- The existing coefficient-linear constant-cohomology pullbacks compose
contravariantly under actual scheme endomorphism composition. -/
theorem etaleConstantCohomologyPullbackMap_comp_end (f g : X ⟶ X)
    (M : ModuleCat.{u} R) (n : ℕ) :
    etaleConstantCohomologyPullbackMap (f ≫ g) R M n =
      etaleConstantCohomologyPullbackMap f R M n *
        etaleConstantCohomologyPullbackMap g R M n := by
  apply LinearMap.ext
  intro x
  let A := (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj M
  let F := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A
  let d := etaleConstantCohomologyForgetEquiv R (X := X) M n
  let a (h : X ⟶ X) : AddMonoid.End (Sheaf.H.{u} F n) :=
    (Sheaf.H.map ((etaleAbelianPullbackConstantIso h).hom.app A) n).comp
      (etaleAbelianCohomologyPullbackMap h F n)
  have ha (h : X ⟶ X) (y : etaleCohomology X R
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj M) n) :
      d (etaleConstantCohomologyPullbackMap h R M n y) = a h (d y) :=
    etaleConstantCohomologyPullbackMap_forget R h M n y
  apply d.injective
  change d (etaleConstantCohomologyPullbackMap (f ≫ g) R M n x) =
    d (etaleConstantCohomologyPullbackMap f R M n
      (etaleConstantCohomologyPullbackMap g R M n x))
  calc
    _ = a (f ≫ g) (d x) := ha (f ≫ g) x
    _ = a f (a g (d x)) :=
      etaleAbelianConstantCohomologyEndomorphismPullbackMap_comp f g A n (d x)
    _ = a f (d (etaleConstantCohomologyPullbackMap g R M n x)) :=
      congrArg (a f) (ha g x).symm
    _ = _ := (ha f (etaleConstantCohomologyPullbackMap g R M n x)).symm

/-- Powers of the native coefficient-linear pullback are pullbacks by the
actual powers of the original scheme endomorphism. -/
theorem etaleConstantCohomologyPullbackMap_pow (f : X ⟶ X)
    (M : ModuleCat.{u} R) (n m : ℕ) :
    (etaleConstantCohomologyPullbackMap f R M n) ^ m =
      etaleConstantCohomologyPullbackMap ((CategoryTheory.End.of f) ^ m).asHom R M n := by
  induction m with
  | zero =>
      change 1 = etaleConstantCohomologyPullbackMap (𝟙 X) R M n
      exact (etaleConstantCohomologyPullbackMap_id R M n).symm
  | succ m ih =>
      rw [pow_succ', pow_succ, CategoryTheory.End.mul_def,
        etaleConstantCohomologyPullbackMap_comp_end, ih]

end EtaleCohomology

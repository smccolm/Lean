import Mathlib.RingTheory.Norm.Basic
import P2M.Util
namespace P2MW.S_Algebra_norm_of_subsingleton

theorem solution {R A : Type*} [CommRing R] [Ring A] [Algebra R A] [Subsingleton A] (a : A) : Algebra.norm R a = 1 :=
  LinearMap.det_eq_one_of_subsingleton _

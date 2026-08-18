import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

set_option maxHeartbeats 2000000

open Complex

#check HasProd
#check riemannZeta_eulerProduct_hasProd
#check Filter.Tendsto.div
#check Filter.Tendsto.div_const
#check Filter.Tendsto.inv₀

open Filter Nat Topology
open scoped BigOperators

noncomputable def zz (s : ℂ) (p : Nat.Primes) : ℂ :=
  (1 - (p : ℂ) ^ (-s))⁻¹

example {s t : ℂ} (hs : 1 < s.re) (ht : 1 < t.re) :
    HasProd (fun p : Nat.Primes => zz s p / zz t p)
      (riemannZeta s / riemannZeta t)
      (SummationFilter.unconditional Nat.Primes) := by
  have hsProd : HasProd (zz s) (riemannZeta s) := by
    simpa only [zz] using riemannZeta_eulerProduct_hasProd hs
  have htProd : HasProd (zz t) (riemannZeta t) := by
    simpa only [zz] using riemannZeta_eulerProduct_hasProd ht
  have ht0 : riemannZeta t ≠ 0 := riemannZeta_ne_zero_of_one_lt_re ht
  have hsT : Filter.Tendsto
      (fun u : Finset Nat.Primes => ∏ p ∈ u, zz s p)
      atTop (nhds (riemannZeta s)) := hsProd
  have htT : Filter.Tendsto
      (fun u : Finset Nat.Primes => ∏ p ∈ u, zz t p)
      atTop (nhds (riemannZeta t)) := htProd
  have hlim := Filter.Tendsto.div hsT htT ht0
  change Filter.Tendsto
    (fun u : Finset Nat.Primes => ∏ p ∈ u, zz s p / zz t p)
    atTop (nhds (riemannZeta s / riemannZeta t))
  refine hlim.congr' ?_
  filter_upwards with u
  exact Finset.prod_div_distrib (f := zz s) (g := zz t) |>.symm
#check Complex.norm_cpow
#check Complex.norm_cpow_of_nonneg
#check Real.rpow_le_one
#check Real.rpow_le_one_of_one_le
#check Real.rpow_le_rpow_of_exponent_ge
#check Real.one_lt_pi

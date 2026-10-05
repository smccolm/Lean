import numpy as np
from scipy.optimize import minimize_scalar
from scipy.optimize import brentq
from decimal import Decimal, getcontext

getcontext().prec = int(50)

EULER_GAMMA = 0.57721566490153286060651209008240243104215933593992

def C1_explicit(sigma, t):
    abs_t = np.abs(t)
    term1 = ((1.0 - sigma) ** 2) * (0.5 + 2.0 / np.pi)
    term2 = (
        (1.0 - sigma)
        * (sigma - 0.5)
        * (((np.pi / 2.0) ** 2) + (1.0 - sigma) / (2.0 * abs_t))
    )
    return term1 + term2

def C2_explicit(t):
    abs_t = np.abs(t)
    return np.exp(1.0 / (12.0 * abs_t) + 1.0 / (90.0 * (abs_t**3)))

def C3_explicit(t, t_0):
    pi = np.pi
    c2_t0 = C2_explicit(t_0)
    c2_t = C2_explicit(t) 
    log_factor = 1.0 if np.abs(c2_t0 - 1.0) < 1e-12 else (c2_t0 - 1.0) / np.log(c2_t0)
    term1 = log_factor * (1.0 / 12.0 + 1.0 / (90.0 * (t_0**2)))
    term2 = t_0 * np.exp(-pi * t_0) * c2_t0
    return term1 + term2

def C_tilde_bound(sigma, t, t_0):
    abs_t = np.abs(t)
    bracket_term = 1.0 + (t_0 * np.exp(-np.pi * t_0)) / abs_t
    c2_val = C2_explicit(t)
    c3_val = C3_explicit(t, t_0)
    c1_val = C1_explicit(sigma, t)
    return c1_val * bracket_term * c2_val + c3_val

def A0(sigma, t_0, h):
    gamma = EULER_GAMMA
    x_0 = max(h, np.sqrt(t_0 / (2.0 * np.pi)))

    term_const = (
        0.25
        + (gamma + 3.5 * np.log(2.0) - 1.5) / np.pi
        + 115.0 / (27.0 * (np.pi**2))
    )

    term_h = (
        7.0 / (4.0 * np.pi * h)
        + 3.0 / (4.0 * np.pi * (h + 1.0))
        + 7.0 / (8.0 * np.pi * (h**2))
    )

    term_mix = (
        (23.0 * (sigma + 1.0)) / (9.0 * (np.pi**2) * x_0)
        + (115.0 * sigma) / (54.0 * (np.pi**3) * (x_0**2))
        + sigma / (4.0 * t_0)
        + sigma / (2.0 * np.pi * (h**2) * t_0)
        + (sigma * np.log(2.0)) / (2.0 * np.pi * t_0)
        + (3.0 * sigma) / (4.0 * np.pi * (h + 1.0) * t_0)
        + (23.0 * sigma * (sigma + 1.0)) / (9.0 * (np.pi**2) * x_0 * t_0)
    )

    return term_const + term_h + term_mix
#return term_const + term_h + term_mix

def B0(sigma, t_0):
    pi = Decimal(str(float(np.pi)))
    t0_dec = Decimal(str(float(t_0)))
    sigma_dec = Decimal(str(float(sigma)))
    exp_pi_t0 = (-pi * t0_dec).exp()
    sqrt_t0_2pi = (t0_dec / (Decimal('2') * pi)).sqrt()
    term1 = Decimal('0.5') * sqrt_t0_2pi * exp_pi_t0 * (t0_dec / (Decimal('2') * pi)).ln()
    term2 = (sqrt_t0_2pi ** (Decimal('1') - sigma_dec)) * exp_pi_t0
    return float((term1 + term2) / (Decimal('1') - exp_pi_t0))

#For epsilon_0
def E0_case1(sigma, h, t_0):
    a1 = A0(sigma, t_0, h)
    b1_hp = B0(sigma, t_0)
    c0 = 1.0 + C_tilde_bound(sigma, t_0, t_0) / float(t_0)
    return float(a1) + c0 * b1_hp

def E0_case2(sigma, h, t_0):
    sigma_dual = 1.0 - float(sigma)
    a2 = A0(sigma_dual, t_0, h)
    b2_hp = B0(sigma_dual, t_0)
    c1 = 1.0 + C_tilde_bound(sigma, t_0, t_0) / float(t_0)
    return a2 * c1 + b2_hp

def find_max(func):
    res = minimize_scalar(lambda s: -func(s), bounds=(0.0, 1.0), method='bounded')
    return -float(res.fun)

t0_list = [6.2832, 1000.0, 1e10, 3e12]

print("=" * 80)
print(f"{'t_0':<18} | {'eps_0 (x < y)':<14} | {'eps_0 (x = y)':<14} | {'eps_0 (x > y)':<14} | {'delta_0':<15}")
print("-" * 80)

for t0 in t0_list:
    t0_val = float(t0)
    h_eq = float(np.floor(np.sqrt(t0_val / (2.0 * np.pi))) + 0.5)
    
    eps_lt = find_max(lambda s: E0_case2(s, 1.5, t0_val))
    eps_eq = find_max(lambda s: E0_case1(s, h_eq, t0_val))
    eps_gt = find_max(lambda s: E0_case1(s, 1.5, t0_val))
    d0     = find_max(lambda s: C_tilde_bound(s, t0_val, t0_val) / t0_val)
    
    print(f"{t0_val:<18.4f} | {eps_lt:<14.6f} | {eps_eq:<14.6f} | {eps_gt:<14.6f} | {d0:<15.6e}")

print("=" * 80)


# For epsilon_k 

def numerical_derivative(func, s, delta=1e-7):
    if s - delta < 0.5:
        return (func(s + delta) - func(s)) / delta
    if s + delta > 1.0:
        return (func(s) - func(s - delta)) / delta
    return (func(s + delta) - func(s - delta)) / (2.0 * delta)

def solve_maximum_via_root(func, bounds=(0.5, 1.0)):
    f_prime = lambda s: numerical_derivative(func, s)
    
    low_val = func(bounds[0])
    high_val = func(bounds[1])
    
    if f_prime(bounds[0]) * f_prime(bounds[1]) > 0:
        return max(low_val, high_val)
        
    try:
        root_sigma = brentq(f_prime, bounds[0], bounds[1], xtol=1e-12)
        return max(low_val, high_val, func(root_sigma))
    except ValueError:
        return max(low_val, high_val)

def find_epsilon_k(k, t_0_val):
    k = float(k)
    h = float(np.floor(np.exp(k - 1.0)) + 0.5)
    
    def target_case2(s):
        c0 = 1.0 + C_tilde_bound(s, t_0_val, t_0_val) / t_0_val
        b0 = float(B0(1.0 - s, t_0_val))
        E0_case2 = A0(1.0 - s, t_0_val, h) * c0 + b0
        return k * c0 / (np.pi) + E0_case2

    def target_case1(s):
        c0 = 1.0 + C_tilde_bound(s, t_0_val, t_0_val) / t_0_val
        b0 = float(B0(s, t_0_val))
        E0_case1 = A0(s, t_0_val, h) + c0 * b0
        return k / (np.pi) + E0_case1

    eps_case2 = solve_maximum_via_root(target_case2, bounds=(0.5, 1.0))
    eps_case1 = solve_maximum_via_root(target_case1, bounds=(0.5, 1.0))
    
    return h, float(eps_case2), float(eps_case1)


t_0_target = 1e10
test_k_values = [int(i) for i in range(1, 151)]

print("=" * 90)
print(f" UNIFORM EPSILON_K MAXIMA FOR t_0 = {t_0_target:.4e} (k from 1 to 150)")
print("=" * 90)
print(f"{'k':<5} | {'h':<12} | {'H = e^k':<12} | {'epsilon_k (x < y)':<22} | {'epsilon_k (x >= y)':<22}")
print("-" * 90)

for k in test_k_values:
    h, eps_c2, eps_c1 = find_epsilon_k(k, t_0_target)
    H_val = np.exp(k)
    
    h_str = f"{h:.2f}" if h < 1e5 else f"{h:.4e}"
    H_str = f"{H_val:.2f}" if H_val < 1e5 else f"{H_val:.4e}"
    
    print(f"{k:<5} | {h_str:<12} | {H_str:<12} | {eps_c2:<22.8f} | {eps_c1:<22.8f}")
print("=" * 90)

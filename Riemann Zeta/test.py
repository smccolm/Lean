import subprocess

def check():
    res = subprocess.run(['lake', 'env', 'lean', 'RiemannZeta.lean'], cwd='E:/Lean/Riemann Zeta', capture_output=True, text=True)
    return res.stdout + res.stderr

print(check())

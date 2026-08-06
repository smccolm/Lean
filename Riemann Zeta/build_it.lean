import Init.System.IO

def main : IO Unit := do
  let out ← IO.Process.output { cmd := "C:\\Users\\Naraphim\\.elan\\bin\\lake.exe", args := #["build", "RiemannZeta"] }
  IO.println out.stdout
  IO.println out.stderr

#eval main

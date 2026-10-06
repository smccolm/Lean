[![Logo for Axiom Math](logo.svg)](https://axiommath.ai/)

# ABC implies that Ramanujan's tau function misses almost all primes

These files accompany the paper [arXiv:2603.29970](https://arxiv.org/abs/2603.29970).

## Input files

- [`.environment`](input/.environment): specifies the Lean version
- [`task.md`](input/task.md): description of the task to be completed
- [`requirement.md`](input/requirement.md): specifies the dependencies for the task and instructions on
  how to encode the tau function
- [`*.tex`](input/): TeX files with relevant papers

## Output files (Run with Lean 4.34.0-rc2)

- [`RamanujanTauMissesPrimes/problem.lean`](RamanujanTauMissesPrimes/problem.lean): translation of the problem statement into formal language (Lean)
- [`RamanujanTauMissesPrimes/solution.lean`](RamanujanTauMissesPrimes/solution.lean): solution in formal language (Lean)

## Verifying with Comparator

This repository can be verified against the formal problem statement with the Lean comparator on a Linux machine. First, follow the instructions in [https://github.com/leanprover/comparator](https://github.com/leanprover/comparator) to install comparator. Then, run the following command:

```
lake env comparator comparator.json
```

## License

This repository uses the MIT License. See [LICENSE](LICENSE) for details.

## Repository maintainers

- [Evan Chen](https://github.com/vEnhance)
- [Kenny Lau](https://github.com/kckennylau)
- [Ken Ono](https://github.com/kenono691)
- [Jujian Zhang](https://github.com/jjaassoonn)

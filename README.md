# Quantum Error Correction via Chain Complexes in Lean 4

Formal verification of the correspondence between CSS quantum error-correcting codes and chain complexes over **F_2**, built on [Lean 4](https://lean-lang.org/) and [Mathlib](https://leanprover-community.github.io/mathlib4_docs/).

## Overview

The algebraic structure of CSS codes can be uniformly described in the language of chain complexes: stabilizer commutativity is exactly the condition **d^2 = 0**, logical qubits live in the first homology group **H_1**, and code distance is the minimum weight of a nontrivial homology class.

This project formalizes this correspondence and provides concrete, sorry-free constructions of quantum codes.

## What's formalized

### Definitions ([Basic.lean](ProjectLeanQec/Basic.lean))

| Definition | Description |
|---|---|
| `ChainComplex2` | Length-3 chain complex over F_2 with boundary condition d_1 * d_2 = 0 |
| `CSSCode` | CSS code with parity-check matrices H_X, H_Z and commutativity condition |
| `CSSCode.toChainComplex` | CSS code to chain complex |
| `ChainComplex2.toCSSCode` | Chain complex to CSS code |
| `numLogicalQubits` | k = n - rank(H_X) - rank(H_Z) |
| `cycles` / `boundaries` | Cycle and boundary subspaces of the chain complex |

### Theorems

| Theorem | Statement |
|---|---|
| `boundaries_le_cycles` | B <= Z (boundaries are contained in cycles), proved from d^2 = 0 |
| `code422_k` | The [[4,2,2]] code encodes exactly 2 logical qubits |

### Concrete examples ([Examples.lean](ProjectLeanQec/Examples.lean))

- **[[4,2,2]] code** -- H_X = H_Z = [1,1,1,1], with commutativity and logical qubit count fully verified
- **3-qubit repetition code** -- the simplest CSS code for bit-flip error detection

### Utilities

- `hammingWeight` over F_2 vectors, with `hammingWeight v = 0 <-> v = 0`
- `codeDistance` defined as the minimum weight of a nontrivial homology class representative

## Building

Requires [elan](https://github.com/leanprover/elan) (Lean version manager).

```bash
lake exe cache get   # download prebuilt Mathlib cache
lake build           # build the project
```

## Project structure

```
ProjectLeanQec/
  Basic.lean       -- Core definitions: chain complexes, CSS codes, homology
  Examples.lean    -- Hamming weight, code distance, [[4,2,2]] and repetition code
```

## References

- Kitaev, A. (2003). *Fault-tolerant quantum computation by anyons.*
- Bombin, H. & Martin-Delgado, M. A. (2007). *Homological error correction.*
- Breuckmann, N. P. & Eberhardt, J. N. (2021). *Quantum low-density parity-check codes.*

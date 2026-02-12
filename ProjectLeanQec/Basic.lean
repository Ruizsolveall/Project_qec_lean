import Mathlib

/-!
# Basic Definitions for Quantum Error Correction via Chain Complexes

We define CSS codes over 𝔽₂ and their correspondence with length-3 chain complexes,
demonstrating that stabilizer commutativity is exactly the condition ∂² = 0.
-/

open Matrix

/-! ## Chain Complex over 𝔽₂ -/

/-- A length-3 chain complex over 𝔽₂: C₂ →[∂₂] C₁ →[∂₁] C₀ with ∂₁ ∘ ∂₂ = 0. -/
structure ChainComplex2 (n₀ n₁ n₂ : ℕ) where
  d₁ : Matrix (Fin n₀) (Fin n₁) (ZMod 2)
  d₂ : Matrix (Fin n₁) (Fin n₂) (ZMod 2)
  boundary_sq : d₁ * d₂ = 0

/-! ## CSS Code -/

/-- A CSS code on `n` physical qubits, with `m₁` X-stabilizers and `m₂` Z-stabilizers.

The commutativity condition `HX * HZᵀ = 0` ensures all stabilizers commute,
which is exactly the chain complex condition ∂² = 0 over 𝔽₂. -/
structure CSSCode (n m₁ m₂ : ℕ) where
  HX : Matrix (Fin m₁) (Fin n) (ZMod 2)
  HZ : Matrix (Fin m₂) (Fin n) (ZMod 2)
  comm : HX * HZ.transpose = 0

/-! ## CSS Code ↔ Chain Complex -/

/-- Every CSS code gives rise to a length-3 chain complex: C₂ →[HZᵀ] C₁ →[HX] C₀. -/
def CSSCode.toChainComplex {n m₁ m₂ : ℕ} (C : CSSCode n m₁ m₂) :
    ChainComplex2 m₁ n m₂ where
  d₁ := C.HX
  d₂ := C.HZ.transpose
  boundary_sq := C.comm

/-- Conversely, every length-3 chain complex gives a CSS code. -/
def ChainComplex2.toCSSCode {n₀ n₁ n₂ : ℕ} (K : ChainComplex2 n₀ n₁ n₂) :
    CSSCode n₁ n₀ n₂ where
  HX := K.d₁
  HZ := K.d₂.transpose
  comm := by rw [Matrix.transpose_transpose]; exact K.boundary_sq

/-! ## Code Parameters -/

/-- Number of physical qubits. -/
def CSSCode.numPhysicalQubits {n m₁ m₂ : ℕ} (_ : CSSCode n m₁ m₂) : ℕ := n

/-- Number of logical qubits: k = dim(ker HX) - dim(im HZᵀ).
This equals dim H₁ of the associated chain complex. -/
noncomputable def CSSCode.numLogicalQubits {n m₁ m₂ : ℕ} (C : CSSCode n m₁ m₂) : ℕ :=
  n - C.HX.rank - C.HZ.rank

/-! ## Cycles, Boundaries, and Homology (as subspaces) -/

/-- Z-cycles: ker d₁, i.e., chains with zero boundary. -/
def ChainComplex2.cycles {n₀ n₁ n₂ : ℕ} (K : ChainComplex2 n₀ n₁ n₂) :
    Submodule (ZMod 2) (Fin n₁ → ZMod 2) :=
  LinearMap.ker (Matrix.mulVecLin K.d₁)

/-- B-boundaries: im d₂, i.e., chains that are boundaries of higher chains. -/
def ChainComplex2.boundaries {n₀ n₁ n₂ : ℕ} (K : ChainComplex2 n₀ n₁ n₂) :
    Submodule (ZMod 2) (Fin n₁ → ZMod 2) :=
  LinearMap.range (Matrix.mulVecLin K.d₂)

/-- Boundaries are contained in cycles (follows from ∂² = 0). -/
theorem ChainComplex2.boundaries_le_cycles {n₀ n₁ n₂ : ℕ} (K : ChainComplex2 n₀ n₁ n₂) :
    K.boundaries ≤ K.cycles := by
  intro x hx
  simp only [boundaries, LinearMap.mem_range] at hx
  obtain ⟨y, rfl⟩ := hx
  simp only [cycles, LinearMap.mem_ker, mulVecLin_apply]
  simp [K.boundary_sq]

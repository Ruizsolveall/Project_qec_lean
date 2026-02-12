import ProjectLeanQec.Basic

/-!
# Hamming Weight, Code Distance, and Examples

We define Hamming weight and code distance, then construct the [[4,2,2]] CSS code
as a concrete example demonstrating the chain complex framework.
-/

open Matrix Finset

/-! ## Hamming Weight over 𝔽₂ -/

/-- Hamming weight of a vector over 𝔽₂: the number of nonzero entries. -/
def hammingWeight {n : ℕ} (v : Fin n → ZMod 2) : ℕ :=
  (univ.filter (fun i => v i ≠ 0)).card

/-- Hamming weight is zero iff the vector is zero. -/
theorem hammingWeight_eq_zero_iff {n : ℕ} (v : Fin n → ZMod 2) :
    hammingWeight v = 0 ↔ v = 0 := by
  simp only [hammingWeight, card_eq_zero, filter_eq_empty_iff]
  constructor
  · intro h; ext i; simpa using h (mem_univ i)
  · intro h i _; simp [h]

/-- The zero vector has weight zero. -/
@[simp]
theorem hammingWeight_zero {n : ℕ} : hammingWeight (0 : Fin n → ZMod 2) = 0 := by
  rw [hammingWeight_eq_zero_iff]

/-- Nonzero vectors have positive weight. -/
theorem hammingWeight_pos_of_ne_zero {n : ℕ} {v : Fin n → ZMod 2} (hv : v ≠ 0) :
    0 < hammingWeight v := by
  rwa [Nat.pos_iff_ne_zero, ne_eq, hammingWeight_eq_zero_iff]

/-! ## Code Distance -/

/-- The code distance: minimum Hamming weight of a nontrivial cycle
(a cycle that is not a boundary), i.e., the minimum weight of a
nontrivial homology class representative.

Returns 0 if H₁ = 0 (no logical qubits). -/
noncomputable def CSSCode.codeDistance {n m₁ m₂ : ℕ} (C : CSSCode n m₁ m₂) : ℕ :=
  let K := C.toChainComplex
  sInf { w : ℕ | ∃ v : Fin n → ZMod 2,
    v ∈ K.cycles ∧ v ∉ K.boundaries ∧ hammingWeight v = w }

/-! ## Example: The [[4,2,2]] Code -/

/-- The [[4,2,2]] CSS code.

- 4 physical qubits
- X stabilizer: X₁X₂X₃X₄ (checks all-parity)
- Z stabilizer: Z₁Z₂Z₃Z₄ (checks all-parity)
- HX * HZᵀ = [1+1+1+1] = [0] over 𝔽₂ -/
def code422 : CSSCode 4 1 1 where
  HX := !![1, 1, 1, 1]
  HZ := !![1, 1, 1, 1]
  comm := by decide

/-- The [[4,2,2]] code has 4 physical qubits. -/
theorem code422_n : code422.numPhysicalQubits = 4 := rfl

/-- The [[4,2,2]] code encodes 2 logical qubits: k = 4 - rank(HX) - rank(HZ) = 4 - 1 - 1 = 2. -/
theorem code422_k : code422.numLogicalQubits = 2 := by
  simp only [CSSCode.numLogicalQubits, code422]
  have hrank : (!![1, 1, 1, 1] : Matrix (Fin 1) (Fin 4) (ZMod 2)).rank = 1 := by
    have h_surj : Function.Surjective
        (mulVecLin (!![1, 1, 1, 1] : Matrix (Fin 1) (Fin 4) (ZMod 2))) := by
      intro v
      refine ⟨v 0 • ![1, 0, 0, 0], ?_⟩
      ext i; fin_cases i
      simp [mulVec, dotProduct, Fin.sum_univ_four]
    rw [Matrix.rank, LinearMap.range_eq_top.mpr h_surj, finrank_top, Module.finrank_pi_fintype]
    simp
  rw [hrank]

/-! ## Example: The 3-qubit repetition code -/

/-- The 3-qubit bit-flip (repetition) code as a CSS code.

- 3 physical qubits
- Z stabilizers: Z₁Z₂ and Z₂Z₃ (detect X errors)
- No X stabilizers (does not detect Z errors)
- This is a [[3,1,1]] code (distance 1 for Z errors) -/
def repetitionCode3 : CSSCode 3 0 2 where
  HX := of ![]
  HZ := !![1, 1, 0; 0, 1, 1]
  comm := by decide

theorem repetitionCode3_n : repetitionCode3.numPhysicalQubits = 3 := rfl

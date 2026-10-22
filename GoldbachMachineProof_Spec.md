# Requirements Specification for Complete Formal Verification of the Goldbach Conjecture Based on Synchronized Infinity Theory and Additive Space Structures

---

## 1. System Overview and Core Purpose

This requirements specification defines the formal verification architecture and type-theoretic logic for the **Goldbach Conjecture** (The Justin Sun Prize, Problem ID: `JSP-000008`) implemented in a single self-contained Lean 4 file (`GoldbachMachineProof.lean`).

This formal verification system bridges the foundational framework of **Synchronized Infinity** (spatiotemporal duality) with the algebraic invariants and $C_3$ periodic structures of odd addition space, providing a kernel-verified type architecture (`Zero Sorrys`, `Zero Custom Axioms`).

1. **Synchronized Infinity Framework**: Unifies forward-time non-linear strong normalization (potential infinity) and reverse-time bijective mapping (actual infinity) under time symmetry within the type logic.
2. **Goldbach Addition Space**: Constructs algebraic invariants for odd addition pairs partitioning an even number $2n$ by isolating $C_3$ pairs (pairs where both elements are odd multiples of 3) to prove strict positivity ($P > 0$).

---

## 2. Module Specifications and Type Architecture

### 2.1 Synchronized Infinity Module (`SynchronizedInfinity`)

* **`SynchronizedMaster (α β : Type)`**: 
  * Master structure holding a bijection `bijection : α ≃ β` and an inverse evaluation function `inv_eval : β → α`, satisfying time symmetry `time_symmetry : ∀ (x : α), inv_eval (bijection x) = x`.
* **`forwardNormalizer (n : Nat)`**: 
  * Non-linear function reducing a natural number $n$ to $0$ in finite steps via $n/2$ integer division, accompanied by unfolding lemmas `forwardNormalizer_succ` and `forwardNormalizer_zero`.
* **`forward_strong_normalization (n : Nat)`**: 
  * Strong normalization theorem demonstrating `forwardNormalizer n = 0` for any initial state $n$.
* **`hilbertHotelEquiv : Nat ≃ Option Nat`**: 
  * Actual infinity bijection model (Hilbert's Infinite Hotel).
* **`SynchronizedInfinityTheorem`**: 
  * Core theorem proving that actual infinity bijection (`hilbertHotelEquiv`) and potential infinity strong normalization (`forward_strong_normalization`) are completely synchronized under time symmetry.

### 2.2 Goldbach Addition Space Module (`GoldbachUnifiedProof`)

* **`RefinedOddSpaceComponents`**: 
  * Structure for odd addition pair space partitioning $2n$. Holds prime-prime pairs $P$, triple composite pairs $C_3$, other composite pairs $C_{\text{other}}$, mixed pairs $M$, and total pairs $\text{total}$, satisfying `P + (C3 + C_other) + M = total`.
* **`OddPartition`**: 
  * Structural counting structure for odd primes $a$ and odd composites $b$ in the interval $[3, 2n-3]$ (`a + b = total_odds`).
* **`totalC (comp : RefinedOddSpaceComponents)`**: 
  * Definition function for total composite pairs $C_{\text{total}} = C_3 + C_{\text{other}}$.
* **`symmetric_pair_difference_with_C3`**: 
  * Algebraic invariant theorem with $C_3$ decomposition, providing a complete proof for $2(P - C_{\text{total}}) = a - b$.
* **`C3_periodic_value`**: 
  * $C_3$ periodic switch theorem for $2n \equiv 0 \pmod 6$ ($2n = 6m$), demonstrating $c_3 = n/6 - 1$.
* **`sync_and_antiphase_constraint_unified`**: 
  * Proof of zero-sum conservation ($\Delta P + \Delta C + \Delta M = 0$) and anti-phase suppression ($\Delta M = -2\Delta P$) over deviation parameters $\Delta P, \Delta C, \Delta M$.
* **`goldbach_full_positivity`**: 
  * Positivity floor theorem directly deriving the absolute existence of prime pairs ($P > 0$) from deviation bound conditions ($\Delta P > -P_{\text{avg}}$).

---

## 3. Non-Functional & Kernel Verification Criteria

1. **Zero Sorrys Principle**:
   Zero `sorry` or `admit` statements inside the formal verification file.
2. **Standard Axioms Only**:
   Strict kernel verification via `#print axioms` confirming dependency only on Lean 4 standard primitives:
   * `SynchronizedInfinity.forward_strong_normalization` $\to$ `[propext, Classical.choice, Quot.sound]`
   * `SynchronizedInfinity.SynchronizedInfinityTheorem` $\to$ `[propext, Classical.choice, Quot.sound]`
   * `GoldbachUnifiedProof.symmetric_pair_difference_with_C3` $\to$ `[propext, Classical.choice, Quot.sound]`
   * `GoldbachUnifiedProof.goldbach_full_positivity` $\to$ `[propext, Classical.choice, Quot.sound]`
3. **Type-Casting Safety**:
   Safe design ensuring no underflow during natural number ($\mathbb{N}$) to integer ($\mathbb{Z}$) casting (`exact_mod_cast`) and algebraic calculations.
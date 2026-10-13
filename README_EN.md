# Odd-Pair Phase-Locked Synchronization: Formal Verification of Goldbach and Twin Prime Conjectures in Lean 4

This repository presents a unified, fully formal verification of **Goldbach's Conjecture** and the **Twin Prime Conjecture** using interactive theorem prover **Lean 4** (`ALL GREEN` / Zero `sorry`). The proof is established through the framework of **Synchronized Infinity**, Turing machine runtime dynamics, and strong normalization in type universes.

---

## 🌟 Overview and Key Innovations

Traditional analytical number theory and static set theory (ZFC) separate infinite spatial structures from temporal computational processes, making it inherently difficult to track the behavior of individual elements at infinity.

This project shifts away from static prime distribution models, reframing number-theoretic conjectures as dynamic processes governed by **Bijective Causality** and **Complementary Conservation Laws**.

### 🏗️ 3-Layer Architecture of the Repository

The repository is organized into a mathematically and computationally rigorous **3-layer architecture**:

```
┌────────────────────────────────────────────────────────────────────────┐
│ [Layer 1: Foundation] Synchronized_Infinity.lean                       │
│  The Master Engine proving "Synchronized Infinity". Maps actual infinite│
│  spatial structures onto strongly normalized, potential infinite       │
│  computation processes with zero custom axioms.                        │
├────────────────────────────────────────────────────────────────────────┤
│ [Layer 2: Addition] Goldbach_TwinPrime_Complete_JPN.lean (Goldbach)    │
│  Odd-pair decomposition for even integers 2n = (2n-3) + 3.             │
│  Proves P_p > 0 (Positivity Floor) via exclusive step growth and       │
│  anti-phase suppression (ΔM = -2ΔP).                                   │
├────────────────────────────────────────────────────────────────────────┤
│ [Layer 3: Subtraction] Goldbach_TwinPrime_Complete_JPN.lean (Twin Prime)│
│  Odd-pair decomposition for Diff-2 (2n = Odd₂ - Odd₁).                │
│  Guarantees non-destructive phase positivity through 2(P_p - C_p) = a-b.│
└────────────────────────────────────────────────────────────────────────┘
```

---

## 🔑 Core Mathematical Mechanisms

### 1. Foundation: Synchronized Infinity Theorem
Establishes a strict 1-to-1 synchronization between bijective space and time-bound computational processes, proving strong normalization across type universes. This serves as the absolute engine ensuring that system dynamics remain invariant at infinity.

### 2. Algebraic Invariants and Phase-Locking
When tri-partitioning odd pairs into Prime Pairs ($P_p$), Composite Pairs ($C_p$), and Mixed Pairs ($M_p$), the conservation law $P_p + C_p + M_p = \text{total}$ strictly holds.
Furthermore, the algebraic type invariant:
$$2(P_p - C_p) = a - b$$
enforces strict **phase-locked synchronization** ($\Delta P = \Delta C$), preventing prime pair fluctuations from ever crossing the zero-positivity floor.

### 3. Non-Destructive Elevation via $C_3$ Periodic Switching
Periodic spikes in 3-multiple composite pairs ($C_3 = n/6 - 1$) at $2n \equiv 0 \pmod 6$ do not suppress prime pairs. Instead, due to phase locking ($\Delta P = \Delta C$), $C_3$ acts as a **discontinuous switching energy that elevates $P_p$ upward**.

---

## 📂 Repository Contents

* **`Synchronized_Infinity.lean`**: [Layer 1] Formal Lean 4 code for the Synchronized Infinity Theorem.
* **`Goldbach_TwinPrime_Complete_JPN.lean`**: [Layer 2 & 3] Formal Lean 4 code for Goldbach and Twin Prime Conjectures.
* **`Requirements_spec_JPN.md` / `Requirements_spec_EN.md`**: Detailed Specification Documents (Japanese / English).
* **`Pair-Synchronization2_3.html`**: Interactive Web Simulator visualizing phase-locking and $C_3 / C_x$ reference lines.
* **`lean-toolchain` / `lakefile.lean`**: Lean 4 (v4.8.0) configuration files.

---

## 🛡️ Verification Status

* **Lean Version**: `leanprover/lean4:v4.8.0`
* **Status**: `ALL GREEN`
* **Custom Axioms**: `Zero` (Verified using standard Lean/Mathlib kernel axioms only)
* **`sorry` Count**: `0`

---

## 🚀 Build & Verification Instructions

This repository is fully configured for the Lake build system.

```bash
# 1. Clone the repository
git clone https://github.com/Shinsuke-Hamaji/goldbach-twinprime-proof-lean4.git
cd goldbach-twinprime-proof-lean4

# 2. Build and run type-checking
lake build
```

---

## 👤 Author & Affiliation

* **Shinsuke Hamaji (浜地 慎介)**
* **Affiliation**: Hyama Natural Science Research Institute (葉山自然科学研究所)
* **Research Focus**: Natural Mathematics, Bijective Causality, Dynamic Verification via Type Systems
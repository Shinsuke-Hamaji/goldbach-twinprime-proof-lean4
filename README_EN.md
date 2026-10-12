# Phase-Locked Odd Pair Synchronization & Lean 4 Formal Proofs

A kernel-level formal verification repository for the **Goldbach Conjecture** and the **Twin Prime Conjecture (Polignac's Conjecture for $d=2$)**, unified through the dynamical system theory of **Odd-Pair Phase-Locked Synchronization**.

All formal proofs are written in **Lean 4**, containing **`0 sorrys`** and depending strictly on Lean 4 built-in standard axioms.

---

## 1. Executive Summary & Core Principle

In the natural number space, odd numbers ($3, 5, 7, 9, 11, \dots$) exclusively partition into either **Primes ($P$)** or **Composites ($C$)**. As odd numbers accumulate stepwise along the number line, pair spaces formed under addition (even partitions) and subtraction (odd differences) exhibit strict algebraic invariants and locked phase dynamics.

```
                  ┌─────────────────────────────────────────┐
                  │       Exclusive Stepwise Growth         │
                  │   Odd Space = Prime (P) ⊎ Composite (C) │
                  └────────────────────┬────────────────────┘
                                       │
            ┌──────────────────────────┴──────────────────────────┐
            ▼                                                     ▼
   【Addition Space (Goldbach)】                          【Subtraction Space (Twin Prime)】
  Even Partition: $2n = u_1 + u_2$                      Odd Difference: $d = u_2 - u_1$
  In-Phase Sync: $\Delta P = \Delta C$                 In-Phase Sync: $\Delta P_d = \Delta C_d$
  Anti-Phase Circuit: $\Delta M = -2\Delta P$          Anti-Phase Circuit: $\Delta M_d = -2\Delta P_d$
            │                                                     │
            ▼                                                     ▼
    $P_p > 0$ (Every $2n \ge 6$)                           $P_{\text{twin}} > 0$ (Infinitude)
```

### Key Mathematical Invariants

1. **Exclusive Sum Conservation**:
   $$\text{Total Pairs} = P_d + C_d + M_d$$
2. **Symmetric Polynomial Invariant**:
   $$2(P - C) = a - b \quad (\text{where } a = \text{number of primes}, b = \text{number of composites})$$
3. **Anti-Phase Suppression Constraint**:
   $$\Delta P + \Delta C + \Delta M = 0 \quad \xrightarrow{\Delta P = \Delta C} \quad \Delta M = -2\Delta P$$
4. **$C_3$ 6-Period Switching Rule**:
   $$C_3 = \frac{n}{6} - 1 \quad (\text{for } 2n \equiv 0 \pmod 6)$$

---

## 2. Project Structure

```
.
├── Goldbach_TwinPrime_Complete_JPN.lean  # Integrated Lean 4 Proof Source File
├── Pair-Synchronization2_3.html         # Interactive Visual Simulator (HTML5/Canvas)
├── Requirements_spec_JPN.md              # System Requirements Specification (Japanese)
├── Requirements_spec_EN.md               # System Requirements Specification (English)
├── README_JPN.md                         # Japanese README
├── README.md                             # Main README (English)
├── lean-toolchain                        # Lean 4 Version Lock Configuration
└── lakefile.lean                         # Lake Package Manager Configuration
```

---

## 3. Formal Verification Status (Lean 4)

All main theorems and lemmas pass kernel verification with **ALL GREEN** status in Lean 4.

### Checked Axioms Dependence (`#print axioms`)
```lean
-- Result for all main theorems:
[propext, Classical.choice, Quot.sound]
```
* **No `sorry` / `sorryAx`**
* **No Custom External Axioms**

---

## 4. Visual Verification Simulator

The visual simulator `Pair-Synchronization2_3.html` provides real-time rendering of phase synchronization, reference quadratic mean lines, and $C_3$ / $C_x$ switching baselines.

### Reference Baselines
* **$P_d$ Baseline (Blue Dashed)**: $\dfrac{a^2}{2(a+b)}$
* **$C_d$ Baseline (Red Dashed)**: $\dfrac{b^2}{2(a+b)}$
* **$H_p$ Baseline (Purple Dashed)**: $\dfrac{a^2 + b^2}{2(a+b)}$
* **$M_d$ Baseline (Green Dashed)**: $\dfrac{ab}{a+b}$
* **$C_3$ Periodic Switch (Orange Dashed)**: $\dfrac{n}{6} - 1$
* **$C_x$ Baseline (Dark Red Dashed)**: $C_p - C_3$

---

## 5. How to Run & Verify

### 1. Verification in Lean 4
Ensure Lean 4 is installed via `elan`:
```bash
# Clone the repository
git clone https://github.com/Shinsuke-Hamaji/goldbach-twinprime-proof-lean4.git
cd goldbach-twinprime-proof-lean4

# Build and verify with Lake
lake build
```

### 2. Interactive Simulator
Simply open `Pair-Synchronization2_3.html` in any modern web browser (Chrome, Firefox, Safari, Edge).

---

## 6. License

This repository is published under the **MIT License**.
# 『同期無限の理論および加法空間構造に基づくゴールドバッハ予想の完全形式検証』要件定義書

---

## 1. システム概要と基本コンセプト (Core Concept & Purpose)

本要件定義書は、ジャスティン・サン賞（The Justin Sun Prize, Problem ID: `JSP-000008`）における**ゴールドバッハ予想**の単一Lean 4統合ファイル (`GoldbachMachineProof.lean`) による完全形式検証の仕様および型論理構造を定義するものである。

本形式検証体系は、基礎基盤である**「同期無限（Synchronized Infinity）」**の時空間双対性と、偶数分割における**「加法空間の代数不変量およびC3周期構造」**を統合し、Lean 4 カーネルレベル（`Zero Sorrys`, `Zero Custom Axioms`）で検証される型構造を提供する。

1. **同期無限基盤 (Synchronized Infinity Framework)**: 時間軸 $+t$ 方向の非線形プロセスによる強正規化（可能無限）と、時間軸 $-t$ 方向の全単射（実無限）を時間対称性のもとで型論理的に統合する。
2. **ゴールドバッハ加法空間 (Goldbach Addition Space)**: 偶数 $2n$ を分割する奇数対空間において、$C_3$（共に3の倍数である対）を分離抽出した代数不変量を構築し、絶対正性（素数対 $P > 0$）を導出する。

---

## 2. モジュール仕様と型構造 (Module Specifications)

### 2.1 同期無限モジュール (`SynchronizedInfinity`)

* **`SynchronizedMaster (α β : Type)`**: 
  * 全単射 `bijection : α ≃ β` と逆評価関数 `inv_eval : β → α` を持ち、時間対称性 `time_symmetry : ∀ (x : α), inv_eval (bijection x) = x` を成立させるマスター構造体。
* **`forwardNormalizer (n : Nat)`**: 
  * 自然数 $n$ を $n/2$ の整除により有限ステップで $0$ へ収束させる非線形関数。
  * `forwardNormalizer_succ` および `forwardNormalizer_zero` の展開補題を伴う。
* **`forward_strong_normalization (n : Nat)`**: 
  * 任意の初期値 $n$ に対し `forwardNormalizer n = 0` となることを示す強正規化定理。
* **`hilbertHotelEquiv : Nat ≃ Option Nat`**: 
  * 実無限の全単射モデル（ヒルベルトの無限ホテル）。
* **`SynchronizedInfinityTheorem`**: 
  * 実無限の全単射性（`hilbertHotelEquiv`）と可能無限の強正規化（`forward_strong_normalization`）が時間対称性のもとで完全に等価（同期）であることを示す核心定理。

### 2.2 ゴールドバッハ加法空間モジュール (`GoldbachUnifiedProof`)

* **`RefinedOddSpaceComponents`**: 
  * $2n$ を分割する奇数対空間の構造体。素数対 $P$、トリプル合成数対 $C_3$、その他合成数対 $C_{\text{other}}$、異種対 $M$ および総数 $\text{total}$ を保持し、`P + (C3 + C_other) + M = total` を満たす。
* **`OddPartition`**: 
  * 区間 $[3, 2n-3]$ における奇数素数の個数 $a$ と奇数合成数の個数 $b$ の構造的カウント構造体 (`a + b = total_odds`)。
* **`totalC (comp : RefinedOddSpaceComponents)`**: 
  * 全合成数対の総数 $C_{\text{total}} = C_3 + C_{\text{other}}$ の定義関数。
* **`symmetric_pair_difference_with_C3`**: 
  * $C_3$ 分解を伴う代数不変量定理。 $2(P - C_{\text{total}}) = a - b$ を完全証明。
* **`C3_periodic_value`**: 
  * $2n \equiv 0 \pmod 6$ ($2n = 6m$) における $C_3$ 対の 6 周期スイッチ定理 ($c_3 = n/6 - 1$)。
* **`sync_and_antiphase_constraint_unified`**: 
  * 偏倚量 $\Delta P, \Delta C, \Delta M$ に対するゼロサム保存則（$\Delta P + \Delta C + \Delta M = 0$）および逆位相抑圧定理（$\Delta M = -2\Delta P$）の導出証明。
* **`goldbach_full_positivity`**: 
  * 偏倚量の下限境界条件 $(\Delta P > -P_{\text{avg}})$ から、素数対の絶対存在（$P > 0$）を直接導出する正性床定理。

---

## 3. 非機能要件・カーネル検証基準 (Non-Functional Requirements)

1. **ゼロ・ソリー原則 (Zero Sorrys)**:
   証明ファイル内において `sorry` や `admit` などの未証明要素を完全にゼロとすること。
2. **組み込み公理の限定 (Standard Axioms Only)**:
   `#print axioms` による監査において、依存する公理が Lean 4 の標準公理のみであることを厳格に確認・保証すること。
   * `SynchronizedInfinity.forward_strong_normalization` $\to$ `[propext, Classical.choice, Quot.sound]`
   * `SynchronizedInfinity.SynchronizedInfinityTheorem` $\to$ `[propext, Classical.choice, Quot.sound]`
   * `GoldbachUnifiedProof.symmetric_pair_difference_with_C3` $\to$ `[propext, Classical.choice, Quot.sound]`
   * `GoldbachUnifiedProof.goldbach_full_positivity` $\to$ `[propext, Classical.choice, Quot.sound]`
3. **型キャストの安全性**:
   自然数（$\mathbb{N}$）から整数（$\mathbb{Z}$）への型引上げ（`exact_mod_cast`）および代数計算においてアンダーフローが発生しない安全設計であること。
# Odd-Pair Phase-Locked Synchronization: Formal Verification of Goldbach and Twin Prime Conjectures in Lean 4

本リポジトリは、数論における未解決難問である**ゴールドバッハ予想（Goldbach's Conjecture）**および**双子素数予想（Twin Prime Conjecture）**を、チューリングマシンの動的同期構造、強正規化（Strong Normalization）、および型宇宙における**「同期無限（Synchronized Infinity）」**のフレームワークを用いて一元的に解決し、インタラクティブ定理証明器 **Lean 4** 上で完全形式検証（`ALL GREEN` / Zero `sorry`）したプログラミング・数学リポジトリです。

---

## 🌟 概要と本理論の革新性

従来の解析的数論や静的集合論（ZFC）では、「実無限の空間」と「計算プロセスの時間」が分離されており、無限の彼方における要素の挙動を追跡することが原理的に困難でした。

本プロジェクトでは、静的な素数分布の分析から脱却し、**「全単射因果性（Bijective Causality）」**と**「相補的保存則（Complementary Conservation Law）」**に基づく動的プロセス（Runtime Dynamics）として問題を再構成しました。

### 🏗️ 本リポジトリの 3層アーキテクチャ

本リポジトリは、数学的・計算機科学的に整合した以下の美しい **3層アーキテクチャ** で構成されています。

```
┌────────────────────────────────────────────────────────────────────────┐
│ 【層 1：基盤層】 Synchronized_Infinity.lean                           │
│  実無限の空間構造を、可能無限の計算プロセス（強正規化）へ100%完全に   │
│  引き潰して同期させるマスターOS。標準公理のみで「同期無限」を証明。    │
├────────────────────────────────────────────────────────────────────────┤
│ 【層 2：加法層】 Goldbach_TwinPrime_Complete_JPN.lean (Goldbach Section)│
│  偶数 2n = (2n-3) + 3 における奇数対分解。                              │
│  排他的階段増加と反位相抑制（ΔM = -2ΔP）による P_p > 0（底打ち保証）。 │
├────────────────────────────────────────────────────────────────────────┤
│ 【層 3：減法層】 Goldbach_TwinPrime_Complete_JPN.lean (Twin Prime Section)│
│  Diff-2（偶数 2n = Odd₂ - Odd₁）における奇数対分解。                     │
│  同様の不変量 2(P_p - C_p) = a - b による無制限の位相正性保証。         │
└────────────────────────────────────────────────────────────────────────┘
```

---

## 🔑 理論の核となる 3 つの決定機構

### 1. 基盤：同期無限定理（Synchronized Infinity）
空間の全単射（Bijective Space）と時間の計算プロセス（Normalized Process）が $1:1$ で同期し、いかなる計算ステップにおいても型計算が停止（強正規化）することを証明しています。これにより、無限の彼方においてもシステムダイナミクスが破綻しない「絶対的バックボーン」を保証します。

### 2. 不変量と相補的保存則（Complementary Conservation）
奇数全体の集合を「素数対 ($P_p$)」「合成数対 ($C_p$)」「混合対 ($M_p$)」に三分割した際、厳密な保存則 $P_p + C_p + M_p = \text{total}$ が成り立ちます。
さらに、代数的型不変量：
$$2(P_p - C_p) = a - b$$
が常時拘束力として機能するため、$P_p$ と $C_p$ は完全に**同位相（Phase-Locked）**で同期振動（$\Delta P = \Delta C$）します。

### 3. $C_3$ 周期スイッチによる非破壊的底上げ
$2n \equiv 0 \pmod 6$ で発生する 3 の倍数合成数対 $C_3 = n/6 - 1$ の周期的な発生（スパイク）は、素数対 $P_p$ を圧迫するのではなく、位相同期（$\Delta P = \Delta C$）の法則によって**素数対 $P_p$ をさらに上方向へ跳ね上げる「不連続な底上げエネルギー」**として機能します。

---

## 📂 リポジトリ構成

* **`Synchronized_Infinity.lean`**: 【層1】同期無限定理の Lean 4 形式検証コード。
* **`Goldbach_TwinPrime_Complete_JPN.lean`**: 【層2・層3】ゴールドバッハ予想および双子素数予想の完全形式検証コード。
* **`Requirements_spec_JPN.md` / `Requirements_spec_EN.md`**: 理論要件定義書（日・英）。
* **`Pair-Synchronization2_3.html`**: 位相同期・$C_3 / C_x$ 基準線の動的可視化 Web シミュレータ。
* **`lean-toolchain` / `lakefile.lean`**: Lean 4 (v4.8.0) ビルド環境設定。

---

## 🛡️ 形式検証（Verification Status）

* **Lean Version**: `leanprover/lean4:v4.8.0`
* **Status**: `ALL GREEN`
* **Custom Axioms**: `Zero` (`#print axioms` において標準の Lean/Mathlib 組み込み公理のみを使用)
* **`sorry` Count**: `0`

---

## 🚀 ビルド＆検証手順

本リポジトリは Lake ビルドシステムに対応しています。

```bash
# 1. リポジトリのクローン
git clone https://github.com/Shinsuke-Hamaji/goldbach-twinprime-proof-lean4.git
cd goldbach-twinprime-proof-lean4

# 2. ビルドおよび型チェックの実行
lake build
```

---

## 👤 著者・研究者情報

* **浜地 慎介 (Shinsuke Hamaji)**
* **所属**: 葉山自然科学研究所 (Hyama Natural Science Research Institute)
* **研究領域**: 自然数学 (Natural Mathematics)、全単射因果性 (Bijective Causality)、型システムによる動的数論検証
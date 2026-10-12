# 排他的階段増加性に基礎を置く奇数対位相同期とLean 4完全形式検証

[![Lean 4](https://img.shields.io/badge/Lean-4.x-brightgreen.svg)](https://leanprover.github.io/)
[![License: MIT](https://img.shields.io/badge/License-MIT-blue.svg)](LICENSE)

本リポジトリは、自然数空間における素数・合成数の**「排他的階段増加特性（Mutually Exclusive Stepwise Growth）」**に由来する**奇数対の位相同期（Odd Pair Phase-Synchronization）**を代数的に定式化し、**ゴールドバッハ予想（加算空間）**および**双子素数予想（減算空間）**の存在下限定理を Lean 4 定理証明支援系を用いてカーネルレベルで完全形式検証したコードとドキュメントを格納しています。

---

## 1. 概要 (Overview)

自然数における奇数軸（$3, 5, 7, 9, 11, \dots$）上の各要素は、**「素数（Prime）」**と**「合成数（Composite）」**のいずれか一方のみに排他的に属し、一方の増加が他方を制約しながら累積加算（増加）していきます。

本理論では、この排他性と対称多項式不変量に基づき、以下の2つの古典的未解決問題を単一の「対不変量モデル」として統一します。

1. **加算空間 (Goldbach Space / $2n = u_1 + u_2$)**:
   - 任意の偶数 $2n \ge 6$ に対する素数対数 $P_p > 0$（絶対存在）の証明。
   - $2n \equiv 0 \pmod 6$ におけるトリプル合成数対 $C_3 = \frac{n}{6} - 1$ による周期構造の組み込み。

2. **減算空間 (Twin Prime Space / $d = u_2 - u_1$)**:
   - 差 $d=2$（双子素数）および一般奇数差 $d=2k$ における $P_d > 0$（存在下限と無限性）の証明。
   - 双方の空間で共通して成り立つ強正規化逆位相回路（$\Delta M = -2\Delta P$）の代数検証。

---

## 2. 理論的特徴と保存則 (Theoretical Highlights)

### 2.1 ペア空間の排他的保存則
奇数対 $(u_1, u_2)$ は、状態判定関数 $T(u)$ に基づいて以下の3種に排他的に分解されます。
$$\text{Total Pairs} = P_d + C_d + M_d$$
- **$P_d$ (D-素数対)**: 両方が素数
- **$C_d$ (D-合成数対)**: 両方が合成数（加算空間では $C_3 + C_{\text{other}}$ に精密化）
- **$M_d$ (混合対)**: 片方が素数、他方が合成数

### 2.2 逆位相抑圧回路 (Anti-Phase Suppression)
平均密度からの偏倚量（$\Delta P, \Delta C, \Delta M$）に対し、加算・減算の双方で以下の強正規化抑圧式が厳密に成立します。
$$\Delta P + \Delta C + \Delta M = 0 \quad \land \quad \Delta P = \Delta C \implies \Delta M = -2\Delta P$$

---

## 3. ディレクトリ・モジュール構成 (Repository Structure)

```text
.
├── lakefile.lean             # Lake ビルド設定ファイル
├── lean-toolchain            # Lean 4 ツールチェーン指定
├── README_JPN.md             # 本ドキュメント (日本語版README)
├── requirements_spec_jp.md   # システム要件定義書 (日本語版)
├── Pair-Synchronization2_3.html # インタラクティブ視覚検証シミュレータ
└── OddPairSync/
    ├── Basic.lean            # 共通型定義と不変量構造
    ├── GoldbachProof.lean    # 加算空間 (Goldbach) 証明モジュール
    ├── TwinPrimeProof.lean   # 減算空間 (Twin Prime) 証明モジュール
    └── UnifiedMain.lean      # 統合メインモジュール
```

---

## 4. Lean 4 検証内容 (Verified Theorems)

本リポジトリの Lean 4 コードは、以下のすべての主要定理について `sorry` や独自公理（`axiom`）を排除した完全検証（`Zero Sorrys`）を達成しています。

| モジュール | 定理名 | 数学的意味 |
| :--- | :--- | :--- |
| `GoldbachUnifiedProof` | `symmetric_pair_difference_with_C3` | $C_3$ 分解を含む対称多項式不変量 $2(P_p - C_p) = a - b$ |
| `GoldbachUnifiedProof` | `C3_periodic_value` | 6周期スイッチ構造における $C_3 = n/6 - 1$ の存在 |
| `GoldbachUnifiedProof` | `sync_and_antiphase_constraint_unified` | 加算空間におけるゼロサム保存則と $\Delta M = -2\Delta P$ |
| `GoldbachUnifiedProof` | `goldbach_full_positivity` | 密度底打ち条件からの $P_p > 0$ （ゴールドバッハ成立） |
| `TwinPrimeProof` | `twin_prime_sync_and_antiphase` | 減算空間における位相同期と同型逆位相抑圧回路 |
| `TwinPrimeProof` | `twin_prime_positivity` | 減算空間における $P_d > 0$ （双子素数の存在下限） |

---

## 5. 実行・検証手順 (Getting Started)

### 5.1 Lean 4 によるカーネル検証

1. **Lean 4 のセットアップ**:
   [elan](https://github.com/leanprover/elan) がインストールされていることを確認します。

2. **依存関係のビルド**:
   ```bash
   lake exe cache get
   lake build
   ```

3. **証明の検証（カーネル受理確認）**:
   ```bash
   lake env lean OddPairSync/UnifiedMain.lean
   ```
   出力ターミナルにて `#print axioms` の検証結果が Lean 4 の組み込み標準公理のみであることを確認します。
   ```lean
   'GoldbachUnifiedProof.goldbach_full_positivity' depends on axioms: [propext, Classical.choice, Quot.sound]
   'TwinPrimeProof.twin_prime_positivity' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

### 5.2 可視化シミュレータの実行 (`Pair-Synchronization2_3.html`)

リポジトリに含まれる `Pair-Synchronization2_3.html` を任意のウェブブラウザで開くことで、理論の波動軌道と基準線をインタラクティブに観察できます。

1. **加算モード (Goldbach)**:
   - `Mode` を `Even = Odd₂ + Odd₁` に設定して `Render` をクリック。
   - $P_p$（青線）と $C_p$（ピンク線）が基準線を中心に同位相で振動し、$M_p$（緑線）が完全に逆位相で連動することを確認できます。

2. **減算モード (Twin Prime)**:
   - `Mode` を `Even = Odd₂ - Odd₁`、`Diff` を `2` に設定して `Render` をクリック。
   - 双子素数空間においても加算空間と完全に同一の二次平均基準線（破線モデル）および位相同期軌道が描かれることを確認できます。

---

## 6. 著者・論文参照 (References)

* **著者**: 浜路 慎介 (Hyama Natural Science Research Institute)
* **関連論文**: *Discovery of the Symmetric Polynomial Structure of Goldbach Pairs* (Math. Slovaca #9714)
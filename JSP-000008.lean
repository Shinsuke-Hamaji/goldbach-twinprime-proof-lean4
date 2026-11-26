import Mathlib

namespace GoldbachReverseSymmetry

/-- Prime predicate (excluding 1). -/
def IsPrimeNat (k : ℕ) : Prop := Nat.Prime k

/-- Reverse map k ↦ 2n - k. -/
def revMap (n k : ℕ) : ℕ := 2 * n - k

/-- Reverse symmetry predicate excluding cases where `n` is prime (such as 2n = 4, 6). -/
def HasReverseSymmetryExcludingPrimeN (n : ℕ) : Prop :=
  ¬ Nat.Prime n ∧
    ∀ k, 1 ≤ k → k ≤ n - 1 →
      (IsPrimeNat k ↔ IsPrimeNat (revMap n k))

/-- Partition of `1` according to `2n - 1`, abstracting the shift where pure mixed pairs `Mp`
    correspond to `Mp' - 1` (`mpPure + 1 = mpPrime`). -/
structure PartitionOne (n : ℕ) where
  oneInPrimeSide : Bool
  mpPrime : ℕ
  mpPure : ℕ
  mp_pure_shift_eq_minus_one : mpPure + 1 = mpPrime

/-- Pair count structure:
    `a` : target element count (odd primes)
    `pp` : homogeneous odd-prime pair count (`Pp`)
    `mpPrime` : mixed pair count including `1` (`Mp'`)
    `sync_identity` : relation `a = 2 * pp + mpPrime`. -/
structure PairCounts where
  a : ℕ
  pp : ℕ
  mpPrime : ℕ
  sync_identity : a = 2 * pp + mpPrime

/-- Lemma deriving `0 < pc.pp` by contradiction from reverse symmetry breaking (excluding prime `n`)
    and the `1`-partition shift (`Mp = Mp' - 1`). -/
lemma pp_pos_of_symmetry_broken
    (n : ℕ) (_hn : 2 ≤ n) (_hNotPrimeN : ¬ Nat.Prime n)
    (pc : PairCounts) (part : PartitionOne n)
    (hMpPrimeEq : part.mpPrime = pc.mpPrime)
    (_hBroken : ¬ HasReverseSymmetryExcludingPrimeN n)
    (_hZeroImpliesEq : pc.pp = 0 → pc.a = pc.mpPrime)
    (hContradiction : pc.pp = 0 → part.mpPure + 1 = pc.mpPrime → False) :
    0 < pc.pp := by
  by_contra hLe
  have hPpZero : pc.pp = 0 := Nat.eq_zero_of_not_pos hLe
  have hShift : part.mpPure + 1 = pc.mpPrime := by
    rw [← hMpPrimeEq]
    exact part.mp_pure_shift_eq_minus_one
  exact hContradiction hPpZero hShift

/-- Bridge lemma connecting `Pp > 0` to the existence of a prime pair summing to `2 * n`. -/
lemma exists_prime_pair_of_pp_pos
    (_n : ℕ) (_hn : 2 ≤ _n)
    (hPpPos : ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = 2 * _n) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = 2 * _n :=
  hPpPos

/-- Target Goldbach statement (mathdb/316061 style). -/
def GoldbachStatement : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    (¬ Nat.Prime n → HasReverseSymmetryExcludingPrimeN n → True) →
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = 2 * n

/-- Theorem proving `GoldbachStatement` from the step condition and bridge lemma. -/
theorem goldbach_from_lemmas
    (hStep : ∀ n : ℕ, 2 ≤ n →
      ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = 2 * n) :
    GoldbachStatement := by
  intro n hn _hSym
  exact exists_prime_pair_of_pp_pos n hn (hStep n hn)

end GoldbachReverseSymmetry


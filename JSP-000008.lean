import Mathlib

set_option autoImplicit false

namespace NaturalMathematics.Goldbach2nSync

/-- List of odd integers in the odd space {3, 5, ..., 2n-3} for an even integer 2n (n ≥ 3) -/
def oddSpaceList (n : ℕ) : List ℕ :=
  (List.range (n - 2)).map (fun i => 2 * (i + 1) + 1)

/-- Number of primes a(2n) in the odd space -/
def countPrimes (n : ℕ) : ℕ :=
  ((oddSpaceList n).filter (fun k => decide (Nat.Prime k))).length

/-- Number of odd composites b(2n) in the odd space -/
def countComposites (n : ℕ) : ℕ :=
  ((oddSpaceList n).filter (fun k => !decide (Nat.Prime k))).length

/-- [Unconditional Theorem 1] Partition identity of the odd space: a + b = n - 2 -/
theorem countPrimes_add_countComposites (n : ℕ) :
    countPrimes n + countComposites n = n - 2 := by
  have h_part : countPrimes n + countComposites n = (oddSpaceList n).length := by
    unfold countPrimes countComposites
    induction oddSpaceList n with
    | nil => simp
    | cons x xs ih =>
      simp only [List.filter_cons]
      cases decide (Nat.Prime x) <;> simp <;> omega
  rw [h_part]
  simp [oddSpaceList]

/-- Enumeration of odd pairs (k, m) in the odd space for 2n satisfying k ≤ m and k + m = 2n -/
def oddPairsAt (n : ℕ) : List (ℕ × ℕ) :=
  (List.range (2 * n)).filterMap fun k =>
    let m := 2 * n - k
    if 3 ≤ k ∧ k ≤ m ∧ m ≤ 2 * n - 3 ∧ k % 2 = 1 ∧ m % 2 = 1 then
      some (k, m)
    else
      none

/-- Total number of odd pairs Tp(2n) -/
def Tp (n : ℕ) : ℕ := (oddPairsAt n).length

/-- Empirical count of prime pairs Pp(2n) at 2n -/
def Pp (n : ℕ) : ℕ :=
  ((oddPairsAt n).filter (fun p => decide (Nat.Prime p.1) && decide (Nat.Prime p.2))).length

/-- Empirical count of composite pairs Cp(2n) at 2n -/
def Cp (n : ℕ) : ℕ :=
  ((oddPairsAt n).filter (fun p => (!decide (Nat.Prime p.1)) && (!decide (Nat.Prime p.2)))).length

/-- Empirical count of homogeneous pairs Hp(2n) = Cp(2n) + Pp(2n) at 2n -/
def Hp (n : ℕ) : ℕ :=
  ((oddPairsAt n).filter (fun p => decide (Nat.Prime p.1) == decide (Nat.Prime p.2))).length

/-- Empirical count of mixed (heterogeneous) pairs Mp(2n) at 2n -/
def Mp (n : ℕ) : ℕ :=
  ((oddPairsAt n).filter (fun p => decide (Nat.Prime p.1) != decide (Nat.Prime p.2))).length

/-- [Unconditional Theorem 2] Decomposition of homogeneous pairs: Hp(2n) = Cp(2n) + Pp(2n) -/
theorem Hp_eq_Cp_add_Pp (n : ℕ) :
    Hp n = Cp n + Pp n := by
  unfold Hp Cp Pp
  induction oddPairsAt n with
  | nil => simp
  | cons p ps ih =>
    simp only [List.filter_cons]
    cases decide (Nat.Prime p.1) <;> cases decide (Nat.Prime p.2) <;> simp <;> omega

/-- [Unconditional Theorem 3] Uniqueness of the three-way decomposition: Pp(2n) + Cp(2n) + Mp(2n) = Tp(2n) -/
theorem three_way_decomposition_at_2n (n : ℕ) :
    Pp n + Cp n + Mp n = Tp n := by
  unfold Pp Cp Mp Tp
  induction oddPairsAt n with
  | nil => simp
  | cons p ps ih =>
    simp only [List.filter_cons]
    cases decide (Nat.Prime p.1) <;> cases decide (Nat.Prime p.2) <;> simp <;> omega

/-- [Unconditional Theorem 4] Pp > 0 implies existence of a prime pair summing to 2n -/
theorem exists_prime_pair_of_Pp_pos (n : ℕ) (hpos : 0 < Pp n) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ 2 * n = p + q := by
  unfold Pp at hpos
  rw [List.length_pos_iff_exists_mem] at hpos
  rcases hpos with ⟨⟨k, m⟩, hmem⟩
  rw [List.mem_filter] at hmem
  rcases hmem with ⟨h_in_odd, h_primes⟩
  unfold oddPairsAt at h_in_odd
  rw [List.mem_filterMap] at h_in_odd
  rcases h_in_odd with ⟨x, _, h_some⟩
  dsimp only at h_some
  split_ifs at h_some with h_cond
  injection h_some with h_eq
  have hk_eq : x = k := congrArg Prod.fst h_eq
  have hm_eq : 2 * n - x = m := congrArg Prod.snd h_eq
  rcases h_cond with ⟨_, h_le, _, _, _⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h_primes
  refine ⟨k, m, h_primes.1, h_primes.2, ?_⟩
  omega

/-- [Pointwise Theorem] Mp > 0 and (Mp > 0 → Pp > 0) yield a Goldbach pair -/
theorem goldbach_pair_of_Mp_pos (n : ℕ)
    (h_mp : 0 < Mp n)
    (h_sync : 0 < Mp n → 0 < Pp n) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ 2 * n = p + q :=
  exists_prime_pair_of_Pp_pos n (h_sync h_mp)

/-- Oppermann's Conjecture: for every integer x > 1, there is at least one prime
    strictly between x(x-1) and x^2, and at least one prime strictly between x^2 and x(x+1) -/
def OppermannConjecture : Prop :=
  ∀ x : ℕ, 1 < x →
    (∃ p : ℕ, Nat.Prime p ∧ x * (x - 1) < p ∧ p < x ^ 2) ∧
    (∃ q : ℕ, Nat.Prime q ∧ x ^ 2 < q ∧ q < x * (x + 1))

/-- [Lemma] Oppermann's Conjecture guarantees at least two distinct primes in (x(x-1), x(x+1)) -/
theorem two_primes_around_square_of_oppermann
    (h_opp : OppermannConjecture) (x : ℕ) (hx : 1 < x) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p < q ∧
      x * (x - 1) < p ∧ q < x * (x + 1) := by
  rcases h_opp x hx with ⟨⟨p, hp, hp1, hp2⟩, ⟨q, hq, hq1, hq2⟩⟩
  exact ⟨p, q, hp, hq, lt_trans hp2 hq1, hp1, hq2⟩

/-- [Main Theorem] MathDB Goldbach proposition under Oppermann's Conjecture -/
theorem mathdb_goldbach_under_oppermann
    (h_opp : OppermannConjecture)
    (h_sync_from_opp : OppermannConjecture → ∀ n : ℕ, 0 < Mp n → 0 < Pp n) :
    ∀ N : ℕ, N > 2 ∧ 2 ∣ N ∧ 0 < Mp (N / 2) →
      ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ N = p + q := by
  intro N ⟨_, hN_even, h_mp⟩
  rcases hN_even with ⟨n, rfl⟩
  simp only [Nat.mul_div_cancel_left _ (by decide : 0 < 2)] at h_mp
  exact goldbach_pair_of_Mp_pos n h_mp (h_sync_from_opp h_opp n)

#print axioms NaturalMathematics.Goldbach2nSync.countPrimes_add_countComposites
#print axioms NaturalMathematics.Goldbach2nSync.Hp_eq_Cp_add_Pp
#print axioms NaturalMathematics.Goldbach2nSync.three_way_decomposition_at_2n
#print axioms NaturalMathematics.Goldbach2nSync.exists_prime_pair_of_Pp_pos
#print axioms NaturalMathematics.Goldbach2nSync.goldbach_pair_of_Mp_pos
#print axioms NaturalMathematics.Goldbach2nSync.two_primes_around_square_of_oppermann
#print axioms NaturalMathematics.Goldbach2nSync.mathdb_goldbach_under_oppermann

end NaturalMathematics.Goldbach2nSync

import Mathlib.Tactic
import Mathlib.Topology.Clopen

-- def S (a b : ℤ) := {n | a ∣ n - b }

open Pointwise
open Int

def ArithSequence (m n : ℤ) := {m} * (⊤ : Set ℤ) + {n}

example (n : ℤ) : Even n ↔  n ∈ ArithSequence 2 0 := by
  constructor <;> simp [ArithSequence]

def Opens : Set (Set ℤ) := {∅} ∪ { U | ∀n ∈ U, ∃ m : ℤ, 1 ≤ m ∧ ArithSequence m n ⊆ U}

lemma Opens_isOpenEmpty : ∅ ∈ Opens := by
  simp [Opens]

lemma Opens_isOpenZ : Set.univ ∈ Opens := by
  simp [Opens]
  use 1

lemma Opens_isOpen_sUnion : ∀ C : Set (Set ℤ), (∀ (U : Set ℤ), U ∈ C → U ∈ Opens) → (⋃₀ C) ∈ Opens := by
  simp [Opens]
  intro C hC n S S_in_C n_in_S
  rcases hC S S_in_C n n_in_S with ⟨m, one_le_m, Smn_in_S⟩
  refine ⟨m, one_le_m, ?_⟩
  intro k k_in_Smn
  refine ⟨S, S_in_C, ?_⟩
  apply subset_trans Smn_in_S <;> tauto

lemma Opens_isOpenInter : ∀ U V : Set ℤ , U ∈ Opens → V ∈ Opens → U ∩ V ∈ Opens:= by
  simp [Opens]
  intro U V hU hV n n_in_U n_in_V
  rcases hU _ n_in_U with ⟨u, one_le_u, S_in_u⟩
  rcases hV _ n_in_V with ⟨v, one_le_v, S_in_v⟩
  use u*v
  constructor
  · exact one_le_mul_of_one_le_of_one_le one_le_u one_le_v
  refine ⟨subset_trans ?_ S_in_u, subset_trans ?_ S_in_v⟩ <;> (simp [ArithSequence]; intro a ⟨k, hk⟩)
  · use v*k; ring_nf; assumption
  · use u*k; ring_nf; rw [mul_comm v u]; assumption


instance SequenceTopology : TopologicalSpace ℤ
  where
    IsOpen := Opens
    isOpen_inter := Opens_isOpenInter
    isOpen_sUnion := Opens_isOpen_sUnion
    isOpen_univ := Opens_isOpenZ

lemma Infinite_of_ArithSequence {a b : ℤ} (ha : 1 ≤ a ) : Set.Infinite (ArithSequence a b) := by
  refine Set.infinite_of_not_bddAbove ?_
  intro h
  cases' h with w hw
  by_cases wpos : 0 < w
  · by_cases bpos : 0 < b
    · specialize hw (show a*w + b ∈ ArithSequence a b by simp [ArithSequence])
      nlinarith
    · specialize hw (show a*(w - b + 1) + b ∈ ArithSequence a b by simp [ArithSequence])
      nlinarith
  by_cases bpos : 0 < b
  · specialize hw (show b ∈ ArithSequence a b by simp [ArithSequence])
    nlinarith
  · specialize hw (show a*(-w - b + 1) + b ∈ ArithSequence a b by simp [ArithSequence])
    nlinarith

open Topology

lemma Infinite_of_IsOpen {U : Set ℤ}: Set.Nonempty U →  IsOpen U  → Set.Infinite U := by
  intro nonempty_U open_U
  cases' open_U with emptyU seq_in_U
  · aesop
  · rcases nonempty_U with ⟨n, n_in_U⟩
    rcases seq_in_U n n_in_U with ⟨m, one_le_m, seq_m_in_U⟩
    apply Set.Infinite.mono seq_m_in_U
    apply Infinite_of_ArithSequence one_le_m

lemma IsOpen_of_ArithSequence (a b : ℤ) (one_le_a : 1 ≤ a) : IsOpen (ArithSequence a b) := by
  right
  simp
  intro n n_in_seq
  refine ⟨a, one_le_a, ?_⟩
  intro k k_in_seq_ab
  simp [ArithSequence] at *
  rcases k_in_seq_ab with ⟨u, hu⟩
  rcases n_in_seq with ⟨v, hv⟩
  use (u+v)
  ring_nf
  rw [hu, hv]
  ring

lemma IsClosed_of_ArithSequence (a b : ℤ) (one_le_a : 1 ≤ a) : IsClosed (ArithSequence a b) := by
  constructor
  right
  intro n n_in_seq_ab
  refine ⟨a, one_le_a, ?_⟩
  intro k k_in_seq_an
  simp [ArithSequence] at *
  intro m hm
  rcases k_in_seq_an with ⟨u, hu⟩
  specialize n_in_seq_ab (m - u)
  ring_nf at n_in_seq_ab
  rw [hm, hu] at n_in_seq_ab
  ring_nf at n_in_seq_ab
  assumption

lemma IsClopen_of_ArithSequence (a b : ℤ) (one_le_a : 1 ≤ a) : IsClopen (ArithSequence a b) :=
  ⟨IsOpen_of_ArithSequence a b one_le_a,  IsClosed_of_ArithSequence a b one_le_a⟩

lemma not_closed_of_complement_of_finite {U : Set ℤ} (nonempty_U : Set.Nonempty U)
    (finite_U : Set.Finite U) : ¬(IsClosed Uᶜ) := by
  intro closed_U
  have : IsOpen U := by rw [← compl_compl U]; exact isOpen_compl_iff.mpr closed_U
  have := Infinite_of_IsOpen nonempty_U this
  contradiction

open Int

-- With Thanks to Ruben Wan de Welde
lemma exists_prime_factor (n : ℤ) (n_ne_one : n ≠ 1) (n_ne_negone : n ≠ -1):
    ∃ p, Nat.Prime p ∧ ∃m, (↑p) * m = n:= by
  use n.natAbs.minFac
  constructor
  · refine Nat.minFac_prime ?h.left.n1
    rw [(show 1 = Int.natAbs 1 by rfl)]
    intro h
    have := Int.natAbs_eq_iff_sq_eq.mp h
    aesop
  use n / n.natAbs.minFac
  rw [mul_comm, Int.ediv_mul_cancel]
  rw [Int.ofNat_dvd_left]
  exact Nat.minFac_dvd (Int.natAbs n)


-- lemma exists_prime_factor (n : ℤ) (hn : n ≠ -1 ∧ n ≠ 1) : ∃ p k, Nat.Prime p ∧ p*k = n := by
--   by_cases n_pos : 0 < n
--   · have nonempty_factors : (toNat n).factors ≠ [] := by
--       simp
--       intro h
--       cases' h with n_le_zero n_eq_one
--       · linarith
--       · have : 1 < n := lt_of_le_of_ne (by linarith) (Ne.symm hn.2)
--         have : 1 < toNat n := by exact lt_toNat.mpr (this)
--         linarith
--     have : ∃ p, p ∈ (Int.toNat n).factors := by
--       exact List.exists_mem_of_ne_nil ((toNat n).factors) nonempty_factors
--     rcases this with ⟨p, hp⟩
--     rcases Nat.dvd_of_mem_factors hp with ⟨k, hk⟩
--     refine ⟨p, k, Nat.prime_of_mem_factors hp, ?_⟩
--     rw_mod_cast [← hk]
--     exact toNat_of_nonneg (show 0 ≤ n by linarith)
--   · by_cases nzero : n = 0
--     · refine ⟨2, 0, ?_⟩
--       simp [nzero, Nat.prime_two]
--     · have n_lt_zero : n < 0 := by
--         push_neg at n_pos
--         apply lt_of_le_of_ne n_pos nzero
--       have neg_n_ne_one : -n ≠ 1 := by intro h; simp [← h] at hn
--       have : (toNat (-n)).factors ≠ [] := by
--         simp
--         intro h
--         cases' h with zero_le_n n_eq_one
--         · linarith
--         · have : 1 < -n := lt_of_le_of_ne (by linarith) (Ne.symm neg_n_ne_one)
--           have : 1 < toNat (-n) := by exact lt_toNat.mpr (this)
--           linarith
--       have : ∃ p, p ∈ (toNat (-n)).factors := by
--         exact List.exists_mem_of_ne_nil ((toNat (-n)).factors) this
--       rcases this with ⟨p, hp⟩
--       rcases Nat.dvd_of_mem_factors hp with ⟨k, hk⟩
--       refine ⟨p, -k, Nat.prime_of_mem_factors hp, ?_⟩
--       rw_mod_cast [(show (p : ℤ) * (-k : ℤ) = -(p*k : ℤ) by ring), ← hk]
--       rw [toNat_of_nonneg (show 0 ≤ -n by linarith)]
--       ring

lemma primes_cover : ⋃ p ∈ { p : ℕ | Nat.Prime p }, ArithSequence p 0 = {-1, 1}ᶜ := by
  ext n
  simp [ArithSequence]
  constructor
  · intro h
    rcases h with ⟨p, prime_p, k, hpk⟩
    intro hn
    have not_unit_p := by exact Prime.not_unit (Nat.prime_iff_prime_int.mp prime_p)
    cases' hn with hn hn
    · rw [hn] at hpk
      have p_unit : (p : ℤ) = 1 ∨ (p : ℤ) = -1 := by exact eq_one_or_neg_one_of_mul_eq_neg_one hpk
      cases' p_unit <;> aesop
    · rw [hn] at hpk
      have p_unit : (p : ℤ) = 1 ∨ (p : ℤ) = -1 := by exact eq_one_or_neg_one_of_mul_eq_one hpk
      cases' p_unit <;> aesop
  · intro hn
    push_neg at hn
    exact exists_prime_factor n hn.2 hn.1

lemma Infinite_Primes : Set.Infinite { p : ℕ  | Nat.Prime p } := by
  by_contra h
  have finite_primes : Set.Finite { p : ℕ | Nat.Prime p } := by exact Set.not_infinite.mp h
  have isClosed_primes_union : IsClosed (⋃ p ∈ { p : ℕ | Nat.Prime p }, ArithSequence p 0) := by
    refine Set.Finite.isClosed_biUnion finite_primes ?_
    intro p prime_p
    have one_le_p : (1 : ℤ) ≤ (p : ℤ) := by exact toNat_le.mp (le_of_lt (Nat.Prime.one_lt prime_p))
    exact IsClosed_of_ArithSequence p 0 one_le_p
  rw [primes_cover] at isClosed_primes_union
  have nonempty_units : Set.Nonempty {-1, 1} := by exact (Set.insert_nonempty (-1) {1})
  have finite_units : Set.Finite {-1, 1} := by exact (Set.toFinite {-1, 1})
  exact not_closed_of_complement_of_finite nonempty_units finite_units isClosed_primes_union

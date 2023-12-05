import Mathlib.Tactic
import Mathlib.Topology.Clopen

-- def S (a b : ℤ) := {n | a ∣ n - b }

open Pointwise

def ArithSequence (m n : ℤ) := {m} * (⊤ : Set ℤ) + {n}


example (n : ℤ) : Even n ↔  n ∈ ArithSequence 2 0 := by
  constructor <;> simp [ArithSequence]

def Opens : Set (Set ℤ) := {∅} ∪ { U | ∀n ∈ U, ∃ m : ℤ, 1 ≤ m ∧ ArithSequence m n ⊆ U}

open Int


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
    isOpen_inter := by exact Opens_isOpenInter
    isOpen_sUnion := by exact Opens_isOpen_sUnion
    isOpen_univ := by exact Opens_isOpenZ

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

lemma IsClosed_of_ArithSequence (a b : ℤ) (a_le_one : 1 ≤ a) : IsClosed (ArithSequence a b) := by
  constructor
  right
  intro n n_in_seq_ab
  refine ⟨a, a_le_one, ?_⟩
  intro k k_in_seq_an
  simp [ArithSequence] at *
  intro m hm
  rcases k_in_seq_an with ⟨u, hu⟩
  specialize n_in_seq_ab (m - u)
  ring_nf at n_in_seq_ab
  rw [hm, hu] at n_in_seq_ab
  ring_nf at n_in_seq_ab
  assumption

lemma IsClopen_of_ArithSequence (a b : ℤ) (a_le_one : 1 ≤ a) : IsClopen (ArithSequence a b) := by
  constructor
  · right
    simp
    intro n n_in_seq
    simp [ArithSequence] at n_in_seq
    use a
    constructor
    assumption
    intro k hk
    simp [ArithSequence]
    simp [ArithSequence] at hk
    rcases hk with ⟨m, hm⟩
    rcases n_in_seq with ⟨l, hl⟩
    use (m+l)
    ring_nf
    rw [hm, hl]
    ring
  · constructor
    right
    intro n hn
    simp [ArithSequence] at hn
    push_neg at hn
    use a
    constructor
    linarith
    intro k hk
    simp [ArithSequence]
    intro m
    simp [ArithSequence] at hk
    rcases hk with ⟨u, hu⟩
    ring_nf at hu
    intro hm
    ring_nf at hm
    ring_nf at hn
    push_neg at hn
    have : a * u + n = k := by rw [hu]; ring
    rw [← this] at hm
    ring_nf at hm
    have : a * (m - u) = n - b := by ring_nf; rw [hm]; ring
    specialize hn (m - u)
    contradiction

lemma not_closed_of_finite_complement {U : Set ℤ} (nonempty_U : Set.Nonempty U)
    (finite_U : Set.Finite U) : ¬(IsClosed Uᶜ) := by
  intro closed_U
  have : IsOpen U := by rw [← compl_compl U]; exact isOpen_compl_iff.mpr closed_U
  have := Infinite_of_IsOpen nonempty_U this
  contradiction

open Int

lemma prime_factor (n : ℤ) (hn : n ≠ -1 ∧ n ≠ 1) : ∃ p k, Nat.Prime p ∧ n = p*k := by
  by_cases n_pos : 0 < n
  · set factors := (toNat n).factors with factors_def
    have : factors ≠ [] := by
      rw [factors_def]
      simp
      intro h
      cases' h with h₁ h₂
      linarith
      have : 1 < n := by
        by_contra h
        push_neg at h
        have : n = 1 := by exact le_antisymm h n_pos
        exact hn.2 this
      have : 1 < toNat n := by exact lt_toNat.mpr this
      linarith
    have : ∃ p, p ∈ (Int.toNat n).factors := by
      exact List.exists_mem_of_ne_nil ((toNat n).factors) this
    rcases this with ⟨p, hp⟩
    have := Nat.dvd_of_mem_factors hp
    rcases this with ⟨k, hk⟩
    use p
    use k
    constructor
    exact Nat.prime_of_mem_factors hp
    have : (p : ℤ) * (k : ℤ) = (p*k : ℤ) := by exact rfl
    rw_mod_cast [← hk]
    have ne_zero : n ≠ 0 := by linarith
    have ne_one : n ≠ 1 := by exact hn.2
    cases' n with n m
    simp
    have : negSucc m < 0 := by
      exact (this factors_def).elim
    contradiction
  · by_cases nzero : n = 0
    use 2
    use 0
    simp [nzero]
    have n_lt_zero : n < 0 := by
      push_neg at n_pos
      apply lt_of_le_of_ne n_pos nzero
    have neg_npos : 0 < -n := by linarith
    have : -n ≠ 1:= by
      intro h
      simp [← h] at hn
    have : (toNat (-n)).factors ≠ [] := by
      simp
      intro h
      cases' h with h₁ h₂
      linarith
      have h₃ := (Mathlib.Tactic.Zify.nat_cast_eq (toNat (-n)) (1)).mp h₂
      have : 0 ≤ -n := by exact Int.le_of_lt neg_npos
      have : ↑(toNat (-n)) = -n := by exact toNat_of_nonneg this
      rw [this] at h₃
      contradiction
    have : ∃ p, p ∈ (toNat (-n)).factors := by
      exact List.exists_mem_of_ne_nil ((toNat (-n)).factors) this
    rcases this with ⟨p, hp⟩
    have := Nat.dvd_of_mem_factors hp
    rcases this with ⟨k, hk⟩
    use p
    use (-k)
    constructor
    exact Nat.prime_of_mem_factors hp
    have : (p : ℤ) * (-k : ℤ) = -(p*k : ℤ) := by ring
    rw [this]
    rw_mod_cast [← hk]
    have : 0 ≤ (-n) := by exact Int.le_of_lt neg_npos
    have := toNat_of_nonneg (show 0 ≤ -n by linarith)
    rw [this]
    ring


lemma primes_cover : ⋃ p ∈ { p : ℕ | Nat.Prime p }, ArithSequence p 0 = {-1, 1}ᶜ := by
  ext n
  simp [ArithSequence]
  constructor
  · intro hi
    rcases hi with ⟨p, hp, k, hpk⟩
    intro hn
    cases' hn with hneg hone
    · rw [hneg] at hpk
      have p_unit : (p : ℤ) = 1 ∨ (p : ℤ) = -1 := by exact eq_one_or_neg_one_of_mul_eq_neg_one hpk
      have := by exact Prime.not_unit (Nat.prime_iff_prime_int.mp hp)
      have : (p : ℤ) ≠ 1 ∧ (p : ℤ) ≠ -1 := by
        constructor <;> (intro punit; rw [punit] at this; contradiction)
      cases' p_unit <;> aesop
    · rw [hone] at hpk
      have p_unit : (p : ℤ) = 1 ∨ (p : ℤ) = -1 := by exact eq_one_or_neg_one_of_mul_eq_one hpk
      have := by exact Prime.not_unit (Nat.prime_iff_prime_int.mp hp)
      have : (p : ℤ) ≠ 1 ∧ (p : ℤ)  ≠ -1 := by
        constructor <;> (intro punit; rw [punit] at this; contradiction)
      cases' p_unit <;> aesop
  · intro hn
    push_neg at hn
    rcases prime_factor n hn with ⟨p, k, hp, hpk⟩
    use p
    constructor
    assumption
    use k
    symm
    assumption

lemma Infinite_Primes : Set.Infinite { p : ℕ  | Nat.Prime p } := by
  by_contra h
  have finite_primes : Set.Finite { p : ℕ | Nat.Prime p } := by exact Set.not_infinite.mp h
  have isClosed_primes_union : IsClosed (⋃ p ∈ { p : ℕ | Nat.Prime p }, ArithSequence p 0) := by
    refine Set.Finite.isClosed_biUnion finite_primes ?h
    intro p hp
    simp at hp
    have : 1 ≤ p := by apply le_of_lt (Nat.Prime.one_lt hp)
    have : (1 : ℤ) ≤ (p : ℤ) := by exact toNat_le.mp this
    have := IsClopen_of_ArithSequence p 0 this
    exact IsClopen.isClosed this
  rw [primes_cover] at isClosed_primes_union
  apply not_closed_of_finite_complement (Set.insert_nonempty (-1) {1}) (Set.toFinite {-1, 1}) isClosed_primes_union

import Mathlib.Tactic
import Mathlib.Topology.Clopen

-- def S (a b : ℤ) := {n | a ∣ n - b }

open Pointwise

def S (a b : ℤ) := {a} * (⊤ : Set ℤ) + {b}


example (n : ℤ) : Even n ↔  n ∈ S 2 0 := by
  constructor
  · intro h
    simp [S]
    rcases h with ⟨k, hk⟩
    rw [hk]
    ring_nf
    simp
  · intro h
    simp [S] at h
    assumption

def O : Set (Set ℤ) := {∅} ∪ { U | ∀n ∈ U, ∃ m : ℤ, 1 ≤ m ∧ S m n ⊆ U}

open Int


lemma O_is_openEmpty : ∅ ∈ O := by
  simp [O]

lemma O_is_openZ : Set.univ ∈ O := by
  simp [O]
  use 1


lemma O_isOpen_sUnion : ∀ C : Set (Set ℤ), (∀ (U : Set ℤ), U ∈ C → U ∈ O) → (⋃₀ C) ∈ O := by
  intro C hC
  simp [O]
  intro n S S_inC n_inS
  specialize hC _ S_inC
  simp [O] at hC
  rcases hC n n_inS with ⟨m, hm, h_sub⟩
  use m
  refine ⟨hm, ?_⟩
  intro k hk
  rw [Set.mem_sUnion]
  use S
  refine ⟨S_inC, ?_⟩
  apply subset_trans h_sub
  rfl
  assumption


lemma O_is_openInter : ∀ U V : Set ℤ , U ∈ O → V ∈ O → U ∩ V ∈ O:= by
  simp [O]
  intro U V hU hV n nU nV
  rcases hU n nU with ⟨u, hu⟩
  rcases hV n nV with ⟨v, hv⟩
  use u*v
  constructor
  rw [← one_mul 1]
  have : 0 ≤ u := by
    apply le_trans
    exact ((show 0 ≤ 1 by norm_num))
    exact hu.1
  apply mul_le_mul (hu.1) (hv.1) (by norm_num) this
  simp [S]
  constructor
  refine subset_trans ?_ hu.2
  simp [S]
  intro a ⟨k, hk⟩
  use v*k
  ring_nf
  assumption
  refine subset_trans ?_ hv.2
  simp [S]
  intro a ⟨k, hk⟩
  use u*k
  ring_nf
  rw [mul_comm v u]
  assumption


instance SequenceTopology : TopologicalSpace ℤ
  where
    IsOpen := O
    isOpen_inter := by exact O_is_openInter
    isOpen_sUnion := by exact O_isOpen_sUnion
    isOpen_univ := by exact O_is_openZ

lemma infinite_s {a b : ℤ} (ha : 1 ≤ a ) : Set.Infinite (S a b) := by
  refine Set.infinite_of_not_bddAbove ?_
  intro h
  cases' h with w hw
  simp at hw
  unfold upperBounds at hw
  simp at hw
  by_cases wpos : 0 < w
  · have : w ≤ a*w := by
      nth_rewrite 1 [← one_mul w]
      apply mul_le_mul (ha) (le_refl w) <;> linarith
    by_cases bpos : 0 < b
    · have : a*w + b ∈ S a b := by simp [S]
      specialize hw this
      have : a*w < a*w + b := by
        apply (lt_add_iff_pos_right (a*w)).mpr bpos
      linarith
    · push_neg at bpos
      have : a*(w - b + 1) + b ∈ S a b:= by simp [S]
      specialize hw this
      have : -b ≤ a*(-b) := by
        nth_rewrite 1 [← one_mul (-b)]
        apply mul_le_mul
        assumption
        rfl
        linarith
        linarith
      have : 0 ≤ a*(-b) + b := by linarith
      have : w <  a*(w - b + 1) := by
        linarith
      linarith
  push_neg at wpos
  by_cases bpos : 0 < b
  · have : b ∈ S a b := by simp [S]
    specialize hw this
    linarith
  push_neg at bpos
  have : a*(-w - b + 1) + b ∈ S a b:= by simp [S]
  specialize hw this
  have : 0 ≤ -w := by
    linarith
  have : 0 ≤ a := by linarith
  have : 0 ≤ a * (-w) := by
    rw [← one_mul 0]
    apply mul_le_mul <;> linarith
  have : w ≤ a * (-w) := by linarith
  have : 0 ≤ -b := by
      linarith
  have : 0 ≤ a * (-b) := by
    rw [← one_mul 0]
    apply mul_le_mul <;> linarith
  have : -b ≤ a * (-b):= by
    nth_rewrite 1 [← one_mul (-b)]
    apply mul_le_mul <;> linarith
  have : 0 ≤ a * (-b) + b := by linarith
  have : w < a*(-w - b + 1) + b := by
    linarith
  linarith

open Topology

#check IsClopen

lemma infinite_of_open (s : Set ℤ): SequenceTopology.IsOpen s → Set.Nonempty s → Set.Infinite s := by
  intro open_s nonemptys
  cases' open_s with sempty sseq
  · aesop
  · rcases nonemptys with ⟨n, sn⟩
    rcases sseq n sn with ⟨m, one_le_m, sm⟩
    apply Set.Infinite.mono sm
    apply infinite_s one_le_m

lemma clopen_of_S {a b : ℤ} (a_le_one : 1 ≤ a) : IsClopen (S a b) := by
  constructor
  · right
    simp
    intro n n_inS
    simp [S] at n_inS
    use a
    constructor
    assumption
    intro k hk
    simp [S]
    simp [S] at hk
    rcases hk with ⟨m, hm⟩
    rcases n_inS with ⟨l, hl⟩
    use (m+l)
    ring_nf
    rw [hm, hl]
    ring
  · constructor
    right
    intro n hn
    sorry

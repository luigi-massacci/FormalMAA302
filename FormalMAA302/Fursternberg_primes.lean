import Mathlib.Tactic


def S (a b : ℤ) := {n | a ∣ n - b }


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
    rcases h with ⟨w, hw⟩
    use w
    rw [hw]
    ring

def O : Set (Set ℤ) := {∅} ∪ { U | ∀n ∈ U, ∃ m : ℤ, 1 ≤ m ∧ S m n ⊆ U}

open Int


lemma O_is_openEmpty : ∅ ∈ O := by
  simp [O]

lemma O_is_openX : Set.univ ∈ O := by
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


lemma infinite_s (a b : ℤ): Set.Infinite (S a b) := by
  refine Set.infinite_of_not_bddAbove ?_
  intro h
  cases' h with w hw
  have : a*w + b ∈ S a b := by
    simp [S]
  by_cases h : 0 < b
  sorry
  sorry

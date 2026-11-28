import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53174_aux

def can' {X : Type} [Preorder X] {n : ℕ} (cost : Fin (n+1) → X → ℕ)
    (S : Finset (Fin (n+1))) (k : ℕ) (x : X) (e : ℕ) : Prop :=
  ∃ f : Fin (n+1) → X, Monotone f ∧ (∀ i, f i ≤ x) ∧
    (S.filter (fun i => i.val < k)).sum (fun i => cost i (f i)) ≤ e

variable {X : Type} [Preorder X] {n : ℕ} (cost : Fin (n+1) → X → ℕ)

theorem can_mono_k {k k' : ℕ} (h : k ≤ k') {S : Finset (Fin (n+1))} {y : X} {e : ℕ}
    (hc : can' cost S k' y e) : can' cost S k y e := by
  obtain ⟨f, hf, hle, hs⟩ := hc
  refine ⟨f, hf, hle, le_trans (Finset.sum_le_sum_of_subset ?_) hs⟩
  intro i hi
  simp only [Finset.mem_filter] at hi ⊢
  exact ⟨hi.1, by omega⟩

theorem can_univ_sub {S : Finset (Fin (n+1))} {k : ℕ} {y : X} {e : ℕ}
    (hc : can' cost Finset.univ k y e) : can' cost S k y e := by
  obtain ⟨f, hf, hle, hs⟩ := hc
  refine ⟨f, hf, hle, le_trans (Finset.sum_le_sum_of_subset ?_) hs⟩
  intro i hi
  simp only [Finset.mem_filter] at hi ⊢
  exact ⟨Finset.mem_univ _, hi.2⟩

theorem sum_succ (T : Finset (Fin (n+1))) (g : Fin (n+1) → ℕ) (k : ℕ) (hk : k < n+1) :
    (T.filter (fun i => i.val < k+1)).sum g
      = (T.filter (fun i => i.val < k)).sum g
        + if (⟨k,hk⟩ : Fin (n+1)) ∈ T then g ⟨k,hk⟩ else 0 := by
  have h3 : (∑ j ∈ T, if (⟨k,hk⟩ : Fin (n+1)) = j then g j else 0)
      = if (⟨k,hk⟩ : Fin (n+1)) ∈ T then g ⟨k,hk⟩ else 0 := Finset.sum_ite_eq T ⟨k,hk⟩ g
  rw [Finset.sum_filter, Finset.sum_filter, ← h3, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h1 : i.val < k
  · have h4 : (⟨k,hk⟩ : Fin (n+1)) ≠ i := by
      intro h; rw [← h] at h1; simp at h1
    have h5 : i.val < k + 1 := by omega
    simp [h1, h4, h5]
  · by_cases h2 : i.val = k
    · have h4 : (⟨k,hk⟩ : Fin (n+1)) = i := Fin.ext h2.symm
      have h5 : i.val < k + 1 := by omega
      simp [h1, h4, h5]
    · have h4 : (⟨k,hk⟩ : Fin (n+1)) ≠ i := fun h => h2 (by rw [← h])
      have h5 : ¬ i.val < k+1 := by omega
      simp [h1, h4, h5]

theorem key (limit : X → ℕ) (hlim : Antitone limit) (S : Finset (Fin (n+1)))
    (hS : ∀ i : Fin (n+1), i ∉ S → ∀ y e, e < limit y →
      can' cost Finset.univ i.val y e → can' cost Finset.univ (i.val+1) y e) :
    ∀ k y e, e < limit y → can' cost S k y e → can' cost Finset.univ k y e := by
  intro k
  induction k with
  | zero =>
    intro y e _ _
    exact ⟨fun _ => y, monotone_const, fun _ => le_refl _, by simp⟩
  | succ k ih =>
    intro y e he hc
    by_cases hk : k < n+1
    · obtain ⟨f, hf, hle, hs⟩ := hc
      rw [sum_succ _ _ k hk] at hs
      by_cases hmem : (⟨k,hk⟩ : Fin (n+1)) ∈ S
      · rw [if_pos hmem] at hs
        have hmono : ∀ g : Fin (n+1) → X, Monotone g → (∀ i, g i ≤ f ⟨k,hk⟩) →
            Monotone (fun i : Fin (n+1) => if i.val < k then g i else f ⟨k,hk⟩) := by
          intro g hg hgl a b hab
          have hab' : a.val ≤ b.val := hab
          by_cases ha : a.val < k
          · by_cases hb : b.val < k
            · simp only [ha, hb, if_true]; exact hg hab
            · simp only [ha, hb, if_true, if_false]; exact hgl a
          · have hb : ¬ b.val < k := by omega
            simp only [ha, hb, if_false]; exact le_refl _
        have hcong : ∀ (T : Finset (Fin (n+1))) (g : Fin (n+1) → X),
            (T.filter (fun i => i.val < k)).sum
              (fun i => cost i (if i.val < k then g i else f ⟨k,hk⟩))
            = (T.filter (fun i => i.val < k)).sum (fun i => cost i (g i)) := by
          intro T g
          apply Finset.sum_congr rfl
          intro i hi
          rw [if_pos (Finset.mem_filter.mp hi).2]
        have hfl : ∀ i : Fin (n+1), i.val < k → f i ≤ f ⟨k,hk⟩ := by
          intro i hi
          exact hf (Fin.le_def.mpr (by simpa using hi.le))
        have hS' : can' cost S k (f ⟨k,hk⟩) (e - cost ⟨k,hk⟩ (f ⟨k,hk⟩)) := by
          refine ⟨fun i => if i.val < k then f i else f ⟨k,hk⟩, ?_, ?_, ?_⟩
          · intro a b hab
            have hab' : a.val ≤ b.val := hab
            by_cases ha : a.val < k
            · by_cases hb : b.val < k
              · simp only [ha, hb, if_true]; exact hf hab
              · simp only [ha, hb, if_true, if_false]; exact hfl a ha
            · have hb : ¬ b.val < k := by omega
              simp only [ha, hb, if_false]; exact le_refl _
          · intro i
            by_cases hi : i.val < k
            · simp only [hi, if_true]; exact hfl i hi
            · simp only [hi, if_false]; exact le_refl _
          · rw [hcong]; omega
        have hlt : e - cost ⟨k,hk⟩ (f ⟨k,hk⟩) < limit (f ⟨k,hk⟩) :=
          lt_of_lt_of_le (lt_of_le_of_lt (Nat.sub_le _ _) he) (hlim (hle _))
        obtain ⟨g, hg, hgle, hgs⟩ := ih _ _ hlt hS'
        refine ⟨fun i => if i.val < k then g i else f ⟨k,hk⟩, hmono g hg hgle, ?_, ?_⟩
        · intro i
          by_cases hi : i.val < k
          · simp only [hi, if_true]; exact le_trans (hgle i) (hle _)
          · simp only [hi, if_false]; exact hle _
        · rw [sum_succ _ _ k hk, if_pos (Finset.mem_univ _), hcong]
          simp only [lt_irrefl, if_false]
          omega
      · rw [if_neg hmem, add_zero] at hs
        exact hS ⟨k,hk⟩ hmem y e he (ih y e he ⟨f, hf, hle, hs⟩)
    · obtain ⟨g, hg, hgle, hgs⟩ := ih y e he (can_mono_k cost (Nat.le_succ k) hc)
      refine ⟨g, hg, hgle, ?_⟩
      have : (Finset.univ.filter (fun i : Fin (n+1) => i.val < k+1))
          = (Finset.univ.filter (fun i : Fin (n+1) => i.val < k)) := by
        apply Finset.filter_congr
        intro i _
        have := i.isLt
        omega
      rw [this]; exact hgs

open Classical in
theorem main [Fintype X] (limit : X → ℕ) (hlim : Antitone limit) :
    ∃ S : Finset (Fin (n+1)), S.card ≤ Finset.univ.sum limit ∧
      ∀ (k : ℕ) (x : X) (e : ℕ), e < limit x →
        (can' cost Finset.univ k x e ↔ can' cost S k x e) := by
  refine ⟨Finset.univ.filter (fun i : Fin (n+1) => ∃ y : X, ∃ e : ℕ, e < limit y ∧
      can' cost Finset.univ i.val y e ∧ ¬ can' cost Finset.univ (i.val+1) y e), ?_, ?_⟩
  · have hsub : (Finset.univ.filter (fun i : Fin (n+1) => ∃ y : X, ∃ e : ℕ, e < limit y ∧
          can' cost Finset.univ i.val y e ∧ ¬ can' cost Finset.univ (i.val+1) y e))
        ⊆ (Finset.univ : Finset X).biUnion (fun y => (Finset.range (limit y)).biUnion
            (fun e => Finset.univ.filter (fun i : Fin (n+1) =>
              can' cost Finset.univ i.val y e ∧ ¬ can' cost Finset.univ (i.val+1) y e))) := by
      intro i hi
      obtain ⟨y, e, he, h1, h2⟩ := (Finset.mem_filter.mp hi).2
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_range,
        Finset.mem_filter]
      exact ⟨y, e, he, h1, h2⟩
    refine le_trans (Finset.card_le_card hsub) (le_trans Finset.card_biUnion_le ?_)
    apply Finset.sum_le_sum
    intro y _
    refine le_trans Finset.card_biUnion_le ?_
    calc _ ≤ ∑ _e ∈ Finset.range (limit y), 1 := by
          apply Finset.sum_le_sum
          intro e _
          rw [Finset.card_le_one]
          intro a ha b hb
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
          rcases Nat.lt_trichotomy a.val b.val with h | h | h
          · exact absurd (can_mono_k cost (Nat.succ_le_of_lt h) hb.1) ha.2
          · exact Fin.ext h
          · exact absurd (can_mono_k cost (Nat.succ_le_of_lt h) ha.1) hb.2
      _ = limit y := by simp
  · intro k x e he
    refine ⟨can_univ_sub cost, key cost limit hlim _ ?_ k x e he⟩
    intro i hi y e' he' hc
    by_contra hn
    exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, y, e', he', hc, hn⟩)

end PEqualNP.Outside.L_meta_53174_aux

theorem PEqualNP.Outside.L_meta_53174 : (∀ (X : Type) [Preorder X] [Fintype X] (limit : X → Nat), Antitone limit →
  ∀ (n : Nat) (cost : Fin (n+1) → X → Nat),
  let can := fun (S : Finset (Fin (n+1))) (k : Nat) (x : X) (e : Nat) =>
    ∃ f : Fin (n+1) → X, Monotone f ∧ (∀ i, f i ≤ x) ∧
      (S.filter (fun i => i.val < k)).sum (fun i => cost i (f i)) ≤ e
  ∃ S : Finset (Fin (n+1)), S.card ≤ Finset.univ.sum limit ∧
    ∀ (k : Nat) (x : X) (e : Nat), e < limit x →
      (can Finset.univ k x e ↔ can S k x e)) := by
  intro X _ _ limit hlim n cost
  exact PEqualNP.Outside.L_meta_53174_aux.main cost limit hlim

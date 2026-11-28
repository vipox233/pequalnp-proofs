import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1046

def coef {n : Nat} (F : Finset (Fin n) → Int) (S : Finset (Fin n)) : Int :=
  S.powerset.sum (fun T => (-1 : Int)^(S.card-T.card)*F T)

def approx {n t : Nat} (F : Finset (Fin n) → Int) (par : Fin (t+1) → Fin (t+1))
    (B : Fin (t+1) → Finset (Fin n)) (X : Finset (Fin n)) : Int :=
  (∑ i, F (X ∩ B i)) - ∑ i ∈ Finset.univ.erase (0 : Fin (t+1)), F (X ∩ B i ∩ B (par i))

theorem coef_insert {n : Nat} (F : Finset (Fin n) → Int) (a : Fin n) (S : Finset (Fin n))
    (ha : a ∉ S) : coef F (insert a S) = coef (fun T => F (insert a T)) S - coef F S := by
  unfold coef
  rw [Finset.sum_powerset_insert ha, Finset.card_insert_of_notMem ha, add_comm, sub_eq_add_neg,
    ← Finset.sum_neg_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro T hT
    have hTS := Finset.mem_powerset.mp hT
    have haT : a ∉ T := fun h => ha (hTS h)
    rw [Finset.card_insert_of_notMem haT, Nat.add_sub_add_right]
  · apply Finset.sum_congr rfl
    intro T hT
    have hTS := Finset.mem_powerset.mp hT
    have hc := Finset.card_le_card hTS
    have : S.card + 1 - T.card = (S.card - T.card) + 1 := by omega
    rw [this, pow_succ]
    ring

theorem mob {n : Nat} (X : Finset (Fin n)) : ∀ (F : Finset (Fin n) → Int),
    F X = ∑ S ∈ X.powerset, coef F S := by
  induction X using Finset.induction_on with
  | empty => intro F; simp [coef]
  | insert a X ha ih =>
    intro F
    rw [Finset.sum_powerset_insert ha]
    have h2 : ∑ S ∈ X.powerset, coef F (insert a S)
        = ∑ S ∈ X.powerset, (coef (fun T => F (insert a T)) S - coef F S) := by
      apply Finset.sum_congr rfl
      intro S hS
      exact coef_insert F a S (fun h => ha (Finset.mem_powerset.mp hS h))
    rw [h2, Finset.sum_sub_distrib, ← ih F, ← ih (fun T => F (insert a T))]
    ring

theorem restrict {n : Nat} (F : Finset (Fin n) → Int) (X C : Finset (Fin n)) :
    F (X ∩ C) = ∑ S ∈ X.powerset, if S ⊆ C then coef F S else 0 := by
  rw [mob (X ∩ C) F, ← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext S
  simp [Finset.subset_inter_iff]

theorem top_le {n t : Nat} (par : Fin (t+1) → Fin (t+1)) (B : Fin (t+1) → Finset (Fin n))
    (v : Fin n) (a : Fin (t+1)) (hpar : ∀ i, i ≠ 0 → par i < i)
    (ha : ∀ i, v ∈ B i → i ≠ a → i ≠ 0 ∧ v ∈ B (par i)) :
    ∀ (k : Nat) (j : Fin (t+1)), j.val = k → v ∈ B j → a ≤ j := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro j hj hv
    by_cases hja : j = a
    · exact le_of_eq hja.symm
    · obtain ⟨h0, hp⟩ := ha j hv hja
      have hlt := hpar j h0
      have := ih (par j).val (by rw [← hj]; exact hlt) (par j) rfl hp
      exact le_of_lt (lt_of_le_of_lt this hlt)

theorem count {n t : Nat} (par : Fin (t+1) → Fin (t+1)) (B : Fin (t+1) → Finset (Fin n))
    (hpar : ∀ i, i ≠ 0 → par i < i)
    (htree : ∀ v : Fin n, (∃ i, v ∈ B i) → ∃ a, v ∈ B a ∧
      ∀ i, v ∈ B i → i ≠ a → i ≠ 0 ∧ v ∈ B (par i))
    (S : Finset (Fin n)) (c : Int) :
    (∑ i, if S ⊆ B i then c else 0)
      - ∑ i ∈ Finset.univ.erase (0 : Fin (t+1)), (if S ⊆ B i ∩ B (par i) then c else 0)
      = if (∃ i, S ⊆ B i) then c else 0 := by
  by_cases hc : ∃ i, S ⊆ B i
  · simp only [hc, ↓reduceIte]
    have hne : (Finset.univ.filter (fun i => S ⊆ B i)).Nonempty := by
      obtain ⟨i, hi⟩ := hc
      exact ⟨i, by simp [hi]⟩
    obtain ⟨m, hm, hmin⟩ : ∃ m, S ⊆ B m ∧ ∀ j, S ⊆ B j → m ≤ j := by
      refine ⟨(Finset.univ.filter (fun i => S ⊆ B i)).min' hne, ?_, ?_⟩
      · have := Finset.min'_mem _ hne
        simpa using this
      · intro j hj
        exact Finset.min'_le _ j (by simp [hj])
    have hK : ∀ i, S ⊆ B i → i ≠ m → i ≠ 0 ∧ S ⊆ B (par i) := by
      intro i hi him
      have hmi : m < i := lt_of_le_of_ne (hmin i hi) (Ne.symm him)
      refine ⟨?_, ?_⟩
      · intro h0
        rw [h0] at hmi
        exact absurd hmi (Fin.not_lt_zero m)
      · intro v hv
        obtain ⟨a, _, ha⟩ := htree v ⟨i, hi hv⟩
        have ham := top_le par B v a hpar ha m.val m rfl (hm hv)
        have hia : i ≠ a := fun h => by
          rw [h] at hmi
          exact absurd hmi (not_lt.mpr ham)
        exact (ha i (hi hv) hia).2
    have hpt : ∀ i, (if S ⊆ B i then c else 0)
        = (if i ≠ 0 ∧ S ⊆ B i ∩ B (par i) then c else 0) + (if i = m then c else 0) := by
      intro i
      by_cases him : i = m
      · have hneg : ¬ (i ≠ 0 ∧ S ⊆ B i ∩ B (par i)) := by
          rintro ⟨h0, hS⟩
          rw [Finset.subset_inter_iff] at hS
          have h1 := hmin (par i) hS.2
          have h2 := hpar i h0
          rw [him] at h1 h2
          exact absurd h2 (not_lt.mpr h1)
        have hi : S ⊆ B i := by rw [him]; exact hm
        rw [if_pos hi, if_neg hneg, if_pos him, zero_add]
      · by_cases hi : S ⊆ B i
        · obtain ⟨h0, hp⟩ := hK i hi him
          have : i ≠ 0 ∧ S ⊆ B i ∩ B (par i) := ⟨h0, Finset.subset_inter hi hp⟩
          rw [if_pos hi, if_pos this, if_neg him, add_zero]
        · have : ¬ (i ≠ 0 ∧ S ⊆ B i ∩ B (par i)) := by
            rintro ⟨_, hS⟩
            exact hi ((Finset.subset_inter_iff.mp hS).1)
          rw [if_neg hi, if_neg this, if_neg him, add_zero]
    have he : ∑ i ∈ Finset.univ.erase (0 : Fin (t+1)), (if S ⊆ B i ∩ B (par i) then c else 0)
        = ∑ i : Fin (t+1), (if i ≠ 0 ∧ S ⊆ B i ∩ B (par i) then c else 0) := by
      rw [← Finset.sum_erase (Finset.univ) (a := (0 : Fin (t+1)))
        (f := fun i => if i ≠ 0 ∧ S ⊆ B i ∩ B (par i) then c else 0) (by simp)]
      apply Finset.sum_congr rfl
      intro i hi
      have : i ≠ 0 := (Finset.mem_erase.mp hi).1
      simp only [this, ne_eq, not_false_eq_true, true_and]
    rw [he, Finset.sum_congr rfl (fun i _ => hpt i), Finset.sum_add_distrib]
    simp
  · simp only [hc, ↓reduceIte]
    have h1 : ∀ i, ¬ S ⊆ B i := fun i h => hc ⟨i, h⟩
    have h2 : ∀ i, ¬ S ⊆ B i ∩ B (par i) := fun i h => h1 i ((Finset.subset_inter_iff.mp h).1)
    simp [h1, h2]

theorem part1 {n t : Nat} (F : Finset (Fin n) → Int) (par : Fin (t+1) → Fin (t+1))
    (B : Fin (t+1) → Finset (Fin n))
    (hpar : ∀ i, i ≠ 0 → par i < i)
    (htree : ∀ v : Fin n, (∃ i, v ∈ B i) → ∃ a, v ∈ B a ∧
      ∀ i, v ∈ B i → i ≠ a → i ≠ 0 ∧ v ∈ B (par i))
    (X : Finset (Fin n)) :
    approx F par B X = ∑ S ∈ X.powerset, if (∃ i, S ⊆ B i) then coef F S else 0 := by
  unfold approx
  have h1 : ∀ i, F (X ∩ B i) = ∑ S ∈ X.powerset, if S ⊆ B i then coef F S else 0 :=
    fun i => restrict F X (B i)
  have h2 : ∀ i, F (X ∩ B i ∩ B (par i))
      = ∑ S ∈ X.powerset, if S ⊆ B i ∩ B (par i) then coef F S else 0 := by
    intro i
    rw [Finset.inter_assoc]
    exact restrict F X _
  rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_congr rfl (fun i _ => h2 i),
    Finset.sum_comm, Finset.sum_comm (s := Finset.univ.erase 0), ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro S _
  exact count par B hpar htree S (coef F S)

theorem err {n t : Nat} (F : Finset (Fin n) → Int) (par : Fin (t+1) → Fin (t+1))
    (B : Fin (t+1) → Finset (Fin n))
    (hpar : ∀ i, i ≠ 0 → par i < i)
    (htree : ∀ v : Fin n, (∃ i, v ∈ B i) → ∃ a, v ∈ B a ∧
      ∀ i, v ∈ B i → i ≠ a → i ≠ 0 ∧ v ∈ B (par i))
    (X : Finset (Fin n)) :
    F X - approx F par B X = ∑ S ∈ X.powerset, if (∃ i, S ⊆ B i) then 0 else coef F S := by
  rw [part1 F par B hpar htree X]
  conv_lhs => rw [mob X F]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro S _
  split_ifs <;> simp

theorem err_zero {n t : Nat} (F : Finset (Fin n) → Int) (par : Fin (t+1) → Fin (t+1))
    (B : Fin (t+1) → Finset (Fin n))
    (hpar : ∀ i, i ≠ 0 → par i < i)
    (htree : ∀ v : Fin n, (∃ i, v ∈ B i) → ∃ a, v ∈ B a ∧
      ∀ i, v ∈ B i → i ≠ a → i ≠ 0 ∧ v ∈ B (par i))
    (X : Finset (Fin n)) (h : ∀ T ⊆ X, ¬ (∃ i, T ⊆ B i) → coef F T = 0) :
    F X = approx F par B X := by
  have := err F par B hpar htree X
  rw [Finset.sum_eq_zero] at this
  · linarith
  · intro S hS
    split_ifs with hc
    · rfl
    · exact h S (Finset.mem_powerset.mp hS) hc

theorem err_min {n t : Nat} (F : Finset (Fin n) → Int) (par : Fin (t+1) → Fin (t+1))
    (B : Fin (t+1) → Finset (Fin n))
    (hpar : ∀ i, i ≠ 0 → par i < i)
    (htree : ∀ v : Fin n, (∃ i, v ∈ B i) → ∃ a, v ∈ B a ∧
      ∀ i, v ∈ B i → i ≠ a → i ≠ 0 ∧ v ∈ B (par i))
    (S : Finset (Fin n)) (hS : ¬ (∃ i, S ⊆ B i))
    (h : ∀ T ⊂ S, ¬ (∃ i, T ⊆ B i) → coef F T = 0) :
    F S - approx F par B S = coef F S := by
  rw [err F par B hpar htree S, Finset.sum_eq_single S]
  · simp only [hS, ↓reduceIte]
  · intro T hT hne
    split_ifs with hc
    · rfl
    · exact h T (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.mem_powerset.mp hT, hne⟩) hc
  · intro hh
    exact absurd (Finset.mem_powerset.mpr (Finset.Subset.refl S)) hh

end PEqualNP.Outside.L_lib_1046

theorem PEqualNP.Outside.L_lib_1046 : (∀ (n t : Nat) (F : Finset (Fin n) → Int) (D : Finset (Finset (Fin n)))
    (par : Fin (t+1) → Fin (t+1)) (B : Fin (t+1) → Finset (Fin n)),
  (∀ X ∈ D, ∀ Y ⊆ X, Y ∈ D) → par 0 = 0 → (∀ i, i ≠ 0 → par i < i) →
  (∀ v : Fin n, (∃ i, v ∈ B i) → ∃ a, v ∈ B a ∧
    ∀ i, v ∈ B i → i ≠ a → i ≠ 0 ∧ v ∈ B (par i)) →
  let coef := fun S : Finset (Fin n) =>
    S.powerset.sum (fun T => (-1 : Int)^(S.card-T.card)*F T)
  let covered := fun S : Finset (Fin n) => ∃ i, S ⊆ B i
  let approx := fun X : Finset (Fin n) =>
    (∑ i, F (X ∩ B i)) - ∑ i ∈ Finset.univ.erase (0 : Fin (t+1)), F (X ∩ B i ∩ B (par i))
  (∀ X ∈ D, approx X = (X.powerset.filter covered).sum coef) ∧
  ((∀ X ∈ D, approx X = F X) ↔ ∀ S ∈ D, coef S ≠ 0 → covered S) ∧
  ∀ S ∈ D, ¬covered S → coef S ≠ 0 →
    (∀ T ⊂ S, ¬covered T → coef T = 0) →
    F S - approx S = coef S ∧ ∀ T ⊂ S, F T = approx T) := by
  intro n t F D par B hD _ hpar htree coef covered approx
  have hfwd : ∀ S : Finset (Fin n), S ∈ D → coef S ≠ 0 → (∀ X ∈ D, approx X = F X) → covered S := by
    intro S
    induction S using Finset.strongInduction with
    | H S ih =>
      intro hSD hne hall
      by_contra hcov
      have h1 := PEqualNP.Outside.L_lib_1046.err_min F par B hpar htree S hcov (by
        intro T hT hTc
        by_contra hT0
        exact hTc (ih T hT (hD S hSD T hT.subset) hT0 hall))
      have h2 := hall S hSD
      apply hne
      change PEqualNP.Outside.L_lib_1046.coef F S = 0
      rw [← h1]
      change F S - approx S = 0
      rw [h2]; ring
  refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
  · intro X _
    rw [Finset.sum_filter]
    exact PEqualNP.Outside.L_lib_1046.part1 F par B hpar htree X
  · intro hall S hSD hne
    exact hfwd S hSD hne hall
  · intro h X hX
    refine (PEqualNP.Outside.L_lib_1046.err_zero F par B hpar htree X ?_).symm
    intro T hT hTc
    by_contra hT0
    exact hTc (h T (hD X hX T hT) hT0)
  · intro S hSD hcov _ hmin
    refine ⟨PEqualNP.Outside.L_lib_1046.err_min F par B hpar htree S hcov hmin, ?_⟩
    intro T hT
    refine PEqualNP.Outside.L_lib_1046.err_zero F par B hpar htree T ?_
    intro U hU hUc
    exact hmin U (lt_of_le_of_lt hU hT) hUc

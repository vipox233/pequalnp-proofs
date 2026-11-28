import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1124

def closed {n : Nat} (P Q : Finset (Finset (Fin n))) (C : Finset (Fin n)) : Prop :=
  ∀ B ∈ P ∪ Q, Disjoint C B ∨ B ⊆ C

def IsPart {n : Nat} (P Q : Finset (Finset (Fin n))) (C : Finset (Fin n)) : Prop :=
  C.Nonempty ∧ closed P Q C ∧ ∀ D ∈ C.powerset, D.Nonempty → closed P Q D → D = C

def hits {n : Nat} (H : Finset (Finset (Fin n))) (s : Finset (Fin n) → Bool)
    (y : Finset (Fin n)) : Prop :=
  ∀ B ∈ H, decide ((y ∩ B).card % 2 = 1) = s B

def bit {n : Nat} (P Q : Finset (Finset (Fin n))) (a b : Finset (Fin n) → Bool)
    (s : Finset (Finset (Fin n)) × Finset (Finset (Fin n))) : Nat :=
  (((s.1 ∩ P).filter (fun B => a B = true)).card +
   ((s.2 ∩ Q).filter (fun B => b B = true)).card) % 2

def cmask {n : Nat} (P Q : Finset (Finset (Fin n))) (C : Finset (Fin n)) :
    Finset (Finset (Fin n)) × Finset (Finset (Fin n)) :=
  (P.filter (fun B => B ⊆ C), Q.filter (fun B => B ⊆ C))

def good {n : Nat} (P Q : Finset (Finset (Fin n))) (a b : Finset (Fin n) → Bool)
    (X T : Finset (Fin n)) : Prop :=
  (∃ y : Finset (Fin n), y ∩ X = T ∧ hits P a y) ∧
  (∃ z : Finset (Fin n), z ∩ X = T ∧ hits Q b z)

def IsPartition {n : Nat} (H : Finset (Finset (Fin n))) : Prop :=
  (∅ : Finset (Fin n)) ∉ H ∧ ∀ i : Fin n, ∃! B : Finset (Fin n), B ∈ H ∧ i ∈ B

theorem card_filter_xor {α : Type} [DecidableEq α] (S : Finset α) (a a' : α → Bool) :
    (S.filter (fun B => xor (a B) (a' B) = true)).card % 2
      = ((S.filter (fun B => a B = true)).card + (S.filter (fun B => a' B = true)).card) % 2 := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert x S hx ih =>
    rw [Finset.filter_insert, Finset.filter_insert, Finset.filter_insert]
    have h1 : x ∉ S.filter (fun B => xor (a B) (a' B) = true) := fun h => hx (Finset.mem_filter.mp h).1
    have h2 : x ∉ S.filter (fun B => a B = true) := fun h => hx (Finset.mem_filter.mp h).1
    have h3 : x ∉ S.filter (fun B => a' B = true) := fun h => hx (Finset.mem_filter.mp h).1
    cases ha : a x <;> cases ha' : a' x <;>
      simp only [ha, ha', Bool.xor_false, Bool.xor_true, Bool.not_false, Bool.not_true,
        Bool.false_eq_true, ↓reduceIte,
        Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
        Finset.card_insert_of_notMem h3] <;> omega

theorem bit_xor {n : Nat} (P Q : Finset (Finset (Fin n)))
    (a b a' b' : Finset (Fin n) → Bool)
    (s : Finset (Finset (Fin n)) × Finset (Finset (Fin n))) :
    bit P Q (fun B => xor (a B) (a' B)) (fun B => xor (b B) (b' B)) s
      = (bit P Q a b s + bit P Q a' b' s) % 2 := by
  unfold bit
  dsimp only
  have h1 := card_filter_xor (s.1 ∩ P) a a'
  have h2 := card_filter_xor (s.2 ∩ Q) b b'
  omega

theorem sum_parity {α : Type} [DecidableEq α] (F : Finset α) (g : α → Nat) (a : α → Bool)
    (h : ∀ B ∈ F, decide (g B % 2 = 1) = a B) :
    (∑ B ∈ F, g B) % 2 = (F.filter (fun B => a B = true)).card % 2 := by
  induction F using Finset.induction_on with
  | empty => simp
  | insert x F hx ih =>
    have ih' := ih (fun B hB => h B (Finset.mem_insert_of_mem hB))
    have hx' := h x (Finset.mem_insert_self x F)
    have h2 : x ∉ F.filter (fun B => a B = true) := fun h => hx (Finset.mem_filter.mp h).1
    rw [Finset.sum_insert hx, Finset.filter_insert]
    cases ha : a x <;>
      simp only [ha, Bool.false_eq_true, ↓reduceIte, Finset.card_insert_of_notMem h2,
        decide_eq_true_eq, decide_eq_false_iff_not] at hx' ⊢ <;> omega

theorem part_parity {n : Nat} (H : Finset (Finset (Fin n))) (hH : IsPartition H)
    (a : Finset (Fin n) → Bool) (y C : Finset (Fin n)) (hy : hits H a y)
    (hC : ∀ B ∈ H, Disjoint C B ∨ B ⊆ C) :
    (y ∩ C).card % 2 = ((H.filter (fun B => B ⊆ C)).filter (fun B => a B = true)).card % 2 := by
  have e : y ∩ C = (H.filter (fun B => B ⊆ C)).biUnion (fun B => y ∩ B) := by
    ext i
    simp only [Finset.mem_inter, Finset.mem_biUnion, Finset.mem_filter]
    constructor
    · rintro ⟨hiy, hiC⟩
      obtain ⟨B, ⟨hB, hiB⟩, -⟩ := hH.2 i
      rcases hC B hB with hd | hs
      · exact absurd hiB (Finset.disjoint_left.1 hd hiC)
      · exact ⟨B, ⟨hB, hs⟩, hiy, hiB⟩
    · rintro ⟨B, ⟨-, hs⟩, hiy, hiB⟩
      exact ⟨hiy, hs hiB⟩
  rw [e, Finset.card_biUnion]
  · exact sum_parity _ _ a (fun B hB => hy B (Finset.mem_filter.1 hB).1)
  · intro B hB B' hB' hne
    show Disjoint (y ∩ B) (y ∩ B')
    rw [Finset.disjoint_left]
    intro i hi hi'
    obtain ⟨B0, -, huniq⟩ := hH.2 i
    exact hne ((huniq B ⟨(Finset.mem_filter.1 (Finset.mem_coe.1 hB)).1, (Finset.mem_inter.1 hi).2⟩).trans
      (huniq B' ⟨(Finset.mem_filter.1 (Finset.mem_coe.1 hB')).1, (Finset.mem_inter.1 hi').2⟩).symm)

theorem card_symmDiff_mod {α : Type} [DecidableEq α] (u v : Finset α) :
    (symmDiff u v).card % 2 = (u.card + v.card) % 2 := by
  have h1 := Finset.card_sdiff_add_card_inter u v
  have h2 := Finset.card_sdiff_add_card_inter v u
  rw [Finset.inter_comm] at h2
  have h3 : (symmDiff u v).card = (u \ v).card + (v \ u).card := by
    rw [symmDiff_def, Finset.sup_eq_union, Finset.card_union_of_disjoint disjoint_sdiff_sdiff]
  omega

theorem par {n : Nat} (y y0 B : Finset (Fin n)) :
    ((symmDiff y y0) ∩ B).card % 2 = ((y ∩ B).card + (y0 ∩ B).card) % 2 := by
  have e : (symmDiff y y0) ∩ B = symmDiff (y ∩ B) (y0 ∩ B) := inf_symmDiff_distrib_right y y0 B
  rw [e, card_symmDiff_mod]

theorem trace_sd {n : Nat} (y y0 X T T0 : Finset (Fin n)) (hy : y ∩ X = T) (hy0 : y0 ∩ X = T0) :
    symmDiff y y0 ∩ X = symmDiff T T0 := by
  have e : (symmDiff y y0) ∩ X = symmDiff (y ∩ X) (y0 ∩ X) := inf_symmDiff_distrib_right y y0 X
  rw [e, hy, hy0]

def w {n : Nat} (s : Finset (Fin n) → Bool) (y B : Finset (Fin n)) : Bool :=
  xor (decide ((y ∩ B).card % 2 = 1)) (s B)

theorem hits_iff_w {n : Nat} (H : Finset (Finset (Fin n))) (s : Finset (Fin n) → Bool)
    (y : Finset (Fin n)) : hits H s y ↔ ∀ B ∈ H, w s y B = false := by
  unfold hits w
  refine forall₂_congr (fun B _ => ?_)
  generalize decide ((y ∩ B).card % 2 = 1) = d
  generalize s B = e
  cases d <;> cases e <;> simp

theorem tog {n : Nat} (y : Finset (Fin n)) (i : Fin n) (B : Finset (Fin n)) :
    ((symmDiff y {i}) ∩ B).card % 2 = ((y ∩ B).card + (if i ∈ B then 1 else 0)) % 2 := by
  rw [par]
  by_cases h : i ∈ B
  · simp [Finset.singleton_inter_of_mem h, h]
  · simp [Finset.singleton_inter_of_notMem h, h]

theorem w_tog {n : Nat} (s : Finset (Fin n) → Bool) (y : Finset (Fin n)) (i : Fin n)
    (B : Finset (Fin n)) : w s (symmDiff y {i}) B = xor (w s y B) (decide (i ∈ B)) := by
  have h := tog y i B
  unfold w
  by_cases hi : i ∈ B
  · simp only [hi, if_true] at h
    rcases Nat.mod_two_eq_zero_or_one (y ∩ B).card with h1 | h1 <;>
      rcases Nat.mod_two_eq_zero_or_one ((symmDiff y {i}) ∩ B).card with h2 | h2 <;>
      first
        | (exfalso; omega)
        | (rw [h1, h2]; generalize s B = e; cases e <;> simp [hi])
  · simp only [hi, if_false] at h
    rcases Nat.mod_two_eq_zero_or_one (y ∩ B).card with h1 | h1 <;>
      rcases Nat.mod_two_eq_zero_or_one ((symmDiff y {i}) ∩ B).card with h2 | h2 <;>
      first
        | (exfalso; omega)
        | (rw [h1, h2]; generalize s B = e; cases e <;> simp [hi])

theorem exists_min {α : Type} (p : α → Prop) (m : α → Nat)
    (step : ∀ x, p x → m x ≠ 0 → ∃ x', p x' ∧ m x' < m x) :
    ∀ k x, p x → m x = k → ∃ x', p x' ∧ m x' = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro x hx hk
    by_cases h0 : m x = 0
    · exact ⟨x, hx, h0⟩
    · obtain ⟨x', hx', hlt⟩ := step x hx h0
      exact ih (m x') (hk ▸ hlt) x' hx' rfl

theorem card_decrease {α : Type} [DecidableEq α] (H : Finset α) (f f' : α → Prop)
    [DecidablePred f] [DecidablePred f'] (h : ∀ B ∈ H, f' B → f B) (B0 : α) (hB0 : B0 ∈ H)
    (h0 : f B0) (h0' : ¬ f' B0) : (H.filter f').card < (H.filter f).card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨B0, Finset.mem_filter.2 ⟨hB0, h0⟩, fun h => h0' (Finset.mem_filter.1 h).2⟩
  · intro B hB
    rw [Finset.mem_filter] at hB ⊢
    exact ⟨hB.1, h B hB.1 hB.2⟩

theorem zero_of_card {α : Type} (H : Finset α) (f : α → Prop) [DecidablePred f]
    (h : (H.filter f).card = 0) : ∀ B ∈ H, ¬ f B := by
  intro B hB hf
  rw [Finset.card_eq_zero] at h
  have : B ∈ H.filter f := Finset.mem_filter.2 ⟨hB, hf⟩
  rw [h] at this
  exact absurd this (Finset.notMem_empty B)

theorem blk_eq {n : Nat} {H : Finset (Finset (Fin n))} (hH : IsPartition H)
    {B B' : Finset (Fin n)} {i : Fin n} (hB : B ∈ H) (hB' : B' ∈ H) (hi : i ∈ B) (hi' : i ∈ B') :
    B = B' := by
  obtain ⟨B0, -, hu⟩ := hH.2 i
  exact (hu B ⟨hB, hi⟩).trans (hu B' ⟨hB', hi'⟩).symm

theorem exists_hits {n : Nat} (H : Finset (Finset (Fin n))) (hH : IsPartition H)
    (s : Finset (Fin n) → Bool) : ∃ y, hits H s y := by
  have key := exists_min (fun _ : Finset (Fin n) => True)
    (fun y => (H.filter (fun B => w s y B = true)).card) ?_ _ ∅ trivial rfl
  · obtain ⟨y, -, hy⟩ := key
    refine ⟨y, (hits_iff_w H s y).2 ?_⟩
    intro B hB
    have := zero_of_card H _ hy B hB
    simpa using this
  · intro y _ hm
    obtain ⟨B, hB⟩ := Finset.card_ne_zero.1 hm
    rw [Finset.mem_filter] at hB
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.2 (fun h => hH.1 (h ▸ hB.1))
    refine ⟨symmDiff y {i}, trivial, card_decrease H _ _ ?_ B hB.1 hB.2 ?_⟩
    · intro B' hB' hw
      rw [w_tog] at hw
      by_cases hiB : i ∈ B'
      · have e := blk_eq hH hB' hB.1 hiB hi
        subst e
        simp [hB.2, hi] at hw
      · simpa [hiB] using hw
    · rw [w_tog, hB.2]
      simp [hi]

theorem exists_part {n : Nat} (P Q : Finset (Finset (Fin n))) :
    ∀ k (U : Finset (Fin n)), U.card = k → U.Nonempty → closed P Q U →
      ∃ C, C ⊆ U ∧ IsPart P Q C := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro U hk hne hcl
    by_cases hp : IsPart P Q U
    · exact ⟨U, subset_rfl, hp⟩
    · have hex : ∃ D ∈ U.powerset, D.Nonempty ∧ closed P Q D ∧ D ≠ U := by
        by_contra hcon
        apply hp
        refine ⟨hne, hcl, fun D hD hDn hDc => ?_⟩
        by_contra hne'
        exact hcon ⟨D, hD, hDn, hDc, hne'⟩
      obtain ⟨D, hD, hDn, hDc, hDU⟩ := hex
      have hsub := Finset.mem_powerset.1 hD
      have hlt : D.card < k := hk ▸ Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hsub, hDU⟩)
      obtain ⟨C, hC, hCp⟩ := ih D.card hlt D rfl hDn hDc
      exact ⟨C, hC.trans hsub, hCp⟩

theorem even_wrong {n : Nat} (P Q : Finset (Finset (Fin n)))
    (hP : IsPartition P) (hQ : IsPartition Q) (a b : Finset (Fin n) → Bool)
    (y C : Finset (Fin n)) (hy : hits P a y) (hC : closed P Q C)
    (hbit : bit P Q a b (cmask P Q C) = 0) :
    ((Q.filter (fun B => B ⊆ C)).filter (fun B => w b y B = true)).card % 2 = 0 := by
  have p1 := part_parity P hP a y C hy (fun B hB => hC B (Finset.mem_union_left _ hB))
  have p2 := part_parity Q hQ (fun B => decide ((y ∩ B).card % 2 = 1)) y C (fun B _ => rfl)
    (fun B hB => hC B (Finset.mem_union_right _ hB))
  have x := card_filter_xor (Q.filter (fun B => B ⊆ C))
    (fun B => decide ((y ∩ B).card % 2 = 1)) b
  unfold bit cmask at hbit
  dsimp only at hbit x p2
  rw [Finset.inter_eq_left.2 (Finset.filter_subset _ P),
    Finset.inter_eq_left.2 (Finset.filter_subset _ Q)] at hbit
  unfold w
  omega

theorem improve {n : Nat} (P Q : Finset (Finset (Fin n)))
    (hP : IsPartition P) (hQ : IsPartition Q) (a b : Finset (Fin n) → Bool)
    (X : Finset (Fin n))
    (h : ∀ C : Finset (Fin n), IsPart P Q C → C ⊆ X → bit P Q a b (cmask P Q C) = 0)
    (y : Finset (Fin n)) (hy : hits P a y) (B0 : Finset (Fin n)) (hB0 : B0 ∈ Q)
    (hB0X : B0 ⊆ X) (hw0 : w b y B0 = true) :
    ∃ y', hits P a y' ∧ (Q.filter (fun B => B ⊆ X ∧ w b y' B = true)).card <
      (Q.filter (fun B => B ⊆ X ∧ w b y B = true)).card := by
  obtain ⟨S, hS⟩ : ∃ S : Finset (Finset (Fin n)), ∀ B, B ∈ S ↔ B ∈ Q ∧ ∃ y', hits P a y' ∧
      ∀ B' ∈ Q, w b y' B' = xor (w b y B') (xor (decide (B' = B0)) (decide (B' = B))) :=
    ⟨@Finset.filter _ _ (Classical.decPred _) Q, fun B => @Finset.mem_filter _ _ (Classical.decPred _) _ _⟩
  have hS0 : B0 ∈ S := (hS B0).2 ⟨hB0, y, hy, fun B' _ => by simp⟩
  have dec : ∀ B2 ∈ S, B2 ≠ B0 → (w b y B2 = true ∨ ¬ B2 ⊆ X) →
      ∃ y', hits P a y' ∧ (Q.filter (fun B => B ⊆ X ∧ w b y' B = true)).card <
        (Q.filter (fun B => B ⊆ X ∧ w b y B = true)).card := by
    intro B2 hB2 hne hor
    obtain ⟨hB2Q, y2, hy2, hw2⟩ := (hS B2).1 hB2
    refine ⟨y2, hy2, card_decrease Q _ _ ?_ B0 hB0 ⟨hB0X, hw0⟩ ?_⟩
    · rintro B' hB' ⟨hX, hw'⟩
      refine ⟨hX, ?_⟩
      rw [hw2 B' hB'] at hw'
      by_cases e0 : B' = B0
      · rw [e0]; exact hw0
      · by_cases e2 : B' = B2
        · rcases hor with h1 | h1
          · rw [e2]; exact h1
          · exact absurd (e2 ▸ hX) h1
        · simpa [e0, e2] using hw'
    · rintro ⟨_, hw'⟩
      rw [hw2 B0 hB0, hw0] at hw'
      simp [Ne.symm hne] at hw'
  by_contra hcon
  have hno : ∀ B2 ∈ S, B2 ≠ B0 → w b y B2 = false ∧ B2 ⊆ X := by
    intro B2 hB2 hne
    by_contra hh
    apply hcon
    apply dec B2 hB2 hne
    by_cases hx : B2 ⊆ X
    · left
      cases hwv : w b y B2
      · exact absurd ⟨hwv, hx⟩ hh
      · rfl
    · right; exact hx
  have hSQ : ∀ B ∈ S, B ∈ Q := fun B hB => ((hS B).1 hB).1
  have hUS : ∀ B ∈ Q, ∀ i ∈ B, i ∈ S.biUnion id → B ∈ S := by
    intro B hB i hi hiU
    obtain ⟨B', hB', hiB'⟩ := Finset.mem_biUnion.1 hiU
    have e := blk_eq hQ hB (hSQ B' hB') hi hiB'
    rw [e]; exact hB'
  have hUcl : closed P Q (S.biUnion id) := by
    intro B hB
    rcases Finset.mem_union.1 hB with hBP | hBQ
    · by_cases hd : Disjoint (S.biUnion id) B
      · left; exact hd
      · right
        rw [Finset.not_disjoint_iff] at hd
        obtain ⟨i, hiU, hiB⟩ := hd
        obtain ⟨Bi, hBi, hiBi⟩ := Finset.mem_biUnion.1 hiU
        obtain ⟨hBiQ, y1, hy1, hw1⟩ := (hS Bi).1 hBi
        intro j hj
        obtain ⟨Bj, ⟨hBjQ, hjBj⟩, -⟩ := hQ.2 j
        refine Finset.mem_biUnion.2 ⟨Bj, (hS Bj).2 ⟨hBjQ, symmDiff (symmDiff y1 {i}) {j}, ?_, ?_⟩, hjBj⟩
        · rw [hits_iff_w] at hy1 ⊢
          intro B' hB'
          rw [w_tog, w_tog, hy1 B' hB']
          have e : (i ∈ B') ↔ (j ∈ B') :=
            ⟨fun hi' => (blk_eq hP hBP hB' hiB hi') ▸ hj, fun hj' => (blk_eq hP hBP hB' hj hj') ▸ hiB⟩
          have dd : decide (i ∈ B') = decide (j ∈ B') := decide_eq_decide.2 e
          rw [dd]
          generalize decide (j ∈ B') = d
          cases d <;> rfl
        · intro B' hB'
          rw [w_tog, w_tog, hw1 B' hB']
          have e1 : (i ∈ B') ↔ B' = Bi :=
            ⟨fun hi' => blk_eq hQ hB' hBiQ hi' hiBi, fun e => e ▸ hiBi⟩
          have e2 : (j ∈ B') ↔ B' = Bj :=
            ⟨fun hj' => blk_eq hQ hB' hBjQ hj' hjBj, fun e => e ▸ hjBj⟩
          have d1 : decide (i ∈ B') = decide (B' = Bi) := decide_eq_decide.2 e1
          have d2 : decide (j ∈ B') = decide (B' = Bj) := decide_eq_decide.2 e2
          rw [d1, d2]
          generalize w b y B' = x
          generalize decide (B' = B0) = c0
          generalize decide (B' = Bi) = c1
          generalize decide (B' = Bj) = c2
          cases x <;> cases c0 <;> cases c1 <;> cases c2 <;> rfl
    · by_cases hBS : B ∈ S
      · right; exact fun i hi => Finset.mem_biUnion.2 ⟨B, hBS, hi⟩
      · left
        rw [Finset.disjoint_left]
        intro i hiU hiB
        exact hBS (hUS B hBQ i hiB hiU)
  have hne0 : ∀ B ∈ Q, B.Nonempty := fun B hB =>
    Finset.nonempty_iff_ne_empty.2 (fun e => hQ.1 (e ▸ hB))
  have hUne : (S.biUnion id).Nonempty := by
    obtain ⟨i, hi⟩ := hne0 B0 hB0
    exact ⟨i, Finset.mem_biUnion.2 ⟨B0, hS0, hi⟩⟩
  have hUX : S.biUnion id ⊆ X := by
    intro i hi
    obtain ⟨B, hB, hiB⟩ := Finset.mem_biUnion.1 hi
    by_cases e : B = B0
    · exact hB0X (e ▸ hiB)
    · exact (hno B hB e).2 hiB
  obtain ⟨C, hCU, hCp⟩ := exists_part P Q _ (S.biUnion id) rfl hUne hUcl
  obtain ⟨i, hiC⟩ := hCp.1
  obtain ⟨B1, ⟨hB1Q, hiB1⟩, -⟩ := hQ.2 i
  have hB1S := hUS B1 hB1Q i hiB1 (hCU hiC)
  have hB1C : B1 ⊆ C := by
    rcases hCp.2.1 B1 (Finset.mem_union_right _ hB1Q) with hd | hs
    · exact absurd hiB1 (Finset.disjoint_left.1 hd hiC)
    · exact hs
  obtain ⟨-, y1, hy1, hw1⟩ := (hS B1).1 hB1S
  have ev := even_wrong P Q hP hQ a b y1 C hy1 hCp.2.1 (h C hCp (hCU.trans hUX))
  have single : (Q.filter (fun B => B ⊆ C)).filter (fun B => w b y1 B = true) = {B1} := by
    ext B'
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hB'Q, hB'C⟩, hw'⟩
      obtain ⟨j, hj⟩ := hne0 B' hB'Q
      have hB'S := hUS B' hB'Q j hj (hCU (hB'C hj))
      rw [hw1 B' hB'Q] at hw'
      by_contra hne1
      by_cases e0 : B' = B0
      · rw [e0, hw0] at hw'
        rw [e0] at hne1
        simp [hne1] at hw'
      · rw [(hno B' hB'S e0).1] at hw'
        simp [e0, hne1] at hw'
    · intro e
      rw [e]
      refine ⟨⟨hB1Q, hB1C⟩, ?_⟩
      rw [hw1 B1 hB1Q]
      by_cases e0 : B1 = B0
      · rw [e0, hw0]; simp
      · rw [(hno B1 hB1S e0).1]; simp [e0]
  rw [single, Finset.card_singleton] at ev
  exact absurd ev (by decide)

theorem good_exists_of_bits {n : Nat} (P Q : Finset (Finset (Fin n)))
    (hP : IsPartition P) (hQ : IsPartition Q) (a b : Finset (Fin n) → Bool)
    (X : Finset (Fin n))
    (h : ∀ C : Finset (Fin n), IsPart P Q C → C ⊆ X → bit P Q a b (cmask P Q C) = 0) :
    ∃ T : Finset (Fin n), T ⊆ X ∧ good P Q a b X T := by
  obtain ⟨y0, hy0⟩ := exists_hits P hP a
  obtain ⟨y, hy, hm⟩ := exists_min (fun y => hits P a y)
    (fun y => (Q.filter (fun B => B ⊆ X ∧ w b y B = true)).card)
    (by
      intro y hy hm
      obtain ⟨B0, hB0⟩ := Finset.card_ne_zero.1 hm
      rw [Finset.mem_filter] at hB0
      exact improve P Q hP hQ a b X h y hy B0 hB0.1 hB0.2.1 hB0.2.2) _ y0 hy0 rfl
  have hyQ : ∀ B ∈ Q, B ⊆ X → w b y B = false := by
    intro B hB hBX
    have hz := zero_of_card Q _ hm B hB
    cases hwv : w b y B
    · rfl
    · exact absurd ⟨hBX, hwv⟩ hz
  obtain ⟨z, hz, hmz⟩ := exists_min (fun z : Finset (Fin n) => z ∩ X = y ∩ X)
    (fun z => (Q.filter (fun B => w b z B = true)).card)
    (by
      intro z hz hm
      obtain ⟨B, hB⟩ := Finset.card_ne_zero.1 hm
      rw [Finset.mem_filter] at hB
      have hBX : ¬ B ⊆ X := by
        intro hBX
        have e : z ∩ B = y ∩ B := by
          rw [← Finset.inter_eq_right.2 hBX, ← Finset.inter_assoc, ← Finset.inter_assoc, hz]
        have hw := hB.2
        unfold w at hw
        rw [e] at hw
        have hw' := hyQ B hB.1 hBX
        unfold w at hw'
        rw [hw'] at hw
        exact absurd hw (by decide)
      obtain ⟨i, hi, hiX⟩ := Finset.not_subset.1 hBX
      refine ⟨symmDiff z {i}, ?_, card_decrease Q _ _ ?_ B hB.1 hB.2 ?_⟩
      · have t := trace_sd z {i} X (z ∩ X) ∅ rfl (Finset.singleton_inter_of_notMem hiX)
        rw [t]
        exact (symmDiff_bot (z ∩ X)).trans hz
      · intro B' hB' hw
        rw [w_tog] at hw
        by_cases hiB : i ∈ B'
        · have e := blk_eq hQ hB' hB.1 hiB hi
          subst e
          simp [hB.2, hi] at hw
        · simpa [hiB] using hw
      · rw [w_tog, hB.2]
        simp [hi]) _ y rfl rfl
  have hzQ : hits Q b z := by
    rw [hits_iff_w]
    intro B hB
    have := zero_of_card Q _ hmz B hB
    simpa using this
  exact ⟨y ∩ X, Finset.inter_subset_right, ⟨y, rfl, hy⟩, ⟨z, hz, hzQ⟩⟩

theorem good_exists_iff {n : Nat} (P Q : Finset (Finset (Fin n)))
    (hP : IsPartition P) (hQ : IsPartition Q) (a b : Finset (Fin n) → Bool)
    (X : Finset (Fin n)) :
    (∃ T : Finset (Fin n), T ⊆ X ∧ good P Q a b X T) ↔
      ∀ C : Finset (Fin n), IsPart P Q C → C ⊆ X → bit P Q a b (cmask P Q C) = 0 := by
  refine ⟨?_, good_exists_of_bits P Q hP hQ a b X⟩
  rintro ⟨T, -, ⟨y, hy, h1⟩, ⟨z, hz, h2⟩⟩ C hC hCX
  have p1 := part_parity P hP a y C h1 (fun B hB => hC.2.1 B (Finset.mem_union_left _ hB))
  have p2 := part_parity Q hQ b z C h2 (fun B hB => hC.2.1 B (Finset.mem_union_right _ hB))
  have e : y ∩ C = z ∩ C := by
    rw [← Finset.inter_eq_right.2 hCX, ← Finset.inter_assoc, ← Finset.inter_assoc, hy, hz]
  rw [e] at p1
  unfold bit cmask
  dsimp only
  rw [Finset.inter_eq_left.2 (Finset.filter_subset _ P),
    Finset.inter_eq_left.2 (Finset.filter_subset _ Q)]
  omega

theorem solvable_iff {n : Nat} (P Q : Finset (Finset (Fin n)))
    (hP : IsPartition P) (hQ : IsPartition Q) (a b : Finset (Fin n) → Bool) :
    (∃ y : Finset (Fin n), hits P a y ∧ hits Q b y) ↔
      ∀ C : Finset (Fin n), IsPart P Q C → bit P Q a b (cmask P Q C) = 0 := by
  have key := good_exists_iff P Q hP hQ a b Finset.univ
  have e : (∃ y : Finset (Fin n), hits P a y ∧ hits Q b y) ↔
      (∃ T : Finset (Fin n), T ⊆ Finset.univ ∧ good P Q a b Finset.univ T) := by
    constructor
    · rintro ⟨y, h1, h2⟩
      exact ⟨y, Finset.subset_univ _, ⟨y, Finset.inter_univ y, h1⟩, ⟨y, Finset.inter_univ y, h2⟩⟩
    · rintro ⟨T, -, ⟨y, hy, h1⟩, ⟨z, hz, h2⟩⟩
      rw [Finset.inter_univ] at hy hz
      subst hy; subst hz
      exact ⟨_, h1, h2⟩
  rw [e, key]
  exact ⟨fun h C hC => h C hC (Finset.subset_univ _), fun h C hC _ => h C hC⟩

theorem hits_sd_zero {n : Nat} (H : Finset (Finset (Fin n))) (a : Finset (Fin n) → Bool)
    (y y0 : Finset (Fin n)) (h1 : hits H a y) (h2 : hits H a y0) :
    hits H (fun _ => false) (symmDiff y y0) := by
  intro B hB
  have e1 := h1 B hB
  have e2 := h2 B hB
  have p := par y y0 B
  cases h : a B <;> simp [h] at e1 e2 ⊢ <;> omega

theorem hits_sd_add {n : Nat} (H : Finset (Finset (Fin n))) (a : Finset (Fin n) → Bool)
    (w y0 : Finset (Fin n)) (h1 : hits H (fun _ => false) w) (h2 : hits H a y0) :
    hits H a (symmDiff w y0) := by
  intro B hB
  have e1 := h1 B hB
  have e2 := h2 B hB
  have p := par w y0 B
  cases h : a B <;> simp [h] at e1 e2 ⊢ <;> omega

theorem good_translate {n : Nat} (P Q : Finset (Finset (Fin n)))
    (a b : Finset (Fin n) → Bool)
    (X T₀ : Finset (Fin n)) (h₀ : good P Q a b X T₀) (T : Finset (Fin n)) :
    good P Q a b X T ↔
      good P Q (fun _ => false) (fun _ => false) X (symmDiff T T₀) := by
  obtain ⟨⟨y0, hy0, g1⟩, ⟨z0, hz0, g2⟩⟩ := h₀
  constructor
  · rintro ⟨⟨y, hy, h1⟩, ⟨z, hz, h2⟩⟩
    exact ⟨⟨symmDiff y y0, trace_sd y y0 X T T₀ hy hy0, hits_sd_zero P a y y0 h1 g1⟩,
      ⟨symmDiff z z0, trace_sd z z0 X T T₀ hz hz0, hits_sd_zero Q b z z0 h2 g2⟩⟩
  · rintro ⟨⟨y, hy, h1⟩, ⟨z, hz, h2⟩⟩
    refine ⟨⟨symmDiff y y0, ?_, hits_sd_add P a y y0 h1 g1⟩,
      ⟨symmDiff z z0, ?_, hits_sd_add Q b z z0 h2 g2⟩⟩
    · rw [trace_sd y y0 X _ T₀ hy hy0, symmDiff_symmDiff_cancel_right]
    · rw [trace_sd z z0 X _ T₀ hz hz0, symmDiff_symmDiff_cancel_right]

def pathOf {M : Type} (ask : List Nat → Option M) (v : Option M → Nat) (k : Nat) :
    List (Option M × Nat) :=
  (List.range k).foldl
    (fun (p : List (Option M × Nat)) _ =>
      let m := ask (p.map Prod.snd)
      p ++ [(m, v m)]) []

theorem pathOf_succ {M : Type} (ask : List Nat → Option M) (v : Option M → Nat) (k : Nat) :
    pathOf ask v (k + 1) =
      pathOf ask v k ++ [(ask ((pathOf ask v k).map Prod.snd),
        v (ask ((pathOf ask v k).map Prod.snd)))] := by
  simp [pathOf, List.range_succ, List.foldl_append]

theorem path_congr {M : Type} (ask : List Nat → Option M) (v v' : Option M → Nat) (k : Nat)
    (h : ∀ z ∈ pathOf ask v k, v' z.1 = v z.1) : pathOf ask v' k = pathOf ask v k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pathOf_succ] at h
    have ih' := ih (fun z hz => h z (List.mem_append_left _ hz))
    have hl := h _ (List.mem_append_right _ (List.mem_singleton_self _))
    rw [pathOf_succ, pathOf_succ, ih']
    exact congrArg (fun x => _ ++ [(_, x)]) hl

theorem sd_subset {n : Nat} (T T0 X : Finset (Fin n)) (h : T ⊆ X) (h0 : T0 ⊆ X) :
    symmDiff T T0 ⊆ X :=
  (symmDiff_le_sup : symmDiff T T0 ≤ T ⊔ T0).trans (Finset.union_subset h h0)

theorem count_eq {n : Nat} (X T0 : Finset (Fin n)) (p p' : Finset (Fin n) → Prop)
    [DecidablePred p] [DecidablePred p'] (hT0 : T0 ⊆ X)
    (h : ∀ T, p T ↔ p' (symmDiff T T0)) :
    (X.powerset.filter p).card = (X.powerset.filter p').card := by
  refine Finset.card_bij' (fun T _ => symmDiff T T0) (fun T _ => symmDiff T T0) ?_ ?_ ?_ ?_
  · intro T hT
    rw [Finset.mem_filter, Finset.mem_powerset] at hT ⊢
    exact ⟨sd_subset T T0 X hT.1 hT0, (h T).1 hT.2⟩
  · intro T hT
    rw [Finset.mem_filter, Finset.mem_powerset] at hT ⊢
    refine ⟨sd_subset T T0 X hT.1 hT0, (h _).2 ?_⟩
    rw [symmDiff_symmDiff_cancel_right]
    exact hT.2
  · intro T _
    exact symmDiff_symmDiff_cancel_right T0 T
  · intro T _
    exact symmDiff_symmDiff_cancel_right T0 T

theorem pathOf_length {M : Type} (ask : List Nat → Option M) (v : Option M → Nat) (k : Nat) :
    (pathOf ask v k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pathOf_succ, List.length_append, ih]; rfl

theorem pathOf_static {M : Type} (L : List M) (v : Option M → Nat) (k : Nat) :
    pathOf (fun l => L[l.length]?) v k = (List.range k).map (fun i => (L[i]?, v L[i]?)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pathOf_succ, List.range_succ, List.map_append, List.length_map, pathOf_length, ← ih]
    rfl

theorem filterMap_getElem {M : Type} (L : List M) (k : Nat) (hk : L.length ≤ k) :
    (List.range k).filterMap (fun i => L[i]?) = L := by
  induction L generalizing k with
  | nil => simp
  | cons x L ih =>
    cases k with
    | zero => simp at hk
    | succ k =>
      have h' : L.length ≤ k := by simpa using hk
      rw [List.range_succ_eq_map, List.filterMap_cons, List.filterMap_map]
      simp only [List.getElem?_cons_zero]
      congr 1
      exact ih k h'

theorem bit_lt {n : Nat} (P Q : Finset (Finset (Fin n))) (a b : Finset (Fin n) → Bool)
    (s : Finset (Finset (Fin n)) × Finset (Finset (Fin n))) : bit P Q a b s < 2 :=
  Nat.mod_lt _ (by decide)

theorem fm_none {α β : Type} (l : List β) :
    l.filterMap (fun _ : β => (none : Option α)) = [] := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [List.filterMap_cons_none rfl, ih]

theorem fm_left {α β : Type} (xs : List α) (ss : List β) :
    (xs.map Sum.inl ++ ss.map Sum.inr).filterMap Sum.getLeft? = xs := by
  rw [List.filterMap_append, List.filterMap_map, List.filterMap_map]
  have h1 : ((Sum.getLeft? : α ⊕ β → Option α) ∘ Sum.inl) = some := rfl
  have h2 : ((Sum.getLeft? : α ⊕ β → Option α) ∘ Sum.inr) = fun _ => none := rfl
  rw [h1, h2, List.filterMap_some, fm_none, List.append_nil]

theorem fm_right {α β : Type} (xs : List α) (ss : List β) :
    (xs.map Sum.inl ++ ss.map Sum.inr).filterMap Sum.getRight? = ss := by
  rw [List.filterMap_append, List.filterMap_map, List.filterMap_map]
  have h1 : ((Sum.getRight? : α ⊕ β → Option β) ∘ Sum.inr) = some := rfl
  have h2 : ((Sum.getRight? : α ⊕ β → Option β) ∘ Sum.inl) = fun _ => none := rfl
  rw [h1, h2, List.filterMap_some, fm_none, List.nil_append]

end PEqualNP.Outside.L_lib_1124

theorem PEqualNP.Outside.L_lib_1124 : ∀ (n : Nat) (P Q : Finset (Finset (Fin n))),
  (∀ H ∈ [P, Q], (∅ : Finset (Fin n)) ∉ H ∧
    ∀ i : Fin n, ∃! B : Finset (Fin n), B ∈ H ∧ i ∈ B) →
  let spaces := (Finset.univ : Finset (Finset (Fin n)))
  let closed := fun (C : Finset (Fin n)) =>
    ∀ B ∈ P ∪ Q, Disjoint C B ∨ B ⊆ C
  let parts := spaces.filter (fun C => C.Nonempty ∧ closed C ∧
    ∀ D ∈ C.powerset, D.Nonempty → closed D → D = C)
  let hits := fun (H : Finset (Finset (Fin n))) (s : Finset (Fin n) → Bool)
      (y : Finset (Fin n)) => ∀ B ∈ H, decide ((y ∩ B).card % 2 = 1) = s B
  let count := fun (a b : Finset (Fin n) → Bool) (X : Finset (Fin n)) =>
    (X.powerset.filter (fun T =>
      (∃ y ∈ spaces, y ∩ X = T ∧ hits P a y) ∧
      (∃ z ∈ spaces, z ∩ X = T ∧ hits Q b z))).card

  let Mask := Finset (Finset (Fin n)) × Finset (Finset (Fin n))
  let Move := Sum (Finset (Fin n)) Mask
  let bit := fun (a b : Finset (Fin n) → Bool) (s : Mask) =>
    (((s.1 ∩ P).filter (fun B => a B = true)).card +
     ((s.2 ∩ Q).filter (fun B => b B = true)).card) % 2
  let componentMask := fun (C : Finset (Fin n)) =>
    (P.filter (fun B => B ⊆ C), Q.filter (fun B => B ⊆ C))
  ∀ (windows : Finset (Finset (Fin n))) (masks : Finset Mask) (q t : Nat),
    (∃ (ask : List Nat → Option Move) (answer : List Nat → Bool),
      ∀ a b : Finset (Fin n) → Bool,
        let value := fun (m : Option Move) =>
          m.elim 0 (Sum.elim (count a b) (bit a b))
        let path := (List.range (q + t)).foldl
          (fun (p : List (Option Move × Nat)) _ =>
            let m := ask (p.map Prod.snd)
            p ++ [(m, value m)]) []
        let used := path.filterMap (fun z => z.1)
        (used.filterMap Sum.getLeft?).length ≤ q ∧
        (used.filterMap Sum.getRight?).length ≤ t ∧
        (∀ m ∈ used, Sum.elim (fun X => X ∈ windows) (fun s => s ∈ masks) m) ∧
        (answer (path.map Prod.snd) = true ↔ ∃ y ∈ spaces, hits P a y ∧ hits Q b y)) ↔
    ∃ (xs : List (Finset (Fin n))) (ss : List Mask),
      xs.length ≤ q ∧ ss.length ≤ t ∧ (∀ X ∈ xs, X ∈ windows) ∧
      (∀ s ∈ ss, s ∈ masks) ∧
      ∀ a b : Finset (Fin n) → Bool,
        (∀ s ∈ ss, bit a b s = 0) →
        (∀ C ∈ parts, (∃ X ∈ xs, C ⊆ X) → bit a b (componentMask C) = 0) →
        ∀ C ∈ parts, bit a b (componentMask C) = 0 := by
  intro n P Q hPQ spaces cl parts hts cnt Mask Move bt cm windows masks q t
  have hP : PEqualNP.Outside.L_lib_1124.IsPartition P := hPQ P (by simp)
  have hQ : PEqualNP.Outside.L_lib_1124.IsPartition Q := hPQ Q (by simp)
  have hpart : ∀ C, C ∈ parts ↔ PEqualNP.Outside.L_lib_1124.IsPart P Q C := fun C =>
    Finset.mem_filter.trans (and_iff_right (Finset.mem_univ _))
  have hsolv : ∀ a b, (∃ y ∈ spaces, hts P a y ∧ hts Q b y) ↔
      ∀ C ∈ parts, bt a b (cm C) = 0 := by
    intro a b
    have key := PEqualNP.Outside.L_lib_1124.solvable_iff P Q hP hQ a b
    constructor
    · rintro ⟨y, _, h⟩ C hC
      exact key.1 ⟨y, h⟩ C ((hpart C).1 hC)
    · intro h
      obtain ⟨y, hy⟩ := key.2 (fun C hC => h C ((hpart C).2 hC))
      exact ⟨y, Finset.mem_univ _, hy⟩
  have hgood : ∀ a b X T, ((∃ y ∈ spaces, y ∩ X = T ∧ hts P a y) ∧
      (∃ z ∈ spaces, z ∩ X = T ∧ hts Q b z)) ↔ PEqualNP.Outside.L_lib_1124.good P Q a b X T := by
    intro a b X T
    constructor
    · rintro ⟨⟨y, _, h⟩, ⟨z, _, h'⟩⟩
      exact ⟨⟨y, h⟩, ⟨z, h'⟩⟩
    · rintro ⟨⟨y, h⟩, ⟨z, h'⟩⟩
      exact ⟨⟨y, Finset.mem_univ _, h⟩, ⟨z, Finset.mem_univ _, h'⟩⟩
  have hcnt : ∀ a b X, (∀ C ∈ parts, C ⊆ X → bt a b (cm C) = 0) →
      cnt a b X = cnt (fun _ => false) (fun _ => false) X := by
    intro a b X h
    obtain ⟨T0, hT0, g0⟩ := (PEqualNP.Outside.L_lib_1124.good_exists_iff P Q hP hQ a b X).2
      (fun C hC hCX => h C ((hpart C).2 hC) hCX)
    apply PEqualNP.Outside.L_lib_1124.count_eq X T0 _ _ hT0
    intro T
    exact (hgood a b X T).trans ((PEqualNP.Outside.L_lib_1124.good_translate P Q a b X T0 g0 T).trans (hgood _ _ X _).symm)
  have hbit0 : ∀ s, bt (fun _ => false) (fun _ => false) s = 0 := by
    intro s
    show PEqualNP.Outside.L_lib_1124.bit P Q _ _ s = 0
    simp [PEqualNP.Outside.L_lib_1124.bit]
  constructor
  · rintro ⟨ask, answer, H⟩
    obtain ⟨h1, h2, h3, h4⟩ := H (fun _ => false) (fun _ => false)
    let v := fun (a b : Finset (Fin n) → Bool) (m : Option Move) =>
      m.elim 0 (Sum.elim (cnt a b) (bt a b))
    let f : Finset (Fin n) → Bool := fun _ => false
    let used := (PEqualNP.Outside.L_lib_1124.pathOf ask (v f f) (q + t)).filterMap (fun z => z.1)
    refine ⟨used.filterMap Sum.getLeft?, used.filterMap Sum.getRight?, h1, h2, ?_, ?_, ?_⟩
    · intro X hX
      obtain ⟨m, hm, hmX⟩ := List.mem_filterMap.1 hX
      cases m with
      | inl X' =>
        simp at hmX
        subst hmX
        exact h3 _ hm
      | inr s => simp at hmX
    · intro s hs
      obtain ⟨m, hm, hms⟩ := List.mem_filterMap.1 hs
      cases m with
      | inl X' => simp at hms
      | inr s' =>
        simp at hms
        subst hms
        exact h3 _ hm
    · intro a b hss hxs
      have hv : ∀ z ∈ PEqualNP.Outside.L_lib_1124.pathOf ask (v f f) (q + t), v a b z.1 = v f f z.1 := by
        rintro ⟨m, k⟩ hz
        cases m with
        | none => rfl
        | some m =>
          have hu : m ∈ used := List.mem_filterMap.2 ⟨(some m, k), hz, rfl⟩
          cases m with
          | inl X =>
            show cnt a b X = cnt f f X
            apply hcnt
            intro C hC hCX
            exact hxs C hC ⟨X, List.mem_filterMap.2 ⟨Sum.inl X, hu, rfl⟩, hCX⟩
          | inr s =>
            show bt a b s = bt f f s
            rw [hbit0, hss s (List.mem_filterMap.2 ⟨Sum.inr s, hu, rfl⟩)]
      have hp := PEqualNP.Outside.L_lib_1124.path_congr ask (v f f) (v a b) (q + t) hv
      obtain ⟨-, -, -, g4⟩ := H a b
      have g4' : answer ((PEqualNP.Outside.L_lib_1124.pathOf ask (v a b) (q + t)).map Prod.snd) = true ↔
          ∃ y ∈ spaces, hts P a y ∧ hts Q b y := g4
      rw [hp] at g4'
      have e0 : ∃ y ∈ spaces, hts P f y ∧ hts Q f y := by
        refine ⟨∅, Finset.mem_univ _, ?_, ?_⟩
        · intro B _
          show decide (((∅ : Finset (Fin n)) ∩ B).card % 2 = 1) = false
          simp
        · intro B _
          show decide (((∅ : Finset (Fin n)) ∩ B).card % 2 = 1) = false
          simp
      exact (hsolv a b).1 (g4'.1 (h4.2 e0))
  · rintro ⟨xs, ss, hxq, hst, hxw, hsm, hstat⟩
    let v := fun (a b : Finset (Fin n) → Bool) (m : Option Move) =>
      m.elim 0 (Sum.elim (cnt a b) (bt a b))
    let L : List Move := xs.map Sum.inl ++ ss.map Sum.inr
    have hLlen : L.length ≤ q + t := by
      simp only [L, List.length_append, List.length_map]; omega
    let ask : List Nat → Option Move := fun l => L[l.length]?
    let resp := fun (a b : Finset (Fin n) → Bool) =>
      (PEqualNP.Outside.L_lib_1124.pathOf ask (v a b) (q + t)).map Prod.snd
    have hused : ∀ a b, (PEqualNP.Outside.L_lib_1124.pathOf ask (v a b) (q + t)).filterMap (fun z => z.1) = L := by
      intro a b
      rw [PEqualNP.Outside.L_lib_1124.pathOf_static L (v a b) (q + t), List.filterMap_map]
      exact PEqualNP.Outside.L_lib_1124.filterMap_getElem L (q + t) hLlen
    have hLl : L.filterMap Sum.getLeft? = xs := PEqualNP.Outside.L_lib_1124.fm_left xs ss
    have hLr : L.filterMap Sum.getRight? = ss := PEqualNP.Outside.L_lib_1124.fm_right xs ss
    have hcntpos : ∀ a b X, cnt a b X ≠ 0 ↔ ∀ C ∈ parts, C ⊆ X → bt a b (cm C) = 0 := by
      intro a b X
      rw [Finset.card_ne_zero]
      constructor
      · rintro ⟨T, hT⟩ C hC hCX
        rw [Finset.mem_filter, Finset.mem_powerset] at hT
        exact (PEqualNP.Outside.L_lib_1124.good_exists_iff P Q hP hQ a b X).1 ⟨T, hT.1, (hgood a b X T).1 hT.2⟩ C
          ((hpart C).1 hC) hCX
      · intro h
        obtain ⟨T, hT, g⟩ := (PEqualNP.Outside.L_lib_1124.good_exists_iff P Q hP hQ a b X).2
          (fun C hC hCX => h C ((hpart C).2 hC) hCX)
        exact ⟨T, Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hT, (hgood a b X T).2 g⟩⟩
    have hresp : ∀ a b a' b', resp a' b' = resp a b → ∀ m ∈ L, v a' b' (some m) = v a b (some m) := by
      intro a b a' b' h m hm
      obtain ⟨i, hi, hiL⟩ := List.getElem_of_mem hm
      have h' : (List.range (q + t)).map (fun i => v a' b' L[i]?) =
          (List.range (q + t)).map (fun i => v a b L[i]?) := by
        have e := h
        simp only [resp] at e
        rw [PEqualNP.Outside.L_lib_1124.pathOf_static L (v a' b') (q + t), PEqualNP.Outside.L_lib_1124.pathOf_static L (v a b) (q + t),
          List.map_map, List.map_map] at e
        exact e
      have h'' := List.map_inj_left.1 h' i (List.mem_range.2 (by omega))
      simp only [List.getElem?_eq_getElem hi, hiL] at h''
      exact h''
    have hkey : ∀ a b a' b', resp a' b' = resp a b →
        (∀ C ∈ parts, bt a' b' (cm C) = 0) → ∀ C ∈ parts, bt a b (cm C) = 0 := by
      intro a b a' b' h h0
      have hm := hresp a b a' b' h
      have hx := PEqualNP.Outside.L_lib_1124.bit_xor P Q a b a' b'
      have hall := hstat (fun B => xor (a B) (a' B)) (fun B => xor (b B) (b' B)) ?_ ?_
      · intro C hC
        have e1 := hall C hC
        have e2 := hx (cm C)
        have e3 := h0 C hC
        have e4 := PEqualNP.Outside.L_lib_1124.bit_lt P Q a b (cm C)
        change PEqualNP.Outside.L_lib_1124.bit P Q _ _ (cm C) = 0 at e1
        change PEqualNP.Outside.L_lib_1124.bit P Q a' b' (cm C) = 0 at e3
        change PEqualNP.Outside.L_lib_1124.bit P Q a b (cm C) = 0
        omega
      · intro s hs
        have e2 := hx s
        have e3 : PEqualNP.Outside.L_lib_1124.bit P Q a' b' s = PEqualNP.Outside.L_lib_1124.bit P Q a b s :=
          hm (Sum.inr s) (List.mem_append_right _ (List.mem_map_of_mem hs))
        have e4 := PEqualNP.Outside.L_lib_1124.bit_lt P Q a b s
        change PEqualNP.Outside.L_lib_1124.bit P Q _ _ s = 0
        omega
      · rintro C hC ⟨X, hX, hCX⟩
        have e2 := hx (cm C)
        have e3 := h0 C hC
        have e5 : cnt a' b' X = cnt a b X :=
          hm (Sum.inl X) (List.mem_append_left _ (List.mem_map_of_mem hX))
        have e6 : cnt a b X ≠ 0 := by
          rw [← e5]
          exact (hcntpos a' b' X).2 (fun C hC _ => h0 C hC)
        have e7 := (hcntpos a b X).1 e6 C hC hCX
        change PEqualNP.Outside.L_lib_1124.bit P Q a b (cm C) = 0 at e7
        change PEqualNP.Outside.L_lib_1124.bit P Q a' b' (cm C) = 0 at e3
        change PEqualNP.Outside.L_lib_1124.bit P Q _ _ (cm C) = 0
        omega
    refine ⟨ask, fun l => @decide (∃ a b, resp a b = l ∧ ∃ y ∈ spaces, hts P a y ∧ hts Q b y)
      (Classical.propDecidable _), ?_⟩
    intro a b
    refine ⟨?_, ?_, ?_, ?_⟩
    · show (((PEqualNP.Outside.L_lib_1124.pathOf ask (v a b) (q + t)).filterMap (fun z => z.1)).filterMap
        Sum.getLeft?).length ≤ q
      rw [hused, hLl]; exact hxq
    · show (((PEqualNP.Outside.L_lib_1124.pathOf ask (v a b) (q + t)).filterMap (fun z => z.1)).filterMap
        Sum.getRight?).length ≤ t
      rw [hused, hLr]; exact hst
    · show ∀ m ∈ (PEqualNP.Outside.L_lib_1124.pathOf ask (v a b) (q + t)).filterMap (fun z => z.1),
        Sum.elim (fun X => X ∈ windows) (fun s => s ∈ masks) m
      rw [hused]
      intro m hm
      rcases List.mem_append.1 hm with h | h
      · obtain ⟨X, hX, rfl⟩ := List.mem_map.1 h
        exact hxw X hX
      · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 h
        exact hsm s hs
    · show (@decide (∃ a' b', resp a' b' = resp a b ∧ ∃ y ∈ spaces, hts P a' y ∧ hts Q b' y)
        (Classical.propDecidable _)) = true ↔ ∃ y ∈ spaces, hts P a y ∧ hts Q b y
      rw [@decide_eq_true_iff _ (Classical.propDecidable _)]
      constructor
      · rintro ⟨a', b', hr, hs⟩
        exact (hsolv a b).2 (hkey a b a' b' hr ((hsolv a' b').1 hs))
      · intro hs
        exact ⟨a, b, rfl, hs⟩

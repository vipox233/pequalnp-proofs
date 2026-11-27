import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_337_aux

open PEqualNP.ProofComplexity

abbrev RawType {n : ℕ} (w : Fin n → ℕ) := (i : Fin n) × Fin (w i)

def blockParity {m : ℕ} (f : Fin m → Bool) : Bool :=
  decide (Odd ((Finset.univ : Finset (Fin m)).filter (fun j => f j = true)).card)

def parity {n : ℕ} {w : Fin n → ℕ} (y : RawType w → Bool) (i : Fin n) : Bool :=
  decide (Odd ((Finset.univ : Finset (Fin (w i))).filter (fun j => y ⟨i, j⟩ = true)).card)

def liftAx {n : ℕ} {w : Fin n → ℕ}
    (F : Set (Clause (Fin n))) (A : Clause (RawType w)) : Prop :=
  ∃ C ∈ F, ∃ y : RawType w → Bool, (∀ lit ∈ C, parity y lit.1 ≠ lit.2) ∧
    A = ((Finset.univ : Finset (RawType w)).filter (fun b => b.1 ∈ C.image Prod.fst)).image
      (fun b => (b, !(y b)))

def shape (N J : Finset (List Bool)) : Prop :=
  [] ∈ N ∧ J ⊆ N ∧
  (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
  ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N

def join (a b : ℕ) : ℕ := if a = b then a + 1 else max a b

def refutes {n : ℕ} {w : Fin n → ℕ} (F : Set (Clause (Fin n))) (H s : ℕ) : Prop :=
  ∃ (N J : Finset (List Bool)) (line : List Bool → Clause (RawType w))
    (r : List Bool → ℕ), shape N J ∧ line [] = ∅ ∧ r [] ≤ s ∧ (∀ p ∈ N, p.length ≤ H) ∧
    (∀ p ∈ N \ J, liftAx F (line p) ∧ r p = 0) ∧
    ∀ p ∈ J, IsResolvent (line (p ++ [false])) (line (p ++ [true])) (line p) ∧
      r p = join (r (p ++ [false])) (r (p ++ [true]))

def F_path (n : ℕ) : Set (Clause (Fin n)) := {C | ∃ e : Fin (n + 1),
  C = (((Finset.univ : Finset (Fin n)).filter (fun v => v.val + 1 = e.val)).image
    (fun v => (v, false))) ∪ (((Finset.univ : Finset (Fin n)).filter (fun v => v.val = e.val)).image
    (fun v => (v, true)))}

def feasible (n : ℕ) (w : Fin n → ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ → Prop := Nat.rec
  (fun i j _ _ => i = j)
  (fun _ prev i j H s => i = j ∨ ∃ v : Fin n, i ≤ v.val ∧ v.val < j ∧ w v ≤ H ∧
    ∃ a b : ℕ, (w v - 1) + join a b ≤ s ∧ prev i v.val (H - w v) a ∧ prev (v.val + 1) j (H - w v) b)

lemma join_comm (a b : ℕ) : join a b = join b a := by
  unfold join
  split_ifs <;> omega

lemma join_mono {a a' b b' : ℕ} (ha : a ≤ a') (hb : b ≤ b') : join a b ≤ join a' b' := by
  unfold join
  split_ifs <;> omega

lemma le_join_left (a b : ℕ) : a ≤ join a b := by
  unfold join; split_ifs <;> omega

lemma le_join_right (a b : ℕ) : b ≤ join a b := by
  unfold join; split_ifs <;> omega

lemma join_add_le (a b u v : ℕ) : join (a + u) (b + v) ≤ join a b + u + v := by
  unfold join
  split_ifs <;> omega

lemma join_succ_le (a b : ℕ) : a + 1 ≤ join a b ∨ b + 1 ≤ join a b := by
  unfold join
  split_ifs <;> omega

lemma feasible_succ {n : ℕ} {w : Fin n → ℕ} :
    ∀ (k i j H s : ℕ), feasible n w k i j H s → feasible n w (k + 1) i j H s := by
  intro k
  induction k with
  | zero =>
    intro i j H s h
    change i = j at h
    left; exact h
  | succ k ih =>
    intro i j H s h
    rcases h with rfl | ⟨v, hiv, hvj, hwH, a, b, hs, hL, hR⟩
    · left; rfl
    · right; exact ⟨v, hiv, hvj, hwH, a, b, hs, ih _ _ _ _ hL, ih _ _ _ _ hR⟩

lemma feasible_mono_fuel {n : ℕ} {w : Fin n → ℕ} {k k' : ℕ} (hk : k ≤ k') :
    ∀ {i j H s : ℕ}, feasible n w k i j H s → feasible n w k' i j H s := by
  induction hk with
  | refl => intro _ _ _ _ h; exact h
  | @step m _ ih => intro i j H s h; exact feasible_succ _ _ _ _ _ (ih h)

lemma shape_leaf : shape {[]} ∅ := by
  refine ⟨by simp, by simp, ?_, ?_⟩
  · intro p b h
    simp only [Finset.mem_singleton] at h
    exact absurd (congrArg List.length h) (by simp)
  · intro p hp
    simp at hp

lemma shape_combine {N0 J0 N1 J1 : Finset (List Bool)}
    (h0 : shape N0 J0) (h1 : shape N1 J1) :
    shape (insert [] (N0.image (false :: ·) ∪ N1.image (true :: ·)))
      (insert [] (J0.image (false :: ·) ∪ J1.image (true :: ·))) := by
  refine ⟨Finset.mem_insert_self _ _, ?_, ?_, ?_⟩
  · intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      rcases Finset.mem_union.mp hp with hp | hp
      · rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
        exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (h0.2.1 hq))
      · rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
        exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (h1.2.1 hq))
  · intro p b hp
    rcases Finset.mem_insert.mp hp with h_eq | hp
    · exact absurd (congrArg List.length h_eq) (by simp)
    · rcases Finset.mem_union.mp hp with hp | hp
      · rcases Finset.mem_image.mp hp with ⟨q, hq, h_eq⟩
        cases p with
        | nil => exact Finset.mem_insert_self _ _
        | cons c p' =>
          simp only [List.cons_append, List.cons.injEq] at h_eq
          rcases h_eq with ⟨rfl, rfl⟩
          apply Finset.mem_insert_of_mem
          exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (h0.2.2.1 p' b hq))
      · rcases Finset.mem_image.mp hp with ⟨q, hq, h_eq⟩
        cases p with
        | nil => exact Finset.mem_insert_self _ _
        | cons c p' =>
          simp only [List.cons_append, List.cons.injEq] at h_eq
          rcases h_eq with ⟨rfl, rfl⟩
          apply Finset.mem_insert_of_mem
          exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (h1.2.2.1 p' b hq))
  · intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · constructor
      · apply Finset.mem_insert_of_mem
        exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ h0.1)
      · apply Finset.mem_insert_of_mem
        exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ h1.1)
    · rcases Finset.mem_union.mp hp with hp | hp
      · rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
        constructor <;> apply Finset.mem_insert_of_mem <;> apply Finset.mem_union_left <;>
          apply Finset.mem_image_of_mem
        · exact (h0.2.2.2 q hq).1
        · exact (h0.2.2.2 q hq).2
      · rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
        constructor <;> apply Finset.mem_insert_of_mem <;> apply Finset.mem_union_right <;>
          apply Finset.mem_image_of_mem
        · exact (h1.2.2.2 q hq).1
        · exact (h1.2.2.2 q hq).2

lemma disjoint_cons_images (S0 S1 : Finset (List Bool)) :
    Disjoint (S0.image (false :: ·)) (S1.image (true :: ·)) := by
  rw [Finset.disjoint_left]
  intro p h0 h1
  rcases Finset.mem_image.mp h0 with ⟨q0, _, rfl⟩
  rcases Finset.mem_image.mp h1 with ⟨q1, _, h⟩
  exact Bool.noConfusion (List.cons.inj h).1

lemma sdiff_combine {N0 J0 N1 J1 : Finset (List Bool)}
    (_h0 : [] ∈ N0) (_h1 : [] ∈ N1) :
    insert [] (N0.image (false :: ·) ∪ N1.image (true :: ·)) \
      insert [] (J0.image (false :: ·) ∪ J1.image (true :: ·)) =
    (N0 \ J0).image (false :: ·) ∪ (N1 \ J1).image (true :: ·) := by
  ext p
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨rfl | (⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩), hnot⟩
    · exfalso; apply hnot; left; rfl
    · left; refine ⟨q, ⟨hq, fun hqJ => hnot (Or.inr (Or.inl ⟨q, hqJ, rfl⟩))⟩, rfl⟩
    · right; refine ⟨q, ⟨hq, fun hqJ => hnot (Or.inr (Or.inr ⟨q, hqJ, rfl⟩))⟩, rfl⟩
  · rintro (⟨q, ⟨hqN, hqJ⟩, rfl⟩ | ⟨q, ⟨hqN, hqJ⟩, rfl⟩)
    · refine ⟨Or.inr (Or.inl ⟨q, hqN, rfl⟩), ?_⟩
      rintro (h | ⟨q', hq', h⟩ | ⟨q', _, h⟩)
      · cases h
      · rcases List.cons.inj h with ⟨_, rfl⟩; exact hqJ hq'
      · exact Bool.noConfusion (List.cons.inj h).1
    · refine ⟨Or.inr (Or.inr ⟨q, hqN, rfl⟩), ?_⟩
      rintro (h | ⟨q', _, h⟩ | ⟨q', hq', h⟩)
      · cases h
      · exact Bool.noConfusion (List.cons.inj h).1
      · rcases List.cons.inj h with ⟨_, rfl⟩; exact hqJ hq'

def blockLit {n : ℕ} {w : Fin n → ℕ} (v : Fin n) (f : Fin (w v) → Bool) :
    Clause (RawType w) :=
  (Finset.univ : Finset (Fin (w v))).image (fun j => (⟨v, j⟩, !(f j)))

def bndClause {n : ℕ} {w : Fin n → ℕ} (i j : ℕ)
    (yL : ∀ (_hi : 0 < i) (hin : i - 1 < n), Fin (w ⟨i - 1, hin⟩) → Bool)
    (yR : ∀ (hj : j < n), Fin (w ⟨j, hj⟩) → Bool) : Clause (RawType w) :=
  (if h : 0 < i ∧ i - 1 < n then blockLit ⟨i - 1, h.2⟩ (yL h.1 h.2) else ∅) ∪
  (if h : j < n then blockLit ⟨j, h⟩ (yR h) else ∅)

def Derivable {n : ℕ} {w : Fin n → ℕ} (F : Set (Clause (Fin n)))
    (H s : ℕ) (C : Clause (RawType w)) : Prop :=
  ∃ (N J : Finset (List Bool)) (line : List Bool → Clause (RawType w)) (r : List Bool → ℕ),
    shape N J ∧ line [] = C ∧ r [] ≤ s ∧ (∀ p ∈ N, p.length ≤ H) ∧
    (∀ p ∈ N \ J, liftAx F (line p) ∧ r p = 0) ∧
    ∀ p ∈ J, IsResolvent (line (p ++ [false])) (line (p ++ [true])) (line p) ∧
      r p = join (r (p ++ [false])) (r (p ++ [true]))

lemma derivable_combine {n : ℕ} {w : Fin n → ℕ} {F : Set (Clause (Fin n))}
    {H0 H1 s0 s1 : ℕ} {C0 C1 R : Clause (RawType w)}
    (hres : IsResolvent C0 C1 R)
    (h0 : Derivable F H0 s0 C0) (h1 : Derivable F H1 s1 C1) :
    Derivable F (1 + max H0 H1) (join s0 s1) R := by
  rcases h0 with ⟨N0, J0, line0, r0, hsh0, hrt0, hr0, hlen0, hax0, hres0⟩
  rcases h1 with ⟨N1, J1, line1, r1, hsh1, hrt1, hr1, hlen1, hax1, hres1⟩
  let N := insert [] (N0.image (false :: ·) ∪ N1.image (true :: ·))
  let J := insert [] (J0.image (false :: ·) ∪ J1.image (true :: ·))
  let line : List Bool → Clause (RawType w) := fun p => match p with
    | [] => R
    | false :: q => line0 q
    | true :: q => line1 q
  let r : List Bool → ℕ := fun p => match p with
    | [] => join (r0 []) (r1 [])
    | false :: q => r0 q
    | true :: q => r1 q
  refine ⟨N, J, line, r, shape_combine hsh0 hsh1, rfl, join_mono hr0 hr1, ?_, ?_, ?_⟩
  · intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · simp
    · rcases Finset.mem_union.mp hp with hp | hp
      · rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
        have := hlen0 q hq; simp; omega
      · rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
        have := hlen1 q hq; simp; omega
  · intro p hp
    rw [sdiff_combine hsh0.1 hsh1.1] at hp
    rcases Finset.mem_union.mp hp with hp | hp
    · rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
      exact hax0 q hq
    · rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
      exact hax1 q hq
  · intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · refine ⟨?_, rfl⟩
      simpa [line, hrt0, hrt1] using hres
    · rcases Finset.mem_union.mp hp with hp | hp
      · rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
        exact hres0 q hq
      · rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
        exact hres1 q hq

lemma derivable_mono {n : ℕ} {w : Fin n → ℕ} {F : Set (Clause (Fin n))}
    {H H' s s' : ℕ} {C : Clause (RawType w)} (hH : H ≤ H') (hs : s ≤ s')
    (h : Derivable F H s C) : Derivable F H' s' C := by
  rcases h with ⟨N, J, line, r, hsh, hrt, hr, hlen, hax, hres⟩
  exact ⟨N, J, line, r, hsh, hrt, le_trans hr hs, fun p hp => le_trans (hlen p hp) hH, hax, hres⟩

def prefixClause {n : ℕ} {w : Fin n → ℕ} (v : Fin n) (d : ℕ) (f : Fin (w v) → Bool) :
    Clause (RawType w) :=
  ((Finset.univ : Finset (Fin (w v))).filter (fun j => j.val < d)).image (fun j => (⟨v, j⟩, !(f j)))

lemma prefixClause_zero {n : ℕ} {w : Fin n → ℕ} (v : Fin n) (f : Fin (w v) → Bool) :
    prefixClause v 0 f = ∅ := by
  simp [prefixClause]

lemma prefixClause_full {n : ℕ} {w : Fin n → ℕ} (v : Fin n) (f : Fin (w v) → Bool) :
    prefixClause v (w v) f = blockLit v f := by
  unfold prefixClause blockLit
  congr 1
  ext j
  simp

lemma isResolvent_prefixClause {n : ℕ} {w : Fin n → ℕ} (v : Fin n) (d : ℕ) (hd : d < w v)
    (extraL extraR : Clause (RawType w))
    (hexL : ∀ l ∈ extraL, l.1.1 ≠ v) (hexR : ∀ l ∈ extraR, l.1.1 ≠ v)
    (f : Fin (w v) → Bool) :
    IsResolvent
      (extraL ∪ prefixClause v (d + 1) (Function.update f ⟨d, hd⟩ false))
      (extraR ∪ prefixClause v (d + 1) (Function.update f ⟨d, hd⟩ true))
      ((extraL ∪ extraR) ∪ prefixClause v d f) := by
  refine ⟨⟨v, ⟨d, hd⟩⟩, ?_, ?_, ?_⟩
  · apply Finset.mem_union_right
    rw [prefixClause, Finset.mem_image]
    refine ⟨⟨d, hd⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.lt_succ_self d⟩, ?_⟩
    simp
  · apply Finset.mem_union_right
    rw [prefixClause, Finset.mem_image]
    refine ⟨⟨d, hd⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.lt_succ_self d⟩, ?_⟩
    simp
  · ext lit
    constructor
    · intro h
      rw [Finset.mem_union] at h
      rcases h with hLR | hP
      · rw [Finset.mem_union] at hLR
        rcases hLR with hL | hR
        · apply Finset.mem_union_left
          rw [Finset.mem_erase]
          refine ⟨fun heq => hexL lit hL (congrArg (fun x => x.1.1) heq), Finset.mem_union_left _ hL⟩
        · apply Finset.mem_union_right
          rw [Finset.mem_erase]
          refine ⟨fun heq => hexR lit hR (congrArg (fun x => x.1.1) heq), Finset.mem_union_left _ hR⟩
      · rw [prefixClause, Finset.mem_image] at hP
        rcases hP with ⟨⟨j, hj⟩, hjd, hlit⟩
        rw [Finset.mem_filter] at hjd
        have hne : (⟨j, hj⟩ : Fin (w v)) ≠ ⟨d, hd⟩ := by
          intro heq; have hval : j = d := congrArg Fin.val heq; dsimp only at hjd; omega
        apply Finset.mem_union_left
        rw [Finset.mem_erase]
        refine ⟨?_, Finset.mem_union_right _ ?_⟩
        · intro heq
          rw [← hlit] at heq
          have hfst : (⟨v, ⟨j, hj⟩⟩ : RawType w) = ⟨v, ⟨d, hd⟩⟩ := congrArg Prod.fst heq
          exact hne (by simpa using hfst)
        · rw [prefixClause, Finset.mem_image]
          refine ⟨⟨j, hj⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.lt_succ_of_lt hjd.2⟩, ?_⟩
          rw [Function.update_of_ne hne]
          exact hlit
    · intro h
      rw [Finset.mem_union] at h
      rcases h with h | h
      · rw [Finset.mem_erase, Finset.mem_union] at h
        rcases h with ⟨h_ne, hL | hP⟩
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ hL)
        · rw [prefixClause, Finset.mem_image] at hP
          rcases hP with ⟨⟨j, hj⟩, hjd, hlit⟩
          rw [Finset.mem_filter] at hjd
          have hne : (⟨j, hj⟩ : Fin (w v)) ≠ ⟨d, hd⟩ := by
            intro heq; apply h_ne; rw [← hlit, heq]; simp
          have hlt : j < d := by have : j ≠ d := fun h => hne (Fin.ext h); dsimp only at hjd; omega
          apply Finset.mem_union_right
          rw [prefixClause, Finset.mem_image]
          refine ⟨⟨j, hj⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩, ?_⟩
          rw [Function.update_of_ne hne] at hlit
          exact hlit
      · rw [Finset.mem_erase, Finset.mem_union] at h
        rcases h with ⟨h_ne, hR | hP⟩
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ hR)
        · rw [prefixClause, Finset.mem_image] at hP
          rcases hP with ⟨⟨j, hj⟩, hjd, hlit⟩
          rw [Finset.mem_filter] at hjd
          have hne : (⟨j, hj⟩ : Fin (w v)) ≠ ⟨d, hd⟩ := by
            intro heq; apply h_ne; rw [← hlit, heq]; simp
          have hlt : j < d := by have : j ≠ d := fun h => hne (Fin.ext h); dsimp only at hjd; omega
          apply Finset.mem_union_right
          rw [prefixClause, Finset.mem_image]
          refine ⟨⟨j, hj⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩, ?_⟩
          rw [Function.update_of_ne hne] at hlit
          exact hlit

lemma blockParity_update_not {m : ℕ} (f : Fin m → Bool) (j : Fin m) :
    blockParity (Function.update f j true) = !(blockParity (Function.update f j false)) := by
  unfold blockParity
  let s0 := (Finset.univ : Finset (Fin m)).filter (fun t => Function.update f j false t = true)
  let s1 := (Finset.univ : Finset (Fin m)).filter (fun t => Function.update f j true t = true)
  have hj0 : j ∉ s0 := by simp [s0]
  have hs1 : s1 = insert j s0 := by
    ext t
    simp only [s1, s0, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases h : t = j
    · subst h; simp
    · simp [h]
  have hcard : s1.card = s0.card + 1 := by
    rw [hs1, Finset.card_insert_of_notMem hj0]
  change decide (Odd s1.card) = !decide (Odd s0.card)
  rw [hcard]
  by_cases ho : Odd s0.card
  · have hno : ¬ Odd (s0.card + 1) := by
      rcases ho with ⟨k, hk⟩; intro ⟨l, hl⟩; omega
    simp [ho, hno]
  · have ho1 : Odd (s0.card + 1) := by
      rw [Nat.not_odd_iff_even] at ho; rcases ho with ⟨k, hk⟩; exact ⟨k, by omega⟩
    simp [ho, ho1]

lemma expand_block_aux {n : ℕ} {w : Fin n → ℕ} (F : Set (Clause (Fin n)))
    (v : Fin n) (extraL extraR : Clause (RawType w))
    (hexL : ∀ l ∈ extraL, l.1.1 ≠ v) (hexR : ∀ l ∈ extraR, l.1.1 ≠ v)
    (H a b : ℕ)
    (hL : ∀ f : Fin (w v) → Bool, blockParity f = false →
      Derivable F H a (extraL ∪ blockLit v f))
    (hR : ∀ f : Fin (w v) → Bool, blockParity f = true →
      Derivable F H b (extraR ∪ blockLit v f)) :
    ∀ (m : ℕ) (_hm : m ≤ w v) (_hm_pos : 0 < m) (f : Fin (w v) → Bool),
      Derivable F (H + m) ((m - 1) + join a b)
        ((extraL ∪ extraR) ∪ prefixClause v (w v - m) f) := by
  intro m
  induction m with
  | zero => intro _ hm_pos; exact absurd hm_pos (Nat.lt_irrefl 0)
  | succ m' ih =>
    intro hm hm_pos f
    let d := w v - (m' + 1)
    have hd : d < w v := by omega
    let f0 := Function.update f ⟨d, hd⟩ false
    let f1 := Function.update f ⟨d, hd⟩ true
    have hres := isResolvent_prefixClause v d hd extraL extraR hexL hexR f
    cases m' with
    | zero =>
      have hdw : d + 1 = w v := by omega
      have hp_flip : blockParity f1 = !(blockParity f0) := blockParity_update_not f ⟨d, hd⟩
      cases hb0 : blockParity f0
      · have hb1 : blockParity f1 = true := by rw [hp_flip, hb0]; rfl
        have hD0 := hL f0 hb0
        have hD1 := hR f1 hb1
        rw [← prefixClause_full, ← hdw] at hD0 hD1
        have hc := derivable_combine hres hD0 hD1
        rw [max_self] at hc
        exact derivable_mono (by omega) (by omega) hc
      · have hb1 : blockParity f1 = false := by rw [hp_flip, hb0]; rfl
        have hD0 := hR f0 hb0
        have hD1 := hL f1 hb1
        rw [← prefixClause_full, ← hdw] at hD0 hD1
        have hres' : IsResolvent
            (extraR ∪ prefixClause v (d + 1) f0)
            (extraL ∪ prefixClause v (d + 1) f1)
            ((extraL ∪ extraR) ∪ prefixClause v d f) := by
          have := isResolvent_prefixClause v d hd extraR extraL hexR hexL f
          rwa [Finset.union_comm extraR extraL] at this
        have hc := derivable_combine hres' hD0 hD1
        rw [max_self, join_comm b a] at hc
        exact derivable_mono (by omega) (by omega) hc
    | succ m'' =>
      have hd1 : d + 1 = w v - (m'' + 1) := by omega
      have hD0 := ih (by omega) (Nat.succ_pos m'') f0
      have hD1 := ih (by omega) (Nat.succ_pos m'') f1
      rw [← hd1] at hD0 hD1
      have hexLR : ∀ l ∈ extraL ∪ extraR, l.1.1 ≠ v := by
        intro l hl
        rcases Finset.mem_union.mp hl with h | h
        · exact hexL l h
        · exact hexR l h
      have hres' := isResolvent_prefixClause v d hd (extraL ∪ extraR) (extraL ∪ extraR) hexLR hexLR f
      rw [Finset.union_self] at hres'
      have hc := derivable_combine hres' hD0 hD1
      rw [max_self] at hc
      have hjoin : join ((m'' + 1 - 1) + join a b) ((m'' + 1 - 1) + join a b) =
          (m'' + 1 + 1 - 1) + join a b := by
        unfold join
        simp only [ite_true]
        omega
      rw [hjoin] at hc
      exact derivable_mono (by omega) le_rfl hc

lemma expand_block {n : ℕ} {w : Fin n → ℕ} (hw : ∀ i, 0 < w i) (F : Set (Clause (Fin n)))
    (v : Fin n) (extraL extraR : Clause (RawType w))
    (hexL : ∀ l ∈ extraL, l.1.1 ≠ v) (hexR : ∀ l ∈ extraR, l.1.1 ≠ v)
    (H a b : ℕ)
    (hL : ∀ f : Fin (w v) → Bool, blockParity f = false →
      Derivable F H a (extraL ∪ blockLit v f))
    (hR : ∀ f : Fin (w v) → Bool, blockParity f = true →
      Derivable F H b (extraR ∪ blockLit v f)) :
    Derivable F (H + w v) ((w v - 1) + join a b) (extraL ∪ extraR) := by
  have h := expand_block_aux F v extraL extraR hexL hexR H a b hL hR (w v) le_rfl (hw v) (fun _ => false)
  rw [Nat.sub_self, prefixClause_zero, Finset.union_empty] at h
  exact h

lemma base_bndClause_liftAx {n : ℕ} {w : Fin n → ℕ} (i : ℕ) (hi : i ≤ n)
    (yL : ∀ (hi0 : 0 < i) (hin : i - 1 < n), Fin (w ⟨i - 1, hin⟩) → Bool)
    (hyL : ∀ (hi0 : 0 < i) (hin : i - 1 < n), blockParity (yL hi0 hin) = true)
    (yR : ∀ (hi0 : i < n), Fin (w ⟨i, hi0⟩) → Bool)
    (hyR : ∀ (hi0 : i < n), blockParity (yR hi0) = false) :
    liftAx (F_path n) (bndClause i i yL yR) := by
  let e : Fin (n + 1) := ⟨i, Nat.lt_succ_of_le hi⟩
  let C : Clause (Fin n) :=
    (((Finset.univ : Finset (Fin n)).filter (fun v => v.val + 1 = e.val)).image (fun v => (v, false))) ∪
    (((Finset.univ : Finset (Fin n)).filter (fun v => v.val = e.val)).image (fun v => (v, true)))
  have hCF : C ∈ F_path n := ⟨e, rfl⟩
  let y : RawType w → Bool := fun ⟨v, j⟩ =>
    if hv1 : v.val + 1 = i then yL (by omega) (by omega) ⟨j.val, by
      have : v = ⟨i - 1, by omega⟩ := Fin.ext (by dsimp only; omega)
      rw [← this]; exact j.isLt⟩
    else if hv2 : v.val = i then yR (by omega) ⟨j.val, by
      have : v = ⟨i, by omega⟩ := Fin.ext hv2
      rw [← this]; exact j.isLt⟩
    else false
  refine ⟨C, hCF, y, ?_, ?_⟩
  · intro lit hlit
    rcases Finset.mem_union.mp hlit with h | h <;>
      rcases Finset.mem_image.mp h with ⟨v, hv, rfl⟩ <;>
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv <;>
      dsimp only [e] at hv
    · have hv_eq : v = ⟨i - 1, by omega⟩ := Fin.ext (by dsimp only; omega)
      have hy_eq : parity y ⟨i - 1, by omega⟩ = blockParity (yL (by omega) (by omega)) := by
        unfold parity blockParity
        congr 3
        ext j
        simp [y, Nat.sub_add_cancel (by omega : 0 < i)]
      rw [hv_eq, hy_eq, hyL (by omega) (by omega)]
      simp
    · have hv_eq : v = ⟨i, by omega⟩ := Fin.ext hv
      have hy_eq : parity y ⟨i, by omega⟩ = blockParity (yR (by omega)) := by
        unfold parity blockParity
        congr 3
        ext j
        simp [y]
      rw [hv_eq, hy_eq, hyR (by omega)]
      simp
  · ext ⟨⟨v, j⟩, b⟩
    simp only [bndClause, blockLit, Finset.mem_union]
    constructor
    · rintro (h | h)
      · split_ifs at h with hi0
        · rcases Finset.mem_image.mp h with ⟨j', _, h_eq⟩
          cases h_eq
          rw [Finset.mem_image]
          refine ⟨⟨⟨i - 1, hi0.2⟩, j'⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
          · rw [Finset.mem_image]
            refine ⟨(⟨i - 1, hi0.2⟩, false), Finset.mem_union_left _ (Finset.mem_image.mpr
              ⟨⟨i - 1, hi0.2⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only [e]; omega⟩, rfl⟩), rfl⟩
          · simp [y, Nat.sub_add_cancel hi0.1]
        · exact absurd h (Finset.notMem_empty _)
      · split_ifs at h with hin
        · rcases Finset.mem_image.mp h with ⟨j', _, h_eq⟩
          cases h_eq
          rw [Finset.mem_image]
          refine ⟨⟨⟨i, hin⟩, j'⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
          · rw [Finset.mem_image]
            refine ⟨(⟨i, hin⟩, true), Finset.mem_union_right _ (Finset.mem_image.mpr
              ⟨⟨i, hin⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only [e]⟩, rfl⟩), rfl⟩
          · simp [y]
        · exact absurd h (Finset.notMem_empty _)
    · rw [Finset.mem_image]
      rintro ⟨⟨v', j'⟩, hv', h_eq⟩
      cases h_eq
      rw [Finset.mem_filter] at hv'
      rcases Finset.mem_image.mp hv'.2 with ⟨lit, hlit, hlit_eq⟩
      dsimp only at hlit_eq
      subst hlit_eq
      rcases Finset.mem_union.mp hlit with h | h <;>
        rcases Finset.mem_image.mp h with ⟨u, hu, rfl⟩ <;>
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu <;>
        dsimp only [e] at hu
      · left
        have hi0 : 0 < i ∧ i - 1 < n := ⟨by omega, by omega⟩
        simp only [dif_pos hi0]
        have hu_eq : u = ⟨i - 1, hi0.2⟩ := Fin.ext (by dsimp only; omega)
        subst hu_eq
        rw [Finset.mem_image]
        refine ⟨j, Finset.mem_univ _, ?_⟩
        simp [y, Nat.sub_add_cancel hi0.1]
      · right
        have hin : i < n := by omega
        simp only [dif_pos hin]
        have hu_eq : u = ⟨i, hin⟩ := Fin.ext hu
        subst hu_eq
        rw [Finset.mem_image]
        refine ⟨j, Finset.mem_univ _, ?_⟩
        simp [y]

lemma feasible_to_derivable {n : ℕ} {w : Fin n → ℕ} (hw : ∀ i, 0 < w i) :
    ∀ (k i j H s : ℕ), i ≤ j → j ≤ n → feasible n w k i j H s →
      ∀ (yL : ∀ (hi0 : 0 < i) (hin : i - 1 < n), Fin (w ⟨i - 1, hin⟩) → Bool),
        (∀ (hi0 : 0 < i) (hin : i - 1 < n), blockParity (yL hi0 hin) = true) →
      ∀ (yR : ∀ (hj : j < n), Fin (w ⟨j, hj⟩) → Bool),
        (∀ (hj : j < n), blockParity (yR hj) = false) →
      Derivable (F_path n) H s (bndClause i j yL yR) := by
  intro k
  induction k with
  | zero =>
    intro i j H s hij hjn hf yL hyL yR hyR
    change i = j at hf
    subst hf
    refine ⟨{[]}, ∅, fun _ => bndClause i i yL yR, fun _ => 0, shape_leaf, rfl, Nat.zero_le _, ?_, ?_, ?_⟩
    · intro p hp; simp only [Finset.mem_singleton] at hp; subst hp; simp
    · intro p hp
      simp only [Finset.sdiff_empty, Finset.mem_singleton] at hp
      subst hp
      exact ⟨base_bndClause_liftAx i hjn yL hyL yR hyR, rfl⟩
    · intro p hp; simp at hp
  | succ k ih =>
    intro i j H s hij hjn hf yL hyL yR hyR
    rcases hf with rfl | ⟨v, hiv, hvj, hwH, a, b, hs, hL, hR⟩
    · refine ⟨{[]}, ∅, fun _ => bndClause i i yL yR, fun _ => 0, shape_leaf, rfl, Nat.zero_le _, ?_, ?_, ?_⟩
      · intro p hp; simp only [Finset.mem_singleton] at hp; subst hp; simp
      · intro p hp
        simp only [Finset.sdiff_empty, Finset.mem_singleton] at hp
        subst hp
        exact ⟨base_bndClause_liftAx i hjn yL hyL yR hyR, rfl⟩
      · intro p hp; simp at hp
    · let extraL := if h : 0 < i ∧ i - 1 < n then blockLit ⟨i - 1, h.2⟩ (yL h.1 h.2) else ∅
      let extraR := if h : j < n then blockLit ⟨j, h⟩ (yR h) else ∅
      have hexL : ∀ l ∈ extraL, l.1.1 ≠ v := by
        intro l hl
        dsimp only [extraL] at hl
        split_ifs at hl with h
        · rcases Finset.mem_image.mp hl with ⟨t, _, rfl⟩
          intro heq
          have := Fin.ext_iff.mp heq
          dsimp only at this
          omega
        · exact absurd hl (Finset.notMem_empty _)
      have hexR : ∀ l ∈ extraR, l.1.1 ≠ v := by
        intro l hl
        dsimp only [extraR] at hl
        split_ifs at hl with h
        · rcases Finset.mem_image.mp hl with ⟨t, _, rfl⟩
          intro heq
          have := Fin.ext_iff.mp heq
          dsimp only at this
          omega
        · exact absurd hl (Finset.notMem_empty _)
      have hDL : ∀ f : Fin (w v) → Bool, blockParity f = false →
          Derivable (F_path n) (H - w v) a (extraL ∪ blockLit v f) := by
        intro f hf_par
        let yR' : ∀ (hv' : v.val < n), Fin (w ⟨v.val, hv'⟩) → Bool := fun _ => f
        have hyR' : ∀ (hv' : v.val < n), blockParity (yR' hv') = false := fun _ => hf_par
        have hder := ih i v.val (H - w v) a hiv (le_of_lt v.isLt) hL yL hyL yR' hyR'
        have h_eq : bndClause i v.val yL yR' = extraL ∪ blockLit v f := by
          unfold bndClause
          simp only [dif_pos v.isLt]
          rfl
        rwa [h_eq] at hder
      have hDR : ∀ f : Fin (w v) → Bool, blockParity f = true →
          Derivable (F_path n) (H - w v) b (extraR ∪ blockLit v f) := by
        intro f hf_par
        let yL' : ∀ (hv0 : 0 < v.val + 1) (hvn : v.val + 1 - 1 < n),
            Fin (w ⟨v.val + 1 - 1, hvn⟩) → Bool := fun _ _ => f
        have hyL' : ∀ (hv0 : 0 < v.val + 1) (hvn : v.val + 1 - 1 < n),
            blockParity (yL' hv0 hvn) = true := fun _ _ => hf_par
        have hder := ih (v.val + 1) j (H - w v) b hvj hjn hR yL' hyL' yR hyR
        have h_eq : bndClause (v.val + 1) j yL' yR = extraR ∪ blockLit v f := by
          unfold bndClause
          have hv1 : 0 < v.val + 1 ∧ v.val + 1 - 1 < n := ⟨Nat.succ_pos _, v.isLt⟩
          simp only [dif_pos hv1, Finset.union_comm]
          rfl
        rwa [h_eq] at hder
      have hexp := expand_block hw (F_path n) v extraL extraR hexL hexR (H - w v) a b hDL hDR
      have h_bnd : bndClause i j yL yR = extraL ∪ extraR := rfl
      rw [← h_bnd] at hexp
      exact derivable_mono (by omega) hs hexp

inductive RTree (Raw : Type) where
  | leaf
  | node (v : Raw) (l r : RTree Raw)

def rheight {Raw : Type} : RTree Raw → ℕ
  | .leaf => 0
  | .node _ l r => 1 + max (rheight l) (rheight r)

def rrank {Raw : Type} : RTree Raw → ℕ
  | .leaf => 0
  | .node _ l r => join (rrank l) (rrank r)

def Falsifies {V : Type} (ρ : V → Option Bool) (C : Clause V) : Prop :=
  ∀ lit ∈ C, ρ lit.1 = some (!lit.2)

def RSound {n : ℕ} {w : Fin n → ℕ} (F : Set (Clause (Fin n)))
    (ρ : RawType w → Option Bool) : RTree (RawType w) → Prop
  | .leaf => ∃ A, liftAx F A ∧ Falsifies ρ A
  | .node v l r =>
      RSound F (Function.update ρ v (some false)) l ∧
      RSound F (Function.update ρ v (some true)) r

lemma extract_rtree_aux {n : ℕ} {w : Fin n → ℕ}
    (F : Set (Clause (Fin n)))
    (N J : Finset (List Bool)) (line : List Bool → Clause (RawType w))
    (r : List Bool → ℕ) (H : ℕ)
    (hshape : shape N J) (hlen : ∀ p ∈ N, p.length ≤ H)
    (hax : ∀ p ∈ N \ J, liftAx F (line p) ∧ r p = 0)
    (hres : ∀ p ∈ J, IsResolvent (line (p ++ [false])) (line (p ++ [true])) (line p) ∧
      r p = join (r (p ++ [false])) (r (p ++ [true]))) :
    ∀ (d : ℕ) (p : List Bool), p ∈ N → H - p.length ≤ d →
      ∀ ρ : RawType w → Option Bool, Falsifies ρ (line p) →
        ∃ T : RTree (RawType w),
          RSound F ρ T ∧ rheight T ≤ H - p.length ∧ rrank T ≤ r p := by
  intro d
  induction d with
  | zero =>
    intro p hp hle ρ hfals
    have hnotJ : p ∉ J := by
      intro hpJ
      have hc := (hshape.2.2.2 p hpJ).1
      have hlc := hlen (p ++ [false]) hc
      simp at hlc
      omega
    have hleaf : p ∈ N \ J := Finset.mem_sdiff.mpr ⟨hp, hnotJ⟩
    exact ⟨RTree.leaf, ⟨line p, (hax p hleaf).1, hfals⟩, Nat.zero_le _, Nat.zero_le _⟩
  | succ d ih =>
    intro p hp hle ρ hfals
    by_cases hpJ : p ∈ J
    · have hp0 : p ++ [false] ∈ N := (hshape.2.2.2 p hpJ).1
      have hp1 : p ++ [true] ∈ N := (hshape.2.2.2 p hpJ).2
      obtain ⟨⟨v, hv0, hv1, hreq⟩, hr_eq⟩ := hres p hpJ
      have hlen0 : H - (p ++ [false]).length ≤ d := by
        have := hlen (p ++ [false]) hp0; simp at this ⊢; omega
      have hlen1 : H - (p ++ [true]).length ≤ d := by
        have := hlen (p ++ [true]) hp1; simp at this ⊢; omega
      by_cases hρv_false : ρ v = some false
      · have hf0 : Falsifies ρ (line (p ++ [false])) := by
          intro lit hlit
          by_cases hlv : lit.1 = v
          · by_cases hlb : lit.2 = true
            · rw [hlv, hlb, hρv_false]; rfl
            · have hne : lit ≠ (v, true) := fun h => hlb (congrArg Prod.snd h)
              exact hfals lit (hreq ▸ Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hne, hlit⟩))
          · have hne : lit ≠ (v, true) := fun h => hlv (congrArg Prod.fst h)
            exact hfals lit (hreq ▸ Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hne, hlit⟩))
        obtain ⟨T0, hS0, hH0, hR0⟩ := ih (p ++ [false]) hp0 hlen0 ρ hf0
        refine ⟨T0, hS0, by simp at hH0; omega, ?_⟩
        rw [hr_eq]
        exact le_trans hR0 (le_join_left _ _)
      · by_cases hρv_true : ρ v = some true
        · have hf1 : Falsifies ρ (line (p ++ [true])) := by
            intro lit hlit
            by_cases hlv : lit.1 = v
            · by_cases hlb : lit.2 = false
              · rw [hlv, hlb, hρv_true]; rfl
              · have hne : lit ≠ (v, false) := fun h => hlb (congrArg Prod.snd h)
                exact hfals lit (hreq ▸ Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hne, hlit⟩))
            · have hne : lit ≠ (v, false) := fun h => hlv (congrArg Prod.fst h)
              exact hfals lit (hreq ▸ Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hne, hlit⟩))
          obtain ⟨T1, hS1, hH1, hR1⟩ := ih (p ++ [true]) hp1 hlen1 ρ hf1
          refine ⟨T1, hS1, by simp at hH1; omega, ?_⟩
          rw [hr_eq]
          exact le_trans hR1 (le_join_right _ _)
        · have hρv_none : ρ v = none := by
            cases h : ρ v with
            | none => rfl
            | some b => cases b <;> simp_all
          have hf0 : Falsifies (Function.update ρ v (some false)) (line (p ++ [false])) := by
            intro lit hlit
            by_cases hlv : lit.1 = v
            · by_cases hlb : lit.2 = true
              · rw [hlv, hlb]; simp
              · have hne : lit ≠ (v, true) := fun h => hlb (congrArg Prod.snd h)
                have hcontra := hfals lit (hreq ▸ Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hne, hlit⟩))
                rw [hlv, hρv_none] at hcontra
                cases hcontra
            · have hne : lit ≠ (v, true) := fun h => hlv (congrArg Prod.fst h)
              rw [Function.update_of_ne hlv]
              exact hfals lit (hreq ▸ Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hne, hlit⟩))
          have hf1 : Falsifies (Function.update ρ v (some true)) (line (p ++ [true])) := by
            intro lit hlit
            by_cases hlv : lit.1 = v
            · by_cases hlb : lit.2 = false
              · rw [hlv, hlb]; simp
              · have hne : lit ≠ (v, false) := fun h => hlb (congrArg Prod.snd h)
                have hcontra := hfals lit (hreq ▸ Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hne, hlit⟩))
                rw [hlv, hρv_none] at hcontra
                cases hcontra
            · have hne : lit ≠ (v, false) := fun h => hlv (congrArg Prod.fst h)
              rw [Function.update_of_ne hlv]
              exact hfals lit (hreq ▸ Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hne, hlit⟩))
          obtain ⟨T0, hS0, hH0, hR0⟩ := ih (p ++ [false]) hp0 hlen0 _ hf0
          obtain ⟨T1, hS1, hH1, hR1⟩ := ih (p ++ [true]) hp1 hlen1 _ hf1
          have hp0_len := hlen (p ++ [false]) hp0
          refine ⟨RTree.node v T0 T1, ⟨hS0, hS1⟩, ?_, ?_⟩
          · simp only [rheight] at *
            simp only [List.length_append, List.length_singleton] at hH0 hH1 hp0_len
            omega
          · simp only [rrank, hr_eq]
            exact join_mono hR0 hR1
    · have hleaf : p ∈ N \ J := Finset.mem_sdiff.mpr ⟨hp, hpJ⟩
      exact ⟨RTree.leaf, ⟨line p, (hax p hleaf).1, hfals⟩, Nat.zero_le _, Nat.zero_le _⟩

def rem {n : ℕ} {w : Fin n → ℕ} (ρ : RawType w → Option Bool) (v : Fin n) : ℕ :=
  ((Finset.univ : Finset (Fin (w v))).filter (fun j => ρ ⟨v, j⟩ = none)).card

def used {n : ℕ} {w : Fin n → ℕ} (ρ : RawType w → Option Bool) (i j : ℕ) : ℕ :=
  ∑ v ∈ (Finset.univ : Finset (Fin n)).filter (fun v => i ≤ v.val ∧ v.val < j), (w v - rem ρ v)

def assignedParity {n : ℕ} {w : Fin n → ℕ} (ρ : RawType w → Option Bool) (v : Fin n) : Bool :=
  decide (Odd ((Finset.univ : Finset (Fin (w v))).filter (fun j => ρ ⟨v, j⟩ = some true)).card)

lemma rem_le {n : ℕ} {w : Fin n → ℕ} (ρ : RawType w → Option Bool) (v : Fin n) :
    rem ρ v ≤ w v := by
  unfold rem
  calc _ ≤ (Finset.univ : Finset (Fin (w v))).card := Finset.card_filter_le _ _
    _ = w v := Fintype.card_fin _

lemma rem_update_ne {n : ℕ} {w : Fin n → ℕ} (ρ : RawType w → Option Bool)
    {u v : Fin n} (huv : u ≠ v) (k : Fin (w u)) (val : Option Bool) :
    rem (Function.update ρ ⟨u, k⟩ val) v = rem ρ v := by
  unfold rem
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hne : (⟨v, j⟩ : RawType w) ≠ ⟨u, k⟩ := fun h => huv (congrArg Sigma.fst h).symm
  rw [Function.update_of_ne hne]

lemma rem_update_eq_some {n : ℕ} {w : Fin n → ℕ} (ρ : RawType w → Option Bool)
    (v : Fin n) (k : Fin (w v)) (hnone : ρ ⟨v, k⟩ = none) (b : Bool) :
    rem (Function.update ρ ⟨v, k⟩ (some b)) v = rem ρ v - 1 := by
  unfold rem
  let s := (Finset.univ : Finset (Fin (w v))).filter (fun j => ρ ⟨v, j⟩ = none)
  let s' := (Finset.univ : Finset (Fin (w v))).filter
    (fun j => Function.update ρ ⟨v, k⟩ (some b) ⟨v, j⟩ = none)
  have hk : k ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnone⟩
  have hs' : s' = s.erase k := by
    ext j
    simp only [s', s, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hjk : j = k
    · subst hjk; simp
    · have hne : (⟨v, j⟩ : RawType w) ≠ ⟨v, k⟩ := fun h => hjk (by
        have := (Sigma.ext_iff.mp h).2
        simpa using this)
      rw [Function.update_of_ne hne]
      exact ⟨fun h => ⟨hjk, h⟩, fun h => h.2⟩
  change s'.card = s.card - 1
  rw [hs', Finset.card_erase_of_mem hk]

lemma assignedParity_update_ne {n : ℕ} {w : Fin n → ℕ} (ρ : RawType w → Option Bool)
    {u v : Fin n} (huv : u ≠ v) (k : Fin (w u)) (val : Option Bool) :
    assignedParity (Function.update ρ ⟨u, k⟩ val) v = assignedParity ρ v := by
  unfold assignedParity
  congr 3
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hne : (⟨v, j⟩ : RawType w) ≠ ⟨u, k⟩ := fun h => huv (congrArg Sigma.fst h).symm
  rw [Function.update_of_ne hne]

lemma assignedParity_update_not {n : ℕ} {w : Fin n → ℕ} (ρ : RawType w → Option Bool)
    (v : Fin n) (k : Fin (w v)) (hnone : ρ ⟨v, k⟩ = none) :
    assignedParity (Function.update ρ ⟨v, k⟩ (some true)) v =
      !(assignedParity (Function.update ρ ⟨v, k⟩ (some false)) v) := by
  unfold assignedParity
  let s0 := (Finset.univ : Finset (Fin (w v))).filter
    (fun j => Function.update ρ ⟨v, k⟩ (some false) ⟨v, j⟩ = some true)
  let s1 := (Finset.univ : Finset (Fin (w v))).filter
    (fun j => Function.update ρ ⟨v, k⟩ (some true) ⟨v, j⟩ = some true)
  have hk0 : k ∉ s0 := by simp [s0]
  have hs1 : s1 = insert k s0 := by
    ext j
    simp only [s1, s0, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hjk : j = k
    · subst hjk; simp
    · have hne : (⟨v, j⟩ : RawType w) ≠ ⟨v, k⟩ := fun h => hjk (by
        have := (Sigma.ext_iff.mp h).2; simpa using this)
      rw [Function.update_of_ne hne, Function.update_of_ne hne]
      exact ⟨fun h => Or.inr h, fun h => h.elim (fun heq => absurd heq hjk) id⟩
  have hcard : s1.card = s0.card + 1 := by rw [hs1, Finset.card_insert_of_notMem hk0]
  change decide (Odd s1.card) = !decide (Odd s0.card)
  rw [hcard]
  by_cases ho : Odd s0.card
  · have hno : ¬ Odd (s0.card + 1) := by rcases ho with ⟨t, ht⟩; intro ⟨u, hu⟩; omega
    simp [ho, hno]
  · have ho1 : Odd (s0.card + 1) := by
      rw [Nat.not_odd_iff_even] at ho; rcases ho with ⟨t, ht⟩; exact ⟨t, by omega⟩
    simp [ho, ho1]

lemma assignedParity_eq_parity {n : ℕ} {w : Fin n → ℕ} (ρ : RawType w → Option Bool)
    (y : RawType w → Bool) (v : Fin n) (h : ∀ j : Fin (w v), ρ ⟨v, j⟩ = some (y ⟨v, j⟩)) :
    assignedParity ρ v = parity y v := by
  unfold assignedParity parity
  congr 3
  ext j
  simp [h j]

def Inv {n : ℕ} {w : Fin n → ℕ} (ρ : RawType w → Option Bool) (i j : ℕ) : Prop :=
  (∀ v : Fin n, i ≤ v.val → v.val < j → 0 < rem ρ v) ∧
  (∀ v : Fin n, v.val < i → rem ρ v = 0 → assignedParity ρ v = true) ∧
  (∀ v : Fin n, j ≤ v.val → rem ρ v = 0 → assignedParity ρ v = false)

lemma no_leaf_of_inv {n : ℕ} {w : Fin n → ℕ} (ρ : RawType w → Option Bool)
    (i j : ℕ) (hij : i < j) (hjn : j ≤ n) (hinv : Inv ρ i j) :
    ¬ ∃ A, liftAx (F_path n) A ∧ Falsifies ρ A := by
  rintro ⟨A, ⟨C, ⟨e, rfl⟩, y, hy, rfl⟩, hfals⟩
  have hblock : ∀ v : Fin n, v ∈ ((((Finset.univ : Finset (Fin n)).filter
      (fun v => v.val + 1 = e.val)).image (fun v => (v, false))) ∪
      (((Finset.univ : Finset (Fin n)).filter (fun v => v.val = e.val)).image
        (fun v => (v, true)))).image Prod.fst →
      rem ρ v = 0 ∧ assignedParity ρ v = parity y v := by
    intro v hv
    have hall : ∀ k : Fin (w v), ρ ⟨v, k⟩ = some (y ⟨v, k⟩) := by
      intro k
      have hmem : ((⟨v, k⟩ : RawType w), !(y ⟨v, k⟩)) ∈
          ((Finset.univ : Finset (RawType w)).filter (fun b => b.1 ∈ _)).image (fun b => (b, !(y b))) :=
        Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩)
      have := hfals _ hmem
      simpa using this
    constructor
    · unfold rem
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro k _
      rw [hall k]
      simp
    · exact assignedParity_eq_parity ρ y v hall
  by_cases hei : e.val < i
  · have hen : e.val < n := by omega
    let v : Fin n := ⟨e.val, hen⟩
    have hvC : (v, true) ∈ (((Finset.univ : Finset (Fin n)).filter (fun v => v.val + 1 = e.val)).image
        (fun v => (v, false))) ∪ (((Finset.univ : Finset (Fin n)).filter (fun v => v.val = e.val)).image
        (fun v => (v, true))) :=
      Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩))
    have hvfst : v ∈ _ := Finset.mem_image_of_mem Prod.fst hvC
    obtain ⟨hrem0, hpar⟩ := hblock v hvfst
    have hinv_t := hinv.2.1 v hei hrem0
    have hy_f := hy (v, true) hvC
    rw [← hpar, hinv_t] at hy_f
    exact hy_f rfl
  · by_cases hej : j < e.val
    · have he0 : 0 < e.val := by omega
      let v : Fin n := ⟨e.val - 1, by omega⟩
      have hvC : (v, false) ∈ (((Finset.univ : Finset (Fin n)).filter (fun v => v.val + 1 = e.val)).image
          (fun v => (v, false))) ∪ (((Finset.univ : Finset (Fin n)).filter (fun v => v.val = e.val)).image
          (fun v => (v, true))) :=
        Finset.mem_union_left _ (Finset.mem_image_of_mem _
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only [v]; omega⟩))
      have hvfst : v ∈ _ := Finset.mem_image_of_mem Prod.fst hvC
      obtain ⟨hrem0, hpar⟩ := hblock v hvfst
      have hinv_f := hinv.2.2 v (by dsimp only [v]; omega) hrem0
      have hy_t := hy (v, false) hvC
      rw [← hpar, hinv_f] at hy_t
      exact hy_t rfl
    · have hei_le : i ≤ e.val := by omega
      have hej_le : e.val ≤ j := by omega
      by_cases hej_lt : e.val < j
      · let v : Fin n := ⟨e.val, by omega⟩
        have hvC : (v, true) ∈ (((Finset.univ : Finset (Fin n)).filter (fun v => v.val + 1 = e.val)).image
            (fun v => (v, false))) ∪ (((Finset.univ : Finset (Fin n)).filter (fun v => v.val = e.val)).image
            (fun v => (v, true))) :=
          Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩))
        have hvfst : v ∈ _ := Finset.mem_image_of_mem Prod.fst hvC
        obtain ⟨hrem0, _⟩ := hblock v hvfst
        have := hinv.1 v hei_le hej_lt
        omega
      · have he_eq : e.val = j := by omega
        let v : Fin n := ⟨j - 1, by omega⟩
        have hvC : (v, false) ∈ (((Finset.univ : Finset (Fin n)).filter (fun v => v.val + 1 = e.val)).image
            (fun v => (v, false))) ∪ (((Finset.univ : Finset (Fin n)).filter (fun v => v.val = e.val)).image
            (fun v => (v, true))) :=
          Finset.mem_union_left _ (Finset.mem_image_of_mem _
            (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only [v]; omega⟩))
        have hvfst : v ∈ _ := Finset.mem_image_of_mem Prod.fst hvC
        obtain ⟨hrem0, _⟩ := hblock v hvfst
        have := hinv.1 v (by dsimp only [v]; omega) (by dsimp only [v]; omega)
        omega

lemma used_update_outside {n : ℕ} {w : Fin n → ℕ} (ρ : RawType w → Option Bool)
    {i j : ℕ} (u : Fin n) (k : Fin (w u)) (val : Option Bool) (hout : u.val < i ∨ j ≤ u.val) :
    used (Function.update ρ ⟨u, k⟩ val) i j = used ρ i j := by
  unfold used
  refine Finset.sum_congr rfl fun v hv => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
  have huv : u ≠ v := by intro heq; subst heq; omega
  rw [rem_update_ne ρ huv]

lemma used_update_inside {n : ℕ} {w : Fin n → ℕ} (ρ : RawType w → Option Bool)
    {i j : ℕ} (v : Fin n) (hiv : i ≤ v.val) (hvj : v.val < j)
    (k : Fin (w v)) (hnone : ρ ⟨v, k⟩ = none) (b : Bool) :
    used (Function.update ρ ⟨v, k⟩ (some b)) i j = used ρ i j + 1 := by
  unfold used
  let S := (Finset.univ : Finset (Fin n)).filter (fun u => i ≤ u.val ∧ u.val < j)
  have hvS : v ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiv, hvj⟩
  rw [← Finset.add_sum_erase S _ hvS, ← Finset.add_sum_erase S _ hvS]
  have hsum : ∑ u ∈ S.erase v, (w u - rem (Function.update ρ ⟨v, k⟩ (some b)) u) =
      ∑ u ∈ S.erase v, (w u - rem ρ u) := by
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [rem_update_ne ρ (Finset.ne_of_mem_erase hu).symm]
  rw [hsum, rem_update_eq_some ρ v k hnone b]
  have hrem_pos : 0 < rem ρ v := Finset.card_pos.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnone⟩⟩
  have hrem_le : rem ρ v ≤ w v := rem_le ρ v
  omega

lemma used_split {n : ℕ} {w : Fin n → ℕ} (ρ ρL ρR : RawType w → Option Bool)
    {i j : ℕ} (v : Fin n) (hiv : i ≤ v.val) (hvj : v.val < j) (hrem1 : rem ρ v = 1)
    (hL : ∀ u : Fin n, u ≠ v → rem ρL u = rem ρ u)
    (hR : ∀ u : Fin n, u ≠ v → rem ρR u = rem ρ u) :
    used ρ i j = (w v - 1) + used ρL i v.val + used ρR (v.val + 1) j := by
  unfold used
  let S := (Finset.univ : Finset (Fin n)).filter (fun u => i ≤ u.val ∧ u.val < j)
  let SL := (Finset.univ : Finset (Fin n)).filter (fun u => i ≤ u.val ∧ u.val < v.val)
  let SR := (Finset.univ : Finset (Fin n)).filter (fun u => v.val + 1 ≤ u.val ∧ u.val < j)
  have hvS : v ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiv, hvj⟩
  have hdisj : Disjoint SL SR := by
    rw [Finset.disjoint_left]
    intro u huL huR
    simp only [SL, SR, Finset.mem_filter, Finset.mem_univ, true_and] at huL huR
    omega
  have hunion : S.erase v = SL ∪ SR := by
    ext u
    simp only [S, SL, SR, Finset.mem_erase, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨huv, hiu, huj⟩
      have hne : u.val ≠ v.val := fun h => huv (Fin.ext h)
      omega
    · rintro (⟨hiu, huv⟩ | ⟨hvu, huj⟩)
      · exact ⟨fun h => by subst h; omega, hiu, by omega⟩
      · exact ⟨fun h => by subst h; omega, by omega, huj⟩
  rw [← Finset.add_sum_erase S _ hvS, hunion, Finset.sum_union hdisj, hrem1]
  have hsumL : ∑ u ∈ SL, (w u - rem ρ u) = ∑ u ∈ SL, (w u - rem ρL u) := by
    refine Finset.sum_congr rfl fun u hu => ?_
    simp only [SL, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    rw [hL u (fun h => by subst h; omega)]
  have hsumR : ∑ u ∈ SR, (w u - rem ρ u) = ∑ u ∈ SR, (w u - rem ρR u) := by
    refine Finset.sum_congr rfl fun u hu => ?_
    simp only [SR, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    rw [hR u (fun h => by subst h; omega)]
  rw [hsumL, hsumR]
  dsimp only [SL, SR]
  have hrem_le := rem_le ρ v
  omega

lemma used_ge_sub {n : ℕ} {w : Fin n → ℕ} (ρ : RawType w → Option Bool)
    {i j : ℕ} (v : Fin n) (hiv : i ≤ v.val) (hvj : v.val < j) :
    w v - rem ρ v ≤ used ρ i j := by
  unfold used
  have hmem : v ∈ (Finset.univ : Finset (Fin n)).filter (fun u => i ≤ u.val ∧ u.val < j) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ v, hiv, hvj⟩
  exact Finset.single_le_sum (fun u _ => Nat.zero_le (w u - rem ρ u)) hmem

lemma forward_ind {n : ℕ} {w : Fin n → ℕ} (T : RTree (RawType w)) :
    ∀ (i j H s : ℕ) (ρ : RawType w → Option Bool),
      i ≤ j → j ≤ n → Inv ρ i j → RSound (F_path n) ρ T →
      rheight T + used ρ i j ≤ H → rrank T + used ρ i j ≤ s →
      feasible n w (j - i) i j H s := by
  induction T with
  | leaf =>
    intro i j H s ρ hij hjn hinv hsound _ _
    by_cases heq : i = j
    · subst heq; simp [feasible]
    · exfalso; exact no_leaf_of_inv ρ i j (by omega) hjn hinv hsound
  | node u l r ihL ihR =>
    intro i j H s ρ hij hjn hinv hsound hH hs
    by_cases heq : i = j
    · subst heq; simp [feasible]
    · have hij_lt : i < j := by omega
      have hfuel : ∃ m, j - i = m + 1 := ⟨j - i - 1, by omega⟩
      rcases hfuel with ⟨m, hm⟩
      rw [hm]
      cases hρu : ρ u with
      | some b =>
        have hupd : Function.update ρ u (some b) = ρ := by
          funext x; by_cases hx : x = u <;> simp [hx, hρu]
        cases b
        · have hsound' : RSound (F_path n) ρ l := by simpa [hupd] using hsound.1
          have hH' : rheight l + used ρ i j ≤ H := by simp only [rheight] at hH; omega
          have hs' : rrank l + used ρ i j ≤ s := by
            simp only [rrank] at hs; exact le_trans (Nat.add_le_add_right (le_join_left _ _) _) hs
          have hres := ihL i j H s ρ hij hjn hinv hsound' hH' hs'
          rwa [hm] at hres
        · have hsound' : RSound (F_path n) ρ r := by simpa [hupd] using hsound.2
          have hH' : rheight r + used ρ i j ≤ H := by simp only [rheight] at hH; omega
          have hs' : rrank r + used ρ i j ≤ s := by
            simp only [rrank] at hs; exact le_trans (Nat.add_le_add_right (le_join_right _ _) _) hs
          have hres := ihR i j H s ρ hij hjn hinv hsound' hH' hs'
          rwa [hm] at hres
      | none =>
        rcases u with ⟨v, k⟩
        by_cases hiv : i ≤ v.val
        · by_cases hvj : v.val < j
          ·
            by_cases hrem1 : rem ρ v = 1
            ·
              have hp_flip := assignedParity_update_not ρ v k hρu
              have hex_bF : ∃ bF : Bool, assignedParity (Function.update ρ ⟨v, k⟩ (some bF)) v = false := by
                cases h0 : assignedParity (Function.update ρ ⟨v, k⟩ (some false)) v
                · exact ⟨false, h0⟩
                · exact ⟨true, by rw [hp_flip, h0]; rfl⟩
              rcases hex_bF with ⟨bF, hbF⟩
              let bT := !bF
              have hbT : assignedParity (Function.update ρ ⟨v, k⟩ (some bT)) v = true := by
                cases bF <;> simp [bT] at * <;> rw [hp_flip] at * <;> simp_all
              let ρF := Function.update ρ ⟨v, k⟩ (some bF)
              let ρT := Function.update ρ ⟨v, k⟩ (some bT)
              have hremF0 : rem ρF v = 0 := by
                dsimp only [ρF]; rw [rem_update_eq_some ρ v k hρu bF, hrem1]
              have hremT0 : rem ρT v = 0 := by
                dsimp only [ρT]; rw [rem_update_eq_some ρ v k hρu bT, hrem1]
              have hinvF : Inv ρF i v.val := by
                refine ⟨fun u hiu huv => ?_, fun u hui hrem0 => ?_, fun u hvu hrem0 => ?_⟩
                · dsimp only [ρF]; rw [rem_update_ne ρ (fun h => by subst h; omega)]; exact hinv.1 u hiu (by omega)
                · dsimp only [ρF]; rw [rem_update_ne ρ (fun h => by subst h; omega)] at hrem0
                  rw [assignedParity_update_ne ρ (fun h => by subst h; omega)]
                  exact hinv.2.1 u hui hrem0
                · by_cases huv : u = v
                  · subst huv; exact hbF
                  · dsimp only [ρF]; rw [rem_update_ne ρ (Ne.symm huv)] at hrem0
                    rw [assignedParity_update_ne ρ (Ne.symm huv)]
                    exact hinv.2.2 u (by
                      have hne : u.val ≠ v.val := fun h => huv (Fin.ext h)
                      by_contra hlt
                      have := hinv.1 u (by omega) (by omega)
                      omega) hrem0
              have hinvT : Inv ρT (v.val + 1) j := by
                refine ⟨fun u hvu huj => ?_, fun u huv hrem0 => ?_, fun u hju hrem0 => ?_⟩
                · dsimp only [ρT]; rw [rem_update_ne ρ (fun h => by subst h; omega)]; exact hinv.1 u (by omega) huj
                · by_cases huv' : u = v
                  · subst huv'; exact hbT
                  · dsimp only [ρT]; rw [rem_update_ne ρ (Ne.symm huv')] at hrem0
                    rw [assignedParity_update_ne ρ (Ne.symm huv')]
                    exact hinv.2.1 u (by
                      have hne : u.val ≠ v.val := fun h => huv' (Fin.ext h)
                      by_contra hlt
                      have := hinv.1 u (by omega) (by omega)
                      omega) hrem0
                · dsimp only [ρT]; rw [rem_update_ne ρ (fun h => by subst h; omega)] at hrem0
                  rw [assignedParity_update_ne ρ (fun h => by subst h; omega)]
                  exact hinv.2.2 u hju hrem0
              have hus := used_split ρ ρF ρT v hiv hvj hrem1
                (fun u huv => rem_update_ne ρ (Ne.symm huv) _ _)
                (fun u huv => rem_update_ne ρ (Ne.symm huv) _ _)
              have hused_ge : w v - 1 ≤ used ρ i j := by
                have := used_ge_sub ρ v hiv hvj; rwa [hrem1] at this
              have hht_ge : 1 ≤ rheight (RTree.node ⟨v, k⟩ l r) := by simp [rheight]
              have hwH : w v ≤ H := by omega
              cases bF
              ·
                have hSF : RSound (F_path n) ρF l := hsound.1
                have hST : RSound (F_path n) ρT r := hsound.2
                have hHF : rheight l + used ρF i v.val ≤ H - w v := by
                  simp only [rheight] at hH; omega
                have hHT : rheight r + used ρT (v.val + 1) j ≤ H - w v := by
                  simp only [rheight] at hH; omega
                let a := rrank l + used ρF i v.val
                let b := rrank r + used ρT (v.val + 1) j
                have hs_le : (w v - 1) + join a b ≤ s := by
                  calc (w v - 1) + join a b
                      ≤ (w v - 1) + (join (rrank l) (rrank r) + used ρF i v.val + used ρT (v.val + 1) j) := by
                        exact Nat.add_le_add_left (join_add_le _ _ _ _) _
                    _ = rrank (RTree.node ⟨v, k⟩ l r) + used ρ i j := by simp only [rrank]; omega
                    _ ≤ s := hs
                have hrecF := ihL i v.val (H - w v) a ρF hiv (by omega) hinvF hSF hHF le_rfl
                have hrecT := ihR (v.val + 1) j (H - w v) b ρT (by omega) hjn hinvT hST hHT le_rfl
                right
                exact ⟨v, hiv, hvj, hwH, a, b, hs_le,
                  feasible_mono_fuel (by omega) hrecF, feasible_mono_fuel (by omega) hrecT⟩
              ·
                have hSF : RSound (F_path n) ρF r := hsound.2
                have hST : RSound (F_path n) ρT l := hsound.1
                have hHF : rheight r + used ρF i v.val ≤ H - w v := by
                  simp only [rheight] at hH; omega
                have hHT : rheight l + used ρT (v.val + 1) j ≤ H - w v := by
                  simp only [rheight] at hH; omega
                let a := rrank r + used ρF i v.val
                let b := rrank l + used ρT (v.val + 1) j
                have hs_le : (w v - 1) + join a b ≤ s := by
                  calc (w v - 1) + join a b
                      ≤ (w v - 1) + (join (rrank r) (rrank l) + used ρF i v.val + used ρT (v.val + 1) j) := by
                        exact Nat.add_le_add_left (join_add_le _ _ _ _) _
                    _ = rrank (RTree.node ⟨v, k⟩ l r) + used ρ i j := by
                        simp only [rrank, join_comm (rrank r) (rrank l)]; omega
                    _ ≤ s := hs
                have hrecF := ihR i v.val (H - w v) a ρF hiv (by omega) hinvF hSF hHF le_rfl
                have hrecT := ihL (v.val + 1) j (H - w v) b ρT (by omega) hjn hinvT hST hHT le_rfl
                right
                exact ⟨v, hiv, hvj, hwH, a, b, hs_le,
                  feasible_mono_fuel (by omega) hrecF, feasible_mono_fuel (by omega) hrecT⟩
            ·
              have hrem_pos : 0 < rem ρ v := hinv.1 v hiv hvj
              have hrem_gt1 : 1 < rem ρ v := by omega
              have hlt := join_succ_le (rrank l) (rrank r)
              rcases hlt with hl_lt | hr_lt
              · let ρ' := Function.update ρ ⟨v, k⟩ (some false)
                have hinv' : Inv ρ' i j := by
                  refine ⟨fun u hiu huj => ?_, fun u hui hrem0 => ?_, fun u hju hrem0 => ?_⟩
                  · by_cases huv : u = v
                    · subst huv; dsimp only [ρ']; rw [rem_update_eq_some ρ u k hρu false]; omega
                    · dsimp only [ρ']; rw [rem_update_ne ρ (Ne.symm huv)]; exact hinv.1 u hiu huj
                  · dsimp only [ρ']; rw [rem_update_ne ρ (fun h => by subst h; omega)] at hrem0
                    rw [assignedParity_update_ne ρ (fun h => by subst h; omega)]
                    exact hinv.2.1 u hui hrem0
                  · dsimp only [ρ']; rw [rem_update_ne ρ (fun h => by subst h; omega)] at hrem0
                    rw [assignedParity_update_ne ρ (fun h => by subst h; omega)]
                    exact hinv.2.2 u hju hrem0
                have hus' := used_update_inside ρ v hiv hvj k hρu false
                have hH' : rheight l + used ρ' i j ≤ H := by
                  simp only [rheight] at hH; rw [hus']; omega
                have hs' : rrank l + used ρ' i j ≤ s := by
                  simp only [rrank] at hs; rw [hus']; omega
                have hres := ihL i j H s ρ' hij hjn hinv' hsound.1 hH' hs'
                rwa [hm] at hres
              · let ρ' := Function.update ρ ⟨v, k⟩ (some true)
                have hinv' : Inv ρ' i j := by
                  refine ⟨fun u hiu huj => ?_, fun u hui hrem0 => ?_, fun u hju hrem0 => ?_⟩
                  · by_cases huv : u = v
                    · subst huv; dsimp only [ρ']; rw [rem_update_eq_some ρ u k hρu true]; omega
                    · dsimp only [ρ']; rw [rem_update_ne ρ (Ne.symm huv)]; exact hinv.1 u hiu huj
                  · dsimp only [ρ']; rw [rem_update_ne ρ (fun h => by subst h; omega)] at hrem0
                    rw [assignedParity_update_ne ρ (fun h => by subst h; omega)]
                    exact hinv.2.1 u hui hrem0
                  · dsimp only [ρ']; rw [rem_update_ne ρ (fun h => by subst h; omega)] at hrem0
                    rw [assignedParity_update_ne ρ (fun h => by subst h; omega)]
                    exact hinv.2.2 u hju hrem0
                have hus' := used_update_inside ρ v hiv hvj k hρu true
                have hH' : rheight r + used ρ' i j ≤ H := by
                  simp only [rheight] at hH; rw [hus']; omega
                have hs' : rrank r + used ρ' i j ≤ s := by
                  simp only [rrank] at hs; rw [hus']; omega
                have hres := ihR i j H s ρ' hij hjn hinv' hsound.2 hH' hs'
                rwa [hm] at hres
          ·
            have hjv : j ≤ v.val := by omega
            have hp_flip := assignedParity_update_not ρ v k hρu
            have hex_b : ∃ b : Bool, assignedParity (Function.update ρ ⟨v, k⟩ (some b)) v = false := by
              cases h0 : assignedParity (Function.update ρ ⟨v, k⟩ (some false)) v
              · exact ⟨false, h0⟩
              · exact ⟨true, by rw [hp_flip, h0]; rfl⟩
            rcases hex_b with ⟨b, hb⟩
            let ρ' := Function.update ρ ⟨v, k⟩ (some b)
            have hinv' : Inv ρ' i j := by
              refine ⟨fun u hiu huj => ?_, fun u hui hrem0 => ?_, fun u hju hrem0 => ?_⟩
              · dsimp only [ρ']; rw [rem_update_ne ρ (fun h => by subst h; omega)]; exact hinv.1 u hiu huj
              · dsimp only [ρ']; rw [rem_update_ne ρ (fun h => by subst h; omega)] at hrem0
                rw [assignedParity_update_ne ρ (fun h => by subst h; omega)]
                exact hinv.2.1 u hui hrem0
              · by_cases huv : u = v
                · subst huv; exact hb
                · dsimp only [ρ']; rw [rem_update_ne ρ (Ne.symm huv)] at hrem0
                  rw [assignedParity_update_ne ρ (Ne.symm huv)]
                  exact hinv.2.2 u hju hrem0
            have hus' := used_update_outside ρ (i := i) (j := j) v k (some b) (Or.inr hjv)
            cases b
            · have hH' : rheight l + used ρ' i j ≤ H := by
                rw [hus']; simp only [rheight] at hH; omega
              have hs' : rrank l + used ρ' i j ≤ s := by
                rw [hus']; simp only [rrank] at hs
                exact le_trans (Nat.add_le_add_right (le_join_left _ _) _) hs
              have hres := ihL i j H s ρ' hij hjn hinv' hsound.1 hH' hs'
              rwa [hm] at hres
            · have hH' : rheight r + used ρ' i j ≤ H := by
                rw [hus']; simp only [rheight] at hH; omega
              have hs' : rrank r + used ρ' i j ≤ s := by
                rw [hus']; simp only [rrank] at hs
                exact le_trans (Nat.add_le_add_right (le_join_right _ _) _) hs
              have hres := ihR i j H s ρ' hij hjn hinv' hsound.2 hH' hs'
              rwa [hm] at hres
        ·
          have hvi : v.val < i := by omega
          have hp_flip := assignedParity_update_not ρ v k hρu
          have hex_b : ∃ b : Bool, assignedParity (Function.update ρ ⟨v, k⟩ (some b)) v = true := by
            cases h0 : assignedParity (Function.update ρ ⟨v, k⟩ (some false)) v
            · exact ⟨true, by rw [hp_flip, h0]; rfl⟩
            · exact ⟨false, h0⟩
          rcases hex_b with ⟨b, hb⟩
          let ρ' := Function.update ρ ⟨v, k⟩ (some b)
          have hinv' : Inv ρ' i j := by
            refine ⟨fun u hiu huj => ?_, fun u hui hrem0 => ?_, fun u hju hrem0 => ?_⟩
            · dsimp only [ρ']; rw [rem_update_ne ρ (fun h => by subst h; omega)]; exact hinv.1 u hiu huj
            · by_cases huv : u = v
              · subst huv; exact hb
              · dsimp only [ρ']; rw [rem_update_ne ρ (Ne.symm huv)] at hrem0
                rw [assignedParity_update_ne ρ (Ne.symm huv)]
                exact hinv.2.1 u hui hrem0
            · dsimp only [ρ']; rw [rem_update_ne ρ (fun h => by subst h; omega)] at hrem0
              rw [assignedParity_update_ne ρ (fun h => by subst h; omega)]
              exact hinv.2.2 u hju hrem0
          have hus' := used_update_outside ρ (i := i) (j := j) v k (some b) (Or.inl hvi)
          cases b
          · have hH' : rheight l + used ρ' i j ≤ H := by
              rw [hus']; simp only [rheight] at hH; omega
            have hs' : rrank l + used ρ' i j ≤ s := by
              rw [hus']; simp only [rrank] at hs
              exact le_trans (Nat.add_le_add_right (le_join_left _ _) _) hs
            have hres := ihL i j H s ρ' hij hjn hinv' hsound.1 hH' hs'
            rwa [hm] at hres
          · have hH' : rheight r + used ρ' i j ≤ H := by
              rw [hus']; simp only [rheight] at hH; omega
            have hs' : rrank r + used ρ' i j ≤ s := by
              rw [hus']; simp only [rrank] at hs
              exact le_trans (Nat.add_le_add_right (le_join_right _ _) _) hs
            have hres := ihR i j H s ρ' hij hjn hinv' hsound.2 hH' hs'
            rwa [hm] at hres

end PEqualNP.Outside.L_pcx_337_aux

theorem PEqualNP.Outside.L_pcx_337 : (∀ (n : ℕ) (w : Fin n → ℕ), (∀ i, 0 < w i) →
  let Raw := (i : Fin n) × Fin (w i)
  let parity := fun (y : Raw → Bool) (i : Fin n) =>
    decide (Odd ((Finset.univ : Finset (Fin (w i))).filter (fun j => y ⟨i,j⟩ = true)).card)
  let liftAx := fun (F : Set (PEqualNP.ProofComplexity.Clause (Fin n)))
      (A : PEqualNP.ProofComplexity.Clause Raw) =>
    ∃ C ∈ F, ∃ y : Raw → Bool, (∀ lit ∈ C, parity y lit.1 ≠ lit.2) ∧
      A = ((Finset.univ : Finset Raw).filter (fun b => b.1 ∈ C.image Prod.fst)).image
        (fun b => (b, !(y b)))
  let shape := fun (N J : Finset (List Bool)) =>
    [] ∈ N ∧ J ⊆ N ∧
    (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
    ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N
  let join := fun a b : ℕ => if a = b then a+1 else max a b
  let refutes := fun (F : Set (PEqualNP.ProofComplexity.Clause (Fin n))) (H s : ℕ) =>
    ∃ (N J : Finset (List Bool)) (line : List Bool → PEqualNP.ProofComplexity.Clause Raw)
      (r : List Bool → ℕ), shape N J ∧ line [] = ∅ ∧ r [] ≤ s ∧ (∀ p ∈ N, p.length ≤ H) ∧
      (∀ p ∈ N \ J, liftAx F (line p) ∧ r p = 0) ∧
      ∀ p ∈ J, PEqualNP.ProofComplexity.IsResolvent (line (p ++ [false]))
        (line (p ++ [true])) (line p) ∧ r p = join (r (p ++ [false])) (r (p ++ [true]))
  let F : Set (PEqualNP.ProofComplexity.Clause (Fin n)) := {C | ∃ e : Fin (n+1),
    C = (((Finset.univ : Finset (Fin n)).filter (fun v => v.val+1 = e.val)).image
      (fun v => (v,false))) ∪ (((Finset.univ : Finset (Fin n)).filter (fun v => v.val = e.val)).image
      (fun v => (v,true)))}
  let feasible : ℕ → ℕ → ℕ → ℕ → ℕ → Prop := Nat.rec
    (fun i j _ _ => i = j)
    (fun _ prev i j H s => i = j ∨ ∃ v : Fin n, i ≤ v.val ∧ v.val < j ∧ w v ≤ H ∧
      ∃ a b : ℕ, (w v-1) + join a b ≤ s ∧ prev i v.val (H-w v) a ∧ prev (v.val+1) j (H-w v) b)
  ∀ H s : ℕ, refutes F H s ↔ feasible n 0 n H s) := by
  intro n w hw
  dsimp only
  intro H s
  constructor
  · rintro ⟨N, J, line, r, hsh, hrt, hr, hlen, hax, hres⟩
    have hfals0 : PEqualNP.Outside.L_pcx_337_aux.Falsifies
        (fun _ : PEqualNP.Outside.L_pcx_337_aux.RawType w => none) (line []) := by
      rw [hrt]
      intro lit hlit
      exact absurd hlit (Finset.notMem_empty _)
    obtain ⟨T, hS, hH, hR⟩ := PEqualNP.Outside.L_pcx_337_aux.extract_rtree_aux
      (PEqualNP.Outside.L_pcx_337_aux.F_path n) N J line r H hsh hlen hax hres H [] hsh.1
      (by simp) _ hfals0
    have hinv0 : PEqualNP.Outside.L_pcx_337_aux.Inv
        (fun _ : PEqualNP.Outside.L_pcx_337_aux.RawType w => none) 0 n := by
      refine ⟨fun v _ _ => ?_, fun v hv _ => absurd hv (Nat.not_lt_zero _), fun v hv _ => absurd hv (not_le_of_gt v.isLt)⟩
      have hrem : PEqualNP.Outside.L_pcx_337_aux.rem
          (fun _ : PEqualNP.Outside.L_pcx_337_aux.RawType w => none) v = w v := by
        simp [PEqualNP.Outside.L_pcx_337_aux.rem]
      rw [hrem]
      exact hw v
    have hused0 : PEqualNP.Outside.L_pcx_337_aux.used
        (fun _ : PEqualNP.Outside.L_pcx_337_aux.RawType w => none) 0 n = 0 := by
      unfold PEqualNP.Outside.L_pcx_337_aux.used
      refine Finset.sum_eq_zero fun v _ => ?_
      simp [PEqualNP.Outside.L_pcx_337_aux.rem]
    have hres_fwd := PEqualNP.Outside.L_pcx_337_aux.forward_ind T 0 n H s
      (fun _ => none) (Nat.zero_le n) le_rfl hinv0 hS
      (by rw [hused0, add_zero]; simpa using hH)
      (by rw [hused0, add_zero]; exact le_trans hR hr)
    dsimp only [PEqualNP.Outside.L_pcx_337_aux.feasible, PEqualNP.Outside.L_pcx_337_aux.join] at hres_fwd
    simpa [Nat.sub_zero] using hres_fwd
  · intro hf
    have hder := PEqualNP.Outside.L_pcx_337_aux.feasible_to_derivable hw n 0 n H s (Nat.zero_le n) le_rfl hf
      (fun hi0 _ => absurd hi0 (Nat.lt_irrefl 0)) (fun hi0 _ => absurd hi0 (Nat.lt_irrefl 0))
      (fun hn => absurd hn (Nat.lt_irrefl n)) (fun hn => absurd hn (Nat.lt_irrefl n))
    have h_empty : PEqualNP.Outside.L_pcx_337_aux.bndClause (w := w) 0 n
        (fun hi0 _ => absurd hi0 (Nat.lt_irrefl 0)) (fun hn => absurd hn (Nat.lt_irrefl n)) = ∅ := by
      simp [PEqualNP.Outside.L_pcx_337_aux.bndClause]
    rw [h_empty] at hder
    exact hder

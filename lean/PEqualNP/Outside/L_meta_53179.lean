import Mathlib
import PEqualNP.Defs
import PEqualNP.Library.Helpers.RankedTapSchedule
import PEqualNP.Library.Helpers.RunIntervalBank

namespace PEqualNP.Outside.L_meta_53179

namespace Track

def qb_Z (n : ℕ) (c : Fin (n+1) → ℕ) (k : ℕ) (i : ℕ) : ℕ :=
  ((List.finRange (n+1)).scanl (fun z j => max (c j - k) (min (c j) z)) 0).getD (i+1) 0

theorem qb_Z_zero (n : ℕ) (c : Fin (n+1) → ℕ) (k : ℕ) : qb_Z n c k 0 = c 0 - k := by
  unfold qb_Z
  rw [List.getD_eq_getElem?_getD, List.getElem?_succ_scanl]
  simp

theorem qb_Z_succ (n : ℕ) (c : Fin (n+1) → ℕ) (k i : ℕ) (h : i + 1 < n + 1) :
    qb_Z n c k (i+1) = max (c ⟨i+1, h⟩ - k) (min (c ⟨i+1, h⟩) (qb_Z n c k i)) := by
  unfold qb_Z
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_succ_scanl]
  have h1 : ((List.finRange (n+1)).scanl (fun z j => max (c j - k) (min (c j) z)) 0)[i+1]? =
      some (((List.finRange (n+1)).scanl (fun z j => max (c j - k) (min (c j) z)) 0)[i+1]'(by simp; omega)) :=
    List.getElem?_eq_getElem _
  have h2 : (List.finRange (n+1))[i+1]? = some ⟨i+1, h⟩ := by
    rw [List.getElem?_eq_getElem (by simp; omega)]
    simp
  rw [h1, h2]
  simp

def qb_falls {n : ℕ} (u : Fin (n+1) → Bool) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter (fun i => u i.castSucc = true ∧ u i.succ = false)).card

def qb_al {T n : ℕ} (c : Fin (n+1) → ℕ) (w : Fin T → Fin (n+1) → Bool) : Prop :=
  ∀ (t : Fin T) (i : Fin n),
    (c i.castSucc ≤ c i.succ → w t i.castSucc ≤ w t i.succ) ∧
    (c i.succ ≤ c i.castSucc → w t i.succ ≤ w t i.castSucc)

theorem qb_fsum {T n : ℕ} (w : Fin T → Fin (n+1) → Bool) (S : Finset (Fin T)) :
    S.sum (fun t => qb_falls (w t)) =
      (Finset.univ : Finset (Fin n)).sum (fun i =>
        (S.filter (fun t => w t i.castSucc = true ∧ w t i.succ = false)).card) := by
  unfold qb_falls
  simp only [Finset.card_filter]
  exact Finset.sum_comm

theorem qb_cnt_le {T n : ℕ} (w : Fin T → Fin (n+1) → Bool) (S : Finset (Fin T)) (i : Fin n) :
    (S.filter (fun t => w t i.castSucc = true)).card - (S.filter (fun t => w t i.succ = true)).card ≤
      (S.filter (fun t => w t i.castSucc = true ∧ w t i.succ = false)).card := by
  have h1 : S.filter (fun t => w t i.castSucc = true) ⊆
      S.filter (fun t => w t i.succ = true) ∪
        S.filter (fun t => w t i.castSucc = true ∧ w t i.succ = false) := by
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_union] at ht ⊢
    cases h : w t i.succ <;> simp_all
  have h2 := Finset.card_le_card h1
  have h3 := Finset.card_union_le (S.filter (fun t => w t i.succ = true))
    (S.filter (fun t => w t i.castSucc = true ∧ w t i.succ = false))
  omega

theorem qb_cnt_ge {T n : ℕ} (c : Fin (n+1) → ℕ) (w : Fin T → Fin (n+1) → Bool) (hal : qb_al c w)
    (S : Finset (Fin T)) (i : Fin n) :
    (S.filter (fun t => w t i.castSucc = true ∧ w t i.succ = false)).card ≤
    (S.filter (fun t => w t i.castSucc = true)).card - (S.filter (fun t => w t i.succ = true)).card := by
  by_cases hci : c i.castSucc ≤ c i.succ
  · have : S.filter (fun t => w t i.castSucc = true ∧ w t i.succ = false) = ∅ := by
      apply Finset.filter_false_of_mem
      intro t _ h
      have h2 := (hal t i).1 hci
      rw [h.1, h.2] at h2
      exact absurd h2 (by decide)
    rw [this]
    simp
  · have hci' : c i.succ ≤ c i.castSucc := by omega
    have hd : Disjoint (S.filter (fun t => w t i.castSucc = true ∧ w t i.succ = false))
        (S.filter (fun t => w t i.succ = true)) := by
      rw [Finset.disjoint_filter]
      intro t _ h1 h2
      rw [h1.2] at h2
      exact absurd h2 (by decide)
    have hs : S.filter (fun t => w t i.castSucc = true ∧ w t i.succ = false) ∪
        S.filter (fun t => w t i.succ = true) ⊆ S.filter (fun t => w t i.castSucc = true) := by
      intro t ht
      simp only [Finset.mem_filter, Finset.mem_union] at ht ⊢
      have h2 := (hal t i).2 hci'
      rcases ht with ⟨h3, h4, _⟩ | ⟨h3, h4⟩
      · exact ⟨h3, h4⟩
      · refine ⟨h3, ?_⟩
        rw [h4] at h2
        revert h2
        cases w t i.castSucc <;> decide
    have h5 := Finset.card_le_card hs
    rw [Finset.card_union_of_disjoint hd] at h5
    omega

theorem qb_card_lt (T k : ℕ) :
    ((Finset.univ : Finset (Fin T)).filter (fun t => t.val < k)).card ≤ k := by
  have := Finset.card_le_card_of_injOn (fun t : Fin T => t.val)
    (s := (Finset.univ : Finset (Fin T)).filter (fun t => t.val < k)) (t := Finset.range k)
    (fun a ha => by simp at ha ⊢; exact ha) (fun a _ b _ h => Fin.ext h)
  simpa using this

def qb_ext {n : ℕ} (g : Fin (n+1) → ℕ) (j : ℕ) : ℕ := if h : j < n+1 then g ⟨j, h⟩ else 0

theorem qb_ext_cs {n : ℕ} (g : Fin (n+1) → ℕ) (i : Fin n) : qb_ext g i.val = g i.castSucc := by
  unfold qb_ext
  rw [dif_pos (by omega)]
  rfl

theorem qb_ext_succ {n : ℕ} (g : Fin (n+1) → ℕ) (i : Fin n) : qb_ext g (i.val+1) = g i.succ := by
  unfold qb_ext
  rw [dif_pos (by omega)]
  rfl

theorem qb_sum_fin {n : ℕ} (g : ℕ → ℕ) :
    (Finset.univ : Finset (Fin n)).sum (fun i => g i.val - g (i.val+1)) =
      (Finset.range n).sum (fun j => g j - g (j+1)) :=
  Fin.sum_univ_eq_sum_range (fun j => g j - g (j+1)) n

theorem qb_clamp (L U y z : ℕ → ℕ) (m : ℕ) (hL : ∀ j ≤ m, L j ≤ y j) (hU : ∀ j ≤ m, y j ≤ U j)
    (h0 : z 0 = L 0) (hs : ∀ j < m, z (j+1) = max (L (j+1)) (min (U (j+1)) (z j))) :
    ∀ m' ≤ m, (Finset.range m').sum (fun j => z j - z (j+1)) + (z m' - y m') ≤
      (Finset.range m').sum (fun j => y j - y (j+1)) := by
  intro m' hm'
  induction m' with
  | zero => simp [h0]; have := hL 0 (by omega); omega
  | succ m ih =>
    have ih' := ih (by omega)
    rw [Finset.sum_range_succ, Finset.sum_range_succ, hs m (by omega)]
    have a1 := hL (m+1) hm'
    have a2 := hU (m+1) hm'
    have a3 := hL m (by omega)
    omega

theorem qb_Z_zero' (n : ℕ) (c : Fin (n+1) → ℕ) (k : ℕ) : qb_Z n c k 0 = c ⟨0, Nat.succ_pos n⟩ - k :=
  qb_Z_zero n c k

theorem qb_N (T n : ℕ) (d : Fin T → ℕ) (c : Fin (n+1) → ℕ) (w : Fin T → Fin (n+1) → Bool)
    (hc : ∀ i, ((Finset.univ : Finset (Fin T)).filter (fun t => w t i = true)).card = c i)
    (hd : ∀ t, qb_falls (w t) ≤ d t) (k : ℕ) :
    (Finset.univ : Finset (Fin n)).sum (fun i => qb_Z n c k i.castSucc.val - qb_Z n c k i.succ.val) ≤
      ((Finset.univ : Finset (Fin T)).filter (fun t => k ≤ t.val)).sum d := by
  set S := (Finset.univ : Finset (Fin T)).filter (fun t => k ≤ t.val) with hS
  let y : Fin (n+1) → ℕ := fun i => (S.filter (fun t => w t i = true)).card
  have hbox : ∀ i, c i - k ≤ y i ∧ y i ≤ c i := by
    intro i
    constructor
    · have h1 : (Finset.univ : Finset (Fin T)).filter (fun t => w t i = true) ⊆
          ((Finset.univ : Finset (Fin T)).filter (fun t => t.val < k)) ∪
            S.filter (fun t => w t i = true) := by
        intro t ht
        simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and, hS] at ht ⊢
        by_cases h : t.val < k
        · left; exact h
        · right; exact ⟨by omega, ht⟩
      have h2 := Finset.card_le_card h1
      have h3 := Finset.card_union_le ((Finset.univ : Finset (Fin T)).filter (fun t => t.val < k))
        (S.filter (fun t => w t i = true))
      have h4 := qb_card_lt T k
      rw [hc i] at h2
      show c i - k ≤ (S.filter (fun t => w t i = true)).card
      omega
    · rw [← hc i]
      apply Finset.card_le_card
      intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hS] at ht ⊢
      exact ht.2
  have hcl := qb_clamp (qb_ext (fun i => c i - k)) (qb_ext c) (qb_ext y) (qb_Z n c k) n
    (fun j hj => by
      have hj' : j < n + 1 := by omega
      simp only [qb_ext, hj', ↓reduceDIte]
      exact (hbox _).1)
    (fun j hj => by
      have hj' : j < n + 1 := by omega
      simp only [qb_ext, hj', ↓reduceDIte]
      exact (hbox _).2)
    (by
      rw [qb_Z_zero']
      have hj' : 0 < n + 1 := by omega
      simp only [qb_ext, hj', ↓reduceDIte])
    (fun j hj => by
      rw [qb_Z_succ n c k j (by omega)]
      have hj' : j + 1 < n + 1 := by omega
      simp only [qb_ext, hj', ↓reduceDIte]) n le_rfl
  have e1 : (Finset.univ : Finset (Fin n)).sum
      (fun i => qb_Z n c k i.castSucc.val - qb_Z n c k i.succ.val) =
        (Finset.range n).sum (fun j => qb_Z n c k j - qb_Z n c k (j+1)) := by
    rw [← qb_sum_fin]; rfl
  have e2 : (Finset.range n).sum (fun j => qb_ext y j - qb_ext y (j+1)) =
      (Finset.univ : Finset (Fin n)).sum (fun i => y i.castSucc - y i.succ) := by
    rw [← qb_sum_fin]
    apply Finset.sum_congr rfl
    intro i _
    rw [qb_ext_cs, qb_ext_succ]
  have e3 : (Finset.univ : Finset (Fin n)).sum (fun i => y i.castSucc - y i.succ) ≤
      S.sum (fun t => qb_falls (w t)) := by
    rw [qb_fsum]
    apply Finset.sum_le_sum
    intro i _
    exact qb_cnt_le w S i
  have e4 : S.sum (fun t => qb_falls (w t)) ≤ S.sum d := Finset.sum_le_sum (fun t _ => hd t)
  rw [e1]
  omega

theorem qb_Zbox (n : ℕ) (c : Fin (n+1) → ℕ) (k : ℕ) :
    ∀ j (h : j < n+1), qb_Z n c k j ≤ c ⟨j, h⟩ ∧ c ⟨j, h⟩ - k ≤ qb_Z n c k j := by
  intro j
  induction j with
  | zero => intro h; rw [qb_Z_zero']; omega
  | succ j ih =>
    intro h
    rw [qb_Z_succ n c k j h]
    have := ih (by omega)
    omega

theorem qb_Zmono (n : ℕ) (c : Fin (n+1) → ℕ) (k : ℕ) :
    ∀ j, j < n+1 → qb_Z n c (k+1) j ≤ qb_Z n c k j ∧ qb_Z n c k j ≤ qb_Z n c (k+1) j + 1 := by
  intro j
  induction j with
  | zero => intro h; rw [qb_Z_zero', qb_Z_zero']; omega
  | succ j ih =>
    intro h
    rw [qb_Z_succ n c k j h, qb_Z_succ n c (k+1) j h]
    have := ih (by omega)
    omega

theorem qb_Z0 (n : ℕ) (c : Fin (n+1) → ℕ) : ∀ j (h : j < n+1), qb_Z n c 0 j = c ⟨j, h⟩ := by
  intro j h
  cases j with
  | zero => rw [qb_Z_zero']; simp
  | succ j => rw [qb_Z_succ n c 0 j h]; omega

theorem qb_ZT (T n : ℕ) (c : Fin (n+1) → ℕ) (hc : ∀ i, c i ≤ T) :
    ∀ j, j < n+1 → qb_Z n c T j = 0 := by
  intro j
  induction j with
  | zero => intro h; rw [qb_Z_zero']; have := hc ⟨0, h⟩; omega
  | succ j ih =>
    intro h
    rw [qb_Z_succ n c T j h]
    have := hc ⟨j+1, h⟩
    have := ih (by omega)
    omega

theorem qb_tele (f : ℕ → ℕ) (hf : ∀ t, f (t+1) ≤ f t ∧ f t ≤ f (t+1) + 1) (k : ℕ) :
    ∀ m, k ≤ m → ((Finset.range m).filter (fun t => k ≤ t ∧ f (t+1) < f t)).card + f m = f k := by
  intro m hm
  induction m with
  | zero =>
    have : k = 0 := by omega
    subst this
    simp
  | succ m ih =>
    by_cases hkm : k ≤ m
    · rw [Finset.range_add_one, Finset.filter_insert]
      have ih' := ih hkm
      have := hf m
      split_ifs with h
      · rw [Finset.card_insert_of_notMem (by simp)]
        omega
      · omega
    · have : k = m + 1 := by omega
      subst this
      have : (Finset.range (m+1)).filter (fun t => m + 1 ≤ t ∧ f (t+1) < f t) = ∅ := by
        apply Finset.filter_false_of_mem
        intro t ht
        simp at ht
        omega
      rw [this]
      simp

theorem qb_finrange_card (T : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    ((Finset.univ : Finset (Fin T)).filter (fun t => P t.val)).card =
      ((Finset.range T).filter P).card := by
  rw [Finset.card_filter, Finset.card_filter]
  exact Fin.sum_univ_eq_sum_range (fun t => if P t then 1 else 0) T

def qb_w0 (T n : ℕ) (c : Fin (n+1) → ℕ) : Fin T → Fin (n+1) → Bool :=
  fun t i => decide (qb_Z n c (t.val+1) i.val < qb_Z n c t.val i.val)

theorem qb_w0_cnt (T n : ℕ) (c : Fin (n+1) → ℕ) (hc : ∀ i, c i ≤ T) (k : ℕ) (hk : k ≤ T)
    (i : Fin (n+1)) :
    (((Finset.univ : Finset (Fin T)).filter (fun t => k ≤ t.val)).filter
      (fun t => qb_w0 T n c t i = true)).card = qb_Z n c k i.val := by
  rw [Finset.filter_filter]
  have := qb_finrange_card T (fun t => k ≤ t ∧ qb_Z n c (t+1) i.val < qb_Z n c t i.val)
  simp only [qb_w0, decide_eq_true_eq]
  rw [this]
  have h2 := qb_tele (fun t => qb_Z n c t i.val) (fun t => qb_Zmono n c t i.val i.isLt) k T hk
  have h3 := qb_ZT T n c hc i.val i.isLt
  omega

theorem qb_w0_col (T n : ℕ) (c : Fin (n+1) → ℕ) (hc : ∀ i, c i ≤ T) (i : Fin (n+1)) :
    ((Finset.univ : Finset (Fin T)).filter (fun t => qb_w0 T n c t i = true)).card = c i := by
  have h := qb_w0_cnt T n c hc 0 (Nat.zero_le _) i
  have e : (Finset.univ : Finset (Fin T)).filter (fun t => 0 ≤ t.val) = Finset.univ :=
    Finset.filter_true_of_mem (fun t _ => Nat.zero_le _)
  rw [e, qb_Z0 n c i.val i.isLt] at h
  exact h

theorem qb_w0_al (T n : ℕ) (c : Fin (n+1) → ℕ) : qb_al c (qb_w0 T n c) := by
  intro t i
  have m1 : qb_Z n c (t.val+1) i.val ≤ qb_Z n c t.val i.val ∧
      qb_Z n c t.val i.val ≤ qb_Z n c (t.val+1) i.val + 1 := qb_Zmono n c t.val i.val (by omega)
  have b1 : qb_Z n c t.val i.val ≤ c i.castSucc ∧ c i.castSucc - t.val ≤ qb_Z n c t.val i.val :=
    qb_Zbox n c t.val i.val (by omega)
  have b2 : qb_Z n c (t.val+1) i.val ≤ c i.castSucc ∧
      c i.castSucc - (t.val+1) ≤ qb_Z n c (t.val+1) i.val :=
    qb_Zbox n c (t.val+1) i.val (by omega)
  have s1 : qb_Z n c t.val (i.val+1) =
      max (c i.succ - t.val) (min (c i.succ) (qb_Z n c t.val i.val)) :=
    qb_Z_succ n c t.val i.val (by omega)
  have s2 : qb_Z n c (t.val+1) (i.val+1) =
      max (c i.succ - (t.val+1)) (min (c i.succ) (qb_Z n c (t.val+1) i.val)) :=
    qb_Z_succ n c (t.val+1) i.val (by omega)
  constructor
  · intro h
    show decide (qb_Z n c (t.val+1) i.val < qb_Z n c t.val i.val) ≤
      decide (qb_Z n c (t.val+1) (i.val+1) < qb_Z n c t.val (i.val+1))
    by_cases h1 : qb_Z n c (t.val+1) i.val < qb_Z n c t.val i.val <;>
      by_cases h2 : qb_Z n c (t.val+1) (i.val+1) < qb_Z n c t.val (i.val+1) <;>
        simp [h1, h2] <;> omega
  · intro h
    show decide (qb_Z n c (t.val+1) (i.val+1) < qb_Z n c t.val (i.val+1)) ≤
      decide (qb_Z n c (t.val+1) i.val < qb_Z n c t.val i.val)
    by_cases h1 : qb_Z n c (t.val+1) i.val < qb_Z n c t.val i.val <;>
      by_cases h2 : qb_Z n c (t.val+1) (i.val+1) < qb_Z n c t.val (i.val+1) <;>
        simp [h1, h2] <;> omega

theorem qb_w0_falls (T n : ℕ) (c : Fin (n+1) → ℕ) (hc : ∀ i, c i ≤ T) (k : ℕ) (hk : k ≤ T) :
    ((Finset.univ : Finset (Fin T)).filter (fun t => k ≤ t.val)).sum
      (fun t => qb_falls (qb_w0 T n c t)) ≤
    (Finset.univ : Finset (Fin n)).sum (fun i => qb_Z n c k i.castSucc.val - qb_Z n c k i.succ.val) := by
  rw [qb_fsum]
  apply Finset.sum_le_sum
  intro i _
  have := qb_cnt_ge c (qb_w0 T n c) (qb_w0_al T n c)
    ((Finset.univ : Finset (Fin T)).filter (fun t => k ≤ t.val)) i
  rw [qb_w0_cnt T n c hc k hk, qb_w0_cnt T n c hc k hk] at this
  exact this

def qb_eb {n : ℕ} (u : Fin (n+1) → Bool) (j : ℕ) : Bool := if h : j < n+1 then u ⟨j, h⟩ else false

def qb_fl {n : ℕ} (u : Fin (n+1) → Bool) (j : ℕ) : ℕ :=
  if qb_eb u j = true ∧ qb_eb u (j+1) = false then 1 else 0

theorem qb_falls_eq {n : ℕ} (u : Fin (n+1) → Bool) :
    qb_falls u = (Finset.range n).sum (qb_fl u) := by
  unfold qb_falls
  rw [Finset.card_filter, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  unfold qb_fl qb_eb
  rw [dif_pos (show i.val < n+1 by omega), dif_pos (show i.val + 1 < n+1 by omega)]
  rfl

theorem qb_ivt (P Q : ℕ → Bool) (n : ℕ) (fp fq : ℕ → ℕ)
    (hfp : ∀ j, fp j = if P j = true ∧ P (j+1) = false then 1 else 0)
    (hfq : ∀ j, fq j = if Q j = true ∧ Q (j+1) = false then 1 else 0)
    (hJ : ∀ j < n, ¬(P j = true ∧ P (j+1) = false ∧ Q j = false ∧ Q (j+1) = true) ∧
      ¬(Q j = true ∧ Q (j+1) = false ∧ P j = false ∧ P (j+1) = true))
    (G : ℕ → ℕ) (hG0 : G 0 + 2 ≤ G n) (hGs : ∀ j < n, G (j+1) + fq j = G j + fp j) :
    ∃ a ≤ n, P a = Q a ∧ G a + 1 = G n := by
  have key : ∀ j ≤ n, (∃ a ≤ j, P a = Q a ∧ G a + 1 = G n) ∨ G j + 1 < G n ∨
      (G j + 1 = G n ∧ P j = false ∧ Q j = true) := by
    intro j hj
    induction j with
    | zero => right; left; omega
    | succ j ih =>
      have ih' := ih (by omega)
      have hs := hGs j (by omega)
      have hJj := hJ j (by omega)
      rw [hfp j, hfq j] at hs
      rcases ih' with ⟨a, ha, h1, h2⟩ | h | ⟨h, h1, h2⟩
      · left; exact ⟨a, by omega, h1, h2⟩
      · by_cases hlt : G (j+1) + 1 < G n
        · right; left; exact hlt
        · have hx : G (j+1) + 1 = G n ∧ P (j+1) = false ∧ Q j = Q (j+1) := by
            cases hP : P j <;> cases hP1 : P (j+1) <;> cases hQ : Q j <;> cases hQ1 : Q (j+1) <;>
              simp [hP, hP1, hQ, hQ1] at hs hJj ⊢ <;> omega
          cases hQ1 : Q (j+1)
          · left; exact ⟨j+1, le_rfl, by rw [hx.2.1, hQ1], hx.1⟩
          · right; right; exact ⟨hx.1, hx.2.1, rfl⟩
      · rw [h1, h2] at hs
        cases hQ1 : Q (j+1)
        · right; left
          rw [hQ1] at hs
          simp at hs
          omega
        · rw [hQ1] at hs
          simp at hs
          cases hP1 : P (j+1)
          · right; right; exact ⟨by omega, rfl, rfl⟩
          · left; exact ⟨j+1, le_rfl, by rw [hP1, hQ1], by omega⟩
  rcases key n le_rfl with h | h | ⟨h, _, _⟩
  · exact h
  · omega
  · omega

theorem qb_eb_cs {n : ℕ} (u : Fin (n+1) → Bool) (i : Fin n) : qb_eb u i.val = u i.castSucc := by
  unfold qb_eb
  rw [dif_pos (by omega)]
  rfl

theorem qb_eb_succ {n : ℕ} (u : Fin (n+1) → Bool) (i : Fin n) :
    qb_eb u (i.val+1) = u i.succ := by
  unfold qb_eb
  rw [dif_pos (by omega)]
  rfl

theorem qb_transfer {T n : ℕ} (c : Fin (n+1) → ℕ) (w : Fin T → Fin (n+1) → Bool)
    (hal : qb_al c w) (p q : Fin T) (hpq : p ≠ q)
    (hf : qb_falls (w q) + 2 ≤ qb_falls (w p)) :
    ∃ w' : Fin T → Fin (n+1) → Bool, qb_al c w' ∧
      (∀ i, ((Finset.univ : Finset (Fin T)).filter (fun t => w' t i = true)).card =
            ((Finset.univ : Finset (Fin T)).filter (fun t => w t i = true)).card) ∧
      qb_falls (w' p) + 1 = qb_falls (w p) ∧ qb_falls (w' q) = qb_falls (w q) + 1 ∧
      ∀ t, t ≠ p → t ≠ q → w' t = w t := by
  have hJ : ∀ j < n, ¬(qb_eb (w p) j = true ∧ qb_eb (w p) (j+1) = false ∧
      qb_eb (w q) j = false ∧ qb_eb (w q) (j+1) = true) ∧
      ¬(qb_eb (w q) j = true ∧ qb_eb (w q) (j+1) = false ∧
        qb_eb (w p) j = false ∧ qb_eb (w p) (j+1) = true) := by
    intro j hj
    have e1 := qb_eb_cs (w p) ⟨j, hj⟩
    have e2 := qb_eb_succ (w p) ⟨j, hj⟩
    have e3 := qb_eb_cs (w q) ⟨j, hj⟩
    have e4 := qb_eb_succ (w q) ⟨j, hj⟩
    simp only at e1 e2 e3 e4
    rw [e1, e2, e3, e4]
    have h1 := hal p ⟨j, hj⟩
    have h2 := hal q ⟨j, hj⟩
    by_cases hc : c (Fin.castSucc ⟨j, hj⟩) ≤ c (Fin.succ ⟨j, hj⟩)
    · have a1 := h1.1 hc
      have a2 := h2.1 hc
      constructor
      · rintro ⟨b1, b2, _, _⟩
        rw [b1, b2] at a1
        exact absurd a1 (by decide)
      · rintro ⟨b1, b2, _, _⟩
        rw [b1, b2] at a2
        exact absurd a2 (by decide)
    · have hc' : c (Fin.succ ⟨j, hj⟩) ≤ c (Fin.castSucc ⟨j, hj⟩) := by omega
      have a1 := h1.2 hc'
      have a2 := h2.2 hc'
      constructor
      · rintro ⟨_, _, b3, b4⟩
        rw [b3, b4] at a2
        exact absurd a2 (by decide)
      · rintro ⟨_, _, b3, b4⟩
        rw [b3, b4] at a1
        exact absurd a1 (by decide)
  set G : ℕ → ℕ := fun a => (Finset.range n).sum
    (fun j => if j < a then qb_fl (w p) j else qb_fl (w q) j) with hGdef
  have hG0 : G 0 = qb_falls (w q) := by
    rw [qb_falls_eq, hGdef]
    simp
  have hGn : G n = qb_falls (w p) := by
    rw [qb_falls_eq, hGdef]
    apply Finset.sum_congr rfl
    intro j hj
    rw [if_pos (Finset.mem_range.mp hj)]
  have hGs : ∀ j < n, G (j+1) + qb_fl (w q) j = G j + qb_fl (w p) j := by
    intro j hj
    have hm : j ∈ Finset.range n := Finset.mem_range.mpr hj
    have r1 := (Finset.add_sum_erase (Finset.range n)
      (fun i => if i < j + 1 then qb_fl (w p) i else qb_fl (w q) i) hm).symm
    have r2 := (Finset.add_sum_erase (Finset.range n)
      (fun i => if i < j then qb_fl (w p) i else qb_fl (w q) i) hm).symm
    have r3 : ((Finset.range n).erase j).sum
        (fun i => if i < j + 1 then qb_fl (w p) i else qb_fl (w q) i) =
        ((Finset.range n).erase j).sum
        (fun i => if i < j then qb_fl (w p) i else qb_fl (w q) i) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hij : i ≠ j := Finset.ne_of_mem_erase hi
      by_cases h : i < j
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]
    simp only [hGdef]
    rw [r1, r2, r3]
    simp
    omega
  obtain ⟨a, ha, hag, hGa⟩ := qb_ivt (qb_eb (w p)) (qb_eb (w q)) n (qb_fl (w p)) (qb_fl (w q))
    (fun j => rfl) (fun j => rfl) hJ G (by rw [hG0, hGn]; exact hf) hGs
  have hagree : w p ⟨a, by omega⟩ = w q ⟨a, by omega⟩ := by
    unfold qb_eb at hag
    rw [dif_pos (by omega), dif_pos (by omega)] at hag
    exact hag
  have hsw : ∀ t, w (Equiv.swap p q t) ⟨a, by omega⟩ = w t ⟨a, by omega⟩ := by
    intro t
    by_cases h1 : t = p
    · subst h1; rw [Equiv.swap_apply_left]; exact hagree.symm
    · by_cases h2 : t = q
      · subst h2; rw [Equiv.swap_apply_right]; exact hagree
      · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
  refine ⟨fun t i => if a < i.val then w (Equiv.swap p q t) i else w t i, ?_, ?_, ?_, ?_, ?_⟩
  · intro t i
    simp only [Fin.coe_castSucc, Fin.val_succ]
    rcases lt_trichotomy a i.val with h | h | h
    · rw [if_pos h, if_pos (by omega)]
      exact hal _ i
    · rw [if_neg (by omega), if_pos (by omega)]
      have e : i.castSucc = ⟨a, by omega⟩ := Fin.ext (by simp [h])
      have e2 : w t i.castSucc = w (Equiv.swap p q t) i.castSucc := by
        rw [e]; exact (hsw t).symm
      rw [e2]
      exact hal _ i
    · rw [if_neg (by omega), if_neg (by omega)]
      exact hal t i
  · intro i
    by_cases h : a < i.val
    · simp only [h, if_true]
      rw [Finset.card_filter, Finset.card_filter]
      exact Equiv.sum_comp (Equiv.swap p q) (fun t => if w t i = true then 1 else 0)
    · simp only [h, if_false]
  · have hfl : ∀ j ∈ Finset.range n, qb_fl (fun i => if a < i.val then w (Equiv.swap p q p) i
        else w p i) j = if j < a then qb_fl (w p) j else qb_fl (w q) j := by
      intro j hj
      have hj' := Finset.mem_range.mp hj
      have hj1 : j < n + 1 := by omega
      have hj2 : j + 1 < n + 1 := by omega
      rw [Equiv.swap_apply_left]
      simp only [qb_fl, qb_eb, hj1, hj2, ↓reduceDIte, Fin.val_mk]
      rcases lt_trichotomy j a with h | h | h
      · have h1 : ¬ a < j := by omega
        have h2 : ¬ a < j + 1 := by omega
        simp only [h, h1, h2, ↓reduceIte]
      · subst h
        have h1 : ¬ j < j := lt_irrefl j
        have h2 : j < j + 1 := Nat.lt_succ_self j
        simp only [h1, h2, ↓reduceIte, hagree]
      · have h1 : ¬ j < a := by omega
        have h2 : a < j + 1 := by omega
        simp only [h, h1, h2, ↓reduceIte]
    rw [qb_falls_eq, Finset.sum_congr rfl hfl]
    rw [← hGn, ← hGa]
  · have hfl : ∀ j ∈ Finset.range n, qb_fl (fun i => if a < i.val then w (Equiv.swap p q q) i
        else w q i) j = if j < a then qb_fl (w q) j else qb_fl (w p) j := by
      intro j hj
      have hj' := Finset.mem_range.mp hj
      have hj1 : j < n + 1 := by omega
      have hj2 : j + 1 < n + 1 := by omega
      rw [Equiv.swap_apply_right]
      simp only [qb_fl, qb_eb, hj1, hj2, ↓reduceDIte, Fin.val_mk]
      rcases lt_trichotomy j a with h | h | h
      · have h1 : ¬ a < j := by omega
        have h2 : ¬ a < j + 1 := by omega
        simp only [h, h1, h2, ↓reduceIte]
      · subst h
        have h1 : ¬ j < j := lt_irrefl j
        have h2 : j < j + 1 := Nat.lt_succ_self j
        simp only [h1, h2, ↓reduceIte, hagree]
      · have h1 : ¬ j < a := by omega
        have h2 : a < j + 1 := by omega
        simp only [h, h1, h2, ↓reduceIte]
    rw [qb_falls_eq, Finset.sum_congr rfl hfl]
    have htot : (Finset.range n).sum (fun j => if j < a then qb_fl (w q) j else qb_fl (w p) j) +
        G a = qb_falls (w p) + qb_falls (w q) := by
      rw [hGdef, qb_falls_eq, qb_falls_eq, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> omega
    omega
  · intro t h1 h2
    funext i
    simp [Equiv.swap_apply_of_ne_of_ne h1 h2]

theorem qb_B (T n : ℕ) (d : Fin T → ℕ) (c : Fin (n+1) → ℕ) (hd : Antitone d) :
    ∀ (m : ℕ) (w : Fin T → Fin (n+1) → Bool), qb_al c w →
      (∀ i, ((Finset.univ : Finset (Fin T)).filter (fun t => w t i = true)).card = c i) →
      (∀ k, ((Finset.univ : Finset (Fin T)).filter (fun t => k ≤ t.val)).sum
          (fun t => qb_falls (w t)) ≤
        ((Finset.univ : Finset (Fin T)).filter (fun t => k ≤ t.val)).sum d) →
      (Finset.univ : Finset (Fin T)).sum (fun t => qb_falls (w t) - d t) = m →
      ∃ w' : Fin T → Fin (n+1) → Bool, qb_al c w' ∧
        (∀ i, ((Finset.univ : Finset (Fin T)).filter (fun t => w' t i = true)).card = c i) ∧
        ∀ t, qb_falls (w' t) ≤ d t := by
  intro m
  induction m with
  | zero =>
    intro w hal hcol _ hOL
    refine ⟨w, hal, hcol, ?_⟩
    intro t
    have := (Finset.sum_eq_zero_iff.mp hOL) t (Finset.mem_univ t)
    omega
  | succ m ih =>
    intro w hal hcol hsuf hOL
    have hex : ∃ t, d t < qb_falls (w t) := by
      by_contra hne
      push_neg at hne
      have : (Finset.univ : Finset (Fin T)).sum (fun t => qb_falls (w t) - d t) = 0 :=
        Finset.sum_eq_zero (fun t _ => by have := hne t; omega)
      omega
    obtain ⟨p, hpO, hpmax'⟩ : ∃ p, p ∈ (Finset.univ : Finset (Fin T)).filter
        (fun t => d t < qb_falls (w t)) ∧ ∀ t ∈ (Finset.univ : Finset (Fin T)).filter
        (fun t => d t < qb_falls (w t)), t ≤ p := by
      obtain ⟨t0, ht0⟩ := hex
      have hO : ((Finset.univ : Finset (Fin T)).filter (fun t => d t < qb_falls (w t))).Nonempty :=
        ⟨t0, by simp [ht0]⟩
      exact ⟨_, Finset.max'_mem _ hO, fun t ht => Finset.le_max' _ t ht⟩
    have hp : d p < qb_falls (w p) := (Finset.mem_filter.mp hpO).2
    have hpmax : ∀ t, p < t → qb_falls (w t) ≤ d t := by
      intro t hpt
      by_contra h
      push_neg at h
      have := hpmax' t (by simp [h])
      exact absurd hpt (not_lt.mpr this)
    have hsp := hsuf p.val
    have hsplit : (Finset.univ : Finset (Fin T)).filter (fun t : Fin T => p.val ≤ t.val) =
        insert p ((Finset.univ : Finset (Fin T)).filter (fun t => p < t)) := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · intro h
        by_cases h2 : t = p
        · left; exact h2
        · right; rw [Fin.lt_def]; have : t.val ≠ p.val := fun e => h2 (Fin.ext e); omega
      · rintro (h | h)
        · rw [h]
        · rw [Fin.lt_def] at h; omega
    rw [hsplit, Finset.sum_insert (by simp), Finset.sum_insert (by simp)] at hsp
    have hlt : ((Finset.univ : Finset (Fin T)).filter (fun t => p < t)).sum
        (fun t => qb_falls (w t)) < ((Finset.univ : Finset (Fin T)).filter (fun t => p < t)).sum
          (fun t => d t) := by
      omega
    obtain ⟨q, hqmem, hq⟩ := Finset.exists_lt_of_sum_lt hlt
    have hpq : p < q := (Finset.mem_filter.mp hqmem).2
    have hdq : d q ≤ d p := hd (le_of_lt hpq)
    obtain ⟨w', hal', hcol', hfp, hfq, hoth⟩ :=
      qb_transfer c w hal p q (ne_of_lt hpq) (by omega)
    apply ih w' hal' (fun i => (hcol' i).trans (hcol i))
    · intro k
      by_cases hk : k ≤ p.val
      · have e : ∀ t, qb_falls (w' t) + (if t = p then 1 else 0) =
            qb_falls (w t) + (if t = q then 1 else 0) := by
          intro t
          by_cases h1 : t = p
          · subst h1
            have : t ≠ q := ne_of_lt hpq
            simp only [this, if_true, if_false]
            omega
          · by_cases h2 : t = q
            · subst h2
              simp only [h1, if_true, if_false]
              omega
            · simp only [h1, h2, if_false, hoth t h1 h2]
        have hsum := Finset.sum_congr rfl
          (fun t (_ : t ∈ (Finset.univ : Finset (Fin T)).filter (fun t => k ≤ t.val)) => e t)
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
          at hsum
        have hpm : p ∈ (Finset.univ : Finset (Fin T)).filter (fun t => k ≤ t.val) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hk
        have hqm : q ∈ (Finset.univ : Finset (Fin T)).filter (fun t => k ≤ t.val) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rw [Fin.lt_def] at hpq; omega
        rw [if_pos hpm, if_pos hqm] at hsum
        have := hsuf k
        omega
      · apply Finset.sum_le_sum
        intro t ht
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
        have hpt : p < t := by rw [Fin.lt_def]; omega
        by_cases h2 : t = q
        · subst h2; omega
        · rw [hoth t (ne_of_gt hpt) h2]; exact hpmax t hpt
    · have e : ∀ t, (qb_falls (w' t) - d t) + (if t = p then 1 else 0) = qb_falls (w t) - d t := by
        intro t
        by_cases h1 : t = p
        · subst h1
          simp only [if_true]
          omega
        · by_cases h2 : t = q
          · subst h2
            simp only [h1, if_false]
            omega
          · simp only [h1, if_false, hoth t h1 h2, Nat.add_zero]
      have hsum := Finset.sum_congr rfl (fun t (_ : t ∈ (Finset.univ : Finset (Fin T))) => e t)
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_univ p)] at hsum
      omega

end Track

theorem trackCriterion : ∀ (T n : Nat) (d : Fin T → Nat) (c : Fin (n+1) → Nat),
  Antitone d → (∀ i, c i ≤ T) →
  let tail := fun (k : Nat) => ((Finset.univ : Finset (Fin T)).filter (fun t => k ≤ t.val)).sum d
  let rem := fun (k : Nat) (i : Fin (n+1)) =>
    ((List.finRange (n+1)).scanl
      (fun z j => max (c j - k) (min (c j) z)) 0).getD (i.val+1) 0
  let falls := fun (w : Fin (n+1) → Bool) =>
    ((Finset.univ : Finset (Fin n)).filter (fun i => w i.castSucc = true ∧ w i.succ = false)).card
  let fits := fun (w : Fin T → Fin (n+1) → Bool) =>
    (∀ i, ((Finset.univ : Finset (Fin T)).filter (fun t => w t i = true)).card = c i) ∧
    (∀ t, falls (w t) ≤ d t)
  let aligned := fun (w : Fin T → Fin (n+1) → Bool) => ∀ (t : Fin T) (i : Fin n),
    (c i.castSucc ≤ c i.succ → w t i.castSucc ≤ w t i.succ) ∧
    (c i.succ ≤ c i.castSucc → w t i.succ ≤ w t i.castSucc)
  let bounds := ∀ k ≤ T, (Finset.univ : Finset (Fin n)).sum
    (fun i => rem k i.castSucc - rem k i.succ) ≤ tail k
  ((∃ w, fits w) ↔ bounds) ∧ (bounds → ∃ w, fits w ∧ aligned w) := by
  intro T n d c hd hc tail rem falls fits aligned bounds
  have hN : (∃ w, fits w) → bounds := by
    rintro ⟨w, hcol, hfl⟩ k _
    exact Track.qb_N T n d c w hcol hfl k
  have hS : bounds → ∃ w, fits w ∧ aligned w := by
    intro hb
    have hsuf : ∀ k, ((Finset.univ : Finset (Fin T)).filter (fun t => k ≤ t.val)).sum
        (fun t => Track.qb_falls
          (Track.qb_w0 T n c t)) ≤
        ((Finset.univ : Finset (Fin T)).filter (fun t => k ≤ t.val)).sum d := by
      intro k
      by_cases hk : k ≤ T
      · exact (Track.qb_w0_falls T n c hc k hk).trans (hb k hk)
      · have : (Finset.univ : Finset (Fin T)).filter (fun t : Fin T => k ≤ t.val) = ∅ :=
          Finset.filter_false_of_mem (fun t _ => by have := t.isLt; omega)
        simp only [this, Finset.sum_empty, le_refl]
    obtain ⟨w, hal, hcol, hfl⟩ := Track.qb_B T n d c hd
      ((Finset.univ : Finset (Fin T)).sum (fun t =>
        Track.qb_falls (Track.qb_w0 T n c t) - d t))
      (Track.qb_w0 T n c) (Track.qb_w0_al T n c)
      (Track.qb_w0_col T n c hc) hsuf rfl
    exact ⟨w, ⟨hcol, hfl⟩, hal⟩
  exact ⟨⟨hN, fun hb => (hS hb).elim (fun w hw => ⟨w, hw.1⟩)⟩, hS⟩

def path (n : ℕ) (lo hi : Fin (n+1) → ℕ) (i : ℕ) : ℕ :=
  ((List.finRange (n+1)).scanl (fun z j => max (lo j) (min (hi j) z)) 0).getD (i+1) 0

theorem path_zero (n : ℕ) (lo hi : Fin (n+1) → ℕ) : path n lo hi 0 = lo 0 := by
  unfold path
  rw [List.getD_eq_getElem?_getD, List.getElem?_succ_scanl]
  simp

theorem path_succ (n : ℕ) (lo hi : Fin (n+1) → ℕ) (i : ℕ) (h : i + 1 < n + 1) :
    path n lo hi (i+1) = max (lo ⟨i+1, h⟩) (min (hi ⟨i+1, h⟩) (path n lo hi i)) := by
  unfold path
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_succ_scanl]
  have h1 : ((List.finRange (n+1)).scanl (fun z j => max (lo j) (min (hi j) z)) 0)[i+1]? =
      some (((List.finRange (n+1)).scanl (fun z j => max (lo j) (min (hi j) z)) 0)[i+1]'(by simp; omega)) :=
    List.getElem?_eq_getElem _
  have h2 : (List.finRange (n+1))[i+1]? = some ⟨i+1, h⟩ := by
    rw [List.getElem?_eq_getElem (by simp; omega)]
    simp
  rw [h1, h2]
  simp

def idx (n j : ℕ) : Fin (n+1) := ⟨min j n, by omega⟩

theorem idx_at {n} (i : Fin (n+1)) : idx n i.val = i := by
  apply Fin.ext
  exact min_eq_left (by omega)

def loss (z : ℕ → ℕ) (j : ℕ) := (Finset.range j).sum (fun i => z i - z (i+1))

theorem loss_succ (z : ℕ → ℕ) (j : ℕ) : loss z (j+1) = loss z j + (z j-z (j+1)) :=
  Finset.sum_range_succ ..

theorem loss_mono (z : ℕ → ℕ) : Monotone (loss z) := by
  apply monotone_nat_of_le_succ
  intro j
  rw [loss_succ]
  omega

theorem loss_segment (z : ℕ → ℕ) {u v : ℕ} (h : u ≤ v) :
    loss z u + (z u-z v) ≤ loss z v := by
  have hp : Monotone (fun i => loss z i + z i) := by
    apply monotone_nat_of_le_succ
    intro i
    change loss z i + z i ≤ loss z (i+1) + z (i+1)
    rw [loss_succ]
    omega
  have h₁ := hp h
  have h₂ := loss_mono z h
  change loss z u + z u ≤ loss z v + z v at h₁
  omega

structure Family (m : ℕ) where
  u : Fin m → ℕ
  v : Fin m → ℕ
  valid : ∀ i, u i ≤ v i
  ordered : ∀ i j, i < j → v i ≤ u j

def Family.ends {m} (f : Family m) (t : ℕ) := ∀ i, f.v i ≤ t
def Family.score {m} (f : Family m) (L U : ℕ → ℕ) :=
  ∑ i, (L (f.u i) - U (f.v i))

def nilFam : Family 0 := ⟨Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩

def Family.push {m} (f : Family m) (a t : ℕ) (ha : f.ends a) (hat : a ≤ t) : Family (m+1) where
  u := Fin.lastCases a f.u
  v := Fin.lastCases t f.v
  valid := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hat
    · simpa using f.valid j
  ordered := by
    intro i j
    refine Fin.lastCases ?_ (fun i => ?_) i
    · intro h
      exact False.elim ((not_lt_of_ge (Fin.le_last j)) h)
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · intro _
        simpa using ha i
      · intro h
        simpa using f.ordered i j (Fin.castSucc_lt_castSucc_iff.mp h)

theorem push_ends {m} (f : Family m) (a t) (ha : f.ends a) (hat : a ≤ t) :
    (f.push a t ha hat).ends t := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [Family.push]
  · simpa [Family.push] using (ha j).trans hat

theorem push_score {m} (f : Family m) (a t) (ha : f.ends a) (hat : a ≤ t) (L U) :
    (f.push a t ha hat).score L U = f.score L U + (L a - U t) := by
  simp [Family.score, Fin.sum_univ_castSucc, Family.push]

theorem family_le (z L U : ℕ → ℕ) {n} (box : ∀ j ≤ n, L j ≤ z j ∧ z j ≤ U j)
    (m) (f : Family m) (he : f.ends n) : f.score L U ≤ loss z n := by
  induction m generalizing n with
  | zero => simp [Family.score]
  | succ m ih =>
    let last := Fin.last m
    let g : Family m := ⟨fun i => f.u i.castSucc, fun i => f.v i.castSucc,
      fun i => f.valid _, fun i j h => f.ordered _ _ (Fin.castSucc_lt_castSucc_iff.mpr h)⟩
    have ge : g.ends (f.u last) := fun i => f.ordered _ _ (Fin.castSucc_lt_last i)
    have uv := f.valid last
    have vn := he last
    have earlier := ih (n := f.u last) (fun j hj => box j (by omega)) g ge
    have seg := loss_segment z uv
    have later := loss_mono z vn
    have l := (box (f.u last) (by omega)).1
    have u := (box (f.v last) vn).2
    unfold Family.score
    rw [Fin.sum_univ_castSucc]
    change g.score L U + (L (f.u last) - U (f.v last)) ≤ _
    omega

theorem attain (L U z : ℕ → ℕ) {n} (zero : z 0 = L 0)
    (step : ∀ j < n, z (j+1) = max (L (j+1)) (min (U (j+1)) (z j)))
    (box : ∀ j ≤ n, L j ≤ U j) :
    ∃ (m : ℕ) (f : Family m), f.ends n ∧ loss z n ≤ f.score L U := by
  let closed (j : ℕ) := ∃ (m : ℕ) (f : Family m), f.ends j ∧ loss z j ≤ f.score L U
  let pending (j : ℕ) := ∃ a ≤ j, ∃ (m : ℕ) (f : Family m), f.ends a ∧
    loss z j + z j ≤ f.score L U + L a
  have both : ∀ j ≤ n, closed j ∧ pending j := by
    intro j
    induction j with
    | zero =>
      intro _
      have e : nilFam.ends 0 := fun i => i.elim0
      exact ⟨⟨0,nilFam,e,by simp [loss]⟩,⟨0,le_rfl,0,nilFam,e,by simp [loss,zero]⟩⟩
    | succ j ih =>
      intro hj
      obtain ⟨⟨m,f,hf,cf⟩,a,aj,p,g,hg,cg⟩ := ih (by omega)
      have s := step j (by omega)
      have lu := box (j+1) hj
      have old : f.ends (j+1) := fun i => (hf i).trans (by omega)
      have hfall := loss_succ z j
      constructor
      · by_cases h : z (j+1) < z j
        · have hat : a ≤ j+1 := by omega
          exact ⟨_,g.push a (j+1) hg hat,push_ends g a (j+1) hg hat,by rw [push_score]; omega⟩
        · exact ⟨m,f,old,by omega⟩
      · by_cases h : z j < z (j+1)
        · exact ⟨j+1,le_rfl,m,f,old,by omega⟩
        · exact ⟨a,by omega,p,g,hg,by omega⟩
  exact (both n le_rfl).1

open Track

abbrev Budget {T} (d : Fin T → ℕ) (k : ℕ) :=
  ((Finset.univ : Finset (Fin T)).filter (fun t => k ≤ t.val)).sum d

abbrev Bounds {T n} (d : Fin T → ℕ) (lo hi : Fin (n+1) → ℕ) :=
  ∀ k ≤ T, ∀ (m : ℕ) (u v : Fin m → Fin (n+1)),
    (∀ i, u i ≤ v i) → (∀ i j, i < j → v i ≤ u j) →
    ∑ j, (lo (u j) - hi (v j) - k) ≤ Budget d k

def X {n} (lo hi : Fin (n+1) → ℕ) (i : Fin (n+1)) := path n lo hi i.val

theorem xbox {n} (lo hi : Fin (n+1) → ℕ) (bh : ∀ i, lo i ≤ hi i) (i) :
    lo i ≤ X lo hi i ∧ X lo hi i ≤ hi i := by
  obtain ⟨j,hj⟩ := i
  cases j with
  | zero =>
    unfold X
    rw [path_zero]
    exact ⟨le_rfl,bh _⟩
  | succ j =>
    change lo _ ≤ path n lo hi (j+1) ∧ path n lo hi (j+1) ≤ _
    rw [path_succ _ _ _ _ hj]
    have h := bh ⟨j+1,hj⟩
    omega

theorem shift_step {n} (lo hi : Fin (n+1) → ℕ) (k j : ℕ) (hj : j < n)
    (bh : ∀ i, lo i ≤ hi i) :
    qb_Z n (X lo hi) k (j+1) = max (lo (idx n (j+1))-k)
      (min (hi (idx n (j+1))) (qb_Z n (X lo hi) k j)) := by
  let i : Fin (n+1) := ⟨j,by omega⟩
  let i' : Fin (n+1) := ⟨j+1,by omega⟩
  have he : idx n (j+1) = i' := idx_at i'
  rw [he,qb_Z_succ _ _ _ _ i'.isLt]
  have z := qb_Zbox n (X lo hi) k j i.isLt
  change qb_Z n (X lo hi) k j ≤ X lo hi i ∧ X lo hi i - k ≤ qb_Z n (X lo hi) k j at z
  have hx : X lo hi i' = max (lo i') (min (hi i') (X lo hi i)) :=
    path_succ n lo hi j i'.isLt
  change max (X lo hi i' - k) (min (X lo hi i') _) = _
  rw [hx]
  have h := bh i'
  omega

theorem needed {T n} (d : Fin T → ℕ) (lo hi c : Fin (n+1) → ℕ)
    (box : ∀ i, lo i ≤ c i ∧ c i ≤ hi i)
    (w : Fin T → Fin (n+1) → Bool)
    (col : ∀ i, ((Finset.univ : Finset (Fin T)).filter (fun t => w t i = true)).card = c i)
    (cap : ∀ t, qb_falls (w t) ≤ d t) : Bounds d lo hi := by
  intro k hk m u v uv order
  let z := qb_Z n c k
  let L (j : ℕ) := lo (idx n j) - k
  let U (j : ℕ) := hi (idx n j)
  let f : Family m := ⟨fun i => (u i).val, fun i => (v i).val,uv,order⟩
  have e : f.ends n := fun i => Nat.le_of_lt_succ (v i).isLt
  have hbox (j) (hj : j ≤ n) : L j ≤ z j ∧ z j ≤ U j := by
    let t : Fin (n+1) := ⟨j,by omega⟩
    have r := qb_Zbox n c k j t.isLt
    have s := box t
    have eq : idx n j = t := idx_at t
    change z j ≤ c t ∧ c t-k ≤ z j at r
    change lo (idx n j)-k ≤ z j ∧ z j ≤ hi (idx n j)
    rw [eq]
    omega
  have h := family_le z L U hbox m f e
  have hs : f.score L U = ∑ j, (lo (u j) - hi (v j) - k) := by
    apply Finset.sum_congr rfl
    intro i _
    change lo (idx n (u i).val) - k - hi (idx n (v i).val) = _
    rw [idx_at,idx_at]
    omega
  have fl := qb_N T n d c w col cap k
  change (∑ i : Fin n, (z i.val-z (i.val+1))) ≤ _ at fl
  rw [qb_sum_fin] at fl
  exact (hs ▸ h).trans fl

theorem enough {T n} (d : Fin T → ℕ) (lo hi : Fin (n+1) → ℕ)
    (bh : ∀ i, lo i ≤ hi i) (bounds : Bounds d lo hi) (k : ℕ) (hk : k ≤ T) :
    (∑ i : Fin n, (qb_Z n (X lo hi) k i.castSucc.val - qb_Z n (X lo hi) k i.succ.val)) ≤
      Budget d k := by
  let z := qb_Z n (X lo hi) k
  let L (j : ℕ) := lo (idx n j) - k
  let U (j : ℕ) := hi (idx n j)
  have z0 : z 0 = L 0 := by
    change qb_Z n (X lo hi) k 0 = _
    rw [qb_Z_zero]
    change path n lo hi 0 - k = _
    rw [path_zero]
    rfl
  obtain ⟨m,f,e,score⟩ := attain L U z z0 (fun j hj => shift_step lo hi k j hj bh)
    (n:=n) (fun j _ => (Nat.sub_le ..).trans (bh _))
  let u (i : Fin m) := idx n (f.u i)
  let v (i : Fin m) := idx n (f.v i)
  have bound := bounds k hk m u v (fun i => min_le_min_right _ (f.valid i))
    (fun i j h => min_le_min_right _ (f.ordered _ _ h))
  have eq : f.score L U = ∑ j, (lo (u j)-hi (v j)-k) := by
    apply Finset.sum_congr rfl
    intro i _
    change lo (u i) - k - hi (v i) = _
    omega
  change (∑ i : Fin n, (z i.val-z (i.val+1))) ≤ _
  rw [qb_sum_fin]
  exact score.trans (eq ▸ bound)

open CircuitLowerBounds MetaComplexity MetaComplexity.NestedCover
open Track
abbrev Valid (n b : ℕ) (C : Circuit) := FanInTwo C ∧ ReadsBack (n+2) C ∧
  NotBracket.notCount C ≤ b ∧ C.output < n+2+C.size
abbrev signal {n} (C : Circuit) (i : Fin (n+1)) := C.eval (RankedTapSchedule.xs n i)

def bit (w : ℕ → Bool) (j : ℕ) : ℕ := if w j = true ∧ w (j+1) = false then 1 else 0
def drops (w : ℕ → Bool) (j : ℕ) := (Finset.range j).sum (bit w)

theorem drops_eq {n} (w : Fin (n+1) → Bool) :
    qb_falls w = drops (fun j => w (idx n j)) n := by
  unfold qb_falls drops
  rw [Finset.card_filter, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  have l := idx_at i.castSucc
  have r := idx_at i.succ
  change idx n i.val = i.castSucc at l
  change idx n (i.val+1) = i.succ at r
  simp [bit,l,r]

theorem physical_falls {n b} {C : Circuit} (v : Valid n b C) :
    qb_falls (signal (n:=n) C) ≤ 2^b-1 := by
  let w := signal (n:=n) C
  let ok (i : Fin (n+1)) (s : Fin 1 → Bool) := s 0 = w i
  have fits : RankedTapSchedule.Fits 1 n b ok Finset.univ :=
    ⟨C,fun _ => C.output,v.1,v.2.1,v.2.2.1,v.2.2.2,fun _ => v.2.2.2,fun _ _ => rfl⟩
  obtain ⟨F,mono,same⟩ := (RankedTapSchedule.fits_iff _ _).mp fits
  let rank (j : ℕ) := (ofLex (F (idx n j))).1.val
  let g (j : ℕ) := w (idx n j)
  have growth (j : ℕ) : rank j + bit g j ≤ rank (j+1) := by
    have h := Prod.Lex.le_iff'.mp (mono (show idx n j ≤ idx n (j+1) from
      min_le_min_right _ (Nat.le_succ j)))
    have le : rank j ≤ rank (j+1) := h.1
    unfold bit
    split
    · rename_i fall
      have ne : rank j ≠ rank (j+1) := by
        intro eq
        have imp := Bool.le_iff_imp.mp (h.2 (Fin.ext eq) 0)
        have l : (ofLex (F (idx n j))).2 0 = g j := same _ (Finset.mem_univ _)
        have r : (ofLex (F (idx n (j+1)))).2 0 = g (j+1) := same _ (Finset.mem_univ _)
        simp [l,r,fall.1,fall.2] at imp
      omega
    · omega
  have cap : ∀ j, drops g j ≤ rank j := by
    intro j
    induction j with
    | zero => simp [drops]
    | succ j ih =>
      change (Finset.range (j+1)).sum (bit g) ≤ _
      rw [Finset.sum_range_succ]
      exact (Nat.add_le_add_right ih _).trans (growth j)
  have c := cap n
  have d : rank n < 2^b := (ofLex (F (idx n n))).1.isLt
  rw [drops_eq]
  change drops g n ≤ _
  omega

theorem cuts_eq (g : ℕ → Bool) (n : ℕ) :
    (RunIntervalBank.cuts n (fun j (_ : Fin 1) => g j)).card = drops g n := by
  unfold RunIntervalBank.cuts drops
  rw [Finset.card_filter,Finset.sum_range_succ']
  simp [bit]
  rw [Finset.card_filter]
  rfl

theorem starts_le (g : ℕ → Bool) (n : ℕ) :
    (RunIntervalBank.starts n (fun j (_ : Fin 1) => g j) 0).card +
      (if g n = false then 1 else 0) ≤ drops g n + 1 := by
  induction n with
  | zero => cases e : g 0 <;> simp [RunIntervalBank.starts,drops,Finset.filter_singleton,e]
  | succ n ih =>
    change _ ≤ (Finset.range (n+1)).sum (bit g) + 1
    rw [Finset.sum_range_succ]
    unfold RunIntervalBank.starts at *
    rw [Finset.range_add_one (n:=n+1),Finset.filter_insert]
    have hcount : ((Finset.range n).filter (fun j => g j = true ∧ g (j+1) = false)).card =
        (Finset.range n).sum (bit g) := by
      rw [Finset.card_filter]
      rfl
    cases e : g n <;> cases d : g (n+1) <;>
      simp [bit,drops,e,d,Finset.card_insert_of_notMem,Finset.mem_filter] at ih ⊢ <;> omega

theorem compileTrack {n b} (w : Fin (n+1) → Bool) (h : qb_falls w ≤ 2^b-1) :
    ∃ C : Circuit, Valid n b C ∧ (∀ i, signal C i = w i) ∧ C.size ≤ b+6*qb_falls w+2 := by
  let g (j : ℕ) := w (idx n j)
  let f (j : ℕ) (_ : Fin 1) := g j
  have cf : (RunIntervalBank.cuts n f).card = qb_falls w := (cuts_eq g n).trans (drops_eq w).symm
  have pos : 0 < 2^b := pow_pos (by decide) _
  obtain ⟨C,tap,fan,back,_,neg,size,eq⟩ := RunIntervalBank.upper n b f (by omega)
  let D : Circuit := ⟨C.gates,(tap 0).val⟩
  refine ⟨D,⟨fan,back,neg.le,(tap 0).isLt⟩,?_,?_⟩
  · intro i
    exact (eq i 0).trans (congrArg w (idx_at i))
  · have s := starts_le g n
    have d : drops g n = qb_falls w := (drops_eq w).symm
    rw [Fin.sum_univ_one] at size
    change (RunIntervalBank.starts n f 0).card + _ ≤ _ at s
    change C.size ≤ _
    omega

theorem solve : (∀ (T n : Nat) (b : Fin T → Nat) (lo hi : Fin (n+1) → Nat),
  Antitone b → (∀ i, lo i ≤ hi i ∧ hi i ≤ T) →
  let raw := fun (i : Fin (n+1)) => List.ofFn (fun j : Fin n => decide (j.val < i.val)) ++ [false,true]
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let read := fun (C : Fin T → Circ) (t : Fin T) (i : Fin (n+1)) => (C t).eval (raw i)
  let count := fun (C : Fin T → Circ) (i : Fin (n+1)) =>
    ((Finset.univ : Finset (Fin T)).filter (fun t => read C t i = true)).card
  let valid := fun (C : Fin T → Circ) => ∀ t, PEqualNP.MetaComplexity.FanInTwo (C t) ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) (C t) ∧
    PEqualNP.NotBracket.notCount (C t) ≤ b t ∧ (C t).output < n+2+(C t).size
  let x := fun (i : Fin (n+1)) => ((List.finRange (n+1)).scanl
    (fun z j => max (lo j) (min (hi j) z)) 0).getD (i.val+1) 0
  let tail := fun (k : Nat) => ((Finset.univ : Finset (Fin T)).filter
    (fun t => k ≤ t.val)).sum (fun t => 2^(b t)-1)
  let bounds := ∀ k ≤ T, ∀ (m : Nat) (u v : Fin m → Fin (n+1)),
    (∀ j, u j ≤ v j) → (∀ i j, i < j → v i ≤ u j) →
    (Finset.univ : Finset (Fin m)).sum (fun j => lo (u j) - hi (v j) - k) ≤ tail k
  ((∃ C, valid C ∧ ∀ i, lo i ≤ count C i ∧ count C i ≤ hi i) ↔ bounds) ∧
    (bounds → ∃ C, valid C ∧ (∀ i, count C i = x i) ∧ ∀ t,
      let s := ((Finset.univ : Finset (Fin n)).filter (fun i =>
        read C t i.castSucc = true ∧ read C t i.succ = false)).card
      (C t).size ≤ b t+6*s+2)) := by
  intro T n b lo hi hb hbox raw Circ read count valid x tail bounds
  let d (t : Fin T) := 2^(b t)-1
  have hd : Antitone d := fun i j h => Nat.sub_le_sub_right
    (Nat.pow_le_pow_right (by decide : 0 < 2) (hb h)) 1
  have lh (i) := (hbox i).1
  have fit (i) := xbox lo hi lh i
  have lim (i) : X lo hi i ≤ T := (fit i).2.trans (hbox i).2
  have necessary : (∃ C, valid C ∧ ∀ i, lo i ≤ count C i ∧ count C i ≤ hi i) → bounds := by
    rintro ⟨C,vc,range⟩
    exact needed d lo hi (count C) range (read C) (fun _ => rfl)
      (fun t => physical_falls (vc t))
  have construct (h : bounds) : ∃ C, valid C ∧ (∀ i, count C i = x i) ∧ ∀ t,
      (C t).size ≤ b t + 6 * Track.qb_falls (read C t) + 2 := by
    have criterion := trackCriterion T n d (X lo hi) hd lim
    obtain ⟨w,col,cap⟩ := criterion.1.mpr (fun k hk => enough d lo hi lh h k hk)
    choose C vc eq small using fun t => compileTrack (w t) (b:=b t) (cap t)
    have same (t) : read C t = w t := funext (eq t)
    refine ⟨C,vc,?_,?_⟩
    · intro i
      change ((Finset.univ : Finset (Fin T)).filter (fun t => read C t i = true)).card = _
      calc
        _ = ((Finset.univ : Finset (Fin T)).filter (fun t => w t i = true)).card := by
          apply congrArg Finset.card
          apply Finset.filter_congr
          intro t _
          rw [same t]
        _ = _ := col i
    · intro t
      rw [same]
      exact small t
  refine ⟨⟨necessary,?_⟩,construct⟩
  intro h
  obtain ⟨C,vc,eq,_⟩ := construct h
  exact ⟨C,vc,fun i => eq i ▸ fit i⟩

end PEqualNP.Outside.L_meta_53179

theorem PEqualNP.Outside.L_meta_53179 : (∀ (T n : Nat) (b : Fin T → Nat) (lo hi : Fin (n+1) → Nat),
  Antitone b → (∀ i, lo i ≤ hi i ∧ hi i ≤ T) →
  let raw := fun (i : Fin (n+1)) => List.ofFn (fun j : Fin n => decide (j.val < i.val)) ++ [false,true]
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let read := fun (C : Fin T → Circ) (t : Fin T) (i : Fin (n+1)) => (C t).eval (raw i)
  let count := fun (C : Fin T → Circ) (i : Fin (n+1)) =>
    ((Finset.univ : Finset (Fin T)).filter (fun t => read C t i = true)).card
  let valid := fun (C : Fin T → Circ) => ∀ t, PEqualNP.MetaComplexity.FanInTwo (C t) ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) (C t) ∧
    PEqualNP.NotBracket.notCount (C t) ≤ b t ∧ (C t).output < n+2+(C t).size
  let x := fun (i : Fin (n+1)) => ((List.finRange (n+1)).scanl
    (fun z j => max (lo j) (min (hi j) z)) 0).getD (i.val+1) 0
  let tail := fun (k : Nat) => ((Finset.univ : Finset (Fin T)).filter
    (fun t => k ≤ t.val)).sum (fun t => 2^(b t)-1)
  let bounds := ∀ k ≤ T, ∀ (m : Nat) (u v : Fin m → Fin (n+1)),
    (∀ j, u j ≤ v j) → (∀ i j, i < j → v i ≤ u j) →
    (Finset.univ : Finset (Fin m)).sum (fun j => lo (u j) - hi (v j) - k) ≤ tail k
  ((∃ C, valid C ∧ ∀ i, lo i ≤ count C i ∧ count C i ≤ hi i) ↔ bounds) ∧
    (bounds → ∃ C, valid C ∧ (∀ i, count C i = x i) ∧ ∀ t,
      let s := ((Finset.univ : Finset (Fin n)).filter (fun i =>
        read C t i.castSucc = true ∧ read C t i.succ = false)).card
      (C t).size ≤ b t+6*s+2)) := by
  exact PEqualNP.Outside.L_meta_53179.solve

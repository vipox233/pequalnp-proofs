import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53178

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

end PEqualNP.Outside.L_meta_53178

theorem PEqualNP.Outside.L_meta_53178 : ∀ (T n : Nat) (d : Fin T → Nat) (c : Fin (n+1) → Nat),
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
    exact PEqualNP.Outside.L_meta_53178.qb_N T n d c w hcol hfl k
  have hS : bounds → ∃ w, fits w ∧ aligned w := by
    intro hb
    have hsuf : ∀ k, ((Finset.univ : Finset (Fin T)).filter (fun t => k ≤ t.val)).sum
        (fun t => PEqualNP.Outside.L_meta_53178.qb_falls
          (PEqualNP.Outside.L_meta_53178.qb_w0 T n c t)) ≤
        ((Finset.univ : Finset (Fin T)).filter (fun t => k ≤ t.val)).sum d := by
      intro k
      by_cases hk : k ≤ T
      · exact (PEqualNP.Outside.L_meta_53178.qb_w0_falls T n c hc k hk).trans (hb k hk)
      · have : (Finset.univ : Finset (Fin T)).filter (fun t : Fin T => k ≤ t.val) = ∅ :=
          Finset.filter_false_of_mem (fun t _ => by have := t.isLt; omega)
        simp only [this, Finset.sum_empty, le_refl]
    obtain ⟨w, hal, hcol, hfl⟩ := PEqualNP.Outside.L_meta_53178.qb_B T n d c hd
      ((Finset.univ : Finset (Fin T)).sum (fun t =>
        PEqualNP.Outside.L_meta_53178.qb_falls (PEqualNP.Outside.L_meta_53178.qb_w0 T n c t) - d t))
      (PEqualNP.Outside.L_meta_53178.qb_w0 T n c) (PEqualNP.Outside.L_meta_53178.qb_w0_al T n c)
      (PEqualNP.Outside.L_meta_53178.qb_w0_col T n c hc) hsuf rfl
    exact ⟨w, ⟨hcol, hfl⟩, hal⟩
  exact ⟨⟨hN, fun hb => (hS hb).elim (fun w hw => ⟨w, hw.1⟩)⟩, hS⟩

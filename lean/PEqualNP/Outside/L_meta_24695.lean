import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24695

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (x : List Bool) : List Bool := gs.foldl stp x

def V (gs : List Gate) (x : List Bool) (i : ℕ) : Bool := (W gs x).getD i false

theorem W_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    W (gs ++ [g]) x = stp (W gs x) g := by simp [W]

theorem W_len (gs : List Gate) (x : List Bool) : (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih => rw [W_snoc, stp]; simp [ih]; omega

theorem fold_getD (H : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (H.foldl stp w).getD i false = w.getD i false := by
  induction H generalizing w with
  | nil => rfl
  | cons h H ih =>
    rw [List.foldl_cons, ih (stp w h) (by simp [stp]; omega)]
    simp [stp, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem V_prefix (G H : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + G.length) :
    V (G ++ H) x i = V G x i := by
  unfold V W
  rw [List.foldl_append]
  exact fold_getD H _ i (by rw [← W, W_len]; exact hi)

theorem V_last (G : List Gate) (g : Gate) (x : List Bool) :
    V (G ++ [g]) x (x.length + G.length) = g.op.eval (g.inputs.map (V G x)) := by
  unfold V
  rw [W_snoc, stp]
  have h := W_len G x
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
  simp [h]

theorem V_out (G : List Gate) (x : List Bool) (i : ℕ) (hi : x.length + G.length ≤ i) :
    V G x i = false := by
  unfold V
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [W_len]; exact hi)]
  rfl

theorem V_nil (x : List Bool) (i : ℕ) : V [] x i = x.getD i false := rfl

theorem oneEach_len {n m : ℕ} (u : Fin n) (v : Fin m) : (oneEach u v).length = n + m := by
  simp [oneEach]

theorem oneEach_getD {n m : ℕ} (u : Fin n) (v : Fin m) (w : ℕ) :
    (oneEach u v).getD w false = (decide (w = u.val) || decide (w = n + v.val)) := by
  have hu := u.2
  have hv := v.2
  unfold oneEach
  rw [List.getD_eq_getElem?_getD]
  by_cases h1 : w < n
  · rw [List.getElem?_append_left (by simpa using h1)]
    have : ¬ w = n + v.val := by omega
    simp [h1, this, Fin.ext_iff]
  · rw [List.getElem?_append_right (by simpa using h1)]
    have : ¬ w = u.val := by omega
    by_cases h2 : w - n < m
    · have h3 : (w = n + v.val) ↔ (w - n = v.val) := by omega
      simp [h2, this, h3, Fin.ext_iff]
    · have h3 : ¬ w = n + v.val := by omega
      simp [h2, this, h3]


def Ex (g : Gate) : Prop :=
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
    (g.op = GateOp.not ∧ g.inputs.length = 1)

def RB (N : ℕ) (G : List Gate) : Prop :=
  ∀ j g, G[j]? = some g → ∀ i ∈ g.inputs, i < N + j

def Lst (L : List Gate) (w : ℕ) : Prop := ∃ g ∈ L, w ∈ g.inputs

def I (G : List Gate) (x : List Bool) (s : ℕ ⊕ Bool) : Bool := Sum.elim (V G x) id s

theorem I_append (G H : List Gate) (x : List Bool) (s : ℕ ⊕ Bool)
    (h : ∀ i, s = Sum.inl i → i < x.length + G.length) : I (G ++ H) x s = I G x s := by
  cases s with
  | inl i => exact V_prefix G H x i (h i rfl)
  | inr b => rfl

theorem step (N' : ℕ) (G' : List Gate) (g : Gate) (hg : Ex g) (τ : ℕ → ℕ ⊕ Bool) :
    ∃ (G'' : List Gate) (r : ℕ ⊕ Bool),
      ((G'' = G' ∧ ((∃ b, r = Sum.inr b) ∨ ∃ a ∈ g.inputs, τ a = r)) ∨
        (∃ g', G'' = G' ++ [g'] ∧ Ex g' ∧ (∀ i ∈ g'.inputs, ∃ a ∈ g.inputs, τ a = Sum.inl i) ∧
          r = Sum.inl (N' + G'.length))) ∧
      ((∃ a ∈ g.inputs, τ a = Sum.inr false) → G'' = G') ∧
      (∀ x : List Bool, x.length = N' →
        I G'' x r = g.op.eval (g.inputs.map fun a => I G' x (τ a))) := by
  obtain ⟨op, ins⟩ := g
  rcases hg with ⟨hop, hlen⟩ | ⟨hop, hlen⟩
  · simp only at hop hlen
    obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hlen
    rcases ha : τ a with i | ba <;> rcases hb : τ b with j | bb
    · refine ⟨G' ++ [⟨op, [i, j]⟩], Sum.inl (N' + G'.length), Or.inr ⟨_, rfl, ?_, ?_, rfl⟩, ?_, ?_⟩
      · exact Or.inl ⟨hop, rfl⟩
      · intro i' hi'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi'
        rcases hi' with rfl | rfl
        · exact ⟨a, by simp, ha⟩
        · exact ⟨b, by simp, hb⟩
      · rintro ⟨a', ha', h⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha'
        rcases ha' with rfl | rfl <;> simp_all
      · intro x hx
        have := V_last G' ⟨op, [i, j]⟩ x
        rw [hx] at this
        simp [I, this, ha, hb]
    · rcases hop with rfl | rfl <;> cases bb
      · exact ⟨G', Sum.inr false, Or.inl ⟨rfl, Or.inl ⟨_, rfl⟩⟩, fun _ => rfl,
          fun x _ => by simp [I, ha, hb, GateOp.eval]⟩
      · exact ⟨G', Sum.inl i, Or.inl ⟨rfl, Or.inr ⟨a, by simp, ha⟩⟩, fun _ => rfl,
          fun x _ => by simp [I, ha, hb, GateOp.eval]⟩
      · exact ⟨G', Sum.inl i, Or.inl ⟨rfl, Or.inr ⟨a, by simp, ha⟩⟩, fun _ => rfl,
          fun x _ => by simp [I, ha, hb, GateOp.eval]⟩
      · exact ⟨G', Sum.inr true, Or.inl ⟨rfl, Or.inl ⟨_, rfl⟩⟩, fun _ => rfl,
          fun x _ => by simp [I, ha, hb, GateOp.eval]⟩
    · rcases hop with rfl | rfl <;> cases ba
      · exact ⟨G', Sum.inr false, Or.inl ⟨rfl, Or.inl ⟨_, rfl⟩⟩, fun _ => rfl,
          fun x _ => by simp [I, ha, hb, GateOp.eval]⟩
      · exact ⟨G', Sum.inl j, Or.inl ⟨rfl, Or.inr ⟨b, by simp, hb⟩⟩, fun _ => rfl,
          fun x _ => by simp [I, ha, hb, GateOp.eval]⟩
      · exact ⟨G', Sum.inl j, Or.inl ⟨rfl, Or.inr ⟨b, by simp, hb⟩⟩, fun _ => rfl,
          fun x _ => by simp [I, ha, hb, GateOp.eval]⟩
      · exact ⟨G', Sum.inr true, Or.inl ⟨rfl, Or.inl ⟨_, rfl⟩⟩, fun _ => rfl,
          fun x _ => by simp [I, ha, hb, GateOp.eval]⟩
    · rcases hop with rfl | rfl
      · exact ⟨G', Sum.inr (ba && bb), Or.inl ⟨rfl, Or.inl ⟨_, rfl⟩⟩, fun _ => rfl,
          fun x _ => by simp [I, ha, hb, GateOp.eval]⟩
      · exact ⟨G', Sum.inr (ba || bb), Or.inl ⟨rfl, Or.inl ⟨_, rfl⟩⟩, fun _ => rfl,
          fun x _ => by simp [I, ha, hb, GateOp.eval]⟩
  · simp only at hop hlen
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hlen
    subst hop
    rcases ha : τ a with i | ba
    · refine ⟨G' ++ [⟨GateOp.not, [i]⟩], Sum.inl (N' + G'.length), Or.inr ⟨_, rfl, ?_, ?_, rfl⟩, ?_, ?_⟩
      · exact Or.inr ⟨rfl, rfl⟩
      · intro i' hi'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi'
        subst hi'
        exact ⟨a, by simp, ha⟩
      · rintro ⟨a', ha', h⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha'
        subst ha'
        simp_all
      · intro x hx
        have := V_last G' ⟨GateOp.not, [i]⟩ x
        rw [hx] at this
        simp [I, this, ha]
    · exact ⟨G', Sum.inr (!ba), Or.inl ⟨rfl, Or.inl ⟨_, rfl⟩⟩, fun _ => rfl,
        fun x _ => by simp [I, ha, GateOp.eval]⟩

def up (n k i : ℕ) : ℕ := if i < n + k then i else i + 1

def phi0 (n k w : ℕ) : ℕ ⊕ Bool :=
  if w < n + k then Sum.inl w else if w = n + k then Sum.inr false else Sum.inl (w - 1)

theorem phi0_inl (n m k w i : ℕ) (hk : k ≤ m) (hw : w < n + (m + 1))
    (h : phi0 n k w = Sum.inl i) : w = up n k i ∧ i < n + m := by
  unfold phi0 at h
  unfold up
  split_ifs at h with h1 h2
  · have hi : w = i := by simpa using h
    subst hi
    rw [if_pos h1]
    exact ⟨rfl, by omega⟩
  · have hi : w - 1 = i := by simpa using h
    subst hi
    have h3 : ¬ (w - 1 < n + k) := by omega
    rw [if_neg h3]
    exact ⟨by omega, by omega⟩

theorem base_sem {n m : ℕ} (k : Fin (m + 1)) (u : Fin n) (v : Fin m) (w : ℕ)
    (hw : w < n + (m + 1)) :
    (oneEach u (k.succAbove v)).getD w false = I [] (oneEach u v) (phi0 n k.val w) := by
  have hu := u.2
  have hv := v.2
  have hk := k.2
  have hs : (k.succAbove v).val = if v.val < k.val then v.val else v.val + 1 := by
    simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc]
    split_ifs <;> simp
  rw [oneEach_getD]
  unfold phi0
  split_ifs with h1 h2
  · simp only [I, Sum.elim_inl, V_nil, oneEach_getD]
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    rw [hs]
    split_ifs <;> omega
  · simp only [I, Sum.elim_inr, id]
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    rw [hs]
    split_ifs <;> simp <;> omega
  · simp only [I, Sum.elim_inl, V_nil, oneEach_getD]
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    rw [hs]
    split_ifs <;> omega

theorem fold (n m : ℕ) (k : Fin (m + 1)) (L : List Gate) (hL : ∀ g ∈ L, Ex g) :
    ∃ (G' : List Gate) (φ : ℕ → ℕ ⊕ Bool),
      (∀ g ∈ G', Ex g) ∧ RB (n + m) G' ∧ G'.length ≤ L.length ∧
      (Lst L (n + k.val) → G'.length + 1 ≤ L.length) ∧
      (∀ w < n + (m + 1) + L.length, ∀ i, φ w = Sum.inl i → i < n + m + G'.length) ∧
      (∀ (u : Fin n) (v : Fin m), ∀ w < n + (m + 1) + L.length,
        V L (oneEach u (k.succAbove v)) w = I G' (oneEach u v) (φ w)) ∧
      (∀ w < n + (m + 1), φ w = phi0 n k.val w) ∧
      (∀ g' ∈ G', ∀ i ∈ g'.inputs, i < n + m → Lst L (up n k.val i)) ∧
      (∀ w, n + (m + 1) ≤ w → w < n + (m + 1) + L.length → ∀ i, φ w = Sum.inl i →
        i < n + m → Lst L (up n k.val i)) := by
  have hk := k.2
  induction L using List.reverseRecOn with
  | nil =>
    refine ⟨[], phi0 n k.val, by simp, ?_, le_refl _, ?_, ?_, ?_, fun _ _ => rfl, by simp, ?_⟩
    · intro j g h
      simp at h
    · rintro ⟨g, hg, _⟩
      simp at hg
    · intro w hw i h
      have := (phi0_inl n m k.val w i (by omega) (by simpa using hw) h).2
      simpa using this
    · intro u v w hw
      rw [V_nil]
      exact base_sem k u v w (by simpa using hw)
    · intro w h1 h2
      simp at h2
      omega
  | append_singleton L g ih =>
    have hL' : ∀ g ∈ L, Ex g := fun g0 hg0 => hL g0 (by simp [hg0])
    have hgE : Ex g := hL g (by simp)
    obtain ⟨G', φ, hA, hB, hC1, hC2, hD, hE, hF0, hF1, hF2⟩ := ih hL'
    have hτ : ∀ a i, (if a < n + (m + 1) + L.length then φ a else Sum.inr false) = Sum.inl i →
        a < n + (m + 1) + L.length ∧ φ a = Sum.inl i := by
      intro a i h
      split_ifs at h with h1
      exact ⟨h1, h⟩
    obtain ⟨G'', r, hS1, hS2, hS3⟩ := step (n + m) G' g hgE
      (fun a => if a < n + (m + 1) + L.length then φ a else Sum.inr false)
    have hop : ∀ a ∈ g.inputs, ∀ i,
        (if a < n + (m + 1) + L.length then φ a else Sum.inr false) = Sum.inl i →
        i < n + m → Lst (L ++ [g]) (up n k.val i) := by
      intro a ha i h hi
      obtain ⟨h1, h2⟩ := hτ a i h
      by_cases h3 : a < n + (m + 1)
      · rw [hF0 a h3] at h2
        have := (phi0_inl n m k.val a i (by omega) h3 h2).1
        exact ⟨g, by simp, this ▸ ha⟩
      · obtain ⟨g0, hg0, hin⟩ := hF2 a (by omega) h1 i h2 hi
        exact ⟨g0, by simp [hg0], hin⟩
    have hmono : ∀ w, Lst L w → Lst (L ++ [g]) w :=
      fun w ⟨g0, hg0, hin⟩ => ⟨g0, by simp [hg0], hin⟩
    have hrb : ∀ i, r = Sum.inl i → i < n + m + G''.length := by
      intro i hi
      rcases hS1 with ⟨rfl, h | ⟨a, ha, h⟩⟩ | ⟨g', rfl, _, _, h⟩
      · obtain ⟨b, hb⟩ := h
        rw [hb] at hi
        cases hi
      · rw [← h] at hi
        obtain ⟨h1, h2⟩ := hτ a i hi
        exact hD a h1 i h2
      · rw [h] at hi
        cases hi
        simp
    refine ⟨G'', Function.update φ (n + (m + 1) + L.length) r, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rcases hS1 with ⟨rfl, _⟩ | ⟨g', rfl, hg', _⟩
      · exact hA
      · intro g0 hg0
        simp only [List.mem_append, List.mem_singleton] at hg0
        rcases hg0 with h | rfl
        · exact hA _ h
        · exact hg'
    · rcases hS1 with ⟨rfl, _⟩ | ⟨g', rfl, hg', hin, _⟩
      · exact hB
      · intro j g0 hj i hi
        rw [List.getElem?_append] at hj
        split_ifs at hj with hj'
        · exact hB j g0 hj i hi
        · rw [List.getElem?_singleton] at hj
          split_ifs at hj with hj2
          cases hj
          obtain ⟨a, ha, h⟩ := hin i hi
          obtain ⟨h1, h2⟩ := hτ a i h
          have := hD a h1 i h2
          omega
    · rcases hS1 with ⟨rfl, _⟩ | ⟨g', rfl, _⟩ <;> simp <;> omega
    · rintro ⟨g0, hg0, hin⟩
      simp only [List.mem_append, List.mem_singleton] at hg0
      rcases hg0 with h | rfl
      · have := hC2 ⟨g0, h, hin⟩
        rcases hS1 with ⟨rfl, _⟩ | ⟨g', rfl, _⟩ <;> simp <;> omega
      · have hG : G'' = G' := by
          apply hS2
          refine ⟨n + k.val, hin, ?_⟩
          rw [if_pos (by omega), hF0 _ (by omega)]
          simp [phi0]
        subst hG
        simp
        omega
    · intro w hw i hi
      simp only [List.length_append, List.length_singleton] at hw
      by_cases hw' : w = n + (m + 1) + L.length
      · subst hw'
        rw [Function.update_self] at hi
        exact hrb i hi
      · rw [Function.update_of_ne hw'] at hi
        have := hD w (by omega) i hi
        rcases hS1 with ⟨rfl, _⟩ | ⟨g', rfl, _⟩
        · exact this
        · simp
          omega
    · intro u v w hw
      simp only [List.length_append, List.length_singleton] at hw
      have hx : (oneEach u (k.succAbove v)).length = n + (m + 1) := oneEach_len _ _
      by_cases hw' : w = n + (m + 1) + L.length
      · subst hw'
        rw [Function.update_self]
        have h1 := V_last L g (oneEach u (k.succAbove v))
        rw [hx] at h1
        rw [h1, hS3 (oneEach u v) (oneEach_len u v)]
        congr 1
        apply List.map_congr_left
        intro a ha
        split_ifs with h2
        · exact hE u v a h2
        · rw [V_out L _ a (by rw [hx]; omega)]
          rfl
      · rw [Function.update_of_ne hw']
        have hw2 : w < n + (m + 1) + L.length := by omega
        rw [V_prefix L [g] _ w (by rw [hx]; exact hw2), hE u v w hw2]
        rcases hS1 with ⟨rfl, _⟩ | ⟨g', rfl, _⟩
        · rfl
        · exact (I_append G' [g'] _ _
            (fun i hi => by rw [oneEach_len]; exact hD w hw2 i hi)).symm
    · intro w hw
      rw [Function.update_of_ne (by omega)]
      exact hF0 w hw
    · intro g0 hg0 i hi hlt
      rcases hS1 with ⟨rfl, _⟩ | ⟨g', rfl, _, hin, _⟩
      · exact hmono _ (hF1 g0 hg0 i hi hlt)
      · simp only [List.mem_append, List.mem_singleton] at hg0
        rcases hg0 with h | rfl
        · exact hmono _ (hF1 g0 h i hi hlt)
        · obtain ⟨a, ha, h⟩ := hin i hi
          exact hop a ha i h hlt
    · intro w hw1 hw2 i hi hlt
      simp only [List.length_append, List.length_singleton] at hw2
      by_cases hw' : w = n + (m + 1) + L.length
      · subst hw'
        rw [Function.update_self] at hi
        rcases hS1 with ⟨_, h | ⟨a, ha, h⟩⟩ | ⟨g', _, _, _, h⟩
        · obtain ⟨b, hb⟩ := h
          rw [hb] at hi
          cases hi
        · rw [← h] at hi
          exact hop a ha i hi hlt
        · rw [h] at hi
          cases hi
          omega
      · rw [Function.update_of_ne hw'] at hi
        exact hmono _ (hF2 w hw1 (by omega) i hi hlt)

def shg (p : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (fun i => if i < p then i else i - 1)⟩

theorem Ex_shg (p : ℕ) (g : Gate) (h : Ex g) : Ex (shg p g) := by
  unfold Ex at h ⊢
  simpa [shg] using h

theorem erase_getD (l : List Bool) (p i : ℕ) (hne : i ≠ p) :
    (l.eraseIdx p).getD (if i < p then i else i - 1) false = l.getD i false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eraseIdx]
  by_cases h1 : i < p
  · simp [h1]
  · have h2 : ¬ (i - 1 < p) := by omega
    have h3 : i - 1 + 1 = i := by omega
    simp [h1, h2, h3]

theorem del_sem (P : List Gate) (g : Gate) (x : List Bool) (S : List Gate)
    (hS : ∀ h ∈ S, x.length + P.length ∉ h.inputs) :
    W (P ++ S.map (shg (x.length + P.length))) x =
      (W (P ++ g :: S) x).eraseIdx (x.length + P.length) := by
  induction S using List.reverseRecOn with
  | nil =>
    have h1 : P ++ [g] = P ++ [g] := rfl
    simp only [List.map_nil, List.append_nil]
    rw [W_snoc, stp, List.eraseIdx_append_of_length_le (by rw [W_len])]
    simp [W_len]
  | append_singleton S h ih =>
    have hS' : ∀ h0 ∈ S, x.length + P.length ∉ h0.inputs := fun h0 hh => hS h0 (by simp [hh])
    have hh : x.length + P.length ∉ h.inputs := hS h (by simp)
    have e1 : P ++ (S ++ [h]).map (shg (x.length + P.length)) =
        (P ++ S.map (shg (x.length + P.length))) ++ [shg (x.length + P.length) h] := by simp
    have e2 : P ++ g :: (S ++ [h]) = (P ++ g :: S) ++ [h] := by simp
    rw [e1, e2, W_snoc, W_snoc, ih hS', stp, stp]
    rw [List.eraseIdx_append_of_lt_length (by rw [W_len]; simp)]
    congr 2
    simp only [shg, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i hi
    exact erase_getD _ _ i (fun hEq => hh (hEq ▸ hi))

theorem prune (N : ℕ) : ∀ (t : ℕ) (G : List Gate), G.length = t → G ≠ [] → (∀ g ∈ G, Ex g) →
    RB N G →
    ∃ G2 : List Gate, G2 ≠ [] ∧ (∀ g ∈ G2, Ex g) ∧ RB N G2 ∧ G2.length ≤ G.length ∧
      (∀ j, j + 1 < G2.length → Lst G2 (N + j)) ∧
      (∀ x : List Bool, x.length = N → V G2 x (N + G2.length - 1) = V G x (N + G.length - 1)) ∧
      (∀ i < N, Lst G2 i → Lst G i) := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro G ht hne hEx hRB
    by_cases hall : ∀ j, j + 1 < G.length → Lst G (N + j)
    · exact ⟨G, hne, hEx, hRB, le_refl _, hall, fun _ _ => rfl, fun _ _ h => h⟩
    · obtain ⟨j, hj, hnl⟩ : ∃ j, j + 1 < G.length ∧ ¬ Lst G (N + j) := by
        by_contra hcon
        apply hall
        intro j hj
        by_contra hl
        exact hcon ⟨j, hj, hl⟩
      have hjl : j < G.length := by omega
      have hsplit : G.take j ++ G[j] :: G.drop (j + 1) = G := by
        rw [List.getElem_cons_drop, List.take_append_drop]
      have hPl : (G.take j).length = j := by
        rw [List.length_take]
        omega
      have hSl : (G.drop (j + 1)).length = G.length - (j + 1) := List.length_drop
      have hnot : ∀ h0 ∈ G, N + j ∉ h0.inputs := fun h0 hh hin => hnl ⟨h0, hh, hin⟩
      have hGsl : (G.take j ++ (G.drop (j + 1)).map (shg (N + j))).length = G.length - 1 := by
        rw [List.length_append, List.length_map, hPl, hSl]
        omega
      have hmem : ∀ g0 ∈ G.take j ++ (G.drop (j + 1)).map (shg (N + j)),
          g0 ∈ G ∨ ∃ h0 ∈ G, g0 = shg (N + j) h0 := by
        intro g0 hg0
        rw [List.mem_append, List.mem_map] at hg0
        rcases hg0 with h | ⟨h0, hh, rfl⟩
        · exact Or.inl (List.mem_of_mem_take h)
        · exact Or.inr ⟨h0, List.mem_of_mem_drop hh, rfl⟩
      obtain ⟨G2, hne2, hEx2, hRB2, hlen2, hread2, hV2, hus2⟩ :=
        ih (G.length - 1) (by omega) (G.take j ++ (G.drop (j + 1)).map (shg (N + j))) hGsl
          (by
            intro h0
            have := congrArg List.length h0
            rw [hGsl] at this
            simp at this
            omega)
          (by
            intro g0 hg0
            rcases hmem g0 hg0 with h | ⟨h0, hh, rfl⟩
            · exact hEx g0 h
            · exact Ex_shg _ _ (hEx h0 hh))
          (by
            intro t' g0 hg0 i hi
            rw [List.getElem?_append] at hg0
            split_ifs at hg0 with h1
            · rw [List.getElem?_take] at hg0
              split_ifs at hg0 with h2
              exact hRB t' g0 hg0 i hi
            · rw [hPl] at hg0 h1
              rw [List.getElem?_map, List.getElem?_drop] at hg0
              obtain ⟨h0, hh0, rfl⟩ := Option.map_eq_some_iff.mp hg0
              simp only [shg, List.mem_map] at hi
              obtain ⟨i0, hi0, rfl⟩ := hi
              have hb := hRB _ h0 hh0 i0 hi0
              have hne0 : i0 ≠ N + j := fun hEq => hnot h0 (List.mem_of_getElem? hh0) (hEq ▸ hi0)
              split_ifs <;> omega)
      refine ⟨G2, hne2, hEx2, hRB2, by omega, hread2, ?_, ?_⟩
      · intro x hx
        rw [hV2 x hx, hGsl]
        unfold V
        have hd := del_sem (G.take j) G[j] x (G.drop (j + 1))
          (by
            intro h0 hh
            rw [hx, hPl]
            exact hnot h0 (List.mem_of_mem_drop hh))
        rw [hx, hPl, hsplit] at hd
        rw [hd]
        have he := erase_getD (W G x) (N + j) (N + G.length - 1) (by omega)
        rw [if_neg (by omega)] at he
        have e3 : N + G.length - 1 - 1 = N + (G.length - 1) - 1 := by omega
        rw [← e3]
        exact he
      · intro i hi hl
        obtain ⟨g0, hg0, hin⟩ := hus2 i hi hl
        rcases hmem g0 hg0 with h | ⟨h0, hh, rfl⟩
        · exact ⟨g0, h, hin⟩
        · simp only [shg, List.mem_map] at hin
          obtain ⟨i0, hi0, hEq⟩ := hin
          have hne0 : i0 ≠ N + j := fun hEq' => hnot h0 hh (hEq' ▸ hi0)
          refine ⟨h0, hh, ?_⟩
          split_ifs at hEq with h3
          · exact hEq ▸ hi0
          · omega

theorem Ex_fan (g : Gate) (h : Ex g) :
    g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  rcases h with ⟨h1 | h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]

theorem gateAt_eq (C : Circuit) (t : ℕ) (ht : t < C.gates.length) :
    NestedCover.gateAt C t = C.gates[t] := by
  unfold NestedCover.gateAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]
  rfl

theorem readsIn_zero (C : Circuit) (w : ℕ) :
    NestedCover.readsIn C (Finset.range C.size) w = 0 ↔ ¬ Lst C.gates w := by
  unfold NestedCover.readsIn
  rw [Finset.sum_eq_zero_iff]
  constructor
  · rintro h ⟨g, hg, hw⟩
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hg
    have := h t (Finset.mem_range.mpr ht)
    rw [gateAt_eq C t ht, List.count_eq_zero] at this
    exact this hw
  · intro h t ht
    have ht' : t < C.gates.length := Finset.mem_range.mp ht
    rw [gateAt_eq C t ht', List.count_eq_zero]
    intro hw
    exact h ⟨C.gates[t], List.getElem_mem ht', hw⟩

theorem up_row (n k u : ℕ) (h : u < n) : up n k u = u := by
  unfold up
  rw [if_pos (by omega)]

theorem up_col {n m : ℕ} (k : Fin (m + 1)) (v : Fin m) :
    up n k.val (n + v.val) = n + (k.succAbove v).val := by
  have hs : (k.succAbove v).val = if v.val < k.val then v.val else v.val + 1 := by
    simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc]
    split_ifs <;> simp
  unfold up
  rw [hs]
  split_ifs <;> omega

theorem main : ∀ (n m : ℕ) (A : Fin n → Fin (m + 1) → Bool) (k : Fin (m + 1)) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents A C → ((∀ g ∈ C.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + (m + 1)) C ∧ 0 < C.size ∧ C.output + 1 = (n + (m + 1)) + C.size ∧ (∀ j < C.size, (PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) ((n + (m + 1)) + j) = 0 ↔ j + 1 = C.size)) ∨ (C.size = 0 ∧ C.output < (n + (m + 1)))) → (∃ g ∈ C.gates, n + k.val ∈ g.inputs) → (∃ (u u2 : Fin n) (v v2 : Fin m), A u (k.succAbove v) ≠ A u2 (k.succAbove v2)) → ∃ C2 : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C2 ∧ PEqualNP.Represents.Represents (fun (u : Fin n) (v : Fin m) => A u (k.succAbove v)) C2 ∧ ((∀ g ∈ C2.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C2 ∧ 0 < C2.size ∧ C2.output + 1 = (n + m) + C2.size ∧ (∀ j < C2.size, (PEqualNP.MetaComplexity.NestedCover.readsIn C2 (Finset.range C2.size) ((n + m) + j) = 0 ↔ j + 1 = C2.size)) ∨ (C2.size = 0 ∧ C2.output < (n + m))) ∧ C2.size + 1 ≤ C.size ∧ (∀ u : Fin n, ((∃ g ∈ C2.gates, u.val ∈ g.inputs) ∨ C2.output = u.val) → ((∃ g ∈ C.gates, u.val ∈ g.inputs) ∨ C.output = u.val)) ∧ (∀ v : Fin m, ((∃ g ∈ C2.gates, (n + v.val) ∈ g.inputs) ∨ C2.output = (n + v.val)) → ((∃ g ∈ C.gates, (n + (k.succAbove v).val) ∈ g.inputs) ∨ C.output = (n + (k.succAbove v).val))) := by
  intro n m A k C hF hR hRed hlist hnc
  rcases hRed with ⟨hEx, hRBC, hpos, hout, hread⟩ | ⟨h0, _⟩
  swap
  · exfalso
    obtain ⟨g, hg, _⟩ := hlist
    have h0' : C.gates.length = 0 := h0
    rw [List.eq_nil_of_length_eq_zero h0'] at hg
    simp at hg
  have hpos' : 0 < C.gates.length := hpos
  have hout' : C.output + 1 = n + (m + 1) + C.gates.length := hout
  have hR' : ∀ (u : Fin n) (v : Fin (m + 1)), C.eval (oneEach u v) = A u v := hR
  obtain ⟨G', φ, hA, hB, hC1, hC2, hD, hE, hF0, hF1, hF2⟩ := fold n m k C.gates hEx
  have hstrict : G'.length + 1 ≤ C.gates.length := hC2 hlist
  have hsem : ∀ (u : Fin n) (v : Fin m),
      A u (k.succAbove v) = I G' (oneEach u v) (φ C.output) := by
    intro u v
    rw [← hR' u (k.succAbove v)]
    exact hE u v C.output (by omega)
  rcases hφ : φ C.output with i | b
  · by_cases hi : i < n + m
    · refine ⟨⟨[], i⟩, ?_, ?_, Or.inr ⟨rfl, hi⟩, ?_, ?_, ?_⟩
      · intro g hg
        simp at hg
      · intro u v
        have h1 := V_prefix [] G' (oneEach u v) i (by rw [oneEach_len]; simpa using hi)
        rw [List.nil_append] at h1
        show (oneEach u v).getD i false = A u (k.succAbove v)
        rw [hsem u v, hφ]
        exact h1.symm
      · show 0 + 1 ≤ C.gates.length
        omega
      · intro u hu
        rcases hu with ⟨g, hg, _⟩ | hu
        · simp at hg
        · have hu' : i = u.val := hu
          subst hu'
          have := hF2 C.output (by omega) (by omega) u.val hφ hi
          rw [up_row n k.val u.val u.2] at this
          exact Or.inl this
      · intro v hv
        rcases hv with ⟨g, hg, _⟩ | hv
        · simp at hg
        · have hv' : i = n + v.val := hv
          subst hv'
          have := hF2 C.output (by omega) (by omega) (n + v.val) hφ hi
          rw [up_col k v] at this
          exact Or.inl this
    · have hib := hD C.output (by omega) i hφ
      have htl : (G'.take (i - (n + m) + 1)).length = i - (n + m) + 1 := by
        rw [List.length_take]
        omega
      obtain ⟨G2, hne2, hEx2, hRB2, hlen2, hread2, hV2, hus2⟩ :=
        prune (n + m) _ (G'.take (i - (n + m) + 1)) rfl
          (by
            intro h0
            have := congrArg List.length h0
            rw [htl] at this
            simp at this)
          (fun g hg => hA g (List.mem_of_mem_take hg))
          (by
            intro j g hj a ha
            rw [List.getElem?_take] at hj
            split_ifs at hj with h2
            exact hB j g hj a ha)
      rw [htl] at hlen2
      have hG2pos : 0 < G2.length := List.length_pos_of_ne_nil hne2
      refine ⟨⟨G2, n + m + G2.length - 1⟩, ?_, ?_, Or.inl ⟨hEx2, ?_, hG2pos, ?_, ?_⟩, ?_, ?_, ?_⟩
      · exact fun g hg => Ex_fan g (hEx2 g hg)
      · intro u v
        show V G2 (oneEach u v) (n + m + G2.length - 1) = A u (k.succAbove v)
        rw [hV2 _ (oneEach_len u v), htl, hsem u v, hφ]
        have h1 := V_prefix (G'.take (i - (n + m) + 1)) (G'.drop (i - (n + m) + 1))
          (oneEach u v) i (by rw [oneEach_len, htl]; omega)
        rw [List.take_append_drop] at h1
        have e : n + m + (i - (n + m) + 1) - 1 = i := by omega
        rw [e]
        exact h1.symm
      · intro j hj a ha
        have hj' : j < G2.length := hj
        rw [gateAt_eq _ j hj'] at ha
        exact hRB2 j _ (List.getElem?_eq_getElem hj') a ha
      · show n + m + G2.length - 1 + 1 = n + m + G2.length
        omega
      · intro j hj
        have hj' : j < G2.length := hj
        rw [readsIn_zero]
        constructor
        · intro h0
          by_contra hne
          have hne' : ¬ j + 1 = G2.length := hne
          exact h0 (hread2 j (by omega))
        · intro hj1
          have hj1' : j + 1 = G2.length := hj1
          rintro ⟨g, hg, hw⟩
          obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hg
          have ht' : t < G2.length := ht
          have := hRB2 t _ (List.getElem?_eq_getElem ht') _ hw
          omega
      · show G2.length + 1 ≤ C.gates.length
        omega
      · intro u hu
        have hu2 := u.2
        rcases hu with hu | hu
        · obtain ⟨g0, hg0, hin⟩ := hus2 u.val (by omega) hu
          have := hF1 g0 (List.mem_of_mem_take hg0) u.val hin (by omega)
          rw [up_row n k.val u.val u.2] at this
          exact Or.inl this
        · exfalso
          have hu' : n + m + G2.length - 1 = u.val := hu
          omega
      · intro v hv
        have hv2 := v.2
        rcases hv with hv | hv
        · obtain ⟨g0, hg0, hin⟩ := hus2 (n + v.val) (by omega) hv
          have := hF1 g0 (List.mem_of_mem_take hg0) (n + v.val) hin (by omega)
          rw [up_col k v] at this
          exact Or.inl this
        · exfalso
          have hv' : n + m + G2.length - 1 = n + v.val := hv
          omega
  · exfalso
    obtain ⟨u, u2, v, v2, hne⟩ := hnc
    apply hne
    rw [hsem u v, hsem u2 v2, hφ]
    rfl

end PEqualNP.Outside.L_meta_24695

theorem PEqualNP.Outside.L_meta_24695 : (∀ (n m : ℕ) (A : Fin n → Fin (m + 1) → Bool) (k : Fin (m + 1)) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents A C → ((∀ g ∈ C.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + (m + 1)) C ∧ 0 < C.size ∧ C.output + 1 = (n + (m + 1)) + C.size ∧ (∀ j < C.size, (PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) ((n + (m + 1)) + j) = 0 ↔ j + 1 = C.size)) ∨ (C.size = 0 ∧ C.output < (n + (m + 1)))) → (∃ g ∈ C.gates, n + k.val ∈ g.inputs) → (∃ (u u2 : Fin n) (v v2 : Fin m), A u (k.succAbove v) ≠ A u2 (k.succAbove v2)) → ∃ C2 : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C2 ∧ PEqualNP.Represents.Represents (fun (u : Fin n) (v : Fin m) => A u (k.succAbove v)) C2 ∧ ((∀ g ∈ C2.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C2 ∧ 0 < C2.size ∧ C2.output + 1 = (n + m) + C2.size ∧ (∀ j < C2.size, (PEqualNP.MetaComplexity.NestedCover.readsIn C2 (Finset.range C2.size) ((n + m) + j) = 0 ↔ j + 1 = C2.size)) ∨ (C2.size = 0 ∧ C2.output < (n + m))) ∧ C2.size + 1 ≤ C.size ∧ (∀ u : Fin n, ((∃ g ∈ C2.gates, u.val ∈ g.inputs) ∨ C2.output = u.val) → ((∃ g ∈ C.gates, u.val ∈ g.inputs) ∨ C.output = u.val)) ∧ (∀ v : Fin m, ((∃ g ∈ C2.gates, (n + v.val) ∈ g.inputs) ∨ C2.output = (n + v.val)) → ((∃ g ∈ C.gates, (n + (k.succAbove v).val) ∈ g.inputs) ∨ C.output = (n + (k.succAbove v).val)))) :=
  PEqualNP.Outside.L_meta_24695.main

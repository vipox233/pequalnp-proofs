import Mathlib
import PEqualNP.Defs

-- Proof of L-meta-29745 (two-round marking patterns): max-plus walk scores over the
-- product automaton (state, phase) are eventually exactly periodic (cycle removal, best-ratio
-- cycle pumping, monotone bounded potential); the joining bound then gives the uniform error.

namespace PEqualNP.Outside.L_meta_29745_aux

open Finset

variable {V : Type}

def Wk (E : V → V → ℕ → Prop) (u : V) (n : ℕ) (pos : ℕ → V) (rw : ℕ → ℕ) : Prop :=
  pos 0 = u ∧ ∀ i < n, E (pos i) (pos (i+1)) (rw i)

lemma Wk.pre {E : V → V → ℕ → Prop} {u n pos rw} (h : Wk E u n pos rw) {m : ℕ} (hm : m ≤ n) :
    Wk E u m pos rw :=
  ⟨h.1, fun i hi => h.2 i (by omega)⟩

lemma sum_le10 (rw : ℕ → ℕ) (n : ℕ) (h : ∀ i < n, rw i ≤ 10) : ∑ i ∈ range n, rw i ≤ 10 * n := by
  have := Finset.sum_le_card_nsmul (range n) rw 10 (fun i hi => h i (Finset.mem_range.1 hi))
  simpa [mul_comm] using this

lemma Wk.remove {E : V → V → ℕ → Prop} {u n pos rw} (h : Wk E u n pos rw) {i j : ℕ}
    (hij : i < j) (hjn : j ≤ n) (heq : pos i = pos j) :
    ∃ pos' rw', Wk E u (n - (j - i)) pos' rw' ∧ pos' (n - (j - i)) = pos n ∧
      (∑ k ∈ range n, rw k) = (∑ k ∈ range (n - (j - i)), rw' k) + ∑ k ∈ range (j - i), rw (i + k) ∧
      (∀ k ≤ n - (j - i), ∃ k' ≤ n, pos' k = pos k') ∧
      (∀ k < n - (j - i), ∃ k' < n, rw' k = rw k') := by
  set l := j - i with hl
  refine ⟨fun k => if k ≤ i then pos k else pos (k + l),
    fun k => if k < i then rw k else rw (k + l), ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · simp [h.1]
  · intro k hk
    by_cases h1 : k < i
    · have h2 : k ≤ i := by omega
      have h3 : k + 1 ≤ i := by omega
      simp only [h1, h2, h3, ite_true]
      exact h.2 k (by omega)
    · by_cases h2 : k = i
      · subst h2
        simp only [le_refl, ite_true, lt_irrefl, ite_false, show ¬ (k + 1 ≤ k) by omega]
        rw [heq, show k + 1 + l = j + 1 by omega, show k + l = j by omega]
        exact h.2 j (by omega)
      · have h3 : ¬ k ≤ i := by omega
        have h4 : ¬ k + 1 ≤ i := by omega
        simp only [h1, h3, h4, ite_false]
        rw [show k + 1 + l = k + l + 1 by omega]
        exact h.2 (k + l) (by omega)
  · by_cases h1 : n - l ≤ i
    · simp only [h1, ite_true]
      rw [show n - l = i by omega, heq, show j = n by omega]
    · simp only [h1, ite_false]
      rw [show n - l + l = n by omega]
  · have e1 : n = i + l + (n - j) := by omega
    have e2 : n - l = i + (n - j) := by omega
    rw [e2]
    conv_lhs => rw [e1]
    rw [sum_range_add, sum_range_add, sum_range_add]
    have s1 : ∑ x ∈ range i, (if x < i then rw x else rw (x + l)) = ∑ x ∈ range i, rw x :=
      sum_congr rfl (fun x hx => by simp [Finset.mem_range.1 hx])
    have s2 : ∑ x ∈ range (n - j), (if i + x < i then rw (i + x) else rw (i + x + l)) =
        ∑ x ∈ range (n - j), rw (i + l + x) :=
      sum_congr rfl (fun x hx => by
        simp only [show ¬ (i + x < i) by omega, ite_false]
        rw [show i + x + l = i + l + x by omega])
    rw [s1, s2]; ring
  · intro k hk
    by_cases h1 : k ≤ i
    · exact ⟨k, by omega, by simp [h1]⟩
    · exact ⟨k + l, by omega, by simp [h1]⟩
  · intro k hk
    by_cases h1 : k < i
    · exact ⟨k, by omega, by simp [h1]⟩
    · exact ⟨k + l, by omega, by simp [h1]⟩

lemma Wk.insert {E : V → V → ℕ → Prop} {u n pos rw} (h : Wk E u n pos rw) {i : ℕ}
    (hin : i ≤ n) {l : ℕ} {cp : ℕ → V} {cr : ℕ → ℕ} (hc : Wk E (pos i) l cp cr) (hcl : cp l = pos i) :
    ∃ pos' rw', Wk E u (n + l) pos' rw' ∧ pos' (n + l) = pos n ∧
      (∑ k ∈ range (n + l), rw' k) = (∑ k ∈ range n, rw k) + ∑ k ∈ range l, cr k := by
  set P : ℕ → V := fun k => if k ≤ i then pos k else if k ≤ i + l then cp (k - i) else pos (k - l)
    with hP
  set R : ℕ → ℕ := fun k => if k < i then rw k else if k < i + l then cr (k - i) else rw (k - l)
    with hR
  have pA : ∀ k ≤ i, P k = pos k := fun k hk => by simp [hP, hk]
  have pB : ∀ k, i ≤ k → k ≤ i + l → P k = cp (k - i) := by
    intro k h1 h2
    by_cases h3 : k ≤ i
    · have : k = i := by omega
      subst this; simp [hP, hc.1]
    · simp [hP, h3, h2]
  have pC : ∀ k, i + l ≤ k → P k = pos (k - l) := by
    intro k h1
    by_cases h3 : k ≤ i
    · have : k = i := by omega
      have : l = 0 := by omega
      subst this; simp [hP, h3]
    · by_cases h4 : k ≤ i + l
      · have : k = i + l := by omega
        subst this; simp [hP, h3, hcl]
      · simp [hP, h3, h4]
  refine ⟨P, R, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [pA 0 (Nat.zero_le _)]; exact h.1
  · intro k hk
    by_cases h1 : k < i
    · rw [pA k (by omega), pA (k+1) (by omega)]
      simp only [hR, h1, ite_true]
      exact h.2 k (by omega)
    · by_cases h2 : k < i + l
      · rw [pB k (by omega) (by omega), pB (k+1) (by omega) (by omega)]
        simp only [hR, h1, h2, ite_false, ite_true]
        rw [show k + 1 - i = k - i + 1 by omega]
        exact hc.2 (k - i) (by omega)
      · rw [pC k (by omega), pC (k+1) (by omega)]
        simp only [hR, h1, h2, ite_false]
        rw [show k + 1 - l = k - l + 1 by omega]
        exact h.2 (k - l) (by omega)
  · rw [pC (n + l) (by omega)]; simp
  · have e1 : n + l = i + l + (n - i) := by omega
    have e2 : n = i + (n - i) := by omega
    rw [e1, sum_range_add, sum_range_add]
    conv_rhs => rw [e2, sum_range_add]
    have s1 : ∑ x ∈ range i, R x = ∑ x ∈ range i, rw x :=
      sum_congr rfl (fun x hx => by simp [hR, Finset.mem_range.1 hx])
    have s2 : ∑ x ∈ range l, R (i + x) = ∑ x ∈ range l, cr x :=
      sum_congr rfl (fun x hx => by
        have := Finset.mem_range.1 hx
        simp only [hR, show ¬ (i + x < i) by omega, show i + x < i + l by omega, ite_false, ite_true]
        rw [show i + x - i = x by omega])
    have s3 : ∑ x ∈ range (n - i), R (i + l + x) = ∑ x ∈ range (n - i), rw (i + x) :=
      sum_congr rfl (fun x hx => by
        simp only [hR, show ¬ (i + l + x < i + l) by omega, show ¬ (i + l + x < i) by omega, ite_false]
        rw [show i + l + x - l = i + x by omega])
    rw [s1, s2, s3]; ring

lemma rep {E : V → V → ℕ → Prop} {x : V} {l : ℕ} {cp : ℕ → V} {cr : ℕ → ℕ}
    (hc : Wk E x l cp cr) (hcl : cp l = x) (m : ℕ) :
    ∃ cp' cr', Wk E x (m * l) cp' cr' ∧ cp' (m * l) = x ∧
      ∑ k ∈ range (m * l), cr' k = m * ∑ k ∈ range l, cr k := by
  induction m with
  | zero => exact ⟨fun _ => x, fun _ => 0, ⟨rfl, fun i hi => by simp at hi⟩, rfl, by simp⟩
  | succ m ih =>
    obtain ⟨cp', cr', hw, he, hs⟩ := ih
    have hc' : Wk E (cp' (m * l)) l cp cr := by rw [he]; exact hc
    obtain ⟨P, R, hw2, he2, hs2⟩ := hw.insert (le_refl _) hc' (by rw [hcl, he])
    refine ⟨P, R, ?_, ?_, ?_⟩
    · rw [Nat.succ_mul]; exact hw2
    · rw [Nat.succ_mul, he2, he]
    · rw [Nat.succ_mul, hs2, hs]; ring


lemma Wk.seg {E : V → V → ℕ → Prop} {u n pos rw} (h : Wk E u n pos rw) {i j : ℕ}
    (hij : i ≤ j) (hjn : j ≤ n) :
    Wk E (pos i) (j - i) (fun k => pos (i + k)) (fun k => rw (i + k)) ∧
      (fun k => pos (i + k)) (j - i) = pos j := by
  refine ⟨⟨by simp, fun k hk => ?_⟩, by simp only; rw [show i + (j - i) = j by omega]⟩
  simp only
  rw [show i + (k + 1) = i + k + 1 by omega]
  exact h.2 (i + k) (by omega)

lemma ub [Fintype V] {E : V → V → ℕ → Prop} (hE : ∀ u v r, E u v r → r ≤ 10) (L β δ : ℕ) :
    ∀ n u pos rw, Wk E u n pos rw →
      (∀ k ≤ n, ∀ l cp cr, 1 ≤ l → l ≤ Fintype.card V → Wk E (pos k) l cp cr → cp l = pos k →
        L * (∑ x ∈ range l, cr x) + δ ≤ β * l) →
      Fintype.card V * L * (∑ x ∈ range n, rw x) + δ * n ≤
        Fintype.card V * n * β + 10 * L * Fintype.card V * Fintype.card V + δ * Fintype.card V := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro u pos rw h hyp
  set N := Fintype.card V with hNdef
  by_cases hn : n < N
  · have hs := sum_le10 rw n (fun i hi => hE _ _ _ (h.2 i hi))
    have h1 : N * L * (∑ x ∈ range n, rw x) ≤ N * L * (10 * n) := Nat.mul_le_mul_left _ hs
    have h2 : n ≤ N := hn.le
    have h3 : N * L * (10 * n) ≤ 10 * L * N * N := by
      have := Nat.mul_le_mul_left (10 * L * N) h2
      linarith
    have h4 : δ * n ≤ δ * N := Nat.mul_le_mul_left _ h2
    have h5 : 0 ≤ N * n * β := Nat.zero_le _
    linarith
  · push_neg at hn
    obtain ⟨x, y, hxy, hpxy⟩ := Fintype.exists_ne_map_eq_of_card_lt
      (fun k : Fin (N + 1) => pos k.val) (by simp [hNdef])
    have hv : x.val ≠ y.val := fun e => hxy (Fin.ext e)
    obtain ⟨i, j, hij, hjN, heq⟩ : ∃ i j, i < j ∧ j ≤ N ∧ pos i = pos j := by
      rcases lt_or_gt_of_ne hv with hl | hl
      · exact ⟨x.val, y.val, hl, by omega, hpxy⟩
      · exact ⟨y.val, x.val, hl, by omega, hpxy.symm⟩
    obtain ⟨pos', rw', hw', -, hsum, hvis, -⟩ := h.remove hij (by omega) heq
    have ih' := ih (n - (j - i)) (by omega) u pos' rw' hw' (fun k hk l cp cr h1 h2 hw hcl => by
      obtain ⟨k', hk', e⟩ := hvis k hk
      rw [e] at hw hcl
      exact hyp k' hk' l cp cr h1 h2 hw hcl)
    obtain ⟨hcw, hcl⟩ := h.seg hij.le (by omega)
    have hcyc := hyp i (by omega) (j - i) _ _ (by omega) (by omega) hcw (hcl.trans heq.symm)
    have hc2 : N * (L * (∑ x ∈ range (j - i), rw (i + x)) + δ) ≤ N * (β * (j - i)) :=
      Nat.mul_le_mul_left _ hcyc
    have hdl : δ * (j - i) ≤ δ * N := Nat.mul_le_mul_left _ (by omega)
    obtain ⟨m, hm⟩ : ∃ m, n = m + (j - i) := ⟨n - (j - i), by omega⟩
    rw [show n - (j - i) = m by omega] at ih'
    rw [hsum, show n - (j - i) = m by omega, hm]
    nlinarith

def score (fin : V → ℕ) (n : ℕ) (pos : ℕ → V) (rw : ℕ → ℕ) : ℕ :=
  (∑ i ∈ range n, rw i) + fin (pos n)

noncomputable def Mx (E : V → V → ℕ → Prop) (v0 : V) (fin : V → ℕ) (n : ℕ) : ℕ :=
  sSup {x | ∃ pos rw, Wk E v0 n pos rw ∧ score fin n pos rw = x}

lemma Mx_spec {E : V → V → ℕ → Prop} {v0 : V} {fin : V → ℕ} (hE : ∀ u v r, E u v r → r ≤ 10)
    (hfin : ∀ v, fin v ≤ 10) (n : ℕ) (hex : ∃ pos rw, Wk E v0 n pos rw) :
    (∃ pos rw, Wk E v0 n pos rw ∧ score fin n pos rw = Mx E v0 fin n) ∧
      ∀ pos rw, Wk E v0 n pos rw → score fin n pos rw ≤ Mx E v0 fin n := by
  have hb : BddAbove {x | ∃ pos rw, Wk E v0 n pos rw ∧ score fin n pos rw = x} := by
    refine ⟨10 * n + 10, ?_⟩
    rintro x ⟨pos, rw, h, rfl⟩
    have := sum_le10 rw n (fun i hi => hE _ _ _ (h.2 i hi))
    have := hfin (pos n)
    unfold score; omega
  obtain ⟨pos, rw, h⟩ := hex
  have hne : Set.Nonempty {x | ∃ pos rw, Wk E v0 n pos rw ∧ score fin n pos rw = x} :=
    ⟨_, pos, rw, h, rfl⟩
  exact ⟨Nat.sSup_mem hne hb, fun pos rw h => le_csSup hb ⟨pos, rw, h, rfl⟩⟩

lemma evconst (f : ℕ → ℤ) (C : ℤ) (hm : ∀ j, f j ≤ f (j + 1)) (hb : ∀ j, f j ≤ C) :
    ∃ J, ∀ j ≥ J, f (j + 1) = f j := by
  by_contra hc
  push_neg at hc
  have mono := monotone_nat_of_le_succ hm
  have key : ∀ k : ℕ, ∃ j, f 0 + k ≤ f j := by
    intro k
    induction k with
    | zero => exact ⟨0, by simp⟩
    | succ k ih =>
      obtain ⟨j, hj⟩ := ih
      obtain ⟨j', hj', hne⟩ := hc j
      have h1 := mono hj'
      have h2 := hm j'
      have h3 : f j' + 1 ≤ f (j' + 1) := by
        rcases lt_or_eq_of_le h2 with h | h
        · omega
        · exact absurd h.symm hne
      exact ⟨j' + 1, by push_cast; linarith⟩
  obtain ⟨j, hj⟩ := key (C - f 0 + 1).toNat
  have := hb j
  have : ((C - f 0 + 1).toNat : ℤ) ≥ C - f 0 + 1 := Int.self_le_toNat _
  linarith


theorem core [Fintype V] [DecidableEq V] (E : V → V → ℕ → Prop) (v0 : V) (fin : V → ℕ)
    (hE : ∀ u v r, E u v r → r ≤ 10) (hfin : ∀ v, fin v ≤ 10) :
    (∃ N, ∀ n ≥ N, ∀ pos rw, ¬ Wk E v0 n pos rw) ∨
    (∃ L β C0 C1 T Q A : ℕ, 0 < L ∧ 0 < Q ∧ (∀ n, ∃ pos rw, Wk E v0 n pos rw) ∧
      (∀ n, L * Mx E v0 fin n ≤ n * β + C0) ∧ (∀ n, n * β ≤ L * Mx E v0 fin n + C1) ∧
      (∀ n ≥ T, Mx E v0 fin (n + Q) = Mx E v0 fin n + A) ∧ L * A = Q * β) := by
  classical
  set N := Fintype.card V with hNdef
  have hN : 0 < N := Fintype.card_pos_iff.2 ⟨v0⟩
  set S := ((Icc 1 N) ×ˢ (range (10 * N + 1))).filter (fun q : ℕ × ℕ =>
    ∃ n pos rw, Wk E v0 n pos rw ∧ ∃ k ≤ n, ∃ cp cr, Wk E (pos k) q.1 cp cr ∧ cp q.1 = pos k ∧
      ∑ x ∈ range q.1, cr x = q.2) with hSdef
  have memS : ∀ n pos rw, Wk E v0 n pos rw → ∀ k ≤ n, ∀ l cp cr, 1 ≤ l → l ≤ N →
      Wk E (pos k) l cp cr → cp l = pos k → (l, ∑ x ∈ range l, cr x) ∈ S := by
    intro n pos rw h k hk l cp cr h1 h2 hw hcl
    have hs := sum_le10 cr l (fun i hi => hE _ _ _ (hw.2 i hi))
    simp only [hSdef, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_range]
    refine ⟨⟨⟨h1, h2⟩, by nlinarith⟩, n, pos, rw, h, k, hk, cp, cr, hw, hcl, rfl⟩
  have pig : ∀ n pos rw, Wk E v0 n pos rw → N ≤ n → ∃ i j, i < j ∧ j ≤ N ∧ pos i = pos j := by
    intro n pos rw h hn
    obtain ⟨x, y, hxy, hpxy⟩ := Fintype.exists_ne_map_eq_of_card_lt
      (fun k : Fin (N + 1) => pos k.val) (by simp [hNdef])
    have hv : x.val ≠ y.val := fun e => hxy (Fin.ext e)
    rcases lt_or_gt_of_ne hv with hl | hl
    · exact ⟨x.val, y.val, hl, by omega, hpxy⟩
    · exact ⟨y.val, x.val, hl, by omega, hpxy.symm⟩
  rcases S.eq_empty_or_nonempty with hS | hS
  · left
    refine ⟨N, fun n hn pos rw h => ?_⟩
    obtain ⟨i, j, hij, hjN, heq⟩ := pig n pos rw h hn
    obtain ⟨hcw, hcl⟩ := h.seg hij.le (by omega)
    have := memS n pos rw h i (by omega) (j - i) _ _ (by omega) (by omega) hcw (hcl.trans heq.symm)
    rw [hS] at this
    simp at this
  right
  obtain ⟨⟨L, β⟩, hmem, hmax⟩ := S.exists_max_image (fun q => (q.2 : ℚ) / q.1) hS
  have hmem' := hmem
  simp only [hSdef, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_range] at hmem'
  obtain ⟨⟨⟨hL1, hLN⟩, -⟩, n0, pos0, rw0, h0, k0, hk0, cp, cr, hc, hcl, hcs⟩ := hmem'
  have hL : 0 < L := hL1
  have ratio : ∀ q ∈ S, q.2 * L ≤ β * q.1 := by
    intro q hq
    have h1 := hmax q hq
    have hq1 : 1 ≤ q.1 := by
      simp only [hSdef, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hq
      exact hq.1.1.1
    simp only at h1
    rw [div_le_div_iff₀ (by exact_mod_cast hq1) (by exact_mod_cast hL)] at h1
    exact_mod_cast h1
  have ub0 : ∀ n pos rw, Wk E v0 n pos rw →
      L * score fin n pos rw ≤ n * β + (10 * L * N + 10 * L) := by
    intro n pos rw h
    have := ub hE L β 0 n v0 pos rw h (fun k hk l cp cr h1 h2 hw hcl => by
      have r := ratio _ (memS n pos rw h k hk l cp cr h1 h2 hw hcl)
      simp only at r
      linarith)
    have h2 : N * (L * ∑ x ∈ range n, rw x) ≤ N * (n * β + 10 * L * N) := by nlinarith
    have h3 := Nat.le_of_mul_le_mul_left h2 hN
    have := hfin (pos n)
    unfold score
    nlinarith
  have pump : ∀ m, ∃ pos rw, Wk E v0 (k0 + m * L) pos rw ∧
      m * β ≤ ∑ x ∈ range (k0 + m * L), rw x := by
    intro m
    obtain ⟨cp', cr', hw', he', hs'⟩ := rep hc hcl m
    obtain ⟨P, R, hP, -, hs⟩ := (h0.pre hk0).insert (le_refl k0) hw' he'
    refine ⟨P, R, hP, ?_⟩
    rw [hs, hs', hcs]
    exact Nat.le_add_left _ _
  set C1 := 10 * L * (k0 + L) with hC1
  set C0 := 10 * L * N + 10 * L with hC0
  have lb : ∀ n, ∃ pos rw, Wk E v0 n pos rw ∧ n * β ≤ L * score fin n pos rw + C1 := by
    intro n
    obtain ⟨P, R, hP, hs⟩ := pump (n / L + 1)
    have hd1 := Nat.div_add_mod n L
    have hd2 := Nat.mod_lt n hL
    have hmL : n ≤ (n / L + 1) * L := by nlinarith
    have hmL2 : (n / L + 1) * L ≤ n + L := by
      rw [add_mul, one_mul]; have := Nat.div_mul_le_self n L; omega
    obtain ⟨d, hd⟩ : ∃ d, k0 + (n / L + 1) * L = n + d := ⟨k0 + (n / L + 1) * L - n, by omega⟩
    have hdle : d ≤ k0 + L := by omega
    rw [hd, sum_range_add] at hs
    have hP' := hP
    rw [hd] at hP'
    have hrest : ∑ x ∈ range d, R (n + x) ≤ 10 * d :=
      sum_le10 _ d (fun i hi => hE _ _ _ (hP'.2 (n + i) (by omega)))
    refine ⟨P, R, hP'.pre (by omega), ?_⟩
    unfold score
    have e1 : n * β ≤ (n / L + 1) * L * β := Nat.mul_le_mul_right _ hmL
    have e2 : L * ((n / L + 1) * β) ≤ L * (∑ x ∈ range n, R x + ∑ x ∈ range d, R (n + x)) :=
      Nat.mul_le_mul_left _ hs
    have e3 : L * (10 * d) ≤ L * (10 * (k0 + L)) := Nat.mul_le_mul_left _ (by omega)
    have e4 : L * ∑ x ∈ range d, R (n + x) ≤ L * (10 * d) := Nat.mul_le_mul_left _ hrest
    nlinarith
  have hall : ∀ n, ∃ pos rw, Wk E v0 n pos rw := fun n => by
    obtain ⟨P, R, h, -⟩ := lb n; exact ⟨P, R, h⟩
  have lbM : ∀ n, n * β ≤ L * Mx E v0 fin n + C1 := by
    intro n
    obtain ⟨P, R, h, hb⟩ := lb n
    have := (Mx_spec hE hfin n (hall n)).2 P R h
    nlinarith
  have ubM : ∀ n, L * Mx E v0 fin n ≤ n * β + C0 := by
    intro n
    obtain ⟨⟨P, R, h, he⟩, -⟩ := Mx_spec hE hfin n (hall n)
    rw [← he]; exact ub0 n P R h
  set T0 := 10 * L * N + N * C1 + 10 * L * N * N + N + 1 with hT0
  have crit : ∀ n ≥ T0, ∀ pos rw, Wk E v0 n pos rw → n * β ≤ L * score fin n pos rw + C1 →
      ∃ k ≤ n, ∃ l cp cr, 1 ≤ l ∧ l ≤ N ∧ Wk E (pos k) l cp cr ∧ cp l = pos k ∧
        (∑ x ∈ range l, cr x) * L = β * l := by
    intro n hn pos rw h hsc
    by_contra hno
    push_neg at hno
    have hu := ub hE L β 1 n v0 pos rw h (fun k hk l cp cr h1 h2 hw hcl => by
      have r := ratio _ (memS n pos rw h k hk l cp cr h1 h2 hw hcl)
      simp only at r
      have hne := hno k hk l cp cr h1 h2 hw hcl
      have : (∑ x ∈ range l, cr x) * L < β * l := lt_of_le_of_ne r hne
      linarith)
    have hf := hfin (pos n)
    unfold score at hsc
    have e1 : N * (n * β) ≤ N * (L * (∑ x ∈ range n, rw x + fin (pos n)) + C1) :=
      Nat.mul_le_mul_left _ hsc
    have e2 : N * (L * fin (pos n)) ≤ N * (L * 10) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hf)
    nlinarith
  set Q := L * N.factorial with hQ
  set A := N.factorial * β with hA
  have hLA : L * A = Q * β := by rw [hA, hQ]; ring
  have hQpos : 0 < Q := Nat.mul_pos hL (Nat.factorial_pos _)
  have step : ∀ n ≥ T0, Mx E v0 fin n + A ≤ Mx E v0 fin (n + Q) := by
    intro n hn
    obtain ⟨⟨pos, rw, h, hsc⟩, -⟩ := Mx_spec hE hfin n (hall n)
    have hsc' : n * β ≤ L * score fin n pos rw + C1 := by rw [hsc]; exact lbM n
    obtain ⟨k, hk, l, cp, cr, h1, h2, hw, hcl, hcrit⟩ := crit n hn pos rw h hsc'
    obtain ⟨c, hc⟩ := Nat.dvd_factorial h1 h2
    obtain ⟨cp', cr', hw', he', hs'⟩ := rep hw hcl (L * c)
    obtain ⟨P, R, hP, heP, hsP⟩ := h.insert hk hw' he'
    have hlen : n + L * c * l = n + Q := by rw [hQ, hc]; ring
    rw [hlen] at hP heP hsP
    have hsum : L * c * ∑ x ∈ range l, cr x = A := by
      have : l * (L * c * ∑ x ∈ range l, cr x) = l * A := by
        rw [hA, hc]
        calc l * (L * c * ∑ x ∈ range l, cr x) = c * ((∑ x ∈ range l, cr x) * L) * l := by ring
          _ = c * (β * l) * l := by rw [hcrit]
          _ = l * ((l * c) * β) := by ring
      exact Nat.eq_of_mul_eq_mul_left h1 this
    have := (Mx_spec hE hfin (n + Q) (hall _)).2 P R hP
    unfold score at this hsc
    rw [hsP, heP, hs', hsum] at this
    omega
  set g : ℕ → ℤ := fun n => (L : ℤ) * (Mx E v0 fin n : ℤ) - (n : ℤ) * β with hg
  have gmono : ∀ n ≥ T0, g n ≤ g (n + Q) := by
    intro n hn
    have h1 := step n hn
    have h2 : (L : ℤ) * (Mx E v0 fin n + A) ≤ L * Mx E v0 fin (n + Q) := by
      exact_mod_cast Nat.mul_le_mul_left L h1
    have h3 : (L : ℤ) * A = Q * β := by exact_mod_cast hLA
    simp only [hg]; push_cast; nlinarith
  have gbd : ∀ n, g n ≤ C0 := by
    intro n
    have := ubM n
    have h2 : ((L * Mx E v0 fin n : ℕ) : ℤ) ≤ ((n * β + C0 : ℕ) : ℤ) := by exact_mod_cast this
    push_cast at h2
    simp only [hg]; linarith
  set G : ℕ → ℤ := fun j => ∑ r ∈ range Q, g (T0 + j * Q + r) with hG
  have Gmono : ∀ j, G j ≤ G (j + 1) := by
    intro j
    simp only [hG]
    apply sum_le_sum
    intro r _
    have := gmono (T0 + j * Q + r) (by omega)
    rw [show T0 + (j + 1) * Q + r = T0 + j * Q + r + Q by ring]
    exact this
  have Gbd : ∀ j, G j ≤ Q * C0 := by
    intro j
    simp only [hG]
    have := sum_le_card_nsmul (range Q) (fun r => g (T0 + j * Q + r)) (C0 : ℤ)
      (fun r _ => gbd _)
    simpa using this
  obtain ⟨J, hJ⟩ := evconst G (Q * C0) Gmono Gbd
  refine ⟨L, β, C0, C1, T0 + J * Q, Q, A, hL, hQpos, hall, ubM, lbM, ?_, hLA⟩
  intro n hn
  have hT : T0 ≤ n := le_trans (Nat.le_add_right _ _) hn
  obtain ⟨j, r, hrQ, hn'⟩ : ∃ j r, r < Q ∧ n = T0 + j * Q + r := by
    refine ⟨(n - T0) / Q, (n - T0) % Q, Nat.mod_lt _ hQpos, ?_⟩
    have h1 := Nat.div_add_mod (n - T0) Q
    have h2 := Nat.sub_add_cancel hT
    rw [mul_comm] at h1
    linarith
  have hjJ : J ≤ j := by
    by_contra hcon
    push_neg at hcon
    have : (j + 1) * Q ≤ J * Q := Nat.mul_le_mul_right _ hcon
    nlinarith
  have heq := hJ j hjJ
  simp only [hG] at heq
  have hall2 := (sum_eq_sum_iff_of_le (fun r _ => by
      have := gmono (T0 + j * Q + r) (by omega)
      rw [show T0 + (j + 1) * Q + r = T0 + j * Q + r + Q by ring]
      exact this)).1 heq.symm r (Finset.mem_range.2 hrQ)
  rw [show T0 + (j + 1) * Q + r = T0 + j * Q + r + Q by ring, ← hn'] at hall2
  simp only [hg] at hall2
  have h3 : (L : ℤ) * A = Q * β := by exact_mod_cast hLA
  rw [Nat.cast_add n Q] at hall2
  have h4 : (L : ℤ) * Mx E v0 fin (n + Q) = L * ((Mx E v0 fin n : ℤ) + (A : ℤ)) := by
    linarith
  have h5 : L * Mx E v0 fin (n + Q) = L * (Mx E v0 fin n + A) := by
    have : ((L * Mx E v0 fin (n + Q) : ℕ) : ℤ) = ((L * (Mx E v0 fin n + A) : ℕ) : ℤ) := by
      rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_add]; exact h4
    exact Nat.cast_injective this
  exact Nat.eq_of_mul_eq_mul_left hL h5


def EE {s p : ℕ} (mark : Fin p → Bool × Bool) (edge : Bool × Bool → Fin s → Fin s → Fin 11 → Prop)
    (u v : Fin s × Fin p) (r : ℕ) : Prop :=
  v.2.val = (u.2.val + 1) % p ∧ ∃ r' : Fin 11, r'.val = r ∧ edge (mark u.2) u.1 v.1 r'

def fn {s p : ℕ} (finish : Fin s → Fin 11) (v : Fin s × Fin p) : ℕ := (finish v.1).val

lemma succ_mod (i p : ℕ) : (i % p + 1) % p = (i + 1) % p := by
  rw [Nat.add_mod (i % p), Nat.mod_mod, ← Nat.add_mod]

lemma phase {s p : ℕ} (hp : 0 < p) (mark : Fin p → Bool × Bool)
    (edge : Bool × Bool → Fin s → Fin s → Fin 11 → Prop) (start : Fin s) {n pos rw}
    (h : Wk (EE mark edge) (start, ⟨0, hp⟩) n pos rw) : ∀ i ≤ n, (pos i).2.val = i % p := by
  intro i
  induction i with
  | zero => intro _; rw [h.1]; simp
  | succ i ih =>
    intro hi
    rw [(h.2 i (by omega)).1, ih (by omega), succ_mod]

lemma trans {s p : ℕ} (hp : 0 < p) (mark : Fin p → Bool × Bool) (start : Fin s)
    (edge : Bool × Bool → Fin s → Fin s → Fin 11 → Prop) (finish : Fin s → Fin 11) (k d : ℕ)
    (w : Fin k → Bool × Bool) (hw : ∀ i, w i = mark ⟨i.val % p, Nat.mod_lt _ hp⟩) :
    (∃ (path : Fin (k + 1) → Fin s) (reward : Fin k → Fin 11),
      path 0 = start ∧
      (∀ i : Fin k, edge (w i) (path i.castSucc) (path i.succ) (reward i)) ∧
      k ≤ d + (∑ i, (reward i).val) + (finish (path (Fin.last k))).val) ↔
    ∃ pos rw, Wk (EE mark edge) (start, ⟨0, hp⟩) k pos rw ∧ k ≤ d + score (fn finish) k pos rw := by
  constructor
  · rintro ⟨path, reward, h0, hed, hk⟩
    refine ⟨fun i => if h : i ≤ k then (path ⟨i, by omega⟩, ⟨i % p, Nat.mod_lt _ hp⟩)
        else (start, ⟨0, hp⟩),
      fun i => if h : i < k then (reward ⟨i, h⟩).val else 0, ⟨?_, ?_⟩, ?_⟩
    · simp only [Nat.zero_le, dite_true]
      rw [← h0]
      exact Prod.ext rfl (Fin.ext (by simp))
    · intro i hi
      simp only [show i ≤ k by omega, show i + 1 ≤ k by omega, hi, dite_true]
      refine ⟨by simp [succ_mod], reward ⟨i, hi⟩, rfl, ?_⟩
      have := hed ⟨i, hi⟩
      rw [hw] at this
      exact this
    · unfold score fn
      simp only [le_refl, dite_true]
      have : ∑ i ∈ range k, (if h : i < k then (reward ⟨i, h⟩).val else 0) =
          ∑ i : Fin k, (reward i).val := by
        rw [← Fin.sum_univ_eq_sum_range]
        apply Finset.sum_congr rfl
        intro i _
        simp [i.isLt]
      rw [this, ← add_assoc]
      exact hk
  · rintro ⟨pos, rw, hW, hk⟩
    have ph := phase hp mark edge start hW
    have hx : ∀ i : Fin k, ∃ r' : Fin 11, r'.val = rw i.val ∧
        edge (mark (pos i.val).2) (pos i.val).1 (pos (i.val + 1)).1 r' :=
      fun i => (hW.2 i.val i.isLt).2
    choose rew hrew using hx
    refine ⟨fun i => (pos i.val).1, rew, ?_, ?_, ?_⟩
    · simp [hW.1]
    · intro i
      have e1 : (pos i.val).2 = ⟨i.val % p, Nat.mod_lt _ hp⟩ := Fin.ext (ph i.val (by omega))
      have := (hrew i).2
      rw [e1] at this
      rw [hw]
      exact this
    · unfold score fn at hk
      have : ∑ i : Fin k, (rew i).val = ∑ i ∈ range k, rw i := by
        rw [← Fin.sum_univ_eq_sum_range]
        exact Finset.sum_congr rfl (fun i _ => (hrew i).1)
      rw [this, add_assoc]
      simpa using hk

noncomputable def Fk {V : Type} (E : V → V → ℕ → Prop) (v0 : V) (fin : V → ℕ) (k : ℕ) : ℕ :=
  sInf {d | ∃ pos rw, Wk E v0 k pos rw ∧ k ≤ d + score fin k pos rw}

lemma Fk_eq {V : Type} {E : V → V → ℕ → Prop} {v0 : V} {fin : V → ℕ}
    (hE : ∀ u v r, E u v r → r ≤ 10) (hfin : ∀ v, fin v ≤ 10) (k : ℕ)
    (hex : ∃ pos rw, Wk E v0 k pos rw) : Fk E v0 fin k = k - Mx E v0 fin k := by
  obtain ⟨⟨pos, rw, h, he⟩, hall⟩ := Mx_spec hE hfin k hex
  apply le_antisymm
  · apply Nat.sInf_le
    exact ⟨pos, rw, h, by rw [he]; omega⟩
  · apply le_csInf
    · exact ⟨k, pos, rw, h, by omega⟩
    · rintro d ⟨pos', rw', h', hd⟩
      have := hall pos' rw' h'
      omega

lemma Fk_le {V : Type} (E : V → V → ℕ → Prop) (v0 : V) (fin : V → ℕ) (k : ℕ) :
    Fk E v0 fin k ≤ k := by
  by_cases hw : ∃ pos rw, Wk E v0 k pos rw
  · obtain ⟨pos, rw, h⟩ := hw
    exact Nat.sInf_le ⟨pos, rw, h, by omega⟩
  · have : {d | ∃ pos rw, Wk E v0 k pos rw ∧ k ≤ d + score fin k pos rw} = ∅ := by
      ext d
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨pos, rw, h, -⟩
      exact hw ⟨pos, rw, h⟩
    unfold Fk
    rw [this, Nat.sInf_empty]
    omega

lemma Fk_zero {V : Type} (E : V → V → ℕ → Prop) (v0 : V) (fin : V → ℕ) (k : ℕ)
    (hno : ∀ pos rw, ¬ Wk E v0 k pos rw) : Fk E v0 fin k = 0 := by
  have : {d | ∃ pos rw, Wk E v0 k pos rw ∧ k ≤ d + score fin k pos rw} = ∅ := by
    ext d
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨pos, rw, h, -⟩
    exact hno pos rw h
  unfold Fk
  rw [this, Nat.sInf_empty]

lemma final (p e : ℕ) (d : ℕ → ℕ)
    (hqa : ∀ t t', 0 < t → 0 < t' → d t + d t' ≤ d (t + t') + e ∧ d (t + t') ≤ d t + d t' + e)
    (hle : ∀ t, d t ≤ p * t) (T q a : ℕ) (hq : 0 < q) (hper : ∀ t ≥ T, d (t + q) = d t + a) :
    ∃ T q a : ℕ, 0 < T ∧ 0 < q ∧ a ≤ p * q ∧ (∀ t, T ≤ t → d (t + q) = d t + a) ∧
      ∀ t, 0 < t → q * d t ≤ t * a + q * e ∧ t * a ≤ q * d t + q * e := by
  have iter : ∀ t ≥ T, ∀ i, d (t + i * q) = d t + i * a := by
    intro t ht i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [show t + (i + 1) * q = t + i * q + q by ring, hper _ (by nlinarith), ih]
      ring
  have mult : ∀ t, 0 < t → ∀ n, (n + 1) * d t ≤ d ((n + 1) * t) + (n + 1) * e ∧
      d ((n + 1) * t) ≤ (n + 1) * d t + (n + 1) * e := by
    intro t ht n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [show (n + 1 + 1) * t = (n + 1) * t + t by ring]
      have h := hqa ((n + 1) * t) t (by positivity) ht
      constructor <;> nlinarith [ih.1, ih.2, h.1, h.2]
  refine ⟨T + 1, q, a, by omega, hq, ?_, fun t ht => hper t (by omega), ?_⟩
  · by_contra hcon
    push_neg at hcon
    have h1 := iter T le_rfl (p * T + 1)
    have h2 := hle (T + (p * T + 1) * q)
    have h3 : (p * T + 1) * (p * q + 1) ≤ (p * T + 1) * a := Nat.mul_le_mul_left _ hcon
    nlinarith
  · intro t ht
    have hB : T ≤ T * q * t := by
      have : 1 ≤ q * t := Nat.mul_pos hq ht
      nlinarith
    have key : ∀ m, 0 < m → (T + m) * q * d t ≤ d (T * q * t) + m * t * a + (T + m) * q * e ∧
        d (T * q * t) + m * t * a ≤ (T + m) * q * d t + (T + m) * q * e := by
      intro m hm
      have hpos : 0 < (T + m) * q := Nat.mul_pos (by omega) hq
      obtain ⟨n, hn⟩ : ∃ n, (T + m) * q = n + 1 := ⟨(T + m) * q - 1, by omega⟩
      have hm2 := mult t ht n
      rw [← hn] at hm2
      have hit := iter (T * q * t) hB (m * t)
      rw [show T * q * t + m * t * q = (T + m) * q * t by ring] at hit
      rw [hit] at hm2
      constructor <;> nlinarith [hm2.1, hm2.2]
    constructor
    · by_contra hcon
      push_neg at hcon
      have hk := (key (d (T * q * t) + 1) (by omega)).1
      have h1 : (T + (d (T * q * t) + 1)) * (t * a + q * e + 1) ≤
          (T + (d (T * q * t) + 1)) * (q * d t) := Nat.mul_le_mul_left _ hcon
      have h0 : 0 ≤ T * t * a := Nat.zero_le _
      nlinarith
    · by_contra hcon
      push_neg at hcon
      set m := T * q * d t + T * q * e + 1 with hm
      have hk := (key m (by omega)).2
      have h1 : m * (q * d t + q * e + 1) ≤ m * (t * a) := Nat.mul_le_mul_left _ hcon
      nlinarith

end PEqualNP.Outside.L_meta_29745_aux

theorem PEqualNP.Outside.L_meta_29745 :
    let fits := fun (k : ℕ) (hk : 0 < k) (mark : Fin k → Bool × Bool) (d : ℕ)
        (name c₁ c₂ : Bool → Fin k → ZMod 2) =>
      let F := ZMod 2
      let W := Fin k → F
      let D := W →ₗ[F] F
      let ix := fun n : ℕ => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
      let rot := fun (s : ℕ) (x : W) (i : Fin k) => x (ix (i.val + k - s % k))
      let mix := fun (g : ℕ) (x : W) (i : Fin k) =>
        x i + x (ix (i.val + g)) + x (ix (i.val + k - g % k))
      let step := fun (x : W) (i : Fin k) =>
        x i + (1 + x (ix (i.val + 1))) * x (ix (i.val + 2))
      let gap := fun b : Bool => if b then 2 else (1 : ℕ)
      let spin := fun b : Bool => if b then 3 else (1 : ℕ)
      let diff := fun (f : W → F) (u x : W) => f (x + u) - f x
      let fourth := fun (f : W → F) (v : Fin 4 → W) => (List.ofFn v).foldl diff f
      let cubic := fun (f : W → F) => ∀ v x, fourth f v x = 0
      let out := fun (x : W) (b : Bool) =>
        let z := mix (gap b) (rot (spin b) x + name b)
        let y := step z + rot (if b then 4 else 0) x + c₁ b
        step (mix (gap b) y) + rot (if b then 7 else 2) x + c₂ b
      let run := fun (ask : Fin d → ℕ → D) (x : W) =>
        (List.finRange d).foldl (fun h j =>
          2 * h + (if ask j h x = 0 then 0 else 1)) (0 : ℕ)
      ∃ (ask : Fin d → ℕ → D) (readout : ℕ → Bool → Fin k → W → F),
        (∀ h b i, cubic (readout h b i)) ∧
        ∀ x b i, (if b then (mark i).2 else (mark i).1) = true →
          out x b i = readout (run ask x) b i x
    let cost := fun (k : ℕ) (hk : 0 < k) (mark : Fin k → Bool × Bool) =>
      sInf {d : ℕ | ∀ name c₁ c₂, fits k hk mark d name c₁ c₂}
    (∃ (s : ℕ) (start : Fin s) (edge : Bool × Bool → Fin s → Fin s → Fin 11 → Prop)
        (finish : Fin s → Fin 11),
      s ≤ 2 ^ 400 ∧
      ∀ (k : ℕ) (hk : 0 < k) (mark : Fin k → Bool × Bool) (d : ℕ) (name c₁ c₂),
        fits k hk mark d name c₁ c₂ ↔
        ∃ (path : Fin (k + 1) → Fin s) (reward : Fin k → Fin 11),
          path 0 = start ∧
          (∀ i : Fin k, edge (mark i) (path i.castSucc) (path i.succ) (reward i)) ∧
          k ≤ d + (∑ i, (reward i).val) + (finish (path (Fin.last k))).val) →
    (∀ (k l : ℕ) (hk : 0 < k) (hl : 0 < l) (a : Fin k → Bool × Bool) (b : Fin l → Bool × Bool),
      let u := cost k hk a + cost l hl b
      let v := cost (k + l) (Nat.add_pos_left hk l) (Fin.addCases a b)
      let e : ℕ := if (∀ i, (a i).2 = false) ∧ (∀ j, (b j).2 = false) then 6 else 10
      u ≤ v + e ∧ v ≤ u + e) →
    ∀ (p : ℕ) (hp : 0 < p) (mark : Fin p → Bool × Bool),
      let depth := fun t : ℕ => if ht : 0 < t then
        cost (p * t) (Nat.mul_pos hp ht)
          (fun i => mark ⟨i.val % p, Nat.mod_lt _ hp⟩) else 0
      let e : ℕ := if ∀ j, (mark j).2 = false then 6 else 10
      ∃ T q a : ℕ, 0 < T ∧ 0 < q ∧ a ≤ p * q ∧
        (∀ t, T ≤ t → depth (t + q) = depth t + a) ∧
        ∀ t, 0 < t → q * depth t ≤ t * a + q * e ∧ t * a ≤ q * depth t + q * e := by
  intro fits cost hscan H2 p hp mark depth e
  obtain ⟨s, start, edge, finish, -, H1⟩ := hscan
  have hE : ∀ u v r, PEqualNP.Outside.L_meta_29745_aux.EE mark edge u v r → r ≤ 10 := by
    rintro u v r ⟨-, r', rfl, -⟩
    have := r'.isLt
    omega
  have hfin : ∀ v : Fin s × Fin p, PEqualNP.Outside.L_meta_29745_aux.fn finish v ≤ 10 := by
    intro v
    have := (finish v.1).isLt
    unfold PEqualNP.Outside.L_meta_29745_aux.fn
    omega
  have hcost : ∀ k hk (w : Fin k → Bool × Bool), (∀ i, w i = mark ⟨i.val % p, Nat.mod_lt _ hp⟩) →
      cost k hk w = PEqualNP.Outside.L_meta_29745_aux.Fk (PEqualNP.Outside.L_meta_29745_aux.EE mark edge)
        (start, ⟨0, hp⟩) (PEqualNP.Outside.L_meta_29745_aux.fn finish) k := by
    intro k hk w hw
    show sInf _ = sInf _
    congr 1
    ext d
    simp only [Set.mem_setOf_eq]
    rw [← PEqualNP.Outside.L_meta_29745_aux.trans hp mark start edge finish k d w hw]
    constructor
    · intro h
      exact (H1 k hk w d 0 0 0).1 (h 0 0 0)
    · intro h n c1 c2
      exact (H1 k hk w d n c1 c2).2 h
  set D : ℕ → ℕ := fun t => PEqualNP.Outside.L_meta_29745_aux.Fk
    (PEqualNP.Outside.L_meta_29745_aux.EE mark edge) (start, ⟨0, hp⟩)
    (PEqualNP.Outside.L_meta_29745_aux.fn finish) (p * t) with hD
  have hdepth : ∀ t, 0 < t → depth t = D t := by
    intro t ht
    show (if ht : 0 < t then cost (p * t) (Nat.mul_pos hp ht)
      (fun i => mark ⟨i.val % p, Nat.mod_lt _ hp⟩) else 0) = D t
    rw [dif_pos ht]
    exact hcost _ (Nat.mul_pos hp ht) _ (fun i => rfl)
  have hqa : ∀ t t', 0 < t → 0 < t' → D t + D t' ≤ D (t + t') + e ∧ D (t + t') ≤ D t + D t' + e := by
    intro t t' ht ht'
    have h := H2 (p * t) (p * t') (Nat.mul_pos hp ht) (Nat.mul_pos hp ht')
      (fun i => mark ⟨i.val % p, Nat.mod_lt _ hp⟩) (fun i => mark ⟨i.val % p, Nat.mod_lt _ hp⟩)
    have hadd : ∀ i : Fin (p * t + p * t'), Fin.addCases (motive := fun _ => Bool × Bool)
        (fun i : Fin (p * t) => mark ⟨i.val % p, Nat.mod_lt _ hp⟩)
        (fun i : Fin (p * t') => mark ⟨i.val % p, Nat.mod_lt _ hp⟩) i =
        mark ⟨i.val % p, Nat.mod_lt _ hp⟩ := by
      intro i
      refine Fin.addCases (fun i => ?_) (fun j => ?_) i
      · rw [Fin.addCases_left]
        rfl
      · rw [Fin.addCases_right]
        congr 1
        apply Fin.ext
        simp [Nat.add_mod]
    have he' : (if (∀ i : Fin (p * t), (mark ⟨i.val % p, Nat.mod_lt _ hp⟩).2 = false) ∧
        (∀ j : Fin (p * t'), (mark ⟨j.val % p, Nat.mod_lt _ hp⟩).2 = false) then 6 else 10) = e := by
      show _ = if ∀ j, (mark j).2 = false then 6 else 10
      by_cases hm : ∀ j, (mark j).2 = false
      · rw [if_pos ⟨fun i => hm _, fun i => hm _⟩, if_pos hm]
      · rw [if_neg hm, if_neg]
        rintro ⟨h1, -⟩
        apply hm
        intro j
        have hj : j.val < p * t := lt_of_lt_of_le j.isLt (Nat.le_mul_of_pos_right p ht)
        have := h1 ⟨j.val, hj⟩
        simpa [Nat.mod_eq_of_lt j.isLt] using this
    simp only at h
    rw [hcost _ (Nat.mul_pos hp ht) _ (fun i => rfl), hcost _ (Nat.mul_pos hp ht') _ (fun i => rfl),
      hcost _ (Nat.add_pos_left (Nat.mul_pos hp ht) (p * t')) _ hadd] at h
    rw [show p * t + p * t' = p * (t + t') by ring] at h
    rw [he'] at h
    exact h
  have hle : ∀ t, D t ≤ p * t := fun t => PEqualNP.Outside.L_meta_29745_aux.Fk_le _ _ _ _
  have hp1 : ∀ t, t ≤ p * t := fun t => Nat.le_mul_of_pos_left t hp
  obtain ⟨T, q, a, hq, hper⟩ : ∃ T q a : ℕ, 0 < q ∧ ∀ t ≥ T, D (t + q) = D t + a := by
    rcases PEqualNP.Outside.L_meta_29745_aux.core (PEqualNP.Outside.L_meta_29745_aux.EE mark edge)
      (start, ⟨0, hp⟩) (PEqualNP.Outside.L_meta_29745_aux.fn finish) hE hfin with
      ⟨N, hN⟩ | ⟨L, β, C0, C1, T, Q, A, hL, hQ, hall, ubM, lbM, hper, hLA⟩
    · refine ⟨N, 1, 0, Nat.one_pos, fun t ht => ?_⟩
      simp only [hD]
      rw [PEqualNP.Outside.L_meta_29745_aux.Fk_zero _ _ _ _ (hN _ (le_trans ht (hp1 t))),
        PEqualNP.Outside.L_meta_29745_aux.Fk_zero _ _ _ _ (hN _ (le_trans (by omega) (hp1 (t+1))))]
    · have hDeq : ∀ t, D t = p * t - PEqualNP.Outside.L_meta_29745_aux.Mx
          (PEqualNP.Outside.L_meta_29745_aux.EE mark edge) (start, ⟨0, hp⟩)
          (PEqualNP.Outside.L_meta_29745_aux.fn finish) (p * t) := fun t =>
        PEqualNP.Outside.L_meta_29745_aux.Fk_eq hE hfin _ (hall _)
      set M := PEqualNP.Outside.L_meta_29745_aux.Mx
          (PEqualNP.Outside.L_meta_29745_aux.EE mark edge) (start, ⟨0, hp⟩)
          (PEqualNP.Outside.L_meta_29745_aux.fn finish) with hM
      have iterM : ∀ n ≥ T, ∀ i, M (n + i * Q) = M n + i * A := by
        intro n hn i
        induction i with
        | zero => simp
        | succ i ih =>
          rw [show n + (i + 1) * Q = n + i * Q + Q by ring, hper _ (by nlinarith), ih]
          ring
      have hMp : ∀ t, T ≤ t → M (p * (t + Q)) = M (p * t) + p * A := by
        intro t ht
        have := iterM (p * t) (le_trans ht (hp1 t)) p
        rw [mul_add]
        exact this
      rcases lt_trichotomy β L with hβ | hβ | hβ
      · have hAQ : A < Q := by
          have : L * A < L * Q := by
            rw [hLA, mul_comm L Q]; exact Nat.mul_lt_mul_of_pos_left hβ hQ
          exact Nat.lt_of_mul_lt_mul_left this
        have hpA : p * A ≤ p * Q := Nat.mul_le_mul_left _ hAQ.le
        have hsmall : ∀ t, C0 + 1 ≤ t → M (p * t) < p * t := by
          intro t ht
          have h1 := ubM (p * t)
          have h2 : p * t * β + p * t ≤ p * t * L := by
            have := Nat.mul_le_mul_left (p * t) hβ
            linarith [this]
          have h3 := hp1 t
          have : L * M (p * t) < L * (p * t) := by nlinarith
          exact Nat.lt_of_mul_lt_mul_left this
        refine ⟨T + C0 + 1, Q, p * Q - p * A, hQ, fun t ht => ?_⟩
        rw [hDeq, hDeq, hMp t (by omega), show p * (t + Q) = p * t + p * Q by ring]
        have h1 := hsmall t (by omega)
        omega
      · subst hβ
        have hAQ : A = Q := by
          have : β * A = β * Q := by rw [hLA, mul_comm]
          exact Nat.eq_of_mul_eq_mul_left hL this
        refine ⟨T, Q, 0, hQ, fun t ht => ?_⟩
        rw [hDeq, hDeq, hMp t ht, show p * (t + Q) = p * t + p * Q by ring, hAQ]
        omega
      · have hbig : ∀ t, C1 + 1 ≤ t → p * t < M (p * t) := by
          intro t ht
          have h1 := lbM (p * t)
          have h2 : p * t * L + p * t ≤ p * t * β := by
            have := Nat.mul_le_mul_left (p * t) hβ
            linarith [this]
          have h3 := hp1 t
          have : L * (p * t) < L * M (p * t) := by nlinarith
          exact Nat.lt_of_mul_lt_mul_left this
        refine ⟨T + C1 + 1, Q, 0, hQ, fun t ht => ?_⟩
        rw [hDeq, hDeq]
        have h1 := hbig t (by omega)
        have h2 := hbig (t + Q) (by omega)
        omega
  obtain ⟨T', q', a', hT', hq', ha', hper', hbd⟩ :=
    PEqualNP.Outside.L_meta_29745_aux.final p e D hqa hle T q a hq hper
  refine ⟨T', q', a', hT', hq', ha', fun t ht => ?_, fun t ht => ?_⟩
  · rw [hdepth t (by omega), hdepth (t + q') (by omega)]
    exact hper' t ht
  · rw [hdepth t ht]
    exact hbd t ht

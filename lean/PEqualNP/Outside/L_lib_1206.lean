import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1206

open Finset
open scoped Classical

private def inDeg (E : Finset (Nat × Nat)) (u : Nat) : Nat :=
  (E.filter (fun e => e.2 = u)).card

private def outDeg (E : Finset (Nat × Nat)) (u : Nat) : Nat :=
  (E.filter (fun e => e.1 = u)).card

private def actFn {n k : Nat} (on : Fin k → Bool) (lit : Fin k → Fin n → Bool → Bool)
    (src : Nat → Option (Fin k ⊕ (Fin k × Fin n × Bool))) (u : Nat) : Bool :=
  (src u).elim true (Sum.elim on (fun p => lit p.1 p.2.1 p.2.2))

private def ValidV (m : Nat) (E : Finset (Nat × Nat)) (act : Nat → Bool)
    (v : Fin m → Bool) : Prop :=
  (∀ i : Fin m, act i.val = false → v i = false) ∧
  (∀ e ∈ E, ∀ (h1 : e.1 < m) (h2 : e.2 < m),
    act e.1 = true → act e.2 = true → v ⟨e.1, h1⟩ = true → v ⟨e.2, h2⟩ = true)

private def nbOf (m : Nat) (E : Finset (Nat × Nat)) (p : Fin m × Bool) :
    Finset (Fin m × Bool) :=
  match p.2 with
  | false =>
    insert (p.1, true)
      ((Finset.univ.filter (fun w : Fin m => (w.val, p.1.val) ∈ E)).image (fun w => (w, true)))
  | true =>
    insert (p.1, false)
      ((Finset.univ.filter (fun w : Fin m => (p.1.val, w.val) ∈ E)).image (fun w => (w, false)))

private lemma nbOf_opp {m : Nat} {E : Finset (Nat × Nat)} (p q : Fin m × Bool)
    (hq : q ∈ nbOf m E p) : p.2 ≠ q.2 := by
  rcases p with ⟨u, a⟩
  cases a <;> simp only [nbOf, mem_insert, mem_image, mem_filter, mem_univ, true_and] at hq
  · rcases hq with rfl | ⟨w, _, rfl⟩ <;> simp
  · rcases hq with rfl | ⟨w, _, rfl⟩ <;> simp

private lemma nbOf_not_mem {m : Nat} {E : Finset (Nat × Nat)} (p : Fin m × Bool) :
    p ∉ nbOf m E p := by
  intro hp
  exact nbOf_opp p p hp rfl

private lemma nbOf_self_pair {m : Nat} {E : Finset (Nat × Nat)} (i : Fin m) :
    (i, true) ∈ nbOf m E (i, false) := by
  simp [nbOf]

private lemma nbOf_symm {m : Nat} {E : Finset (Nat × Nat)} (p q : Fin m × Bool) :
    q ∈ nbOf m E p ↔ p ∈ nbOf m E q := by
  rcases p with ⟨u, a⟩
  rcases q with ⟨w, c⟩
  cases a <;> cases c <;> simp only [nbOf, mem_insert, mem_image, mem_filter, mem_univ, true_and,
    Prod.mk.injEq, and_true, and_false, Bool.false_eq_true, Bool.true_eq_false, exists_false,
    or_false, exists_eq_right]
  · exact ⟨fun h => h.elim (fun h1 => Or.inl h1.symm) Or.inr,
      fun h => h.elim (fun h1 => Or.inl h1.symm) Or.inr⟩
  · exact ⟨fun h => h.elim (fun h1 => Or.inl h1.symm) Or.inr,
      fun h => h.elim (fun h1 => Or.inl h1.symm) Or.inr⟩

private lemma nbOf_cross_edge {m : Nat} {E : Finset (Nat × Nat)}
    {i j : Fin m} {a c : Bool} (hij : i ≠ j) (h : (j, c) ∈ nbOf m E (i, a)) :
    (i.val, j.val) ∈ E ∨ (j.val, i.val) ∈ E := by
  cases a <;> cases c <;> simp only [nbOf, mem_insert, mem_image, mem_filter, mem_univ, true_and,
    Prod.mk.injEq, and_true, and_false, Bool.false_eq_true, Bool.true_eq_false, exists_false,
    or_false, exists_eq_right] at h
  · rcases h with hji | he
    · exact absurd hji.symm hij
    · exact Or.inr he
  · rcases h with hji | he
    · exact absurd hji.symm hij
    · exact Or.inl he

private lemma nbOf_card_le {m : Nat} {E : Finset (Nat × Nat)}
    (hdeg : ∀ u < m, inDeg E u ≤ 2 ∧ outDeg E u ≤ 2) (p : Fin m × Bool) :
    (nbOf m E p).card ≤ 3 := by
  rcases p with ⟨u, a⟩
  have hdu := hdeg u.val u.isLt
  cases a
  · dsimp only [nbOf]
    have h1 : (insert (u, true)
        ((Finset.univ.filter (fun w : Fin m => (w.val, u.val) ∈ E)).image
          (fun w => (w, true)))).card ≤
        ((Finset.univ.filter (fun w : Fin m => (w.val, u.val) ∈ E)).image
          (fun w => (w, true))).card + 1 := card_insert_le _ _
    have h2 : ((Finset.univ.filter (fun w : Fin m => (w.val, u.val) ∈ E)).image
        (fun w => (w, true))).card ≤
        (Finset.univ.filter (fun w : Fin m => (w.val, u.val) ∈ E)).card := card_image_le
    have h3 : (Finset.univ.filter (fun w : Fin m => (w.val, u.val) ∈ E)).card ≤
        inDeg E u.val := by
      unfold inDeg
      apply card_le_card_of_injOn (fun w : Fin m => (w.val, u.val))
      · intro w hw
        simp only [mem_coe, mem_filter, mem_univ, true_and] at hw ⊢
        exact ⟨hw, trivial⟩
      · intro w1 _ w2 _ heq
        simp only [Prod.mk.injEq] at heq
        exact Fin.ext heq.1
    omega
  · dsimp only [nbOf]
    have h1 : (insert (u, false)
        ((Finset.univ.filter (fun w : Fin m => (u.val, w.val) ∈ E)).image
          (fun w => (w, false)))).card ≤
        ((Finset.univ.filter (fun w : Fin m => (u.val, w.val) ∈ E)).image
          (fun w => (w, false))).card + 1 := card_insert_le _ _
    have h2 : ((Finset.univ.filter (fun w : Fin m => (u.val, w.val) ∈ E)).image
        (fun w => (w, false))).card ≤
        (Finset.univ.filter (fun w : Fin m => (u.val, w.val) ∈ E)).card := card_image_le
    have h3 : (Finset.univ.filter (fun w : Fin m => (u.val, w.val) ∈ E)).card ≤
        outDeg E u.val := by
      unfold outDeg
      apply card_le_card_of_injOn (fun w : Fin m => (u.val, w.val))
      · intro w hw
        simp only [mem_coe, mem_filter, mem_univ, true_and] at hw ⊢
        exact ⟨hw, trivial⟩
      · intro w1 _ w2 _ heq
        simp only [Prod.mk.injEq] at heq
        exact Fin.ext heq.2
    omega

private def xOf {m : Nat} (act : Nat → Bool) (v : Fin m → Bool) : (Fin m × Bool) → Bool
  | (i, false) => if act i.val then v i else true
  | (i, true) => if act i.val then !(v i) else true

private def vOf {m : Nat} (act : Nat → Bool) (x : (Fin m × Bool) → Bool) (i : Fin m) : Bool :=
  if act i.val then x (i, false) else false

private lemma card_validX_eq_card_validV (m : Nat) (E : Finset (Nat × Nat)) (act : Nat → Bool) :
      ((Finset.univ : Finset ((Fin m × Bool) → Bool)).filter (fun x =>
      (∀ p, ∀ q ∈ nbOf m E p, x p = true ∨ x q = true) ∧
      ∀ i, xor (x (i, false)) (x (i, true)) = act i.val)).card =
    ((Finset.univ : Finset (Fin m → Bool)).filter (ValidV m E act)).card := by
  apply Finset.card_bij'
    (fun x _ => vOf act x)
    (fun v _ => xOf act v)
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    rcases hx with ⟨hcov, hxor⟩
    refine ⟨?_, ?_⟩
    · intro i hi
      simp [vOf, hi]
    · intro e he h1 h2 ha1 ha2 hv1
      have hq : (⟨e.2, h2⟩, false) ∈ nbOf m E (⟨e.1, h1⟩, true) := by
        simp only [nbOf, mem_insert, mem_image, mem_filter, mem_univ, true_and]
        exact Or.inr ⟨⟨e.2, h2⟩, he, rfl⟩
      have hor := hcov (⟨e.1, h1⟩, true) (⟨e.2, h2⟩, false) hq
      have hx1 := hxor ⟨e.1, h1⟩
      simp only [vOf, ha1, ↓reduceIte] at hv1
      simp only [vOf, ha2, ↓reduceIte]
      rw [hv1, ha1] at hx1
      cases hxt : x (⟨e.1, h1⟩, true)
      · rw [hxt] at hor
        exact hor.resolve_left Bool.false_ne_true
      · rw [hxt] at hx1
        simp at hx1
  · intro v hv
    simp only [mem_filter, mem_univ, true_and] at hv ⊢
    rcases hv with ⟨hzero, himp⟩
    refine ⟨?_, ?_⟩
    · intro p q hq
      rcases p with ⟨u, a⟩
      cases a
      · simp only [nbOf, mem_insert, mem_image, mem_filter, mem_univ, true_and] at hq
        rcases hq with rfl | ⟨w, hw, rfl⟩
        · simp only [xOf]
          cases ha : act u.val
          · left; rfl
          · cases v u <;> simp
        · simp only [xOf]
          cases hau : act u.val
          · left; rfl
          · cases haw : act w.val
            · right; rfl
            · cases hvw : v w
              · right; rfl
              · left
                exact himp (w.val, u.val) hw w.isLt u.isLt haw hau hvw
      · simp only [nbOf, mem_insert, mem_image, mem_filter, mem_univ, true_and] at hq
        rcases hq with rfl | ⟨w, hw, rfl⟩
        · simp only [xOf]
          cases ha : act u.val
          · left; rfl
          · cases v u <;> simp
        · simp only [xOf]
          cases hau : act u.val
          · left; rfl
          · cases haw : act w.val
            · right; rfl
            · cases hvu : v u
              · left; rfl
              · right
                exact himp (u.val, w.val) hw u.isLt w.isLt hau haw hvu
    · intro i
      simp only [xOf]
      cases ha : act i.val
      · rfl
      · cases v i <;> rfl
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    rcases hx with ⟨hcov, hxor⟩
    funext p
    rcases p with ⟨i, a⟩
    have hor := hcov (i, false) (i, true) (nbOf_self_pair i)
    have hxi := hxor i
    cases ha : act i.val
    · rw [ha] at hxi
      cases hxf : x (i, false) <;> cases hxt : x (i, true)
      · rw [hxf, hxt] at hor; cases hor <;> contradiction
      · rw [hxf, hxt] at hxi; contradiction
      · rw [hxf, hxt] at hxi; contradiction
      · cases a <;> simp [xOf, ha, hxf, hxt]
    · rw [ha] at hxi
      cases hxf : x (i, false) <;> cases hxt : x (i, true)
      · rw [hxf, hxt] at hxi; contradiction
      · cases a <;> simp [xOf, vOf, ha, hxf, hxt]
      · cases a <;> simp [xOf, vOf, ha, hxf, hxt]
      · rw [hxf, hxt] at hxi; contradiction
  · intro v hv
    simp only [mem_filter, mem_univ, true_and] at hv
    funext i
    simp only [vOf, xOf]
    cases ha : act i.val
    · simp [hv.1 i ha]
    · simp

private lemma mod_eq_of_sum_mod {α : Type*} (s : Finset α) (f g : α → Nat) (M : Nat)
    (h : ∀ x ∈ s, f x % M = g x % M) :
    (∑ x ∈ s, f x) % M = (∑ x ∈ s, g x) % M := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have h1 := h a (mem_insert_self a s)
    have h2 := ih (fun x hx => h x (mem_insert_of_mem hx))
    rw [Nat.add_mod, h1, h2, ← Nat.add_mod]

private lemma sum_lt_pow (B : Nat) (hB : 0 < B) (c : Nat → Nat) (j : Nat)
    (hc : ∀ v < j, c v < B) :
    ∑ v ∈ Finset.range j, c v * B ^ v < B ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ]
    have hprev := ih (fun v hv => hc v (by omega))
    have hcj : c j < B := hc j (by omega)
    have hstep : (c j + 1) * B ^ j ≤ B * B ^ j := Nat.mul_le_mul_right (B ^ j) hcj
    have hpow : B * B ^ j = B ^ (j + 1) := by rw [pow_succ, Nat.mul_comm]
    have hmul : c j * B ^ j + B ^ j = (c j + 1) * B ^ j := by
      rw [Nat.add_mul, Nat.one_mul]
    omega

private lemma sum_tail_dvd (B : Nat) (c : Nat → Nat) (j t : Nat) :
    B ^ (j + 1) ∣ ∑ v ∈ Finset.range t, c (j + 1 + v) * B ^ (j + 1 + v) := by
  apply Finset.dvd_sum
  intro v _
  rw [pow_add B (j + 1) v]
  exact dvd_mul_of_dvd_right (dvd_mul_right (B ^ (j + 1)) (B ^ v)) (c (j + 1 + v))

private lemma div_pow_mod_base (B : Nat) (hB : 0 < B) (c : Nat → Nat) (M j : Nat)
    (hj : j < M) (hc : ∀ v < M, c v < B) :
    ((∑ v ∈ Finset.range M, c v * B ^ v) / B ^ j) % B = c j := by
  have hM : M = (j + 1) + (M - (j + 1)) := by omega
  have hsplit : ∑ v ∈ Finset.range M, c v * B ^ v =
      (∑ v ∈ Finset.range j, c v * B ^ v) + c j * B ^ j +
      ∑ v ∈ Finset.range (M - (j + 1)), c (j + 1 + v) * B ^ (j + 1 + v) := by
    conv_lhs => rw [hM]
    rw [Finset.sum_range_add, Finset.sum_range_succ]
  rw [hsplit]
  obtain ⟨q, hq⟩ := sum_tail_dvd B c j (M - (j + 1))
  rw [hq]
  have hlow : ∑ v ∈ Finset.range j, c v * B ^ v < B ^ j :=
    sum_lt_pow B hB c j (fun v hv => hc v (by omega))
  have hre : (∑ v ∈ Finset.range j, c v * B ^ v) + c j * B ^ j + B ^ (j + 1) * q =
      (∑ v ∈ Finset.range j, c v * B ^ v) + (c j + B * q) * B ^ j := by
    rw [pow_succ]
    have : B ^ j * B * q = B * q * B ^ j := by
      rw [Nat.mul_assoc, Nat.mul_comm (B ^ j)]
    rw [Nat.add_mul, this, Nat.add_assoc]
  rw [hre, Nat.add_mul_div_right _ _ (Nat.pow_pos hB), Nat.div_eq_of_lt hlow, Nat.zero_add]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hc j hj)]

private lemma div_pow_mod_eq_mod_div (B : Nat) (hB : 0 < B) (N j : Nat) :
    (N / B ^ j) % B = (N % B ^ (j + 1)) / B ^ j := by
  have hbj : 0 < B ^ j := Nat.pow_pos hB
  have h1 : N = N % B ^ (j + 1) + (B * (N / B ^ (j + 1))) * B ^ j := by
    have hdiv := Nat.mod_add_div N (B ^ (j + 1))
    have hre : B ^ (j + 1) * (N / B ^ (j + 1)) = (B * (N / B ^ (j + 1))) * B ^ j := by
      rw [pow_succ, Nat.mul_assoc, Nat.mul_comm (B ^ j)]
    omega
  conv_lhs => rw [h1]
  rw [Nat.add_mul_div_right _ _ hbj, Nat.add_mul_mod_self_left]
  have hlt : N % B ^ (j + 1) / B ^ j < B := by
    apply Nat.div_lt_of_lt_mul
    rw [← pow_succ]
    exact Nat.mod_lt N (Nat.pow_pos hB)
  exact Nat.mod_eq_of_lt hlt

private lemma div_pow_mod_of_mod_pow (B : Nat) (hB : 0 < B) (Z S h j : Nat)
    (hj : j < h) (hmod : Z % B ^ h = S % B ^ h) :
    (Z / B ^ j) % B = (S / B ^ j) % B := by
  rw [div_pow_mod_eq_mod_div B hB Z j, div_pow_mod_eq_mod_div B hB S j]
  have hdvd : B ^ (j + 1) ∣ B ^ h := Nat.pow_dvd_pow B (by omega)
  have hz : Z % B ^ (j + 1) = (Z % B ^ h) % B ^ (j + 1) := (Nat.mod_mod_of_dvd Z hdvd).symm
  have hs : S % B ^ (j + 1) = (S % B ^ h) % B ^ (j + 1) := (Nat.mod_mod_of_dvd S hdvd).symm
  rw [hz, hmod, ← hs]

private lemma sum_pow_eq_sum_card {α : Type*} [Fintype α] (B M : Nat) (f : α → Nat)
    (hf : ∀ y : α, f y < M) :
      ∑ y : α, B ^ f y =
      ∑ v ∈ Finset.range M, ((Finset.univ : Finset α).filter (fun y => f y = v)).card * B ^ v := by
  have h1 : ∀ y : α, B ^ f y = ∑ v ∈ Finset.range M, if f y = v then B ^ v else 0 := by
    intro y
    rw [Finset.sum_ite_eq (Finset.range M) (f y) (fun v => B ^ v)]
    simp [Finset.mem_range.mpr (hf y)]
  calc
    ∑ y : α, B ^ f y
        = ∑ y : α, ∑ v ∈ Finset.range M, if f y = v then B ^ v else 0 := by
            apply Finset.sum_congr rfl
            intro y _
            exact h1 y
    _ = ∑ v ∈ Finset.range M, ∑ y : α, if f y = v then B ^ v else 0 := Finset.sum_comm
    _ = ∑ v ∈ Finset.range M,
          ((Finset.univ : Finset α).filter (fun y => f y = v)).card * B ^ v := by
            apply Finset.sum_congr rfl
            intro v _
            rw [← smul_eq_mul, ← Finset.sum_const, Finset.sum_filter]

private structure GState (n k : Nat) where
  m : Nat
  edges : Finset (Nat × Nat)
  source : Nat → Option (Fin k ⊕ (Fin k × Fin n × Bool))
  bags : List (Finset Nat)

private structure WellFormed (n k : Nat) (st : GState n k) : Prop where
  edges_lt : ∀ e ∈ st.edges, e.1 < st.m ∧ e.2 < st.m ∧ e.1 ≠ e.2
  deg_le : ∀ u < st.m, inDeg st.edges u ≤ 2 ∧ outDeg st.edges u ≤ 2
  bags_ne : st.bags ≠ []
  bags_len : st.bags.length ≤ st.m + 1
  bags_card : ∀ b ∈ st.bags, b.card ≤ n + 9
  bags_lt : ∀ b ∈ st.bags, ∀ u ∈ b, u < st.m
  bags_cov : ∀ u < st.m, ∃ b ∈ st.bags, u ∈ b
  bags_edge : ∀ e ∈ st.edges, ∃ b ∈ st.bags, e.1 ∈ b ∧ e.2 ∈ b
  bags_inter : ∀ u (s t w : Nat)
    (hs : s < st.bags.length) (ht : t < st.bags.length) (hw : w < st.bags.length),
    s ≤ t → t ≤ w → u ∈ st.bags[s] → u ∈ st.bags[w] → u ∈ st.bags[t]

private lemma inDeg_union_of_disjoint {E1 E2 : Finset (Nat × Nat)} (hd : Disjoint E1 E2) (u : Nat) :
    inDeg (E1 ∪ E2) u = inDeg E1 u + inDeg E2 u := by
  unfold inDeg
  rw [Finset.filter_union]
  exact Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hd)

private lemma outDeg_union_of_disjoint {E1 E2 : Finset (Nat × Nat)} (hd : Disjoint E1 E2) (u : Nat) :
    outDeg (E1 ∪ E2) u = outDeg E1 u + outDeg E2 u := by
  unfold outDeg
  rw [Finset.filter_union]
  exact Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hd)

private lemma inDeg_eq_zero_of_ge {E : Finset (Nat × Nat)} {m u : Nat}
    (hlt : ∀ e ∈ E, e.1 < m ∧ e.2 < m ∧ e.1 ≠ e.2) (hu : m ≤ u) :
    inDeg E u = 0 := by
  unfold inDeg
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro e he
  have h := (hlt e he).2.1
  omega

private lemma outDeg_eq_zero_of_ge {E : Finset (Nat × Nat)} {m u : Nat}
    (hlt : ∀ e ∈ E, e.1 < m ∧ e.2 < m ∧ e.1 ≠ e.2) (hu : m ≤ u) :
    outDeg E u = 0 := by
  unfold outDeg
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro e he
  have h := (hlt e he).1
  omega

private lemma extend_wellFormed {n k : Nat} (st : GState n k) (hwf : WellFormed n k st)
    (Δ : Nat) (hΔ : 1 ≤ Δ) (newE : Finset (Nat × Nat))
    (newSrc : Nat → Option (Fin k ⊕ (Fin k × Fin n × Bool))) (newBag : Finset Nat)
    (hnewE_lt : ∀ e ∈ newE, e.1 < st.m + Δ ∧ e.2 < st.m + Δ ∧ e.1 ≠ e.2)
    (hnewE_fresh : ∀ e ∈ newE, st.m ≤ e.1 ∨ st.m ≤ e.2)
    (hdeg_old : ∀ u < st.m, inDeg st.edges u + inDeg newE u ≤ 2 ∧
      outDeg st.edges u + outDeg newE u ≤ 2)
    (hdeg_new : ∀ u, st.m ≤ u → u < st.m + Δ → inDeg newE u ≤ 2 ∧ outDeg newE u ≤ 2)
    (hbag_card : newBag.card ≤ n + 9)
    (hbag_lt : ∀ u ∈ newBag, u < st.m + Δ)
    (hbag_cov : ∀ u, st.m ≤ u → u < st.m + Δ → u ∈ newBag)
    (hbag_last : ∀ u ∈ newBag, u < st.m → u ∈ st.bags.getLast hwf.bags_ne)
    (hbag_edge : ∀ e ∈ newE, e.1 ∈ newBag ∧ e.2 ∈ newBag) :
    WellFormed n k ⟨st.m + Δ, st.edges ∪ newE, newSrc, st.bags ++ [newBag]⟩ := by
  have hdisj : Disjoint st.edges newE := by
    rw [Finset.disjoint_left]
    intro e he1 he2
    have hlt := hwf.edges_lt e he1
    have hfr := hnewE_fresh e he2
    omega
  refine
    { edges_lt := ?_
      deg_le := ?_
      bags_ne := by simp
      bags_len := ?_
      bags_card := ?_
      bags_lt := ?_
      bags_cov := ?_
      bags_edge := ?_
      bags_inter := ?_ }
  · intro e he
    dsimp only at he ⊢
    rcases Finset.mem_union.mp he with he1 | he2
    · rcases hwf.edges_lt e he1 with ⟨h1, h2, h3⟩
      exact ⟨by omega, by omega, h3⟩
    · exact hnewE_lt e he2
  · intro u hu
    dsimp only at hu ⊢
    rw [inDeg_union_of_disjoint hdisj u, outDeg_union_of_disjoint hdisj u]
    by_cases hlt : u < st.m
    · exact hdeg_old u hlt
    · have hge : st.m ≤ u := by omega
      rw [inDeg_eq_zero_of_ge hwf.edges_lt hge, outDeg_eq_zero_of_ge hwf.edges_lt hge,
        Nat.zero_add, Nat.zero_add]
      exact hdeg_new u hge hu
  · dsimp only
    simp only [List.length_append, List.length_singleton]
    have := hwf.bags_len
    omega
  · intro b hb
    dsimp only at hb
    simp only [List.mem_append, List.mem_singleton] at hb
    rcases hb with hb1 | rfl
    · exact hwf.bags_card b hb1
    · exact hbag_card
  · intro b hb u hu
    dsimp only at hb ⊢
    simp only [List.mem_append, List.mem_singleton] at hb
    rcases hb with hb1 | rfl
    · have := hwf.bags_lt b hb1 u hu
      omega
    · exact hbag_lt u hu
  · intro u hu
    dsimp only at hu ⊢
    by_cases hlt : u < st.m
    · obtain ⟨b, hb, hub⟩ := hwf.bags_cov u hlt
      exact ⟨b, List.mem_append_left _ hb, hub⟩
    · exact ⟨newBag, List.mem_append_right _ (List.mem_singleton_self _), hbag_cov u (by omega) hu⟩
  · intro e he
    dsimp only at he ⊢
    rcases Finset.mem_union.mp he with he1 | he2
    · obtain ⟨b, hb, h1, h2⟩ := hwf.bags_edge e he1
      exact ⟨b, List.mem_append_left _ hb, h1, h2⟩
    · exact ⟨newBag, List.mem_append_right _ (List.mem_singleton_self _), hbag_edge e he2⟩
  · intro u s t w hs ht hw hst htw hus huw
    dsimp only at hs ht hw hus huw ⊢
    have hlen : (st.bags ++ [newBag]).length = st.bags.length + 1 := by simp
    by_cases hwl : w < st.bags.length
    · have hsl : s < st.bags.length := by omega
      have htl : t < st.bags.length := by omega
      rw [List.getElem_append_left hsl] at hus
      rw [List.getElem_append_left hwl] at huw
      rw [List.getElem_append_left htl]
      exact hwf.bags_inter u s t w hsl htl hwl hst htw hus huw
    · have hw_eq : w = st.bags.length := by omega
      by_cases htl : t < st.bags.length
      · have hsl : s < st.bags.length := by omega
        rw [List.getElem_append_left hsl] at hus
        have huw' : u ∈ newBag := by
          subst hw_eq
          simpa [List.getElem_append_right (Nat.le_refl st.bags.length)] using huw
        have hult : u < st.m := hwf.bags_lt _ (List.getElem_mem hsl) u hus
        have hulast : u ∈ st.bags.getLast hwf.bags_ne := hbag_last u huw' hult
        have hpos : 0 < st.bags.length := List.length_pos_of_ne_nil hwf.bags_ne
        have hlast_idx : st.bags.length - 1 < st.bags.length := by omega
        have hulast' : u ∈ st.bags[st.bags.length - 1] := by
          rwa [List.getLast_eq_getElem] at hulast
        rw [List.getElem_append_left htl]
        exact hwf.bags_inter u s t (st.bags.length - 1) hsl htl hlast_idx hst (by omega) hus hulast'
      · have ht_eq : t = w := by omega
        subst ht_eq
        exact huw

private def joinV {m Δ : Nat} (v1 : Fin m → Bool) (v2 : Fin Δ → Bool)
    (i : Fin (m + Δ)) : Bool :=
  if h : i.val < m then v1 ⟨i.val, h⟩ else v2 ⟨i.val - m, by omega⟩

private lemma joinV_lt {m Δ : Nat} (v1 : Fin m → Bool) (v2 : Fin Δ → Bool)
    (u : Nat) (h1 : u < m) (h2 : u < m + Δ) :
    joinV v1 v2 ⟨u, h2⟩ = v1 ⟨u, h1⟩ := by
  simp [joinV, h1]

private lemma joinV_ge {m Δ : Nat} (v1 : Fin m → Bool) (v2 : Fin Δ → Bool)
    (j : Fin Δ) (h2 : m + j.val < m + Δ) :
    joinV v1 v2 ⟨m + j.val, h2⟩ = v2 j := by
  have hn : ¬ (m + j.val < m) := by omega
  simp [joinV, hn]

private lemma joinV_m {m Δ : Nat} [NeZero Δ] (v1 : Fin m → Bool) (v2 : Fin Δ → Bool)
    (h2 : m < m + Δ) :
    joinV v1 v2 ⟨m, h2⟩ = v2 0 := by
  have hn : ¬ (m < m) := by omega
  simp [joinV, hn]

private lemma joinV_nat {m Δ : Nat} (v1 : Fin m → Bool) (v2 : Fin Δ → Bool)
    (k : Nat) (j : Fin Δ) (hk : j.val = k) (h2 : m + k < m + Δ) :
    joinV v1 v2 ⟨m + k, h2⟩ = v2 j := by
  subst hk
  exact joinV_ge v1 v2 j h2

private lemma stepImp {m Δ : Nat} {newE : Finset (Nat × Nat)} {act' : Nat → Bool}
    {v1 : Fin m → Bool} {v2 : Fin Δ → Bool}
    (himp : ∀ e ∈ newE, ∀ (h1 : e.1 < m + Δ) (h2 : e.2 < m + Δ),
      act' e.1 = true → act' e.2 = true →
      joinV v1 v2 ⟨e.1, h1⟩ = true → joinV v1 v2 ⟨e.2, h2⟩ = true)
    {a b : Nat} (he : (a, b) ∈ newE) (h1 : a < m + Δ) (h2 : b < m + Δ)
    (ha1 : act' a = true) (ha2 : act' b = true)
    (hv : joinV v1 v2 ⟨a, h1⟩ = true) : joinV v1 v2 ⟨b, h2⟩ = true :=
  himp (a, b) he h1 h2 ha1 ha2 hv

private def StepValid (m Δ : Nat) (newE : Finset (Nat × Nat)) (act' : Nat → Bool)
    (v1 : Fin m → Bool) (v2 : Fin Δ → Bool) : Prop :=
  (∀ j : Fin Δ, act' (m + j.val) = false → v2 j = false) ∧
  (∀ e ∈ newE, ∀ (h1 : e.1 < m + Δ) (h2 : e.2 < m + Δ),
    act' e.1 = true → act' e.2 = true →
    joinV v1 v2 ⟨e.1, h1⟩ = true → joinV v1 v2 ⟨e.2, h2⟩ = true)

private lemma validV_join_iff (m Δ : Nat) (E newE : Finset (Nat × Nat)) (act act' : Nat → Bool)
    (hE_lt : ∀ e ∈ E, e.1 < m ∧ e.2 < m ∧ e.1 ≠ e.2)
    (hact : ∀ u < m, act' u = act u)
    (v1 : Fin m → Bool) (v2 : Fin Δ → Bool) :
    ValidV (m + Δ) (E ∪ newE) act' (joinV v1 v2) ↔
      ValidV m E act v1 ∧ StepValid m Δ newE act' v1 v2 := by
  constructor
  · intro ⟨hzero, himp⟩
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · intro i hi
      have h := hzero ⟨i.val, by omega⟩ (by rw [hact i.val i.isLt]; exact hi)
      rwa [joinV_lt v1 v2 i.val i.isLt] at h
    · intro e he h1 h2 ha1 ha2 hv1
      have h := himp e (Finset.mem_union_left _ he) (by omega) (by omega)
        (by rw [hact e.1 h1]; exact ha1) (by rw [hact e.2 h2]; exact ha2)
        (by rw [joinV_lt v1 v2 e.1 h1]; exact hv1)
      rwa [joinV_lt v1 v2 e.2 h2] at h
    · intro j hj
      have h := hzero ⟨m + j.val, by omega⟩ hj
      rwa [joinV_ge v1 v2 j] at h
    · intro e he h1 h2 ha1 ha2 hv1
      exact himp e (Finset.mem_union_right _ he) h1 h2 ha1 ha2 hv1
  · intro ⟨⟨hzero1, himp1⟩, ⟨hzero2, himp2⟩⟩
    refine ⟨?_, ?_⟩
    · intro i hi
      by_cases hlt : i.val < m
      · rw [joinV_lt v1 v2 i.val hlt i.isLt]
        exact hzero1 ⟨i.val, hlt⟩ (by rw [← hact i.val hlt]; exact hi)
      · have hj : i.val - m < Δ := by omega
        have heq : i = ⟨m + (⟨i.val - m, hj⟩ : Fin Δ).val, by omega⟩ := by
          ext; dsimp; omega
        rw [heq, joinV_ge]
        have hm_eq : m + (i.val - m) = i.val := by omega
        exact hzero2 ⟨i.val - m, hj⟩ (by dsimp only; rw [hm_eq]; exact hi)
    · intro e he h1 h2 ha1 ha2 hv1
      rcases Finset.mem_union.mp he with he1 | he2
      · have hlt := hE_lt e he1
        rw [joinV_lt v1 v2 e.1 hlt.1 h1] at hv1
        rw [joinV_lt v1 v2 e.2 hlt.2.1 h2]
        exact himp1 e he1 hlt.1 hlt.2.1 (by rw [← hact e.1 hlt.1]; exact ha1)
          (by rw [← hact e.2 hlt.2.1]; exact ha2) hv1
      · exact himp2 e he2 h1 h2 ha1 ha2 hv1

private lemma card_extend_mul (m Δ : Nat) (E newE : Finset (Nat × Nat)) (act act' : Nat → Bool)
    (hE_lt : ∀ e ∈ E, e.1 < m ∧ e.2 < m ∧ e.1 ≠ e.2)
    (hact : ∀ u < m, act' u = act u)
    (P : (Fin m → Bool) → Prop) [DecidablePred P]
    (Q : (Fin (m + Δ) → Bool) → Prop) [DecidablePred Q] (K : Nat)
    (hproj : ∀ v1 v2, ValidV m E act v1 → StepValid m Δ newE act' v1 v2 →
      Q (joinV v1 v2) → P v1)
    (hfiber : ∀ v1, ValidV m E act v1 → P v1 →
          ((Finset.univ : Finset (Fin Δ → Bool)).filter
        (fun v2 => StepValid m Δ newE act' v1 v2 ∧ Q (joinV v1 v2))).card = K) :
      ((Finset.univ : Finset (Fin (m + Δ) → Bool)).filter
      (fun v => ValidV (m + Δ) (E ∪ newE) act' v ∧ Q v)).card =
    ((Finset.univ : Finset (Fin m → Bool)).filter (fun v1 => ValidV m E act v1 ∧ P v1)).card * K := by
  let s1 := (Finset.univ : Finset (Fin m → Bool)).filter (fun v1 => ValidV m E act v1 ∧ P v1)
  let t := fun v1 : Fin m → Bool =>
    (Finset.univ : Finset (Fin Δ → Bool)).filter
      (fun v2 => StepValid m Δ newE act' v1 v2 ∧ Q (joinV v1 v2))
  have hbij :
      ((Finset.univ : Finset (Fin (m + Δ) → Bool)).filter
        (fun v => ValidV (m + Δ) (E ∪ newE) act' v ∧ Q v)).card =
      (s1.sigma t).card := by
    refine Finset.card_bij'
      (fun v _ => Sigma.mk (fun i : Fin m => v ⟨i.val, by omega⟩)
        (fun j : Fin Δ => v ⟨m + j.val, by omega⟩))
      (fun p _ => joinV p.1 p.2) ?_ ?_ ?_ ?_
    · intro v hv
      simp only [mem_filter, mem_univ, true_and] at hv
      have hjoin : joinV (fun i : Fin m => v ⟨i.val, by omega⟩)
          (fun j : Fin Δ => v ⟨m + j.val, by omega⟩) = v := by
        funext i
        by_cases hlt : i.val < m
        · simp [joinV, hlt]
        · have heq : m + (i.val - m) = i.val := by omega
          simp [joinV, hlt, heq]
      rw [← hjoin] at hv
      have hval := (validV_join_iff m Δ E newE act act' hE_lt hact _ _).mp hv.1
      have hp := hproj _ _ hval.1 hval.2 hv.2
      simp only [s1, t, mem_sigma, mem_filter, mem_univ, true_and]
      exact ⟨⟨hval.1, hp⟩, ⟨hval.2, hv.2⟩⟩
    · intro p hp
      simp only [s1, t, mem_sigma, mem_filter, mem_univ, true_and] at hp
      simp only [mem_filter, mem_univ, true_and]
      exact ⟨(validV_join_iff m Δ E newE act act' hE_lt hact p.1 p.2).mpr ⟨hp.1.1, hp.2.1⟩, hp.2.2⟩
    · intro v _
      funext i
      by_cases hlt : i.val < m
      · simp [joinV, hlt]
      · have heq : m + (i.val - m) = i.val := by omega
        simp [joinV, hlt, heq]
    · intro p _
      rcases p with ⟨v1, v2⟩
      apply Sigma.ext
      · funext i
        exact joinV_lt v1 v2 i.val i.isLt (by omega)
      · apply heq_of_eq
        funext j
        exact joinV_ge v1 v2 j (by omega)
  rw [hbij, Finset.card_sigma]
  have hsum : ∑ v1 ∈ s1, (t v1).card = ∑ _v1 ∈ s1, K := by
    apply Finset.sum_congr rfl
    intro v1 hv1
    simp only [s1, mem_filter, mem_univ, true_and] at hv1
    exact hfiber v1 hv1.1 hv1.2
  rw [hsum, Finset.sum_const, smul_eq_mul]

private lemma card_filter_unique {Δ : Nat} (p : (Fin Δ → Bool) → Prop) [DecidablePred p]
    (target : Fin Δ → Bool) (R : Prop)
    (h : ∀ v, p v ↔ v = target ∧ R) :
      ((Finset.univ : Finset (Fin Δ → Bool)).filter p).card = if R then 1 else 0 := by
  by_cases hR : R
  · simp only [hR, ↓reduceIte]
    have hset : (Finset.univ : Finset (Fin Δ → Bool)).filter p = {target} := by
      ext v
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      rw [h v]
      exact ⟨fun h1 => h1.1, fun h1 => ⟨h1, hR⟩⟩
    rw [hset, Finset.card_singleton]
  · simp only [hR, ↓reduceIte]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro v _ hv
    exact hR ((h v).mp hv).2

private lemma card_filter_fin1 (p : (Fin 1 → Bool) → Prop) [DecidablePred p] :
      ((Finset.univ : Finset (Fin 1 → Bool)).filter p).card =
      (if p (fun _ => false) then 1 else 0) + (if p (fun _ => true) then 1 else 0) := by
  have hbij : ((Finset.univ : Finset (Fin 1 → Bool)).filter p).card =
      ((Finset.univ : Finset Bool).filter (fun b => p (fun _ => b))).card := by
    refine Finset.card_bij' (fun v _ => v 0) (fun b _ => fun _ => b) ?_ ?_ ?_ ?_
    · intro v hv
      simp only [mem_filter, mem_univ, true_and] at hv ⊢
      have heq : (fun _ : Fin 1 => v 0) = v := by
        funext i
        have : i = 0 := Fin.ext (by omega)
        subst this
        rfl
      rwa [heq]
    · intro b hb
      simpa using hb
    · intro v _
      funext i
      have : i = 0 := Fin.ext (by omega)
      subst this
      rfl
    · intro b _; rfl
  rw [hbij]
  have huniv : (Finset.univ : Finset Bool) = {false, true} := by ext b; cases b <;> simp
  rw [huniv, Finset.filter_insert, Finset.filter_singleton]
  by_cases hf : p (fun _ => false) <;> by_cases ht : p (fun _ => true) <;>
    simp [hf, ht]

private lemma card_filter_fin5_last (p : (Fin 5 → Bool) → Prop) [DecidablePred p]
    (a0 a1 a2 a3 : Bool)
    (Q : Bool → Prop)
    (h : ∀ v, p v ↔ v 0 = a0 ∧ v 1 = a1 ∧ v 2 = a2 ∧ v 3 = a3 ∧ Q (v 4)) :
      ((Finset.univ : Finset (Fin 5 → Bool)).filter p).card =
      (if Q false then 1 else 0) + (if Q true then 1 else 0) := by
  let mk5 : Bool → Fin 5 → Bool := fun b i =>
    match i.val with
    | 0 => a0
    | 1 => a1
    | 2 => a2
    | 3 => a3
    | _ => b
  have hbij : ((Finset.univ : Finset (Fin 5 → Bool)).filter p).card =
      ((Finset.univ : Finset Bool).filter Q).card := by
    refine Finset.card_bij' (fun v _ => v 4) (fun b _ => mk5 b) ?_ ?_ ?_ ?_
    · intro v hv
      simp only [mem_filter, mem_univ, true_and] at hv ⊢
      exact ((h v).mp hv).2.2.2.2
    · intro b hb
      simp only [mem_filter, mem_univ, true_and] at hb ⊢
      rw [h]
      exact ⟨rfl, rfl, rfl, rfl, hb⟩
    · intro v hv
      simp only [mem_filter, mem_univ, true_and] at hv
      have h0 := (h v).mp hv
      funext i
      rcases i with ⟨iv, hiv⟩
      match iv, hiv with
      | 0, _ => exact h0.1.symm
      | 1, _ => exact h0.2.1.symm
      | 2, _ => exact h0.2.2.1.symm
      | 3, _ => exact h0.2.2.2.1.symm
      | 4, _ => rfl
    · intro b _; rfl
  rw [hbij]
  have huniv : (Finset.univ : Finset Bool) = {false, true} := by ext b; cases b <;> simp
  rw [huniv, Finset.filter_insert, Finset.filter_singleton]
  by_cases hf : Q false <;> by_cases ht : Q true <;> simp [hf, ht]

private lemma card_split_bool {m : Nat} (P : (Fin m → Bool) → Prop) [DecidablePred P] (u : Fin m) :
      ((Finset.univ : Finset (Fin m → Bool)).filter P).card =
      ((Finset.univ : Finset (Fin m → Bool)).filter (fun v => P v ∧ v u = false)).card +
      ((Finset.univ : Finset (Fin m → Bool)).filter (fun v => P v ∧ v u = true)).card := by
  have hdisj : Disjoint
      ((Finset.univ : Finset (Fin m → Bool)).filter (fun v => P v ∧ v u = false))
      ((Finset.univ : Finset (Fin m → Bool)).filter (fun v => P v ∧ v u = true)) := by
    rw [Finset.disjoint_left]
    intro v h1 h2
    simp only [mem_filter, mem_univ, true_and] at h1 h2
    rw [h1.2] at h2
    exact Bool.false_ne_true h2.2
  rw [← Finset.card_union_of_disjoint hdisj]
  congr 1
  ext v
  simp only [mem_filter, mem_univ, true_and, mem_union]
  cases hvu : v u <;> simp

private lemma card_sum_obsX {n m : Nat} (P : (Fin m → Bool) → Prop) [DecidablePred P]
    (xCur : Fin n → Nat) (hx : ∀ i, xCur i < m) :
      ((Finset.univ : Finset (Fin m → Bool)).filter P).card =
      ∑ y : Fin n → Bool,
        ((Finset.univ : Finset (Fin m → Bool)).filter
          (fun v => P v ∧ (fun i => v ⟨xCur i, hx i⟩) = y)).card := by
  have h1 : ∀ v ∈ (Finset.univ : Finset (Fin m → Bool)).filter P,
      (1 : Nat) = ∑ y : Fin n → Bool,
        if (fun i => v ⟨xCur i, hx i⟩) = y then 1 else 0 := by
    intro v _
    rw [Finset.sum_ite_eq]
    simp
  calc
    ((Finset.univ : Finset (Fin m → Bool)).filter P).card
        = ∑ v ∈ (Finset.univ : Finset (Fin m → Bool)).filter P, (1 : Nat) := by simp
    _ = ∑ v ∈ (Finset.univ : Finset (Fin m → Bool)).filter P,
          ∑ y : Fin n → Bool, if (fun i => v ⟨xCur i, hx i⟩) = y then 1 else 0 := by
          apply Finset.sum_congr rfl
          exact h1
    _ = ∑ y : Fin n → Bool,
          ∑ v ∈ (Finset.univ : Finset (Fin m → Bool)).filter P,
            if (fun i => v ⟨xCur i, hx i⟩) = y then 1 else 0 := Finset.sum_comm
    _ = ∑ y : Fin n → Bool,
          ((Finset.univ : Finset (Fin m → Bool)).filter
            (fun v => P v ∧ (fun i => v ⟨xCur i, hx i⟩) = y)).card := by
          apply Finset.sum_congr rfl
          intro y _
          rw [← Finset.sum_filter, Finset.filter_filter, Finset.sum_const, smul_eq_mul,
            Nat.mul_one]

private noncomputable def cntX {n k : Nat} (on : Fin k → Bool) (lit : Fin k → Fin n → Bool → Bool)
    (st : GState n k) (xCur : Fin n → Nat) (hx : ∀ i, xCur i < st.m) (y : Fin n → Bool) : Nat :=
  ((Finset.univ : Finset (Fin st.m → Bool)).filter
    (fun v => ValidV st.m st.edges (actFn on lit st.source) v ∧
      (fun i => v ⟨xCur i, hx i⟩) = y)).card

private noncomputable def cntXD {n k : Nat} (on : Fin k → Bool) (lit : Fin k → Fin n → Bool → Bool)
    (st : GState n k) (xCur : Fin n → Nat) (hx : ∀ i, xCur i < st.m)
    (det : Nat) (hdet : det < st.m) (y : Fin n → Bool) (d : Bool) : Nat :=
  ((Finset.univ : Finset (Fin st.m → Bool)).filter
    (fun v => ValidV st.m st.edges (actFn on lit st.source) v ∧
      (fun i => v ⟨xCur i, hx i⟩) = y ∧ v ⟨det, hdet⟩ = d)).card

private noncomputable def cntXDS {n k : Nat} (on : Fin k → Bool) (lit : Fin k → Fin n → Bool → Bool)
    (st : GState n k) (xCur : Fin n → Nat) (hx : ∀ i, xCur i < st.m)
    (det : Nat) (hdet : det < st.m) (s : Nat) (hs : s < st.m)
    (y : Fin n → Bool) (d sb : Bool) : Nat :=
  ((Finset.univ : Finset (Fin st.m → Bool)).filter
    (fun v => ValidV st.m st.edges (actFn on lit st.source) v ∧
      (fun i => v ⟨xCur i, hx i⟩) = y ∧ v ⟨det, hdet⟩ = d ∧ v ⟨s, hs⟩ = sb)).card

private structure XInv (n k : Nat) (st : GState n k) (xCur : Fin n → Nat) : Prop where
  wf : WellFormed n k st
  x_lt : ∀ i, xCur i < st.m
  x_inj : Function.Injective xCur
  x_deg : ∀ i, inDeg st.edges (xCur i) ≤ 1 ∧ outDeg st.edges (xCur i) ≤ 1
  x_src : ∀ i, st.source (xCur i) = none
  x_bag : ∀ i, xCur i ∈ st.bags.getLast wf.bags_ne

private structure DetInv (n k : Nat) (e : Fin k) (st : GState n k)
    (xCur : Fin n → Nat) (det : Nat) : Prop where
  xinv : XInv n k st xCur
  det_lt : det < st.m
  det_ne : ∀ i, xCur i ≠ det
  det_deg : inDeg st.edges det ≤ 1 ∧ outDeg st.edges det ≤ 1
  det_src : st.source det = some (Sum.inl e)
  det_bag : det ∈ st.bags.getLast xinv.wf.bags_ne

private structure NegInv (n k : Nat) (e : Fin k) (i : Fin n) (st : GState n k)
    (xCur : Fin n → Nat) (det s : Nat) : Prop where
  dinv : DetInv n k e st xCur det
  s_lt : s < st.m
  s_ne_x : ∀ j, xCur j ≠ s
  s_ne_det : det ≠ s
  s_deg : inDeg st.edges s ≤ 1 ∧ outDeg st.edges s ≤ 1
  s_src : st.source s = some (Sum.inr (e, i, false))
  s_bag : s ∈ st.bags.getLast dinv.xinv.wf.bags_ne

private def initState (n k : Nat) : GState n k :=
  ⟨n, ∅, fun _ => none, [Finset.range n]⟩

private def initX (n : Nat) : Fin n → Nat := fun i => i.val

private lemma init_xInv (n k : Nat) : XInv n k (initState n k) (initX n) := by
  have hwf : WellFormed n k (initState n k) :=
    { edges_lt := by simp [initState]
      deg_le := by intro u _; simp [initState, inDeg, outDeg]
      bags_ne := by simp [initState]
      bags_len := by simp [initState]
      bags_card := by
        intro b hb
        simp only [initState, List.mem_singleton] at hb
        subst hb
        rw [Finset.card_range]
        omega
      bags_lt := by
        intro b hb u hu
        simp only [initState, List.mem_singleton] at hb
        subst hb
        exact Finset.mem_range.mp hu
      bags_cov := by
        intro u hu
        exact ⟨Finset.range n, List.mem_singleton_self _, Finset.mem_range.mpr hu⟩
      bags_edge := by simp [initState]
      bags_inter := by
        intro u s t w hs ht hw hst htw hus _
        simp only [initState, List.length_singleton] at hs ht hw
        have : s = t := by omega
        subst this
        exact hus }
  refine
    { wf := hwf
      x_lt := fun i => i.isLt
      x_inj := fun i j h => Fin.ext h
      x_deg := fun i => by simp [initState, inDeg, outDeg]
      x_src := fun _ => rfl
      x_bag := fun i => by simp [initState, initX] }

private lemma init_cntX {n k : Nat} (on : Fin k → Bool) (lit : Fin k → Fin n → Bool → Bool)
    (y : Fin n → Bool) :
    cntX on lit (initState n k) (initX n) (init_xInv n k).x_lt y = 1 := by
  unfold cntX
  rw [card_filter_unique
    (fun v : Fin (initState n k).m → Bool =>
      ValidV (initState n k).m (initState n k).edges (actFn on lit (initState n k).source) v ∧
      (fun i => v ⟨initX n i, (init_xInv n k).x_lt i⟩) = y)
    y True
    (by
      intro v
      constructor
      · intro ⟨_, hv⟩
        exact ⟨by funext i; exact congrFun hv i, trivial⟩
      · intro ⟨hv, _⟩
        subst hv
        refine ⟨⟨?_, by simp [initState]⟩, rfl⟩
        intro i hi
        simp [initState, actFn] at hi)]
  simp

private def allocDetStep {n k : Nat} (e : Fin k) (st : GState n k) (xCur : Fin n → Nat) :
    GState n k × Nat :=
  let det0 := st.m
  let newSrc := fun u => if u = det0 then some (Sum.inl e) else st.source u
  let newBag := insert det0 (Finset.univ.image xCur)
  (⟨st.m + 1, st.edges, newSrc, st.bags ++ [newBag]⟩, det0)

private lemma allocDet_inv {n k : Nat} (e : Fin k) (st : GState n k) (xCur : Fin n → Nat)
    (hinv : XInv n k st xCur) :
    DetInv n k e (allocDetStep e st xCur).1 xCur (allocDetStep e st xCur).2 := by
  dsimp only [allocDetStep]
  have hallX : (Finset.univ.image xCur).card ≤ n := by
    calc (Finset.univ.image xCur).card
        ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_image_le
      _ = n := Fintype.card_fin n
  have hwf : WellFormed n k ⟨st.m + 1, st.edges ∪ ∅,
      fun u => if u = st.m then some (Sum.inl e) else st.source u,
      st.bags ++ [insert st.m (Finset.univ.image xCur)]⟩ := by
    apply extend_wellFormed st hinv.wf 1 (by omega) ∅
    · simp
    · simp
    · intro u hu
      have h := hinv.wf.deg_le u hu
      simp only [inDeg, outDeg, Finset.filter_empty, Finset.card_empty, Nat.add_zero]
      exact h
    · intro u _ _
      simp [inDeg, outDeg]
    · have h1 := Finset.card_insert_le st.m (Finset.univ.image xCur)
      omega
    · intro u hu
      simp only [mem_insert, mem_image, mem_univ, true_and] at hu
      rcases hu with rfl | ⟨i, rfl⟩
      · omega
      · have := hinv.x_lt i; omega
    · intro u h1 h2
      have : u = st.m := by omega
      subst this
      exact mem_insert_self _ _
    · intro u hu hlt
      simp only [mem_insert, mem_image, mem_univ, true_and] at hu
      rcases hu with rfl | ⟨i, rfl⟩
      · omega
      · exact hinv.x_bag i
    · simp
  rw [Finset.union_empty] at hwf
  have hxinv : XInv n k ⟨st.m + 1, st.edges,
      fun u => if u = st.m then some (Sum.inl e) else st.source u,
      st.bags ++ [insert st.m (Finset.univ.image xCur)]⟩ xCur :=
    { wf := hwf
      x_lt := fun i => by dsimp only; have := hinv.x_lt i; omega
      x_inj := hinv.x_inj
      x_deg := hinv.x_deg
      x_src := fun i => by
        dsimp only
        have hlt := hinv.x_lt i
        have hne : xCur i ≠ st.m := by omega
        simp [hne, hinv.x_src i]
      x_bag := fun i => by
        dsimp only
        rw [List.getLast_append_singleton]
        exact mem_insert_of_mem (mem_image_of_mem xCur (mem_univ i)) }
  refine
    { xinv := hxinv
      det_lt := by dsimp only; omega
      det_ne := fun i => by have := hinv.x_lt i; omega
      det_deg := ⟨by dsimp only; rw [inDeg_eq_zero_of_ge hinv.wf.edges_lt (Nat.le_refl _)]; omega,
        by dsimp only; rw [outDeg_eq_zero_of_ge hinv.wf.edges_lt (Nat.le_refl _)]; omega⟩
      det_src := by simp
      det_bag := by
        dsimp only
        rw [List.getLast_append_singleton]
        exact mem_insert_self _ _ }

private lemma allocDet_cnt {n k : Nat} (on : Fin k → Bool) (lit : Fin k → Fin n → Bool → Bool)
    (e : Fin k) (st : GState n k) (xCur : Fin n → Nat) (hinv : XInv n k st xCur)
    (y : Fin n → Bool) (d : Bool) :
    let res := allocDetStep e st xCur
    let hdet := allocDet_inv e st xCur hinv
    cntXD on lit res.1 xCur hdet.xinv.x_lt res.2 hdet.det_lt y d =
      cntX on lit st xCur hinv.x_lt y * (if on e = false ∧ d = true then 0 else 1) := by
  dsimp only [allocDetStep, cntXD, cntX]
  let newSrc := fun u => if u = st.m then some (Sum.inl e) else st.source u
  have hact : ∀ u < st.m, actFn on lit newSrc u = actFn on lit st.source u := by
    intro u hu
    have hne : u ≠ st.m := by omega
    simp [actFn, newSrc, hne]
  have h := card_extend_mul st.m 1 st.edges ∅ (actFn on lit st.source) (actFn on lit newSrc)
    hinv.wf.edges_lt hact
    (fun v1 => (fun i => v1 ⟨xCur i, hinv.x_lt i⟩) = y)
    (fun v => (fun i => v ⟨xCur i, by have := hinv.x_lt i; omega⟩) = y ∧ v ⟨st.m, by omega⟩ = d)
    (if on e = false ∧ d = true then 0 else 1)
    (by
      intro v1 v2 _ _ hq
      funext i
      have h1 := congrFun hq.1 i
      rwa [joinV_lt v1 v2 (xCur i) (hinv.x_lt i)] at h1)
    (by
      intro v1 _ hp
      have hcf := card_filter_unique
        (fun v2 : Fin 1 → Bool => StepValid st.m 1 ∅ (actFn on lit newSrc) v1 v2 ∧
          (fun i => joinV v1 v2 ⟨xCur i, by have := hinv.x_lt i; omega⟩) = y ∧
          joinV v1 v2 ⟨st.m, by omega⟩ = d)
        (fun _ => d) (¬ (on e = false ∧ d = true))
        (by
          intro v2
          constructor
          · intro ⟨⟨hz, _⟩, _, hvd⟩
            have h0 : v2 0 = d := by
              have hg := joinV_ge v1 v2 (0 : Fin 1) (by omega)
              simp only [Fin.val_zero, Nat.add_zero] at hg
              rw [← hg, hvd]
            have heq : v2 = fun _ => d := by
              funext j
              have hj : j = 0 := Fin.ext (by omega)
              subst hj; exact h0
            refine ⟨heq, ?_⟩
            intro ⟨hon, hd⟩
            have hact0 : actFn on lit newSrc (st.m + (0 : Fin 1).val) = false := by
              simp [actFn, newSrc, hon]
            have hv0 := hz 0 hact0
            rw [h0, hd] at hv0
            contradiction
          · intro ⟨hv2, hnr⟩
            subst hv2
            refine ⟨⟨?_, by simp⟩, ?_, ?_⟩
            · intro j hj
              have hact0 : actFn on lit newSrc (st.m + j.val) = on e := by
                have hj0 : j.val = 0 := by omega
                rw [hj0]
                simp [actFn, newSrc]
              rw [hact0] at hj
              cases hd : d
              · rfl
              · exact absurd ⟨hj, hd⟩ hnr
            · funext i
              rw [joinV_lt v1 (fun _ => d) (xCur i) (hinv.x_lt i)]
              exact congrFun hp i
            · have hg := joinV_ge v1 (fun _ => d) (0 : Fin 1) (by omega)
              simpa using hg)
      rw [hcf]
      by_cases hc : on e = false ∧ d = true <;> simp [hc])
  simpa [Finset.union_empty] using h

private def posEdges (xi px xi' det pd det' ppos : Nat) : Finset (Nat × Nat) :=
  {(xi, px), (px, xi'), (xi', xi), (det, pd), (pd, det'), (det', det),
    (px, ppos), (ppos, px), (ppos, pd)}

private def posStep {n k : Nat} (e : Fin k) (i : Fin n) (st : GState n k)
    (xCur : Fin n → Nat) (det : Nat) : GState n k × (Fin n → Nat) × Nat :=
  let m := st.m
  let xi := xCur i
  let px := m
  let xi' := m + 1
  let pd := m + 2
  let det' := m + 3
  let ppos := m + 4
  let newE := posEdges xi px xi' det pd det' ppos
  let newSrc := fun u =>
    if u = px ∨ u = xi' then none
    else if u = pd ∨ u = det' then some (Sum.inl e)
    else if u = ppos then some (Sum.inr (e, i, true))
    else st.source u
  let newBag := insert ppos (insert det' (insert pd (insert det (insert xi' (insert px
    (Finset.univ.image xCur))))))
  let xCur' := Function.update xCur i xi'
  (⟨m + 5, st.edges ∪ newE, newSrc, st.bags ++ [newBag]⟩, xCur', det')

private lemma card_filter_subset_pair {α : Type*} [DecidableEq α] (s : Finset α)
    (p : α → Prop) [DecidablePred p] (a b : α)
    (h : ∀ x ∈ s, p x → x = a ∨ x = b) :
    (s.filter p).card ≤ 2 := by
  have hsub : s.filter p ⊆ {a, b} := by
    intro x hx
    simp only [mem_filter] at hx
    simp only [mem_insert, mem_singleton]
    exact h x hx.1 hx.2
  calc (s.filter p).card ≤ ({a, b} : Finset α).card := Finset.card_le_card hsub
    _ ≤ ({b} : Finset α).card + 1 := Finset.card_insert_le a {b}
    _ = 2 := by simp

private lemma card_filter_subset_single {α : Type*} [DecidableEq α] (s : Finset α)
    (p : α → Prop) [DecidablePred p] (a : α)
    (h : ∀ x ∈ s, p x → x = a) :
    (s.filter p).card ≤ 1 := by
  have hsub : s.filter p ⊆ {a} := by
    intro x hx
    simp only [mem_filter] at hx
    simp only [mem_singleton]
    exact h x hx.1 hx.2
  calc (s.filter p).card ≤ ({a} : Finset α).card := Finset.card_le_card hsub
    _ = 1 := Finset.card_singleton a

private lemma card_filter_empty {α : Type*} (s : Finset α) (p : α → Prop) [DecidablePred p]
    (h : ∀ x ∈ s, ¬ p x) :
    (s.filter p).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact h

private lemma posEdges_deg {m xi det : Nat} (hxi : xi < m) (hdet : det < m) (hne : xi ≠ det) :
    let newE := posEdges xi m (m + 1) det (m + 2) (m + 3) (m + 4)
    (∀ u < m, u ≠ xi → u ≠ det → inDeg newE u = 0 ∧ outDeg newE u = 0) ∧
    (inDeg newE xi ≤ 1 ∧ outDeg newE xi ≤ 1) ∧
    (inDeg newE det ≤ 1 ∧ outDeg newE det ≤ 1) ∧
    (inDeg newE m ≤ 2 ∧ outDeg newE m ≤ 2) ∧
    (inDeg newE (m + 1) ≤ 1 ∧ outDeg newE (m + 1) ≤ 1) ∧
    (inDeg newE (m + 2) ≤ 2 ∧ outDeg newE (m + 2) ≤ 2) ∧
    (inDeg newE (m + 3) ≤ 1 ∧ outDeg newE (m + 3) ≤ 1) ∧
    (inDeg newE (m + 4) ≤ 2 ∧ outDeg newE (m + 4) ≤ 2) := by
  dsimp only
  refine ⟨?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro u hu hux hud
    refine ⟨card_filter_empty _ _ ?_, card_filter_empty _ _ ?_⟩ <;>
      · intro e he
        simp only [posEdges, mem_insert, mem_singleton] at he
        rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp <;> omega
  · apply card_filter_subset_single _ _ (m + 1, xi)
    intro e he h2
    simp only [posEdges, mem_insert, mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | rfl | (dsimp at h2; omega)
  · apply card_filter_subset_single _ _ (xi, m)
    intro e he h1
    simp only [posEdges, mem_insert, mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | rfl | (dsimp at h1; omega)
  · apply card_filter_subset_single _ _ (m + 3, det)
    intro e he h2
    simp only [posEdges, mem_insert, mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | rfl | (dsimp at h2; omega)
  · apply card_filter_subset_single _ _ (det, m + 2)
    intro e he h1
    simp only [posEdges, mem_insert, mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | rfl | (dsimp at h1; omega)
  · apply card_filter_subset_pair _ _ (xi, m) (m + 4, m)
    intro e he h2
    simp only [posEdges, mem_insert, mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact Or.inl rfl | exact Or.inr rfl | (dsimp at h2; omega)
  · apply card_filter_subset_pair _ _ (m, m + 1) (m, m + 4)
    intro e he h1
    simp only [posEdges, mem_insert, mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact Or.inl rfl | exact Or.inr rfl | (dsimp at h1; omega)
  · apply card_filter_subset_single _ _ (m, m + 1)
    intro e he h2
    simp only [posEdges, mem_insert, mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | rfl | (dsimp at h2; omega)
  · apply card_filter_subset_single _ _ (m + 1, xi)
    intro e he h1
    simp only [posEdges, mem_insert, mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | rfl | (dsimp at h1; omega)
  · apply card_filter_subset_pair _ _ (det, m + 2) (m + 4, m + 2)
    intro e he h2
    simp only [posEdges, mem_insert, mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact Or.inl rfl | exact Or.inr rfl | (dsimp at h2; omega)
  · apply card_filter_subset_pair _ _ (m + 2, m + 3) (m + 2, m + 3)
    intro e he h1
    simp only [posEdges, mem_insert, mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact Or.inl rfl | (dsimp at h1; omega)
  · apply card_filter_subset_single _ _ (m + 2, m + 3)
    intro e he h2
    simp only [posEdges, mem_insert, mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | rfl | (dsimp at h2; omega)
  · apply card_filter_subset_single _ _ (m + 3, det)
    intro e he h1
    simp only [posEdges, mem_insert, mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | rfl | (dsimp at h1; omega)
  · apply card_filter_subset_pair _ _ (m, m + 4) (m, m + 4)
    intro e he h2
    simp only [posEdges, mem_insert, mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact Or.inl rfl | (dsimp at h2; omega)
  · apply card_filter_subset_pair _ _ (m + 4, m) (m + 4, m + 2)
    intro e he h1
    simp only [posEdges, mem_insert, mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact Or.inl rfl | exact Or.inr rfl | (dsimp at h1; omega)

private lemma posStep_inv {n k : Nat} (e : Fin k) (i : Fin n) (st : GState n k)
    (xCur : Fin n → Nat) (det : Nat) (hinv : DetInv n k e st xCur det) :
    let res := posStep e i st xCur det
    DetInv n k e res.1 res.2.1 res.2.2 := by
  dsimp only [posStep]
  have hxi := hinv.xinv.x_lt i
  have hdet := hinv.det_lt
  have hne := hinv.det_ne i
  have hdeg := posEdges_deg hxi hdet hne
  let newE := posEdges (xCur i) st.m (st.m + 1) det (st.m + 2) (st.m + 3) (st.m + 4)
  let newBag := insert (st.m + 4) (insert (st.m + 3) (insert (st.m + 2)
    (insert det (insert (st.m + 1) (insert st.m (Finset.univ.image xCur))))))
  have hdisj : Disjoint st.edges newE := by
    rw [Finset.disjoint_left]
    intro ed he1 he2
    have hlt := hinv.xinv.wf.edges_lt ed he1
    simp only [newE, posEdges, mem_insert, mem_singleton] at he2
    rcases he2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp at hlt <;> omega
  have hwf : WellFormed n k ⟨st.m + 5, st.edges ∪ newE,
      fun u => if u = st.m ∨ u = st.m + 1 then none
        else if u = st.m + 2 ∨ u = st.m + 3 then some (Sum.inl e)
        else if u = st.m + 4 then some (Sum.inr (e, i, true))
        else st.source u,
      st.bags ++ [newBag]⟩ := by
    apply extend_wellFormed st hinv.xinv.wf 5 (by omega) newE _ newBag
    · intro ed hed
      simp only [newE, posEdges, mem_insert, mem_singleton] at hed
      rcases hed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp <;> omega
    · intro ed hed
      simp only [newE, posEdges, mem_insert, mem_singleton] at hed
      rcases hed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp <;> omega
    · intro u hu
      dsimp only [newE]
      by_cases h1 : u = xCur i
      · subst h1
        rcases hinv.xinv.x_deg i with ⟨ha1, ha2⟩
        rcases hdeg.2.1 with ⟨hb1, hb2⟩
        exact ⟨by omega, by omega⟩
      · by_cases h2 : u = det
        · subst h2
          rcases hinv.det_deg with ⟨ha1, ha2⟩
          rcases hdeg.2.2.1 with ⟨hb1, hb2⟩
          exact ⟨by omega, by omega⟩
        · rcases hdeg.1 u hu h1 h2 with ⟨hb1, hb2⟩
          rcases hinv.xinv.wf.deg_le u hu with ⟨ha1, ha2⟩
          exact ⟨by omega, by omega⟩
    · intro u hge hlt
      dsimp only [newE]
      have hcases : u = st.m ∨ u = st.m + 1 ∨ u = st.m + 2 ∨ u = st.m + 3 ∨ u = st.m + 4 := by
        omega
      rcases hcases with rfl | rfl | rfl | rfl | rfl
      · exact hdeg.2.2.2.1
      · rcases hdeg.2.2.2.2.1 with ⟨h1, h2⟩; exact ⟨by omega, by omega⟩
      · exact hdeg.2.2.2.2.2.1
      · rcases hdeg.2.2.2.2.2.2.1 with ⟨h1, h2⟩; exact ⟨by omega, by omega⟩
      · exact hdeg.2.2.2.2.2.2.2
    · have hallX : (Finset.univ.image xCur).card ≤ n := by
        calc (Finset.univ.image xCur).card ≤ (Finset.univ : Finset (Fin n)).card := card_image_le
          _ = n := Fintype.card_fin n
      have h1 := card_insert_le (st.m + 4) (insert (st.m + 3) (insert (st.m + 2)
        (insert det (insert (st.m + 1) (insert st.m (Finset.univ.image xCur))))))
      have h2 := card_insert_le (st.m + 3) (insert (st.m + 2)
        (insert det (insert (st.m + 1) (insert st.m (Finset.univ.image xCur)))))
      have h3 := card_insert_le (st.m + 2)
        (insert det (insert (st.m + 1) (insert st.m (Finset.univ.image xCur))))
      have h4 := card_insert_le det (insert (st.m + 1) (insert st.m (Finset.univ.image xCur)))
      have h5 := card_insert_le (st.m + 1) (insert st.m (Finset.univ.image xCur))
      have h6 := card_insert_le st.m (Finset.univ.image xCur)
      dsimp only [newBag]
      omega
    · intro u hu
      simp only [newBag, mem_insert, mem_image, mem_univ, true_and] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | ⟨j, rfl⟩
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · have := hinv.xinv.x_lt j; omega
    · intro u hge hlt
      have hcases : u = st.m ∨ u = st.m + 1 ∨ u = st.m + 2 ∨ u = st.m + 3 ∨ u = st.m + 4 := by
        omega
      rcases hcases with rfl | rfl | rfl | rfl | rfl <;> simp [newBag]
    · intro u hu hlt
      simp only [newBag, mem_insert, mem_image, mem_univ, true_and] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | ⟨j, rfl⟩
      · omega
      · omega
      · omega
      · exact hinv.det_bag
      · omega
      · omega
      · exact hinv.xinv.x_bag j
    · intro ed hed
      have hxim : xCur i ∈ Finset.univ.image xCur := mem_image_of_mem xCur (mem_univ i)
      simp only [newE, posEdges, mem_insert, mem_singleton] at hed
      rcases hed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [newBag, hxim]
  have hxinv : XInv n k ⟨st.m + 5, st.edges ∪ newE,
      fun u => if u = st.m ∨ u = st.m + 1 then none
        else if u = st.m + 2 ∨ u = st.m + 3 then some (Sum.inl e)
        else if u = st.m + 4 then some (Sum.inr (e, i, true))
        else st.source u,
      st.bags ++ [newBag]⟩ (Function.update xCur i (st.m + 1)) :=
    { wf := hwf
      x_lt := fun j => by
        dsimp only
        by_cases hji : j = i
        · subst hji; simp
        · simp [Function.update, hji]; have := hinv.xinv.x_lt j; omega
      x_inj := by
        intro j1 j2 heq
        by_cases h1 : j1 = i <;> by_cases h2 : j2 = i
        · rw [h1, h2]
        · simp [Function.update, h1, h2] at heq
          have := hinv.xinv.x_lt j2; omega
        · simp [Function.update, h1, h2] at heq
          have := hinv.xinv.x_lt j1; omega
        · simp [Function.update, h1, h2] at heq
          exact hinv.xinv.x_inj heq
      x_deg := fun j => by
        dsimp only
        rw [inDeg_union_of_disjoint hdisj, outDeg_union_of_disjoint hdisj]
        by_cases hji : j = i
        · subst hji
          simp only [Function.update_self]
          rw [inDeg_eq_zero_of_ge hinv.xinv.wf.edges_lt (by omega),
            outDeg_eq_zero_of_ge hinv.xinv.wf.edges_lt (by omega), Nat.zero_add, Nat.zero_add]
          exact hdeg.2.2.2.2.1
        · simp only [Function.update_of_ne hji]
          dsimp only [newE]
          have hne_xi : xCur j ≠ xCur i := fun h => hji (hinv.xinv.x_inj h)
          have hne_det : xCur j ≠ det := hinv.det_ne j
          rcases hdeg.1 (xCur j) (hinv.xinv.x_lt j) hne_xi hne_det with ⟨hb1, hb2⟩
          rcases hinv.xinv.x_deg j with ⟨ha1, ha2⟩
          exact ⟨by omega, by omega⟩
      x_src := fun j => by
        dsimp only
        by_cases hji : j = i
        · subst hji; simp
        · simp only [Function.update_of_ne hji]
          have hlt := hinv.xinv.x_lt j
          have h1 : ¬ (xCur j = st.m ∨ xCur j = st.m + 1) := by omega
          have h2 : ¬ (xCur j = st.m + 2 ∨ xCur j = st.m + 3) := by omega
          have h3 : xCur j ≠ st.m + 4 := by omega
          simp [h1, h2, h3, hinv.xinv.x_src j]
      x_bag := fun j => by
        dsimp only
        rw [List.getLast_append_singleton]
        by_cases hji : j = i
        · subst hji; simp [newBag]
        · simp only [Function.update_of_ne hji]
          have hjm : xCur j ∈ Finset.univ.image xCur := mem_image_of_mem xCur (mem_univ j)
          simp [newBag, hjm] }
  refine
    { xinv := hxinv
      det_lt := by dsimp only; omega
      det_ne := fun j => by
        by_cases hji : j = i
        · subst hji; simp
        · simp only [Function.update_of_ne hji]
          have := hinv.xinv.x_lt j; omega
      det_deg := by
        dsimp only
        rw [inDeg_union_of_disjoint hdisj, outDeg_union_of_disjoint hdisj,
          inDeg_eq_zero_of_ge hinv.xinv.wf.edges_lt (by omega),
          outDeg_eq_zero_of_ge hinv.xinv.wf.edges_lt (by omega), Nat.zero_add, Nat.zero_add]
        exact hdeg.2.2.2.2.2.2.1
      det_src := by simp
      det_bag := by
        dsimp only
        rw [List.getLast_append_singleton]
        simp [newBag] }

private def fPos (on_e lit_pos y_i d : Bool) : Nat :=
  if on_e = true ∧ lit_pos = true ∧ y_i = true ∧ d = false then 0 else 1

private lemma posStep_cnt {n k : Nat} (on : Fin k → Bool) (lit : Fin k → Fin n → Bool → Bool)
    (e : Fin k) (i : Fin n) (st : GState n k) (xCur : Fin n → Nat) (det : Nat)
    (hinv : DetInv n k e st xCur det) (y : Fin n → Bool) (d : Bool) :
    let res := posStep e i st xCur det
    let hres := posStep_inv e i st xCur det hinv
    cntXD on lit res.1 res.2.1 hres.xinv.x_lt res.2.2 hres.det_lt y d =
      cntXD on lit st xCur hinv.xinv.x_lt det hinv.det_lt y d *
        fPos (on e) (lit e i true) (y i) d := by
  dsimp only [posStep, cntXD]
  let m := st.m
  let xi := xCur i
  let newE := posEdges xi m (m + 1) det (m + 2) (m + 3) (m + 4)
  let newSrc : Nat → Option (Fin k ⊕ (Fin k × Fin n × Bool)) := fun u =>
    if u = m ∨ u = m + 1 then none
    else if u = m + 2 ∨ u = m + 3 then some (Sum.inl e)
    else if u = m + 4 then some (Sum.inr (e, i, true))
    else st.source u
  have hact_old : ∀ u < m, actFn on lit newSrc u = actFn on lit st.source u := by
    intro u hu
    have h1 : ¬ (u = m ∨ u = m + 1) := by omega
    have h2 : ¬ (u = m + 2 ∨ u = m + 3) := by omega
    have h3 : u ≠ m + 4 := by omega
    simp [actFn, newSrc, h1, h2, h3]
  have hact_xi : actFn on lit newSrc xi = true := by
    dsimp only [xi]
    rw [hact_old (xCur i) (hinv.xinv.x_lt i)]
    simp [actFn, hinv.xinv.x_src i]
  have hact_det : actFn on lit newSrc det = on e := by
    rw [hact_old det hinv.det_lt]
    simp [actFn, hinv.det_src]
  have hact0 : actFn on lit newSrc m = true := by simp [actFn, newSrc]
  have hact1 : actFn on lit newSrc (m + 1) = true := by simp [actFn, newSrc]
  have hact2 : actFn on lit newSrc (m + 2) = on e := by
    have h1 : ¬ (m + 2 = m ∨ m + 2 = m + 1) := by omega
    simp [actFn, newSrc, h1]
  have hact3 : actFn on lit newSrc (m + 3) = on e := by
    have h1 : ¬ (m + 3 = m ∨ m + 3 = m + 1) := by omega
    simp [actFn, newSrc, h1]
  have hact4 : actFn on lit newSrc (m + 4) = lit e i true := by
    have h1 : ¬ (m + 4 = m ∨ m + 4 = m + 1) := by omega
    have h2 : ¬ (m + 4 = m + 2 ∨ m + 4 = m + 3) := by omega
    simp [actFn, newSrc, h1, h2]
  have hxi_lt : xi < m := hinv.xinv.x_lt i
  have hdet_lt : det < m := hinv.det_lt
  have hchar : ∀ (v1 : Fin m → Bool) (v2 : Fin 5 → Bool),
      ValidV m st.edges (actFn on lit st.source) v1 →
      (StepValid m 5 newE (actFn on lit newSrc) v1 v2 ↔
        v2 0 = v1 ⟨xi, hxi_lt⟩ ∧
        v2 1 = v1 ⟨xi, hxi_lt⟩ ∧
        v2 2 = v1 ⟨det, hdet_lt⟩ ∧
        v2 3 = v1 ⟨det, hdet_lt⟩ ∧
        v2 4 = (if lit e i true then v1 ⟨xi, hxi_lt⟩ else false) ∧
        (on e = true → lit e i true = true → v1 ⟨xi, hxi_lt⟩ = true → v1 ⟨det, hdet_lt⟩ = true)) := by
    intro v1 v2 hv1
    have hdet_zero : on e = false → v1 ⟨det, hdet_lt⟩ = false := by
      intro hon
      exact hv1.1 ⟨det, hdet_lt⟩ (by simp [actFn, hinv.det_src, hon])
    constructor
    · intro ⟨hz, himp⟩
      have he1 : (xi, m) ∈ newE := by simp [newE, posEdges]
      have he2 : (m, m + 1) ∈ newE := by simp [newE, posEdges]
      have he3 : (m + 1, xi) ∈ newE := by simp [newE, posEdges]
      have he4 : (det, m + 2) ∈ newE := by simp [newE, posEdges]
      have he5 : (m + 2, m + 3) ∈ newE := by simp [newE, posEdges]
      have he6 : (m + 3, det) ∈ newE := by simp [newE, posEdges]
      have he7 : (m, m + 4) ∈ newE := by simp [newE, posEdges]
      have he8 : (m + 4, m) ∈ newE := by simp [newE, posEdges]
      have he9 : (m + 4, m + 2) ∈ newE := by simp [newE, posEdges]
      have hi1 : v1 ⟨xi, hxi_lt⟩ = true → v2 0 = true := by
        intro h
        have := stepImp himp he1 (by omega) (by omega) hact_xi hact0
          (by rw [joinV_lt v1 v2 xi hxi_lt]; exact h)
        rwa [joinV_m v1 v2] at this
      have hi2 : v2 0 = true → v2 1 = true := by
        intro h
        have := stepImp himp he2 (by omega) (by omega) hact0 hact1
          (by rw [joinV_m v1 v2]; exact h)
        rwa [joinV_nat v1 v2 1 1 rfl] at this
      have hi3 : v2 1 = true → v1 ⟨xi, hxi_lt⟩ = true := by
        intro h
        have := stepImp himp he3 (by omega) (by omega) hact1 hact_xi
          (by rw [joinV_nat v1 v2 1 1 rfl]; exact h)
        rwa [joinV_lt v1 v2 xi hxi_lt] at this
      have hv20 : v2 0 = v1 ⟨xi, hxi_lt⟩ := by
        cases h0 : v2 0 <;> cases hx : v1 ⟨xi, hxi_lt⟩
        · rfl
        · exact absurd (hi1 hx) (by rw [h0]; simp)
        · have := hi3 (hi2 h0); rw [hx] at this; cases this
        · rfl
      have hv21 : v2 1 = v1 ⟨xi, hxi_lt⟩ := by
        cases h1 : v2 1 <;> cases hx : v1 ⟨xi, hxi_lt⟩
        · rfl
        · exact absurd (hi2 (hi1 hx)) (by rw [h1]; simp)
        · have := hi3 h1; rw [hx] at this; cases this
        · rfl
      have hdet_eq : v2 2 = v1 ⟨det, hdet_lt⟩ ∧ v2 3 = v1 ⟨det, hdet_lt⟩ := by
        cases hon : on e
        · have hz2 := hz 2 (by simp [hact2, hon])
          have hz3 := hz 3 (by simp [hact3, hon])
          have hzd := hdet_zero hon
          exact ⟨by rw [hz2, hzd], by rw [hz3, hzd]⟩
        · have h4 : v1 ⟨det, hdet_lt⟩ = true → v2 2 = true := by
            intro h
            have := stepImp himp he4 (by omega) (by omega)
              (by rw [hact_det, hon]) (by rw [hact2, hon])
              (by rw [joinV_lt v1 v2 det hdet_lt]; exact h)
            rwa [joinV_nat v1 v2 2 2 rfl] at this
          have h5 : v2 2 = true → v2 3 = true := by
            intro h
            have := stepImp himp he5 (by omega) (by omega)
              (by rw [hact2, hon]) (by rw [hact3, hon])
              (by rw [joinV_nat v1 v2 2 2 rfl]; exact h)
            rwa [joinV_nat v1 v2 3 3 rfl] at this
          have h6 : v2 3 = true → v1 ⟨det, hdet_lt⟩ = true := by
            intro h
            have := stepImp himp he6 (by omega) (by omega)
              (by rw [hact3, hon]) (by rw [hact_det, hon])
              (by rw [joinV_nat v1 v2 3 3 rfl]; exact h)
            rwa [joinV_lt v1 v2 det hdet_lt] at this
          constructor
          · cases ha : v2 2 <;> cases hb : v1 ⟨det, hdet_lt⟩
            · rfl
            · exact absurd (h4 hb) (by rw [ha]; simp)
            · have := h6 (h5 ha); rw [hb] at this; cases this
            · rfl
          · cases ha : v2 3 <;> cases hb : v1 ⟨det, hdet_lt⟩
            · rfl
            · exact absurd (h5 (h4 hb)) (by rw [ha]; simp)
            · have := h6 ha; rw [hb] at this; cases this
            · rfl
      have hv24 : v2 4 = (if lit e i true then v1 ⟨xi, hxi_lt⟩ else false) := by
        cases hlit : lit e i true
        · simp [hz 4 (by simp [hact4, hlit])]
        · simp only [↓reduceIte]
          have h7 : v2 0 = true → v2 4 = true := by
            intro h
            have := stepImp himp he7 (by omega) (by omega) hact0 (by rw [hact4, hlit])
              (by rw [joinV_m v1 v2]; exact h)
            rwa [joinV_nat v1 v2 4 4 rfl] at this
          have h8 : v2 4 = true → v2 0 = true := by
            intro h
            have := stepImp himp he8 (by omega) (by omega) (by rw [hact4, hlit]) hact0
              (by rw [joinV_nat v1 v2 4 4 rfl]; exact h)
            rwa [joinV_m v1 v2] at this
          rw [← hv20]
          cases ha : v2 4 <;> cases hb : v2 0
          · rfl
          · exact absurd (h7 hb) (by rw [ha]; simp)
          · exact absurd (h8 ha) (by rw [hb]; simp)
          · rfl
      have hcond : on e = true → lit e i true = true →
          v1 ⟨xi, hxi_lt⟩ = true → v1 ⟨det, hdet_lt⟩ = true := by
        intro hon hlit hx
        have := stepImp himp he9 (by omega) (by omega)
          (by rw [hact4, hlit]) (by rw [hact2, hon])
          (by rw [joinV_nat v1 v2 4 4 rfl, hv24, hlit, hx]; rfl)
        rw [joinV_nat v1 v2 2 2 rfl, hdet_eq.1] at this
        exact this
      exact ⟨hv20, hv21, hdet_eq.1, hdet_eq.2, hv24, hcond⟩
    · intro ⟨h0, h1, h2, h3, h4, hcond⟩
      refine ⟨?_, ?_⟩
      · intro j hj
        rcases j with ⟨jv, hjv⟩
        match jv, hjv with
        | 0, _ => simp [hact0] at hj
        | 1, _ => simp [hact1] at hj
        | 2, _ => change v2 2 = false; rw [h2]; exact hdet_zero (by simpa [hact2] using hj)
        | 3, _ => change v2 3 = false; rw [h3]; exact hdet_zero (by simpa [hact3] using hj)
        | 4, _ =>
          change v2 4 = false
          have hlit : lit e i true = false := by simpa [hact4] using hj
          simp [h4, hlit]
      · intro ed hed ha hb hact1' hact2' hv
        simp only [newE, posEdges, mem_insert, mem_singleton] at hed
        rcases hed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          dsimp only at hact1' hact2' hv ⊢
        · rw [joinV_lt v1 v2 xi hxi_lt] at hv
          rw [joinV_m v1 v2, h0]; exact hv
        · rw [joinV_m v1 v2, h0] at hv
          rw [joinV_nat v1 v2 1 1 rfl, h1]; exact hv
        · rw [joinV_nat v1 v2 1 1 rfl, h1] at hv
          rw [joinV_lt v1 v2 xi hxi_lt]; exact hv
        · rw [joinV_lt v1 v2 det hdet_lt] at hv
          rw [joinV_nat v1 v2 2 2 rfl, h2]; exact hv
        · rw [joinV_nat v1 v2 2 2 rfl, h2] at hv
          rw [joinV_nat v1 v2 3 3 rfl, h3]; exact hv
        · rw [joinV_nat v1 v2 3 3 rfl, h3] at hv
          rw [joinV_lt v1 v2 det hdet_lt]; exact hv
        · rw [joinV_m v1 v2, h0] at hv
          have hlit : lit e i true = true := by simpa [hact4] using hact2'
          rw [joinV_nat v1 v2 4 4 rfl, h4, hlit]; exact hv
        · rw [joinV_nat v1 v2 4 4 rfl, h4] at hv
          have hlit : lit e i true = true := by simpa [hact4] using hact1'
          rw [hlit] at hv
          rw [joinV_m v1 v2, h0]; exact hv
        · rw [joinV_nat v1 v2 4 4 rfl, h4] at hv
          have hlit : lit e i true = true := by simpa [hact4] using hact1'
          have hon : on e = true := by simpa [hact2] using hact2'
          rw [hlit] at hv
          rw [joinV_nat v1 v2 2 2 rfl, h2]
          exact hcond hon hlit hv
  have hmain := card_extend_mul m 5 st.edges newE (actFn on lit st.source) (actFn on lit newSrc)
    hinv.xinv.wf.edges_lt hact_old
    (fun v1 => (fun j => v1 ⟨xCur j, hinv.xinv.x_lt j⟩) = y ∧ v1 ⟨det, hdet_lt⟩ = d)
    (fun v => (fun j => v ⟨Function.update xCur i (m + 1) j, by
      by_cases hji : j = i
      · subst hji; simp
      · simp [Function.update, hji]; have := hinv.xinv.x_lt j; omega⟩) = y ∧
      v ⟨m + 3, by omega⟩ = d)
    (fPos (on e) (lit e i true) (y i) d)
    (by
      intro v1 v2 hv1 hsv hq
      have hc := (hchar v1 v2 hv1).mp hsv
      refine ⟨?_, ?_⟩
      · funext j
        have hj := congrFun hq.1 j
        by_cases hji : j = i
        · subst hji
          simp only [Function.update_self] at hj
          rw [joinV_nat v1 v2 1 1 rfl, hc.2.1] at hj
          exact hj
        · simp only [Function.update_of_ne hji] at hj
          rwa [joinV_lt v1 v2 (xCur j) (hinv.xinv.x_lt j)] at hj
      · have hd := hq.2
        rw [joinV_nat v1 v2 3 3 rfl, hc.2.2.2.1] at hd
        exact hd)
    (by
      intro v1 hv1 ⟨hy1, hd1⟩
      have hxi_eq : v1 ⟨xi, hxi_lt⟩ = y i := congrFun hy1 i
      let target : Fin 5 → Bool := fun j =>
        match j.val with
        | 0 => y i
        | 1 => y i
        | 2 => d
        | 3 => d
        | _ => if lit e i true then y i else false
      have hcf := card_filter_unique
        (fun v2 : Fin 5 → Bool => StepValid m 5 newE (actFn on lit newSrc) v1 v2 ∧
          (fun j => joinV v1 v2 ⟨Function.update xCur i (m + 1) j, by
            by_cases hji : j = i
            · subst hji; simp
            · simp [Function.update, hji]; have := hinv.xinv.x_lt j; omega⟩) = y ∧
          joinV v1 v2 ⟨m + 3, by omega⟩ = d)
        target
        (¬ (on e = true ∧ lit e i true = true ∧ y i = true ∧ d = false))
        (by
          intro v2
          rw [hchar v1 v2 hv1, hxi_eq, hd1]
          constructor
          · intro ⟨⟨h0, h1, h2, h3, h4, hcond⟩, _, _⟩
            refine ⟨?_, ?_⟩
            · funext j
              rcases j with ⟨jv, hjv⟩
              match jv, hjv with
              | 0, _ => exact h0
              | 1, _ => exact h1
              | 2, _ => exact h2
              | 3, _ => exact h3
              | 4, _ => exact h4
            · intro ⟨hon, hlit, hyi, hd⟩
              have := hcond hon hlit hyi
              rw [hd] at this; cases this
          · intro ⟨hv2, hnr⟩
            subst hv2
            refine ⟨⟨rfl, rfl, rfl, rfl, rfl, ?_⟩, ?_, ?_⟩
            · intro hon hlit hyi
              cases hd : d
              · exact absurd ⟨hon, hlit, hyi, hd⟩ hnr
              · rfl
            · funext j
              by_cases hji : j = i
              · subst hji
                simp only [Function.update_self]
                rw [joinV_nat v1 target 1 1 rfl]
                rfl
              · simp only [Function.update_of_ne hji]
                rw [joinV_lt v1 target (xCur j) (hinv.xinv.x_lt j)]
                exact congrFun hy1 j
            · rw [joinV_nat v1 target 3 3 rfl]
              rfl)
      rw [hcf]
      unfold fPos
      by_cases hc : on e = true ∧ lit e i true = true ∧ y i = true ∧ d = false <;> simp [hc])
  exact hmain

private def allocSStep {n k : Nat} (e : Fin k) (i : Fin n) (st : GState n k)
    (xCur : Fin n → Nat) (det : Nat) : GState n k × Nat :=
  let s0 := st.m
  let newSrc := fun u => if u = s0 then some (Sum.inr (e, i, false)) else st.source u
  let newBag := insert s0 (insert det (Finset.univ.image xCur))
  (⟨st.m + 1, st.edges, newSrc, st.bags ++ [newBag]⟩, s0)

private lemma allocS_inv {n k : Nat} (e : Fin k) (i : Fin n) (st : GState n k)
    (xCur : Fin n → Nat) (det : Nat) (hinv : DetInv n k e st xCur det) :
    NegInv n k e i (allocSStep e i st xCur det).1 xCur det (allocSStep e i st xCur det).2 := by
  dsimp only [allocSStep]
  have hallX : (Finset.univ.image xCur).card ≤ n := by
    calc (Finset.univ.image xCur).card ≤ (Finset.univ : Finset (Fin n)).card := card_image_le
      _ = n := Fintype.card_fin n
  have hwf : WellFormed n k ⟨st.m + 1, st.edges ∪ ∅,
      fun u => if u = st.m then some (Sum.inr (e, i, false)) else st.source u,
      st.bags ++ [insert st.m (insert det (Finset.univ.image xCur))]⟩ := by
    apply extend_wellFormed st hinv.xinv.wf 1 (by omega) ∅
    · simp
    · simp
    · intro u hu
      have h := hinv.xinv.wf.deg_le u hu
      simp only [inDeg, outDeg, Finset.filter_empty, Finset.card_empty, Nat.add_zero]
      exact h
    · intro u _ _; simp [inDeg, outDeg]
    · have h1 := card_insert_le st.m (insert det (Finset.univ.image xCur))
      have h2 := card_insert_le det (Finset.univ.image xCur)
      omega
    · intro u hu
      simp only [mem_insert, mem_image, mem_univ, true_and] at hu
      rcases hu with rfl | rfl | ⟨j, rfl⟩
      · omega
      · have := hinv.det_lt; omega
      · have := hinv.xinv.x_lt j; omega
    · intro u h1 h2
      have : u = st.m := by omega
      subst this; exact mem_insert_self _ _
    · intro u hu hlt
      simp only [mem_insert, mem_image, mem_univ, true_and] at hu
      rcases hu with rfl | rfl | ⟨j, rfl⟩
      · omega
      · exact hinv.det_bag
      · exact hinv.xinv.x_bag j
    · simp
  rw [Finset.union_empty] at hwf
  have hxinv : XInv n k ⟨st.m + 1, st.edges,
      fun u => if u = st.m then some (Sum.inr (e, i, false)) else st.source u,
      st.bags ++ [insert st.m (insert det (Finset.univ.image xCur))]⟩ xCur :=
    { wf := hwf
      x_lt := fun j => by dsimp only; have := hinv.xinv.x_lt j; omega
      x_inj := hinv.xinv.x_inj
      x_deg := hinv.xinv.x_deg
      x_src := fun j => by
        dsimp only
        have hlt := hinv.xinv.x_lt j
        have hne : xCur j ≠ st.m := by omega
        simp [hne, hinv.xinv.x_src j]
      x_bag := fun j => by
        dsimp only
        rw [List.getLast_append_singleton]
        exact mem_insert_of_mem (mem_insert_of_mem (mem_image_of_mem xCur (mem_univ j))) }
  have hdinv : DetInv n k e _ xCur det :=
    { xinv := hxinv
      det_lt := by dsimp only; have := hinv.det_lt; omega
      det_ne := hinv.det_ne
      det_deg := hinv.det_deg
      det_src := by
        dsimp only
        have hlt := hinv.det_lt
        have hne : det ≠ st.m := by omega
        simp [hne, hinv.det_src]
      det_bag := by
        dsimp only
        rw [List.getLast_append_singleton]
        exact mem_insert_of_mem (mem_insert_self _ _) }
  refine
    { dinv := hdinv
      s_lt := by dsimp only; omega
      s_ne_x := fun j => by have := hinv.xinv.x_lt j; omega
      s_ne_det := by have := hinv.det_lt; omega
      s_deg := ⟨by dsimp only; rw [inDeg_eq_zero_of_ge hinv.xinv.wf.edges_lt (Nat.le_refl _)]; omega,
        by dsimp only; rw [outDeg_eq_zero_of_ge hinv.xinv.wf.edges_lt (Nat.le_refl _)]; omega⟩
      s_src := by simp
      s_bag := by
        dsimp only
        rw [List.getLast_append_singleton]
        exact mem_insert_self _ _ }

private lemma allocS_cnt {n k : Nat} (on : Fin k → Bool) (lit : Fin k → Fin n → Bool → Bool)
    (e : Fin k) (i : Fin n) (st : GState n k) (xCur : Fin n → Nat) (det : Nat)
    (hinv : DetInv n k e st xCur det) (y : Fin n → Bool) (d sb : Bool) :
    let res := allocSStep e i st xCur det
    let hres := allocS_inv e i st xCur det hinv
    cntXDS on lit res.1 xCur hres.dinv.xinv.x_lt det hres.dinv.det_lt res.2 hres.s_lt y d sb =
      cntXD on lit st xCur hinv.xinv.x_lt det hinv.det_lt y d *
        (if lit e i false = false ∧ sb = true then 0 else 1) := by
  dsimp only [allocSStep, cntXDS, cntXD]
  let newSrc := fun u => if u = st.m then some (Sum.inr (e, i, false)) else st.source u
  have hact : ∀ u < st.m, actFn on lit newSrc u = actFn on lit st.source u := by
    intro u hu
    have hne : u ≠ st.m := by omega
    simp [actFn, newSrc, hne]
  have h := card_extend_mul st.m 1 st.edges ∅ (actFn on lit st.source) (actFn on lit newSrc)
    hinv.xinv.wf.edges_lt hact
    (fun v1 => (fun j => v1 ⟨xCur j, hinv.xinv.x_lt j⟩) = y ∧ v1 ⟨det, hinv.det_lt⟩ = d)
    (fun v => (fun j => v ⟨xCur j, by have := hinv.xinv.x_lt j; omega⟩) = y ∧
      v ⟨det, by have := hinv.det_lt; omega⟩ = d ∧ v ⟨st.m, by omega⟩ = sb)
    (if lit e i false = false ∧ sb = true then 0 else 1)
    (by
      intro v1 v2 _ _ ⟨hy, hd, _⟩
      refine ⟨?_, ?_⟩
      · funext j
        have h1 := congrFun hy j
        rwa [joinV_lt v1 v2 (xCur j) (hinv.xinv.x_lt j)] at h1
      · rwa [joinV_lt v1 v2 det hinv.det_lt] at hd)
    (by
      intro v1 _ ⟨hy, hd⟩
      have hcf := card_filter_unique
        (fun v2 : Fin 1 → Bool => StepValid st.m 1 ∅ (actFn on lit newSrc) v1 v2 ∧
          (fun j => joinV v1 v2 ⟨xCur j, by have := hinv.xinv.x_lt j; omega⟩) = y ∧
          joinV v1 v2 ⟨det, by have := hinv.det_lt; omega⟩ = d ∧
          joinV v1 v2 ⟨st.m, by omega⟩ = sb)
        (fun _ => sb) (¬ (lit e i false = false ∧ sb = true))
        (by
          intro v2
          constructor
          · intro ⟨⟨hz, _⟩, _, _, hvs⟩
            have h0 : v2 0 = sb := by
              have hg := joinV_ge v1 v2 (0 : Fin 1) (by omega)
              simp only [Fin.val_zero, Nat.add_zero] at hg
              rw [← hg, hvs]
            have heq : v2 = fun _ => sb := by
              funext j
              have hj : j = 0 := Fin.ext (by omega)
              subst hj; exact h0
            refine ⟨heq, ?_⟩
            intro ⟨hlit, hsb⟩
            have hv0 := hz 0 (by simp [actFn, newSrc, hlit])
            rw [h0, hsb] at hv0
            contradiction
          · intro ⟨hv2, hnr⟩
            subst hv2
            refine ⟨⟨?_, by simp⟩, ?_, ?_, ?_⟩
            · intro j hj
              have hj0 : j.val = 0 := by omega
              have hlit : lit e i false = false := by simpa [actFn, newSrc, hj0] using hj
              cases hsb : sb
              · rfl
              · exact absurd ⟨hlit, hsb⟩ hnr
            · funext j
              rw [joinV_lt v1 (fun _ => sb) (xCur j) (hinv.xinv.x_lt j)]
              exact congrFun hy j
            · rw [joinV_lt v1 (fun _ => sb) det hinv.det_lt]
              exact hd
            · have hg := joinV_ge v1 (fun _ => sb) (0 : Fin 1) (by omega)
              simpa using hg)
      rw [hcf]
      by_cases hc : lit e i false = false ∧ sb = true <;> simp [hc])
  simpa [Finset.union_empty] using h

private def negEdges1 (xi px xi' s ps s' lr : Nat) : Finset (Nat × Nat) :=
  {(xi, px), (px, xi'), (xi', xi), (s, ps), (ps, s'), (s', s), (lr, px), (lr, ps)}

private def negEdges2 (px ps ur : Nat) : Finset (Nat × Nat) :=
  {(px, ur), (ps, ur)}

private lemma negEdges1_deg {m xi s : Nat} (hxi : xi < m) (hs : s < m) (hne : xi ≠ s) :
    let newE := negEdges1 xi m (m + 1) s (m + 2) (m + 3) (m + 4)
    (∀ u < m, u ≠ xi → u ≠ s → inDeg newE u = 0 ∧ outDeg newE u = 0) ∧
    (inDeg newE xi ≤ 1 ∧ outDeg newE xi ≤ 1) ∧
    (inDeg newE s ≤ 1 ∧ outDeg newE s ≤ 1) ∧
    (inDeg newE m ≤ 2 ∧ outDeg newE m ≤ 1) ∧
    (inDeg newE (m + 1) ≤ 1 ∧ outDeg newE (m + 1) ≤ 1) ∧
    (inDeg newE (m + 2) ≤ 2 ∧ outDeg newE (m + 2) ≤ 1) ∧
    (inDeg newE (m + 3) ≤ 1 ∧ outDeg newE (m + 3) ≤ 1) ∧
    (inDeg newE (m + 4) ≤ 2 ∧ outDeg newE (m + 4) ≤ 2) := by
  dsimp only
  refine ⟨?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro u hu hux hus
    refine ⟨card_filter_empty _ _ ?_, card_filter_empty _ _ ?_⟩ <;>
      · intro ed hed
        simp only [negEdges1, mem_insert, mem_singleton] at hed
        rcases hed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp <;> omega
  · apply card_filter_subset_single _ _ (m + 1, xi)
    intro ed hed h2
    simp only [negEdges1, mem_insert, mem_singleton] at hed
    rcases hed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | rfl | (dsimp at h2; omega)
  · apply card_filter_subset_single _ _ (xi, m)
    intro ed hed h1
    simp only [negEdges1, mem_insert, mem_singleton] at hed
    rcases hed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | rfl | (dsimp at h1; omega)
  · apply card_filter_subset_single _ _ (m + 3, s)
    intro ed hed h2
    simp only [negEdges1, mem_insert, mem_singleton] at hed
    rcases hed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | rfl | (dsimp at h2; omega)
  · apply card_filter_subset_single _ _ (s, m + 2)
    intro ed hed h1
    simp only [negEdges1, mem_insert, mem_singleton] at hed
    rcases hed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | rfl | (dsimp at h1; omega)
  · apply card_filter_subset_pair _ _ (xi, m) (m + 4, m)
    intro ed hed h2
    simp only [negEdges1, mem_insert, mem_singleton] at hed
    rcases hed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact Or.inl rfl | exact Or.inr rfl | (dsimp at h2; omega)
  · apply card_filter_subset_single _ _ (m, m + 1)
    intro ed hed h1
    simp only [negEdges1, mem_insert, mem_singleton] at hed
    rcases hed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | rfl | (dsimp at h1; omega)
  · apply card_filter_subset_single _ _ (m, m + 1)
    intro ed hed h2
    simp only [negEdges1, mem_insert, mem_singleton] at hed
    rcases hed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | rfl | (dsimp at h2; omega)
  · apply card_filter_subset_single _ _ (m + 1, xi)
    intro ed hed h1
    simp only [negEdges1, mem_insert, mem_singleton] at hed
    rcases hed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | rfl | (dsimp at h1; omega)
  · apply card_filter_subset_pair _ _ (s, m + 2) (m + 4, m + 2)
    intro ed hed h2
    simp only [negEdges1, mem_insert, mem_singleton] at hed
    rcases hed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact Or.inl rfl | exact Or.inr rfl | (dsimp at h2; omega)
  · apply card_filter_subset_single _ _ (m + 2, m + 3)
    intro ed hed h1
    simp only [negEdges1, mem_insert, mem_singleton] at hed
    rcases hed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | rfl | (dsimp at h1; omega)
  · apply card_filter_subset_single _ _ (m + 2, m + 3)
    intro ed hed h2
    simp only [negEdges1, mem_insert, mem_singleton] at hed
    rcases hed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | rfl | (dsimp at h2; omega)
  · apply card_filter_subset_single _ _ (m + 3, s)
    intro ed hed h1
    simp only [negEdges1, mem_insert, mem_singleton] at hed
    rcases hed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | rfl | (dsimp at h1; omega)
  · have : inDeg (negEdges1 xi m (m + 1) s (m + 2) (m + 3) (m + 4)) (m + 4) = 0 := by
      apply card_filter_empty
      intro ed hed
      simp only [negEdges1, mem_insert, mem_singleton] at hed
      rcases hed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp <;> omega
    omega
  · apply card_filter_subset_pair _ _ (m + 4, m) (m + 4, m + 2)
    intro ed hed h1
    simp only [negEdges1, mem_insert, mem_singleton] at hed
    rcases hed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact Or.inl rfl | exact Or.inr rfl | (dsimp at h1; omega)

private lemma negEdges2_deg (m : Nat) :
    let newE := negEdges2 m (m + 2) (m + 5)
    (∀ u < m + 5, u ≠ m → u ≠ m + 2 → inDeg newE u = 0 ∧ outDeg newE u = 0) ∧
    (inDeg newE m = 0 ∧ outDeg newE m ≤ 1) ∧
    (inDeg newE (m + 2) = 0 ∧ outDeg newE (m + 2) ≤ 1) ∧
    (inDeg newE (m + 5) ≤ 2 ∧ outDeg newE (m + 5) = 0) := by
  dsimp only
  refine ⟨?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro u hu h1 h2
    refine ⟨card_filter_empty _ _ ?_, card_filter_empty _ _ ?_⟩ <;>
      · intro ed hed
        simp only [negEdges2, mem_insert, mem_singleton] at hed
        rcases hed with rfl | rfl <;> dsimp <;> omega
  · apply card_filter_empty
    intro ed hed
    simp only [negEdges2, mem_insert, mem_singleton] at hed
    rcases hed with rfl | rfl <;> dsimp <;> omega
  · apply card_filter_subset_single _ _ (m, m + 5)
    intro ed hed h1
    simp only [negEdges2, mem_insert, mem_singleton] at hed
    rcases hed with rfl | rfl <;> first | rfl | (dsimp at h1; omega)
  · apply card_filter_empty
    intro ed hed
    simp only [negEdges2, mem_insert, mem_singleton] at hed
    rcases hed with rfl | rfl <;> dsimp <;> omega
  · apply card_filter_subset_single _ _ (m + 2, m + 5)
    intro ed hed h1
    simp only [negEdges2, mem_insert, mem_singleton] at hed
    rcases hed with rfl | rfl <;> first | rfl | (dsimp at h1; omega)
  · apply card_filter_subset_pair _ _ (m, m + 5) (m + 2, m + 5)
    intro ed hed h2
    simp only [negEdges2, mem_insert, mem_singleton] at hed
    rcases hed with rfl | rfl <;> first | exact Or.inl rfl | exact Or.inr rfl
  · apply card_filter_empty
    intro ed hed
    simp only [negEdges2, mem_insert, mem_singleton] at hed
    rcases hed with rfl | rfl <;> dsimp <;> omega

private def negUnitHalf1 {n k : Nat} (e : Fin k) (i : Fin n) (st : GState n k)
    (xCur : Fin n → Nat) (det s : Nat) : GState n k × (Fin n → Nat) × Nat :=
  let m := st.m
  let xi := xCur i
  let newE := negEdges1 xi m (m + 1) s (m + 2) (m + 3) (m + 4)
  let newSrc := fun u =>
    if u = m ∨ u = m + 1 then none
    else if u = m + 2 ∨ u = m + 3 ∨ u = m + 4 then some (Sum.inr (e, i, false))
    else st.source u
  let newBag := insert (m + 4) (insert (m + 3) (insert (m + 2)
    (insert (m + 1) (insert m (insert s (insert det (Finset.univ.image xCur)))))))
  (⟨m + 5, st.edges ∪ newE, newSrc, st.bags ++ [newBag]⟩,
    Function.update xCur i (m + 1), m + 3)

private def negUnitHalf2 {n k : Nat} (e : Fin k) (i : Fin n) (m0 : Nat) (st1 : GState n k)
    (xCur1 : Fin n → Nat) (det s1 : Nat) : GState n k :=
  let newE := negEdges2 m0 (m0 + 2) (m0 + 5)
  let newSrc := fun u =>
    if u = m0 + 5 then some (Sum.inr (e, i, false)) else st1.source u
  let newBag := insert (m0 + 5) (insert (m0 + 2) (insert m0
    (insert s1 (insert det (Finset.univ.image xCur1)))))
  ⟨st1.m + 1, st1.edges ∪ newE, newSrc, st1.bags ++ [newBag]⟩

private def negUnitStep {n k : Nat} (e : Fin k) (i : Fin n) (st : GState n k)
    (xCur : Fin n → Nat) (det s : Nat) : GState n k × (Fin n → Nat) × Nat :=
  let r1 := negUnitHalf1 e i st xCur det s
  let st2 := negUnitHalf2 e i st.m r1.1 r1.2.1 det r1.2.2
  (st2, r1.2.1, r1.2.2)

private lemma negUnitHalf1_inv {n k : Nat} (e : Fin k) (i : Fin n) (st : GState n k)
    (xCur : Fin n → Nat) (det s : Nat) (hinv : NegInv n k e i st xCur det s) :
    let r1 := negUnitHalf1 e i st xCur det s
    NegInv n k e i r1.1 r1.2.1 det r1.2.2 ∧
    (inDeg r1.1.edges st.m ≤ 2 ∧ outDeg r1.1.edges st.m ≤ 1) ∧
    (inDeg r1.1.edges (st.m + 2) ≤ 2 ∧ outDeg r1.1.edges (st.m + 2) ≤ 1) ∧
    st.m ∈ r1.1.bags.getLast (by dsimp only [r1, negUnitHalf1]; simp) ∧
    st.m + 2 ∈ r1.1.bags.getLast (by dsimp only [r1, negUnitHalf1]; simp) := by
  dsimp only [negUnitHalf1]
  have hxi := hinv.dinv.xinv.x_lt i
  have hs := hinv.s_lt
  have hne := hinv.s_ne_x i
  have hdeg := negEdges1_deg hxi hs hne
  let newE := negEdges1 (xCur i) st.m (st.m + 1) s (st.m + 2) (st.m + 3) (st.m + 4)
  let newBag := insert (st.m + 4) (insert (st.m + 3) (insert (st.m + 2)
    (insert (st.m + 1) (insert st.m (insert s (insert det (Finset.univ.image xCur)))))))
  have hdisj : Disjoint st.edges newE := by
    rw [Finset.disjoint_left]
    intro ed he1 he2
    have hlt := hinv.dinv.xinv.wf.edges_lt ed he1
    simp only [newE, negEdges1, mem_insert, mem_singleton] at he2
    rcases he2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp at hlt <;> omega
  have hwf : WellFormed n k ⟨st.m + 5, st.edges ∪ newE,
      fun u => if u = st.m ∨ u = st.m + 1 then none
        else if u = st.m + 2 ∨ u = st.m + 3 ∨ u = st.m + 4 then some (Sum.inr (e, i, false))
        else st.source u,
      st.bags ++ [newBag]⟩ := by
    apply extend_wellFormed st hinv.dinv.xinv.wf 5 (by omega) newE _ newBag
    · intro ed hed
      simp only [newE, negEdges1, mem_insert, mem_singleton] at hed
      rcases hed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp <;> omega
    · intro ed hed
      simp only [newE, negEdges1, mem_insert, mem_singleton] at hed
      rcases hed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp <;> omega
    · intro u hu
      dsimp only [newE]
      by_cases h1 : u = xCur i
      · subst h1
        rcases hinv.dinv.xinv.x_deg i with ⟨ha1, ha2⟩
        rcases hdeg.2.1 with ⟨hb1, hb2⟩
        exact ⟨by omega, by omega⟩
      · by_cases h2 : u = s
        · subst h2
          rcases hinv.s_deg with ⟨ha1, ha2⟩
          rcases hdeg.2.2.1 with ⟨hb1, hb2⟩
          exact ⟨by omega, by omega⟩
        · rcases hdeg.1 u hu h1 h2 with ⟨hb1, hb2⟩
          rcases hinv.dinv.xinv.wf.deg_le u hu with ⟨ha1, ha2⟩
          exact ⟨by omega, by omega⟩
    · intro u hge hlt
      dsimp only [newE]
      have hc : u = st.m ∨ u = st.m + 1 ∨ u = st.m + 2 ∨ u = st.m + 3 ∨ u = st.m + 4 := by omega
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · rcases hdeg.2.2.2.1 with ⟨h1, h2⟩; exact ⟨by omega, by omega⟩
      · rcases hdeg.2.2.2.2.1 with ⟨h1, h2⟩; exact ⟨by omega, by omega⟩
      · rcases hdeg.2.2.2.2.2.1 with ⟨h1, h2⟩; exact ⟨by omega, by omega⟩
      · rcases hdeg.2.2.2.2.2.2.1 with ⟨h1, h2⟩; exact ⟨by omega, by omega⟩
      · exact hdeg.2.2.2.2.2.2.2
    · have hallX : (Finset.univ.image xCur).card ≤ n := by
        calc (Finset.univ.image xCur).card ≤ (Finset.univ : Finset (Fin n)).card := card_image_le
          _ = n := Fintype.card_fin n
      have h1 := card_insert_le (st.m + 4) (insert (st.m + 3) (insert (st.m + 2)
        (insert (st.m + 1) (insert st.m (insert s (insert det (Finset.univ.image xCur)))))))
      have h2 := card_insert_le (st.m + 3) (insert (st.m + 2)
        (insert (st.m + 1) (insert st.m (insert s (insert det (Finset.univ.image xCur))))))
      have h3 := card_insert_le (st.m + 2)
        (insert (st.m + 1) (insert st.m (insert s (insert det (Finset.univ.image xCur)))))
      have h4 := card_insert_le (st.m + 1) (insert st.m (insert s (insert det (Finset.univ.image xCur))))
      have h5 := card_insert_le st.m (insert s (insert det (Finset.univ.image xCur)))
      have h6 := card_insert_le s (insert det (Finset.univ.image xCur))
      have h7 := card_insert_le det (Finset.univ.image xCur)
      dsimp only [newBag]
      omega
    · intro u hu
      simp only [newBag, mem_insert, mem_image, mem_univ, true_and] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨j, rfl⟩
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · have := hinv.dinv.det_lt; omega
      · have := hinv.dinv.xinv.x_lt j; omega
    · intro u hge hlt
      have hc : u = st.m ∨ u = st.m + 1 ∨ u = st.m + 2 ∨ u = st.m + 3 ∨ u = st.m + 4 := by omega
      rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp [newBag]
    · intro u hu hlt
      simp only [newBag, mem_insert, mem_image, mem_univ, true_and] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨j, rfl⟩
      · omega
      · omega
      · omega
      · omega
      · omega
      · exact hinv.s_bag
      · exact hinv.dinv.det_bag
      · exact hinv.dinv.xinv.x_bag j
    · intro ed hed
      have hxim : xCur i ∈ Finset.univ.image xCur := mem_image_of_mem xCur (mem_univ i)
      simp only [newE, negEdges1, mem_insert, mem_singleton] at hed
      rcases hed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [newBag, hxim]
  have hxinv : XInv n k ⟨st.m + 5, st.edges ∪ newE,
      fun u => if u = st.m ∨ u = st.m + 1 then none
        else if u = st.m + 2 ∨ u = st.m + 3 ∨ u = st.m + 4 then some (Sum.inr (e, i, false))
        else st.source u,
      st.bags ++ [newBag]⟩ (Function.update xCur i (st.m + 1)) :=
    { wf := hwf
      x_lt := fun j => by
        dsimp only
        by_cases hji : j = i
        · subst hji; simp
        · simp [Function.update, hji]; have := hinv.dinv.xinv.x_lt j; omega
      x_inj := by
        intro j1 j2 heq
        by_cases h1 : j1 = i <;> by_cases h2 : j2 = i
        · rw [h1, h2]
        · simp [Function.update, h1, h2] at heq; have := hinv.dinv.xinv.x_lt j2; omega
        · simp [Function.update, h1, h2] at heq; have := hinv.dinv.xinv.x_lt j1; omega
        · simp [Function.update, h1, h2] at heq; exact hinv.dinv.xinv.x_inj heq
      x_deg := fun j => by
        dsimp only
        rw [inDeg_union_of_disjoint hdisj, outDeg_union_of_disjoint hdisj]
        by_cases hji : j = i
        · subst hji
          simp only [Function.update_self]
          rw [inDeg_eq_zero_of_ge hinv.dinv.xinv.wf.edges_lt (by omega),
            outDeg_eq_zero_of_ge hinv.dinv.xinv.wf.edges_lt (by omega), Nat.zero_add, Nat.zero_add]
          exact hdeg.2.2.2.2.1
        · simp only [Function.update_of_ne hji]
          dsimp only [newE]
          have h1 : xCur j ≠ xCur i := fun h => hji (hinv.dinv.xinv.x_inj h)
          have h2 : xCur j ≠ s := hinv.s_ne_x j
          rcases hdeg.1 (xCur j) (hinv.dinv.xinv.x_lt j) h1 h2 with ⟨hb1, hb2⟩
          rcases hinv.dinv.xinv.x_deg j with ⟨ha1, ha2⟩
          exact ⟨by omega, by omega⟩
      x_src := fun j => by
        dsimp only
        by_cases hji : j = i
        · subst hji; simp
        · simp only [Function.update_of_ne hji]
          have hlt := hinv.dinv.xinv.x_lt j
          have h1 : ¬ (xCur j = st.m ∨ xCur j = st.m + 1) := by omega
          have h2 : ¬ (xCur j = st.m + 2 ∨ xCur j = st.m + 3 ∨ xCur j = st.m + 4) := by omega
          simp [h1, h2, hinv.dinv.xinv.x_src j]
      x_bag := fun j => by
        dsimp only
        rw [List.getLast_append_singleton]
        by_cases hji : j = i
        · subst hji; simp [newBag]
        · simp only [Function.update_of_ne hji]
          have hjm : xCur j ∈ Finset.univ.image xCur := mem_image_of_mem xCur (mem_univ j)
          simp [newBag, hjm] }
  have hdinv : DetInv n k e _ (Function.update xCur i (st.m + 1)) det :=
    { xinv := hxinv
      det_lt := by dsimp only; have := hinv.dinv.det_lt; omega
      det_ne := fun j => by
        by_cases hji : j = i
        · subst hji; simp only [Function.update_self]; have := hinv.dinv.det_lt; omega
        · simp only [Function.update_of_ne hji]; exact hinv.dinv.det_ne j
      det_deg := by
        dsimp only
        rw [inDeg_union_of_disjoint hdisj, outDeg_union_of_disjoint hdisj]
        dsimp only [newE]
        rcases hdeg.1 det hinv.dinv.det_lt (hinv.dinv.det_ne i).symm hinv.s_ne_det with ⟨hb1, hb2⟩
        rcases hinv.dinv.det_deg with ⟨ha1, ha2⟩
        exact ⟨by omega, by omega⟩
      det_src := by
        dsimp only
        have hlt := hinv.dinv.det_lt
        have h1 : ¬ (det = st.m ∨ det = st.m + 1) := by omega
        have h2 : ¬ (det = st.m + 2 ∨ det = st.m + 3 ∨ det = st.m + 4) := by omega
        simp [h1, h2, hinv.dinv.det_src]
      det_bag := by
        dsimp only
        rw [List.getLast_append_singleton]
        simp [newBag] }
  have hninv : NegInv n k e i _ (Function.update xCur i (st.m + 1)) det (st.m + 3) :=
    { dinv := hdinv
      s_lt := by dsimp only; omega
      s_ne_x := fun j => by
        by_cases hji : j = i
        · subst hji; simp
        · simp only [Function.update_of_ne hji]; have := hinv.dinv.xinv.x_lt j; omega
      s_ne_det := by have := hinv.dinv.det_lt; omega
      s_deg := by
        dsimp only
        rw [inDeg_union_of_disjoint hdisj, outDeg_union_of_disjoint hdisj,
          inDeg_eq_zero_of_ge hinv.dinv.xinv.wf.edges_lt (by omega),
          outDeg_eq_zero_of_ge hinv.dinv.xinv.wf.edges_lt (by omega), Nat.zero_add, Nat.zero_add]
        exact hdeg.2.2.2.2.2.2.1
      s_src := by simp
      s_bag := by
        dsimp only
        rw [List.getLast_append_singleton]
        simp [newBag] }
  refine ⟨hninv, ?_, ?_, ?_, ?_⟩
  · rw [inDeg_union_of_disjoint hdisj, outDeg_union_of_disjoint hdisj,
      inDeg_eq_zero_of_ge hinv.dinv.xinv.wf.edges_lt (by omega),
      outDeg_eq_zero_of_ge hinv.dinv.xinv.wf.edges_lt (by omega), Nat.zero_add, Nat.zero_add]
    exact hdeg.2.2.2.1
  · rw [inDeg_union_of_disjoint hdisj, outDeg_union_of_disjoint hdisj,
      inDeg_eq_zero_of_ge hinv.dinv.xinv.wf.edges_lt (by omega),
      outDeg_eq_zero_of_ge hinv.dinv.xinv.wf.edges_lt (by omega), Nat.zero_add, Nat.zero_add]
    exact hdeg.2.2.2.2.2.1
  · rw [List.getLast_append_singleton]; simp [newBag]
  · rw [List.getLast_append_singleton]; simp [newBag]

private lemma negUnitStep_inv {n k : Nat} (e : Fin k) (i : Fin n) (st : GState n k)
    (xCur : Fin n → Nat) (det s : Nat) (hinv : NegInv n k e i st xCur det s) :
    let res := negUnitStep e i st xCur det s
    NegInv n k e i res.1 res.2.1 det res.2.2 := by
  dsimp only [negUnitStep]
  have hr1 := negUnitHalf1_inv e i st xCur det s hinv
  rcases hr1 with ⟨hn1, hdeg_px, hdeg_ps, hbag_px, hbag_ps⟩
  set r1 := negUnitHalf1 e i st xCur det s
  have hm1 : r1.1.m = st.m + 5 := rfl
  have hdeg2 := negEdges2_deg st.m
  dsimp only [negUnitHalf2]
  let newE := negEdges2 st.m (st.m + 2) (st.m + 5)
  let newBag := insert (st.m + 5) (insert (st.m + 2) (insert st.m
    (insert r1.2.2 (insert det (Finset.univ.image r1.2.1)))))
  have hdisj : Disjoint r1.1.edges newE := by
    rw [Finset.disjoint_left]
    intro ed he1 he2
    have hlt := hn1.dinv.xinv.wf.edges_lt ed he1
    simp only [newE, negEdges2, mem_insert, mem_singleton] at he2
    rcases he2 with rfl | rfl <;> dsimp at hlt <;> omega
  have hwf : WellFormed n k ⟨r1.1.m + 1, r1.1.edges ∪ newE,
      fun u => if u = st.m + 5 then some (Sum.inr (e, i, false)) else r1.1.source u,
      r1.1.bags ++ [newBag]⟩ := by
    apply extend_wellFormed r1.1 hn1.dinv.xinv.wf 1 (by omega) newE _ newBag
    · intro ed hed
      simp only [newE, negEdges2, mem_insert, mem_singleton] at hed
      rcases hed with rfl | rfl <;> dsimp <;> omega
    · intro ed hed
      simp only [newE, negEdges2, mem_insert, mem_singleton] at hed
      rcases hed with rfl | rfl <;> dsimp <;> omega
    · intro u hu
      dsimp only [newE]
      by_cases h1 : u = st.m
      · subst h1
        rcases hdeg_px with ⟨ha1, ha2⟩
        rcases hdeg2.2.1 with ⟨hb1, hb2⟩
        exact ⟨by omega, by omega⟩
      · by_cases h2 : u = st.m + 2
        · subst h2
          rcases hdeg_ps with ⟨ha1, ha2⟩
          rcases hdeg2.2.2.1 with ⟨hb1, hb2⟩
          exact ⟨by omega, by omega⟩
        · rcases hdeg2.1 u (by omega) h1 h2 with ⟨hb1, hb2⟩
          rcases hn1.dinv.xinv.wf.deg_le u hu with ⟨ha1, ha2⟩
          exact ⟨by omega, by omega⟩
    · intro u hge hlt
      dsimp only [newE]
      have hu : u = st.m + 5 := by omega
      subst hu
      rcases hdeg2.2.2.2 with ⟨h1, h2⟩
      exact ⟨by omega, by omega⟩
    · have hallX : (Finset.univ.image r1.2.1).card ≤ n := by
        calc (Finset.univ.image r1.2.1).card ≤ (Finset.univ : Finset (Fin n)).card := card_image_le
          _ = n := Fintype.card_fin n
      have h1 := card_insert_le (st.m + 5) (insert (st.m + 2) (insert st.m
        (insert r1.2.2 (insert det (Finset.univ.image r1.2.1)))))
      have h2 := card_insert_le (st.m + 2) (insert st.m
        (insert r1.2.2 (insert det (Finset.univ.image r1.2.1))))
      have h3 := card_insert_le st.m (insert r1.2.2 (insert det (Finset.univ.image r1.2.1)))
      have h4 := card_insert_le r1.2.2 (insert det (Finset.univ.image r1.2.1))
      have h5 := card_insert_le det (Finset.univ.image r1.2.1)
      dsimp only [newBag]
      omega
    · intro u hu
      simp only [newBag, mem_insert, mem_image, mem_univ, true_and] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | ⟨j, rfl⟩
      · omega
      · omega
      · omega
      · have := hn1.s_lt; omega
      · have := hn1.dinv.det_lt; omega
      · have := hn1.dinv.xinv.x_lt j; omega
    · intro u hge hlt
      have hu : u = st.m + 5 := by omega
      subst hu; simp [newBag]
    · intro u hu hlt
      simp only [newBag, mem_insert, mem_image, mem_univ, true_and] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | ⟨j, rfl⟩
      · omega
      · exact hbag_ps
      · exact hbag_px
      · exact hn1.s_bag
      · exact hn1.dinv.det_bag
      · exact hn1.dinv.xinv.x_bag j
    · intro ed hed
      simp only [newE, negEdges2, mem_insert, mem_singleton] at hed
      rcases hed with rfl | rfl <;> simp [newBag]
  have hx_ne : ∀ j, r1.2.1 j ≠ st.m ∧ r1.2.1 j ≠ st.m + 2 := by
    intro j
    by_cases hji : j = i
    · subst hji; change (Function.update xCur j (st.m + 1) j) ≠ st.m ∧
        (Function.update xCur j (st.m + 1) j) ≠ st.m + 2
      simp
    · change (Function.update xCur i (st.m + 1) j) ≠ st.m ∧
        (Function.update xCur i (st.m + 1) j) ≠ st.m + 2
      simp only [Function.update_of_ne hji]
      have := hinv.dinv.xinv.x_lt j; omega
  have hxinv : XInv n k ⟨r1.1.m + 1, r1.1.edges ∪ newE,
      fun u => if u = st.m + 5 then some (Sum.inr (e, i, false)) else r1.1.source u,
      r1.1.bags ++ [newBag]⟩ r1.2.1 :=
    { wf := hwf
      x_lt := fun j => by dsimp only; have := hn1.dinv.xinv.x_lt j; omega
      x_inj := hn1.dinv.xinv.x_inj
      x_deg := fun j => by
        dsimp only
        rw [inDeg_union_of_disjoint hdisj, outDeg_union_of_disjoint hdisj]
        dsimp only [newE]
        have hne := hx_ne j
        rcases hdeg2.1 (r1.2.1 j) (by have := hn1.dinv.xinv.x_lt j; omega) hne.1 hne.2 with ⟨hb1, hb2⟩
        rcases hn1.dinv.xinv.x_deg j with ⟨ha1, ha2⟩
        exact ⟨by omega, by omega⟩
      x_src := fun j => by
        dsimp only
        have hlt := hn1.dinv.xinv.x_lt j
        have hne : r1.2.1 j ≠ st.m + 5 := by omega
        simp [hne, hn1.dinv.xinv.x_src j]
      x_bag := fun j => by
        dsimp only
        rw [List.getLast_append_singleton]
        have hjm : r1.2.1 j ∈ Finset.univ.image r1.2.1 := mem_image_of_mem r1.2.1 (mem_univ j)
        simp [newBag, hjm] }
  have hdinv : DetInv n k e _ r1.2.1 det :=
    { xinv := hxinv
      det_lt := by dsimp only; have := hn1.dinv.det_lt; omega
      det_ne := hn1.dinv.det_ne
      det_deg := by
        dsimp only
        rw [inDeg_union_of_disjoint hdisj, outDeg_union_of_disjoint hdisj]
        dsimp only [newE]
        have hlt := hinv.dinv.det_lt
        rcases hdeg2.1 det (by omega) (by omega) (by omega) with ⟨hb1, hb2⟩
        rcases hn1.dinv.det_deg with ⟨ha1, ha2⟩
        exact ⟨by omega, by omega⟩
      det_src := by
        dsimp only
        have hlt := hn1.dinv.det_lt
        have hne : det ≠ st.m + 5 := by omega
        simp [hne, hn1.dinv.det_src]
      det_bag := by
        dsimp only
        rw [List.getLast_append_singleton]; simp [newBag] }
  refine
    { dinv := hdinv
      s_lt := by dsimp only; have := hn1.s_lt; omega
      s_ne_x := hn1.s_ne_x
      s_ne_det := hn1.s_ne_det
      s_deg := by
        dsimp only
        rw [inDeg_union_of_disjoint hdisj, outDeg_union_of_disjoint hdisj]
        dsimp only [newE]
        have hs1 : r1.2.2 = st.m + 3 := rfl
        rcases hdeg2.1 r1.2.2 (by omega) (by omega) (by omega) with ⟨hb1, hb2⟩
        rcases hn1.s_deg with ⟨ha1, ha2⟩
        exact ⟨by omega, by omega⟩
      s_src := by
        dsimp only
        have hs1 : r1.2.2 = st.m + 3 := rfl
        have hne : r1.2.2 ≠ st.m + 5 := by omega
        simp [hne, hn1.s_src]
      s_bag := by
        dsimp only
        rw [List.getLast_append_singleton]; simp [newBag] }

private lemma negUnitHalf1_cnt {n k : Nat} (on : Fin k → Bool) (lit : Fin k → Fin n → Bool → Bool)
    (e : Fin k) (i : Fin n) (st : GState n k) (xCur : Fin n → Nat) (det s : Nat)
    (hinv : NegInv n k e i st xCur det s) (y : Fin n → Bool) (d sb : Bool) :
    let r1 := negUnitHalf1 e i st xCur det s
    let hr1 := (negUnitHalf1_inv e i st xCur det s hinv).1
    cntXDS on lit r1.1 r1.2.1 hr1.dinv.xinv.x_lt det hr1.dinv.det_lt r1.2.2 hr1.s_lt y d sb =
      cntXDS on lit st xCur hinv.dinv.xinv.x_lt det hinv.dinv.det_lt s hinv.s_lt y d sb *
        (if lit e i false = true ∧ y i = true ∧ sb = true then 2 else 1) := by
  dsimp only [negUnitHalf1, cntXDS]
  let m := st.m
  let xi := xCur i
  let newE := negEdges1 xi m (m + 1) s (m + 2) (m + 3) (m + 4)
  let newSrc : Nat → Option (Fin k ⊕ (Fin k × Fin n × Bool)) := fun u =>
    if u = m ∨ u = m + 1 then none
    else if u = m + 2 ∨ u = m + 3 ∨ u = m + 4 then some (Sum.inr (e, i, false))
    else st.source u
  have hact_old : ∀ u < m, actFn on lit newSrc u = actFn on lit st.source u := by
    intro u hu
    have h1 : ¬ (u = m ∨ u = m + 1) := by omega
    have h2 : ¬ (u = m + 2 ∨ u = m + 3 ∨ u = m + 4) := by omega
    simp [actFn, newSrc, h1, h2]
  have hxi_lt : xi < m := hinv.dinv.xinv.x_lt i
  have hdet_lt : det < m := hinv.dinv.det_lt
  have hs_lt : s < m := hinv.s_lt
  have hact_xi : actFn on lit newSrc xi = true := by
    dsimp only [xi]
    rw [hact_old (xCur i) hxi_lt]; simp [actFn, hinv.dinv.xinv.x_src i]
  have hact_s : actFn on lit newSrc s = lit e i false := by
    rw [hact_old s hs_lt]; simp [actFn, hinv.s_src]
  have hact0 : actFn on lit newSrc m = true := by simp [actFn, newSrc]
  have hact1 : actFn on lit newSrc (m + 1) = true := by simp [actFn, newSrc]
  have hact2 : actFn on lit newSrc (m + 2) = lit e i false := by
    have h1 : ¬ (m + 2 = m ∨ m + 2 = m + 1) := by omega
    simp [actFn, newSrc, h1]
  have hact3 : actFn on lit newSrc (m + 3) = lit e i false := by
    have h1 : ¬ (m + 3 = m ∨ m + 3 = m + 1) := by omega
    simp [actFn, newSrc, h1]
  have hact4 : actFn on lit newSrc (m + 4) = lit e i false := by
    have h1 : ¬ (m + 4 = m ∨ m + 4 = m + 1) := by omega
    simp [actFn, newSrc, h1]
  have hchar : ∀ (v1 : Fin m → Bool) (v2 : Fin 5 → Bool),
      ValidV m st.edges (actFn on lit st.source) v1 →
      (StepValid m 5 newE (actFn on lit newSrc) v1 v2 ↔
        v2 0 = v1 ⟨xi, hxi_lt⟩ ∧
        v2 1 = v1 ⟨xi, hxi_lt⟩ ∧
        v2 2 = v1 ⟨s, hs_lt⟩ ∧
        v2 3 = v1 ⟨s, hs_lt⟩ ∧
        (v2 4 = true → lit e i false = true ∧ v1 ⟨xi, hxi_lt⟩ = true ∧ v1 ⟨s, hs_lt⟩ = true)) := by
    intro v1 v2 hv1
    have hs_zero : lit e i false = false → v1 ⟨s, hs_lt⟩ = false := by
      intro hlit
      exact hv1.1 ⟨s, hs_lt⟩ (by simp [actFn, hinv.s_src, hlit])
    constructor
    · intro ⟨hz, himp⟩
      have he1 : (xi, m) ∈ newE := by simp [newE, negEdges1]
      have he2 : (m, m + 1) ∈ newE := by simp [newE, negEdges1]
      have he3 : (m + 1, xi) ∈ newE := by simp [newE, negEdges1]
      have he4 : (s, m + 2) ∈ newE := by simp [newE, negEdges1]
      have he5 : (m + 2, m + 3) ∈ newE := by simp [newE, negEdges1]
      have he6 : (m + 3, s) ∈ newE := by simp [newE, negEdges1]
      have he7 : (m + 4, m) ∈ newE := by simp [newE, negEdges1]
      have he8 : (m + 4, m + 2) ∈ newE := by simp [newE, negEdges1]
      have hi1 : v1 ⟨xi, hxi_lt⟩ = true → v2 0 = true := by
        intro h
        have := stepImp himp he1 (by omega) (by omega) hact_xi hact0
          (by rw [joinV_lt v1 v2 xi hxi_lt]; exact h)
        rwa [joinV_m v1 v2] at this
      have hi2 : v2 0 = true → v2 1 = true := by
        intro h
        have := stepImp himp he2 (by omega) (by omega) hact0 hact1
          (by rw [joinV_m v1 v2]; exact h)
        rwa [joinV_nat v1 v2 1 1 rfl] at this
      have hi3 : v2 1 = true → v1 ⟨xi, hxi_lt⟩ = true := by
        intro h
        have := stepImp himp he3 (by omega) (by omega) hact1 hact_xi
          (by rw [joinV_nat v1 v2 1 1 rfl]; exact h)
        rwa [joinV_lt v1 v2 xi hxi_lt] at this
      have hv20 : v2 0 = v1 ⟨xi, hxi_lt⟩ := by
        cases h0 : v2 0 <;> cases hx : v1 ⟨xi, hxi_lt⟩
        · rfl
        · exact absurd (hi1 hx) (by rw [h0]; simp)
        · have := hi3 (hi2 h0); rw [hx] at this; cases this
        · rfl
      have hv21 : v2 1 = v1 ⟨xi, hxi_lt⟩ := by
        cases h1 : v2 1 <;> cases hx : v1 ⟨xi, hxi_lt⟩
        · rfl
        · exact absurd (hi2 (hi1 hx)) (by rw [h1]; simp)
        · have := hi3 h1; rw [hx] at this; cases this
        · rfl
      have hs_eq : v2 2 = v1 ⟨s, hs_lt⟩ ∧ v2 3 = v1 ⟨s, hs_lt⟩ := by
        cases hlit : lit e i false
        · have hz2 := hz 2 (by simp [hact2, hlit])
          have hz3 := hz 3 (by simp [hact3, hlit])
          have hzs := hs_zero hlit
          exact ⟨by rw [hz2, hzs], by rw [hz3, hzs]⟩
        · have h4 : v1 ⟨s, hs_lt⟩ = true → v2 2 = true := by
            intro h
            have := stepImp himp he4 (by omega) (by omega)
              (by rw [hact_s, hlit]) (by rw [hact2, hlit])
              (by rw [joinV_lt v1 v2 s hs_lt]; exact h)
            rwa [joinV_nat v1 v2 2 2 rfl] at this
          have h5 : v2 2 = true → v2 3 = true := by
            intro h
            have := stepImp himp he5 (by omega) (by omega)
              (by rw [hact2, hlit]) (by rw [hact3, hlit])
              (by rw [joinV_nat v1 v2 2 2 rfl]; exact h)
            rwa [joinV_nat v1 v2 3 3 rfl] at this
          have h6 : v2 3 = true → v1 ⟨s, hs_lt⟩ = true := by
            intro h
            have := stepImp himp he6 (by omega) (by omega)
              (by rw [hact3, hlit]) (by rw [hact_s, hlit])
              (by rw [joinV_nat v1 v2 3 3 rfl]; exact h)
            rwa [joinV_lt v1 v2 s hs_lt] at this
          constructor
          · cases ha : v2 2 <;> cases hb : v1 ⟨s, hs_lt⟩
            · rfl
            · exact absurd (h4 hb) (by rw [ha]; simp)
            · have := h6 (h5 ha); rw [hb] at this; cases this
            · rfl
          · cases ha : v2 3 <;> cases hb : v1 ⟨s, hs_lt⟩
            · rfl
            · exact absurd (h5 (h4 hb)) (by rw [ha]; simp)
            · have := h6 ha; rw [hb] at this; cases this
            · rfl
      have hlr : v2 4 = true →
          lit e i false = true ∧ v1 ⟨xi, hxi_lt⟩ = true ∧ v1 ⟨s, hs_lt⟩ = true := by
        intro h4
        cases hlit : lit e i false
        · have := hz 4 (by simp [hact4, hlit])
          rw [h4] at this; cases this
        · have h7 := stepImp himp he7 (by omega) (by omega) (by rw [hact4, hlit]) hact0
            (by rw [joinV_nat v1 v2 4 4 rfl]; exact h4)
          rw [joinV_m v1 v2, hv20] at h7
          have h8 := stepImp himp he8 (by omega) (by omega)
            (by rw [hact4, hlit]) (by rw [hact2, hlit])
            (by rw [joinV_nat v1 v2 4 4 rfl]; exact h4)
          rw [joinV_nat v1 v2 2 2 rfl, hs_eq.1] at h8
          exact ⟨rfl, h7, h8⟩
      exact ⟨hv20, hv21, hs_eq.1, hs_eq.2, hlr⟩
    · intro ⟨h0, h1, h2, h3, hlr⟩
      refine ⟨?_, ?_⟩
      · intro j hj
        rcases j with ⟨jv, hjv⟩
        match jv, hjv with
        | 0, _ => simp [hact0] at hj
        | 1, _ => simp [hact1] at hj
        | 2, _ => change v2 2 = false; rw [h2]; exact hs_zero (by simpa [hact2] using hj)
        | 3, _ => change v2 3 = false; rw [h3]; exact hs_zero (by simpa [hact3] using hj)
        | 4, _ =>
          change v2 4 = false
          have hlit : lit e i false = false := by simpa [hact4] using hj
          cases hv4 : v2 4
          · rfl
          · have := (hlr hv4).1; rw [hlit] at this; cases this
      · intro ed hed ha hb hact1' hact2' hv
        simp only [newE, negEdges1, mem_insert, mem_singleton] at hed
        rcases hed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          dsimp only at hact1' hact2' hv ⊢
        · rw [joinV_lt v1 v2 xi hxi_lt] at hv
          rw [joinV_m v1 v2, h0]; exact hv
        · rw [joinV_m v1 v2, h0] at hv
          rw [joinV_nat v1 v2 1 1 rfl, h1]; exact hv
        · rw [joinV_nat v1 v2 1 1 rfl, h1] at hv
          rw [joinV_lt v1 v2 xi hxi_lt]; exact hv
        · rw [joinV_lt v1 v2 s hs_lt] at hv
          rw [joinV_nat v1 v2 2 2 rfl, h2]; exact hv
        · rw [joinV_nat v1 v2 2 2 rfl, h2] at hv
          rw [joinV_nat v1 v2 3 3 rfl, h3]; exact hv
        · rw [joinV_nat v1 v2 3 3 rfl, h3] at hv
          rw [joinV_lt v1 v2 s hs_lt]; exact hv
        · rw [joinV_nat v1 v2 4 4 rfl] at hv
          rw [joinV_m v1 v2, h0]; exact (hlr hv).2.1
        · rw [joinV_nat v1 v2 4 4 rfl] at hv
          rw [joinV_nat v1 v2 2 2 rfl, h2]; exact (hlr hv).2.2
  have hmain := card_extend_mul m 5 st.edges newE (actFn on lit st.source) (actFn on lit newSrc)
    hinv.dinv.xinv.wf.edges_lt hact_old
    (fun v1 => (fun j => v1 ⟨xCur j, hinv.dinv.xinv.x_lt j⟩) = y ∧
      v1 ⟨det, hdet_lt⟩ = d ∧ v1 ⟨s, hs_lt⟩ = sb)
    (fun v => (fun j => v ⟨Function.update xCur i (m + 1) j, by
      by_cases hji : j = i
      · subst hji; simp
      · simp [Function.update, hji]; have := hinv.dinv.xinv.x_lt j; omega⟩) = y ∧
      v ⟨det, by omega⟩ = d ∧ v ⟨m + 3, by omega⟩ = sb)
    (if lit e i false = true ∧ y i = true ∧ sb = true then 2 else 1)
    (by
      intro v1 v2 hv1 hsv ⟨hy, hd, hsb⟩
      have hc := (hchar v1 v2 hv1).mp hsv
      refine ⟨?_, ?_, ?_⟩
      · funext j
        have hj := congrFun hy j
        by_cases hji : j = i
        · subst hji
          simp only [Function.update_self] at hj
          rw [joinV_nat v1 v2 1 1 rfl, hc.2.1] at hj
          exact hj
        · simp only [Function.update_of_ne hji] at hj
          rwa [joinV_lt v1 v2 (xCur j) (hinv.dinv.xinv.x_lt j)] at hj
      · rwa [joinV_lt v1 v2 det hdet_lt] at hd
      · rw [joinV_nat v1 v2 3 3 rfl, hc.2.2.2.1] at hsb
        exact hsb)
    (by
      intro v1 hv1 ⟨hy1, hd1, hsb1⟩
      have hxi_eq : v1 ⟨xi, hxi_lt⟩ = y i := congrFun hy1 i
      have hcf := card_filter_fin5_last
        (fun v2 : Fin 5 → Bool => StepValid m 5 newE (actFn on lit newSrc) v1 v2 ∧
          (fun j => joinV v1 v2 ⟨Function.update xCur i (m + 1) j, by
            by_cases hji : j = i
            · subst hji; simp
            · simp [Function.update, hji]; have := hinv.dinv.xinv.x_lt j; omega⟩) = y ∧
          joinV v1 v2 ⟨det, by omega⟩ = d ∧ joinV v1 v2 ⟨m + 3, by omega⟩ = sb)
        (y i) (y i) sb sb
        (fun b => b = true → lit e i false = true ∧ y i = true ∧ sb = true)
        (by
          intro v2
          rw [hchar v1 v2 hv1, hxi_eq, hsb1]
          constructor
          · intro ⟨h, _, _, _⟩; exact h
          · intro ⟨h0, h1, h2, h3, h4⟩
            refine ⟨⟨h0, h1, h2, h3, h4⟩, ?_, ?_, ?_⟩
            · funext j
              by_cases hji : j = i
              · subst hji
                simp only [Function.update_self]
                rw [joinV_nat v1 v2 1 1 rfl, h1]
              · simp only [Function.update_of_ne hji]
                rw [joinV_lt v1 v2 (xCur j) (hinv.dinv.xinv.x_lt j)]
                exact congrFun hy1 j
            · rw [joinV_lt v1 v2 det hdet_lt]; exact hd1
            · rw [joinV_nat v1 v2 3 3 rfl, h3])
      rw [hcf]
      by_cases hc : lit e i false = true ∧ y i = true ∧ sb = true <;> simp [hc])
  exact hmain

private lemma negUnitStep_cnt {n k : Nat} (on : Fin k → Bool) (lit : Fin k → Fin n → Bool → Bool)
    (e : Fin k) (i : Fin n) (st : GState n k) (xCur : Fin n → Nat) (det s : Nat)
    (hinv : NegInv n k e i st xCur det s) (y : Fin n → Bool) (d sb : Bool) :
    let res := negUnitStep e i st xCur det s
    let hres := negUnitStep_inv e i st xCur det s hinv
    cntXDS on lit res.1 res.2.1 hres.dinv.xinv.x_lt det hres.dinv.det_lt res.2.2 hres.s_lt y d sb =
      cntXDS on lit st xCur hinv.dinv.xinv.x_lt det hinv.dinv.det_lt s hinv.s_lt y d sb *
        (if lit e i false = true ∧ sb = y i then 2 else 1) := by
  have h1 := negUnitHalf1_cnt on lit e i st xCur det s hinv y d sb
  set r1 := negUnitHalf1 e i st xCur det s
  have hr1 := (negUnitHalf1_inv e i st xCur det s hinv).1
  let m0 := st.m
  let newE := negEdges2 m0 (m0 + 2) (m0 + 5)
  let newSrc : Nat → Option (Fin k ⊕ (Fin k × Fin n × Bool)) := fun u =>
    if u = m0 + 5 then some (Sum.inr (e, i, false)) else r1.1.source u
  have hm1 : r1.1.m = m0 + 5 := rfl
  have hact_old : ∀ u < r1.1.m, actFn on lit newSrc u = actFn on lit r1.1.source u := by
    intro u hu
    have hne : u ≠ m0 + 5 := by omega
    simp [actFn, newSrc, hne]
  have hact_px : actFn on lit newSrc m0 = true := by
    rw [hact_old m0 (by omega)]
    simp [actFn, r1, negUnitHalf1, m0]
  have hact_ps : actFn on lit newSrc (m0 + 2) = lit e i false := by
    rw [hact_old (m0 + 2) (by omega)]
    have h1 : ¬ (m0 + 2 = m0 ∨ m0 + 2 = m0 + 1) := by omega
    simp [actFn, r1, negUnitHalf1, m0, h1]
  have hact_ur : actFn on lit newSrc (m0 + 5) = lit e i false := by
    simp [actFn, newSrc]
  have hpx_eq : ∀ v1 : Fin r1.1.m → Bool,
      ValidV r1.1.m r1.1.edges (actFn on lit r1.1.source) v1 →
      v1 ⟨m0, by omega⟩ = v1 ⟨m0 + 1, by omega⟩ := by
    intro v1 hv1
    have hxi_lt : xCur i < m0 := hinv.dinv.xinv.x_lt i
    have hact_xi : actFn on lit r1.1.source (xCur i) = true := by
      have hne1 : ¬ (xCur i = m0 ∨ xCur i = m0 + 1) := by omega
      have hne2 : ¬ (xCur i = m0 + 2 ∨ xCur i = m0 + 3 ∨ xCur i = m0 + 4) := by omega
      simp [actFn, r1, negUnitHalf1, m0, hne1, hne2, hinv.dinv.xinv.x_src i]
    have hact_m0 : actFn on lit r1.1.source m0 = true := by simp [actFn, r1, negUnitHalf1, m0]
    have hact_m1 : actFn on lit r1.1.source (m0 + 1) = true := by simp [actFn, r1, negUnitHalf1, m0]
    have he1 : (xCur i, m0) ∈ r1.1.edges := by simp [r1, negUnitHalf1, negEdges1, m0]
    have he2 : (m0, m0 + 1) ∈ r1.1.edges := by simp [r1, negUnitHalf1, negEdges1, m0]
    have he3 : (m0 + 1, xCur i) ∈ r1.1.edges := by simp [r1, negUnitHalf1, negEdges1, m0]
    have i1 := hv1.2 (m0, m0 + 1) he2 (by omega) (by omega) hact_m0 hact_m1
    have i2 := hv1.2 (m0 + 1, xCur i) he3 (by omega) (by omega) hact_m1 hact_xi
    have i3 := hv1.2 (xCur i, m0) he1 (by omega) (by omega) hact_xi hact_m0
    cases ha : v1 ⟨m0, by omega⟩ <;> cases hb : v1 ⟨m0 + 1, by omega⟩
    · rfl
    · have := i3 (i2 hb); rw [ha] at this; cases this
    · have := i1 ha; rw [hb] at this; cases this
    · rfl
  have hps_eq : ∀ v1 : Fin r1.1.m → Bool,
      ValidV r1.1.m r1.1.edges (actFn on lit r1.1.source) v1 →
      v1 ⟨m0 + 2, by omega⟩ = v1 ⟨m0 + 3, by omega⟩ := by
    intro v1 hv1
    have hs_lt : s < m0 := hinv.s_lt
    have hact_s : actFn on lit r1.1.source s = lit e i false := by
      have hne1 : ¬ (s = m0 ∨ s = m0 + 1) := by omega
      have hne2 : ¬ (s = m0 + 2 ∨ s = m0 + 3 ∨ s = m0 + 4) := by omega
      simp [actFn, r1, negUnitHalf1, m0, hne1, hne2, hinv.s_src]
    have hact_m2 : actFn on lit r1.1.source (m0 + 2) = lit e i false := by
      have h1 : ¬ (m0 + 2 = m0 ∨ m0 + 2 = m0 + 1) := by omega
      simp [actFn, r1, negUnitHalf1, m0, h1]
    have hact_m3 : actFn on lit r1.1.source (m0 + 3) = lit e i false := by
      have h1 : ¬ (m0 + 3 = m0 ∨ m0 + 3 = m0 + 1) := by omega
      simp [actFn, r1, negUnitHalf1, m0, h1]
    cases hlit : lit e i false
    · have h2 := hv1.1 ⟨m0 + 2, by omega⟩ (by rw [hact_m2, hlit])
      have h3 := hv1.1 ⟨m0 + 3, by omega⟩ (by rw [hact_m3, hlit])
      rw [h2, h3]
    · have he1 : (s, m0 + 2) ∈ r1.1.edges := by simp [r1, negUnitHalf1, negEdges1, m0]
      have he2 : (m0 + 2, m0 + 3) ∈ r1.1.edges := by simp [r1, negUnitHalf1, negEdges1, m0]
      have he3 : (m0 + 3, s) ∈ r1.1.edges := by simp [r1, negUnitHalf1, negEdges1, m0]
      have i1 := hv1.2 (m0 + 2, m0 + 3) he2 (by omega) (by omega)
        (by rw [hact_m2, hlit]) (by rw [hact_m3, hlit])
      have i2 := hv1.2 (m0 + 3, s) he3 (by omega) (by omega)
        (by rw [hact_m3, hlit]) (by rw [hact_s, hlit])
      have i3 := hv1.2 (s, m0 + 2) he1 (by omega) (by omega)
        (by rw [hact_s, hlit]) (by rw [hact_m2, hlit])
      cases ha : v1 ⟨m0 + 2, by omega⟩ <;> cases hb : v1 ⟨m0 + 3, by omega⟩
      · rfl
      · have := i3 (i2 hb); rw [ha] at this; cases this
      · have := i1 ha; rw [hb] at this; cases this
      · rfl
  have h2 :
      cntXDS on lit (negUnitStep e i st xCur det s).1 (negUnitStep e i st xCur det s).2.1
        (negUnitStep_inv e i st xCur det s hinv).dinv.xinv.x_lt det
        (negUnitStep_inv e i st xCur det s hinv).dinv.det_lt
        (negUnitStep e i st xCur det s).2.2
        (negUnitStep_inv e i st xCur det s hinv).s_lt y d sb =
      cntXDS on lit r1.1 r1.2.1 hr1.dinv.xinv.x_lt det hr1.dinv.det_lt r1.2.2 hr1.s_lt y d sb *
        (if lit e i false = true ∧ y i = false ∧ sb = false then 2 else 1) := by
    dsimp only [negUnitStep, negUnitHalf2, cntXDS]
    have hx_lt1 : ∀ j, r1.2.1 j < r1.1.m := hr1.dinv.xinv.x_lt
    have hdet_lt1 : det < r1.1.m := hr1.dinv.det_lt
    have hs_lt1 : r1.2.2 < r1.1.m := hr1.s_lt
    have hmain := card_extend_mul r1.1.m 1 r1.1.edges newE (actFn on lit r1.1.source)
      (actFn on lit newSrc) hr1.dinv.xinv.wf.edges_lt hact_old
      (fun v1 => (fun j => v1 ⟨r1.2.1 j, hx_lt1 j⟩) = y ∧
        v1 ⟨det, hdet_lt1⟩ = d ∧ v1 ⟨r1.2.2, hs_lt1⟩ = sb)
      (fun v => (fun j => v ⟨r1.2.1 j, by have := hx_lt1 j; omega⟩) = y ∧
        v ⟨det, by omega⟩ = d ∧
        v ⟨r1.2.2, by omega⟩ = sb)
      (if lit e i false = true ∧ y i = false ∧ sb = false then 2 else 1)
      (by
        intro v1 v2 _ _ ⟨hy, hd, hsb⟩
        refine ⟨?_, ?_, ?_⟩
        · funext j
          have hj := congrFun hy j
          rwa [joinV_lt v1 v2 (r1.2.1 j) (hx_lt1 j)] at hj
        · rwa [joinV_lt v1 v2 det hdet_lt1] at hd
        · rwa [joinV_lt v1 v2 r1.2.2 hs_lt1] at hsb)
      (by
        intro v1 hv1 ⟨hy1, hd1, hsb1⟩
        have hvpx : v1 ⟨m0, by omega⟩ = y i := by
          rw [hpx_eq v1 hv1]
          have := congrFun hy1 i
          simpa [r1, negUnitHalf1] using this
        have hvps : v1 ⟨m0 + 2, by omega⟩ = sb := by
          rw [hps_eq v1 hv1]
          simpa [r1, negUnitHalf1] using hsb1
        have hstep_iff : ∀ v2 : Fin 1 → Bool,
            (StepValid r1.1.m 1 newE (actFn on lit newSrc) v1 v2 ∧
              (fun j => joinV v1 v2 ⟨r1.2.1 j, by have := hx_lt1 j; omega⟩) = y ∧
              joinV v1 v2 ⟨det, by omega⟩ = d ∧
              joinV v1 v2 ⟨r1.2.2, by omega⟩ = sb) ↔
            ((lit e i false = false → v2 0 = false) ∧
              (lit e i false = true → (y i = true ∨ sb = true) → v2 0 = true)) := by
          intro v2
          constructor
          · intro ⟨⟨hz, himp⟩, _, _, _⟩
            refine ⟨?_, ?_⟩
            · intro hlit
              exact hz 0 (by simpa [hm1, hact_ur] using hlit)
            · intro hlit hor
              rcases hor with hyi | hsb
              · have he1 : (m0, m0 + 5) ∈ newE := by simp [newE, negEdges2]
                have := stepImp himp he1 (by omega) (by omega)
                  hact_px (by rw [hact_ur, hlit])
                  (by rw [joinV_lt v1 v2 m0 (by omega)]; exact hvpx.trans hyi)
                have hg := joinV_m v1 v2 (by omega)
                simp only [hm1] at hg
                rwa [hg] at this
              · have he2 : (m0 + 2, m0 + 5) ∈ newE := by simp [newE, negEdges2]
                have := stepImp himp he2 (by omega) (by omega)
                  (by rw [hact_ps, hlit]) (by rw [hact_ur, hlit])
                  (by rw [joinV_lt v1 v2 (m0 + 2) (by omega)]; exact hvps.trans hsb)
                have hg := joinV_m v1 v2 (by omega)
                simp only [hm1] at hg
                rwa [hg] at this
          · intro ⟨hfalse, htrue⟩
            refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
            · intro j hj
              have hj0 : j = 0 := Fin.ext (by omega)
              subst hj0
              exact hfalse (by simpa [hm1, hact_ur] using hj)
            · intro ed hed ha hb ha1 ha2 hv
              simp only [newE, negEdges2, mem_insert, mem_singleton] at hed
              rcases hed with rfl | rfl <;> dsimp only at ha1 ha2 hv ⊢
              · rw [joinV_lt v1 v2 m0 (by omega), hvpx] at hv
                have hlit : lit e i false = true := by simpa [hact_ur] using ha2
                have hg := joinV_m v1 v2 (by omega)
                simp only [hm1] at hg
                rw [hg]
                exact htrue hlit (Or.inl hv)
              · rw [joinV_lt v1 v2 (m0 + 2) (by omega), hvps] at hv
                have hlit : lit e i false = true := by simpa [hact_ur] using ha2
                have hg := joinV_m v1 v2 (by omega)
                simp only [hm1] at hg
                rw [hg]
                exact htrue hlit (Or.inr hv)
            · funext j
              rw [joinV_lt v1 v2 (r1.2.1 j) (hx_lt1 j)]
              exact congrFun hy1 j
            · rw [joinV_lt v1 v2 det hdet_lt1]; exact hd1
            · rw [joinV_lt v1 v2 r1.2.2 hs_lt1]; exact hsb1
        rw [card_filter_fin1]
        simp only [hstep_iff]
        cases hlit : lit e i false <;> cases hyi : y i <;> cases hsb : sb <;> simp)
    exact hmain
  dsimp only at h1 ⊢
  rw [h2, h1, Nat.mul_assoc]
  congr 1
  cases hlit : lit e i false <;> cases hyi : y i <;> cases hsb : sb <;> simp

private def negLoop {n k : Nat} (e : Fin k) (i : Fin n) (det : Nat) :
    Nat → GState n k × (Fin n → Nat) × Nat → GState n k × (Fin n → Nat) × Nat
  | 0, acc => acc
  | r + 1, acc =>
    let acc' := negUnitStep e i acc.1 acc.2.1 det acc.2.2
    negLoop e i det r acc'

private lemma negLoop_m {n k : Nat} (e : Fin k) (i : Fin n) (det : Nat) :
    ∀ r acc, (negLoop e i det r acc).1.m = acc.1.m + 6 * r := by
  intro r
  induction r with
  | zero => intro acc; simp [negLoop]
  | succ r ih =>
    intro acc
    dsimp only [negLoop]
    rw [ih]
    have hm : (negUnitStep e i acc.1 acc.2.1 det acc.2.2).1.m = acc.1.m + 6 := rfl
    rw [hm]
    omega

private lemma negLoop_inv {n k : Nat} (e : Fin k) (i : Fin n) (det : Nat) :
    ∀ r acc, NegInv n k e i acc.1 acc.2.1 det acc.2.2 →
      let res := negLoop e i det r acc
      NegInv n k e i res.1 res.2.1 det res.2.2 := by
  intro r
  induction r with
  | zero => intro acc h; exact h
  | succ r ih =>
    intro acc h
    exact ih _ (negUnitStep_inv e i acc.1 acc.2.1 det acc.2.2 h)

private lemma negLoop_cnt {n k : Nat} (on : Fin k → Bool) (lit : Fin k → Fin n → Bool → Bool)
    (e : Fin k) (i : Fin n) (det : Nat) (y : Fin n → Bool) (d sb : Bool) :
    ∀ r acc (h : NegInv n k e i acc.1 acc.2.1 det acc.2.2),
      let res := negLoop e i det r acc
      let hres := negLoop_inv e i det r acc h
      cntXDS on lit res.1 res.2.1 hres.dinv.xinv.x_lt det hres.dinv.det_lt res.2.2 hres.s_lt y d sb =
        cntXDS on lit acc.1 acc.2.1 h.dinv.xinv.x_lt det h.dinv.det_lt acc.2.2 h.s_lt y d sb *
          (if lit e i false = true ∧ sb = y i then 2 else 1) ^ r := by
  intro r
  induction r with
  | zero =>
    intro acc h
    simp [negLoop]
  | succ r ih =>
    intro acc h
    dsimp only [negLoop]
    have hstep_inv := negUnitStep_inv e i acc.1 acc.2.1 det acc.2.2 h
    have hstep_cnt := negUnitStep_cnt on lit e i acc.1 acc.2.1 det acc.2.2 h y d sb
    rw [ih _ hstep_inv, hstep_cnt, Nat.mul_assoc]
    congr 1
    rw [pow_succ, Nat.mul_comm]

private def negEndEdges (det pd det' s : Nat) : Finset (Nat × Nat) :=
  {(det, pd), (pd, det'), (det', det), (s, pd)}

private lemma negEndEdges_deg {m det s : Nat} (hdet : det < m) (hs : s < m) (hne : det ≠ s) :
    let newE := negEndEdges det m (m + 1) s
    (∀ u < m, u ≠ det → u ≠ s → inDeg newE u = 0 ∧ outDeg newE u = 0) ∧
    (inDeg newE det ≤ 1 ∧ outDeg newE det ≤ 1) ∧
    (inDeg newE s = 0 ∧ outDeg newE s ≤ 1) ∧
    (inDeg newE m ≤ 2 ∧ outDeg newE m ≤ 1) ∧
    (inDeg newE (m + 1) ≤ 1 ∧ outDeg newE (m + 1) ≤ 1) := by
  dsimp only
  refine ⟨?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro u hu hd hs'
    refine ⟨card_filter_empty _ _ ?_, card_filter_empty _ _ ?_⟩ <;>
      · intro ed hed
        simp only [negEndEdges, mem_insert, mem_singleton] at hed
        rcases hed with rfl | rfl | rfl | rfl <;> dsimp <;> omega
  · apply card_filter_subset_single _ _ (m + 1, det)
    intro ed hed h2
    simp only [negEndEdges, mem_insert, mem_singleton] at hed
    rcases hed with rfl | rfl | rfl | rfl <;> first | rfl | (dsimp at h2; omega)
  · apply card_filter_subset_single _ _ (det, m)
    intro ed hed h1
    simp only [negEndEdges, mem_insert, mem_singleton] at hed
    rcases hed with rfl | rfl | rfl | rfl <;> first | rfl | (dsimp at h1; omega)
  · apply card_filter_empty
    intro ed hed
    simp only [negEndEdges, mem_insert, mem_singleton] at hed
    rcases hed with rfl | rfl | rfl | rfl <;> dsimp <;> omega
  · apply card_filter_subset_single _ _ (s, m)
    intro ed hed h1
    simp only [negEndEdges, mem_insert, mem_singleton] at hed
    rcases hed with rfl | rfl | rfl | rfl <;> first | rfl | (dsimp at h1; omega)
  · apply card_filter_subset_pair _ _ (det, m) (s, m)
    intro ed hed h2
    simp only [negEndEdges, mem_insert, mem_singleton] at hed
    rcases hed with rfl | rfl | rfl | rfl <;>
      first | exact Or.inl rfl | exact Or.inr rfl | (dsimp at h2; omega)
  · apply card_filter_subset_single _ _ (m, m + 1)
    intro ed hed h1
    simp only [negEndEdges, mem_insert, mem_singleton] at hed
    rcases hed with rfl | rfl | rfl | rfl <;> first | rfl | (dsimp at h1; omega)
  · apply card_filter_subset_single _ _ (m, m + 1)
    intro ed hed h2
    simp only [negEndEdges, mem_insert, mem_singleton] at hed
    rcases hed with rfl | rfl | rfl | rfl <;> first | rfl | (dsimp at h2; omega)
  · apply card_filter_subset_single _ _ (m + 1, det)
    intro ed hed h1
    simp only [negEndEdges, mem_insert, mem_singleton] at hed
    rcases hed with rfl | rfl | rfl | rfl <;> first | rfl | (dsimp at h1; omega)

private def negEndStep {n k : Nat} (e : Fin k) (st : GState n k)
    (xCur : Fin n → Nat) (det s : Nat) : GState n k × Nat :=
  let m := st.m
  let newE := negEndEdges det m (m + 1) s
  let newSrc := fun u =>
    if u = m ∨ u = m + 1 then some (Sum.inl e) else st.source u
  let newBag := insert (m + 1) (insert m (insert det (insert s (Finset.univ.image xCur))))
  (⟨m + 2, st.edges ∪ newE, newSrc, st.bags ++ [newBag]⟩, m + 1)

private lemma negEndStep_inv {n k : Nat} (e : Fin k) (i : Fin n) (st : GState n k)
    (xCur : Fin n → Nat) (det s : Nat) (hinv : NegInv n k e i st xCur det s) :
    let res := negEndStep e st xCur det s
    DetInv n k e res.1 xCur res.2 := by
  dsimp only [negEndStep]
  have hdeg := negEndEdges_deg hinv.dinv.det_lt hinv.s_lt hinv.s_ne_det
  let newE := negEndEdges det st.m (st.m + 1) s
  let newBag := insert (st.m + 1) (insert st.m (insert det (insert s (Finset.univ.image xCur))))
  have hdisj : Disjoint st.edges newE := by
    rw [Finset.disjoint_left]
    intro ed he1 he2
    have hlt := hinv.dinv.xinv.wf.edges_lt ed he1
    simp only [newE, negEndEdges, mem_insert, mem_singleton] at he2
    rcases he2 with rfl | rfl | rfl | rfl <;> dsimp at hlt <;> omega
  have hwf : WellFormed n k ⟨st.m + 2, st.edges ∪ newE,
      fun u => if u = st.m ∨ u = st.m + 1 then some (Sum.inl e) else st.source u,
      st.bags ++ [newBag]⟩ := by
    apply extend_wellFormed st hinv.dinv.xinv.wf 2 (by omega) newE _ newBag
    · intro ed hed
      simp only [newE, negEndEdges, mem_insert, mem_singleton] at hed
      rcases hed with rfl | rfl | rfl | rfl <;>
        (dsimp; have := hinv.dinv.det_lt; have := hinv.s_lt; omega)
    · intro ed hed
      simp only [newE, negEndEdges, mem_insert, mem_singleton] at hed
      rcases hed with rfl | rfl | rfl | rfl <;> dsimp <;> omega
    · intro u hu
      dsimp only [newE]
      by_cases h1 : u = det
      · subst h1
        rcases hinv.dinv.det_deg with ⟨ha1, ha2⟩
        rcases hdeg.2.1 with ⟨hb1, hb2⟩
        exact ⟨by omega, by omega⟩
      · by_cases h2 : u = s
        · subst h2
          rcases hinv.s_deg with ⟨ha1, ha2⟩
          rcases hdeg.2.2.1 with ⟨hb1, hb2⟩
          exact ⟨by omega, by omega⟩
        · rcases hdeg.1 u hu h1 h2 with ⟨hb1, hb2⟩
          rcases hinv.dinv.xinv.wf.deg_le u hu with ⟨ha1, ha2⟩
          exact ⟨by omega, by omega⟩
    · intro u hge hlt
      dsimp only [newE]
      have hc : u = st.m ∨ u = st.m + 1 := by omega
      rcases hc with rfl | rfl
      · rcases hdeg.2.2.2.1 with ⟨h1, h2⟩; exact ⟨by omega, by omega⟩
      · rcases hdeg.2.2.2.2 with ⟨h1, h2⟩; exact ⟨by omega, by omega⟩
    · have hallX : (Finset.univ.image xCur).card ≤ n := by
        calc (Finset.univ.image xCur).card ≤ (Finset.univ : Finset (Fin n)).card := card_image_le
          _ = n := Fintype.card_fin n
      have h1 := card_insert_le (st.m + 1) (insert st.m (insert det (insert s (Finset.univ.image xCur))))
      have h2 := card_insert_le st.m (insert det (insert s (Finset.univ.image xCur)))
      have h3 := card_insert_le det (insert s (Finset.univ.image xCur))
      have h4 := card_insert_le s (Finset.univ.image xCur)
      dsimp only [newBag]
      omega
    · intro u hu
      simp only [newBag, mem_insert, mem_image, mem_univ, true_and] at hu
      rcases hu with rfl | rfl | rfl | rfl | ⟨j, rfl⟩
      · omega
      · omega
      · have := hinv.dinv.det_lt; omega
      · have := hinv.s_lt; omega
      · have := hinv.dinv.xinv.x_lt j; omega
    · intro u hge hlt
      have hc : u = st.m ∨ u = st.m + 1 := by omega
      rcases hc with rfl | rfl <;> simp [newBag]
    · intro u hu hlt
      simp only [newBag, mem_insert, mem_image, mem_univ, true_and] at hu
      rcases hu with rfl | rfl | rfl | rfl | ⟨j, rfl⟩
      · omega
      · omega
      · exact hinv.dinv.det_bag
      · exact hinv.s_bag
      · exact hinv.dinv.xinv.x_bag j
    · intro ed hed
      simp only [newE, negEndEdges, mem_insert, mem_singleton] at hed
      rcases hed with rfl | rfl | rfl | rfl <;> simp [newBag]
  have hxinv : XInv n k ⟨st.m + 2, st.edges ∪ newE,
      fun u => if u = st.m ∨ u = st.m + 1 then some (Sum.inl e) else st.source u,
      st.bags ++ [newBag]⟩ xCur :=
    { wf := hwf
      x_lt := fun j => by dsimp only; have := hinv.dinv.xinv.x_lt j; omega
      x_inj := hinv.dinv.xinv.x_inj
      x_deg := fun j => by
        dsimp only
        rw [inDeg_union_of_disjoint hdisj, outDeg_union_of_disjoint hdisj]
        dsimp only [newE]
        rcases hdeg.1 (xCur j) (hinv.dinv.xinv.x_lt j) (hinv.dinv.det_ne j) (hinv.s_ne_x j) with ⟨hb1, hb2⟩
        rcases hinv.dinv.xinv.x_deg j with ⟨ha1, ha2⟩
        exact ⟨by omega, by omega⟩
      x_src := fun j => by
        dsimp only
        have hlt := hinv.dinv.xinv.x_lt j
        have h1 : ¬ (xCur j = st.m ∨ xCur j = st.m + 1) := by omega
        simp [h1, hinv.dinv.xinv.x_src j]
      x_bag := fun j => by
        dsimp only
        rw [List.getLast_append_singleton]
        have hjm : xCur j ∈ Finset.univ.image xCur := mem_image_of_mem xCur (mem_univ j)
        simp [newBag, hjm] }
  refine
    { xinv := hxinv
      det_lt := by dsimp only; omega
      det_ne := fun j => by have := hinv.dinv.xinv.x_lt j; omega
      det_deg := by
        dsimp only
        rw [inDeg_union_of_disjoint hdisj, outDeg_union_of_disjoint hdisj,
          inDeg_eq_zero_of_ge hinv.dinv.xinv.wf.edges_lt (by omega),
          outDeg_eq_zero_of_ge hinv.dinv.xinv.wf.edges_lt (by omega), Nat.zero_add, Nat.zero_add]
        exact hdeg.2.2.2.2
      det_src := by simp
      det_bag := by
        dsimp only
        rw [List.getLast_append_singleton]; simp [newBag] }

private lemma negEndStep_cnt {n k : Nat} (on : Fin k → Bool) (lit : Fin k → Fin n → Bool → Bool)
    (e : Fin k) (i : Fin n) (st : GState n k) (xCur : Fin n → Nat) (det s : Nat)
    (hinv : NegInv n k e i st xCur det s) (y : Fin n → Bool) (d sb : Bool) :
    let res := negEndStep e st xCur det s
    let hres := negEndStep_inv e i st xCur det s hinv
    cntXDS on lit res.1 xCur hres.xinv.x_lt res.2 hres.det_lt s
        (by dsimp only [res, negEndStep]; have := hinv.s_lt; omega) y d sb =
      cntXDS on lit st xCur hinv.dinv.xinv.x_lt det hinv.dinv.det_lt s hinv.s_lt y d sb *
        (if on e = true ∧ lit e i false = true ∧ sb = true ∧ d = false then 0 else 1) := by
  dsimp only [negEndStep, cntXDS]
  let m := st.m
  let newE := negEndEdges det m (m + 1) s
  let newSrc : Nat → Option (Fin k ⊕ (Fin k × Fin n × Bool)) := fun u =>
    if u = m ∨ u = m + 1 then some (Sum.inl e) else st.source u
  have hact_old : ∀ u < m, actFn on lit newSrc u = actFn on lit st.source u := by
    intro u hu
    have h1 : ¬ (u = m ∨ u = m + 1) := by omega
    simp [actFn, newSrc, h1]
  have hdet_lt : det < m := hinv.dinv.det_lt
  have hs_lt : s < m := hinv.s_lt
  have hact_det : actFn on lit newSrc det = on e := by
    rw [hact_old det hdet_lt]; simp [actFn, hinv.dinv.det_src]
  have hact_s : actFn on lit newSrc s = lit e i false := by
    rw [hact_old s hs_lt]; simp [actFn, hinv.s_src]
  have hact0 : actFn on lit newSrc m = on e := by simp [actFn, newSrc]
  have hact1 : actFn on lit newSrc (m + 1) = on e := by simp [actFn, newSrc]
  have hchar : ∀ (v1 : Fin m → Bool) (v2 : Fin 2 → Bool),
      ValidV m st.edges (actFn on lit st.source) v1 →
      (StepValid m 2 newE (actFn on lit newSrc) v1 v2 ↔
        v2 0 = v1 ⟨det, hdet_lt⟩ ∧
        v2 1 = v1 ⟨det, hdet_lt⟩ ∧
        (on e = true → lit e i false = true → v1 ⟨s, hs_lt⟩ = true → v1 ⟨det, hdet_lt⟩ = true)) := by
    intro v1 v2 hv1
    have hdet_zero : on e = false → v1 ⟨det, hdet_lt⟩ = false := by
      intro hon
      exact hv1.1 ⟨det, hdet_lt⟩ (by simp [actFn, hinv.dinv.det_src, hon])
    constructor
    · intro ⟨hz, himp⟩
      have he1 : (det, m) ∈ newE := by simp [newE, negEndEdges]
      have he2 : (m, m + 1) ∈ newE := by simp [newE, negEndEdges]
      have he3 : (m + 1, det) ∈ newE := by simp [newE, negEndEdges]
      have he4 : (s, m) ∈ newE := by simp [newE, negEndEdges]
      have hdet_eq : v2 0 = v1 ⟨det, hdet_lt⟩ ∧ v2 1 = v1 ⟨det, hdet_lt⟩ := by
        cases hon : on e
        · have hz0 := hz 0 (by simp [hact0, hon])
          have hz1 := hz 1 (by simp [hact1, hon])
          have hzd := hdet_zero hon
          exact ⟨by rw [hz0, hzd], by rw [hz1, hzd]⟩
        · have i1 : v1 ⟨det, hdet_lt⟩ = true → v2 0 = true := by
            intro h
            have := stepImp himp he1 (by omega) (by omega)
              (by rw [hact_det, hon]) (by rw [hact0, hon])
              (by rw [joinV_lt v1 v2 det hdet_lt]; exact h)
            rwa [joinV_m v1 v2] at this
          have i2 : v2 0 = true → v2 1 = true := by
            intro h
            have := stepImp himp he2 (by omega) (by omega)
              (by rw [hact0, hon]) (by rw [hact1, hon])
              (by rw [joinV_m v1 v2]; exact h)
            rwa [joinV_nat v1 v2 1 1 rfl] at this
          have i3 : v2 1 = true → v1 ⟨det, hdet_lt⟩ = true := by
            intro h
            have := stepImp himp he3 (by omega) (by omega)
              (by rw [hact1, hon]) (by rw [hact_det, hon])
              (by rw [joinV_nat v1 v2 1 1 rfl]; exact h)
            rwa [joinV_lt v1 v2 det hdet_lt] at this
          constructor
          · cases ha : v2 0 <;> cases hb : v1 ⟨det, hdet_lt⟩
            · rfl
            · exact absurd (i1 hb) (by rw [ha]; simp)
            · have := i3 (i2 ha); rw [hb] at this; cases this
            · rfl
          · cases ha : v2 1 <;> cases hb : v1 ⟨det, hdet_lt⟩
            · rfl
            · exact absurd (i2 (i1 hb)) (by rw [ha]; simp)
            · have := i3 ha; rw [hb] at this; cases this
            · rfl
      have hcond : on e = true → lit e i false = true →
          v1 ⟨s, hs_lt⟩ = true → v1 ⟨det, hdet_lt⟩ = true := by
        intro hon hlit hvs
        have := stepImp himp he4 (by omega) (by omega)
          (by rw [hact_s, hlit]) (by rw [hact0, hon])
          (by rw [joinV_lt v1 v2 s hs_lt]; exact hvs)
        rw [joinV_m v1 v2, hdet_eq.1] at this
        exact this
      exact ⟨hdet_eq.1, hdet_eq.2, hcond⟩
    · intro ⟨h0, h1, hcond⟩
      refine ⟨?_, ?_⟩
      · intro j hj
        rcases j with ⟨jv, hjv⟩
        match jv, hjv with
        | 0, _ => change v2 0 = false; rw [h0]; exact hdet_zero (by simpa [hact0] using hj)
        | 1, _ => change v2 1 = false; rw [h1]; exact hdet_zero (by simpa [hact1] using hj)
      · intro ed hed ha hb ha1 ha2 hv
        simp only [newE, negEndEdges, mem_insert, mem_singleton] at hed
        rcases hed with rfl | rfl | rfl | rfl <;> dsimp only at ha1 ha2 hv ⊢
        · rw [joinV_lt v1 v2 det hdet_lt] at hv
          rw [joinV_m v1 v2, h0]; exact hv
        · rw [joinV_m v1 v2, h0] at hv
          rw [joinV_nat v1 v2 1 1 rfl, h1]; exact hv
        · rw [joinV_nat v1 v2 1 1 rfl, h1] at hv
          rw [joinV_lt v1 v2 det hdet_lt]; exact hv
        · rw [joinV_lt v1 v2 s hs_lt] at hv
          have hlit : lit e i false = true := by simpa [hact_s] using ha1
          have hon : on e = true := by simpa [hact0] using ha2
          rw [joinV_m v1 v2, h0]
          exact hcond hon hlit hv
  have hmain := card_extend_mul m 2 st.edges newE (actFn on lit st.source) (actFn on lit newSrc)
    hinv.dinv.xinv.wf.edges_lt hact_old
    (fun v1 => (fun j => v1 ⟨xCur j, hinv.dinv.xinv.x_lt j⟩) = y ∧
      v1 ⟨det, hdet_lt⟩ = d ∧ v1 ⟨s, hs_lt⟩ = sb)
    (fun v => (fun j => v ⟨xCur j, by have := hinv.dinv.xinv.x_lt j; omega⟩) = y ∧
      v ⟨m + 1, by omega⟩ = d ∧ v ⟨s, by omega⟩ = sb)
    (if on e = true ∧ lit e i false = true ∧ sb = true ∧ d = false then 0 else 1)
    (by
      intro v1 v2 hv1 hsv ⟨hy, hd, hsb⟩
      have hc := (hchar v1 v2 hv1).mp hsv
      refine ⟨?_, ?_, ?_⟩
      · funext j
        have hj := congrFun hy j
        rwa [joinV_lt v1 v2 (xCur j) (hinv.dinv.xinv.x_lt j)] at hj
      · rw [joinV_nat v1 v2 1 1 rfl, hc.2.1] at hd
        exact hd
      · rwa [joinV_lt v1 v2 s hs_lt] at hsb)
    (by
      intro v1 hv1 ⟨hy1, hd1, hsb1⟩
      have hcf := card_filter_unique
        (fun v2 : Fin 2 → Bool => StepValid m 2 newE (actFn on lit newSrc) v1 v2 ∧
          (fun j => joinV v1 v2 ⟨xCur j, by have := hinv.dinv.xinv.x_lt j; omega⟩) = y ∧
          joinV v1 v2 ⟨m + 1, by omega⟩ = d ∧ joinV v1 v2 ⟨s, by omega⟩ = sb)
        (fun _ => d)
        (¬ (on e = true ∧ lit e i false = true ∧ sb = true ∧ d = false))
        (by
          intro v2
          rw [hchar v1 v2 hv1, hd1, hsb1]
          constructor
          · intro ⟨⟨h0, h1, hcond⟩, _, _, _⟩
            refine ⟨?_, ?_⟩
            · funext j
              rcases j with ⟨jv, hjv⟩
              match jv, hjv with
              | 0, _ => exact h0
              | 1, _ => exact h1
            · intro ⟨hon, hlit, hsb, hd⟩
              have := hcond hon hlit hsb
              rw [hd] at this; cases this
          · intro ⟨hv2, hnr⟩
            subst hv2
            refine ⟨⟨rfl, rfl, ?_⟩, ?_, ?_, ?_⟩
            · intro hon hlit hsb
              cases hd : d
              · exact absurd ⟨hon, hlit, hsb, hd⟩ hnr
              · rfl
            · funext j
              rw [joinV_lt v1 (fun _ => d) (xCur j) (hinv.dinv.xinv.x_lt j)]
              exact congrFun hy1 j
            · rw [joinV_nat v1 (fun _ => d) 1 1 rfl]
            · rw [joinV_lt v1 (fun _ => d) s hs_lt]; exact hsb1)
      rw [hcf]
      by_cases hc : on e = true ∧ lit e i false = true ∧ sb = true ∧ d = false <;> simp [hc])
  exact hmain

private def negFullStep {n k : Nat} (R : Nat) (e : Fin k) (i : Fin n) (st : GState n k)
    (xCur : Fin n → Nat) (det : Nat) : GState n k × (Fin n → Nat) × Nat :=
  let r0 := allocSStep e i st xCur det
  let r1 := negLoop e i det R (r0.1, xCur, r0.2)
  let r2 := negEndStep e r1.1 r1.2.1 det r1.2.2
  (r2.1, r1.2.1, r2.2)

private lemma negFullStep_m {n k : Nat} (R : Nat) (e : Fin k) (i : Fin n) (st : GState n k)
    (xCur : Fin n → Nat) (det : Nat) :
    (negFullStep R e i st xCur det).1.m = st.m + 3 + 6 * R := by
  dsimp only [negFullStep, negEndStep]
  rw [negLoop_m]
  dsimp only [allocSStep]
  omega

private lemma negFullStep_inv {n k : Nat} (R : Nat) (e : Fin k) (i : Fin n) (st : GState n k)
    (xCur : Fin n → Nat) (det : Nat) (hinv : DetInv n k e st xCur det) :
    let res := negFullStep R e i st xCur det
    DetInv n k e res.1 res.2.1 res.2.2 := by
  dsimp only [negFullStep]
  have h0 := allocS_inv e i st xCur det hinv
  have h1 := negLoop_inv e i det R ((allocSStep e i st xCur det).1, xCur,
    (allocSStep e i st xCur det).2) h0
  exact negEndStep_inv e i _ _ det _ h1

private def fNeg (on_e lit_neg y_i d : Bool) (R : Nat) : Nat :=
  if lit_neg = false then 1
  else if on_e = true ∧ d = false then (if y_i = false then 2 ^ R else 1)
  else 1 + 2 ^ R

private lemma negFullStep_cnt {n k : Nat} (on : Fin k → Bool) (lit : Fin k → Fin n → Bool → Bool)
    (R : Nat) (e : Fin k) (i : Fin n) (st : GState n k) (xCur : Fin n → Nat) (det : Nat)
    (hinv : DetInv n k e st xCur det) (y : Fin n → Bool) (d : Bool) :
    let res := negFullStep R e i st xCur det
    let hres := negFullStep_inv R e i st xCur det hinv
    cntXD on lit res.1 res.2.1 hres.xinv.x_lt res.2.2 hres.det_lt y d =
      cntXD on lit st xCur hinv.xinv.x_lt det hinv.det_lt y d *
        fNeg (on e) (lit e i false) (y i) d R := by
  set r0 := allocSStep e i st xCur det
  have h0 := allocS_inv e i st xCur det hinv
  set r1 := negLoop e i det R (r0.1, xCur, r0.2)
  have h1 := negLoop_inv e i det R (r0.1, xCur, r0.2) h0
  set r2 := negEndStep e r1.1 r1.2.1 det r1.2.2
  have h2 := negEndStep_inv e i r1.1 r1.2.1 det r1.2.2 h1
  have hs_lt2 : r1.2.2 < r2.1.m := by
    have hs1 : r1.2.2 < r1.1.m := h1.s_lt
    dsimp only [r2, negEndStep]
    omega
  have hsplit : cntXD on lit r2.1 r1.2.1 h2.xinv.x_lt r2.2 h2.det_lt y d =
      cntXDS on lit r2.1 r1.2.1 h2.xinv.x_lt r2.2 h2.det_lt r1.2.2 hs_lt2 y d false +
      cntXDS on lit r2.1 r1.2.1 h2.xinv.x_lt r2.2 h2.det_lt r1.2.2 hs_lt2 y d true := by
    unfold cntXD cntXDS
    rw [card_split_bool
      (fun v : Fin r2.1.m → Bool => ValidV r2.1.m r2.1.edges (actFn on lit r2.1.source) v ∧
        (fun j => v ⟨r1.2.1 j, h2.xinv.x_lt j⟩) = y ∧ v ⟨r2.2, h2.det_lt⟩ = d)
      ⟨r1.2.2, hs_lt2⟩]
    congr 1
    · congr 1; ext v; simp [and_assoc]
    · congr 1; ext v; simp [and_assoc]
  have hterm : ∀ sb : Bool,
      cntXDS on lit r2.1 r1.2.1 h2.xinv.x_lt r2.2 h2.det_lt r1.2.2 hs_lt2 y d sb =
      cntXD on lit st xCur hinv.xinv.x_lt det hinv.det_lt y d *
        ((if lit e i false = false ∧ sb = true then 0 else 1) *
         (if lit e i false = true ∧ sb = y i then 2 else 1) ^ R *
         (if on e = true ∧ lit e i false = true ∧ sb = true ∧ d = false then 0 else 1)) := by
    intro sb
    have hc2 := negEndStep_cnt on lit e i r1.1 r1.2.1 det r1.2.2 h1 y d sb
    have hc1 := negLoop_cnt on lit e i det y d sb R (r0.1, xCur, r0.2) h0
    have hc0 := allocS_cnt on lit e i st xCur det hinv y d sb
    dsimp only at hc2 hc1 hc0
    rw [hc2, hc1, hc0]
    simp only [Nat.mul_assoc]
  change cntXD on lit r2.1 r1.2.1 h2.xinv.x_lt r2.2 h2.det_lt y d = _
  rw [hsplit, hterm false, hterm true, ← Nat.mul_add]
  congr 1
  unfold fNeg
  cases hon : on e <;> cases hlit : lit e i false <;> cases hyi : y i <;> cases hd : d <;>
    simp [Nat.add_comm]

private def litStep {n k : Nat} (R : Nat) (e : Fin k) (i : Fin n) (st : GState n k)
    (xCur : Fin n → Nat) (det : Nat) : GState n k × (Fin n → Nat) × Nat :=
  let r1 := posStep e i st xCur det
  negFullStep R e i r1.1 r1.2.1 r1.2.2

private lemma litStep_m {n k : Nat} (R : Nat) (e : Fin k) (i : Fin n) (st : GState n k)
    (xCur : Fin n → Nat) (det : Nat) :
    (litStep R e i st xCur det).1.m = st.m + 8 + 6 * R := by
  dsimp only [litStep]
  rw [negFullStep_m]
  have h1 : (posStep e i st xCur det).1.m = st.m + 5 := rfl
  rw [h1]

private lemma litStep_inv {n k : Nat} (R : Nat) (e : Fin k) (i : Fin n) (st : GState n k)
    (xCur : Fin n → Nat) (det : Nat) (hinv : DetInv n k e st xCur det) :
    let res := litStep R e i st xCur det
    DetInv n k e res.1 res.2.1 res.2.2 :=
  negFullStep_inv R e i _ _ _ (posStep_inv e i st xCur det hinv)

private lemma litStep_cnt {n k : Nat} (on : Fin k → Bool) (lit : Fin k → Fin n → Bool → Bool)
    (R : Nat) (e : Fin k) (i : Fin n) (st : GState n k) (xCur : Fin n → Nat) (det : Nat)
    (hinv : DetInv n k e st xCur det) (y : Fin n → Bool) (d : Bool) :
    let res := litStep R e i st xCur det
    let hres := litStep_inv R e i st xCur det hinv
    cntXD on lit res.1 res.2.1 hres.xinv.x_lt res.2.2 hres.det_lt y d =
      cntXD on lit st xCur hinv.xinv.x_lt det hinv.det_lt y d *
        (fPos (on e) (lit e i true) (y i) d * fNeg (on e) (lit e i false) (y i) d R) := by
  dsimp only [litStep]
  have hp_inv := posStep_inv e i st xCur det hinv
  have hp_cnt := posStep_cnt on lit e i st xCur det hinv y d
  have hn_cnt := negFullStep_cnt on lit R e i _ _ _ hp_inv y d
  rw [hn_cnt, hp_cnt, Nat.mul_assoc]

private lemma litFactor_props (on_e lit_t lit_f y_i d : Bool) (R : Nat) (_hR : 0 < 2 ^ R) :
    let fac := fPos on_e lit_t y_i d * fNeg on_e lit_f y_i d R
    ((on_e = false ∨ d = true) → 0 < fac ∧ fac % (2 ^ R) = 1 % (2 ^ R)) ∧
    (on_e = true → d = false → (if y_i then lit_t else lit_f) = false → fac = 1) ∧
    (on_e = true → d = false → (if y_i then lit_t else lit_f) = true → fac % (2 ^ R) = 0) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro hor
    unfold fPos fNeg
    cases hon : on_e <;> cases hlt : lit_t <;> cases hlf : lit_f <;> cases hy : y_i <;>
      cases hd : d <;> simp_all
  · intro hon hd hl
    unfold fPos fNeg
    cases hy : y_i <;> simp_all
  · intro hon hd hl
    unfold fPos fNeg
    cases hy : y_i <;> simp_all

private def litLoop {n k : Nat} (R : Nat) (e : Fin k) :
    (t : Nat) → t ≤ n → GState n k × (Fin n → Nat) × Nat → GState n k × (Fin n → Nat) × Nat
  | 0, _, acc => acc
  | t + 1, ht, acc =>
    let prev := litLoop R e t (by omega) acc
    litStep R e ⟨t, ht⟩ prev.1 prev.2.1 prev.2.2

private lemma litLoop_m {n k : Nat} (R : Nat) (e : Fin k) :
    ∀ (t : Nat) (ht : t ≤ n) acc,
      (litLoop R e t ht acc).1.m = acc.1.m + t * (8 + 6 * R) := by
  intro t
  induction t with
  | zero => intro _ acc; simp [litLoop]
  | succ t ih =>
    intro ht acc
    dsimp only [litLoop]
    rw [litStep_m, ih (by omega) acc]
    rw [Nat.add_mul, Nat.one_mul]
    omega

private lemma litLoop_inv {n k : Nat} (R : Nat) (e : Fin k) :
    ∀ (t : Nat) (ht : t ≤ n) acc (h : DetInv n k e acc.1 acc.2.1 acc.2.2),
      let res := litLoop R e t ht acc
      DetInv n k e res.1 res.2.1 res.2.2 := by
  intro t
  induction t with
  | zero => intro _ acc h; exact h
  | succ t ih =>
    intro ht acc h
    exact litStep_inv R e ⟨t, ht⟩ _ _ _ (ih (by omega) acc h)

private lemma litLoop_cnt_factor {n k : Nat} (on : Fin k → Bool)
    (lit : Fin k → Fin n → Bool → Bool) (R : Nat) (e : Fin k) (y : Fin n → Bool) (d : Bool) :
    ∀ (t : Nat) (ht : t ≤ n) acc (h : DetInv n k e acc.1 acc.2.1 acc.2.2),
      let res := litLoop R e t ht acc
      let hres := litLoop_inv R e t ht acc h
      ∃ M : Nat,
        cntXD on lit res.1 res.2.1 hres.xinv.x_lt res.2.2 hres.det_lt y d =
          cntXD on lit acc.1 acc.2.1 h.xinv.x_lt acc.2.2 h.det_lt y d * M ∧
        ((on e = false ∨ d = true) → 0 < M ∧ M % (2 ^ R) = 1 % (2 ^ R)) ∧
        (on e = true → d = false → (∀ i : Fin n, i.val < t → lit e i (y i) = false) → M = 1) ∧
        (on e = true → d = false → (∃ i : Fin n, i.val < t ∧ lit e i (y i) = true) →
          M % (2 ^ R) = 0) := by
  intro t
  induction t with
  | zero =>
    intro _ acc h
    refine ⟨1, by simp [litLoop], ?_, ?_, ?_⟩
    · intro _; exact ⟨by omega, rfl⟩
    · intro _ _ _; rfl
    · intro _ _ ⟨i, hi, _⟩; omega
  | succ t ih =>
    intro ht acc h
    obtain ⟨Mprev, hcnt, hpos, hall, hex⟩ := ih (by omega) acc h
    set prev := litLoop R e t (by omega) acc
    have hprev_inv := litLoop_inv R e t (by omega) acc h
    have hstep := litStep_cnt on lit R e ⟨t, ht⟩ prev.1 prev.2.1 prev.2.2 hprev_inv y d
    let fac := fPos (on e) (lit e ⟨t, ht⟩ true) (y ⟨t, ht⟩) d *
      fNeg (on e) (lit e ⟨t, ht⟩ false) (y ⟨t, ht⟩) d R
    have hfac := litFactor_props (on e) (lit e ⟨t, ht⟩ true) (lit e ⟨t, ht⟩ false)
      (y ⟨t, ht⟩) d R (Nat.pow_pos (by omega))
    refine ⟨Mprev * fac, ?_, ?_, ?_, ?_⟩
    · dsimp only [litLoop]
      rw [hstep, hcnt, Nat.mul_assoc]
    · intro hor
      have hp1 := hpos hor
      have hp2 := hfac.1 hor
      refine ⟨Nat.mul_pos hp1.1 hp2.1, ?_⟩
      rw [Nat.mul_mod, hp1.2, hp2.2, ← Nat.mul_mod, Nat.mul_one]
    · intro hon hd hall_succ
      have hprev1 := hall hon hd (fun i hi => hall_succ i (by omega))
      have hcur : (if y ⟨t, ht⟩ then lit e ⟨t, ht⟩ true else lit e ⟨t, ht⟩ false) = false := by
        have hct := hall_succ ⟨t, ht⟩ (by dsimp; omega)
        cases hy : y ⟨t, ht⟩ <;> simpa [hy] using hct
      have hfac1 := hfac.2.1 hon hd hcur
      dsimp only [fac]
      rw [hprev1, hfac1, Nat.one_mul]
    · intro hon hd ⟨i, hilt, hlit⟩
      by_cases hlt : i.val < t
      · have hm0 := hex hon hd ⟨i, hlt, hlit⟩
        rw [Nat.mul_mod, hm0, Nat.zero_mul, Nat.zero_mod]
      · have hieq : i = ⟨t, ht⟩ := Fin.ext (by dsimp; omega)
        subst hieq
        have hcur : (if y ⟨t, ht⟩ then lit e ⟨t, ht⟩ true else lit e ⟨t, ht⟩ false) = true := by
          cases hy : y ⟨t, ht⟩ <;> simpa [hy] using hlit
        have hfac0 := hfac.2.2 hon hd hcur
        rw [Nat.mul_mod, hfac0, Nat.mul_zero, Nat.zero_mod]

private def detStep {n k : Nat} (R : Nat) (e : Fin k) (st : GState n k)
    (xCur : Fin n → Nat) : GState n k × (Fin n → Nat) :=
  let r0 := allocDetStep e st xCur
  let r1 := litLoop R e n (Nat.le_refl n) (r0.1, xCur, r0.2)
  (r1.1, r1.2.1)

private lemma detStep_m {n k : Nat} (R : Nat) (e : Fin k) (st : GState n k) (xCur : Fin n → Nat) :
    (detStep R e st xCur).1.m = st.m + (1 + n * (8 + 6 * R)) := by
  dsimp only [detStep]
  rw [litLoop_m]
  have h0 : (allocDetStep e st xCur).1.m = st.m + 1 := rfl
  rw [h0]
  omega

private lemma detStep_inv {n k : Nat} (R : Nat) (e : Fin k) (st : GState n k)
    (xCur : Fin n → Nat) (hinv : XInv n k st xCur) :
    let res := detStep R e st xCur
    XInv n k res.1 res.2 :=
  (litLoop_inv R e n (Nat.le_refl n) _ (allocDet_inv e st xCur hinv)).xinv

private lemma detStep_cnt {n k : Nat} (on : Fin k → Bool) (lit : Fin k → Fin n → Bool → Bool)
    (R : Nat) (e : Fin k) (st : GState n k) (xCur : Fin n → Nat)
    (hinv : XInv n k st xCur) (y : Fin n → Bool) :
    let res := detStep R e st xCur
    let hres := detStep_inv R e st xCur hinv
    ∃ M : Nat,
      cntX on lit res.1 res.2 hres.x_lt y = cntX on lit st xCur hinv.x_lt y * M ∧
      0 < M ∧
      M % (2 ^ R) = (if on e = true ∧ ∀ i : Fin n, lit e i (y i) = false then 2 else 1) % (2 ^ R) := by
  set r0 := allocDetStep e st xCur
  have h0 := allocDet_inv e st xCur hinv
  set r1 := litLoop R e n (Nat.le_refl n) (r0.1, xCur, r0.2)
  have h1 := litLoop_inv R e n (Nat.le_refl n) (r0.1, xCur, r0.2) h0
  obtain ⟨Mf, hcnt_f, hpos_f, hall_f, hex_f⟩ :=
    litLoop_cnt_factor on lit R e y false n (Nat.le_refl n) (r0.1, xCur, r0.2) h0
  obtain ⟨Mt, hcnt_t, hpos_t, _, _⟩ :=
    litLoop_cnt_factor on lit R e y true n (Nat.le_refl n) (r0.1, xCur, r0.2) h0
  have ha_f := allocDet_cnt on lit e st xCur hinv y false
  have ha_t := allocDet_cnt on lit e st xCur hinv y true
  have hsplit : cntX on lit r1.1 r1.2.1 h1.xinv.x_lt y =
      cntXD on lit r1.1 r1.2.1 h1.xinv.x_lt r1.2.2 h1.det_lt y false +
      cntXD on lit r1.1 r1.2.1 h1.xinv.x_lt r1.2.2 h1.det_lt y true := by
    unfold cntX cntXD
    rw [card_split_bool
      (fun v : Fin r1.1.m → Bool => ValidV r1.1.m r1.1.edges (actFn on lit r1.1.source) v ∧
        (fun i => v ⟨r1.2.1 i, h1.xinv.x_lt i⟩) = y)
      ⟨r1.2.2, h1.det_lt⟩]
    congr 1
    · congr 1; ext v; simp [and_assoc]
    · congr 1; ext v; simp [and_assoc]
  dsimp only at ha_f ha_t hcnt_f hcnt_t
  have htot : cntX on lit r1.1 r1.2.1 h1.xinv.x_lt y =
      cntX on lit st xCur hinv.x_lt y * (if on e = false ∧ false = true then 0 else 1) * Mf +
      cntX on lit st xCur hinv.x_lt y * (if on e = false ∧ true = true then 0 else 1) * Mt := by
    rw [hsplit, hcnt_f, hcnt_t, ha_f, ha_t]
  cases hon : on e
  · have hpf := hpos_f (Or.inl hon)
    refine ⟨Mf, ?_, hpf.1, ?_⟩
    · change cntX on lit r1.1 r1.2.1 h1.xinv.x_lt y = _
      rw [htot]
      simp [hon]
    · simp [hpf.2]
  · have hpt := hpos_t (Or.inr rfl)
    refine ⟨Mf + Mt, ?_, by omega, ?_⟩
    · change cntX on lit r1.1 r1.2.1 h1.xinv.x_lt y = _
      rw [htot]
      simp only [hon, Bool.true_eq_false, false_and, ↓reduceIte, Nat.mul_one, ← Nat.mul_add]
    · by_cases hviol : ∀ i : Fin n, lit e i (y i) = false
      · have hmf1 : Mf = 1 := hall_f hon rfl (fun i _ => hviol i)
        have hite : (if true = true ∧ ∀ i : Fin n, lit e i (y i) = false then 2 else 1) = 2 := by
          simp [hviol]
        rw [hite, hmf1, Nat.add_mod, hpt.2, ← Nat.add_mod]
      · have hex' : ∃ i : Fin n, i.val < n ∧ lit e i (y i) = true := by
          by_contra hc
          apply hviol
          intro i
          cases hli : lit e i (y i)
          · rfl
          · exact absurd ⟨i, i.isLt, hli⟩ hc
        have hmf0 : Mf % (2 ^ R) = 0 := hex_f hon rfl hex'
        have hite : (if true = true ∧ ∀ i : Fin n, lit e i (y i) = false then 2 else 1) = 1 := by
          simp [hviol]
        rw [hite, Nat.add_mod, hmf0, hpt.2, Nat.zero_add, Nat.mod_mod]

private def detLoop {n k : Nat} (R : Nat) (e : Fin k) :
    Nat → GState n k × (Fin n → Nat) → GState n k × (Fin n → Nat)
  | 0, acc => acc
  | d + 1, acc =>
    let prev := detLoop R e d acc
    detStep R e prev.1 prev.2

private lemma detLoop_m {n k : Nat} (R : Nat) (e : Fin k) :
    ∀ d (acc : GState n k × (Fin n → Nat)),
      (detLoop R e d acc).1.m = acc.1.m + d * (1 + n * (8 + 6 * R)) := by
  intro d
  induction d with
  | zero => intro acc; simp [detLoop]
  | succ d ih =>
    intro acc
    dsimp only [detLoop]
    rw [detStep_m, ih acc, Nat.add_mul, Nat.one_mul]
    omega

private lemma detLoop_inv {n k : Nat} (R : Nat) (e : Fin k) :
    ∀ d acc, XInv n k acc.1 acc.2 →
      let res := detLoop R e d acc
      XInv n k res.1 res.2 := by
  intro d
  induction d with
  | zero => intro acc h; exact h
  | succ d ih =>
    intro acc h
    exact detStep_inv R e _ _ (ih acc h)

private lemma detLoop_cnt {n k : Nat} (on : Fin k → Bool) (lit : Fin k → Fin n → Bool → Bool)
    (R : Nat) (e : Fin k) (y : Fin n → Bool) :
    ∀ d acc (h : XInv n k acc.1 acc.2),
      let res := detLoop R e d acc
      let hres := detLoop_inv R e d acc h
      ∃ M : Nat,
        cntX on lit res.1 res.2 hres.x_lt y = cntX on lit acc.1 acc.2 h.x_lt y * M ∧
        0 < M ∧
        M % (2 ^ R) =
          ((if on e = true ∧ ∀ i : Fin n, lit e i (y i) = false then 2 else 1) ^ d) % (2 ^ R) := by
  intro d
  induction d with
  | zero =>
    intro acc h
    exact ⟨1, by simp [detLoop], by omega, by simp⟩
  | succ d ih =>
    intro acc h
    obtain ⟨Mprev, hcnt, hpos, hmod⟩ := ih acc h
    set prev := detLoop R e d acc
    have hprev_inv := detLoop_inv R e d acc h
    obtain ⟨Mstep, hs_cnt, hs_pos, hs_mod⟩ := detStep_cnt on lit R e prev.1 prev.2 hprev_inv y
    refine ⟨Mprev * Mstep, ?_, Nat.mul_pos hpos hs_pos, ?_⟩
    · dsimp only [detLoop]
      rw [hs_cnt, hcnt, Nat.mul_assoc]
    · rw [Nat.mul_mod, hmod, hs_mod, ← Nat.mul_mod, ← pow_succ]

private def clauseLoop {n k : Nat} (b R : Nat) :
    (c : Nat) → c ≤ k → GState n k × (Fin n → Nat) → GState n k × (Fin n → Nat)
  | 0, _, acc => acc
  | c + 1, hc, acc =>
    let prev := clauseLoop b R c (by omega) acc
    detLoop R ⟨c, hc⟩ b prev

private lemma clauseLoop_m {n k : Nat} (b R : Nat) :
    ∀ (c : Nat) (hc : c ≤ k) (acc : GState n k × (Fin n → Nat)),
      (clauseLoop b R c hc acc).1.m = acc.1.m + c * (b * (1 + n * (8 + 6 * R))) := by
  intro c
  induction c with
  | zero => intro _ acc; simp [clauseLoop]
  | succ c ih =>
    intro hc acc
    dsimp only [clauseLoop]
    rw [detLoop_m, ih (by omega) acc, Nat.add_mul, Nat.one_mul]
    omega

private lemma clauseLoop_inv {n k : Nat} (b R : Nat) :
    ∀ (c : Nat) (hc : c ≤ k) acc, XInv n k acc.1 acc.2 →
      let res := clauseLoop b R c hc acc
      XInv n k res.1 res.2 := by
  intro c
  induction c with
  | zero => intro _ acc h; exact h
  | succ c ih =>
    intro hc acc h
    exact detLoop_inv R ⟨c, hc⟩ b _ (ih (by omega) acc h)

private def violUpTo {n k : Nat} (on : Fin k → Bool) (lit : Fin k → Fin n → Bool → Bool)
    (c : Nat) (y : Fin n → Bool) : Nat :=
  ((Finset.univ : Finset (Fin k)).filter
    (fun e => e.val < c ∧ on e = true ∧ ∀ i : Fin n, lit e i (y i) = false)).card

private lemma violUpTo_zero {n k : Nat} (on : Fin k → Bool)
    (lit : Fin k → Fin n → Bool → Bool) (y : Fin n → Bool) :
    violUpTo on lit 0 y = 0 := by
  unfold violUpTo
  simp

private lemma violUpTo_succ {n k : Nat} (on : Fin k → Bool)
    (lit : Fin k → Fin n → Bool → Bool) (c : Nat) (hc : c < k) (y : Fin n → Bool) :
    violUpTo on lit (c + 1) y = violUpTo on lit c y +
      (if on ⟨c, hc⟩ = true ∧ ∀ i : Fin n, lit ⟨c, hc⟩ i (y i) = false then 1 else 0) := by
  unfold violUpTo
  by_cases hv : on ⟨c, hc⟩ = true ∧ ∀ i : Fin n, lit ⟨c, hc⟩ i (y i) = false
  · have hite : (if on ⟨c, hc⟩ = true ∧ ∀ i : Fin n, lit ⟨c, hc⟩ i (y i) = false then 1 else 0) = 1 := by
      simp [hv]
    rw [hite]
    have hset : (Finset.univ : Finset (Fin k)).filter
        (fun e => e.val < c + 1 ∧ on e = true ∧ ∀ i, lit e i (y i) = false) =
        insert ⟨c, hc⟩ ((Finset.univ : Finset (Fin k)).filter
          (fun e => e.val < c ∧ on e = true ∧ ∀ i, lit e i (y i) = false)) := by
      ext e
      simp only [mem_filter, mem_univ, true_and, mem_insert]
      constructor
      · intro ⟨hlt, hon, hall⟩
        by_cases he : e.val < c
        · exact Or.inr ⟨he, hon, hall⟩
        · left; exact Fin.ext (by dsimp; omega)
      · intro h
        rcases h with rfl | ⟨hlt, hon, hall⟩
        · exact ⟨by dsimp; omega, hv.1, hv.2⟩
        · exact ⟨by omega, hon, hall⟩
    have hnot : (⟨c, hc⟩ : Fin k) ∉ (Finset.univ : Finset (Fin k)).filter
        (fun e => e.val < c ∧ on e = true ∧ ∀ i, lit e i (y i) = false) := by
      simp
    rw [hset, Finset.card_insert_of_notMem hnot]
  · have hite : (if on ⟨c, hc⟩ = true ∧ ∀ i : Fin n, lit ⟨c, hc⟩ i (y i) = false then 1 else 0) = 0 := by
      simp [hv]
    rw [hite]
    simp only [add_zero]
    apply congrArg Finset.card
    ext e
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · intro ⟨hlt, hon, hall⟩
      refine ⟨?_, hon, hall⟩
      by_contra hge
      have heq : e = ⟨c, hc⟩ := Fin.ext (by dsimp; omega)
      subst heq
      exact hv ⟨hon, hall⟩
    · intro ⟨hlt, hon, hall⟩
      exact ⟨by omega, hon, hall⟩

private lemma clauseLoop_cnt {n k : Nat} (on : Fin k → Bool) (lit : Fin k → Fin n → Bool → Bool)
    (b R : Nat) (y : Fin n → Bool) :
    ∀ (c : Nat) (hc : c ≤ k),
      let res := clauseLoop b R c hc (initState n k, initX n)
      let hres := clauseLoop_inv b R c hc (initState n k, initX n) (init_xInv n k)
      0 < cntX on lit res.1 res.2 hres.x_lt y ∧
      cntX on lit res.1 res.2 hres.x_lt y % (2 ^ R) =
        ((2 ^ b) ^ violUpTo on lit c y) % (2 ^ R) := by
  intro c
  induction c with
  | zero =>
    intro _
    have hi := init_cntX on lit y
    dsimp only [clauseLoop]
    rw [hi, violUpTo_zero, pow_zero]
    exact ⟨by omega, rfl⟩
  | succ c ih =>
    intro hc
    obtain ⟨hpos, hmod⟩ := ih (by omega)
    set prev := clauseLoop b R c (by omega) (initState n k, initX n)
    have hprev_inv := clauseLoop_inv b R c (by omega) (initState n k, initX n) (init_xInv n k)
    obtain ⟨M, hcnt, hMpos, hMmod⟩ := detLoop_cnt on lit R ⟨c, hc⟩ y b prev hprev_inv
    dsimp only [clauseLoop]
    rw [hcnt, violUpTo_succ on lit c hc y]
    refine ⟨Nat.mul_pos hpos hMpos, ?_⟩
    rw [Nat.mul_mod, hmod, hMmod, ← Nat.mul_mod]
    by_cases hv : on ⟨c, hc⟩ = true ∧ ∀ i : Fin n, lit ⟨c, hc⟩ i (y i) = false
    · have hite1 : (if on ⟨c, hc⟩ = true ∧ ∀ i : Fin n, lit ⟨c, hc⟩ i (y i) = false then 1 else 0) = 1 := by
        simp [hv]
      have hite2 : (if on ⟨c, hc⟩ = true ∧ ∀ i : Fin n, lit ⟨c, hc⟩ i (y i) = false then 2 else 1) = 2 := by
        simp [hv]
      rw [hite1, hite2, pow_succ]
    · have hite1 : (if on ⟨c, hc⟩ = true ∧ ∀ i : Fin n, lit ⟨c, hc⟩ i (y i) = false then 1 else 0) = 0 := by
        simp [hv]
      have hite2 : (if on ⟨c, hc⟩ = true ∧ ∀ i : Fin n, lit ⟨c, hc⟩ i (y i) = false then 2 else 1) = 1 := by
        simp [hv]
      rw [hite1, hite2, one_pow, Nat.mul_one, Nat.add_zero]

private def bagOfList {m : Nat} (bags : List (Finset Nat))
    (_hlt : ∀ b ∈ bags, ∀ u ∈ b, u < m) (t : Fin bags.length) : Finset (Fin m) :=
  (Finset.univ : Finset (Fin m)).filter (fun i => i.val ∈ bags[t.val]'t.isLt)

private lemma mem_bagOfList {m : Nat} (bags : List (Finset Nat))
    (hlt : ∀ b ∈ bags, ∀ u ∈ b, u < m) (t : Fin bags.length) (i : Fin m) :
    i ∈ bagOfList bags hlt t ↔ i.val ∈ bags[t.val]'t.isLt := by
  simp [bagOfList]

private lemma card_bagOfList_le {m : Nat} (bags : List (Finset Nat))
    (hlt : ∀ b ∈ bags, ∀ u ∈ b, u < m) (t : Fin bags.length) :
    (bagOfList bags hlt t).card ≤ (bags[t.val]'t.isLt).card := by
  unfold bagOfList
  apply Finset.card_le_card_of_injOn (fun i : Fin m => i.val)
  · intro i hi
    simp only [mem_coe, mem_filter, mem_univ, true_and] at hi
    exact hi
  · intro i1 _ i2 _ heq
    exact Fin.ext heq

private lemma card_filter_fintype {α : Type*} (f1 f2 : Fintype α) (p : α → Prop)
    (d1 d2 : DecidablePred p) :
    (@Finset.filter α p d1 (@Finset.univ α f1)).card =
    (@Finset.filter α p d2 (@Finset.univ α f2)).card := by
  congr 1
  ext x
  simp

private lemma main_proof (n k h : Nat) (_hh : 0 < h) :
    let b := n + 1
    let B := 2 ^ b
    ∃ (m : Nat) (nb : (Fin m × Bool) → Finset (Fin m × Bool))
      (source : Fin m → Option (Fin k ⊕ (Fin k × Fin n × Bool))),
      m ≤ n + k * b * (1 + 26 * n + 26 * n * b * h) ∧
      (∀ p, p ∉ nb p ∧ (nb p).card ≤ 3) ∧
      (∀ p q, q ∈ nb p ↔ p ∈ nb q) ∧ (∀ p, ∀ q ∈ nb p, p.2 ≠ q.2) ∧
      (∀ i, (i, true) ∈ nb (i, false)) ∧
      (∃ (l : Nat) (bag : Fin l → Finset (Fin m)),
        l ≤ 2 * m + 1 ∧ (∀ t, (bag t).card ≤ n + 9) ∧ (∀ i, ∃ t, i ∈ bag t) ∧
        (∀ i j, i ≠ j → (∃ a c : Bool, (j, c) ∈ nb (i, a)) →
          ∃ t, i ∈ bag t ∧ j ∈ bag t) ∧
        ∀ i s t u, s ≤ t → t ≤ u → i ∈ bag s → i ∈ bag u → i ∈ bag t) ∧
      ∀ (on : Fin k → Bool) (lit : Fin k → Fin n → Bool → Bool),
        let active := fun i => (source i).elim true (Sum.elim on (fun p => lit p.1 p.2.1 p.2.2))
        let Z := ((Finset.univ : Finset ((Fin m × Bool) → Bool)).filter (fun x =>
          (∀ p, ∀ q ∈ nb p, x p = true ∨ x q = true) ∧
          ∀ i, xor (x (i, false)) (x (i, true)) = active i)).card
        let violations := fun (y : Fin n → Bool) =>
          ((Finset.univ : Finset (Fin k)).filter (fun e =>
            on e = true ∧ ∀ i, lit e i (y i) = false)).card
        0 < Z ∧ ∀ j : Nat, j < h →
          (Z / B ^ j) % B = ((Finset.univ : Finset (Fin n → Bool)).filter
            (fun y => violations y = j)).card := by
  dsimp only
  let b := n + 1
  let B := 2 ^ b
  let R := b * h
  let res := clauseLoop b R k (Nat.le_refl k) (initState n k, initX n)
  have hinv := clauseLoop_inv b R k (Nat.le_refl k) (initState n k, initX n) (init_xInv n k)
  let st := res.1
  let xCur := res.2
  refine ⟨st.m, nbOf st.m st.edges, fun i => st.source i.val,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hm : st.m = n + k * (b * (1 + n * (8 + 6 * R))) :=
      clauseLoop_m b R k (Nat.le_refl k) _
    rw [hm, ← Nat.mul_assoc]
    apply Nat.add_le_add_left
    apply Nat.mul_le_mul_left
    have h1 : n * (8 + 6 * R) = 8 * n + 6 * (n * b * h) := by
      simp only [R, Nat.mul_add]
      have ha : n * 8 = 8 * n := Nat.mul_comm n 8
      have hb : n * (6 * (b * h)) = 6 * (n * b * h) := by
        rw [← Nat.mul_assoc n 6 (b * h), Nat.mul_comm n 6, Nat.mul_assoc 6 n (b * h),
          ← Nat.mul_assoc n b h]
      omega
    have h2 : 26 * n * b * h = 26 * (n * b * h) := by
      rw [Nat.mul_assoc 26 n b, Nat.mul_assoc 26 (n * b) h]
    rw [h1, h2]
    omega
  · intro p
    exact ⟨nbOf_not_mem p, nbOf_card_le hinv.wf.deg_le p⟩
  · intro p q
    exact nbOf_symm p q
  · intro p q hq
    exact nbOf_opp p q hq
  · intro i
    exact nbOf_self_pair i
  · refine ⟨st.bags.length, bagOfList st.bags hinv.wf.bags_lt, ?_, ?_, ?_, ?_, ?_⟩
    · have hbl : st.bags.length ≤ st.m + 1 := hinv.wf.bags_len
      omega
    · intro t
      have h1 := card_bagOfList_le st.bags hinv.wf.bags_lt t
      have h2 := hinv.wf.bags_card (st.bags[t.val]'t.isLt) (List.getElem_mem t.isLt)
      omega
    · intro i
      obtain ⟨bag0, hmem, hi⟩ := hinv.wf.bags_cov i.val i.isLt
      obtain ⟨t, ht, hteq⟩ := List.getElem_of_mem hmem
      refine ⟨⟨t, ht⟩, ?_⟩
      rw [mem_bagOfList, hteq]
      exact hi
    · intro i j hij ⟨a, c, hnb⟩
      have hedge := nbOf_cross_edge hij hnb
      rcases hedge with he | he
      · obtain ⟨bag0, hmem, h1, h2⟩ := hinv.wf.bags_edge (i.val, j.val) he
        obtain ⟨t, ht, hteq⟩ := List.getElem_of_mem hmem
        refine ⟨⟨t, ht⟩, ?_, ?_⟩
        · rw [mem_bagOfList, hteq]; exact h1
        · rw [mem_bagOfList, hteq]; exact h2
      · obtain ⟨bag0, hmem, h1, h2⟩ := hinv.wf.bags_edge (j.val, i.val) he
        obtain ⟨t, ht, hteq⟩ := List.getElem_of_mem hmem
        refine ⟨⟨t, ht⟩, ?_, ?_⟩
        · rw [mem_bagOfList, hteq]; exact h2
        · rw [mem_bagOfList, hteq]; exact h1
    · intro i s t u hst htu his hiu
      rw [mem_bagOfList] at his hiu ⊢
      exact hinv.wf.bags_inter i.val s.val t.val u.val s.isLt t.isLt u.isLt hst htu his hiu
  · intro on lit
    dsimp only
    let Z := ((Finset.univ : Finset ((Fin st.m × Bool) → Bool)).filter (fun x =>
      (∀ p, ∀ q ∈ nbOf st.m st.edges p, x p = true ∨ x q = true) ∧
      ∀ i, xor (x (i, false)) (x (i, true)) = actFn on lit st.source i.val)).card
    let violations := fun (y : Fin n → Bool) =>
      ((Finset.univ : Finset (Fin k)).filter (fun e =>
        on e = true ∧ ∀ i, lit e i (y i) = false)).card
    have hZ_eq : Z = ∑ y : Fin n → Bool, cntX on lit st xCur hinv.x_lt y := by
      have h1 := card_validX_eq_card_validV st.m st.edges (actFn on lit st.source)
      have h2 := card_sum_obsX (ValidV st.m st.edges (actFn on lit st.source)) xCur hinv.x_lt
      exact h1.trans h2
    have hviol_eq : ∀ y : Fin n → Bool, violUpTo on lit k y = violations y := by
      intro y
      unfold violUpTo
      congr 1
      ext e
      simp
    have hBh : 2 ^ R = B ^ h := by
      simp only [R, B, pow_mul]
    have hcnt_all : ∀ y : Fin n → Bool,
        0 < cntX on lit st xCur hinv.x_lt y ∧
        cntX on lit st xCur hinv.x_lt y % (B ^ h) = (B ^ violations y) % (B ^ h) := by
      intro y
      have hc := clauseLoop_cnt on lit b R y k (Nat.le_refl k)
      rw [hviol_eq y, hBh] at hc
      exact hc
    refine ⟨?_, ?_⟩
    · change 0 < Z
      rw [hZ_eq]
      let y0 : Fin n → Bool := fun _ => false
      have hpos0 := (hcnt_all y0).1
      have hle : cntX on lit st xCur hinv.x_lt y0 ≤
          ∑ y : Fin n → Bool, cntX on lit st xCur hinv.x_lt y :=
        Finset.single_le_sum (f := fun y => cntX on lit st xCur hinv.x_lt y)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ y0)
      omega
    · intro j hj
      change (Z / B ^ j) % B =
        ((Finset.univ : Finset (Fin n → Bool)).filter (fun y => violations y = j)).card
      have hB_pos : 0 < B := Nat.pow_pos (by omega)
      have hZ_mod : Z % (B ^ h) = (∑ y : Fin n → Bool, B ^ violations y) % (B ^ h) := by
        rw [hZ_eq]
        exact mod_eq_of_sum_mod Finset.univ
          (fun y => cntX on lit st xCur hinv.x_lt y)
          (fun y => B ^ violations y) (B ^ h)
          (fun y _ => (hcnt_all y).2)
      rw [div_pow_mod_of_mod_pow B hB_pos Z (∑ y : Fin n → Bool, B ^ violations y) h j hj hZ_mod]
      let M := max (k + 1) (j + 1)
      have hviol_lt : ∀ y : Fin n → Bool, violations y < M := by
        intro y
        have hle : violations y ≤ k := by
          calc violations y ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_filter_le _ _
            _ = k := Fintype.card_fin k
        dsimp only [M]
        omega
      rw [sum_pow_eq_sum_card B M violations hviol_lt]
      have hbase := div_pow_mod_base B hB_pos
        (fun v => ((Finset.univ : Finset (Fin n → Bool)).filter (fun y => violations y = v)).card)
        M j (by dsimp only [M]; omega)
        (by
          intro v _
          have hcard_le : ((Finset.univ : Finset (Fin n → Bool)).filter
              (fun y => violations y = v)).card ≤ (Finset.univ : Finset (Fin n → Bool)).card :=
            Finset.card_filter_le _ _
          have hfun_card : (Finset.univ : Finset (Fin n → Bool)).card = 2 ^ n := by
            change Fintype.card (Fin n → Bool) = 2 ^ n
            rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
          have hlt_B : 2 ^ n < B := by
            have hBeq : B = 2 ^ n * 2 := by simp only [B, b, pow_succ]
            have : 0 < 2 ^ n := Nat.pow_pos (by omega)
            omega
          omega)
      exact hbase

private lemma main_proof_gen (n k h : Nat) (hh : 0 < h) :
    let b := n + 1
    let B := 2 ^ b
    ∃ (m : Nat) (nb : (Fin m × Bool) → Finset (Fin m × Bool))
      (source : Fin m → Option (Fin k ⊕ (Fin k × Fin n × Bool))),
      m ≤ n + k * b * (1 + 26 * n + 26 * n * b * h) ∧
      (∀ p, p ∉ nb p ∧ (nb p).card ≤ 3) ∧
      (∀ p q, q ∈ nb p ↔ p ∈ nb q) ∧ (∀ p, ∀ q ∈ nb p, p.2 ≠ q.2) ∧
      (∀ i, (i, true) ∈ nb (i, false)) ∧
      (∃ (l : Nat) (bag : Fin l → Finset (Fin m)),
        l ≤ 2 * m + 1 ∧ (∀ t, (bag t).card ≤ n + 9) ∧ (∀ i, ∃ t, i ∈ bag t) ∧
        (∀ i j, i ≠ j → (∃ a c : Bool, (j, c) ∈ nb (i, a)) →
          ∃ t, i ∈ bag t ∧ j ∈ bag t) ∧
        ∀ i s t u, s ≤ t → t ≤ u → i ∈ bag s → i ∈ bag u → i ∈ bag t) ∧
      ∀ (on : Fin k → Bool) (lit : Fin k → Fin n → Bool → Bool),
        let active := fun i => (source i).elim true (Sum.elim on (fun p => lit p.1 p.2.1 p.2.2))
        ∀ (fX : Fintype ((Fin m × Bool) → Bool))
          (fK : Fintype (Fin k))
          (fY : Fintype (Fin n → Bool))
          (dZ : DecidablePred (fun x : (Fin m × Bool) → Bool =>
            (∀ p, ∀ q ∈ nb p, x p = true ∨ x q = true) ∧
            ∀ i, xor (x (i, false)) (x (i, true)) = active i))
          (dV : ∀ y : Fin n → Bool, DecidablePred (fun e : Fin k =>
            on e = true ∧ ∀ i, lit e i (y i) = false))
          (dC : ∀ j : Nat, DecidablePred (fun y : Fin n → Bool =>
            (@Finset.filter _ _ (dV y) (@Finset.univ _ fK)).card = j)),
          let Z := (@Finset.filter _ _ dZ (@Finset.univ _ fX)).card
          0 < Z ∧ ∀ j : Nat, j < h →
            (Z / B ^ j) % B = (@Finset.filter _ _ (dC j) (@Finset.univ _ fY)).card := by
  obtain ⟨m, nb, source, hm, h1, h2, h3, h4, hbag, hcount⟩ := main_proof n k h hh
  refine ⟨m, nb, source, hm, h1, h2, h3, h4, hbag, ?_⟩
  intro on lit
  dsimp only
  intro fX fK fY dZ dV dC
  have hc := hcount on lit
  have h1 := hc.1
  have h2 := hc.2
  dsimp only at h1 h2
  refine ⟨?_, ?_⟩
  · convert h1 using 1
    exact card_filter_fintype fX _ _ dZ _
  · intro j hj
    convert h2 j hj using 1
    · congr 2
      exact card_filter_fintype fX _ _ dZ _
    · apply congrArg Finset.card
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact iff_of_eq (congrArg (· = j) (card_filter_fintype fK _ _ (dV y) _))

end PEqualNP.Outside.L_lib_1206

theorem PEqualNP.Outside.L_lib_1206 : (letI : ∀ p : Prop, Decidable p := Classical.propDecidable
∀ n k h : Nat, 0 < h →
  let b := n+1
  let B := 2^b
  ∃ (m : Nat) (nb : (Fin m × Bool) → Finset (Fin m × Bool))
    (source : Fin m → Option (Fin k ⊕ (Fin k × Fin n × Bool))),
    m ≤ n + k*b*(1+26*n+26*n*b*h) ∧
    (∀ p, p ∉ nb p ∧ (nb p).card ≤ 3) ∧
    (∀ p q, q ∈ nb p ↔ p ∈ nb q) ∧ (∀ p, ∀ q ∈ nb p, p.2 ≠ q.2) ∧
    (∀ i, (i,true) ∈ nb (i,false)) ∧
    (∃ (l : Nat) (bag : Fin l → Finset (Fin m)),
      l ≤ 2*m+1 ∧ (∀ t, (bag t).card ≤ n+9) ∧ (∀ i, ∃ t, i ∈ bag t) ∧
      (∀ i j, i ≠ j → (∃ a c : Bool, (j,c) ∈ nb (i,a)) →
        ∃ t, i ∈ bag t ∧ j ∈ bag t) ∧
      ∀ i s t u, s ≤ t → t ≤ u → i ∈ bag s → i ∈ bag u → i ∈ bag t) ∧
    ∀ (on : Fin k → Bool) (lit : Fin k → Fin n → Bool → Bool),
      let active := fun i => (source i).elim true (Sum.elim on (fun p => lit p.1 p.2.1 p.2.2))
      let Z := ((Finset.univ : Finset ((Fin m × Bool) → Bool)).filter (fun x =>
        (∀ p, ∀ q ∈ nb p, x p = true ∨ x q = true) ∧
        ∀ i, xor (x (i,false)) (x (i,true)) = active i)).card
      let violations := fun (y : Fin n → Bool) =>
        ((Finset.univ : Finset (Fin k)).filter (fun e =>
          on e = true ∧ ∀ i, lit e i (y i) = false)).card
      0 < Z ∧ ∀ j : Nat, j < h →
        (Z / B^j) % B = ((Finset.univ : Finset (Fin n → Bool)).filter
          (fun y => violations y = j)).card) := by
  intro n k h hh
  obtain ⟨m, nb, source, hm, h1, h2, h3, h4, hbag, hcount⟩ :=
    PEqualNP.Outside.L_lib_1206.main_proof_gen n k h hh
  exact ⟨m, nb, source, hm, h1, h2, h3, h4, hbag, fun on lit => hcount on lit _ _ _ _ _ _⟩

import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1000

open Finset

variable {q m : ℕ}

abbrev W (q m : ℕ) := Fin m → Fin q

def dd (x y : W q m) : ℕ := (univ.filter (fun i => x i ≠ y i)).card

theorem dd_comm (x y : W q m) : dd x y = dd y x := by
  unfold dd; congr 1; ext i; simp [ne_comm]

theorem key {u v : W q m} (h : dd u v ≤ 1) (a b : Fin m) (hab : a ≠ b) :
    u a = v a ∨ u b = v b := by
  by_contra hc
  push Not at hc
  have hsub : ({a, b} : Finset (Fin m)) ⊆ univ.filter (fun i => u i ≠ v i) := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp [hc.1, hc.2]
  have := card_le_card hsub
  rw [card_pair hab] at this
  unfold dd at h
  omega

theorem three {u v : W q m} (a b c : Fin m) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : u a ≠ v a) (hb : u b ≠ v b) (hc : u c ≠ v c) : 3 ≤ dd u v := by
  have hsub : ({a, b, c} : Finset (Fin m)) ⊆ univ.filter (fun i => u i ≠ v i) := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> simp [ha, hb, hc]
  have := card_le_card hsub
  rw [card_insert_of_notMem (by simp [hab, hac]), card_pair hbc] at this
  unfold dd
  omega

theorem dd_self (x : W q m) : dd x x = 0 := by
  unfold dd; simp

theorem ne_of_dd {x y : W q m} (h : 2 ≤ dd x y) :
    ∃ i j, i ≠ j ∧ x i ≠ y i ∧ x j ≠ y j := by
  have h1 : 1 < (univ.filter (fun i => x i ≠ y i)).card := by unfold dd at h; omega
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp h1
  simp only [mem_filter, mem_univ, true_and] at ha hb
  exact ⟨a, b, hab, ha, hb⟩

/-- counting function -/
def cnt (P : W q m → W q m → Prop) [DecidableRel P] (A B : Finset (W q m)) : ℕ :=
  ∑ x ∈ A, (B.filter (fun y => P x y)).card

theorem cnt_eq (P : W q m → W q m → Prop) [DecidableRel P] (A B : Finset (W q m)) :
    cnt P A B = ∑ x ∈ A, ∑ y ∈ B, if P x y then 1 else 0 := by
  unfold cnt; apply sum_congr rfl; intro x _; rw [card_filter]

theorem prod_eq (P : W q m → W q m → Prop) [DecidableRel P] (A B : Finset (W q m)) :
    ((A ×ˢ B).filter (fun p => P p.1 p.2)).card = cnt P A B := by
  rw [cnt_eq, card_filter, sum_product]

theorem cnt_symm (P : W q m → W q m → Prop) [DecidableRel P] (hP : ∀ x y, P x y ↔ P y x)
    (A B : Finset (W q m)) : cnt P A B = cnt P B A := by
  rw [cnt_eq, cnt_eq, sum_comm]
  apply sum_congr rfl; intro x _; apply sum_congr rfl; intro y _
  simp [hP x y]

theorem cnt_split (P : W q m → W q m → Prop) [DecidableRel P] (S : Finset (W q m))
    (Q : W q m → Prop) [DecidablePred Q] :
    cnt P S S = cnt P (S.filter Q) (S.filter Q) + cnt P (S.filter Q) (S.filter (fun x => ¬ Q x))
      + cnt P (S.filter (fun x => ¬ Q x)) (S.filter Q)
      + cnt P (S.filter (fun x => ¬ Q x)) (S.filter (fun x => ¬ Q x)) := by
  have hS := filter_union_filter_not_eq (p := Q) S
  have hd := disjoint_filter_filter_not S S Q
  simp only [cnt_eq]
  conv_lhs => rw [← hS]
  simp only [sum_union hd, sum_add_distrib]
  ring

/-- vertices of a ball have few neighbours inside it -/
theorem inner_bound (c x : W q m) (hx : dd c x ≤ 1) (hxc : x ≠ c) (B : Finset (W q m))
    (hB : ∀ y ∈ B, dd c y ≤ 1) : (B.filter (fun y => dd x y = 1)).card ≤ q := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hxc
  have hcx : ∀ l, l ≠ i → c l = x l := by
    intro l hl
    rcases key hx i l (Ne.symm hl) with h | h
    · exact absurd h.symm hi
    · exact h
  calc (B.filter (fun y => dd x y = 1)).card ≤ (univ : Finset (Fin q)).card := by
        apply card_le_card_of_injOn (fun y => y i)
        · intro y _; exact mem_coe.mpr (mem_univ _)
        · intro y1 hy1 y2 hy2 he
          simp only [coe_filter, Set.mem_ofPred_eq] at hy1 hy2
          have hdet : ∀ y ∈ B, dd x y = 1 → ∀ l, l ≠ i → y l = x l := by
            intro y hy hxy l hl
            by_contra hne
            rcases key (le_of_eq hxy) i l (Ne.symm hl) with h | h
            · rcases key (hB y hy) i l (Ne.symm hl) with h2 | h2
              · exact hi (h.trans h2.symm)
              · exact hne (h2.symm.trans (hcx l hl))
            · exact hne h.symm
          funext l
          by_cases hl : l = i
          · subst hl; exact he
          · rw [hdet y1 hy1.1 hy1.2 l hl, hdet y2 hy2.1 hy2.2 l hl]
    _ = q := by simp

theorem cross_bound (c w b0 : W q m) (hw : ¬ dd c w ≤ 1) (hb0 : dd c b0 ≤ 1)
    (hwb0 : dd w b0 = 1) (B : Finset (W q m)) (hB : ∀ y ∈ B, dd c y ≤ 1) :
    (B.filter (fun y => dd w y = 1)).card ≤ 2 ∧
      (B.filter (fun y => ¬ 3 ≤ dd w y)).card ≤ 2 * q := by
  obtain ⟨i, j, hij, hi, hj⟩ := ne_of_dd (x := c) (y := w) (by omega)
  have hwb0' : dd w b0 ≤ 1 := le_of_eq hwb0
  have hout : ∀ l, l ≠ i → l ≠ j → w l = c l := by
    intro l hli hlj
    by_contra hl
    have Hi : ¬ (w i = b0 i ∧ c i = b0 i) := fun h => hi (h.2.trans h.1.symm)
    have Hj : ¬ (w j = b0 j ∧ c j = b0 j) := fun h => hj (h.2.trans h.1.symm)
    have Hl : ¬ (w l = b0 l ∧ c l = b0 l) := fun h => hl (h.1.trans h.2.symm)
    have a1 := key hwb0' i j hij
    have a2 := key hwb0' i l (Ne.symm hli)
    have a3 := key hwb0' j l (Ne.symm hlj)
    have b1 := key hb0 i j hij
    have b2 := key hb0 i l (Ne.symm hli)
    have b3 := key hb0 j l (Ne.symm hlj)
    tauto
  have hbl : ∀ y ∈ B, ¬ 3 ≤ dd w y → ∀ l, l ≠ i → l ≠ j → y l = c l := by
    intro y hy h3 l hli hlj
    by_contra hl
    have hyB := hB y hy
    have e1 : c i = y i := by
      rcases key hyB i l (Ne.symm hli) with h | h
      · exact h
      · exact absurd h.symm hl
    have e2 : c j = y j := by
      rcases key hyB j l (Ne.symm hlj) with h | h
      · exact h
      · exact absurd h.symm hl
    apply h3
    apply three i j l hij (Ne.symm hli) (Ne.symm hlj)
    · rw [← e1]; exact hi.symm
    · rw [← e2]; exact hj.symm
    · rw [hout l hli hlj]; exact Ne.symm hl
  constructor
  · calc (B.filter (fun y => dd w y = 1)).card ≤ (univ : Finset Bool).card := by
          apply card_le_card_of_injOn (fun y => decide (y i = c i))
          · intro y _; exact mem_coe.mpr (mem_univ _)
          · intro y1 hy1 y2 hy2 he
            simp only [coe_filter, Set.mem_ofPred_eq] at hy1 hy2
            have hdet : ∀ y ∈ B, dd w y = 1 →
                (y i = c i → y j = w j) ∧ (y i ≠ c i → y i = w i ∧ y j = c j) := by
              intro y hy h1
              have hk := key (le_of_eq h1) i j hij
              have hk2 := key (hB y hy) i j hij
              constructor
              · intro h
                rcases hk with h' | h'
                · exact absurd (h'.trans h) hi.symm
                · exact h'.symm
              · intro h
                have hyj : y j = c j := by
                  rcases hk2 with h' | h'
                  · exact absurd h'.symm h
                  · exact h'.symm
                refine ⟨?_, hyj⟩
                rcases hk with h' | h'
                · exact h'.symm
                · exact absurd (h'.trans hyj) hj.symm
            have n1 : ¬ 3 ≤ dd w y1 := by omega
            have n2 : ¬ 3 ≤ dd w y2 := by omega
            obtain ⟨d1, d1'⟩ := hdet y1 hy1.1 hy1.2
            obtain ⟨d2, d2'⟩ := hdet y2 hy2.1 hy2.2
            simp only [decide_eq_decide] at he
            funext l
            by_cases hli : l = i
            · subst hli
              by_cases h1 : y1 l = c l
              · rw [h1, he.mp h1]
              · have h2 : y2 l ≠ c l := fun h => h1 (he.mpr h)
                rw [(d1' h1).1, (d2' h2).1]
            · by_cases hlj : l = j
              · subst hlj
                by_cases h1 : y1 i = c i
                · rw [d1 h1, d2 (he.mp h1)]
                · have h2 : y2 i ≠ c i := fun h => h1 (he.mpr h)
                  rw [(d1' h1).2, (d2' h2).2]
              · rw [hbl y1 hy1.1 n1 l hli hlj, hbl y2 hy2.1 n2 l hli hlj]
      _ = 2 := by simp
  · calc (B.filter (fun y => ¬ 3 ≤ dd w y)).card ≤ (univ : Finset (Fin q ⊕ Fin q)).card := by
          apply card_le_card_of_injOn
            (fun y => if y i = c i then Sum.inl (y j) else Sum.inr (y i))
          · intro y _; exact mem_coe.mpr (mem_univ _)
          · intro y1 hy1 y2 hy2 he
            simp only [coe_filter, Set.mem_ofPred_eq] at hy1 hy2
            have hj1 : y1 i ≠ c i → y1 j = c j := by
              intro h
              rcases key (hB y1 hy1.1) i j hij with h' | h'
              · exact absurd h'.symm h
              · exact h'.symm
            have hj2 : y2 i ≠ c i → y2 j = c j := by
              intro h
              rcases key (hB y2 hy2.1) i j hij with h' | h'
              · exact absurd h'.symm h
              · exact h'.symm
            funext l
            by_cases h1 : y1 i = c i <;> by_cases h2 : y2 i = c i <;>
              simp only [h1, h2, ite_true, ite_false, Sum.inl.injEq, Sum.inr.injEq,
                reduceCtorEq] at he
            · by_cases hli : l = i
              · subst hli; rw [h1, h2]
              · by_cases hlj : l = j
                · subst hlj; exact he
                · rw [hbl y1 hy1.1 hy1.2 l hli hlj, hbl y2 hy2.1 hy2.2 l hli hlj]
            · by_cases hli : l = i
              · subst hli; exact he
              · by_cases hlj : l = j
                · subst hlj; rw [hj1 h1, hj2 h2]
                · rw [hbl y1 hy1.1 hy1.2 l hli hlj, hbl y2 hy2.1 hy2.2 l hli hlj]
      _ = 2 * q := by simp; ring


theorem main (k : ℕ) (hk : 0 < k) : ∀ (n : ℕ) (S : Finset (W q m)), S.card = n →
    k * cnt (fun x y => dd x y = 1) S S ≤
      k * (3 * q + 2 * k) * S.card + cnt (fun x y => 3 ≤ dd x y) S S := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S hSn
  by_cases hbig : ∃ c ∈ S, 2 * q + 2 * k ≤ (S.filter (fun y => dd c y ≤ 1)).card
  · obtain ⟨c, hcS, hc⟩ := hbig
    set B := S.filter (fun y => dd c y ≤ 1) with hBdef
    set R := S.filter (fun y => ¬ dd c y ≤ 1) with hRdef
    have hBmem : ∀ y ∈ B, dd c y ≤ 1 := by
      intro y hy; rw [hBdef, mem_filter] at hy; exact hy.2
    have hE := cnt_split (fun x y => dd x y = 1) S (fun y => dd c y ≤ 1)
    have hF := cnt_split (fun x y => 3 ≤ dd x y) S (fun y => dd c y ≤ 1)
    rw [← hBdef, ← hRdef] at hE hF
    have hsym1 := cnt_symm (fun x y => dd x y = 1) (by intro x y; rw [dd_comm]) B R
    have hsym3 := cnt_symm (fun x y => 3 ≤ dd x y) (by intro x y; rw [dd_comm]) B R
    have hcard : S.card = B.card + R.card := by
      rw [hBdef, hRdef]; exact (card_filter_add_card_filter_not (s := S) _).symm
    have hcB : c ∈ B := by rw [hBdef, mem_filter]; simp [hcS, dd_self]
    have hRlt : R.card < n := by
      have : 0 < B.card := card_pos.mpr ⟨c, hcB⟩
      omega
    have hIH := ih R.card hRlt R rfl
    -- internal
    have hBB : cnt (fun x y => dd x y = 1) B B ≤ B.card + q * B.card := by
      unfold cnt
      calc ∑ x ∈ B, (B.filter (fun y => dd x y = 1)).card
          ≤ ∑ x ∈ B, ((if x = c then B.card else 0) + q) := by
            apply sum_le_sum; intro x hx
            by_cases hxc : x = c
            · simp only [hxc, if_true]
              have := card_filter_le B (fun y => dd c y = 1)
              omega
            · simp only [hxc, if_false, zero_add]
              exact inner_bound c x (hBmem x hx) hxc B hBmem
        _ = B.card + q * B.card := by
            rw [sum_add_distrib, sum_ite_eq' B c, if_pos hcB]; simp [mul_comm]
    -- cross
    have hRB : k * cnt (fun x y => dd x y = 1) R B ≤ cnt (fun x y => 3 ≤ dd x y) R B := by
      unfold cnt
      rw [mul_sum]
      apply sum_le_sum
      intro w hw
      have hw' : ¬ dd c w ≤ 1 := by rw [hRdef, mem_filter] at hw; exact hw.2
      by_cases h0 : (B.filter (fun y => dd w y = 1)).card = 0
      · rw [h0]; simp
      · obtain ⟨b0, hb0⟩ := card_pos.mp (Nat.pos_of_ne_zero h0)
        rw [mem_filter] at hb0
        obtain ⟨h2, h2q⟩ := cross_bound c w b0 hw' (hBmem b0 hb0.1) hb0.2 B hBmem
        have hsplit := card_filter_add_card_filter_not (s := B) (fun y => 3 ≤ dd w y)
        have : k * (B.filter (fun y => dd w y = 1)).card ≤ k * 2 :=
          Nat.mul_le_mul_left k h2
        beta_reduce
        omega
    have hkBB : k * cnt (fun x y => dd x y = 1) B B ≤ k * (3 * q + 2 * k) * B.card := by
      calc k * cnt (fun x y => dd x y = 1) B B ≤ k * (B.card + q * B.card) :=
            Nat.mul_le_mul_left k hBB
        _ ≤ k * (3 * q + 2 * k) * B.card := by
            rw [mul_assoc]
            apply Nat.mul_le_mul_left k
            have : B.card + q * B.card = (1 + q) * B.card := by ring
            rw [this]
            apply Nat.mul_le_mul_right
            omega
    rw [hE, hF, hsym1, hsym3, hcard]
    have e1 : k * (cnt (fun x y => dd x y = 1) B B + cnt (fun x y => dd x y = 1) R B +
        cnt (fun x y => dd x y = 1) R B + cnt (fun x y => dd x y = 1) R R) =
        k * cnt (fun x y => dd x y = 1) B B + k * cnt (fun x y => dd x y = 1) R B +
        k * cnt (fun x y => dd x y = 1) R B + k * cnt (fun x y => dd x y = 1) R R := by ring
    have e2 : k * (3 * q + 2 * k) * (B.card + R.card) =
        k * (3 * q + 2 * k) * B.card + k * (3 * q + 2 * k) * R.card := by ring
    rw [e1, e2]
    omega
  · push Not at hbig
    unfold cnt
    calc k * ∑ x ∈ S, (S.filter (fun y => dd x y = 1)).card
        ≤ k * ∑ x ∈ S, (3 * q + 2 * k) := by
          apply Nat.mul_le_mul_left
          apply sum_le_sum; intro x hx
          have h1 := hbig x hx
          have h2 : (S.filter (fun y => dd x y = 1)).card ≤
              (S.filter (fun y => dd x y ≤ 1)).card := by
            apply card_le_card; intro y hy; simp only [mem_filter] at hy ⊢; exact ⟨hy.1, by omega⟩
          exact le_trans h2 (by omega)
      _ = k * (3 * q + 2 * k) * S.card := by rw [sum_const, smul_eq_mul]; ring
      _ ≤ _ := Nat.le_add_right _ _

end PEqualNP.Outside.L_lib_1000

open PEqualNP.Outside.L_lib_1000 in
theorem PEqualNP.Outside.L_lib_1000 : ∀ (q m k : Nat), 2 ≤ q → 0 < k →
  let W := Fin m → Fin q
  let dist := fun (x y : W) =>
    ((Finset.univ : Finset (Fin m)).filter (fun i => x i ≠ y i)).card
  ∀ S : Finset W,
    let pairs := S.product S
    let edges := (pairs.filter (fun p => dist p.1 p.2 = 1)).card
    let far := (pairs.filter (fun p => 3 ≤ dist p.1 p.2)).card
    k * edges ≤ k * (3*q + 2*k) * S.card + far := by
  intro q m k _ hk W0 dist S pairs edges far
  have h1 : edges = cnt (q := q) (m := m) (fun x y => dd x y = 1) S S :=
    prod_eq (fun x y => dd x y = 1) S S
  have h2 : far = cnt (q := q) (m := m) (fun x y => 3 ≤ dd x y) S S :=
    prod_eq (fun x y => 3 ≤ dd x y) S S
  rw [h1, h2]
  exact main k (by omega) S.card S rfl

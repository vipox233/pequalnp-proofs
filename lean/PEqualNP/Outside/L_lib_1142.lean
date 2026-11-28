import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1142

private def sIdx (n : Nat) (j : Nat) (hj : j ≤ n) : Fin (9 * n + 1) :=
  ⟨9 * j, by omega⟩

private def vIdx (n : Nat) (j : Fin n) (c : Nat) (hc : c < 9) : Fin (9 * n + 1) :=
  ⟨9 * j.val + c, by omega⟩

private def mkBag (n : Nat) (k : Fin (6 * n)) : Finset (Fin (9 * n + 1)) :=
  let j : Fin n := ⟨k.val / 6, by omega⟩
  let s := sIdx n j.val (by omega)
  let x := vIdx n j 1 (by omega)
  let H := vIdx n j 2 (by omega)
  let U := vIdx n j 3 (by omega)
  let V := vIdx n j 4 (by omega)
  let E := vIdx n j 5 (by omega)
  let F := vIdx n j 6 (by omega)
  let P := vIdx n j 7 (by omega)
  let Q := vIdx n j 8 (by omega)
  let y := sIdx n (j.val + 1) (by omega)
  match k.val % 6 with
  | 0 => {s, H, x}
  | 1 => {s, H, y}
  | 2 => {s, x, E}
  | 3 => {s, y, F}
  | 4 => {H, U, V}
  | _ => {s, P, Q}

private def mkPar (n : Nat) (k : Fin (6 * n)) : Fin (6 * n) :=
  let j := k.val / 6
  match k.val % 6 with
  | 0 => if h : j = 0 then ⟨0, by omega⟩ else ⟨6 * (j - 1) + 1, by omega⟩
  | 1 => ⟨6 * j, by omega⟩
  | 2 => ⟨6 * j, by omega⟩
  | 3 => ⟨6 * j + 1, by omega⟩
  | 4 => ⟨6 * j, by omega⟩
  | _ => ⟨6 * j, by omega⟩

private def linkClauses (n : Nat) (j : Fin n) : Finset (Finset (Fin (9 * n + 1) × Bool)) :=
  let s := sIdx n j.val (by omega)
  let x := vIdx n j 1 (by omega)
  let H := vIdx n j 2 (by omega)
  let U := vIdx n j 3 (by omega)
  let V := vIdx n j 4 (by omega)
  let E := vIdx n j 5 (by omega)
  let F := vIdx n j 6 (by omega)
  let P := vIdx n j 7 (by omega)
  let Q := vIdx n j 8 (by omega)
  let y := sIdx n (j.val + 1) (by omega)
  { {(H, false), (s, true)},
    {(H, false), (x, true)},
    {(H, false), (y, true)},
    {(U, false), (H, true)},
    {(V, false), (H, true)},
    {(U, false), (V, false)},
    {(E, false), (s, true)},
    {(E, false), (x, false)},
    {(F, false), (s, true)},
    {(F, false), (y, false)},
    {(P, false), (s, false)},
    {(Q, false), (s, false)},
    {(P, false), (Q, false)} }

private def mkF (n : Nat) : Finset (Finset (Fin (9 * n + 1) × Bool)) :=
  insert {(sIdx n n (le_refl n), false)} ((Finset.univ : Finset (Fin n)).biUnion (linkClauses n))

private def linkOk (s x y : Bool) (w : Fin 7 → Bool) : Bool :=
  let H := w 0
  let U := w 1
  let V := w 2
  let E := w 3
  let F := w 4
  let P := w 5
  let Q := w 6
  (!H || s) && (!H || x) && (!H || y) &&
  (!U || H) && (!V || H) && (!U || !V) &&
  (!E || s) && (!E || !x) &&
  (!F || s) && (!F || !y) &&
  (!P || !s) && (!Q || !s) && (!P || !Q)

private def transW (x s y : Bool) : Nat :=
  match x, s, y with
  | false, false, false => 3
  | false, false, true  => 3
  | false, true,  false => 4
  | false, true,  true  => 2
  | true,  false, false => 3
  | true,  false, true  => 3
  | true,  true,  false => 2
  | true,  true,  true  => 4

private lemma card_linkOk (s x y : Bool) :
    ((Finset.univ : Finset (Fin 7 → Bool)).filter (fun w => linkOk s x y w = true)).card =
      transW x s y := by
  revert s x y; decide

private lemma linkClauses_card_le (n : Nat) (j : Fin n) : (linkClauses n j).card ≤ 13 := by
  unfold linkClauses
  repeat (refine (Finset.card_insert_le _ _).trans (Nat.add_le_add_right ?_ 1))
  simp

private lemma mkF_card_le (n : Nat) : (mkF n).card ≤ 13 * n + 1 := by
  unfold mkF
  refine (Finset.card_insert_le _ _).trans ?_
  have hbi : ((Finset.univ : Finset (Fin n)).biUnion (linkClauses n)).card ≤ 13 * n := by
    calc _ ≤ ∑ j : Fin n, (linkClauses n j).card := Finset.card_biUnion_le
      _ ≤ ∑ _j : Fin n, 13 := Finset.sum_le_sum (fun j _ => linkClauses_card_le n j)
      _ = 13 * n := by simp [mul_comm]
  omega

private lemma card_pair_le_two {α : Type*} [DecidableEq α] (a b : α) :
    ({a, b} : Finset α).card ≤ 2 := by
  exact (Finset.card_insert_le a {b}).trans (by simp)

private lemma horn_pair_ft {α : Type*} [DecidableEq α] (a b : α) :
    (({(a, false), (b, true)} : Finset (α × Bool)).filter (fun l => l.2 = true)).card ≤ 1 := by
  have hsub : (({(a, false), (b, true)} : Finset (α × Bool)).filter (fun l => l.2 = true)) ⊆
      {(b, true)} := by
    intro l hl
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at hl ⊢
    rcases hl with ⟨rfl | rfl, h2⟩
    · simp at h2
    · rfl
  exact (Finset.card_le_card hsub).trans (by simp)

private lemma horn_pair_ff {α : Type*} [DecidableEq α] (a b : α) :
    (({(a, false), (b, false)} : Finset (α × Bool)).filter (fun l => l.2 = true)).card ≤ 1 := by
  have hemp : (({(a, false), (b, false)} : Finset (α × Bool)).filter (fun l => l.2 = true)) = ∅ := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
      iff_false, not_and]
    rintro (rfl | rfl) <;> simp
  rw [hemp]; simp

private lemma mkF_clauses_ok {n : Nat} (hn : 0 < n) :
    ∀ C ∈ mkF n, C.card ≤ 2 ∧ (C.filter (fun l => l.2 = true)).card ≤ 1 ∧
      ∃ k : Fin (6 * n), ∀ l ∈ C, l.1 ∈ mkBag n k := by
  intro C hC
  simp only [mkF, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ, true_and] at hC
  rcases hC with rfl | ⟨j, hCj⟩
  · refine ⟨by simp, ?_, ⟨⟨6 * (n - 1) + 1, by omega⟩, ?_⟩⟩
    · have : ({(sIdx n n (le_refl n), false)} : Finset (Fin (9 * n + 1) × Bool)).filter
          (fun l => l.2 = true) = ∅ := by ext l; simp; rintro rfl; simp
      rw [this]; simp
    · intro l hl
      rw [Finset.mem_singleton.mp hl]
      have hdiv : (6 * (n - 1) + 1) / 6 = n - 1 := by omega
      have hmod : (6 * (n - 1) + 1) % 6 = 1 := by omega
      simp only [mkBag, hdiv, hmod]
      have hsn : sIdx n n (le_refl n) = sIdx n (n - 1 + 1) (by omega) := by
        apply Fin.ext; simp [sIdx]; omega
      rw [hsn]
      simp
  · simp only [linkClauses, Finset.mem_insert, Finset.mem_singleton] at hCj
    have hbag : ∀ (m : Nat) (hm : m < 6),
        (6 * j.val + m) / 6 = j.val ∧ (6 * j.val + m) % 6 = m := by
      intro m hm; omega
    rcases hCj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨card_pair_le_two _ _, horn_pair_ft _ _, ⟨⟨6 * j.val + 0, by omega⟩, ?_⟩⟩
      intro l hl; simp only [mkBag, (hbag 0 (by omega)).1, (hbag 0 (by omega)).2]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl ⊢
      rcases hl with rfl | rfl <;> simp
    · refine ⟨card_pair_le_two _ _, horn_pair_ft _ _, ⟨⟨6 * j.val + 0, by omega⟩, ?_⟩⟩
      intro l hl; simp only [mkBag, (hbag 0 (by omega)).1, (hbag 0 (by omega)).2]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl ⊢
      rcases hl with rfl | rfl <;> simp
    · refine ⟨card_pair_le_two _ _, horn_pair_ft _ _, ⟨⟨6 * j.val + 1, by omega⟩, ?_⟩⟩
      intro l hl; simp only [mkBag, (hbag 1 (by omega)).1, (hbag 1 (by omega)).2]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl ⊢
      rcases hl with rfl | rfl <;> simp
    · refine ⟨card_pair_le_two _ _, horn_pair_ft _ _, ⟨⟨6 * j.val + 4, by omega⟩, ?_⟩⟩
      intro l hl; simp only [mkBag, (hbag 4 (by omega)).1, (hbag 4 (by omega)).2]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl ⊢
      rcases hl with rfl | rfl <;> simp
    · refine ⟨card_pair_le_two _ _, horn_pair_ft _ _, ⟨⟨6 * j.val + 4, by omega⟩, ?_⟩⟩
      intro l hl; simp only [mkBag, (hbag 4 (by omega)).1, (hbag 4 (by omega)).2]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl ⊢
      rcases hl with rfl | rfl <;> simp
    · refine ⟨card_pair_le_two _ _, horn_pair_ff _ _, ⟨⟨6 * j.val + 4, by omega⟩, ?_⟩⟩
      intro l hl; simp only [mkBag, (hbag 4 (by omega)).1, (hbag 4 (by omega)).2]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl ⊢
      rcases hl with rfl | rfl <;> simp
    · refine ⟨card_pair_le_two _ _, horn_pair_ft _ _, ⟨⟨6 * j.val + 2, by omega⟩, ?_⟩⟩
      intro l hl; simp only [mkBag, (hbag 2 (by omega)).1, (hbag 2 (by omega)).2]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl ⊢
      rcases hl with rfl | rfl <;> simp
    · refine ⟨card_pair_le_two _ _, horn_pair_ff _ _, ⟨⟨6 * j.val + 2, by omega⟩, ?_⟩⟩
      intro l hl; simp only [mkBag, (hbag 2 (by omega)).1, (hbag 2 (by omega)).2]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl ⊢
      rcases hl with rfl | rfl <;> simp
    · refine ⟨card_pair_le_two _ _, horn_pair_ft _ _, ⟨⟨6 * j.val + 3, by omega⟩, ?_⟩⟩
      intro l hl; simp only [mkBag, (hbag 3 (by omega)).1, (hbag 3 (by omega)).2]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl ⊢
      rcases hl with rfl | rfl <;> simp
    · refine ⟨card_pair_le_two _ _, horn_pair_ff _ _, ⟨⟨6 * j.val + 3, by omega⟩, ?_⟩⟩
      intro l hl; simp only [mkBag, (hbag 3 (by omega)).1, (hbag 3 (by omega)).2]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl ⊢
      rcases hl with rfl | rfl <;> simp
    · refine ⟨card_pair_le_two _ _, horn_pair_ff _ _, ⟨⟨6 * j.val + 5, by omega⟩, ?_⟩⟩
      intro l hl; simp only [mkBag, (hbag 5 (by omega)).1, (hbag 5 (by omega)).2]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl ⊢
      rcases hl with rfl | rfl <;> simp
    · refine ⟨card_pair_le_two _ _, horn_pair_ff _ _, ⟨⟨6 * j.val + 5, by omega⟩, ?_⟩⟩
      intro l hl; simp only [mkBag, (hbag 5 (by omega)).1, (hbag 5 (by omega)).2]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl ⊢
      rcases hl with rfl | rfl <;> simp
    · refine ⟨card_pair_le_two _ _, horn_pair_ff _ _, ⟨⟨6 * j.val + 5, by omega⟩, ?_⟩⟩
      intro l hl; simp only [mkBag, (hbag 5 (by omega)).1, (hbag 5 (by omega)).2]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl ⊢
      rcases hl with rfl | rfl <;> simp

private lemma mkBag_par_ok (n : Nat) (k : Fin (6 * n)) :
    (mkBag n k).card ≤ 3 ∧ mkPar n k ≤ k ∧ (0 < k.val → mkPar n k < k) := by
  have hcard : ∀ (a b c : Fin (9 * n + 1)), ({a, b, c} : Finset (Fin (9 * n + 1))).card ≤ 3 := by
    intro a b c
    exact (Finset.card_insert_le a {b, c}).trans (Nat.add_le_add_right (card_pair_le_two b c) 1)
  have hmod : k.val % 6 = 0 ∨ k.val % 6 = 1 ∨ k.val % 6 = 2 ∨
      k.val % 6 = 3 ∨ k.val % 6 = 4 ∨ k.val % 6 = 5 := by omega
  rcases hmod with hm | hm | hm | hm | hm | hm
  · simp only [mkBag, mkPar, hm]
    refine ⟨hcard _ _ _, ?_, ?_⟩
    · split
      · simp [Fin.le_iff_val_le_val]
      · simp [Fin.le_iff_val_le_val]; omega
    · intro hpos
      split
      · rename_i hj; omega
      · simp [Fin.lt_iff_val_lt_val]; omega
  · simp only [mkBag, mkPar, hm]
    exact ⟨hcard _ _ _, by simp [Fin.le_iff_val_le_val]; omega,
      fun _ => by simp [Fin.lt_iff_val_lt_val]; omega⟩
  · simp only [mkBag, mkPar, hm]
    exact ⟨hcard _ _ _, by simp [Fin.le_iff_val_le_val]; omega,
      fun _ => by simp [Fin.lt_iff_val_lt_val]; omega⟩
  · simp only [mkBag, mkPar, hm]
    exact ⟨hcard _ _ _, by simp [Fin.le_iff_val_le_val]; omega,
      fun _ => by simp [Fin.lt_iff_val_lt_val]; omega⟩
  · simp only [mkBag, mkPar, hm]
    exact ⟨hcard _ _ _, by simp [Fin.le_iff_val_le_val]; omega,
      fun _ => by simp [Fin.lt_iff_val_lt_val]; omega⟩
  · simp only [mkBag, mkPar, hm]
    exact ⟨hcard _ _ _, by simp [Fin.le_iff_val_le_val]; omega,
      fun _ => by simp [Fin.lt_iff_val_lt_val]; omega⟩

private lemma mem_mkBag_iff (n : Nat) (k : Fin (6 * n)) (v : Fin (9 * n + 1)) :
    v ∈ mkBag n k ↔
      let j := k.val / 6
      match k.val % 6 with
      | 0 => v.val = 9 * j ∨ v.val = 9 * j + 2 ∨ v.val = 9 * j + 1
      | 1 => v.val = 9 * j ∨ v.val = 9 * j + 2 ∨ v.val = 9 * (j + 1)
      | 2 => v.val = 9 * j ∨ v.val = 9 * j + 1 ∨ v.val = 9 * j + 5
      | 3 => v.val = 9 * j ∨ v.val = 9 * (j + 1) ∨ v.val = 9 * j + 6
      | 4 => v.val = 9 * j + 2 ∨ v.val = 9 * j + 3 ∨ v.val = 9 * j + 4
      | _ => v.val = 9 * j ∨ v.val = 9 * j + 7 ∨ v.val = 9 * j + 8 := by
  have hmod : k.val % 6 = 0 ∨ k.val % 6 = 1 ∨ k.val % 6 = 2 ∨
      k.val % 6 = 3 ∨ k.val % 6 = 4 ∨ k.val % 6 = 5 := by omega
  rcases hmod with hm | hm | hm | hm | hm | hm <;>
    simp [mkBag, hm, Fin.ext_iff, sIdx, vIdx]

private lemma running_intersection {n : Nat} (hn : 0 < n) (v : Fin (9 * n + 1)) :
    ∃ top : Fin (6 * n), v ∈ mkBag n top ∧
      ∀ k : Fin (6 * n), v ∈ mkBag n k → top ≤ k ∧ (k ≠ top → v ∈ mkBag n (mkPar n k)) := by
  by_cases hv0 : v.val = 0
  · refine ⟨⟨0, by omega⟩, ?_, ?_⟩
    · rw [mem_mkBag_iff]; simp [hv0]
    · intro k hk
      refine ⟨by simp [Fin.le_iff_val_le_val], ?_⟩
      intro hne
      rw [mem_mkBag_iff] at hk ⊢
      have hmod : k.val % 6 = 0 ∨ k.val % 6 = 1 ∨ k.val % 6 = 2 ∨
          k.val % 6 = 3 ∨ k.val % 6 = 4 ∨ k.val % 6 = 5 := by omega
      rcases hmod with hm | hm | hm | hm | hm | hm
      · simp only [hm] at hk
        have hkv : k.val = 0 := by omega
        exact absurd (Fin.ext hkv) hne
      · simp only [hm] at hk
        have hkv : k.val / 6 = 0 := by omega
        simp [mkPar, hm, hkv, hv0]
      · simp only [hm] at hk
        have hkv : k.val / 6 = 0 := by omega
        simp [mkPar, hm, hkv, hv0]
      · simp only [hm] at hk
        have hkv : k.val / 6 = 0 := by omega
        simp [mkPar, hm, hkv, hv0]
      · simp only [hm] at hk; omega
      · simp only [hm] at hk
        have hkv : k.val / 6 = 0 := by omega
        simp [mkPar, hm, hkv, hv0]
  · by_cases hvm : v.val % 9 = 0
    · let q := v.val / 9
      have hq_pos : 0 < q := by omega
      have hq_le : q ≤ n := by omega
      have hv_eq : v.val = 9 * q := by omega
      refine ⟨⟨6 * (q - 1) + 1, by omega⟩, ?_, ?_⟩
      · rw [mem_mkBag_iff]
        have hd : (6 * (q - 1) + 1) / 6 = q - 1 := by omega
        have hm : (6 * (q - 1) + 1) % 6 = 1 := by omega
        simp [hd, hm]; omega
      · intro k hk
        rw [mem_mkBag_iff] at hk
        have hmod : k.val % 6 = 0 ∨ k.val % 6 = 1 ∨ k.val % 6 = 2 ∨
            k.val % 6 = 3 ∨ k.val % 6 = 4 ∨ k.val % 6 = 5 := by omega
        rcases hmod with hm | hm | hm | hm | hm | hm
        · simp only [hm] at hk
          have hj : k.val / 6 = q := by omega
          refine ⟨by simp [Fin.le_iff_val_le_val]; omega, fun _ => ?_⟩
          rw [mem_mkBag_iff]
          have hne0 : q ≠ 0 := by omega
          simp only [mkPar, hm, hj, hne0, dite_false]
          have hd : (6 * (q - 1) + 1) / 6 = q - 1 := by omega
          have hm1 : (6 * (q - 1) + 1) % 6 = 1 := by omega
          simp [hd, hm1]; omega
        · simp only [hm] at hk
          have hj : k.val / 6 = q ∨ k.val / 6 = q - 1 := by omega
          rcases hj with hj | hj
          · refine ⟨by simp [Fin.le_iff_val_le_val]; omega, fun _ => ?_⟩
            rw [mem_mkBag_iff]
            simp only [mkPar, hm, hj]
            have hd : (6 * q) / 6 = q := by omega
            have hm0 : (6 * q) % 6 = 0 := by omega
            simp [hd, hm0, hv_eq]
          · refine ⟨by simp [Fin.le_iff_val_le_val]; omega, fun hne => ?_⟩
            exfalso; apply hne; apply Fin.ext; simp; omega
        · simp only [hm] at hk
          have hj : k.val / 6 = q := by omega
          refine ⟨by simp [Fin.le_iff_val_le_val]; omega, fun _ => ?_⟩
          rw [mem_mkBag_iff]
          simp only [mkPar, hm, hj]
          have hd : (6 * q) / 6 = q := by omega
          have hm0 : (6 * q) % 6 = 0 := by omega
          simp [hd, hm0, hv_eq]
        · simp only [hm] at hk
          have hj : k.val / 6 = q ∨ k.val / 6 = q - 1 := by omega
          rcases hj with hj | hj
          · refine ⟨by simp [Fin.le_iff_val_le_val]; omega, fun _ => ?_⟩
            rw [mem_mkBag_iff]
            simp only [mkPar, hm, hj]
            have hd : (6 * q + 1) / 6 = q := by omega
            have hm1 : (6 * q + 1) % 6 = 1 := by omega
            simp [hd, hm1, hv_eq]
          · refine ⟨by simp [Fin.le_iff_val_le_val]; omega, fun _ => ?_⟩
            rw [mem_mkBag_iff]
            simp only [mkPar, hm, hj]
            have hd : (6 * (q - 1) + 1) / 6 = q - 1 := by omega
            have hm1 : (6 * (q - 1) + 1) % 6 = 1 := by omega
            simp [hd, hm1]; omega
        · simp only [hm] at hk; omega
        · simp only [hm] at hk
          have hj : k.val / 6 = q := by omega
          refine ⟨by simp [Fin.le_iff_val_le_val]; omega, fun _ => ?_⟩
          rw [mem_mkBag_iff]
          simp only [mkPar, hm, hj]
          have hd : (6 * q) / 6 = q := by omega
          have hm0 : (6 * q) % 6 = 0 := by omega
          simp [hd, hm0, hv_eq]
    ·
      let q := v.val / 9
      let c := v.val % 9
      have hq : q < n := by omega
      have hc : c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7 ∨ c = 8 := by omega
      let htop_offset : Nat :=
        if c = 1 ∨ c = 2 then 0
        else if c = 3 ∨ c = 4 then 4
        else if c = 5 then 2
        else if c = 6 then 3
        else 5
      have htop_lt : htop_offset < 6 := by
        dsimp only [htop_offset]
        split <;> [omega; split <;> [omega; split <;> [omega; split <;> omega]]]
      refine ⟨⟨6 * q + htop_offset, by omega⟩, ?_, ?_⟩
      · rw [mem_mkBag_iff]
        have hd : (6 * q + htop_offset) / 6 = q := by omega
        have hm : (6 * q + htop_offset) % 6 = htop_offset := by omega
        rw [hd, hm]
        rcases hc with hc | hc | hc | hc | hc | hc | hc | hc <;>
          (simp [htop_offset, hc]; omega)
      · intro k hk
        rw [mem_mkBag_iff] at hk
        have hmod : k.val % 6 = 0 ∨ k.val % 6 = 1 ∨ k.val % 6 = 2 ∨
            k.val % 6 = 3 ∨ k.val % 6 = 4 ∨ k.val % 6 = 5 := by omega
        rcases hc with hc | hc | hc | hc | hc | hc | hc | hc
        ·
          rcases hmod with hm | hm | hm | hm | hm | hm <;> simp only [hm] at hk
          · have hj : k.val / 6 = q := by omega
            refine ⟨by simp [Fin.le_iff_val_le_val, htop_offset, hc]; omega, fun hne => ?_⟩
            exfalso; apply hne; apply Fin.ext; simp [htop_offset, hc]; omega
          · omega
          · have hj : k.val / 6 = q := by omega
            refine ⟨by simp [Fin.le_iff_val_le_val, htop_offset, hc]; omega, fun _ => ?_⟩
            rw [mem_mkBag_iff]; simp only [mkPar, hm, hj]
            have hd : (6 * q) / 6 = q := by omega
            have hm0 : (6 * q) % 6 = 0 := by omega
            simp [hd, hm0]; omega
          · omega
          · omega
          · omega
        ·
          rcases hmod with hm | hm | hm | hm | hm | hm <;> simp only [hm] at hk
          · have hj : k.val / 6 = q := by omega
            refine ⟨by simp [Fin.le_iff_val_le_val, htop_offset, hc]; omega, fun hne => ?_⟩
            exfalso; apply hne; apply Fin.ext; simp [htop_offset, hc]; omega
          · have hj : k.val / 6 = q := by omega
            refine ⟨by simp [Fin.le_iff_val_le_val, htop_offset, hc]; omega, fun _ => ?_⟩
            rw [mem_mkBag_iff]; simp only [mkPar, hm, hj]
            have hd : (6 * q) / 6 = q := by omega
            have hm0 : (6 * q) % 6 = 0 := by omega
            simp [hd, hm0]; omega
          · omega
          · omega
          · have hj : k.val / 6 = q := by omega
            refine ⟨by simp [Fin.le_iff_val_le_val, htop_offset, hc]; omega, fun _ => ?_⟩
            rw [mem_mkBag_iff]; simp only [mkPar, hm, hj]
            have hd : (6 * q) / 6 = q := by omega
            have hm0 : (6 * q) % 6 = 0 := by omega
            simp [hd, hm0]; omega
          · omega
        ·
          rcases hmod with hm | hm | hm | hm | hm | hm <;> simp only [hm] at hk <;> try omega
          have hj : k.val / 6 = q := by omega
          refine ⟨by simp [Fin.le_iff_val_le_val, htop_offset, hc]; omega, fun hne => ?_⟩
          exfalso; apply hne; apply Fin.ext; simp [htop_offset, hc]; omega
        ·
          rcases hmod with hm | hm | hm | hm | hm | hm <;> simp only [hm] at hk <;> try omega
          have hj : k.val / 6 = q := by omega
          refine ⟨by simp [Fin.le_iff_val_le_val, htop_offset, hc]; omega, fun hne => ?_⟩
          exfalso; apply hne; apply Fin.ext; simp [htop_offset, hc]; omega
        ·
          rcases hmod with hm | hm | hm | hm | hm | hm <;> simp only [hm] at hk <;> try omega
          have hj : k.val / 6 = q := by omega
          refine ⟨by simp [Fin.le_iff_val_le_val, htop_offset, hc]; omega, fun hne => ?_⟩
          exfalso; apply hne; apply Fin.ext; simp [htop_offset, hc]; omega
        ·
          rcases hmod with hm | hm | hm | hm | hm | hm <;> simp only [hm] at hk <;> try omega
          have hj : k.val / 6 = q := by omega
          refine ⟨by simp [Fin.le_iff_val_le_val, htop_offset, hc]; omega, fun hne => ?_⟩
          exfalso; apply hne; apply Fin.ext; simp [htop_offset, hc]; omega
        ·
          rcases hmod with hm | hm | hm | hm | hm | hm <;> simp only [hm] at hk <;> try omega
          have hj : k.val / 6 = q := by omega
          refine ⟨by simp [Fin.le_iff_val_le_val, htop_offset, hc]; omega, fun hne => ?_⟩
          exfalso; apply hne; apply Fin.ext; simp [htop_offset, hc]; omega
        ·
          rcases hmod with hm | hm | hm | hm | hm | hm <;> simp only [hm] at hk <;> try omega
          have hj : k.val / 6 = q := by omega
          refine ⟨by simp [Fin.le_iff_val_le_val, htop_offset, hc]; omega, fun hne => ?_⟩
          exfalso; apply hne; apply Fin.ext; simp [htop_offset, hc]; omega

private def dpCount : ∀ (n : Nat), (Fin n → Bool) → Bool → Nat
  | 0, _, b => if b then 0 else 1
  | n + 1, x, b =>
      transW (x 0) b false * dpCount n (fun j => x j.succ) false +
      transW (x 0) b true * dpCount n (fun j => x j.succ) true

private lemma dpCount_props : ∀ (n : Nat) (x : Fin n → Bool),
    (0 < dpCount n x false) ∧
    (0 < n → 0 < dpCount n x true) ∧
    (if ((Finset.univ : Finset (Fin n)).filter (fun j => x j = false)).card % 2 = 0
     then dpCount n x false = dpCount n x true + 1
     else dpCount n x true = dpCount n x false + 1)
  | 0, x => by simp [dpCount]
  | n + 1, x => by
    have ⟨hposF, _, hdiff⟩ := dpCount_props n (fun j => x j.succ)
    have hcard :
        ((Finset.univ : Finset (Fin (n + 1))).filter (fun j => x j = false)).card =
        (if x 0 = false then 1 else 0) +
        ((Finset.univ : Finset (Fin n)).filter (fun j => x j.succ = false)).card := by
      rw [Fin.univ_succ, Finset.cons_eq_insert, Finset.filter_insert]
      cases hx0 : x 0 with
      | false =>
        simp only [ite_true]
        rw [Finset.card_insert_of_notMem (by simp), Finset.filter_map, Finset.card_map]
        exact Nat.add_comm _ 1
      | true =>
        simp only [Bool.true_eq_false, ite_false, zero_add, Finset.filter_map, Finset.card_map]
        rfl
    have hF : dpCount (n + 1) x false =
        3 * dpCount n (fun j => x j.succ) false + 3 * dpCount n (fun j => x j.succ) true := by
      cases hx0 : x 0 <;> simp [dpCount, transW, hx0]
    cases hx0 : x 0 with
    | false =>
      have hT : dpCount (n + 1) x true =
          4 * dpCount n (fun j => x j.succ) false + 2 * dpCount n (fun j => x j.succ) true := by
        simp [dpCount, transW, hx0]
      simp only [hx0, ite_true] at hcard
      refine ⟨by omega, fun _ => by omega, ?_⟩
      by_cases hp : ((Finset.univ : Finset (Fin n)).filter (fun j => x j.succ = false)).card % 2 = 0
      · simp only [hp, ite_true] at hdiff
        have hp' : ((Finset.univ : Finset (Fin (n + 1))).filter (fun j => x j = false)).card % 2 ≠ 0 := by omega
        simp only [hp', ite_false]; omega
      · simp only [hp, ite_false] at hdiff
        have hp' : ((Finset.univ : Finset (Fin (n + 1))).filter (fun j => x j = false)).card % 2 = 0 := by omega
        simp only [hp', ite_true]; omega
    | true =>
      have hT : dpCount (n + 1) x true =
          2 * dpCount n (fun j => x j.succ) false + 4 * dpCount n (fun j => x j.succ) true := by
        simp [dpCount, transW, hx0]
      simp only [hx0, Bool.true_eq_false, ite_false, zero_add] at hcard
      refine ⟨by omega, fun _ => by omega, ?_⟩
      by_cases hp : ((Finset.univ : Finset (Fin n)).filter (fun j => x j.succ = false)).card % 2 = 0
      · simp only [hp, ite_true] at hdiff
        have hp' : ((Finset.univ : Finset (Fin (n + 1))).filter (fun j => x j = false)).card % 2 = 0 := by omega
        simp only [hp', ite_true]; omega
      · simp only [hp, ite_false] at hdiff
        have hp' : ((Finset.univ : Finset (Fin (n + 1))).filter (fun j => x j = false)).card % 2 ≠ 0 := by omega
        simp only [hp', ite_false]; omega

private lemma sum_prod_eq_dpCount : ∀ (n : Nat) (x : Fin n → Bool) (b : Bool),
    ∑ s ∈ (Finset.univ : Finset (Fin (n + 1) → Bool)).filter (fun s => s 0 = b ∧ s ⟨n, by omega⟩ = false),
      ∏ j : Fin n, transW (x j) (s ⟨j.val, by omega⟩) (s ⟨j.val + 1, by omega⟩) =
    dpCount n x b
  | 0, x, b => by
    cases b
    · have hset : (Finset.univ : Finset (Fin 1 → Bool)).filter
          (fun s => s 0 = false ∧ s ⟨0, by omega⟩ = false) = {fun _ => false} := by
        ext s
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · rintro ⟨h0, _⟩; funext i; fin_cases i; exact h0
        · rintro rfl; simp
      rw [hset]; simp [dpCount]
    · have hset : (Finset.univ : Finset (Fin 1 → Bool)).filter
          (fun s => s 0 = true ∧ s ⟨0, by omega⟩ = false) = ∅ := by
        ext s
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        rintro ⟨h0, h1⟩; exact Bool.noConfusion (h0.symm.trans h1)
      rw [hset]; simp [dpCount]
  | n + 1, x, b => by
    simp only [dpCount, ← sum_prod_eq_dpCount n (fun j => x j.succ)]

    let S := (Finset.univ : Finset (Fin (n + 2) → Bool)).filter
      (fun s => s 0 = b ∧ s ⟨n + 1, by omega⟩ = false)
    rw [← Finset.sum_filter_add_sum_filter_not S (fun s => s ⟨1, by omega⟩ = false)]
    congr 1
    ·
      rw [Finset.mul_sum]
      refine Finset.sum_bij (fun s _ => fun i : Fin (n + 1) => s i.succ) ?_ ?_ ?_ ?_
      · intro s hs
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
        exact ⟨hs.2, hs.1.2⟩
      · intro s₁ hs₁ s₂ hs₂ hEq
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hs₁ hs₂
        funext i
        refine Fin.cases ?_ ?_ i
        · exact hs₁.1.1.trans hs₂.1.1.symm
        · intro j; exact congrFun hEq j
      · intro t ht
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
        let s : Fin (n + 2) → Bool := Fin.cons b t
        refine ⟨s, ?_, ?_⟩
        · simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨⟨by simp [s], ?_⟩, ?_⟩
          · have h1 : (⟨n + 1, by omega⟩ : Fin (n + 2)) = Fin.succ ⟨n, by omega⟩ := rfl
            rw [h1]; exact ht.2
          · have h2 : (⟨1, by omega⟩ : Fin (n + 2)) = Fin.succ 0 := rfl
            rw [h2]; exact ht.1
        · funext i; simp [s]
      · intro s hs
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hs
        rw [Fin.prod_univ_succ]
        congr 1
        · change transW (x 0) (s 0) (s ⟨1, by omega⟩) = transW (x 0) b false
          rw [hs.1.1, hs.2]
    ·
      rw [Finset.mul_sum]
      refine Finset.sum_bij (fun s _ => fun i : Fin (n + 1) => s i.succ) ?_ ?_ ?_ ?_
      · intro s hs
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
        have hs1 : s ⟨1, by omega⟩ = true := by cases h : s ⟨1, by omega⟩ <;> simp_all
        exact ⟨hs1, hs.1.2⟩
      · intro s₁ hs₁ s₂ hs₂ hEq
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hs₁ hs₂
        funext i
        refine Fin.cases ?_ ?_ i
        · exact hs₁.1.1.trans hs₂.1.1.symm
        · intro j; exact congrFun hEq j
      · intro t ht
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
        let s : Fin (n + 2) → Bool := Fin.cons b t
        refine ⟨s, ?_, ?_⟩
        · simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨⟨by simp [s], ?_⟩, ?_⟩
          · have h1 : (⟨n + 1, by omega⟩ : Fin (n + 2)) = Fin.succ ⟨n, by omega⟩ := rfl
            rw [h1]; exact ht.2
          · have h2 : (⟨1, by omega⟩ : Fin (n + 2)) = Fin.succ 0 := rfl
            rw [h2]; simp [s, ht.1]
        · funext i; simp [s]
      · intro s hs
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hs
        have hs1 : s ⟨1, by omega⟩ = true := by cases h : s ⟨1, by omega⟩ <;> simp_all
        rw [Fin.prod_univ_succ]
        congr 1
        · change transW (x 0) (s 0) (s ⟨1, by omega⟩) = transW (x 0) b true
          rw [hs.1.1, hs1]

private lemma sat_mkF_iff (n : Nat) (z : Finset (Fin (9 * n + 1))) :
    (∀ C ∈ mkF n, ∃ l ∈ C, decide (l.1 ∈ z) = l.2) ↔
      (decide (sIdx n n (le_refl n) ∈ z) = false) ∧
      ∀ j : Fin n,
        linkOk (decide (sIdx n j.val (by omega) ∈ z))
               (decide (vIdx n j 1 (by omega) ∈ z))
               (decide (sIdx n (j.val + 1) (by omega) ∈ z))
               (fun c : Fin 7 => decide (vIdx n j (c.val + 2) (by omega) ∈ z)) = true := by
  simp only [mkF, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rcases h _ (Or.inl rfl) with ⟨l, hl, hle⟩
      rw [Finset.mem_singleton.mp hl] at hle
      exact hle
    · intro j
      have hcl : ∀ C ∈ linkClauses n j, ∃ l ∈ C, decide (l.1 ∈ z) = l.2 :=
        fun C hC => h C (Or.inr ⟨j, hC⟩)
      simp only [linkOk]
      have hpair : ∀ (a b : Fin (9 * n + 1)) (pa pb : Bool),
          {(a, pa), (b, pb)} ∈ linkClauses n j →
          ((decide (a ∈ z) == pa) || (decide (b ∈ z) == pb)) = true := by
        intro a b pa pb hmem
        rcases hcl _ hmem with ⟨l, hl, hle⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hl
        rcases hl with rfl | rfl <;> simp [hle]
      have c1 := hpair (vIdx n j 2 (by omega)) (sIdx n j.val (by omega)) false true (by simp [linkClauses])
      have c2 := hpair (vIdx n j 2 (by omega)) (vIdx n j 1 (by omega)) false true (by simp [linkClauses])
      have c3 := hpair (vIdx n j 2 (by omega)) (sIdx n (j.val + 1) (by omega)) false true (by simp [linkClauses])
      have c4 := hpair (vIdx n j 3 (by omega)) (vIdx n j 2 (by omega)) false true (by simp [linkClauses])
      have c5 := hpair (vIdx n j 4 (by omega)) (vIdx n j 2 (by omega)) false true (by simp [linkClauses])
      have c6 := hpair (vIdx n j 3 (by omega)) (vIdx n j 4 (by omega)) false false (by simp [linkClauses])
      have c7 := hpair (vIdx n j 5 (by omega)) (sIdx n j.val (by omega)) false true (by simp [linkClauses])
      have c8 := hpair (vIdx n j 5 (by omega)) (vIdx n j 1 (by omega)) false false (by simp [linkClauses])
      have c9 := hpair (vIdx n j 6 (by omega)) (sIdx n j.val (by omega)) false true (by simp [linkClauses])
      have c10 := hpair (vIdx n j 6 (by omega)) (sIdx n (j.val + 1) (by omega)) false false (by simp [linkClauses])
      have c11 := hpair (vIdx n j 7 (by omega)) (sIdx n j.val (by omega)) false false (by simp [linkClauses])
      have c12 := hpair (vIdx n j 8 (by omega)) (sIdx n j.val (by omega)) false false (by simp [linkClauses])
      have c13 := hpair (vIdx n j 7 (by omega)) (vIdx n j 8 (by omega)) false false (by simp [linkClauses])
      simp at c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13
      simp [c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13]
  · rintro ⟨hsn, hall⟩ C (rfl | ⟨j, hCj⟩)
    · exact ⟨(sIdx n n (le_refl n), false), Finset.mem_singleton_self _, hsn⟩
    · have hj := hall j
      simp only [linkOk, Bool.and_eq_true] at hj
      rcases hj with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩, c8⟩, c9⟩, c10⟩, c11⟩, c12⟩, c13⟩
      simp only [linkClauses, Finset.mem_insert, Finset.mem_singleton] at hCj
      rcases hCj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rcases Bool.or_eq_true_iff.mp c1 with h | h
        · exact ⟨_, Finset.mem_insert_self _ _, by simpa using h⟩
        · exact ⟨_, Finset.mem_insert_of_mem (Finset.mem_singleton_self _), h⟩
      · rcases Bool.or_eq_true_iff.mp c2 with h | h
        · exact ⟨_, Finset.mem_insert_self _ _, by simpa using h⟩
        · exact ⟨_, Finset.mem_insert_of_mem (Finset.mem_singleton_self _), h⟩
      · rcases Bool.or_eq_true_iff.mp c3 with h | h
        · exact ⟨_, Finset.mem_insert_self _ _, by simpa using h⟩
        · exact ⟨_, Finset.mem_insert_of_mem (Finset.mem_singleton_self _), h⟩
      · rcases Bool.or_eq_true_iff.mp c4 with h | h
        · exact ⟨_, Finset.mem_insert_self _ _, by simpa using h⟩
        · exact ⟨_, Finset.mem_insert_of_mem (Finset.mem_singleton_self _), h⟩
      · rcases Bool.or_eq_true_iff.mp c5 with h | h
        · exact ⟨_, Finset.mem_insert_self _ _, by simpa using h⟩
        · exact ⟨_, Finset.mem_insert_of_mem (Finset.mem_singleton_self _), h⟩
      · rcases Bool.or_eq_true_iff.mp c6 with h | h
        · exact ⟨_, Finset.mem_insert_self _ _, by simpa using h⟩
        · exact ⟨_, Finset.mem_insert_of_mem (Finset.mem_singleton_self _), by simpa using h⟩
      · rcases Bool.or_eq_true_iff.mp c7 with h | h
        · exact ⟨_, Finset.mem_insert_self _ _, by simpa using h⟩
        · exact ⟨_, Finset.mem_insert_of_mem (Finset.mem_singleton_self _), h⟩
      · rcases Bool.or_eq_true_iff.mp c8 with h | h
        · exact ⟨_, Finset.mem_insert_self _ _, by simpa using h⟩
        · exact ⟨_, Finset.mem_insert_of_mem (Finset.mem_singleton_self _), by simpa using h⟩
      · rcases Bool.or_eq_true_iff.mp c9 with h | h
        · exact ⟨_, Finset.mem_insert_self _ _, by simpa using h⟩
        · exact ⟨_, Finset.mem_insert_of_mem (Finset.mem_singleton_self _), h⟩
      · rcases Bool.or_eq_true_iff.mp c10 with h | h
        · exact ⟨_, Finset.mem_insert_self _ _, by simpa using h⟩
        · exact ⟨_, Finset.mem_insert_of_mem (Finset.mem_singleton_self _), by simpa using h⟩
      · rcases Bool.or_eq_true_iff.mp c11 with h | h
        · exact ⟨_, Finset.mem_insert_self _ _, by simpa using h⟩
        · exact ⟨_, Finset.mem_insert_of_mem (Finset.mem_singleton_self _), by simpa using h⟩
      · rcases Bool.or_eq_true_iff.mp c12 with h | h
        · exact ⟨_, Finset.mem_insert_self _ _, by simpa using h⟩
        · exact ⟨_, Finset.mem_insert_of_mem (Finset.mem_singleton_self _), by simpa using h⟩
      · rcases Bool.or_eq_true_iff.mp c13 with h | h
        · exact ⟨_, Finset.mem_insert_self _ _, by simpa using h⟩
        · exact ⟨_, Finset.mem_insert_of_mem (Finset.mem_singleton_self _), by simpa using h⟩

private lemma count_univ_eq_dpCount (n : Nat) (b : Bool) (B : Finset (Fin n)) :
    let xs := (Finset.univ : Finset (Finset (Fin (9 * n + 1)))).filter (fun z =>
      ∀ C ∈ mkF n, ∃ l ∈ C, decide (l.1 ∈ z) = l.2)
    (xs.filter (fun z => decide (sIdx n 0 (Nat.zero_le n) ∈ z) = b ∧
      (Finset.univ : Finset (Fin n)).filter (fun j => vIdx n j 1 (by omega) ∈ z) = B)).card =
    dpCount n (fun j => decide (j ∈ B)) b := by
  intro xs
  rw [← sum_prod_eq_dpCount]
  let S := (Finset.univ : Finset (Fin (n + 1) → Bool)).filter
    (fun s => s 0 = b ∧ s ⟨n, by omega⟩ = false)
  let Z := xs.filter (fun z => decide (sIdx n 0 (Nat.zero_le n) ∈ z) = b ∧
    (Finset.univ : Finset (Fin n)).filter (fun j => vIdx n j 1 (by omega) ∈ z) = B)
  let proj : Finset (Fin (9 * n + 1)) → (Fin (n + 1) → Bool) := fun z i =>
    decide (sIdx n i.val (by omega) ∈ z)
  have hmap : ∀ z ∈ Z, proj z ∈ S := by
    intro z hz
    simp only [Z, xs, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    have hsat := (sat_mkF_iff n z).mp hz.1
    simp only [S, proj, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hz.2.1, hsat.1⟩
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  apply Finset.sum_congr rfl
  intro s hs
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hs
  let Wset : Fin n → Finset (Fin 7 → Bool) := fun j =>
    (Finset.univ : Finset (Fin 7 → Bool)).filter
      (fun w => linkOk (s ⟨j.val, by omega⟩) (decide (j ∈ B)) (s ⟨j.val + 1, by omega⟩) w = true)
  have hprod : ∏ j : Fin n, transW (decide (j ∈ B)) (s ⟨j.val, by omega⟩) (s ⟨j.val + 1, by omega⟩) =
      (Fintype.piFinset Wset).card := by
    rw [Fintype.card_piFinset]
    apply Finset.prod_congr rfl
    intro j _
    exact (card_linkOk _ _ _).symm
  rw [hprod]

  let toW : Finset (Fin (9 * n + 1)) → (Fin n → Fin 7 → Bool) := fun z j c =>
    decide (vIdx n j (c.val + 2) (by omega) ∈ z)
  let fromW : (Fin n → Fin 7 → Bool) → Finset (Fin (9 * n + 1)) := fun W =>
    (Finset.univ : Finset (Fin (9 * n + 1))).filter (fun v =>
      if h0 : v.val % 9 = 0 then s ⟨v.val / 9, by omega⟩ = true
      else if h1 : v.val % 9 = 1 then decide (⟨v.val / 9, by omega⟩ ∈ B) = true
      else W ⟨v.val / 9, by omega⟩ ⟨v.val % 9 - 2, by omega⟩ = true)
  refine Finset.card_bij (fun z _ => toW z) ?_ ?_ ?_
  · intro z hz
    simp only [Z, xs, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    have hsat := (sat_mkF_iff n z).mp hz.1.1
    rw [Fintype.mem_piFinset]
    intro j
    simp only [Wset, Finset.mem_filter, Finset.mem_univ, true_and]
    have hsj : decide (sIdx n j.val (by omega) ∈ z) = s ⟨j.val, by omega⟩ :=
      congrFun hz.2 ⟨j.val, by omega⟩
    have hsj1 : decide (sIdx n (j.val + 1) (by omega) ∈ z) = s ⟨j.val + 1, by omega⟩ :=
      congrFun hz.2 ⟨j.val + 1, by omega⟩
    have hxj : decide (vIdx n j 1 (by omega) ∈ z) = decide (j ∈ B) := by
      have := Finset.ext_iff.mp hz.1.2.2 j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
      by_cases h : vIdx n j 1 (by omega) ∈ z <;> simp [h, this.mp, mt this.mpr]
    rw [← hsj, ← hsj1, ← hxj]
    exact hsat.2 j
  · intro z₁ hz₁ z₂ hz₂ hEq
    simp only [Z, xs, Finset.mem_filter, Finset.mem_univ, true_and] at hz₁ hz₂
    ext v
    by_cases h0 : v.val % 9 = 0
    · have hv : v = sIdx n (v.val / 9) (by omega) := Fin.ext (by simp [sIdx]; omega)
      rw [hv]
      have h1 := congrFun hz₁.2 ⟨v.val / 9, by omega⟩
      have h2 := congrFun hz₂.2 ⟨v.val / 9, by omega⟩
      have := h1.trans h2.symm
      simpa [proj] using this
    · by_cases h1 : v.val % 9 = 1
      · let j : Fin n := ⟨v.val / 9, by omega⟩
        have hv : v = vIdx n j 1 (by omega) := Fin.ext (by simp [vIdx, j]; omega)
        rw [hv]
        have e1 := Finset.ext_iff.mp hz₁.1.2.2 j
        have e2 := Finset.ext_iff.mp hz₂.1.2.2 j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at e1 e2
        exact e1.trans e2.symm
      · let j : Fin n := ⟨v.val / 9, by omega⟩
        let c : Fin 7 := ⟨v.val % 9 - 2, by omega⟩
        have hv : v = vIdx n j (c.val + 2) (by omega) := Fin.ext (by simp [vIdx, j, c]; omega)
        rw [hv]
        have hW := congrFun (congrFun hEq j) c
        simpa [toW] using hW
  · intro W hW
    rw [Fintype.mem_piFinset] at hW
    refine ⟨fromW W, ?_, ?_⟩
    · have hs_from : ∀ (i : Fin (n + 1)),
          decide (sIdx n i.val (by omega) ∈ fromW W) = s i := by
        intro i
        have hm0 : (9 * i.val) % 9 = 0 := by omega
        have hd : (9 * i.val) / 9 = i.val := by omega
        simp [fromW, sIdx, hm0, hd]
      have hx_from : ∀ (j : Fin n),
          decide (vIdx n j 1 (by omega) ∈ fromW W) = decide (j ∈ B) := by
        intro j
        have hm0 : (9 * j.val + 1) % 9 ≠ 0 := by omega
        have hm1 : (9 * j.val + 1) % 9 = 1 := by omega
        have hd : (9 * j.val + 1) / 9 = j.val := by omega
        have hfin : (⟨(9 * j.val + 1) / 9, by omega⟩ : Fin n) = j := Fin.ext hd
        simp [fromW, vIdx, hm0, hm1, hfin]
      have hw_from : ∀ (j : Fin n) (c : Fin 7),
          decide (vIdx n j (c.val + 2) (by omega) ∈ fromW W) = W j c := by
        intro j c
        have hm0 : (c.val + 2) % 9 ≠ 0 := by omega
        have hm1 : (c.val + 2) % 9 ≠ 1 := by omega
        have hj : (⟨(9 * j.val + (c.val + 2)) / 9, by omega⟩ : Fin n) = j := Fin.ext (by dsimp only; omega)
        have hc : (⟨(c.val + 2) % 9 - 2, by omega⟩ : Fin 7) = c := Fin.ext (by dsimp only; omega)
        simp [fromW, vIdx, hm0, hm1, hj, hc]
      simp only [Z, xs, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨⟨(sat_mkF_iff n (fromW W)).mpr ⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
      · rw [hs_from ⟨n, by omega⟩]; exact hs.2
      · intro j
        have hWj := (Finset.mem_filter.mp (hW j)).2
        rw [hs_from ⟨j.val, by omega⟩, hx_from j, hs_from ⟨j.val + 1, by omega⟩]
        convert hWj using 1
        congr 1; funext c; exact hw_from j c
      · exact (hs_from 0).trans hs.1
      · ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have := hx_from j
        by_cases h : j ∈ B <;> simp_all
      · funext i; exact hs_from i
    · funext j c
      have hm0 : (c.val + 2) % 9 ≠ 0 := by omega
      have hm1 : (c.val + 2) % 9 ≠ 1 := by omega
      have hj : (⟨(9 * j.val + (c.val + 2)) / 9, by omega⟩ : Fin n) = j := Fin.ext (by dsimp only; omega)
      have hc : (⟨(c.val + 2) % 9 - 2, by omega⟩ : Fin 7) = c := Fin.ext (by dsimp only; omega)
      simp [toW, fromW, vIdx, hm0, hm1, hj, hc]

theorem main_proof : (∀ n : Nat, 0 < n →
  let V := Fin (9 * n + 1)
  let I := Fin n
  let Clause := Finset (V × Bool)
  ∃ (F : Finset Clause) (r : V) (mark : I → V)
    (bag : Fin (6 * n) → Finset V) (par : Fin (6 * n) → Fin (6 * n)),
    Function.Injective mark ∧ (∀ j, mark j ≠ r) ∧ F.card ≤ 13 * n + 1 ∧
    (∀ C ∈ F, C.card ≤ 2 ∧ (C.filter (fun l => l.2 = true)).card ≤ 1 ∧
      ∃ k, ∀ l ∈ C, l.1 ∈ bag k) ∧
    (∀ k, (bag k).card ≤ 3 ∧ par k ≤ k ∧ (0 < k.val → par k < k)) ∧
    (∀ v : V, ∃ top, v ∈ bag top ∧ ∀ k, v ∈ bag k → top ≤ k ∧
      (k ≠ top → v ∈ bag (par k))) ∧
    let xs := (Finset.univ : Finset (Finset V)).filter (fun z =>
      ∀ C ∈ F, ∃ l ∈ C, decide (l.1 ∈ z) = l.2)
    let count := fun (b : Bool) (S B : Finset I) =>
      (xs.filter (fun z => decide (r ∈ z) = b ∧ S.filter (fun j => mark j ∈ z) = B)).card
    ∀ S : Finset I, ∀ B ⊆ S,
      (S ≠ Finset.univ → count false S B = count true S B) ∧
      (S = Finset.univ → 0 < count false S B ∧ 0 < count true S B ∧
        (if (n - B.card) % 2 = 0 then count false S B = count true S B + 1
         else count true S B = count false S B + 1))) := by
  intro n hn
  let r : Fin (9 * n + 1) := sIdx n 0 (Nat.zero_le n)
  let mark : Fin n → Fin (9 * n + 1) := fun j => vIdx n j 1 (by omega)
  refine ⟨mkF n, r, mark, mkBag n, mkPar n, ?_, ?_, mkF_card_le n, mkF_clauses_ok hn,
    mkBag_par_ok n, running_intersection hn, ?_⟩
  · intro j₁ j₂ hEq
    have := congrArg Fin.val hEq
    simp only [mark, vIdx] at this
    exact Fin.ext (by omega)
  · intro j hEq
    have := congrArg Fin.val hEq
    simp only [mark, r, vIdx, sIdx] at this
    omega
  · intro xs count S B hBS
    have huniv : ∀ B' : Finset (Fin n),
        0 < count false Finset.univ B' ∧ 0 < count true Finset.univ B' ∧
        (if (n - B'.card) % 2 = 0 then count false Finset.univ B' = count true Finset.univ B' + 1
         else count true Finset.univ B' = count false Finset.univ B' + 1) := by
      intro B'
      have hcf : count false Finset.univ B' = dpCount n (fun j => decide (j ∈ B')) false :=
        count_univ_eq_dpCount n false B'
      have hct : count true Finset.univ B' = dpCount n (fun j => decide (j ∈ B')) true :=
        count_univ_eq_dpCount n true B'
      have hdp := dpCount_props n (fun j => decide (j ∈ B'))
      have hcompl : ((Finset.univ : Finset (Fin n)).filter (fun j => decide (j ∈ B') = false)).card =
          n - B'.card := by
        have hfilt : (Finset.univ : Finset (Fin n)).filter (fun j => decide (j ∈ B') = false) =
            Finset.univ \ B' := by
          ext j; simp
        rw [hfilt, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
      rw [hcompl] at hdp
      rw [hcf, hct]
      exact ⟨hdp.1, hdp.2.1 hn, hdp.2.2⟩
    constructor
    · intro hne
      have hex : ∃ j₀ : Fin n, j₀ ∉ S := by
        by_contra hall
        apply hne
        ext j; simp only [Finset.mem_univ, iff_true]
        by_contra hj; exact hall ⟨j, hj⟩
      rcases hex with ⟨j₀, hj₀⟩
      let extSet := (Finset.univ : Finset (Finset (Fin n))).filter (fun B' => B' ∩ S = B)
      have hpart : ∀ b : Bool, count b S B = ∑ B' ∈ extSet, count b Finset.univ B' := by
        intro b
        let Tset := xs.filter (fun z => decide (r ∈ z) = b ∧ S.filter (fun j => mark j ∈ z) = B)
        have hmap : ∀ z ∈ Tset, (Finset.univ : Finset (Fin n)).filter (fun j => mark j ∈ z) ∈ extSet := by
          intro z hz
          simp only [Tset, Finset.mem_filter] at hz
          simp only [extSet, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [← hz.2.2]
          ext j; simp [and_comm]
        change Tset.card = _
        rw [Finset.card_eq_sum_card_fiberwise hmap]
        apply Finset.sum_congr rfl
        intro B' hB'
        simp only [extSet, Finset.mem_filter, Finset.mem_univ, true_and] at hB'
        congr 1; ext z
        simp only [Tset, count, Finset.mem_filter]
        constructor
        · rintro ⟨⟨hzx, hzb, _⟩, hzu⟩
          exact ⟨hzx, hzb, hzu⟩
        · rintro ⟨hzx, hzb, hzu⟩
          refine ⟨⟨hzx, hzb, ?_⟩, hzu⟩
          rw [← hB', ← hzu]
          ext j; simp [and_comm]
      rw [hpart false, hpart true]
      let E0 := extSet.filter (fun B' => j₀ ∉ B')
      let E1 := extSet.filter (fun B' => j₀ ∈ B')
      have hsplit : ∀ f : Finset (Fin n) → Nat,
          ∑ B' ∈ extSet, f B' = ∑ B' ∈ E0, (f B' + f (insert j₀ B')) := by
        intro f
        rw [← Finset.sum_filter_add_sum_filter_not extSet (fun B' => j₀ ∉ B')]
        rw [Finset.sum_add_distrib]
        congr 1
        refine Finset.sum_bij (fun B' _ => B'.erase j₀) ?_ ?_ ?_ ?_
        · intro B' hB'
          simp only [E0, Finset.mem_filter, not_not, extSet, Finset.mem_univ, true_and] at hB' ⊢
          refine ⟨?_, Finset.notMem_erase _ _⟩
          rw [← hB'.1]
          ext j; simp only [Finset.mem_inter, Finset.mem_erase]
          constructor
          · rintro ⟨⟨_, hjB⟩, hjS⟩; exact ⟨hjB, hjS⟩
          · rintro ⟨hjB, hjS⟩; exact ⟨⟨fun he => hj₀ (he ▸ hjS), hjB⟩, hjS⟩
        · intro B₁ h₁ B₂ h₂ hEq
          simp only [Finset.mem_filter, not_not] at h₁ h₂
          rw [← Finset.insert_erase h₁.2, ← Finset.insert_erase h₂.2, hEq]
        · intro B' hB'
          simp only [E0, Finset.mem_filter, extSet, Finset.mem_univ, true_and] at hB'
          refine ⟨insert j₀ B', ?_, Finset.erase_insert hB'.2⟩
          simp only [Finset.mem_filter, not_not, extSet, Finset.mem_univ, true_and]
          refine ⟨?_, Finset.mem_insert_self _ _⟩
          rw [← hB'.1]
          ext j; simp only [Finset.mem_inter, Finset.mem_insert]
          constructor
          · rintro ⟨rfl | hjB, hjS⟩
            · exact absurd hjS hj₀
            · exact ⟨hjB, hjS⟩
          · rintro ⟨hjB, hjS⟩; exact ⟨Or.inr hjB, hjS⟩
        · intro B' hB'
          simp only [Finset.mem_filter, not_not] at hB'
          rw [Finset.insert_erase hB'.2]
      rw [hsplit (fun B' => count false Finset.univ B'),
          hsplit (fun B' => count true Finset.univ B')]
      apply Finset.sum_congr rfl
      intro B' hB'
      have hj₀' : j₀ ∉ B' := (Finset.mem_filter.mp hB').2
      have hcard_ins : (insert j₀ B').card = B'.card + 1 := Finset.card_insert_of_notMem hj₀'
      have hlt : B'.card < n := by
        have hsub : insert j₀ B' ⊆ Finset.univ := Finset.subset_univ _
        have := Finset.card_le_card hsub
        rw [hcard_ins, Finset.card_univ, Fintype.card_fin] at this
        omega
      have u1 := (huniv B').2.2
      have u2 := (huniv (insert j₀ B')).2.2
      rw [hcard_ins] at u2
      by_cases hp : (n - B'.card) % 2 = 0
      · have hp2 : (n - (B'.card + 1)) % 2 ≠ 0 := by omega
        simp only [hp, ite_true] at u1
        simp only [hp2, ite_false] at u2
        omega
      · have hp2 : (n - (B'.card + 1)) % 2 = 0 := by omega
        simp only [hp, ite_false] at u1
        simp only [hp2, ite_true] at u2
        omega
    · rintro rfl
      exact huniv B

end PEqualNP.Outside.L_lib_1142

theorem PEqualNP.Outside.L_lib_1142 : (∀ n : Nat, 0 < n →
  let V := Fin (9 * n + 1)
  let I := Fin n
  let Clause := Finset (V × Bool)
  ∃ (F : Finset Clause) (r : V) (mark : I → V)
    (bag : Fin (6 * n) → Finset V) (par : Fin (6 * n) → Fin (6 * n)),
    Function.Injective mark ∧ (∀ j, mark j ≠ r) ∧ F.card ≤ 13 * n + 1 ∧
    (∀ C ∈ F, C.card ≤ 2 ∧ (C.filter (fun l => l.2 = true)).card ≤ 1 ∧
      ∃ k, ∀ l ∈ C, l.1 ∈ bag k) ∧
    (∀ k, (bag k).card ≤ 3 ∧ par k ≤ k ∧ (0 < k.val → par k < k)) ∧
    (∀ v : V, ∃ top, v ∈ bag top ∧ ∀ k, v ∈ bag k → top ≤ k ∧
      (k ≠ top → v ∈ bag (par k))) ∧
    let xs := (Finset.univ : Finset (Finset V)).filter (fun z =>
      ∀ C ∈ F, ∃ l ∈ C, decide (l.1 ∈ z) = l.2)
    let count := fun (b : Bool) (S B : Finset I) =>
      (xs.filter (fun z => decide (r ∈ z) = b ∧ S.filter (fun j => mark j ∈ z) = B)).card
    ∀ S : Finset I, ∀ B ⊆ S,
      (S ≠ Finset.univ → count false S B = count true S B) ∧
      (S = Finset.univ → 0 < count false S B ∧ 0 < count true S B ∧
        (if (n - B.card) % 2 = 0 then count false S B = count true S B + 1
         else count true S B = count false S B + 1))) := by
  exact PEqualNP.Outside.L_lib_1142.main_proof

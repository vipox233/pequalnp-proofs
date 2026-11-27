import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin

namespace PEqualNP.Outside.L_lib_729

open Finset

lemma matching {α : Type*} [Fintype α] [DecidableEq α] {degree : ℕ}
    (pos : 0 < degree) (weight : α → α → ℕ)
    (rows : ∀ src, ∑ dst, weight src dst = degree)
    (cols : ∀ dst, ∑ src, weight src dst = degree) :
    ∃ perm : Equiv.Perm α, ∀ src, 0 < weight src (perm src) := by
  classical
  let adj (src : α) := univ.filter (fun dst => 0 < weight src dst)
  have hall (part : Finset α) : part.card ≤ (part.biUnion adj).card := by
    apply Nat.le_of_mul_le_mul_right _ pos
    calc
      part.card * degree = ∑ src ∈ part, ∑ dst ∈ adj src, weight src dst := by
        simp [adj, sum_filter, rows, show ∀ a : ℕ, (if 0 < a then a else 0) = a by grind]
      _ ≤ ∑ src ∈ part, ∑ dst ∈ part.biUnion adj, weight src dst := by
        exact sum_le_sum fun src hsrc => sum_le_sum_of_subset (subset_biUnion_of_mem adj hsrc)
      _ ≤ ∑ src, ∑ dst ∈ part.biUnion adj, weight src dst := sum_le_sum_of_subset (subset_univ _)
      _ = (part.biUnion adj).card * degree := by rw [sum_comm]; simp [cols]
  obtain ⟨f, hinj, hmem⟩ := (all_card_le_biUnion_card_iff_exists_injective adj).1 hall
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), fun src =>
    (mem_filter.mp (hmem src)).2⟩

abbrev Node (n d : ℕ) := (Fin n × Fin d) ⊕ (Fin n × Fin n)

def network {n d : ℕ} (cap : ℕ) (w : Fin n → Fin n → ℕ) : Node n d → Node n d → ℕ
  | .inl _, .inl _ => 0
  | .inl (row, _), .inr (src, dst) => if src = row then w src dst else 0
  | .inr (src, dst), .inl (col, _) => if col = dst then w src dst else 0
  | .inr edge, .inr other => if other = edge then (cap - w edge.1 edge.2) * d else 0

lemma networkMatching {n cap d : ℕ} (hc : 0 < cap) (hd : 0 < d)
    (w : Fin n → Fin n → ℕ) (bound : ∀ i j, w i j ≤ cap)
    (rows : ∀ i, ∑ j, w i j = cap*d) (cols : ∀ j, ∑ i, w i j = cap*d) :
    ∃ perm : Equiv.Perm (Node n d), ∀ src, 0 < network cap w src (perm src) := by
  apply matching (Nat.mul_pos hc hd)
  · rintro (⟨row, step⟩ | ⟨src, dst⟩)
    · simp [Fintype.sum_sum_type, Fintype.sum_prod_type, network, rows]
    · simp only [Fintype.sum_sum_type, network, sum_ite_eq', mem_univ, ite_true]
      rw [Fintype.sum_prod_type_right]
      simp [mul_comm d, Nat.sub_mul, Nat.add_sub_of_le (Nat.mul_le_mul_right d (bound src dst))]
  · rintro (⟨col, step⟩ | ⟨src, dst⟩)
    · simp [Fintype.sum_sum_type, Fintype.sum_prod_type, network, cols]
    · simp only [Fintype.sum_sum_type, network]
      rw [Fintype.sum_prod_type_right]
      simp [mul_comm d, Nat.sub_mul, Nat.add_sub_of_le (Nat.mul_le_mul_right d (bound src dst))]

lemma layer {n cap d : ℕ} (hc : 0 < cap) (hd : 0 < d)
    (w : Fin n → Fin n → ℕ) (bound : ∀ i j, w i j ≤ cap)
    (rows : ∀ i, ∑ j, w i j = cap*d) (cols : ∀ j, ∑ i, w i j = cap*d) :
    ∃ a : Fin n → Fin n → ℕ, (∀ i j, a i j ≤ 1) ∧ (∀ i j, a i j ≤ w i j) ∧
      (∀ i j, w i j = cap → a i j = 1) ∧ (∀ i, ∑ j, a i j = d) ∧ (∀ j, ∑ i, a i j = d) := by
  classical
  obtain ⟨perm, support⟩ := networkMatching hc hd w bound rows cols
  let hit (src dst : Node n d) : ℕ := if perm src = dst then 1 else 0
  have zero (src dst : Node n d) (hz : network cap w src dst = 0) : hit src dst = 0 := by
    have := support src
    simp only [hit]; split <;> grind
  let left (i : Fin n) (t : Fin d) (j : Fin n) := hit (.inl (i,t)) (.inr (i,j))
  let right (i j : Fin n) (t : Fin d) := hit (.inr (i,j)) (.inl (j,t))
  let stay (i j : Fin n) := hit (.inr (i,j)) (.inr (i,j))
  have ll (x y : Fin n × Fin d) : hit (.inl x) (.inl y) = 0 := zero _ _ rfl
  have lr (i t k j) : hit (.inl (i,t)) (.inr (k,j)) = if k = i then left i t j else 0 := by
    split_ifs with h
    · subst k; rfl
    · exact zero _ _ (by simp [network,h])
  have rl (i j k t) : hit (.inr (i,j)) (.inl (k,t)) = if k = j then right i j t else 0 := by
    split_ifs with h
    · subst k; rfl
    · exact zero _ _ (by simp [network,h])
  have rr (x y : Fin n × Fin n) : hit (.inr x) (.inr y) = if y = x then stay x.1 x.2 else 0 := by
    split_ifs with h
    · subst y; rfl
    · exact zero _ _ (by simp [network,h])
  have hrow (src) : ∑ dst, hit src dst = 1 := by simp [hit]
  have hcol (dst) : ∑ src, hit src dst = 1 := by simp [hit, ← perm.eq_symm_apply]
  have rowSlot (i t) : ∑ j, left i t j = 1 := by
    simpa [Fintype.sum_sum_type, Fintype.sum_prod_type, ll, lr, ← ite_sum_zero] using hrow (.inl (i,t))
  have colSlot (j t) : ∑ i, right i j t = 1 := by
    simpa [Fintype.sum_sum_type, Fintype.sum_prod_type, ll, rl] using hcol (.inl (j,t))
  have rowCell (i j) : (∑ t, right i j t) + stay i j = 1 := by
    have := hrow (.inr (i,j))
    simp only [Fintype.sum_sum_type, rr, sum_ite_eq', mem_univ, ite_true] at this
    simpa [Fintype.sum_prod_type, rl, ← ite_sum_zero] using this
  have colCell (i j) : (∑ t, left i t j) + stay i j = 1 := by
    have := hcol (.inr (i,j))
    simp only [Fintype.sum_sum_type, rr, sum_ite_eq, mem_univ, ite_true] at this
    simpa [Fintype.sum_prod_type, lr, ← ite_sum_zero] using this
  refine ⟨fun i j => ∑ t, left i t j, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j; exact (Nat.le_add_right _ _).trans (colCell i j).le
  · intro i j; have := colCell i j
    by_cases hz : w i j = 0
    · have hz' (t) : left i t j = 0 := zero _ _ (by simp [network,hz])
      simp [hz']
    · exact (Nat.le_add_right _ _).trans ((colCell i j).le.trans (Nat.pos_of_ne_zero hz))
  · intro i j hsat
    have hz : stay i j = 0 := zero _ _ (by simp [network,hsat])
    simpa [hz] using colCell i j
  · intro i; rw [sum_comm]; simp [rowSlot]
  · intro j
    have heq (i) : (∑ t, left i t j) = ∑ t, right i j t := by
      have := rowCell i j; have := colCell i j; omega
    simp_rw [heq]; rw [sum_comm]; simp [colSlot]

lemma permutations {n : ℕ} (d : ℕ) (a : Fin n → Fin n → ℕ)
    (rows : ∀ i, ∑ j, a i j = d) (cols : ∀ j, ∑ i, a i j = d) :
    ∃ family : Fin d → Equiv.Perm (Fin n), ∀ i j,
      (∑ t, if family t i = j then 1 else 0) = a i j := by
  classical
  induction d generalizing a with
  | zero =>
    refine ⟨Fin.elim0, fun i j => ?_⟩
    have h := single_le_sum (f := a i) (fun _ _ => Nat.zero_le _) (mem_univ j)
    simpa [rows] using (show 0 = a i j by have := rows i; omega)
  | succ d ih =>
    obtain ⟨perm, hp⟩ := matching (Nat.succ_pos d) a rows cols
    let mark (i j : Fin n) : ℕ := if perm i = j then 1 else 0
    have le (i j) : mark i j ≤ a i j := by
      by_cases he : perm i = j
      · subst j; simpa only [mark,ite_true,eq_self] using Nat.succ_le_of_lt (hp i)
      · simp [mark,he]
    let rest i j := a i j - mark i j
    obtain ⟨family, count⟩ := ih rest (fun i => by
      simp [rest,sum_tsub_distrib _ (fun j _ => le i j), rows, mark]) (fun j => by
      dsimp only [rest]; rw [sum_tsub_distrib _ (fun i _ => le i j), cols]; simp [mark, ← perm.eq_symm_apply])
    refine ⟨Fin.cons perm family, fun i j => ?_⟩
    rw [Fin.sum_univ_succ]; simp only [Fin.cons_zero, Fin.cons_succ, count]
    exact Nat.add_sub_of_le (le i j)

lemma layers {n : ℕ} (cap d : ℕ) (w : Fin n → Fin n → ℕ) (bound : ∀ i j, w i j ≤ cap)
    (rows : ∀ i, ∑ j, w i j = cap*d) (cols : ∀ j, ∑ i, w i j = cap*d) :
    ∃ perm : Fin cap → Fin d → Equiv.Perm (Fin n),
      (∀ layer i, Function.Injective (fun step => perm layer step i)) ∧
      ∀ i j, (∑ layer, ∑ step, if perm layer step i = j then 1 else 0) = w i j := by
  classical
  by_cases hd : d = 0
  · subst d
    refine ⟨fun _ => Fin.elim0, fun _ _ => Function.injective_of_subsingleton _, fun i j => ?_⟩
    have h := single_le_sum (f := w i) (fun _ _ => Nat.zero_le _) (mem_univ j)
    simp [rows] at h; simp [h]
  induction cap generalizing w with
  | zero =>
    exact ⟨Fin.elim0, fun layer => layer.elim0, fun i j => by simp [Nat.eq_zero_of_le_zero (bound i j)]⟩
  | succ cap ih =>
    obtain ⟨a, simple, used, full, ar, ac⟩ := layer (Nat.succ_pos cap) (Nat.pos_of_ne_zero hd) w bound rows cols
    let rest i j := w i j - a i j
    have rb (i j) : rest i j ≤ cap := by
      have := bound i j; have := full i j; dsimp [rest]; omega
    obtain ⟨tail, ti, tc⟩ := ih rest rb (fun i => by
      simp [rest, sum_tsub_distrib _ (fun j _ => used i j), rows, ar, Nat.succ_mul]) (fun j => by
      simp [rest, sum_tsub_distrib _ (fun i _ => used i j), cols, ac, Nat.succ_mul])
    obtain ⟨head, count⟩ := permutations d a ar ac
    refine ⟨Fin.cons head tail, ?_, fun i j => ?_⟩
    · intro idx i
      refine Fin.cases ?_ (fun k => ?_) idx
      · simp only [Fin.cons_zero]
        intro first second he
        have h := count i (head second i)
        rw [sum_boole] at h
        apply card_le_one.mp (h.trans_le (simple _ _)) first (by simpa using he) second (by simp)
      · simpa using ti k i
    · rw [Fin.sum_univ_succ]; simp only [Fin.cons_zero,Fin.cons_succ,count,tc]
      exact Nat.add_sub_of_le (used i j)

end PEqualNP.Outside.L_lib_729

theorem PEqualNP.Outside.L_lib_729 : (∀ (n B D : ℕ),
  ∀ w : Fin n → Fin n → ℕ,
    (∀ i j, w i j ≤ B) →
    (∀ i, (∑ j, w i j) = B*D) →
    (∀ j, (∑ i, w i j) = B*D) →
    ∃ perm : Fin B → Fin D → Equiv.Perm (Fin n),
      (∀ layer i, Function.Injective (fun step => perm layer step i)) ∧
      ∀ i j, ((Finset.univ : Finset (Fin B × Fin D)).filter
        (fun p => perm p.1 p.2 i = j)).card = w i j) := by
  classical
  intro n B D w bound rows cols
  obtain ⟨perm, inj, count⟩ := PEqualNP.Outside.L_lib_729.layers B D w bound rows cols
  refine ⟨perm, inj, fun i j => ?_⟩
  rw [Finset.card_filter, Fintype.sum_prod_type]; exact count i j

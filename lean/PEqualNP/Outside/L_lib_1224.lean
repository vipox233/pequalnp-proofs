import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1224.Aux

structure Witness where
  N : Nat
  adj : List (List Nat)
  side : List Bool
  dist : List Nat
  p : Nat
  r : Nat
  bags : List (List Nat)

def parityRec (N : Nat) (adj : Fin N → Nat) (p r : Fin N) (a b : Bool) : Nat → Nat → Bool
  | 0, mask => decide (mask.testBit p.1 = a ∧ mask.testBit r.1 = b)
  | i + 1, mask =>
    let r0 := parityRec N adj p r a b i mask
    if h : i < N then
      let m := adj ⟨i, h⟩
      if (mask &&& m) == 0 then
        xor r0 (parityRec N adj p r a b i (mask ||| (1 <<< i)))
      else r0
    else r0

def degOf (w : Witness) (u : Fin w.N) : Nat :=
  Fin.foldl w.N (fun c v => if v.1 ∈ w.adj.getD u.1 [] then c + 1 else c) 0

def adjMaskOf (w : Witness) (u : Fin w.N) : Nat :=
  Fin.foldl w.N (fun acc v => if v.1 ∈ w.adj.getD u.1 [] then acc ||| (1 <<< v.1) else acc) 0

def invOf (k00 k01 k10 k11 : Bool) : Bool := xor (k00 && k11) (k01 && k10)

def pathFormOf (k00 k01 k10 k11 : Bool) : Bool :=
  (k00 && !k01 && !k10 && k11) || (k00 && k01 && k10 && !k11) || (!k00 && k01 && k10 && k11)

def cycOf (k00 k01 k10 k11 : Bool) : Nat :=
  if invOf k00 k01 k10 k11 && !(pathFormOf k00 k01 k10 k11) then 1 else 0

def checkWitness (k00 k01 k10 k11 rs : Bool) (w : Witness) : Bool :=
  if h : 0 < w.N ∧ w.N ≤ 15 ∧ w.p < w.N ∧ w.r < w.N ∧ w.p ≠ w.r then
    let p : Fin w.N := ⟨w.p, h.2.2.1⟩
    let r : Fin w.N := ⟨w.r, h.2.2.2.1⟩
    let irrefl := Fin.foldl w.N (fun ok u => ok && !(u.1 ∈ w.adj.getD u.1 [])) true
    let symm := Fin.foldl w.N (fun ok u => ok &&
      Fin.foldl w.N (fun ok2 v => ok2 && ((v.1 ∈ w.adj.getD u.1 []) == (u.1 ∈ w.adj.getD v.1 []))) true) true
    let conn := Fin.foldl w.N (fun ok u => ok && (u.1 == 0 ||
      Fin.foldl w.N (fun ok2 v => ok2 || (v.1 ∈ w.adj.getD u.1 [] && w.dist.getD v.1 0 < w.dist.getD u.1 0)) false)) true
    let shores := !(w.side.getD w.p false) && (w.side.getD w.r false == rs)
    let bip := Fin.foldl w.N (fun ok u => ok &&
      Fin.foldl w.N (fun ok2 v => ok2 && (!(v.1 ∈ w.adj.getD u.1 []) || (w.side.getD u.1 false != w.side.getD v.1 false))) true) true
    let maxdeg := Fin.foldl w.N (fun ok u => ok && (degOf w u ≤ 3)) true
    let pdeg := (degOf w p == 1) && (degOf w r == 1)
    let sumdeg := Fin.foldl w.N (fun c u => c + degOf w u) 0 == 2 * (w.N - 1 + cycOf k00 k01 k10 k11)
    let masks := List.ofFn (adjMaskOf w)
    let mfn : Fin w.N → Nat := fun i => masks.getD i.1 0
    let sigok :=
      (parityRec w.N mfn p r false false w.N 0 == k00) &&
      (parityRec w.N mfn p r false true w.N 0 == k01) &&
      (parityRec w.N mfn p r true false w.N 0 == k10) &&
      (parityRec w.N mfn p r true true w.N 0 == k11)
    let l := w.bags.length
    let bag1 := Fin.foldl l (fun ok t => ok &&
      (w.p ∈ w.bags.getD t.1 []) && (w.r ∈ w.bags.getD t.1 []) &&
      (Fin.foldl w.N (fun c v => if v.1 ∈ w.bags.getD t.1 [] then c + 1 else c) 0 ≤ 6)) true
    let bag2 := Fin.foldl w.N (fun ok v => ok &&
      Fin.foldl l (fun ok2 t => ok2 || (v.1 ∈ w.bags.getD t.1 [])) false) true
    let bag3 := Fin.foldl w.N (fun ok u => ok &&
      Fin.foldl w.N (fun ok2 v => ok2 && (!(v.1 ∈ w.adj.getD u.1 []) ||
        Fin.foldl l (fun ok3 t => ok3 || (u.1 ∈ w.bags.getD t.1 [] && v.1 ∈ w.bags.getD t.1 [])) false)) true) true
    let bag4 := Fin.foldl w.N (fun ok v => ok &&
      Fin.foldl l (fun ok1 s => ok1 &&
        Fin.foldl l (fun ok2 t => ok2 &&
          Fin.foldl l (fun ok3 u => ok3 &&
            (!(s.1 ≤ t.1 && t.1 ≤ u.1 && (v.1 ∈ w.bags.getD s.1 []) && (v.1 ∈ w.bags.getD u.1 [])) ||
              (v.1 ∈ w.bags.getD t.1 []))) true) true) true) true
    irrefl && symm && conn && shores && bip && maxdeg && pdeg && sumdeg && sigok && bag1 && bag2 && bag3 && bag4
  else false

theorem foldl_all_aux (n : Nat) (P : Fin n → Bool) (init : Bool) :
    Fin.foldl n (fun ok i => ok && P i) init = true ↔ init = true ∧ ∀ i : Fin n, P i = true := by
  induction n with
  | zero =>
    simp only [Fin.foldl_zero]
    constructor
    · intro h; exact ⟨h, fun i => Fin.elim0 i⟩
    · intro h; exact h.1
  | succ n ih =>
    rw [Fin.foldl_succ_last]
    simp only [Bool.and_eq_true, ih, Fin.forall_fin_succ']
    tauto

theorem foldl_all {n : Nat} (P : Fin n → Bool) :
    Fin.foldl n (fun ok i => ok && P i) true = true ↔ ∀ i : Fin n, P i = true := by
  simpa using foldl_all_aux n P true

theorem foldl_any_aux (n : Nat) (P : Fin n → Bool) (init : Bool) :
    Fin.foldl n (fun ok i => ok || P i) init = true ↔ init = true ∨ ∃ i : Fin n, P i = true := by
  induction n with
  | zero =>
    simp only [Fin.foldl_zero]
    constructor
    · intro h; exact Or.inl h
    · rintro (h | ⟨i, _⟩)
      · exact h
      · exact Fin.elim0 i
  | succ n ih =>
    rw [Fin.foldl_succ_last]
    simp only [Bool.or_eq_true, ih, Fin.exists_fin_succ']
    tauto

theorem foldl_any {n : Nat} (P : Fin n → Bool) :
    Fin.foldl n (fun ok i => ok || P i) false = true ↔ ∃ i : Fin n, P i = true := by
  simpa using foldl_any_aux n P false

theorem foldl_count_aux (n : Nat) (P : Fin n → Bool) (init : Nat) :
    Fin.foldl n (fun c i => if P i then c + 1 else c) init =
      init + (Finset.univ.filter (fun i : Fin n => P i = true)).card := by
  induction n generalizing init with
  | zero => simp [Fin.foldl_zero]
  | succ n ih =>
    rw [Fin.foldl_succ_last, ih (fun i => P i.castSucc) init]
    have hsum : (Finset.univ.filter (fun i : Fin (n + 1) => P i = true)).card =
        (Finset.univ.filter (fun i : Fin n => P i.castSucc = true)).card +
          (if P (Fin.last n) then 1 else 0) := by
      simp only [Finset.card_filter, Fin.sum_univ_castSucc]
    rw [hsum]
    split_ifs <;> omega

theorem foldl_count {n : Nat} (P : Fin n → Bool) :
    Fin.foldl n (fun c i => if P i then c + 1 else c) 0 =
      (Finset.univ.filter (fun i : Fin n => P i = true)).card := by
  simpa using foldl_count_aux n P 0

theorem foldl_sum_aux (n : Nat) (f : Fin n → Nat) (init : Nat) :
    Fin.foldl n (fun c i => c + f i) init = init + ∑ i : Fin n, f i := by
  induction n generalizing init with
  | zero => simp [Fin.foldl_zero]
  | succ n ih =>
    rw [Fin.foldl_succ_last, ih (fun i => f i.castSucc) init, Fin.sum_univ_castSucc]
    omega

theorem foldl_sum {n : Nat} (f : Fin n → Nat) :
    Fin.foldl n (fun c i => c + f i) 0 = ∑ i : Fin n, f i := by
  simpa using foldl_sum_aux n f 0

theorem connected_of_dist {N : Nat} {G : Fin N → Finset (Fin N)} (hN : 0 < N)
    (hsymm : ∀ u v, v ∈ G u ↔ u ∈ G v) (dist : Fin N → Nat)
    (hdist : ∀ u : Fin N, u.1 = 0 ∨ ∃ v ∈ G u, dist v < dist u) :
    ∀ S : Finset (Fin N), S.Nonempty → S ≠ Finset.univ → ∃ u ∈ S, ∃ v ∈ G u, v ∉ S := by
  intro S hS hSu
  let z : Fin N := ⟨0, hN⟩
  by_cases hz : z ∈ S
  · have hSc : Sᶜ.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hc
      apply hSu
      ext x
      simp only [Finset.mem_univ, iff_true]
      by_contra hx
      have : x ∈ Sᶜ := Finset.mem_compl.mpr hx
      rw [hc] at this
      exact Finset.notMem_empty x this
    obtain ⟨v, hvSc, hvmin⟩ := Finset.exists_min_image Sᶜ dist hSc
    have hvS : v ∉ S := Finset.mem_compl.mp hvSc
    have hv0 : v.1 ≠ 0 := by
      intro h0
      apply hvS
      have : v = z := Fin.ext h0
      rw [this]
      exact hz
    rcases hdist v with h0 | ⟨u, huG, hud⟩
    · exact absurd h0 hv0
    · have huS : u ∈ S := by
        by_contra huNS
        have hle := hvmin u (Finset.mem_compl.mpr huNS)
        omega
      exact ⟨u, huS, v, (hsymm v u).mp huG, hvS⟩
  · obtain ⟨u, huS, humin⟩ := Finset.exists_min_image S dist hS
    have hu0 : u.1 ≠ 0 := by
      intro h0
      apply hz
      have : z = u := Fin.ext h0.symm
      rw [this]
      exact huS
    rcases hdist u with h0 | ⟨v, hvG, hvd⟩
    · exact absurd h0 hu0
    · have hvNS : v ∉ S := by
        intro hvS
        have hle := humin v hvS
        omega
      exact ⟨u, huS, v, hvG, hvNS⟩

theorem foldl_or_shift_testBit_aux (n : Nat) (P : Fin n → Bool) (init m : Nat) :
    (Fin.foldl n (fun acc v => if P v then acc ||| (1 <<< v.1) else acc) init).testBit m =
      (init.testBit m || decide (∃ v : Fin n, v.1 = m ∧ P v = true)) := by
  induction n generalizing init with
  | zero =>
    simp [Fin.foldl_zero]
  | succ n ih =>
    rw [Fin.foldl_succ_last]
    have hbit : ∀ x : Nat,
        ((if P (Fin.last n) then x ||| (1 <<< (Fin.last n).1) else x).testBit m) =
        (x.testBit m || (decide ((Fin.last n).1 = m) && P (Fin.last n))) := by
      intro x
      by_cases hp : P (Fin.last n) = true
      · simp only [hp, ite_true, Nat.testBit_or, Nat.testBit_shiftLeft, Bool.and_true]
        by_cases hm : m = n
        · subst hm; simp
        · have hne : ¬((Fin.last n).1 = m) := by simp; omega
          simp only [hne, decide_false, Bool.or_false]
          by_cases hge : n ≤ m
          · have hlt : 0 < m - n := by omega
            have h1 : (1 : Nat).testBit (m - n) = false := by
              rw [Nat.testBit_eq_false_of_lt]
              exact Nat.one_lt_two_pow (by omega)
            simp [hge, h1]
          · simp [hge]
      · simp [hp]
    rw [hbit]
    simp only [Fin.val_castSucc]
    rw [ih (fun v => P v.castSucc) init, Bool.or_assoc]
    congr 1
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Fin.exists_fin_succ',
      Fin.val_castSucc]

theorem adjMaskOf_testBit (w : Witness) (u : Fin w.N) (m : Nat) :
    (adjMaskOf w u).testBit m =
      decide (∃ v : Fin w.N, v.1 = m ∧ v.1 ∈ w.adj.getD u.1 []) := by
  unfold adjMaskOf
  have h := foldl_or_shift_testBit_aux w.N (fun v => decide (v.1 ∈ w.adj.getD u.1 [])) 0 m
  simpa using h

theorem adjMaskOf_testBit_lt (w : Witness) (u v : Fin w.N) :
    (adjMaskOf w u).testBit v.1 = decide (v.1 ∈ w.adj.getD u.1 []) := by
  rw [adjMaskOf_testBit]
  congr 1
  apply propext
  constructor
  · rintro ⟨v', hv', hmem⟩
    have : v' = v := Fin.ext hv'
    rwa [← this]
  · intro hmem
    exact ⟨v, rfl, hmem⟩

theorem adjMaskOf_testBit_ge (w : Witness) (u : Fin w.N) {m : Nat} (hm : w.N ≤ m) :
    (adjMaskOf w u).testBit m = false := by
  rw [adjMaskOf_testBit]
  simp only [decide_eq_false_iff_not]
  rintro ⟨v, hvm, _⟩
  omega

theorem parityRec_spec (N : Nat) (G : Fin N → Finset (Fin N)) (adj : Fin N → Nat)
    (hirr : ∀ v, v ∉ G v) (hsymm : ∀ u v, v ∈ G u ↔ u ∈ G v)
    (hadj1 : ∀ u v : Fin N, (adj u).testBit v.1 = decide (v ∈ G u))
    (hadj2 : ∀ u : Fin N, ∀ m, N ≤ m → (adj u).testBit m = false)
    (p r : Fin N) (a b : Bool) :
    ∀ k, k ≤ N → ∀ mask : Nat,
      (∀ j : Fin N, j.1 < k → mask.testBit j.1 = false) →
      (∀ u v : Fin N, mask.testBit u.1 = true → v ∈ G u → mask.testBit v.1 = false) →
      parityRec N adj p r a b k mask =
        decide ((Finset.univ.filter (fun I : Finset (Fin N) =>
          (∀ u ∈ I, ∀ v ∈ G u, v ∉ I) ∧ decide (p ∈ I) = a ∧ decide (r ∈ I) = b ∧
          ∀ j : Fin N, k ≤ j.1 → (j ∈ I ↔ mask.testBit j.1 = true))).card % 2 = 1) := by
  intro k
  induction k with
  | zero =>
    intro _ mask _ hmask_is
    simp only [parityRec, Nat.zero_le, forall_true_left]
    let I0 : Finset (Fin N) := Finset.univ.filter (fun j : Fin N => mask.testBit j.1 = true)
    have hI0_is : ∀ u ∈ I0, ∀ v ∈ G u, v ∉ I0 := by
      intro u hu v hv hvI
      simp only [I0, Finset.mem_filter, Finset.mem_univ, true_and] at hu hvI
      have := hmask_is u v hu hv
      rw [hvI] at this
      exact Bool.noConfusion this
    have huniq : ∀ I : Finset (Fin N),
        ((∀ u ∈ I, ∀ v ∈ G u, v ∉ I) ∧ decide (p ∈ I) = a ∧ decide (r ∈ I) = b ∧
          ∀ j : Fin N, j ∈ I ↔ mask.testBit j.1 = true) ↔
        (I = I0 ∧ mask.testBit p.1 = a ∧ mask.testBit r.1 = b) := by
      intro I
      constructor
      · rintro ⟨_, hp, hr, hmem⟩
        have hEq : I = I0 := by
          ext j
          simp only [I0, Finset.mem_filter, Finset.mem_univ, true_and]
          exact hmem j
        subst hEq
        refine ⟨rfl, ?_, ?_⟩
        · simpa [I0] using hp
        · simpa [I0] using hr
      · rintro ⟨rfl, hp, hr⟩
        refine ⟨hI0_is, ?_, ?_, ?_⟩
        · simpa [I0] using hp
        · simpa [I0] using hr
        · intro j; simp [I0]
    by_cases hpr : mask.testBit p.1 = a ∧ mask.testBit r.1 = b
    · have hset : (Finset.univ.filter (fun I : Finset (Fin N) =>
          (∀ u ∈ I, ∀ v ∈ G u, v ∉ I) ∧ decide (p ∈ I) = a ∧ decide (r ∈ I) = b ∧
          ∀ j : Fin N, j ∈ I ↔ mask.testBit j.1 = true)) = {I0} := by
        ext I
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        rw [huniq I]
        simp [hpr]
      rw [hset]
      simp [hpr]
    · have hset : (Finset.univ.filter (fun I : Finset (Fin N) =>
          (∀ u ∈ I, ∀ v ∈ G u, v ∉ I) ∧ decide (p ∈ I) = a ∧ decide (r ∈ I) = b ∧
          ∀ j : Fin N, j ∈ I ↔ mask.testBit j.1 = true)) = ∅ := by
        ext I
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        rw [huniq I]
        intro ⟨_, hpr'⟩
        exact hpr hpr'
      rw [hset]
      simp [hpr]
  | succ i ih =>
    intro hiN mask hlt hmask_is
    have hi : i < N := by omega
    let v : Fin N := ⟨i, hi⟩
    let S := Finset.univ.filter (fun I : Finset (Fin N) =>
      (∀ u ∈ I, ∀ w ∈ G u, w ∉ I) ∧ decide (p ∈ I) = a ∧ decide (r ∈ I) = b ∧
      ∀ j : Fin N, i + 1 ≤ j.1 → (j ∈ I ↔ mask.testBit j.1 = true))
    let S0 := S.filter (fun I => v ∉ I)
    let S1 := S.filter (fun I => v ∈ I)
    have hdisj : Disjoint S0 S1 := by
      rw [Finset.disjoint_left]
      intro I h0 h1
      simp only [S0, S1, Finset.mem_filter] at h0 h1
      exact h0.2 h1.2
    have hunion : S = S0 ∪ S1 := by
      ext I
      simp only [S0, S1, Finset.mem_union, Finset.mem_filter]
      tauto
    have hcard : S.card = S0.card + S1.card := by
      rw [hunion, Finset.card_union_of_disjoint hdisj]
    have hS0 : S0 = Finset.univ.filter (fun I : Finset (Fin N) =>
        (∀ u ∈ I, ∀ w ∈ G u, w ∉ I) ∧ decide (p ∈ I) = a ∧ decide (r ∈ I) = b ∧
        ∀ j : Fin N, i ≤ j.1 → (j ∈ I ↔ mask.testBit j.1 = true)) := by
      ext I
      simp only [S0, S, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨his, hp, hr, hmem⟩, hv⟩
        refine ⟨his, hp, hr, ?_⟩
        intro j hj
        by_cases hji : j.1 = i
        · have hjv : j = v := Fin.ext hji
          subst hjv
          have hbit : mask.testBit v.1 = false := hlt v (by dsimp [v]; omega)
          simp [hv, hbit]
        · exact hmem j (by omega)
      · rintro ⟨his, hp, hr, hmem⟩
        have hv : v ∉ I := by
          have := hmem v (by dsimp [v]; omega)
          have hbit : mask.testBit v.1 = false := hlt v (by dsimp [v]; omega)
          simp [hbit] at this
          exact this
        refine ⟨⟨his, hp, hr, ?_⟩, hv⟩
        intro j hj
        exact hmem j (by omega)
    have ih0 := ih (by omega) mask (fun j hj => hlt j (by omega)) hmask_is
    have hpar0 : decide (S0.card % 2 = 1) = parityRec N adj p r a b i mask := by
      rw [hS0, ← ih0]
    have hxor_card : decide (S.card % 2 = 1) =
        xor (decide (S0.card % 2 = 1)) (decide (S1.card % 2 = 1)) := by
      rw [hcard]
      have : (S0.card + S1.card) % 2 = (S0.card % 2 + S1.card % 2) % 2 := Nat.add_mod _ _ _
      rw [this]
      rcases Nat.mod_two_eq_zero_or_one S0.card with h0 | h0 <;>
        rcases Nat.mod_two_eq_zero_or_one S1.card with h1 | h1 <;>
        simp [h0, h1]
    change parityRec N adj p r a b (i + 1) mask = decide (S.card % 2 = 1)
    unfold parityRec
    split_ifs
    dsimp only
    rw [hxor_card, hpar0]
    split_ifs with hzero
    · have hmask_adj : ∀ u ∈ G v, mask.testBit u.1 = false := by
        intro u hu
        have h0 : mask &&& adj v = 0 := by simpa using hzero
        have hb := congrArg (fun x => Nat.testBit x u.1) h0
        rw [Nat.testBit_and, Nat.zero_testBit, hadj1 v u, decide_eq_true hu, Bool.and_true] at hb
        exact hb
      let mask' := mask ||| (1 <<< i)
      have hlt' : ∀ j : Fin N, j.1 < i → mask'.testBit j.1 = false := by
        intro j hj
        simp only [mask', Nat.testBit_or, Nat.testBit_shiftLeft, hlt j (by omega), Bool.false_or]
        have hnot : ¬(j.1 ≥ i) := by omega
        simp [hnot]
      have hmask_is' : ∀ u w : Fin N, mask'.testBit u.1 = true → w ∈ G u → mask'.testBit w.1 = false := by
        intro u w hu hw
        simp only [mask', Nat.testBit_or, Nat.testBit_shiftLeft, Bool.or_eq_true, Bool.and_eq_true,
          decide_eq_true_eq] at hu
        have hbitw : (1 <<< i).testBit w.1 = false := by
          rw [Nat.testBit_shiftLeft]
          by_cases hwi : w.1 ≥ i
          · by_cases hweq : w.1 = i
            · exfalso
              have hwv : w = v := Fin.ext hweq
              subst hwv
              rcases hu with hu0 | ⟨hge, h1⟩
              · have := hmask_adj u ((hsymm u v).mp hw)
                rw [hu0] at this
                exact Bool.noConfusion this
              · have hueq : u.1 = i := by
                  by_contra hne
                  have hlt2 : 0 < u.1 - i := by omega
                  have hlt_pow : 1 < 2 ^ (u.1 - i) := Nat.one_lt_two_pow (by omega)
                  have h1f : (1 : Nat).testBit (u.1 - i) = false := Nat.testBit_eq_false_of_lt hlt_pow
                  rw [h1f] at h1
                  exact Bool.noConfusion h1
                have huv : u = v := Fin.ext hueq
                subst huv
                exact hirr v hw
            · have hlt2 : 0 < w.1 - i := by omega
              have hlt_pow : 1 < 2 ^ (w.1 - i) := Nat.one_lt_two_pow (by omega)
              simp [hwi, Nat.testBit_eq_false_of_lt hlt_pow]
          · simp [hwi]
        simp only [mask', Nat.testBit_or, hbitw, Bool.or_false]
        rcases hu with hu0 | ⟨hge, h1⟩
        · exact hmask_is u w hu0 hw
        · have hueq : u.1 = i := by
            by_contra hne
            have hlt2 : 0 < u.1 - i := by omega
            have hlt_pow : 1 < 2 ^ (u.1 - i) := Nat.one_lt_two_pow (by omega)
            have h1f : (1 : Nat).testBit (u.1 - i) = false := Nat.testBit_eq_false_of_lt hlt_pow
            rw [h1f] at h1
            exact Bool.noConfusion h1
          have huv : u = v := Fin.ext hueq
          subst huv
          exact hmask_adj w hw
      have hS1 : S1 = Finset.univ.filter (fun I : Finset (Fin N) =>
          (∀ u ∈ I, ∀ w ∈ G u, w ∉ I) ∧ decide (p ∈ I) = a ∧ decide (r ∈ I) = b ∧
          ∀ j : Fin N, i ≤ j.1 → (j ∈ I ↔ mask'.testBit j.1 = true)) := by
        ext I
        simp only [S1, S, Finset.mem_filter, Finset.mem_univ, true_and]
        have hbit_eq : ∀ j : Fin N, i + 1 ≤ j.1 → mask'.testBit j.1 = mask.testBit j.1 := by
          intro j hj
          simp only [mask', Nat.testBit_or, Nat.testBit_shiftLeft]
          have hlt2 : 0 < j.1 - i := by omega
          have hlt_pow : 1 < 2 ^ (j.1 - i) := Nat.one_lt_two_pow (by omega)
          have h1f : (1 : Nat).testBit (j.1 - i) = false := Nat.testBit_eq_false_of_lt hlt_pow
          simp [h1f]
        have hbit_v : mask'.testBit v.1 = true := by
          simp [mask', v, Nat.testBit_or, Nat.testBit_shiftLeft]
        constructor
        · rintro ⟨⟨his, hp, hr, hmem⟩, hv⟩
          refine ⟨his, hp, hr, ?_⟩
          intro j hj
          by_cases hji : j.1 = i
          · have hjv : j = v := Fin.ext hji
            subst hjv
            simp [hv, hbit_v]
          · rw [hbit_eq j (by omega)]
            exact hmem j (by omega)
        · rintro ⟨his, hp, hr, hmem⟩
          have hv : v ∈ I := by
            have := hmem v (by dsimp [v]; omega)
            rw [hbit_v] at this
            simpa using this
          refine ⟨⟨his, hp, hr, ?_⟩, hv⟩
          intro j hj
          rw [← hbit_eq j hj]
          exact hmem j (by omega)
      have ih1 := ih (by omega) mask' hlt' hmask_is'
      have hpar1 : decide (S1.card % 2 = 1) = parityRec N adj p r a b i mask' := by
        rw [hS1, ← ih1]
      rw [hpar1]
    · have hne0 : mask &&& adj v ≠ 0 := by simpa using hzero
      have hex : ∃ m : Nat, (mask &&& adj v).testBit m = true := by
        by_contra hall
        apply hne0
        apply Nat.eq_of_testBit_eq
        intro m
        rw [Nat.zero_testBit]
        by_contra ht
        apply hall
        exact ⟨m, by cases h : (mask &&& adj v).testBit m <;> simp_all⟩
      obtain ⟨m, hm⟩ := hex
      rw [Nat.testBit_and, Bool.and_eq_true] at hm
      have hmN : m < N := by
        by_contra hge
        have := hadj2 v m (by omega)
        rw [hm.2] at this
        exact Bool.noConfusion this
      let u : Fin N := ⟨m, hmN⟩
      have huG : u ∈ G v := by
        have := hadj1 v u
        rw [hm.2] at this
        simpa using this.symm
      have hu_ge : i + 1 ≤ u.1 := by
        by_contra hlt_u
        have := hlt u (by omega)
        rw [hm.1] at this
        exact Bool.noConfusion this
      have hS1_empty : S1 = ∅ := by
        ext I
        simp only [S1, S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
          iff_false]
        rintro ⟨⟨his, _, _, hmem⟩, hv⟩
        have huI : u ∈ I := (hmem u hu_ge).mpr hm.1
        exact his v hv u huG huI
      rw [hS1_empty]
      simp

theorem cycOf_eq (k00 k01 k10 k11 : Bool) :
    let K : Bool → Bool → Bool := fun a b =>
      if a then (if b then k11 else k10) else (if b then k01 else k00)
    let inv := xor (K false false && K true true) (K false true && K true false)
    let pathForm := K = (fun a b => decide (a = b)) ∨
      K = (fun a b => !(a && b)) ∨ K = (fun a b => a || b)
    cycOf k00 k01 k10 k11 = if inv = true ∧ ¬pathForm then 1 else 0 := by
  intro K inv pathForm
  have hinv : invOf k00 k01 k10 k11 = inv := rfl
  have hpf : pathFormOf k00 k01 k10 k11 = true ↔ pathForm := by
    cases k00 <;> cases k01 <;> cases k10 <;> cases k11
    all_goals
      constructor
      · intro h
        first
        | exact False.elim (by revert h; decide)
        | (left; funext a b; cases a <;> cases b <;> decide)
        | (right; left; funext a b; cases a <;> cases b <;> decide)
        | (right; right; funext a b; cases a <;> cases b <;> decide)
      · rintro (h | h | h) <;>
          have h00 := congrFun (congrFun h false) false <;>
          have h01 := congrFun (congrFun h false) true <;>
          have h10 := congrFun (congrFun h true) false <;>
          have h11 := congrFun (congrFun h true) true <;>
          simp only [K] at h00 h01 h10 h11 <;>
          first
          | exact absurd h00 (by decide)
          | exact absurd h01 (by decide)
          | exact absurd h10 (by decide)
          | exact absurd h11 (by decide)
          | decide
  unfold cycOf
  rw [hinv]
  by_cases hp : pathForm
  · have hpt : pathFormOf k00 k01 k10 k11 = true := hpf.mpr hp
    simp [hp, hpt]
  · have hpf2 : pathFormOf k00 k01 k10 k11 = false := by
      cases hc : pathFormOf k00 k01 k10 k11
      · rfl
      · exact absurd (hpf.mp hc) hp
    simp [hp, hpf2]

theorem witness_ok (k00 k01 k10 k11 rs : Bool) (w : Witness)
    (h : checkWitness k00 k01 k10 k11 rs w = true) :
    letI : ∀ q : Prop, Decidable q := Classical.propDecidable
    let K : Bool → Bool → Bool := fun a b =>
      if a then (if b then k11 else k10) else (if b then k01 else k00)
    let inv := xor (K false false && K true true) (K false true && K true false)
    let pathForm := K = (fun a b => decide (a = b)) ∨
      K = (fun a b => !(a && b)) ∨ K = (fun a b => a || b)
    let cycles := if inv = true ∧ ¬pathForm then 1 else 0
    ∃ (N : Nat) (G : Fin N → Finset (Fin N)) (side : Fin N → Bool) (p r : Fin N),
      N ≤ 15 ∧ p ≠ r ∧
      ((∀ v, v ∉ G v) ∧ (∀ u v, v ∈ G u ↔ u ∈ G v) ∧
        ∀ S : Finset (Fin N), S.Nonempty → S ≠ Finset.univ →
          ∃ u ∈ S, ∃ v ∈ G u, v ∉ S) ∧
      side p = false ∧ side r = rs ∧
      (∀ u, ∀ v ∈ G u, side u ≠ side v) ∧ (∀ u, (G u).card ≤ 3) ∧
      (G p).card = 1 ∧ (G r).card = 1 ∧
      (∑ v, (G v).card) = 2*(N-1+cycles) ∧
      (fun a b => decide (((Finset.univ : Finset (Finset (Fin N))).filter (fun I =>
        (∀ u ∈ I, ∀ v ∈ G u, v ∉ I) ∧ decide (p ∈ I) = a ∧ decide (r ∈ I) = b)).card % 2 = 1)) = K ∧
      ∃ (l : Nat) (bag : Fin l → Finset (Fin N)),
        (∀ t, p ∈ bag t ∧ r ∈ bag t ∧ (bag t).card ≤ 6) ∧
        (∀ v, ∃ t, v ∈ bag t) ∧ (∀ u v, v ∈ G u → ∃ t, u ∈ bag t ∧ v ∈ bag t) ∧
        ∀ v s t u, s ≤ t → t ≤ u → v ∈ bag s → v ∈ bag u → v ∈ bag t := by
  unfold checkWitness at h
  split_ifs at h with hdim
  rcases hdim with ⟨hN0, hN15, hpN, hrN, hpr⟩
  simp only [Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hirr, hsymm⟩, hconn⟩, hshores⟩, hbip⟩, hmaxdeg⟩, hpdeg⟩, hsumdeg⟩, hsig⟩, hbag1⟩, hbag2⟩, hbag3⟩, hbag4⟩
  let G : Fin w.N → Finset (Fin w.N) := fun u => Finset.univ.filter (fun v => v.1 ∈ w.adj.getD u.1 [])
  let side : Fin w.N → Bool := fun u => w.side.getD u.1 false
  let p : Fin w.N := ⟨w.p, hpN⟩
  let r : Fin w.N := ⟨w.r, hrN⟩
  have hmemG : ∀ u v : Fin w.N, v ∈ G u ↔ v.1 ∈ w.adj.getD u.1 [] := by
    intro u v; simp [G]
  have hdegG : ∀ u : Fin w.N, degOf w u = (G u).card := by
    intro u
    unfold degOf
    have hc := foldl_count (n := w.N) (fun v => decide (v.1 ∈ w.adj.getD u.1 []))
    simpa [G] using hc
  have hirrG : ∀ v : Fin w.N, v ∉ G v := by
    rw [foldl_all] at hirr
    intro v hv
    rw [hmemG] at hv
    have := hirr v
    simp only [Bool.not_eq_true', decide_eq_false_iff_not] at this
    exact this hv
  have hsymmG : ∀ u v : Fin w.N, v ∈ G u ↔ u ∈ G v := by
    rw [foldl_all] at hsymm
    intro u v
    have h1 := (foldl_all _).mp (hsymm u) v
    simpa [hmemG] using h1
  have hconnG : ∀ S : Finset (Fin w.N), S.Nonempty → S ≠ Finset.univ →
      ∃ u ∈ S, ∃ v ∈ G u, v ∉ S := by
    rw [foldl_all] at hconn
    apply connected_of_dist hN0 hsymmG (fun u => w.dist.getD u.1 0)
    intro u
    have h1 := hconn u
    simp only [Bool.or_eq_true, beq_iff_eq] at h1
    rcases h1 with hu0 | hex
    · exact Or.inl hu0
    · rw [foldl_any] at hex
      obtain ⟨v, hv⟩ := hex
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
      exact Or.inr ⟨v, (hmemG u v).mpr hv.1, hv.2⟩
  refine ⟨w.N, G, side, p, r, hN15, fun heq => hpr (congrArg Fin.val heq),
    ⟨hirrG, hsymmG, hconnG⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Bool.not_eq_true', beq_iff_eq] at hshores
    exact hshores.1
  · simp only [Bool.not_eq_true', beq_iff_eq] at hshores
    exact hshores.2
  · rw [foldl_all] at hbip
    intro u v hv
    have h1 := (foldl_all _).mp (hbip u) v
    rw [hmemG] at hv
    simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, bne_iff_ne] at h1
    rcases h1 with hnot | hne
    · exact absurd hv hnot
    · exact hne
  · rw [foldl_all] at hmaxdeg
    intro u
    have h1 := hmaxdeg u
    rw [← hdegG u]
    simpa using h1
  · simp only [beq_iff_eq] at hpdeg
    rw [← hdegG p]
    exact hpdeg.1
  · simp only [beq_iff_eq] at hpdeg
    rw [← hdegG r]
    exact hpdeg.2
  · simp only [beq_iff_eq] at hsumdeg
    rw [foldl_sum] at hsumdeg
    have hsumG : ∑ u : Fin w.N, degOf w u = ∑ v : Fin w.N, (G v).card := by
      refine Finset.sum_congr rfl (fun u _ => hdegG u)
    dsimp only
    rw [← hsumG, hsumdeg, cycOf_eq]
    congr!
  · simp only [beq_iff_eq] at hsig
    have hmfn : ∀ i : Fin w.N, (List.ofFn (adjMaskOf w)).getD i.1 0 = adjMaskOf w i := by
      intro i
      rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp
    have hpar_eq : ∀ a b,
        parityRec w.N (fun i => (List.ofFn (adjMaskOf w)).getD i.1 0) p r a b w.N 0 =
        parityRec w.N (adjMaskOf w) p r a b w.N 0 := by
      intro a b
      have hfn : (fun i => (List.ofFn (adjMaskOf w)).getD i.1 0) = adjMaskOf w := funext hmfn
      rw [hfn]
    have hspec : ∀ a b,
        decide (((Finset.univ : Finset (Finset (Fin w.N))).filter (fun I =>
          (∀ u ∈ I, ∀ v ∈ G u, v ∉ I) ∧ decide (p ∈ I) = a ∧ decide (r ∈ I) = b)).card % 2 = 1) =
        parityRec w.N (adjMaskOf w) p r a b w.N 0 := by
      intro a b
      have hs := parityRec_spec w.N G (adjMaskOf w) hirrG hsymmG
        (fun u v => by
          rw [adjMaskOf_testBit_lt]
          exact Bool.eq_iff_iff.mpr (by simpa [decide_eq_true_eq] using (hmemG u v).symm))
        (fun u m hm => adjMaskOf_testBit_ge w u hm)
        p r a b w.N (le_refl _) 0
        (fun j _ => Nat.zero_testBit _)
        (fun u _ hu _ => absurd hu (by simp [Nat.zero_testBit]))
      have hset :
          Finset.univ.filter (fun I : Finset (Fin w.N) =>
            (∀ u ∈ I, ∀ v ∈ G u, v ∉ I) ∧ decide (p ∈ I) = a ∧ decide (r ∈ I) = b) =
          Finset.univ.filter (fun I : Finset (Fin w.N) =>
            (∀ u ∈ I, ∀ v ∈ G u, v ∉ I) ∧ decide (p ∈ I) = a ∧ decide (r ∈ I) = b ∧
            ∀ j : Fin w.N, w.N ≤ j.1 → (j ∈ I ↔ (0 : Nat).testBit j.1 = true)) := by
        ext I
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨his, hp, hr⟩
          exact ⟨his, hp, hr, fun j hj => absurd j.2 (by omega)⟩
        · rintro ⟨his, hp, hr, _⟩
          exact ⟨his, hp, hr⟩
      rw [hset, ← hs]
    funext a b
    have hspec_c :
        @decide ((@Finset.filter (Finset (Fin w.N))
          (fun I => (∀ u ∈ I, ∀ v ∈ G u, v ∉ I) ∧
            @decide (p ∈ I) (Classical.propDecidable _) = a ∧
            @decide (r ∈ I) (Classical.propDecidable _) = b)
          (fun _ => Classical.propDecidable _) Finset.univ).card % 2 = 1)
          (Classical.propDecidable _) =
        parityRec w.N (adjMaskOf w) p r a b w.N 0 := by
      rw [← hspec a b]
      congr!
    rw [hspec_c]
    cases a <;> cases b
    · rw [← hpar_eq]; simpa [p, r] using hsig.1.1.1
    · rw [← hpar_eq]; simpa [p, r] using hsig.1.1.2
    · rw [← hpar_eq]; simpa [p, r] using hsig.1.2
    · rw [← hpar_eq]; simpa [p, r] using hsig.2
  · let l := w.bags.length
    let bag : Fin l → Finset (Fin w.N) := fun t => Finset.univ.filter (fun v => v.1 ∈ w.bags.getD t.1 [])
    have hmembag : ∀ (v : Fin w.N) (t : Fin l), v ∈ bag t ↔ v.1 ∈ w.bags.getD t.1 [] := by
      intro v t; simp [bag]
    refine ⟨l, bag, ?_, ?_, ?_, ?_⟩
    · simp only [Bool.and_assoc] at hbag1
      rw [foldl_all] at hbag1
      intro t
      have ht := hbag1 t
      simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
      have hcard : (bag t).card =
          Fin.foldl w.N (fun c v => if v.1 ∈ w.bags.getD t.1 [] then c + 1 else c) 0 := by
        have hc := foldl_count (n := w.N) (fun v => decide (v.1 ∈ w.bags.getD t.1 []))
        simpa [bag] using hc.symm
      refine ⟨(hmembag p t).mpr ht.1, (hmembag r t).mpr ht.2.1, ?_⟩
      rw [hcard]
      exact ht.2.2
    · rw [foldl_all] at hbag2
      intro v
      have hv := hbag2 v
      rw [foldl_any] at hv
      obtain ⟨t, ht⟩ := hv
      simp only [decide_eq_true_eq] at ht
      exact ⟨t, (hmembag v t).mpr ht⟩
    · rw [foldl_all] at hbag3
      intro u v hv
      have h1 := (foldl_all _).mp (hbag3 u) v
      rw [hmemG] at hv
      simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h1
      rcases h1 with hnot | hex
      · exact absurd hv hnot
      · rw [foldl_any] at hex
        obtain ⟨t, ht⟩ := hex
        simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
        exact ⟨t, (hmembag u t).mpr ht.1, (hmembag v t).mpr ht.2⟩
    · rw [foldl_all] at hbag4
      intro v s t u hst htu hvs hvu
      have h1 := (foldl_all _).mp ((foldl_all _).mp ((foldl_all _).mp (hbag4 v) s) t) u
      rw [hmembag] at hvs hvu ⊢
      simp only [Bool.or_eq_true, Bool.not_eq_true'] at h1
      rcases h1 with hnot | hmem
      · exfalso
        have hst' : s.1 ≤ t.1 := Fin.le_iff_val_le_val.mp hst
        have htu' : t.1 ≤ u.1 := Fin.le_iff_val_le_val.mp htu
        have hcond : (decide (s.1 ≤ t.1) && decide (t.1 ≤ u.1) &&
            decide (v.1 ∈ w.bags.getD s.1 []) && decide (v.1 ∈ w.bags.getD u.1 [])) = true := by
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨⟨⟨hst', htu'⟩, hvs⟩, hvu⟩
        rw [hcond] at hnot
        exact Bool.noConfusion hnot
      · simp only [decide_eq_true_eq] at hmem
        exact hmem

def getWitness (k00 k01 k10 k11 rs : Bool) : Witness :=
  match k00, k01, k10, k11, rs with
  | false, false, false, false, false =>
    { N := 7, adj := [[1], [0, 2], [1, 3, 5], [2, 4, 6], [3], [2], [3]], side := [false, true, false, true, false, true, false], dist := [0, 1, 2, 3, 4, 3, 4], p := 0, r := 4, bags := [[0, 1, 4], [0, 1, 2, 4], [0, 2, 4, 5], [0, 2, 3, 4], [0, 3, 4, 6], [0, 3, 4]] }
  | false, false, false, false, true =>
    { N := 6, adj := [[1], [0, 2, 4], [1, 3, 5], [2], [1], [2]], side := [false, true, false, true, false, true], dist := [0, 1, 2, 3, 2, 3], p := 0, r := 3, bags := [[0, 1, 3], [0, 1, 3, 4], [0, 1, 2, 3], [0, 2, 3, 5], [0, 2, 3]] }
  | false, false, false, true, false =>
    { N := 7, adj := [[1], [0, 2], [1, 3, 5], [2, 4], [3], [2, 6], [5]], side := [false, true, false, true, false, true, false], dist := [0, 1, 2, 3, 4, 3, 4], p := 0, r := 4, bags := [[0, 1, 4], [0, 1, 2, 4], [0, 2, 4, 5], [0, 2, 4, 5, 6], [0, 2, 3, 4], [0, 3, 4]] }
  | false, false, false, true, true =>
    { N := 10, adj := [[1], [0, 2], [1, 3, 6], [2, 4, 8], [3, 5], [4], [2, 7], [6], [3, 9], [8]], side := [false, true, false, true, false, true, true, false, false, true], dist := [0, 1, 2, 3, 4, 5, 3, 4, 4, 5], p := 0, r := 5, bags := [[0, 1, 5], [0, 1, 2, 5], [0, 2, 5, 6], [0, 2, 5, 6, 7], [0, 2, 3, 5], [0, 3, 5, 8], [0, 3, 5, 8, 9], [0, 3, 4, 5], [0, 4, 5]] }
  | false, false, true, false, false =>
    { N := 6, adj := [[1], [0, 2], [1, 3], [2, 4, 5], [3], [3]], side := [false, true, false, true, false, false], dist := [0, 1, 2, 3, 4, 4], p := 0, r := 4, bags := [[0, 1, 4], [0, 1, 2, 4], [0, 2, 3, 4], [0, 3, 4, 5], [0, 3, 4]] }
  | false, false, true, false, true =>
    { N := 8, adj := [[1], [0, 2], [1, 3, 6], [2, 4], [3, 5], [4], [2, 7], [6]], side := [false, true, false, true, false, true, true, false], dist := [0, 1, 2, 3, 4, 5, 3, 4], p := 0, r := 5, bags := [[0, 1, 5], [0, 1, 2, 5], [0, 2, 5, 6], [0, 2, 5, 6, 7], [0, 2, 3, 5], [0, 3, 4, 5], [0, 4, 5]] }
  | false, false, true, true, false =>
    { N := 9, adj := [[1], [0, 2], [1, 3, 5], [2, 4, 7], [3], [2, 6], [5], [3, 8], [7]], side := [false, true, false, true, false, true, false, false, true], dist := [0, 1, 2, 3, 4, 3, 4, 4, 5], p := 0, r := 4, bags := [[0, 1, 4], [0, 1, 2, 4], [0, 2, 4, 5], [0, 2, 4, 5, 6], [0, 2, 3, 4], [0, 3, 4, 7], [0, 3, 4, 7, 8], [0, 3, 4]] }
  | false, false, true, true, true =>
    { N := 6, adj := [[1], [0, 2], [1, 3, 4], [2], [2, 5], [4]], side := [false, true, false, true, true, false], dist := [0, 1, 2, 3, 3, 4], p := 0, r := 3, bags := [[0, 1, 3], [0, 1, 2, 3], [0, 2, 3, 4], [0, 2, 3, 4, 5], [0, 2, 3]] }
  | false, true, false, false, false =>
    { N := 6, adj := [[1], [0, 2, 5], [1, 3], [2, 4], [3], [1]], side := [false, true, false, true, false, false], dist := [0, 1, 2, 3, 4, 2], p := 0, r := 4, bags := [[0, 1, 4], [0, 1, 4, 5], [0, 1, 2, 4], [0, 2, 3, 4], [0, 3, 4]] }
  | false, true, false, false, true =>
    { N := 8, adj := [[1], [0, 2], [1, 3], [2, 4, 6], [3, 5], [4], [3, 7], [6]], side := [false, true, false, true, false, true, false, true], dist := [0, 1, 2, 3, 4, 5, 4, 5], p := 0, r := 5, bags := [[0, 1, 5], [0, 1, 2, 5], [0, 2, 3, 5], [0, 3, 5, 6], [0, 3, 5, 6, 7], [0, 3, 4, 5], [0, 4, 5]] }
  | false, true, false, true, false =>
    { N := 9, adj := [[1], [0, 2, 5], [1, 3, 7], [2, 4], [3], [1, 6], [5], [2, 8], [7]], side := [false, true, false, true, false, false, true, true, false], dist := [0, 1, 2, 3, 4, 2, 3, 3, 4], p := 0, r := 4, bags := [[0, 1, 4], [0, 1, 4, 5], [0, 1, 4, 5, 6], [0, 1, 2, 4], [0, 2, 4, 7], [0, 2, 4, 7, 8], [0, 2, 3, 4], [0, 3, 4]] }
  | false, true, false, true, true =>
    { N := 6, adj := [[1], [0, 2, 4], [1, 3], [2], [1, 5], [4]], side := [false, true, false, true, false, true], dist := [0, 1, 2, 3, 2, 3], p := 0, r := 3, bags := [[0, 1, 3], [0, 1, 3, 4], [0, 1, 3, 4, 5], [0, 1, 2, 3], [0, 2, 3]] }
  | false, true, true, false, false =>
    { N := 8, adj := [[1], [0, 2, 3], [1, 6], [1, 4], [3, 5], [4, 6], [2, 5, 7], [6]], side := [false, true, false, false, true, false, true, false], dist := [0, 1, 2, 2, 3, 4, 3, 4], p := 0, r := 7, bags := [[0, 1, 7], [0, 1, 2, 6, 7], [0, 1, 3, 6, 7], [0, 1, 3, 4, 6, 7], [0, 1, 4, 5, 6, 7], [0, 6, 7]] }
  | false, true, true, false, true =>
    { N := 11, adj := [[1], [0, 2, 3], [1, 6], [1, 4], [3, 5], [4, 6], [2, 5, 7], [6, 8], [7, 9], [8, 10], [9]], side := [false, true, false, false, true, false, true, false, true, false, true], dist := [0, 1, 2, 2, 3, 4, 3, 4, 5, 6, 7], p := 0, r := 10, bags := [[0, 1, 10], [0, 1, 2, 6, 10], [0, 1, 3, 6, 10], [0, 1, 3, 4, 6, 10], [0, 1, 4, 5, 6, 10], [0, 6, 7, 10], [0, 7, 8, 10], [0, 8, 9, 10], [0, 9, 10]] }
  | false, true, true, true, false =>
    { N := 3, adj := [[1], [0, 2], [1]], side := [false, true, false], dist := [0, 1, 2], p := 0, r := 2, bags := [[0, 1, 2], [0, 1, 2]] }
  | false, true, true, true, true =>
    { N := 6, adj := [[1], [0, 2], [1, 3], [2, 4], [3, 5], [4]], side := [false, true, false, true, false, true], dist := [0, 1, 2, 3, 4, 5], p := 0, r := 5, bags := [[0, 1, 5], [0, 1, 2, 5], [0, 2, 3, 5], [0, 3, 4, 5], [0, 4, 5]] }
  | true, false, false, false, false =>
    { N := 4, adj := [[1], [0, 2, 3], [1], [1]], side := [false, true, false, false], dist := [0, 1, 2, 2], p := 0, r := 2, bags := [[0, 1, 2], [0, 1, 2, 3], [0, 1, 2]] }
  | true, false, false, false, true =>
    { N := 7, adj := [[1], [0, 2], [1, 3], [2, 4], [3, 5, 6], [4], [4]], side := [false, true, false, true, false, true, true], dist := [0, 1, 2, 3, 4, 5, 5], p := 0, r := 5, bags := [[0, 1, 5], [0, 1, 2, 5], [0, 2, 3, 5], [0, 3, 4, 5], [0, 4, 5, 6], [0, 4, 5]] }
  | true, false, false, true, false =>
    { N := 7, adj := [[1], [0, 2], [1, 3], [2, 4], [3, 5], [4, 6], [5]], side := [false, true, false, true, false, true, false], dist := [0, 1, 2, 3, 4, 5, 6], p := 0, r := 6, bags := [[0, 1, 6], [0, 1, 2, 6], [0, 2, 3, 6], [0, 3, 4, 6], [0, 4, 5, 6], [0, 5, 6]] }
  | true, false, false, true, true =>
    { N := 4, adj := [[1], [0, 2], [1, 3], [2]], side := [false, true, false, true], dist := [0, 1, 2, 3], p := 0, r := 3, bags := [[0, 1, 3], [0, 1, 2, 3], [0, 2, 3]] }
  | true, false, true, false, false =>
    { N := 7, adj := [[1], [0, 2, 5], [1, 3], [2, 4], [3], [1, 6], [5]], side := [false, true, false, true, false, false, true], dist := [0, 1, 2, 3, 4, 2, 3], p := 0, r := 4, bags := [[0, 1, 4], [0, 1, 4, 5], [0, 1, 4, 5, 6], [0, 1, 2, 4], [0, 2, 3, 4], [0, 3, 4]] }
  | true, false, true, false, true =>
    { N := 5, adj := [[1], [0, 2], [1, 3, 4], [2], [2]], side := [false, true, false, true, true], dist := [0, 1, 2, 3, 3], p := 0, r := 3, bags := [[0, 1, 3], [0, 1, 2, 3], [0, 2, 3, 4], [0, 2, 3]] }
  | true, false, true, true, false =>
    { N := 10, adj := [[1], [0, 2], [1, 3], [2, 4, 5], [3, 8], [3, 6], [5, 7], [6, 8], [4, 7, 9], [8]], side := [false, true, false, true, false, false, true, false, true, false], dist := [0, 1, 2, 3, 4, 4, 5, 6, 5, 6], p := 0, r := 9, bags := [[0, 1, 9], [0, 1, 2, 9], [0, 2, 3, 9], [0, 3, 4, 8, 9], [0, 3, 5, 8, 9], [0, 3, 5, 6, 8, 9], [0, 3, 6, 7, 8, 9], [0, 8, 9]] }
  | true, false, true, true, true =>
    { N := 9, adj := [[1], [0, 2, 3], [1, 6], [1, 4], [3, 5], [4, 6], [2, 5, 7], [6, 8], [7]], side := [false, true, false, false, true, false, true, false, true], dist := [0, 1, 2, 2, 3, 4, 3, 4, 5], p := 0, r := 8, bags := [[0, 1, 8], [0, 1, 2, 6, 8], [0, 1, 3, 6, 8], [0, 1, 3, 4, 6, 8], [0, 1, 4, 5, 6, 8], [0, 6, 7, 8], [0, 7, 8]] }
  | true, true, false, false, false =>
    { N := 7, adj := [[1], [0, 2], [1, 3], [2, 4, 5], [3], [3, 6], [5]], side := [false, true, false, true, false, false, true], dist := [0, 1, 2, 3, 4, 4, 5], p := 0, r := 4, bags := [[0, 1, 4], [0, 1, 2, 4], [0, 2, 3, 4], [0, 3, 4, 5], [0, 3, 4, 5, 6], [0, 3, 4]] }
  | true, true, false, false, true =>
    { N := 5, adj := [[1], [0, 2, 4], [1, 3], [2], [1]], side := [false, true, false, true, false], dist := [0, 1, 2, 3, 2], p := 0, r := 3, bags := [[0, 1, 3], [0, 1, 3, 4], [0, 1, 2, 3], [0, 2, 3]] }
  | true, true, false, true, false =>
    { N := 10, adj := [[1], [0, 2, 3], [1, 6], [1, 4], [3, 5], [4, 6], [2, 5, 7], [6, 8], [7, 9], [8]], side := [false, true, false, false, true, false, true, false, true, false], dist := [0, 1, 2, 2, 3, 4, 3, 4, 5, 6], p := 0, r := 9, bags := [[0, 1, 9], [0, 1, 2, 6, 9], [0, 1, 3, 6, 9], [0, 1, 3, 4, 6, 9], [0, 1, 4, 5, 6, 9], [0, 6, 7, 9], [0, 7, 8, 9], [0, 8, 9]] }
  | true, true, false, true, true =>
    { N := 9, adj := [[1], [0, 2], [1, 3, 4], [2, 7], [2, 5], [4, 6], [5, 7], [3, 6, 8], [7]], side := [false, true, false, true, true, false, true, false, true], dist := [0, 1, 2, 3, 3, 4, 5, 4, 5], p := 0, r := 8, bags := [[0, 1, 8], [0, 1, 2, 8], [0, 2, 3, 7, 8], [0, 2, 4, 7, 8], [0, 2, 4, 5, 7, 8], [0, 2, 5, 6, 7, 8], [0, 7, 8]] }
  | true, true, true, false, false =>
    { N := 5, adj := [[1], [0, 2], [1, 3], [2, 4], [3]], side := [false, true, false, true, false], dist := [0, 1, 2, 3, 4], p := 0, r := 4, bags := [[0, 1, 4], [0, 1, 2, 4], [0, 2, 3, 4], [0, 3, 4]] }
  | true, true, true, false, true =>
    { N := 2, adj := [[1], [0]], side := [false, true], dist := [0, 1], p := 0, r := 1, bags := [[0, 1]] }
  | true, true, true, true, false =>
    { N := 5, adj := [[1], [0, 2, 3], [1], [1, 4], [3]], side := [false, true, false, false, true], dist := [0, 1, 2, 2, 3], p := 0, r := 2, bags := [[0, 1, 2], [0, 1, 2, 3], [0, 1, 2, 3, 4], [0, 1, 2]] }
  | true, true, true, true, true =>
    { N := 8, adj := [[1], [0, 2, 4], [1, 3, 6], [2], [1, 5], [4], [2, 7], [6]], side := [false, true, false, true, false, true, true, false], dist := [0, 1, 2, 3, 2, 3, 3, 4], p := 0, r := 3, bags := [[0, 1, 3], [0, 1, 3, 4], [0, 1, 3, 4, 5], [0, 1, 2, 3], [0, 2, 3, 6], [0, 2, 3, 6, 7], [0, 2, 3]] }

theorem all_witnesses_ok : ∀ k00 k01 k10 k11 rs : Bool,
    checkWitness k00 k01 k10 k11 rs (getWitness k00 k01 k10 k11 rs) = true := by
  decide

theorem sum_card_even (N : Nat) (G : Fin N → Finset (Fin N))
    (hirr : ∀ v, v ∉ G v) (hsymm : ∀ u v, v ∈ G u ↔ u ∈ G v) :
    2 ∣ ∑ v : Fin N, (G v).card := by
  let E : Finset (Fin N × Fin N) := Finset.univ.filter (fun e => e.2 ∈ G e.1)
  have hE : ∑ v : Fin N, (G v).card = E.card := by
    have h1 : ∀ v : Fin N, (G v).card = ((Finset.univ : Finset (Fin N)).filter (fun u => u ∈ G v)).card := by
      intro v; simp
    simp only [h1, Finset.card_filter]
    rw [← Fintype.sum_prod_type (f := fun e : Fin N × Fin N => if e.2 ∈ G e.1 then 1 else 0)]
    rw [Finset.card_filter]
  let E1 := E.filter (fun e => e.1 < e.2)
  let E2 := E.filter (fun e => e.2 < e.1)
  have hdisj : Disjoint E1 E2 := by
    rw [Finset.disjoint_left]
    intro e he1 he2
    simp only [E1, E2, Finset.mem_filter] at he1 he2
    exact absurd (lt_trans he1.2 he2.2) (lt_irrefl _)
  have hunion : E = E1 ∪ E2 := by
    ext e
    simp only [E, E1, E2, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro he
      rcases lt_trichotomy e.1 e.2 with h | h | h
      · exact Or.inl ⟨he, h⟩
      · exfalso
        rw [h] at he
        exact hirr e.2 he
      · exact Or.inr ⟨he, h⟩
    · rintro (⟨he, _⟩ | ⟨he, _⟩) <;> exact he
  have hbij : E1.card = E2.card := by
    refine Finset.card_bij (fun e _ => (e.2, e.1)) ?_ ?_ ?_
    · intro e he
      simp only [E1, E2, E, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
      exact ⟨(hsymm e.1 e.2).mp he.1, he.2⟩
    · intro e1 _ e2 _ h
      exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
    · intro e he
      simp only [E2, E, Finset.mem_filter, Finset.mem_univ, true_and] at he
      refine ⟨(e.2, e.1), ?_, rfl⟩
      simp only [E1, E, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨(hsymm e.1 e.2).mp he.1, he.2⟩
  rw [hE, hunion, Finset.card_union_of_disjoint hdisj, hbij]
  exact ⟨E2.card, by omega⟩

theorem connected_deg_lb (N : Nat) (G : Fin N → Finset (Fin N)) (hN : 0 < N)
    (hsymm : ∀ u v, v ∈ G u ↔ u ∈ G v)
    (hconn : ∀ S : Finset (Fin N), S.Nonempty → S ≠ Finset.univ → ∃ u ∈ S, ∃ v ∈ G u, v ∉ S) :
    2 * (N - 1) ≤ ∑ v : Fin N, (G v).card := by
  have hstep : ∀ k, 1 ≤ k → k ≤ N →
      ∃ S : Finset (Fin N), S.card = k ∧ 2 * (k - 1) ≤ ∑ u ∈ S, (G u ∩ S).card := by
    intro k
    induction k with
    | zero => intro h1; omega
    | succ k ih =>
      intro _ hkN
      by_cases hk0 : k = 0
      · subst hk0
        refine ⟨{⟨0, hN⟩}, by simp, by simp⟩
      · have hk1 : 1 ≤ k := by omega
        obtain ⟨S, hScard, hSdeg⟩ := ih hk1 (by omega)
        have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
        have hSnu : S ≠ Finset.univ := by
          intro hu
          rw [hu, Finset.card_univ, Fintype.card_fin] at hScard
          omega
        obtain ⟨u, huS, v, hvGu, hvNS⟩ := hconn S hSne hSnu
        refine ⟨insert v S, by rw [Finset.card_insert_of_notMem hvNS, hScard], ?_⟩
        have huv : u ∈ G v ∩ insert v S := Finset.mem_inter.mpr ⟨(hsymm u v).mp hvGu, Finset.mem_insert_of_mem huS⟩
        have hvc : 1 ≤ (G v ∩ insert v S).card := Finset.card_pos.mpr ⟨u, huv⟩
        have hsum_step : ∑ x ∈ insert v S, (G x ∩ insert v S).card =
            (G v ∩ insert v S).card + ∑ x ∈ S, (G x ∩ insert v S).card :=
          Finset.sum_insert hvNS
        have hS_inc : ∑ x ∈ S, (G x ∩ S).card + 1 ≤ ∑ x ∈ S, (G x ∩ insert v S).card := by
          rw [← Finset.add_sum_erase S (fun x => (G x ∩ S).card) huS]
          rw [← Finset.add_sum_erase S (fun x => (G x ∩ insert v S).card) huS]
          have hsub : ∀ x ∈ S.erase u, (G x ∩ S).card ≤ (G x ∩ insert v S).card := by
            intro x _
            exact Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl _) (Finset.subset_insert v S))
          have hrem : ∑ x ∈ S.erase u, (G x ∩ S).card ≤ ∑ x ∈ S.erase u, (G x ∩ insert v S).card :=
            Finset.sum_le_sum hsub
          have hu_strict : G u ∩ S ⊂ G u ∩ insert v S := by
            rw [Finset.ssubset_iff_of_subset (Finset.inter_subset_inter (Finset.Subset.refl _) (Finset.subset_insert v S))]
            exact ⟨v, Finset.mem_inter.mpr ⟨hvGu, Finset.mem_insert_self v S⟩,
              fun hmem => hvNS (Finset.mem_inter.mp hmem).2⟩
          have hu_card : (G u ∩ S).card + 1 ≤ (G u ∩ insert v S).card :=
            Finset.card_lt_card hu_strict
          omega
        omega
  obtain ⟨S, hScard, hSdeg⟩ := hstep N hN (le_refl N)
  have hSu : S = Finset.univ := Finset.eq_univ_of_card S (by simpa using hScard)
  subst hSu
  simpa using hSdeg

def isSimpleGraph {V : Type} [Fintype V] (G : V → Finset V) : Prop :=
  (∀ v, v ∉ G v) ∧ (∀ u v, v ∈ G u ↔ u ∈ G v) ∧
  ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ → ∃ u ∈ S, ∃ v ∈ G u, v ∉ S

def isIndep {V : Type} (G : V → Finset V) (I : Finset V) : Prop :=
  ∀ u ∈ I, ∀ v ∈ G u, v ∉ I

noncomputable def wsig {V : Type} [Fintype V] [DecidableEq V]
    (G : V → Finset V) (w : V → Bool → Bool) (p r : V) (a b : Bool) : Bool :=
  letI : ∀ q : Prop, Decidable q := Classical.propDecidable
  decide (((Finset.univ : Finset (Finset V)).filter (fun I =>
    isIndep G I ∧ (∀ v : V, w v (decide (v ∈ I)) = true) ∧
    decide (p ∈ I) = a ∧ decide (r ∈ I) = b)).card % 2 = 1)

def matMul (A B : Bool → Bool → Bool) (a b : Bool) : Bool :=
  xor (A a false && B false b) (A a true && B true b)

def diagMat (f : Bool → Bool) (a b : Bool) : Bool :=
  if a = b then f a else false

def HMat (a b : Bool) : Bool := !(a && b)

def invM (K : Bool → Bool → Bool) : Bool :=
  xor (K false false && K true true) (K false true && K true false)

def pathFormM (K : Bool → Bool → Bool) : Prop :=
  K = (fun a b => decide (a = b)) ∨ K = (fun a b => !(a && b)) ∨ K = (fun a b => a || b)

theorem invM_diag_H_mul (f : Bool → Bool) (M : Bool → Bool → Bool)
    (h : invM (matMul (diagMat f) (matMul HMat M)) = true) :
    f false = true ∧ f true = true ∧ invM M = true := by
  have hff := f false
  have hft := f true
  have hm00 := M false false
  have hm01 := M false true
  have hm10 := M true false
  have hm11 := M true true
  cases hf0 : f false <;> cases hf1 : f true <;>
    cases hm0 : M false false <;> cases hm1 : M false true <;>
    cases hm2 : M true false <;> cases hm3 : M true true <;>
    simp_all [invM, matMul, diagMat, HMat]

theorem pathFormM_H_mul (M : Bool → Bool → Bool) (h : pathFormM M) :
    pathFormM (matMul HMat M) := by
  rcases h with rfl | rfl | rfl
  · right; left; funext a b; cases a <;> cases b <;> decide
  · right; right; funext a b; cases a <;> cases b <;> decide
  · left; funext a b; cases a <;> cases b <;> decide

theorem diag_true_mul (M : Bool → Bool → Bool) :
    matMul (diagMat (fun _ => true)) M = M := by
  funext a b; cases a <;> cases b <;> simp [matMul, diagMat]

theorem edge_base_pathForm (f g : Bool → Bool)
    (h : invM (fun a b => f a && g b && !(a && b)) = true) :
    pathFormM (fun a b => f a && g b && !(a && b)) := by
  cases hf0 : f false <;> cases hf1 : f true <;>
    cases hg0 : g false <;> cases hg1 : g true
  all_goals
    try (exfalso; simp [invM, hf0, hf1, hg0, hg1] at h; done)
  right; left
  funext a b; cases a <;> cases b <;> simp [hf0, hf1, hg0, hg1]

def delG {V : Type} [DecidableEq V] (G : V → Finset V) (v : V)
    (x : {y : V // y ≠ v}) : Finset {y : V // y ≠ v} :=
  (G x.1).subtype (· ≠ v)

theorem delG_simple {V : Type} [Fintype V] [DecidableEq V] (G : V → Finset V) (v u : V)
    (hG : isSimpleGraph G) (hGu : G v = {u}) :
    isSimpleGraph (delG G v) := by
  rcases hG with ⟨hirr, hsymm, hconn⟩
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    simp only [delG, Finset.mem_subtype] at hx
    exact hirr x.1 hx
  · intro x y
    simp only [delG, Finset.mem_subtype]
    exact hsymm x.1 y.1
  · intro S' hS'ne hS'nu
    let emb : {y : V // y ≠ v} ↪ V := ⟨Subtype.val, Subtype.coe_injective⟩
    let S : Finset V := S'.map emb
    have hmemS : ∀ {x : V} (hx : x ≠ v), x ∈ S ↔ ⟨x, hx⟩ ∈ S' := by
      intro x hx
      simp only [S, Finset.mem_map, emb, Function.Embedding.coeFn_mk]
      exact ⟨fun ⟨z, hz, hzx⟩ => by subst hzx; exact hz, fun h => ⟨⟨x, hx⟩, h, rfl⟩⟩
    have hSne : S.Nonempty := hS'ne.map (f := emb)
    by_cases huS : u ∈ S
    · let S1 : Finset V := insert v S
      have hS1ne : S1.Nonempty := ⟨v, Finset.mem_insert_self v S⟩
      have hS1nu : S1 ≠ Finset.univ := by
        intro hu1
        apply hS'nu
        ext y
        simp only [Finset.mem_univ, iff_true]
        have hy1 : y.1 ∈ S1 := by rw [hu1]; exact Finset.mem_univ _
        rcases Finset.mem_insert.mp hy1 with hyv | hyS
        · exact absurd hyv y.2
        · exact (hmemS y.2).mp hyS
      obtain ⟨x, hxS1, y, hyGx, hyNS1⟩ := hconn S1 hS1ne hS1nu
      rcases Finset.mem_insert.mp hxS1 with rfl | hxS
      · exfalso
        rw [hGu, Finset.mem_singleton] at hyGx
        rw [hyGx] at hyNS1
        exact hyNS1 (Finset.mem_insert_of_mem huS)
      · have hxne : x ≠ v := by
          intro hxv
          rw [hxv] at hxS
          simp only [S, Finset.mem_map, emb, Function.Embedding.coeFn_mk] at hxS
          obtain ⟨z, _, hzv⟩ := hxS
          exact z.2 hzv
        have hyne : y ≠ v := fun hyv => hyNS1 (by rw [hyv]; exact Finset.mem_insert_self v S)
        have hyNS : y ∉ S := fun hyS => hyNS1 (Finset.mem_insert_of_mem hyS)
        refine ⟨⟨x, hxne⟩, (hmemS hxne).mp hxS, ⟨y, hyne⟩, ?_, ?_⟩
        · simpa [delG] using hyGx
        · intro hyS'; exact hyNS ((hmemS hyne).mpr hyS')
    · have hSnu : S ≠ Finset.univ := by
        intro hu
        have hvS : v ∈ S := by rw [hu]; exact Finset.mem_univ _
        simp only [S, Finset.mem_map, emb, Function.Embedding.coeFn_mk] at hvS
        obtain ⟨z, _, hzv⟩ := hvS
        exact z.2 hzv
      obtain ⟨x, hxS, y, hyGx, hyNS⟩ := hconn S hSne hSnu
      have hxne : x ≠ v := by
          intro hxv
          rw [hxv] at hxS
          simp only [S, Finset.mem_map, emb, Function.Embedding.coeFn_mk] at hxS
          obtain ⟨z, _, hzv⟩ := hxS
          exact z.2 hzv
      have hyne : y ≠ v := by
        intro hyv
        rw [hyv] at hyGx
        have hxv : x ∈ G v := (hsymm x v).mp hyGx
        rw [hGu, Finset.mem_singleton] at hxv
        rw [hxv] at hxS
        exact huS hxS
      refine ⟨⟨x, hxne⟩, (hmemS hxne).mp hxS, ⟨y, hyne⟩, ?_, ?_⟩
      · simpa [delG] using hyGx
      · intro hyS'; exact hyNS ((hmemS hyne).mpr hyS')

theorem delG_sum_card {V : Type} [Fintype V] [DecidableEq V] (G : V → Finset V) (v u : V)
    (hirr : ∀ x, x ∉ G x) (hsymm : ∀ x y, y ∈ G x ↔ x ∈ G y) (hGu : G v = {u}) :
    ∑ x : {y : V // y ≠ v}, (delG G v x).card + 2 = ∑ x : V, (G x).card := by
  have huv : u ≠ v := by
    intro h; subst h
    exact hirr u (by rw [hGu]; exact Finset.mem_singleton_self u)
  let u' : {y : V // y ≠ v} := ⟨u, huv⟩
  have hsub_card : ∀ x : {y : V // y ≠ v},
      (delG G v x).card = (G x.1).card - (if x = u' then 1 else 0) := by
    intro x
    have h1 : (delG G v x).card = ((G x.1).erase v).card := by
      unfold delG
      rw [Finset.card_subtype]
      congr 1
      ext y
      simp only [Finset.mem_filter, Finset.mem_erase, ne_eq]
      tauto
    rw [h1]
    by_cases hxu : x = u'
    · subst hxu
      have hvu : v ∈ G u := (hsymm v u).mp (by rw [hGu]; exact Finset.mem_singleton_self u)
      dsimp only [u']
      simp only [ite_true]
      exact Finset.card_erase_of_mem hvu
    · have hvx : v ∉ G x.1 := by
        intro hmem
        have hxv : x.1 ∈ G v := (hsymm x.1 v).mp hmem
        rw [hGu, Finset.mem_singleton] at hxv
        exact hxu (Subtype.ext hxv)
      simp only [hxu, ite_false, Finset.erase_eq_of_notMem hvx, Nat.sub_zero]
  have hsum_sub : ∑ x : {y : V // y ≠ v}, (delG G v x).card + 1 =
      ∑ x : {y : V // y ≠ v}, (G x.1).card := by
    have hle : ∀ x : {y : V // y ≠ v}, (if x = u' then 1 else 0) ≤ (G x.1).card := by
      intro x
      by_cases hxu : x = u'
      · subst hxu
        have hvu : v ∈ G u := (hsymm v u).mp (by rw [hGu]; exact Finset.mem_singleton_self u)
        simp only [ite_true]
        exact Finset.card_pos.mpr ⟨v, hvu⟩
      · simp [hxu]
    have hadd : ∑ x : {y : V // y ≠ v}, ((delG G v x).card + (if x = u' then 1 else 0)) =
        ∑ x : {y : V // y ≠ v}, (G x.1).card := by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [hsub_card x]
      exact Nat.sub_add_cancel (hle x)
    rw [Finset.sum_add_distrib] at hadd
    simpa using hadd
  have hsplit : ∑ x : V, (G x).card =
      (G v).card + ∑ x : {y : V // y ≠ v}, (G x.1).card := by
    have h1 := Fintype.sum_eq_add_sum_subtype_ne (fun x => (G x).card) v
    exact h1
  rw [hsplit, hGu, Finset.card_singleton, ← hsum_sub]
  omega

theorem wsig_peel_leaf {V : Type} [Fintype V] [DecidableEq V]
    (G : V → Finset V) (w : V → Bool → Bool) (p r v u : V)
    (hirr : ∀ x, x ∉ G x) (hsymm : ∀ x y, y ∈ G x ↔ x ∈ G y)
    (hGu : G v = {u}) (hvp : v ≠ p) (hvr : v ≠ r) :
    let u' : {y : V // y ≠ v} := ⟨u, fun h => hirr v (by rw [hGu, h]; exact Finset.mem_singleton_self v)⟩
    let w' : {y : V // y ≠ v} → Bool → Bool := fun x c =>
      if x = u' then
        (if c then (w x.1 true && w v false) else (w x.1 false && xor (w v false) (w v true)))
      else w x.1 c
    wsig G w p r = wsig (delG G v) w' ⟨p, hvp.symm⟩ ⟨r, hvr.symm⟩ := by
  intro u' w'
  funext a b
  letI : ∀ q : Prop, Decidable q := Classical.propDecidable
  unfold wsig
  let S := (Finset.univ : Finset (Finset V)).filter (fun I =>
    isIndep G I ∧ (∀ x : V, w x (decide (x ∈ I)) = true) ∧
    decide (p ∈ I) = a ∧ decide (r ∈ I) = b)
  let S' := (Finset.univ : Finset (Finset {y : V // y ≠ v})).filter (fun I' =>
    isIndep (delG G v) I' ∧ (∀ x : {y : V // y ≠ v}, w' x (decide (x ∈ I')) = true) ∧
    decide (⟨p, hvp.symm⟩ ∈ I') = a ∧ decide (⟨r, hvr.symm⟩ ∈ I') = b)
  have hS_mod : S.card % 2 =
      (∑ I' : Finset {y : V // y ≠ v},
        (S.filter (fun I => I.subtype (· ≠ v) = I')).card % 2) % 2 := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun I : Finset V => I.subtype (· ≠ v))
      (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
    exact Finset.sum_nat_mod _ 2 _
  have hS'_mod : S'.card % 2 =
      (∑ I' : Finset {y : V // y ≠ v}, (if I' ∈ S' then 1 else 0) % 2) % 2 := by
    have hc : S'.card = ∑ I' : Finset {y : V // y ≠ v}, (if I' ∈ S' then 1 else 0) := by
      rw [← Finset.card_filter]
      congr 1
      ext x
      simp
    rw [hc]
    exact Finset.sum_nat_mod _ 2 _
  have hfib : ∀ I' : Finset {y : V // y ≠ v},
      (S.filter (fun I => I.subtype (· ≠ v) = I')).card % 2 =
      (if I' ∈ S' then 1 else 0) % 2 := by
    intro I'
    let emb : {y : V // y ≠ v} ↪ V := ⟨Subtype.val, Subtype.coe_injective⟩
    let I0 : Finset V := I'.map emb
    let I1 : Finset V := insert v I0
    have hmem0 : ∀ {x : V} (hx : x ≠ v), x ∈ I0 ↔ ⟨x, hx⟩ ∈ I' := by
      intro x hx
      simp only [I0, Finset.mem_map, emb, Function.Embedding.coeFn_mk]
      exact ⟨fun ⟨z, hz, hzx⟩ => by subst hzx; exact hz, fun h => ⟨⟨x, hx⟩, h, rfl⟩⟩
    have hvNI0 : v ∉ I0 := by
      simp only [I0, Finset.mem_map, emb, Function.Embedding.coeFn_mk]
      rintro ⟨z, _, hzv⟩
      exact z.2 hzv
    have hmem1 : ∀ {x : V} (hx : x ≠ v), x ∈ I1 ↔ ⟨x, hx⟩ ∈ I' := by
      intro x hx
      simp only [I1, Finset.mem_insert, hx, false_or]
      exact hmem0 hx
    have hvI1 : v ∈ I1 := Finset.mem_insert_self v I0
    have hI0_sub : I0.subtype (· ≠ v) = I' := by
      ext z; simp only [Finset.mem_subtype]; exact hmem0 z.2
    have hI1_sub : I1.subtype (· ≠ v) = I' := by
      ext z; simp only [Finset.mem_subtype]; exact hmem1 z.2
    have hI01 : ∀ I : Finset V, I.subtype (· ≠ v) = I' ↔ I = I0 ∨ I = I1 := by
      intro I
      constructor
      · intro hsub
        by_cases hvI : v ∈ I
        · right
          ext x
          by_cases hxv : x = v
          · subst hxv; simp only [hvI, hvI1]
          · rw [hmem1 hxv, ← hsub]; simp only [Finset.mem_subtype]
        · left
          ext x
          by_cases hxv : x = v
          · subst hxv; simp only [hvI, hvNI0]
          · rw [hmem0 hxv, ← hsub]; simp only [Finset.mem_subtype]
      · rintro (rfl | rfl)
        · exact hI0_sub
        · exact hI1_sub
    have hne01 : I0 ≠ I1 := by
      intro h
      have : v ∈ I0 := by rw [h]; exact hvI1
      exact hvNI0 this
    have hfilt_card : (S.filter (fun I => I.subtype (· ≠ v) = I')).card =
        (if I0 ∈ S then 1 else 0) + (if I1 ∈ S then 1 else 0) := by
      have hset : S.filter (fun I => I.subtype (· ≠ v) = I') =
          (if I0 ∈ S then {I0} else ∅) ∪ (if I1 ∈ S then {I1} else ∅) := by
        ext I
        simp only [Finset.mem_filter, Finset.mem_union]
        rw [hI01 I]
        by_cases h0 : I0 ∈ S <;> by_cases h1 : I1 ∈ S
        · simp [h0, h1]; rintro (rfl | rfl) <;> assumption
        · simp [h0, h1]; constructor
          · rintro ⟨hI, rfl | rfl⟩; rfl; exact absurd hI h1
          · rintro rfl; exact ⟨h0, Or.inl rfl⟩
        · simp [h0, h1]; constructor
          · rintro ⟨hI, rfl | rfl⟩; exact absurd hI h0; rfl
          · rintro rfl; exact ⟨h1, Or.inr rfl⟩
        · simp [h0, h1]; intro hI; exact ⟨fun h => h0 (h ▸ hI), fun h => h1 (h ▸ hI)⟩
      rw [hset, Finset.card_union_of_disjoint]
      · by_cases h0 : I0 ∈ S <;> by_cases h1 : I1 ∈ S <;> simp [h0, h1]
      · by_cases h0 : I0 ∈ S <;> by_cases h1 : I1 ∈ S <;> simp [h0, h1, hne01]
    rw [hfilt_card]
    have hpr0 : (decide (p ∈ I0) = a ∧ decide (r ∈ I0) = b) ↔
        (decide (⟨p, hvp.symm⟩ ∈ I') = a ∧ decide (⟨r, hvr.symm⟩ ∈ I') = b) := by
      have hp0 := hmem0 hvp.symm
      have hr0 := hmem0 hvr.symm
      have hp_dec : @decide (p ∈ I0) (Classical.propDecidable _) =
          @decide (⟨p, hvp.symm⟩ ∈ I') (Classical.propDecidable _) := by
        apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]; exact hp0
      have hr_dec : @decide (r ∈ I0) (Classical.propDecidable _) =
          @decide (⟨r, hvr.symm⟩ ∈ I') (Classical.propDecidable _) := by
        apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]; exact hr0
      rw [hp_dec, hr_dec]
    have hpr1 : (decide (p ∈ I1) = a ∧ decide (r ∈ I1) = b) ↔
        (decide (⟨p, hvp.symm⟩ ∈ I') = a ∧ decide (⟨r, hvr.symm⟩ ∈ I') = b) := by
      have hp1 := hmem1 hvp.symm
      have hr1 := hmem1 hvr.symm
      have hp_dec : @decide (p ∈ I1) (Classical.propDecidable _) =
          @decide (⟨p, hvp.symm⟩ ∈ I') (Classical.propDecidable _) := by
        apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]; exact hp1
      have hr_dec : @decide (r ∈ I1) (Classical.propDecidable _) =
          @decide (⟨r, hvr.symm⟩ ∈ I') (Classical.propDecidable _) := by
        apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]; exact hr1
      rw [hp_dec, hr_dec]
    have his0 : isIndep G I0 ↔ isIndep (delG G v) I' := by
      constructor
      · intro his x hx y hy hyI
        have hx0 : x.1 ∈ I0 := (hmem0 x.2).mpr hx
        have hy0 : y.1 ∈ I0 := (hmem0 y.2).mpr hyI
        have hyG : y.1 ∈ G x.1 := by simpa [delG] using hy
        exact his x.1 hx0 y.1 hyG hy0
      · intro his x hx y hy hyI
        have hxv : x ≠ v := fun h => hvNI0 (by rwa [← h])
        have hyv : y ≠ v := fun h => hvNI0 (by rwa [← h])
        exact his ⟨x, hxv⟩ ((hmem0 hxv).mp hx) ⟨y, hyv⟩ (by simpa [delG] using hy) ((hmem0 hyv).mp hyI)
    have his1 : isIndep G I1 ↔ (isIndep (delG G v) I' ∧ u' ∉ I') := by
      constructor
      · intro his
        refine ⟨?_, ?_⟩
        · apply his0.mp
          intro x hx y hy hyI
          exact his x (Finset.mem_insert_of_mem hx) y hy (Finset.mem_insert_of_mem hyI)
        · intro huI
          have hu0 : u ∈ I0 := (hmem0 u'.2).mpr huI
          have huG : u ∈ G v := by rw [hGu]; exact Finset.mem_singleton_self u
          exact his v hvI1 u huG (Finset.mem_insert_of_mem hu0)
      · rintro ⟨his', huNI⟩ x hx y hy hyI
        have his0' := his0.mpr his'
        rcases Finset.mem_insert.mp hx with hxv | hx0
        · rw [hxv, hGu, Finset.mem_singleton] at hy
          rw [hy] at hyI
          rcases Finset.mem_insert.mp hyI with huv | hu0
          · exact u'.2 huv
          · exact huNI ((hmem0 u'.2).mp hu0)
        · rcases Finset.mem_insert.mp hyI with hyv | hy0
          · have hxv : x ∈ G v := (hsymm x v).mp (by rwa [← hyv])
            rw [hGu, Finset.mem_singleton] at hxv
            rw [hxv] at hx0
            exact huNI ((hmem0 u'.2).mp hx0)
          · exact his0' x hx0 y hy hy0
    have hw_rest : (∀ x : V, x ≠ v → x ≠ u → w x (decide (x ∈ I0)) = true) ↔
        (∀ x : {y : V // y ≠ v}, x ≠ u' → w' x (decide (x ∈ I')) = true) := by
      constructor
      · intro h x hx
        have hxu : x.1 ≠ u := fun heq => hx (Subtype.ext heq)
        have h1 := h x.1 x.2 hxu
        simp only [w', hx, ite_false]
        have heq_dec : @decide (x.1 ∈ I0) (Classical.propDecidable _) =
            @decide (x ∈ I') (Classical.propDecidable _) := by
          apply Bool.eq_iff_iff.mpr
          simp only [decide_eq_true_eq]
          exact hmem0 x.2
        rw [← heq_dec]
        exact h1
      · intro h x hxv hxu
        have hx' : (⟨x, hxv⟩ : {y : V // y ≠ v}) ≠ u' := fun heq => hxu (congrArg Subtype.val heq)
        have h1 := h ⟨x, hxv⟩ hx'
        simp only [w', hx', ite_false] at h1
        have heq_dec : @decide (x ∈ I0) (Classical.propDecidable _) =
            @decide (⟨x, hxv⟩ ∈ I') (Classical.propDecidable _) := by
          apply Bool.eq_iff_iff.mpr
          simp only [decide_eq_true_eq]
          exact hmem0 hxv
        rw [heq_dec]
        exact h1
    have hw_rest1 : (∀ x : V, x ≠ v → x ≠ u → w x (decide (x ∈ I1)) = true) ↔
        (∀ x : {y : V // y ≠ v}, x ≠ u' → w' x (decide (x ∈ I')) = true) := by
      rw [← hw_rest]
      refine forall_congr' (fun x => forall_congr' (fun hx => forall_congr' (fun _ => ?_)))
      have heq_dec : @decide (x ∈ I1) (Classical.propDecidable _) =
          @decide (x ∈ I0) (Classical.propDecidable _) := by
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq, hmem1 hx, hmem0 hx]
      rw [heq_dec]
    by_cases hbase : isIndep (delG G v) I' ∧
        (∀ x : {y : V // y ≠ v}, x ≠ u' → w' x (decide (x ∈ I')) = true) ∧
        decide (⟨p, hvp.symm⟩ ∈ I') = a ∧ decide (⟨r, hvr.symm⟩ ∈ I') = b
    · have hdec_u0 : @decide (u ∈ I0) (Classical.propDecidable _) =
          @decide (u' ∈ I') (Classical.propDecidable _) := by
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        exact hmem0 u'.2
      have hdec_v0 : @decide (v ∈ I0) (Classical.propDecidable _) = false := by
        simp only [decide_eq_false_iff_not]; exact hvNI0
      have hdec_v1 : @decide (v ∈ I1) (Classical.propDecidable _) = true := by
        simp only [decide_eq_true_eq]; exact hvI1
      have hdec_u1 : @decide (u ∈ I1) (Classical.propDecidable _) =
          @decide (u' ∈ I') (Classical.propDecidable _) := by
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        exact hmem1 u'.2
      have h0_iff : I0 ∈ S ↔ (w v false = true ∧ w u (decide (u' ∈ I')) = true) := by
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [his0, hpr0]
        constructor
        · rintro ⟨_, hw, _⟩
          have hwv := hw v; rw [hdec_v0] at hwv
          have hwu := hw u; rw [hdec_u0] at hwu
          exact ⟨hwv, hwu⟩
        · rintro ⟨hwv, hwu⟩
          refine ⟨hbase.1, ?_, hbase.2.2⟩
          intro x
          by_cases hxv : x = v
          · subst hxv; rw [hdec_v0]; exact hwv
          · by_cases hxu : x = u
            · subst hxu; rw [hdec_u0]; exact hwu
            · exact (hw_rest.mpr hbase.2.1) x hxv hxu
      have h1_iff : I1 ∈ S ↔ (u' ∉ I' ∧ w v true = true ∧ w u false = true) := by
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [his1, hpr1]
        constructor
        · rintro ⟨⟨_, huNI⟩, hw, _⟩
          have hwv := hw v; rw [hdec_v1] at hwv
          have hwu := hw u
          have hduf : @decide (u ∈ I1) (Classical.propDecidable _) = false := by
            rw [hdec_u1]; simp only [decide_eq_false_iff_not]; exact huNI
          rw [hduf] at hwu
          exact ⟨huNI, hwv, hwu⟩
        · rintro ⟨huNI, hwv, hwu⟩
          refine ⟨⟨hbase.1, huNI⟩, ?_, hbase.2.2⟩
          intro x
          by_cases hxv : x = v
          · subst hxv; rw [hdec_v1]; exact hwv
          · by_cases hxu : x = u
            · rw [hxu]
              have hduf : @decide (u ∈ I1) (Classical.propDecidable _) = false := by
                rw [hdec_u1]; simp only [decide_eq_false_iff_not]; exact huNI
              rw [hduf]; exact hwu
            · exact (hw_rest1.mpr hbase.2.1) x hxv hxu
      have hS'_iff : I' ∈ S' ↔ w' u' (decide (u' ∈ I')) = true := by
        simp only [S', Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨_, hw, _⟩; exact hw u'
        · intro hwu'
          refine ⟨hbase.1, ?_, hbase.2.2⟩
          intro x
          by_cases hxu : x = u'
          · subst hxu; exact hwu'
          · exact hbase.2.1 x hxu
      rw [h0_iff, h1_iff, hS'_iff]
      by_cases hu' : u' ∈ I'
      · simp only [hu', not_true_eq_false, false_and, ite_false, Nat.add_zero, decide_true]
        have hw'u : w' u' true = (w u true && w v false) := by simp [w', u']
        rw [hw'u]
        cases w v false <;> cases w u true <;> simp
      · simp only [hu', not_false_eq_true, true_and, decide_false]
        have hw'u : w' u' false = (w u false && xor (w v false) (w v true)) := by simp [w', u']
        rw [hw'u]
        cases w v false <;> cases w v true <;> cases w u false <;> simp
    · have h0_not : I0 ∉ S := by
        intro hmem
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
        apply hbase
        refine ⟨his0.mp hmem.1, ?_, hpr0.mp hmem.2.2⟩
        exact hw_rest.mp (fun x _ _ => hmem.2.1 x)
      have h1_not : I1 ∉ S := by
        intro hmem
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
        apply hbase
        refine ⟨(his1.mp hmem.1).1, ?_, hpr1.mp hmem.2.2⟩
        exact hw_rest1.mp (fun x _ _ => hmem.2.1 x)
      have hS'_not : I' ∉ S' := by
        intro hmem
        simp only [S', Finset.mem_filter, Finset.mem_univ, true_and] at hmem
        apply hbase
        exact ⟨hmem.1, fun x _ => hmem.2.1 x, hmem.2.2⟩
      simp [h0_not, h1_not, hS'_not]
  have hcard_eq : S.card % 2 = S'.card % 2 := by
    rw [hS_mod, hS'_mod]
    exact congrArg (· % 2) (Finset.sum_congr rfl (fun I' _ => hfib I'))
  congr 1
  congr! 1
  convert hcard_eq

theorem wsig_peel_port {V : Type} [Fintype V] [DecidableEq V]
    (G : V → Finset V) (w : V → Bool → Bool) (p q r : V)
    (hirr : ∀ x, x ∉ G x) (hsymm : ∀ x y, y ∈ G x ↔ x ∈ G y)
    (hGq : G p = {q}) (hpr : p ≠ r) (_hqr : q ≠ r) :
    let q' : {y : V // y ≠ p} := ⟨q, fun h => hirr p (by rw [hGq, h]; exact Finset.mem_singleton_self p)⟩
    let r' : {y : V // y ≠ p} := ⟨r, hpr.symm⟩
    let w' : {y : V // y ≠ p} → Bool → Bool := fun x => w x.1
    wsig G w p r = matMul (diagMat (w p)) (matMul HMat (wsig (delG G p) w' q' r')) := by
  intro q' r' w'
  funext a b
  letI : ∀ s : Prop, Decidable s := Classical.propDecidable
  unfold wsig
  let S := (Finset.univ : Finset (Finset V)).filter (fun I =>
    isIndep G I ∧ (∀ x : V, w x (decide (x ∈ I)) = true) ∧
    decide (p ∈ I) = a ∧ decide (r ∈ I) = b)
  let Sf := (Finset.univ : Finset (Finset {y : V // y ≠ p})).filter (fun I' =>
    isIndep (delG G p) I' ∧ (∀ x : {y : V // y ≠ p}, w' x (decide (x ∈ I')) = true) ∧
    decide (q' ∈ I') = false ∧ decide (r' ∈ I') = b)
  let St := (Finset.univ : Finset (Finset {y : V // y ≠ p})).filter (fun I' =>
    isIndep (delG G p) I' ∧ (∀ x : {y : V // y ≠ p}, w' x (decide (x ∈ I')) = true) ∧
    decide (q' ∈ I') = true ∧ decide (r' ∈ I') = b)
  have hdisj : Disjoint Sf St := by
    rw [Finset.disjoint_left]
    intro I' h0 h1
    simp only [Sf, St, Finset.mem_filter, Finset.mem_univ, true_and] at h0 h1
    rw [h0.2.2.1] at h1
    exact Bool.noConfusion h1.2.2.1
  let emb : {y : V // y ≠ p} ↪ V := ⟨Subtype.val, Subtype.coe_injective⟩
  have hmem_map : ∀ (I' : Finset {y : V // y ≠ p}) {x : V} (hx : x ≠ p),
      x ∈ I'.map emb ↔ ⟨x, hx⟩ ∈ I' := by
    intro I' x hx
    simp only [Finset.mem_map, emb, Function.Embedding.coeFn_mk]
    exact ⟨fun ⟨z, hz, hzx⟩ => by subst hzx; exact hz, fun h => ⟨⟨x, hx⟩, h, rfl⟩⟩
  have his_map : ∀ (I' : Finset {y : V // y ≠ p}),
      isIndep G (I'.map emb) ↔ isIndep (delG G p) I' := by
    intro I'
    constructor
    · intro his x hx y hy hyI
      exact his x.1 ((hmem_map I' x.2).mpr hx) y.1 (by simpa [delG] using hy) ((hmem_map I' y.2).mpr hyI)
    · intro his x hx y hy hyI
      have hxp : x ≠ p := by
        intro h; subst h
        simp only [Finset.mem_map, emb, Function.Embedding.coeFn_mk] at hx
        obtain ⟨z, _, hzp⟩ := hx; exact z.2 hzp
      have hyp : y ≠ p := by
        intro h; subst h
        simp only [Finset.mem_map, emb, Function.Embedding.coeFn_mk] at hyI
        obtain ⟨z, _, hzp⟩ := hyI; exact z.2 hzp
      exact his ⟨x, hxp⟩ ((hmem_map I' hxp).mp hx) ⟨y, hyp⟩ (by simpa [delG] using hy) ((hmem_map I' hyp).mp hyI)
  have hcard_eq : S.card =
      if w p a = false then 0 else if a = false then (Sf ∪ St).card else Sf.card := by
    cases hwp : w p a
    · simp only [ite_true]
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro I hI
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hI
      have hpa := hI.2.2.1
      have hwx := hI.2.1 p
      rw [hpa, hwp] at hwx
      exact Bool.noConfusion hwx
    · simp only [Bool.true_eq_false, ite_false]
      cases ha : a
      · simp only [ite_true]
        refine Finset.card_bij (fun I _ => I.subtype (· ≠ p)) ?_ ?_ ?_
        · intro I hI
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hI
          have hpNI : p ∉ I := by
            have := hI.2.2.1
            rw [ha] at this
            simpa using this
          have his' : isIndep (delG G p) (I.subtype (· ≠ p)) := by
            intro x hx y hy hyI
            simp only [Finset.mem_subtype, delG] at hx hy hyI
            exact hI.1 x.1 hx y.1 hy hyI
          have hw'I : ∀ x : {y : V // y ≠ p}, w' x (decide (x ∈ I.subtype (· ≠ p))) = true := by
            intro x
            have heq : @decide (x ∈ I.subtype (· ≠ p)) (Classical.propDecidable _) =
                @decide (x.1 ∈ I) (Classical.propDecidable _) := by
              apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq, Finset.mem_subtype]
            rw [heq]
            exact hI.2.1 x.1
          have hr'I : decide (r' ∈ I.subtype (· ≠ p)) = b := by
            have heq : @decide (r' ∈ I.subtype (· ≠ p)) (Classical.propDecidable _) =
                @decide (r ∈ I) (Classical.propDecidable _) := by
              apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq, Finset.mem_subtype, r']
            rw [heq]
            exact hI.2.2.2
          rw [Finset.mem_union]
          cases hq' : @decide (q' ∈ I.subtype (· ≠ p)) (Classical.propDecidable _)
          · left; simp only [Sf, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨his', hw'I, hq', hr'I⟩
          · right; simp only [St, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨his', hw'I, hq', hr'I⟩
        · intro I1 h1 I2 h2 heq
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
          have hp1 : p ∉ I1 := by have := h1.2.2.1; rw [ha] at this; simpa using this
          have hp2 : p ∉ I2 := by have := h2.2.2.1; rw [ha] at this; simpa using this
          ext x
          by_cases hxp : x = p
          · subst hxp; simp [hp1, hp2]
          · have hx1 : x ∈ I1 ↔ ⟨x, hxp⟩ ∈ I1.subtype (· ≠ p) := by simp
            have hx2 : x ∈ I2 ↔ ⟨x, hxp⟩ ∈ I2.subtype (· ≠ p) := by simp
            rw [hx1, hx2, heq]
        · intro I' hI'
          refine ⟨I'.map emb, ?_, by ext z; simp only [Finset.mem_subtype]; exact hmem_map I' z.2⟩
          have hcond : isIndep (delG G p) I' ∧ (∀ x, w' x (decide (x ∈ I')) = true) ∧ decide (r' ∈ I') = b := by
            rcases Finset.mem_union.mp hI' with hmem | hmem <;>
              simp only [Sf, St, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
            · exact ⟨hmem.1, hmem.2.1, hmem.2.2.2⟩
            · exact ⟨hmem.1, hmem.2.1, hmem.2.2.2⟩
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
          have hpNI : p ∉ I'.map emb := by
            simp only [Finset.mem_map, emb, Function.Embedding.coeFn_mk]
            rintro ⟨z, _, hzp⟩; exact z.2 hzp
          refine ⟨(his_map I').mpr hcond.1, ?_, ?_, ?_⟩
          · intro x
            by_cases hxp : x = p
            · rw [hxp]
              have hd : @decide (p ∈ I'.map emb) (Classical.propDecidable _) = false := by
                simp only [decide_eq_false_iff_not]; exact hpNI
              rw [hd, ← ha, hwp]
            · have heq : @decide (x ∈ I'.map emb) (Classical.propDecidable _) =
                  @decide (⟨x, hxp⟩ ∈ I') (Classical.propDecidable _) := by
                apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]; exact hmem_map I' hxp
              rw [heq]
              exact hcond.2.1 ⟨x, hxp⟩
          · simp only [ha, decide_eq_false_iff_not]; exact hpNI
          · have heq : @decide (r ∈ I'.map emb) (Classical.propDecidable _) =
                @decide (r' ∈ I') (Classical.propDecidable _) := by
              apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]; exact hmem_map I' hpr.symm
            rw [heq]; exact hcond.2.2
      · simp only [Bool.true_eq_false, ite_false]
        refine Finset.card_bij (fun I _ => I.subtype (· ≠ p)) ?_ ?_ ?_
        · intro I hI
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hI
          have hpI : p ∈ I := by
            have := hI.2.2.1
            rw [ha] at this
            simpa using this
          have hqNI : q ∉ I := by
            apply hI.1 p hpI q
            rw [hGq]; exact Finset.mem_singleton_self q
          simp only [Sf, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro x hx y hy hyI
            simp only [Finset.mem_subtype, delG] at hx hy hyI
            exact hI.1 x.1 hx y.1 hy hyI
          · intro x
            have heq : @decide (x ∈ I.subtype (· ≠ p)) (Classical.propDecidable _) =
                @decide (x.1 ∈ I) (Classical.propDecidable _) := by
              apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq, Finset.mem_subtype]
            rw [heq]
            exact hI.2.1 x.1
          · simp only [decide_eq_false_iff_not, Finset.mem_subtype, q']
            exact hqNI
          · have heq : @decide (r' ∈ I.subtype (· ≠ p)) (Classical.propDecidable _) =
                @decide (r ∈ I) (Classical.propDecidable _) := by
              apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq, Finset.mem_subtype, r']
            rw [heq]
            exact hI.2.2.2
        · intro I1 h1 I2 h2 heq
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
          have hp1 : p ∈ I1 := by have := h1.2.2.1; rw [ha] at this; simpa using this
          have hp2 : p ∈ I2 := by have := h2.2.2.1; rw [ha] at this; simpa using this
          ext x
          by_cases hxp : x = p
          · subst hxp; simp [hp1, hp2]
          · have hx1 : x ∈ I1 ↔ ⟨x, hxp⟩ ∈ I1.subtype (· ≠ p) := by simp
            have hx2 : x ∈ I2 ↔ ⟨x, hxp⟩ ∈ I2.subtype (· ≠ p) := by simp
            rw [hx1, hx2, heq]
        · intro I' hI'
          simp only [Sf, Finset.mem_filter, Finset.mem_univ, true_and] at hI'
          refine ⟨insert p (I'.map emb), ?_, by ext z; simp only [Finset.mem_subtype, Finset.mem_insert, z.2, false_or]; exact hmem_map I' z.2⟩
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
          have hqNI' : q' ∉ I' := by simpa using hI'.2.2.1
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro x hx y hy hyI
            rcases Finset.mem_insert.mp hx with rfl | hx0
            · rw [hGq, Finset.mem_singleton] at hy
              rw [hy] at hyI
              rcases Finset.mem_insert.mp hyI with hqp | hq0
              · exact q'.2 hqp
              · exact hqNI' ((hmem_map I' q'.2).mp hq0)
            · rcases Finset.mem_insert.mp hyI with hyp | hy0
              · have hxp' : x ∈ G p := (hsymm x p).mp (by rwa [← hyp])
                rw [hGq, Finset.mem_singleton] at hxp'
                rw [hxp'] at hx0
                exact hqNI' ((hmem_map I' q'.2).mp hx0)
              · exact ((his_map I').mpr hI'.1) x hx0 y hy hy0
          · intro x
            by_cases hxp : x = p
            · rw [hxp]
              have hd : @decide (p ∈ insert p (I'.map emb)) (Classical.propDecidable _) = true := by
                simp only [decide_eq_true_eq]; exact Finset.mem_insert_self p _
              rw [hd]
              exact ha ▸ hwp
            · have heq : @decide (x ∈ insert p (I'.map emb)) (Classical.propDecidable _) =
                  @decide (⟨x, hxp⟩ ∈ I') (Classical.propDecidable _) := by
                apply Bool.eq_iff_iff.mpr
                simp only [decide_eq_true_eq, Finset.mem_insert, hxp, false_or]
                exact hmem_map I' hxp
              rw [heq]
              exact hI'.2.1 ⟨x, hxp⟩
          · simp only [ha, decide_eq_true_eq]; exact Finset.mem_insert_self p _
          · have heq : @decide (r ∈ insert p (I'.map emb)) (Classical.propDecidable _) =
                @decide (r' ∈ I') (Classical.propDecidable _) := by
              apply Bool.eq_iff_iff.mpr
              simp only [decide_eq_true_eq, Finset.mem_insert, hpr.symm, false_or]
              exact hmem_map I' hpr.symm
            rw [heq]; exact hI'.2.2.2
  have hlhs : decide (S.card % 2 = 1) =
      matMul (diagMat (w p)) (matMul HMat (fun c d => decide ((if c then St else Sf).card % 2 = 1))) a b := by
    rw [hcard_eq]
    cases hwp : w p a
    · simp [matMul, diagMat, hwp]
    · cases ha : a
      · have hwpf : w p false = true := ha ▸ hwp
        simp only [hwpf, Bool.true_eq_false, ite_false, ite_true,
          Finset.card_union_of_disjoint hdisj, matMul, diagMat, HMat]
        have hadd : (Sf.card + St.card) % 2 = (Sf.card % 2 + St.card % 2) % 2 := Nat.add_mod _ _ _
        rw [hadd]
        rcases Nat.mod_two_eq_zero_or_one Sf.card with h0 | h0 <;>
          rcases Nat.mod_two_eq_zero_or_one St.card with h1 | h1 <;>
          simp [h0, h1]
      · have hwpt : w p true = true := ha ▸ hwp
        simp [Bool.true_eq_false, matMul, diagMat, HMat, hwpt]
  have hSf_eq : decide (Sf.card % 2 = 1) = wsig (delG G p) w' q' r' false b := by
    unfold wsig; congr!
  have hSt_eq : decide (St.card % 2 = 1) = wsig (delG G p) w' q' r' true b := by
    unfold wsig; congr!
  have hgoal : decide (S.card % 2 = 1) =
      matMul (diagMat (w p)) (matMul HMat (wsig (delG G p) w' q' r')) a b := by
    rw [hlhs]
    simp only [matMul, diagMat, HMat, Bool.false_eq_true, ite_true, ite_false, hSf_eq, hSt_eq]
  convert hgoal using 1
  congr 2
  funext c d
  unfold wsig
  congr!

theorem wsig_base_two {V : Type} [Fintype V] [DecidableEq V]
    (hcard : Fintype.card V = 2) (G : V → Finset V) (w : V → Bool → Bool) (p r : V)
    (hpr : p ≠ r) (hG : isSimpleGraph G) :
    wsig G w p r = fun a b => w p a && w r b && !(a && b) := by
  rcases hG with ⟨hirr, hsymm, hconn⟩
  have huniv : Finset.univ = ({p, r} : Finset V) := by
    symm
    apply Finset.eq_univ_of_card
    rw [Finset.card_pair hpr, hcard]
  have hpr_mem : ∀ x : V, x = p ∨ x = r := by
    intro x
    have hx : x ∈ ({p, r} : Finset V) := by rw [← huniv]; exact Finset.mem_univ x
    rcases Finset.mem_insert.mp hx with h | h
    · exact Or.inl h
    · exact Or.inr (Finset.mem_singleton.mp h)
  have hrGp : r ∈ G p := by
    have hnu : ({p} : Finset V) ≠ Finset.univ := by
      intro h
      have : ({p} : Finset V).card = 2 := by rw [h, Finset.card_univ, hcard]
      simp at this
    obtain ⟨u, hu, v, hv, hvnp⟩ := hconn {p} (Finset.singleton_nonempty p) hnu
    rw [Finset.mem_singleton] at hu
    rw [hu] at hv
    rcases hpr_mem v with hvp | hvr
    · exact absurd (Finset.mem_singleton.mpr hvp) hvnp
    · rwa [← hvr]
  have hpGr : p ∈ G r := (hsymm p r).mp hrGp
  funext a b
  letI : ∀ q : Prop, Decidable q := Classical.propDecidable
  unfold wsig
  let Iab : Finset V := (if a then {p} else ∅) ∪ (if b then {r} else ∅)
  have hpIab : p ∈ Iab ↔ a = true := by
    cases a <;> cases b <;> simp [Iab, hpr]
  have hrIab : r ∈ Iab ↔ b = true := by
    cases a <;> cases b <;> simp [Iab, hpr.symm]
  have huniq : ∀ I : Finset V, (decide (p ∈ I) = a ∧ decide (r ∈ I) = b) ↔ I = Iab := by
    intro I
    constructor
    · rintro ⟨hpI, hrI⟩
      ext x
      rcases hpr_mem x with hxp | hxr
      · rw [hxp, hpIab]
        cases a
        · simp only [Bool.false_eq_true, iff_false]; intro hp; simp [hp] at hpI
        · simp only [iff_true]; by_contra hp; simp [hp] at hpI
      · rw [hxr, hrIab]
        cases b
        · simp only [Bool.false_eq_true, iff_false]; intro hr; simp [hr] at hrI
        · simp only [iff_true]; by_contra hr; simp [hr] at hrI
    · intro h
      rw [h]
      have h1 : @decide (p ∈ Iab) (Classical.propDecidable _) = a := by
        apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]; exact hpIab
      have h2 : @decide (r ∈ Iab) (Classical.propDecidable _) = b := by
        apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]; exact hrIab
      exact ⟨h1, h2⟩
  have hisIab : isIndep G Iab ↔ (a = false ∨ b = false) := by
    cases a <;> cases b
    · simp [Iab, isIndep]
    · simp only [true_or, iff_true]
      intro u hu v hv hvI
      have hur : u = r := by simpa [Iab] using hu
      have hvr : v = r := by simpa [Iab] using hvI
      rw [hur, hvr] at hv; exact hirr r hv
    · simp only [or_true, iff_true]
      intro u hu v hv hvI
      have hup : u = p := by simpa [Iab] using hu
      have hvp : v = p := by simpa [Iab] using hvI
      rw [hup, hvp] at hv; exact hirr p hv
    · simp only [or_self, Bool.true_eq_false, iff_false]
      intro his
      have hp1 : p ∈ Iab := hpIab.mpr rfl
      have hr1 : r ∈ Iab := hrIab.mpr rfl
      exact his p hp1 r hrGp hr1
  have hwIab : (∀ v : V, w v (decide (v ∈ Iab)) = true) ↔ (w p a = true ∧ w r b = true) := by
    constructor
    · intro hw
      have hwp := hw p
      have hwr := hw r
      have hdp : @decide (p ∈ Iab) (Classical.propDecidable _) = a := by
        apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]; exact hpIab
      have hdr : @decide (r ∈ Iab) (Classical.propDecidable _) = b := by
        apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]; exact hrIab
      rw [hdp] at hwp; rw [hdr] at hwr
      exact ⟨hwp, hwr⟩
    · rintro ⟨hwp, hwr⟩ v
      rcases hpr_mem v with hvp | hvr
      · rw [hvp]
        have hdp : @decide (p ∈ Iab) (Classical.propDecidable _) = a := by
          apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]; exact hpIab
        rw [hdp]; exact hwp
      · rw [hvr]
        have hdr : @decide (r ∈ Iab) (Classical.propDecidable _) = b := by
          apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]; exact hrIab
        rw [hdr]; exact hwr
  by_cases hcond : w p a = true ∧ w r b = true ∧ (a = false ∨ b = false)
  · have hset : (Finset.univ : Finset (Finset V)).filter (fun I =>
        isIndep G I ∧ (∀ v : V, w v (decide (v ∈ I)) = true) ∧
        decide (p ∈ I) = a ∧ decide (r ∈ I) = b) = {Iab} := by
      ext I
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨_, _, hprI⟩; exact (huniq I).mp hprI
      · intro h; rw [h]
        exact ⟨hisIab.mpr hcond.2.2, hwIab.mpr ⟨hcond.1, hcond.2.1⟩, (huniq Iab).mpr rfl⟩
    have hlhs : decide ((Finset.univ.filter (fun I =>
        isIndep G I ∧ (∀ v : V, w v (decide (v ∈ I)) = true) ∧
        decide (p ∈ I) = a ∧ decide (r ∈ I) = b)).card % 2 = 1) = true := by
      rw [hset]; simp
    have hrhs : (w p a && w r b && !(a && b)) = true := by
      rcases hcond.2.2 with rfl | rfl <;> simp [hcond.1, hcond.2.1]
    rw [hrhs]
    convert hlhs
  · have hset : (Finset.univ : Finset (Finset V)).filter (fun I =>
        isIndep G I ∧ (∀ v : V, w v (decide (v ∈ I)) = true) ∧
        decide (p ∈ I) = a ∧ decide (r ∈ I) = b) = ∅ := by
      ext I
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      rintro ⟨his, hw, hprI⟩
      have hI := (huniq I).mp hprI
      rw [hI] at his hw
      exact hcond ⟨(hwIab.mp hw).1, (hwIab.mp hw).2, hisIab.mp his⟩
    have hlhs : decide ((Finset.univ.filter (fun I =>
        isIndep G I ∧ (∀ v : V, w v (decide (v ∈ I)) = true) ∧
        decide (p ∈ I) = a ∧ decide (r ∈ I) = b)).card % 2 = 1) = false := by
      rw [hset]; simp
    have hrhs : (w p a && w r b && !(a && b)) = false := by
      cases ha : a <;> cases hb : b <;> cases hw1 : w p a <;> cases hw2 : w r b <;>
        simp_all
    rw [hrhs]
    convert hlhs

theorem wsig_tree_inv_pathForm :
    ∀ n : Nat, ∀ {V : Type} [Fintype V] [DecidableEq V],
      Fintype.card V = n →
      ∀ (G : V → Finset V) (w : V → Bool → Bool) (p r : V),
        p ≠ r → isSimpleGraph G →
        ∑ x : V, (G x).card = 2 * (n - 1) →
        invM (wsig G w p r) = true →
        pathFormM (wsig G w p r) := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro V _ _ hcard G w p r hpr hG hsum hinv
    have hge2 : 2 ≤ n := by
      rw [← hcard]
      exact Fintype.one_lt_card_iff.mpr ⟨p, r, hpr⟩ |>.nat_succ_le
    by_cases hn2 : n = 2
    · subst hn2
      rw [wsig_base_two hcard G w p r hpr hG] at hinv ⊢
      exact edge_base_pathForm _ _ hinv
    · have hge3 : 3 ≤ n := by omega
      have hdeg_pos : ∀ x : V, 1 ≤ (G x).card := by
        intro x
        have hnu : ({x} : Finset V) ≠ Finset.univ := by
          intro h
          have : ({x} : Finset V).card = n := by rw [h, Finset.card_univ, hcard]
          simp at this
          omega
        obtain ⟨u, hu, v, hv, _⟩ := hG.2.2 {x} (Finset.singleton_nonempty x) hnu
        rw [Finset.mem_singleton] at hu
        subst hu
        exact Finset.card_pos.mpr ⟨v, hv⟩
      by_cases hex : ∃ v : V, v ≠ p ∧ v ≠ r ∧ (G v).card = 1
      · obtain ⟨v, hvp, hvr, hdeg1⟩ := hex
        obtain ⟨u, hGu⟩ := Finset.card_eq_one.mp hdeg1
        have hcard' : Fintype.card {y : V // y ≠ v} = n - 1 := by
          rw [Fintype.card_subtype_compl (fun x : V => x = v),
            show Fintype.card {x : V // x = v} = 1 from Fintype.card_unique, hcard]
        have hsum' : ∑ x : {y : V // y ≠ v}, (delG G v x).card = 2 * ((n - 1) - 1) := by
          have hs := delG_sum_card G v u hG.1 hG.2.1 hGu
          omega
        have hG' := delG_simple G v u hG hGu
        rw [wsig_peel_leaf G w p r v u hG.1 hG.2.1 hGu hvp hvr] at hinv ⊢
        exact ih (n - 1) (by omega) hcard' (delG G v) _ ⟨p, hvp.symm⟩ ⟨r, hvr.symm⟩
          (fun h => hpr (congrArg Subtype.val h)) hG' hsum' hinv
      · have hdeg_ge2 : ∀ v : V, v ≠ p → v ≠ r → 2 ≤ (G v).card := by
          intro v hvp hvr
          have h1 := hdeg_pos v
          have hne1 : (G v).card ≠ 1 := fun h => hex ⟨v, hvp, hvr, h⟩
          omega
        have hsum_split : ∑ x : V, (G x).card =
            (G p).card + (G r).card + ∑ x ∈ (Finset.univ.erase p).erase r, (G x).card := by
          have hpU : p ∈ (Finset.univ : Finset V) := Finset.mem_univ p
          have hrU : r ∈ (Finset.univ : Finset V).erase p := Finset.mem_erase.mpr ⟨hpr.symm, Finset.mem_univ r⟩
          rw [← Finset.add_sum_erase Finset.univ (fun x => (G x).card) hpU]
          rw [← Finset.add_sum_erase (Finset.univ.erase p) (fun x => (G x).card) hrU]
          omega
        have hrest_card : ((Finset.univ.erase p).erase r).card = n - 2 := by
          have hpU : p ∈ (Finset.univ : Finset V) := Finset.mem_univ p
          have hrU : r ∈ (Finset.univ : Finset V).erase p := Finset.mem_erase.mpr ⟨hpr.symm, Finset.mem_univ r⟩
          rw [Finset.card_erase_of_mem hrU, Finset.card_erase_of_mem hpU, Finset.card_univ, hcard]
          omega
        have hrest_lb : 2 * (n - 2) ≤ ∑ x ∈ (Finset.univ.erase p).erase r, (G x).card := by
          have hle : ∑ x ∈ (Finset.univ.erase p).erase r, 2 ≤
              ∑ x ∈ (Finset.univ.erase p).erase r, (G x).card := by
            refine Finset.sum_le_sum (fun x hx => ?_)
            simp only [Finset.mem_erase] at hx
            exact hdeg_ge2 x hx.2.1 hx.1
          simpa [hrest_card, mul_comm] using hle
        have hgp1 : (G p).card = 1 := by
          have h1 := hdeg_pos p
          have h2 := hdeg_pos r
          omega
        obtain ⟨q, hGq⟩ := Finset.card_eq_one.mp hgp1
        have hqr : q ≠ r := by
          intro hqr_eq
          rw [hqr_eq] at hGq
          have hgr1 : (G r).card = 1 := by
            have h1 := hdeg_pos p
            have h2 := hdeg_pos r
            omega
          have hpGr : p ∈ G r := (hG.2.1 p r).mp (by rw [hGq]; exact Finset.mem_singleton_self r)
          have hGr : G r = {p} := by
            obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hgr1
            rw [hz, Finset.mem_singleton] at hpGr
            rw [hz, hpGr]
          have hnu : ({p, r} : Finset V) ≠ Finset.univ := by
            intro h
            have : ({p, r} : Finset V).card = n := by rw [h, Finset.card_univ, hcard]
            rw [Finset.card_pair hpr] at this
            omega
          obtain ⟨u, hu, v, hv, hvns⟩ := hG.2.2 {p, r} ⟨p, Finset.mem_insert_self p {r}⟩ hnu
          rcases Finset.mem_insert.mp hu with hup | hur
          · rw [hup, hGq, Finset.mem_singleton] at hv
            rw [hv] at hvns
            exact hvns (Finset.mem_insert_of_mem (Finset.mem_singleton_self r))
          · rw [Finset.mem_singleton] at hur
            rw [hur, hGr, Finset.mem_singleton] at hv
            rw [hv] at hvns
            exact hvns (Finset.mem_insert_self p {r})
        have hcard' : Fintype.card {y : V // y ≠ p} = n - 1 := by
          rw [Fintype.card_subtype_compl (fun x : V => x = p),
            show Fintype.card {x : V // x = p} = 1 from Fintype.card_unique, hcard]
        have hsum' : ∑ x : {y : V // y ≠ p}, (delG G p x).card = 2 * ((n - 1) - 1) := by
          have hs := delG_sum_card G p q hG.1 hG.2.1 hGq
          omega
        have hG' := delG_simple G p q hG hGq
        rw [wsig_peel_port G w p q r hG.1 hG.2.1 hGq hpr hqr] at hinv ⊢
        obtain ⟨hf0, hf1, hinv'⟩ := invM_diag_H_mul (w p) _ hinv
        have hfn : w p = fun _ => true := by
          funext c; cases c <;> simp [hf0, hf1]
        rw [hfn, diag_true_mul]
        apply pathFormM_H_mul
        exact ih (n - 1) (by omega) hcard' (delG G p) (fun x => w x.1)
          ⟨q, fun h => hG.1 p (by rw [hGq, h]; exact Finset.mem_singleton_self p)⟩
          ⟨r, hpr.symm⟩ (fun h => hqr (congrArg Subtype.val h)) hG' hsum' hinv'

theorem lower_bound (K : Bool → Bool → Bool)
    (N : Nat) (G : Fin N → Finset (Fin N)) (p r : Fin N)
    (hpr : p ≠ r)
    (hG : (∀ v, v ∉ G v) ∧ (∀ u v, v ∈ G u ↔ u ∈ G v) ∧
      ∀ S : Finset (Fin N), S.Nonempty → S ≠ Finset.univ →
        ∃ u ∈ S, ∃ v ∈ G u, v ∉ S)
    (hsig : (fun a b => @decide ((@Finset.filter (Finset (Fin N))
      (fun I => (∀ u ∈ I, ∀ v ∈ G u, v ∉ I) ∧
        @decide (p ∈ I) (Classical.propDecidable _) = a ∧
        @decide (r ∈ I) (Classical.propDecidable _) = b)
      (fun _ => Classical.propDecidable _) Finset.univ).card % 2 = 1)
      (Classical.propDecidable _)) = K) :
    let inv := xor (K false false && K true true) (K false true && K true false)
    let pathForm := K = (fun a b => decide (a = b)) ∨
      K = (fun a b => !(a && b)) ∨ K = (fun a b => a || b)
    let cycles := if inv = true ∧ ¬pathForm then 1 else 0
    2 * (N - 1 + cycles) ≤ ∑ v, (G v).card := by
  intro inv pathForm cycles
  have hN : 0 < N := Fin.pos p
  have hlb := connected_deg_lb N G hN hG.2.1 hG.2.2
  by_cases hc : inv = true ∧ ¬pathForm
  · have hcyc : cycles = 1 := by simp [cycles, hc]
    rw [hcyc]
    have heven := sum_card_even N G hG.1 hG.2.1
    by_contra hlt
    have hsum : ∑ v, (G v).card = 2 * (N - 1) := by
      obtain ⟨m, hm⟩ := heven
      omega
    have hwsig : wsig G (fun _ _ => true) p r = K := by
      rw [← hsig]
      funext a b
      unfold wsig isIndep
      simp only [implies_true, true_and]
      congr!
    have hpf := wsig_tree_inv_pathForm N (Fintype.card_fin N) G (fun _ _ => true) p r hpr hG hsum
      (by rw [hwsig]; exact hc.1)
    rw [hwsig] at hpf
    exact hc.2 hpf
  · have hcyc : cycles = 0 := by simp [cycles, hc]
    rw [hcyc, Nat.add_zero]
    exact hlb

end PEqualNP.Outside.L_lib_1224.Aux

theorem PEqualNP.Outside.L_lib_1224 : (letI : ∀ p : Prop, Decidable p := Classical.propDecidable
let graph := fun (N : Nat) (G : Fin N → Finset (Fin N)) =>
  (∀ v, v ∉ G v) ∧ (∀ u v, v ∈ G u ↔ u ∈ G v) ∧
  ∀ S : Finset (Fin N), S.Nonempty → S ≠ Finset.univ →
    ∃ u ∈ S, ∃ v ∈ G u, v ∉ S
let sig := fun (N : Nat) (G : Fin N → Finset (Fin N)) (p r : Fin N) (a b : Bool) =>
  decide (((Finset.univ : Finset (Finset (Fin N))).filter (fun I =>
    (∀ u ∈ I, ∀ v ∈ G u, v ∉ I) ∧ decide (p ∈ I) = a ∧ decide (r ∈ I) = b)).card % 2 = 1)
∀ K : Bool → Bool → Bool,
  let inv := xor (K false false && K true true) (K false true && K true false)
  let pathForm := K = (fun a b => decide (a = b)) ∨
    K = (fun a b => !(a && b)) ∨ K = (fun a b => a || b)
  let cycles := if inv = true ∧ ¬pathForm then 1 else 0
  (∀ rightShore : Bool,
    ∃ (N : Nat) (G : Fin N → Finset (Fin N)) (side : Fin N → Bool) (p r : Fin N),
      N ≤ 15 ∧ p ≠ r ∧ graph N G ∧ side p = false ∧ side r = rightShore ∧
      (∀ u, ∀ v ∈ G u, side u ≠ side v) ∧ (∀ u, (G u).card ≤ 3) ∧
      (G p).card = 1 ∧ (G r).card = 1 ∧
      (∑ v, (G v).card) = 2*(N-1+cycles) ∧ sig N G p r = K ∧
      ∃ (l : Nat) (bag : Fin l → Finset (Fin N)),
        (∀ t, p ∈ bag t ∧ r ∈ bag t ∧ (bag t).card ≤ 6) ∧
        (∀ v, ∃ t, v ∈ bag t) ∧ (∀ u v, v ∈ G u → ∃ t, u ∈ bag t ∧ v ∈ bag t) ∧
        ∀ v s t u, s ≤ t → t ≤ u → v ∈ bag s → v ∈ bag u → v ∈ bag t) ∧
  ∀ (N : Nat) (G : Fin N → Finset (Fin N)) (p r : Fin N),
    p ≠ r → graph N G → sig N G p r = K →
    2*(N-1+cycles) ≤ ∑ v, (G v).card) := by
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  intro graph sig K inv pathForm cycles
  constructor
  · intro rightShore
    have hK : K = fun a b => if a then (if b then K true true else K true false)
        else (if b then K false true else K false false) := by
      funext a b; cases a <;> cases b <;> simp
    have hw := PEqualNP.Outside.L_lib_1224.Aux.witness_ok
      (K false false) (K false true) (K true false) (K true true) rightShore
      (PEqualNP.Outside.L_lib_1224.Aux.getWitness
        (K false false) (K false true) (K true false) (K true true) rightShore)
      (PEqualNP.Outside.L_lib_1224.Aux.all_witnesses_ok _ _ _ _ _)
    rw [← hK] at hw
    exact hw
  · intro N G p r hpr hG hsig
    convert PEqualNP.Outside.L_lib_1224.Aux.lower_bound K N G p r hpr hG hsig

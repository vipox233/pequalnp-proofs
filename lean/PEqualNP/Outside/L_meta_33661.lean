import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Relation
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_33661_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

abbrev F := ZMod 2

def b2z (b : Bool) : F := if b then 1 else 0

def z2b (z : F) : Bool := decide (z = 1)

lemma f_cases (x : F) : x = 0 ∨ x = 1 := by
  match x with
  | ⟨0, _⟩ => exact Or.inl rfl
  | ⟨1, _⟩ => exact Or.inr rfl

lemma f_add_self (x : F) : x + x = 0 := by
  rcases f_cases x with rfl | rfl <;> decide

lemma f_cancel_left (x y : F) : x + (x + y) = y := by
  rw [← add_assoc, f_add_self, zero_add]

lemma f_foil (a b c d : F) : (a + b) * (c + d) = a * c + b * d + (a * d + c * b) := by
  rcases f_cases a with rfl | rfl <;> rcases f_cases b with rfl | rfl <;>
  rcases f_cases c with rfl | rfl <;> rcases f_cases d with rfl | rfl <;> decide

lemma f_cancel2 (r c x y z : F) : (r + x) + (c + y) + (x + y + z) = r + c + z := by
  rcases f_cases r with rfl | rfl <;> rcases f_cases c with rfl | rfl <;>
  rcases f_cases x with rfl | rfl <;> rcases f_cases y with rfl | rfl <;>
  rcases f_cases z with rfl | rfl <;> decide

lemma f_cancel_row (r1 r2 c1 c2 s1 s2 : F) :
    (r1 + c1 + s1) + (r1 + c2 + s1) = (r2 + c1 + s2) + (r2 + c2 + s2) := by
  rcases f_cases r1 with rfl | rfl <;> rcases f_cases r2 with rfl | rfl <;>
  rcases f_cases c1 with rfl | rfl <;> rcases f_cases c2 with rfl | rfl <;>
  rcases f_cases s1 with rfl | rfl <;> rcases f_cases s2 with rfl | rfl <;> decide

lemma ite_pos' {α : Type*} {p : Prop} [Decidable p] (h : p) (a b : α) :
    (if p then a else b) = a := by
  split_ifs; rfl

lemma ite_neg' {α : Type*} {p : Prop} [Decidable p] (h : ¬ p) (a b : α) :
    (if p then a else b) = b := by
  split_ifs; rfl

lemma b2z_xor (a b : Bool) : b2z (xor a b) = b2z a + b2z b := by
  cases a <;> cases b <;> decide

lemma b2z_and (a b : Bool) : b2z (a && b) = b2z a * b2z b := by
  cases a <;> cases b <;> decide

lemma b2z_not (a : Bool) : b2z (!a) = 1 + b2z a := by
  cases a <;> decide

lemma b2z_inj {a b : Bool} (h : b2z a = b2z b) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

lemma b2z_z2b (z : F) : b2z (z2b z) = z := by
  rcases f_cases z with rfl | rfl <;> decide

lemma z2b_b2z (b : Bool) : z2b (b2z b) = b := by
  cases b <;> decide

lemma b2z_eq_iff (a b : Bool) : b2z a = b2z b ↔ a = b :=
  ⟨b2z_inj, fun h => h ▸ rfl⟩

def nonlinear (g : Gate) : Bool :=
  (g.inputs.length == 2) &&
    xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
        (xor (g.op.eval [true, false]) (g.op.eval [true, true]))

def depthList (w : ℕ) (gs : List Gate) : List ℕ :=
  gs.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun h => ds.getD h 0)).foldr max 0 + (nonlinear g).toNat])
    (List.replicate w 0)

def wireList (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma gate_anf_one (op : GateOp) (x : Bool) :
    b2z (op.eval [x]) = b2z (op.eval [false]) + (b2z (op.eval [false]) + b2z (op.eval [true])) * b2z x := by
  cases x
  · simp [b2z]
  · simp only [b2z, ite_true, mul_one, ← add_assoc, f_add_self, zero_add]

lemma gate_anf_two_aux (f00 f01 f10 f11 x y : Bool) :
    b2z (match x, y with
      | false, false => f00
      | false, true => f01
      | true, false => f10
      | true, true => f11) =
    b2z f00 + (b2z f00 + b2z f10) * b2z x + (b2z f00 + b2z f01) * b2z y +
      b2z (xor (xor f00 f01) (xor f10 f11)) * (b2z x * b2z y) := by
  cases x <;> cases y <;> cases f00 <;> cases f01 <;> cases f10 <;> cases f11 <;> decide

lemma gate_anf_two (op : GateOp) (x y : Bool) :
    b2z (op.eval [x, y]) =
      b2z (op.eval [false, false]) +
      (b2z (op.eval [false, false]) + b2z (op.eval [true, false])) * b2z x +
      (b2z (op.eval [false, false]) + b2z (op.eval [false, true])) * b2z y +
      b2z (xor (xor (op.eval [false, false]) (op.eval [false, true]))
               (xor (op.eval [true, false]) (op.eval [true, true]))) * (b2z x * b2z y) := by
  have h := gate_anf_two_aux (op.eval [false, false]) (op.eval [false, true])
    (op.eval [true, false]) (op.eval [true, true]) x y
  cases x <;> cases y <;> exact h

lemma depthList_length (w : ℕ) (gs : List Gate) : (depthList w gs).length = w + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [depthList]
  | append_singleton gs g ih =>
    simp only [depthList, List.foldl_append, List.foldl_cons, List.foldl_nil, List.length_append, List.length_singleton]
    have h1 : (depthList w gs).length = w + gs.length := ih
    unfold depthList at h1
    omega

lemma wireList_length (gs : List Gate) (x : List Bool) : (wireList gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [wireList]
  | append_singleton gs g ih =>
    simp only [wireList, List.foldl_append, List.foldl_cons, List.foldl_nil, List.length_append, List.length_singleton]
    have h1 : (wireList gs x).length = x.length + gs.length := ih
    unfold wireList at h1
    omega

lemma list_getD_append_left {α : Type*} (l1 l2 : List α) (i : ℕ) (d : α) (hi : i < l1.length) :
    (l1 ++ l2).getD i d = l1.getD i d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma list_getD_append_right_singleton {α : Type*} (l : List α) (a d : α) :
    (l ++ [a]).getD l.length d = a := by
  simp [List.getD_eq_getElem?_getD]

lemma depthList_append_getD (w : ℕ) (gs1 gs2 : List Gate) (k : ℕ) (hk : k < w + gs1.length) :
    (depthList w (gs1 ++ gs2)).getD k 0 = (depthList w gs1).getD k 0 := by
  induction gs2 using List.reverseRecOn with
  | nil => simp
  | append_singleton gs2 g ih =>
    rw [← List.append_assoc]
    have hlen : k < (depthList w (gs1 ++ gs2)).length := by
      rw [depthList_length, List.length_append]; omega
    have hstep : depthList w (gs1 ++ gs2 ++ [g]) =
        depthList w (gs1 ++ gs2) ++
          [(g.inputs.map (fun h => (depthList w (gs1 ++ gs2)).getD h 0)).foldr max 0 + (nonlinear g).toNat] := by
      simp [depthList, List.foldl_append]
    rw [hstep, list_getD_append_left _ _ k 0 hlen, ih]

lemma wireList_append_getD (gs1 gs2 : List Gate) (x : List Bool) (k : ℕ) (hk : k < x.length + gs1.length) :
    (wireList (gs1 ++ gs2) x).getD k false = (wireList gs1 x).getD k false := by
  induction gs2 using List.reverseRecOn with
  | nil => simp
  | append_singleton gs2 g ih =>
    rw [← List.append_assoc]
    have hlen : k < (wireList (gs1 ++ gs2) x).length := by
      rw [wireList_length, List.length_append]; omega
    have hstep : wireList (gs1 ++ gs2 ++ [g]) x =
        wireList (gs1 ++ gs2) x ++
          [g.op.eval (g.inputs.map (fun h => (wireList (gs1 ++ gs2) x).getD h false))] := by
      simp [wireList, List.foldl_append]
    rw [hstep, list_getD_append_left _ _ k false hlen, ih]

lemma depthList_input (w : ℕ) (gs : List Gate) (k : ℕ) (hk : k < w) :
    (depthList w gs).getD k 0 = 0 := by
  have h := depthList_append_getD w [] gs k (by simpa using hk)
  simp only [List.nil_append] at h
  rw [h]
  simp [depthList, List.getD_eq_getElem?_getD, hk]

lemma wireList_input (gs : List Gate) (x : List Bool) (k : ℕ) (hk : k < x.length) :
    (wireList gs x).getD k false = x.getD k false := by
  have h := wireList_append_getD [] gs x k (by simpa using hk)
  simp only [List.nil_append] at h
  rw [h]
  simp [wireList]

lemma depthList_gate (w : ℕ) (Q : Circuit) (hrb : ReadsBack w Q) (j : ℕ) (hj : j < Q.gates.length) :
    (depthList w Q.gates).getD (w + j) 0 =
      ((Q.gates[j]).inputs.map (fun h => (depthList w Q.gates).getD h 0)).foldr max 0 +
        (nonlinear (Q.gates[j])).toNat := by
  have hsplit : Q.gates = Q.gates.take j ++ [Q.gates[j]] ++ Q.gates.drop (j + 1) := by
    calc Q.gates = Q.gates.take j ++ Q.gates.drop j := (List.take_append_drop j Q.gates).symm
      _ = Q.gates.take j ++ (Q.gates[j] :: Q.gates.drop (j + 1)) := by rw [List.drop_eq_getElem_cons hj]
      _ = Q.gates.take j ++ [Q.gates[j]] ++ Q.gates.drop (j + 1) := by simp
  have hlen_take : (Q.gates.take j).length = j := List.length_take_of_le (Nat.le_of_lt hj)
  have hpref1 : (depthList w Q.gates).getD (w + j) 0 =
      (depthList w (Q.gates.take j ++ [Q.gates[j]])).getD (w + j) 0 := by
    conv_lhs => rw [hsplit]
    exact depthList_append_getD w (Q.gates.take j ++ [Q.gates[j]]) (Q.gates.drop (j + 1)) (w + j)
      (by rw [List.length_append, List.length_singleton, hlen_take]; omega)
  rw [hpref1]
  have hstep : depthList w (Q.gates.take j ++ [Q.gates[j]]) =
      depthList w (Q.gates.take j) ++
        [((Q.gates[j]).inputs.map (fun h => (depthList w (Q.gates.take j)).getD h 0)).foldr max 0 +
          (nonlinear (Q.gates[j])).toNat] := by
    unfold depthList
    rw [List.foldl_append]
    rfl
  rw [hstep]
  have hidx : w + j = (depthList w (Q.gates.take j)).length := by
    rw [depthList_length, hlen_take]
  rw [hidx, list_getD_append_right_singleton]
  congr 1; congr 1
  apply List.map_congr_left
  intro h hh
  have hlt : h < w + j := by
    have h1 := hrb j hj h
    unfold gateAt at h1
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] at h1
    exact h1 hh
  conv_rhs => rw [hsplit, List.append_assoc]
  exact (depthList_append_getD w (Q.gates.take j) ([Q.gates[j]] ++ Q.gates.drop (j + 1)) h (by omega)).symm

lemma wireList_gate (w : ℕ) (Q : Circuit) (hrb : ReadsBack w Q) (x : List Bool) (hx : x.length = w)
    (j : ℕ) (hj : j < Q.gates.length) :
    (wireList Q.gates x).getD (w + j) false =
      (Q.gates[j]).op.eval ((Q.gates[j]).inputs.map (fun h => (wireList Q.gates x).getD h false)) := by
  have hsplit : Q.gates = Q.gates.take j ++ [Q.gates[j]] ++ Q.gates.drop (j + 1) := by
    calc Q.gates = Q.gates.take j ++ Q.gates.drop j := (List.take_append_drop j Q.gates).symm
      _ = Q.gates.take j ++ (Q.gates[j] :: Q.gates.drop (j + 1)) := by rw [List.drop_eq_getElem_cons hj]
      _ = Q.gates.take j ++ [Q.gates[j]] ++ Q.gates.drop (j + 1) := by simp
  have hlen_take : (Q.gates.take j).length = j := List.length_take_of_le (Nat.le_of_lt hj)
  have hpref1 : (wireList Q.gates x).getD (w + j) false =
      (wireList (Q.gates.take j ++ [Q.gates[j]]) x).getD (w + j) false := by
    conv_lhs => rw [hsplit]
    exact wireList_append_getD (Q.gates.take j ++ [Q.gates[j]]) (Q.gates.drop (j + 1)) x (w + j)
      (by rw [hx, List.length_append, List.length_singleton, hlen_take]; omega)
  rw [hpref1]
  have hstep : wireList (Q.gates.take j ++ [Q.gates[j]]) x =
      wireList (Q.gates.take j) x ++
        [(Q.gates[j]).op.eval ((Q.gates[j]).inputs.map (fun h => (wireList (Q.gates.take j) x).getD h false))] := by
    unfold wireList
    rw [List.foldl_append]
    rfl
  rw [hstep]
  have hidx : w + j = (wireList (Q.gates.take j) x).length := by
    rw [wireList_length, hx, hlen_take]
  rw [hidx, list_getD_append_right_singleton]
  congr 1
  apply List.map_congr_left
  intro h hh
  have hlt : h < w + j := by
    have h1 := hrb j hj h
    unfold gateAt at h1
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] at h1
    exact h1 hh
  conv_rhs => rw [hsplit, List.append_assoc]
  exact (wireList_append_getD (Q.gates.take j) ([Q.gates[j]] ++ Q.gates.drop (j + 1)) x h (by omega)).symm

lemma oneEach_length {a b : ℕ} (u : Fin a) (v : Fin b) : (oneEach u v).length = a + b := by
  simp [oneEach]

lemma oneEach_getD_left {a b : ℕ} (u : Fin a) (v : Fin b) (k : ℕ) (hk : k < a) :
    (oneEach u v).getD k false = decide (k = u.val) := by
  unfold oneEach
  rw [list_getD_append_left _ _ k false (by simp [hk])]
  simp [List.getD_eq_getElem?_getD, hk, Fin.ext_iff]

lemma oneEach_getD_right {a b : ℕ} (u : Fin a) (v : Fin b) (k : ℕ) (hk1 : a ≤ k) (hk2 : k < a + b) :
    (oneEach u v).getD k false = decide (k - a = v.val) := by
  unfold oneEach
  have hlen : (List.ofFn (fun i : Fin a => decide (i = u))).length = a := by simp
  have hge : (List.ofFn (fun i : Fin a => decide (i = u))).length ≤ k := by rw [hlen]; exact hk1
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right hge, hlen]
  have hlt : k - a < b := by omega
  simp [hlt, Fin.ext_iff]

lemma foldr_max_le_iff (l : List ℕ) (bound : ℕ) :
    l.foldr max 0 ≤ bound ↔ ∀ x ∈ l, x ≤ bound := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons, List.mem_cons, max_le_iff, ih]
    constructor
    · rintro ⟨ha, hl⟩ x (rfl | hx)
      · exact ha
      · exact hl x hx
    · intro h
      exact ⟨h a (Or.inl rfl), fun x hx => h x (Or.inr hx)⟩

lemma countP_finset_card {α : Type*} (l : List α) (p : α → Bool) :
    ((Finset.univ : Finset (Fin l.length)).filter (fun i => p l[i] = true)).card = l.countP p := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.countP_cons]
    have hsplit : ((Finset.univ : Finset (Fin (a :: l).length)).filter (fun i => p (a :: l)[i] = true)).card =
        (if p a = true then 1 else 0) +
        ((Finset.univ : Finset (Fin l.length)).filter (fun i => p l[i] = true)).card := by
      let S := (Finset.univ : Finset (Fin (l.length + 1))).filter (fun i => p (a :: l)[i] = true)
      let S0 := S.filter (fun i => i = 0)
      let S1 := S.filter (fun i => i ≠ 0)
      have hd : Disjoint S0 S1 := by
        rw [Finset.disjoint_filter]; intro _ _ h1 h2; exact h2 h1
      have hu : S0 ∪ S1 = S := by
        ext i; simp only [S0, S1, Finset.mem_union, Finset.mem_filter]
        by_cases h : i = 0 <;> simp [h]
      have hc0 : S0.card = if p a = true then 1 else 0 := by
        by_cases hpa : p a = true
        · have heq : S0 = {0} := by
            ext i; simp only [S0, S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
            constructor
            · rintro ⟨_, rfl⟩; rfl
            · rintro rfl; exact ⟨hpa, rfl⟩
          rw [heq, Finset.card_singleton]; simp [hpa]
        · have heq : S0 = ∅ := by
            ext i; simp only [S0, S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
            rintro ⟨hp, rfl⟩; exact hpa hp
          rw [heq, Finset.card_empty]; simp [hpa]
      have hc1 : S1.card = ((Finset.univ : Finset (Fin l.length)).filter (fun i => p l[i] = true)).card := by
        apply Finset.card_bij (fun i hi => ⟨i.val - 1, by
          have hne : i ≠ 0 := (Finset.mem_filter.mp hi).2
          have hpos : 0 < i.val := Nat.pos_of_ne_zero (fun h0 => hne (Fin.ext h0))
          omega⟩)
        · intro i hi
          have h1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
          have hne : i ≠ 0 := (Finset.mem_filter.mp hi).2
          have hpos : 0 < i.val := Nat.pos_of_ne_zero (fun h0 => hne (Fin.ext h0))
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          have hget : (a :: l)[i.val]'(i.isLt) = l[i.val - 1]'(by omega) := by
            rcases i with ⟨iv, hiv⟩
            cases iv with
            | zero => exact (hne rfl).elim
            | succ k => rfl
          simpa [hget] using h1
        · intro i1 hi1 i2 hi2 heq
          have h1 : 0 < i1.val := Nat.pos_of_ne_zero (fun h0 => (Finset.mem_filter.mp hi1).2 (Fin.ext h0))
          have h2 : 0 < i2.val := Nat.pos_of_ne_zero (fun h0 => (Finset.mem_filter.mp hi2).2 (Fin.ext h0))
          have hv : i1.val - 1 = i2.val - 1 := congrArg Fin.val heq
          exact Fin.ext (by omega)
        · intro k hk
          refine ⟨k.succ, ?_, Fin.ext (by simp)⟩
          have hpk := (Finset.mem_filter.mp hk).2
          refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, Fin.succ_ne_zero k⟩
          simpa using hpk
      have htot := Finset.card_union_of_disjoint hd
      rw [hu, hc0, hc1] at htot
      exact htot
    rw [hsplit, ih]
    cases p a <;> simp [Nat.add_comm]

lemma depth0_separable {m n : ℕ} (Q : Circuit)
    (hfan : ∀ g ∈ Q.gates, g.inputs.length ≤ 2)
    (hrb : ReadsBack (m + 1 + n) Q) :
    ∀ k < m + 1 + n + Q.gates.length, (depthList (m + 1 + n) Q.gates).getD k 0 = 0 →
      ∃ (R : Fin (m + 1) → F) (C : Fin n → F),
        ∀ u v, b2z ((wireList Q.gates (oneEach u v)).getD k false) = R u + C v := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hk hd0
    let w0 := m + 1 + n
    by_cases hkin : k < w0
    · by_cases hkm : k < m + 1
      · refine ⟨fun u => b2z (decide (k = u.val)), fun _ => 0, fun u v => ?_⟩
        rw [wireList_input Q.gates (oneEach u v) k (by rw [oneEach_length]; omega),
          oneEach_getD_left u v k hkm, add_zero]
      · refine ⟨fun _ => 0, fun v => b2z (decide (k - (m + 1) = v.val)), fun u v => ?_⟩
        rw [wireList_input Q.gates (oneEach u v) k (by rw [oneEach_length]; omega),
          oneEach_getD_right u v k (by omega) (by omega), zero_add]
    · let j := k - w0
      have hj : j < Q.gates.length := by omega
      have hkj : k = w0 + j := by omega
      rw [hkj] at hd0 ⊢
      have hdg := depthList_gate w0 Q hrb j hj
      rw [hd0] at hdg
      have hnl : nonlinear Q.gates[j] = false := by
        cases hn : nonlinear Q.gates[j]
        · rfl
        · rw [hn] at hdg; simp at hdg
      have hdin : ∀ h ∈ (Q.gates[j]).inputs, (depthList w0 Q.gates).getD h 0 = 0 := by
        intro h hh
        have hle : (((Q.gates[j]).inputs.map (fun i => (depthList w0 Q.gates).getD i 0)).foldr max 0) ≤ 0 := by
          omega
        have h1 := (foldr_max_le_iff _ 0).mp hle _ (List.mem_map.mpr ⟨h, hh, rfl⟩)
        omega
      have hlt_in : ∀ h ∈ (Q.gates[j]).inputs, h < w0 + j := by
        intro h hh
        have h1 := hrb j hj h
        unfold gateAt at h1
        simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] at h1
        exact h1 hh
      have hfl : (Q.gates[j]).inputs.length ≤ 2 := hfan Q.gates[j] (List.getElem_mem hj)
      cases hin : (Q.gates[j]).inputs with
      | nil =>
        refine ⟨fun _ => b2z ((Q.gates[j]).op.eval []), fun _ => 0, fun u v => ?_⟩
        rw [wireList_gate w0 Q hrb (oneEach u v) (oneEach_length u v) j hj, hin, List.map_nil, add_zero]
      | cons i1 tl =>
        cases tl with
        | nil =>
          have hi1_lt : i1 < w0 + j := hlt_in i1 (by simp [hin])
          have hi1_d0 : (depthList w0 Q.gates).getD i1 0 = 0 := hdin i1 (by simp [hin])
          obtain ⟨R1, C1, h1⟩ := ih i1 (by omega) (by omega) hi1_d0
          let c0 := b2z ((Q.gates[j]).op.eval [false])
          let c1 := b2z ((Q.gates[j]).op.eval [false]) + b2z ((Q.gates[j]).op.eval [true])
          refine ⟨fun u => c0 + c1 * R1 u, fun v => c1 * C1 v, fun u v => ?_⟩
          rw [wireList_gate w0 Q hrb (oneEach u v) (oneEach_length u v) j hj, hin]
          simp only [List.map_cons, List.map_nil]
          rw [gate_anf_one, h1 u v]
          change c0 + c1 * (R1 u + C1 v) = (c0 + c1 * R1 u) + c1 * C1 v
          rw [mul_add, add_assoc]
        | cons i2 tl2 =>
          cases tl2 with
          | nil =>
            have hi1_lt : i1 < w0 + j := hlt_in i1 (by simp [hin])
            have hi2_lt : i2 < w0 + j := hlt_in i2 (by simp [hin])
            have hi1_d0 : (depthList w0 Q.gates).getD i1 0 = 0 := hdin i1 (by simp [hin])
            have hi2_d0 : (depthList w0 Q.gates).getD i2 0 = 0 := hdin i2 (by simp [hin])
            obtain ⟨R1, C1, h1⟩ := ih i1 (by omega) (by omega) hi1_d0
            obtain ⟨R2, C2, h2⟩ := ih i2 (by omega) (by omega) hi2_d0
            have hxor0 : xor (xor ((Q.gates[j]).op.eval [false, false]) ((Q.gates[j]).op.eval [false, true]))
                (xor ((Q.gates[j]).op.eval [true, false]) ((Q.gates[j]).op.eval [true, true])) = false := by
              unfold nonlinear at hnl
              rw [hin] at hnl
              simpa using hnl
            let c0 := b2z ((Q.gates[j]).op.eval [false, false])
            let c1 := b2z ((Q.gates[j]).op.eval [false, false]) + b2z ((Q.gates[j]).op.eval [true, false])
            let c2 := b2z ((Q.gates[j]).op.eval [false, false]) + b2z ((Q.gates[j]).op.eval [false, true])
            refine ⟨fun u => c0 + c1 * R1 u + c2 * R2 u, fun v => c1 * C1 v + c2 * C2 v, fun u v => ?_⟩
            rw [wireList_gate w0 Q hrb (oneEach u v) (oneEach_length u v) j hj, hin]
            simp only [List.map_cons, List.map_nil]
            rw [gate_anf_two, hxor0, h1 u v, h2 u v]
            change c0 + c1 * (R1 u + C1 v) + c2 * (R2 u + C2 v) + 0 * _ =
              (c0 + c1 * R1 u + c2 * R2 u) + (c1 * C1 v + c2 * C2 v)
            rw [zero_mul, add_zero, mul_add, mul_add]
            ac_rfl
          | cons _ _ =>
            rw [hin] at hfl; simp at hfl

structure N1Data (m n : ℕ) where
  i1 : ℕ
  i2 : ℕ
  R1 : Fin (m + 1) → F
  R2 : Fin (m + 1) → F
  C1 : Fin n → F
  C2 : Fin n → F

lemma circuit_to_rank2t {m n t : ℕ} (P : Fin (m + 1) → Fin n → Bool) (Q : Circuit)
    (hfan : ∀ g ∈ Q.gates, g.inputs.length ≤ 2)
    (hrb : ReadsBack (m + 1 + n) Q)
    (hrep : Represents P Q)
    (hdep : (depthList (m + 1 + n) Q.gates).getD Q.output 0 ≤ 1)
    (hcnt : Q.gates.countP nonlinear ≤ t) :
    ∃ (R : Fin (m + 1) → F) (C : Fin n → F) (U : Fin (m + 1) → Fin (2 * t) → F) (V : Fin n → Fin (2 * t) → F),
      ∀ u v, b2z (P u v) = R u + C v + ∑ k : Fin (2 * t), U u k * V v k := by
  classical
  let w0 := m + 1 + n
  by_cases hout : Q.output < w0 + Q.gates.length
  · let N1 : Finset (Fin Q.gates.length) :=
      Finset.univ.filter (fun j => nonlinear Q.gates[j] = true ∧ (depthList w0 Q.gates).getD (w0 + j.val) 0 ≤ 1)
    have hN1_card : N1.card ≤ t := by
      have hsub : N1 ⊆ Finset.univ.filter (fun j : Fin Q.gates.length => nonlinear Q.gates[j] = true) :=
        fun j hj => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2.1⟩
      calc N1.card ≤ (Finset.univ.filter (fun j : Fin Q.gates.length => nonlinear Q.gates[j] = true)).card :=
            Finset.card_le_card hsub
        _ = Q.gates.countP nonlinear := countP_finset_card Q.gates nonlinear
        _ ≤ t := hcnt
    have hN1_spec : ∀ j : N1, ∃ d : N1Data m n,
        (Q.gates[j.1.val]).inputs = [d.i1, d.i2] ∧
        (∀ u v, b2z ((wireList Q.gates (oneEach u v)).getD d.i1 false) = d.R1 u + d.C1 v) ∧
        (∀ u v, b2z ((wireList Q.gates (oneEach u v)).getD d.i2 false) = d.R2 u + d.C2 v) := by
      intro ⟨j, hjN⟩
      have hnl : nonlinear Q.gates[j.val] = true := (Finset.mem_filter.mp hjN).2.1
      have hd1 : (depthList w0 Q.gates).getD (w0 + j.val) 0 ≤ 1 := (Finset.mem_filter.mp hjN).2.2
      have hlen2 : (Q.gates[j.val]).inputs.length = 2 := by
        unfold nonlinear at hnl
        simp only [Bool.and_eq_true, beq_iff_eq] at hnl
        exact hnl.1
      rcases List.length_eq_two.mp hlen2 with ⟨i1, i2, hin⟩
      have hdg := depthList_gate w0 Q hrb j.val j.isLt
      rw [hnl] at hdg
      have hle0 : (((Q.gates[j.val]).inputs.map (fun i => (depthList w0 Q.gates).getD i 0)).foldr max 0) ≤ 0 := by
        simp only [Bool.toNat_true] at hdg; omega
      have hdin : ∀ h ∈ (Q.gates[j.val]).inputs, (depthList w0 Q.gates).getD h 0 = 0 := fun h hh => by
        have h1 := (foldr_max_le_iff _ 0).mp hle0 _ (List.mem_map.mpr ⟨h, hh, rfl⟩)
        omega
      have hlt_in : ∀ h ∈ (Q.gates[j.val]).inputs, h < w0 + j.val := fun h hh => by
        have h1 := hrb j.val j.isLt h
        unfold gateAt at h1
        simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem j.isLt, Option.getD_some] at h1
        exact h1 hh
      have hi1_lt : i1 < w0 + j.val := hlt_in i1 (by rw [hin]; simp)
      have hi2_lt : i2 < w0 + j.val := hlt_in i2 (by rw [hin]; simp)
      obtain ⟨R1, C1, h1⟩ := depth0_separable Q hfan hrb i1 (by omega) (hdin i1 (by rw [hin]; simp))
      obtain ⟨R2, C2, h2⟩ := depth0_separable Q hfan hrb i2 (by omega) (hdin i2 (by rw [hin]; simp))
      exact ⟨⟨i1, i2, R1, R2, C1, C2⟩, hin, h1, h2⟩
    let dN : N1 → N1Data m n := fun j => (hN1_spec j).choose
    let pL : N1 → Fin (m + 1) → F := fun j => (dN j).R1
    let pR : N1 → Fin (m + 1) → F := fun j => (dN j).R2
    let qR : N1 → Fin n → F := fun j => (dN j).C1
    let qL : N1 → Fin n → F := fun j => (dN j).C2
    have hwire_span : ∀ k < w0 + Q.gates.length, (depthList w0 Q.gates).getD k 0 ≤ 1 →
        ∃ (R : Fin (m + 1) → F) (C : Fin n → F) (lam : N1 → F),
          ∀ u v, b2z ((wireList Q.gates (oneEach u v)).getD k false) =
            R u + C v + ∑ j : N1, lam j * (pL j u * qL j v + pR j u * qR j v) := by
      intro k
      induction k using Nat.strong_induction_on with
      | ind k ih =>
        intro hk hd1
        by_cases hkin : k < w0
        · obtain ⟨R, C, hRC⟩ := depth0_separable Q hfan hrb k hk (depthList_input w0 Q.gates k hkin)
          refine ⟨R, C, fun _ => 0, fun u v => ?_⟩
          rw [hRC u v]; simp
        · let j : Fin Q.gates.length := ⟨k - w0, by omega⟩
          have hkj : k = w0 + j.val := by dsimp only [j]; omega
          rw [hkj] at hd1 ⊢
          by_cases hnl : nonlinear Q.gates[j] = true
          · have hjN : j ∈ N1 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnl, hd1⟩
            let jN : N1 := ⟨j, hjN⟩
            have hspec := (hN1_spec jN).choose_spec
            have hin : (Q.gates[j.val]).inputs = [(dN jN).i1, (dN jN).i2] := hspec.1
            have h1 : ∀ u v, b2z ((wireList Q.gates (oneEach u v)).getD (dN jN).i1 false) = pL jN u + qR jN v := hspec.2.1
            have h2 : ∀ u v, b2z ((wireList Q.gates (oneEach u v)).getD (dN jN).i2 false) = pR jN u + qL jN v := hspec.2.2
            have hxor1 : xor (xor ((Q.gates[j.val]).op.eval [false, false]) ((Q.gates[j.val]).op.eval [false, true]))
                (xor ((Q.gates[j.val]).op.eval [true, false]) ((Q.gates[j.val]).op.eval [true, true])) = true := by
              have hnl' : nonlinear Q.gates[j.val] = true := hnl
              unfold nonlinear at hnl'
              simp only [Bool.and_eq_true] at hnl'
              exact hnl'.2
            let c0 := b2z ((Q.gates[j.val]).op.eval [false, false])
            let c1 := b2z ((Q.gates[j.val]).op.eval [false, false]) + b2z ((Q.gates[j.val]).op.eval [true, false])
            let c2 := b2z ((Q.gates[j.val]).op.eval [false, false]) + b2z ((Q.gates[j.val]).op.eval [false, true])
            refine ⟨fun u => c0 + c1 * pL jN u + c2 * pR jN u + pL jN u * pR jN u,
              fun v => c1 * qR jN v + c2 * qL jN v + qR jN v * qL jN v,
              fun j' => if j' = jN then 1 else 0, fun u v => ?_⟩
            rw [wireList_gate w0 Q hrb (oneEach u v) (oneEach_length u v) j.val j.isLt, hin]
            simp only [List.map_cons, List.map_nil]
            rw [gate_anf_two, hxor1, h1 u v, h2 u v]
            have hsum_single : ∑ j' : N1, (if j' = jN then (1 : F) else 0) * (pL j' u * qL j' v + pR j' u * qR j' v) =
                pL jN u * qL jN v + pR jN u * qR jN v := by
              rw [Finset.sum_eq_single jN]
              · simp
              · intro j' _ hne; simp [hne]
              · intro hni; exact (hni (Finset.mem_univ _)).elim
            rw [hsum_single]
            change c0 + c1 * (pL jN u + qR jN v) + c2 * (pR jN u + qL jN v) +
              1 * ((pL jN u + qR jN v) * (pR jN u + qL jN v)) =
              (c0 + c1 * pL jN u + c2 * pR jN u + pL jN u * pR jN u) +
              (c1 * qR jN v + c2 * qL jN v + qR jN v * qL jN v) +
              (pL jN u * qL jN v + pR jN u * qR jN v)
            rw [one_mul, mul_add, mul_add, f_foil]
            ac_rfl
          · have hnlf : nonlinear Q.gates[j.val] = false := Bool.eq_false_iff.mpr hnl
            have hdg := depthList_gate w0 Q hrb j.val j.isLt
            have hdin : ∀ h ∈ (Q.gates[j.val]).inputs, (depthList w0 Q.gates).getD h 0 ≤ 1 := fun h hh => by
              have hle : (((Q.gates[j.val]).inputs.map (fun i => (depthList w0 Q.gates).getD i 0)).foldr max 0) ≤ 1 := by
                omega
              exact (foldr_max_le_iff _ 1).mp hle _ (List.mem_map.mpr ⟨h, hh, rfl⟩)
            have hlt_in : ∀ h ∈ (Q.gates[j.val]).inputs, h < w0 + j.val := fun h hh => by
              have h1 := hrb j.val j.isLt h
              unfold gateAt at h1
              simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem j.isLt, Option.getD_some] at h1
              exact h1 hh
            have hfl : (Q.gates[j.val]).inputs.length ≤ 2 := hfan Q.gates[j.val] (List.getElem_mem j.isLt)
            cases hin : (Q.gates[j.val]).inputs with
            | nil =>
              refine ⟨fun _ => b2z ((Q.gates[j.val]).op.eval []), fun _ => 0, fun _ => 0, fun u v => ?_⟩
              rw [wireList_gate w0 Q hrb (oneEach u v) (oneEach_length u v) j.val j.isLt, hin]
              simp
            | cons i1 tl =>
              cases tl with
              | nil =>
                have hi1_lt : i1 < w0 + j.val := hlt_in i1 (by rw [hin]; simp)
                obtain ⟨R1, C1, lam1, h1⟩ := ih i1 (by omega) (by omega) (hdin i1 (by rw [hin]; simp))
                let c0 := b2z ((Q.gates[j.val]).op.eval [false])
                let c1 := b2z ((Q.gates[j.val]).op.eval [false]) + b2z ((Q.gates[j.val]).op.eval [true])
                refine ⟨fun u => c0 + c1 * R1 u, fun v => c1 * C1 v, fun j' => c1 * lam1 j', fun u v => ?_⟩
                rw [wireList_gate w0 Q hrb (oneEach u v) (oneEach_length u v) j.val j.isLt, hin]
                simp only [List.map_cons, List.map_nil]
                rw [gate_anf_one, h1 u v]
                change c0 + c1 * (R1 u + C1 v + ∑ j' : N1, lam1 j' * (pL j' u * qL j' v + pR j' u * qR j' v)) =
                  (c0 + c1 * R1 u) + c1 * C1 v + ∑ j' : N1, (c1 * lam1 j') * (pL j' u * qL j' v + pR j' u * qR j' v)
                rw [mul_add, mul_add, Finset.mul_sum]
                simp_rw [mul_assoc]
                ac_rfl
              | cons i2 tl2 =>
                cases tl2 with
                | nil =>
                  have hi1_lt : i1 < w0 + j.val := hlt_in i1 (by rw [hin]; simp)
                  have hi2_lt : i2 < w0 + j.val := hlt_in i2 (by rw [hin]; simp)
                  obtain ⟨R1, C1, lam1, h1⟩ := ih i1 (by omega) (by omega) (hdin i1 (by rw [hin]; simp))
                  obtain ⟨R2, C2, lam2, h2⟩ := ih i2 (by omega) (by omega) (hdin i2 (by rw [hin]; simp))
                  have hxor0 : xor (xor ((Q.gates[j.val]).op.eval [false, false]) ((Q.gates[j.val]).op.eval [false, true]))
                      (xor ((Q.gates[j.val]).op.eval [true, false]) ((Q.gates[j.val]).op.eval [true, true])) = false := by
                    unfold nonlinear at hnlf
                    rw [hin] at hnlf
                    simpa using hnlf
                  let c0 := b2z ((Q.gates[j.val]).op.eval [false, false])
                  let c1 := b2z ((Q.gates[j.val]).op.eval [false, false]) + b2z ((Q.gates[j.val]).op.eval [true, false])
                  let c2 := b2z ((Q.gates[j.val]).op.eval [false, false]) + b2z ((Q.gates[j.val]).op.eval [false, true])
                  refine ⟨fun u => c0 + c1 * R1 u + c2 * R2 u, fun v => c1 * C1 v + c2 * C2 v,
                    fun j' => c1 * lam1 j' + c2 * lam2 j', fun u v => ?_⟩
                  rw [wireList_gate w0 Q hrb (oneEach u v) (oneEach_length u v) j.val j.isLt, hin]
                  simp only [List.map_cons, List.map_nil]
                  rw [gate_anf_two, hxor0, h1 u v, h2 u v]
                  change c0 + c1 * (R1 u + C1 v + ∑ j' : N1, lam1 j' * (pL j' u * qL j' v + pR j' u * qR j' v)) +
                    c2 * (R2 u + C2 v + ∑ j' : N1, lam2 j' * (pL j' u * qL j' v + pR j' u * qR j' v)) + 0 * _ =
                    (c0 + c1 * R1 u + c2 * R2 u) + (c1 * C1 v + c2 * C2 v) +
                    ∑ j' : N1, (c1 * lam1 j' + c2 * lam2 j') * (pL j' u * qL j' v + pR j' u * qR j' v)
                  rw [zero_mul, add_zero, mul_add, mul_add, mul_add, mul_add, Finset.mul_sum, Finset.mul_sum]
                  simp_rw [add_mul, Finset.sum_add_distrib, mul_assoc]
                  ac_rfl
                | cons _ _ =>
                  rw [hin] at hfl; simp at hfl
    obtain ⟨R, C, lam, hOut⟩ := hwire_span Q.output hout hdep
    let e : N1 ≃ Fin N1.card := Fintype.equivFinOfCardEq (Fintype.card_coe N1)
    let U : Fin (m + 1) → Fin (2 * t) → F := fun u k =>
      if hk : k.val < 2 * N1.card then
        let idx : Fin N1.card := ⟨k.val / 2, by omega⟩
        if k.val % 2 = 0 then lam (e.symm idx) * pL (e.symm idx) u
        else lam (e.symm idx) * pR (e.symm idx) u
      else 0
    let V : Fin n → Fin (2 * t) → F := fun v k =>
      if hk : k.val < 2 * N1.card then
        let idx : Fin N1.card := ⟨k.val / 2, by omega⟩
        if k.val % 2 = 0 then qL (e.symm idx) v
        else qR (e.symm idx) v
      else 0
    refine ⟨R, C, U, V, fun u v => ?_⟩
    have hP : P u v = (wireList Q.gates (oneEach u v)).getD Q.output false := (hrep u v).symm
    rw [hP, hOut u v]
    congr 1
    have hsum_eq : ∑ j : N1, lam j * (pL j u * qL j v + pR j u * qR j v) =
        ∑ idx : Fin N1.card, (lam (e.symm idx) * (pL (e.symm idx) u * qL (e.symm idx) v +
          pR (e.symm idx) u * qR (e.symm idx) v)) := by
      exact (Equiv.sum_comp e.symm _).symm
    rw [hsum_eq]
    have hsplit : ∑ k : Fin (2 * t), U u k * V v k =
        ∑ k ∈ (Finset.univ : Finset (Fin (2 * t))).filter (fun k => k.val < 2 * N1.card), U u k * V v k := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro k _ hk
      have hnot : ¬ k.val < 2 * N1.card := fun h => hk (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      simp [U, V, hnot]
    rw [hsplit]
    let evens := (Finset.univ : Finset (Fin (2 * t))).filter (fun k => k.val < 2 * N1.card ∧ k.val % 2 = 0)
    let odds := (Finset.univ : Finset (Fin (2 * t))).filter (fun k => k.val < 2 * N1.card ∧ k.val % 2 ≠ 0)
    have hdisj : Disjoint evens odds := by
      rw [Finset.disjoint_filter]; intro _ _ h1 h2; exact h2.2 h1.2
    have hunion : evens ∪ odds = (Finset.univ : Finset (Fin (2 * t))).filter (fun k => k.val < 2 * N1.card) := by
      ext k; simp only [evens, odds, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases h : k.val % 2 = 0 <;> simp [h]
    rw [← hunion, Finset.sum_union hdisj]
    have hev : ∑ k ∈ evens, U u k * V v k = ∑ idx : Fin N1.card, lam (e.symm idx) * pL (e.symm idx) u * qL (e.symm idx) v := by
      symm
      apply Finset.sum_bij (fun idx _ => (⟨2 * idx.val, by omega⟩ : Fin (2 * t)))
      · intro idx _
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only; omega, by dsimp only; omega⟩
      · intro i1 _ i2 _ heq
        have hv : 2 * i1.val = 2 * i2.val := congrArg Fin.val heq
        exact Fin.ext (by omega)
      · intro k hk
        have h1 := (Finset.mem_filter.mp hk).2
        refine ⟨⟨k.val / 2, by omega⟩, Finset.mem_univ _, Fin.ext (by dsimp only; omega)⟩
      · intro idx _
        have h1 : 2 * idx.val < 2 * N1.card := by omega
        have h2 : (2 * idx.val) % 2 = 0 := by omega
        have h3 : (⟨(2 * idx.val) / 2, by omega⟩ : Fin N1.card) = idx := Fin.ext (by dsimp only; omega)
        simp only [U, V, h1, dite_true, h2, ite_true, h3]
    have hod : ∑ k ∈ odds, U u k * V v k = ∑ idx : Fin N1.card, lam (e.symm idx) * pR (e.symm idx) u * qR (e.symm idx) v := by
      symm
      apply Finset.sum_bij (fun idx _ => (⟨2 * idx.val + 1, by omega⟩ : Fin (2 * t)))
      · intro idx _
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only; omega, by dsimp only; omega⟩
      · intro i1 _ i2 _ heq
        have hv : 2 * i1.val + 1 = 2 * i2.val + 1 := congrArg Fin.val heq
        exact Fin.ext (by omega)
      · intro k hk
        have h1 := (Finset.mem_filter.mp hk).2
        refine ⟨⟨k.val / 2, by omega⟩, Finset.mem_univ _, Fin.ext (by dsimp only; omega)⟩
      · intro idx _
        have h1 : 2 * idx.val + 1 < 2 * N1.card := by omega
        have h2 : (2 * idx.val + 1) % 2 ≠ 0 := by omega
        have h3 : (⟨(2 * idx.val + 1) / 2, by omega⟩ : Fin N1.card) = idx := Fin.ext (by dsimp only; omega)
        simp only [U, V, h1, dite_true, h2, ite_false, h3]
    rw [hev, hod, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro idx _
    rw [mul_add, mul_assoc, mul_assoc]
  · refine ⟨fun _ => 0, fun _ => 0, fun _ _ => 0, fun _ _ => 0, fun u v => ?_⟩
    have hP : P u v = (wireList Q.gates (oneEach u v)).getD Q.output false := (hrep u v).symm
    have hge : (wireList Q.gates (oneEach u v)).length ≤ Q.output := by
      rw [wireList_length, oneEach_length]; omega
    have hfalse : (wireList Q.gates (oneEach u v)).getD Q.output false = false := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]
    rw [hP, hfalse]
    simp [b2z]

structure Builder (m n : ℕ) where
  gates : List Gate
  hfan : ∀ g ∈ gates, g.inputs.length ≤ 2
  hrb : ReadsBack (m + 1 + n) ⟨gates, 0⟩

def Builder.empty (m n : ℕ) : Builder m n where
  gates := []
  hfan := by simp
  hrb := by intro j hj; simp at hj

def Builder.pushGate {m n : ℕ} (B : Builder m n) (g : Gate)
    (hgf : g.inputs.length ≤ 2) (hgrb : ∀ i ∈ g.inputs, i < m + 1 + n + B.gates.length) :
    Builder m n where
  gates := B.gates ++ [g]
  hfan := by
    intro g' hg'
    rcases List.mem_append.mp hg' with h | h
    · exact B.hfan g' h
    · simp only [List.mem_singleton] at h; subst h; exact hgf
  hrb := by
    intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < B.gates.length
    · have hget : gateAt ⟨B.gates ++ [g], 0⟩ j = gateAt ⟨B.gates, 0⟩ j := by
        unfold gateAt; exact list_getD_append_left B.gates [g] j _ hlt
      rw [hget] at hi
      exact B.hrb j hlt i hi
    · have heq : j = B.gates.length := by omega
      subst heq
      have hget : gateAt ⟨B.gates ++ [g], 0⟩ B.gates.length = g := by
        unfold gateAt; exact list_getD_append_right_singleton B.gates g _
      rw [hget] at hi
      exact hgrb i hi

lemma pushGate_val {m n : ℕ} (B : Builder m n) (g : Gate)
    (hgf : g.inputs.length ≤ 2) (hgrb : ∀ i ∈ g.inputs, i < m + 1 + n + B.gates.length)
    (u : Fin (m + 1)) (v : Fin n) :
    (wireList (B.pushGate g hgf hgrb).gates (oneEach u v)).getD (m + 1 + n + B.gates.length) false =
      g.op.eval (g.inputs.map (fun h => (wireList B.gates (oneEach u v)).getD h false)) := by
  have hstep : wireList (B.gates ++ [g]) (oneEach u v) =
      wireList B.gates (oneEach u v) ++
        [g.op.eval (g.inputs.map (fun h => (wireList B.gates (oneEach u v)).getD h false))] := by
    simp [wireList, List.foldl_append]
  change (wireList (B.gates ++ [g]) (oneEach u v)).getD (m + 1 + n + B.gates.length) false = _
  rw [hstep]
  have hlen : m + 1 + n + B.gates.length = (wireList B.gates (oneEach u v)).length := by
    rw [wireList_length, oneEach_length]
  rw [hlen, list_getD_append_right_singleton]

lemma pushGate_depth {m n : ℕ} (B : Builder m n) (g : Gate)
    (hgf : g.inputs.length ≤ 2) (hgrb : ∀ i ∈ g.inputs, i < m + 1 + n + B.gates.length) :
    (depthList (m + 1 + n) (B.pushGate g hgf hgrb).gates).getD (m + 1 + n + B.gates.length) 0 =
      (g.inputs.map (fun h => (depthList (m + 1 + n) B.gates).getD h 0)).foldr max 0 + (nonlinear g).toNat := by
  have hstep : depthList (m + 1 + n) (B.gates ++ [g]) =
      depthList (m + 1 + n) B.gates ++
        [(g.inputs.map (fun h => (depthList (m + 1 + n) B.gates).getD h 0)).foldr max 0 + (nonlinear g).toNat] := by
    simp [depthList, List.foldl_append]
  change (depthList (m + 1 + n) (B.gates ++ [g])).getD (m + 1 + n + B.gates.length) 0 = _
  rw [hstep]
  have hlen : m + 1 + n + B.gates.length = (depthList (m + 1 + n) B.gates).length := by
    rw [depthList_length]
  rw [hlen, list_getD_append_right_singleton]

lemma pushGate_old_val {m n : ℕ} (B : Builder m n) (g : Gate)
    (hgf : g.inputs.length ≤ 2) (hgrb : ∀ i ∈ g.inputs, i < m + 1 + n + B.gates.length)
    (k : ℕ) (hk : k < m + 1 + n + B.gates.length) (u : Fin (m + 1)) (v : Fin n) :
    (wireList (B.pushGate g hgf hgrb).gates (oneEach u v)).getD k false =
      (wireList B.gates (oneEach u v)).getD k false := by
  exact wireList_append_getD B.gates [g] (oneEach u v) k (by rw [oneEach_length]; exact hk)

lemma pushGate_old_depth {m n : ℕ} (B : Builder m n) (g : Gate)
    (hgf : g.inputs.length ≤ 2) (hgrb : ∀ i ∈ g.inputs, i < m + 1 + n + B.gates.length)
    (k : ℕ) (hk : k < m + 1 + n + B.gates.length) :
    (depthList (m + 1 + n) (B.pushGate g hgf hgrb).gates).getD k 0 =
      (depthList (m + 1 + n) B.gates).getD k 0 := by
  exact depthList_append_getD (m + 1 + n) B.gates [g] k hk

lemma pushGate_countP {m n : ℕ} (B : Builder m n) (g : Gate)
    (hgf : g.inputs.length ≤ 2) (hgrb : ∀ i ∈ g.inputs, i < m + 1 + n + B.gates.length) :
    (B.pushGate g hgf hgrb).gates.countP nonlinear = B.gates.countP nonlinear + (nonlinear g).toNat := by
  change (B.gates ++ [g]).countP nonlinear = _
  rw [List.countP_append, List.countP_singleton]
  cases nonlinear g <;> simp

lemma nonlinear_or_nil : nonlinear ⟨GateOp.or, []⟩ = false := rfl
lemma nonlinear_mod2 (i j : ℕ) : nonlinear ⟨GateOp.mod 2, [i, j]⟩ = false := rfl
lemma nonlinear_not (i : ℕ) : nonlinear ⟨GateOp.not, [i]⟩ = false := rfl
lemma nonlinear_and (i j : ℕ) : nonlinear ⟨GateOp.and, [i, j]⟩ = true := rfl

lemma eval_not_mod2 (a b : Bool) : GateOp.not.eval [GateOp.mod 2 |>.eval [a, b]] = xor a b := by
  cases a <;> cases b <;> decide

lemma eval_and2 (a b : Bool) : GateOp.and.eval [a, b] = (a && b) := by
  cases a <;> cases b <;> decide

lemma build_const_false {m n : ℕ} (B : Builder m n) :
    ∃ (B' : Builder m n) (w : ℕ),
      (∃ ext, B'.gates = B.gates ++ ext) ∧
      w < m + 1 + n + B'.gates.length ∧
      B'.gates.countP nonlinear = B.gates.countP nonlinear ∧
      (depthList (m + 1 + n) B'.gates).getD w 0 = 0 ∧
      ∀ (u : Fin (m + 1)) (v : Fin n), (wireList B'.gates (oneEach u v)).getD w false = false := by
  let g : Gate := ⟨GateOp.or, []⟩
  have hgf : g.inputs.length ≤ 2 := by simp [g]
  have hgrb : ∀ i ∈ g.inputs, i < m + 1 + n + B.gates.length := by simp [g]
  let B' := B.pushGate g hgf hgrb
  refine ⟨B', m + 1 + n + B.gates.length, ⟨[g], rfl⟩, by simp [B', Builder.pushGate], ?_, ?_, ?_⟩
  · rw [pushGate_countP, nonlinear_or_nil]; simp
  · rw [pushGate_depth, nonlinear_or_nil]; simp [g]
  · intro u v; rw [pushGate_val]; rfl

lemma build_xor {m n : ℕ} (B : Builder m n) (i j : ℕ)
    (hi : i < m + 1 + n + B.gates.length) (hj : j < m + 1 + n + B.gates.length) :
    ∃ (B' : Builder m n) (w : ℕ),
      (∃ ext, B'.gates = B.gates ++ ext) ∧
      w < m + 1 + n + B'.gates.length ∧
      B'.gates.countP nonlinear = B.gates.countP nonlinear ∧
      (depthList (m + 1 + n) B'.gates).getD w 0 =
        max ((depthList (m + 1 + n) B.gates).getD i 0) ((depthList (m + 1 + n) B.gates).getD j 0) ∧
      ∀ (u : Fin (m + 1)) (v : Fin n), (wireList B'.gates (oneEach u v)).getD w false =
        xor ((wireList B.gates (oneEach u v)).getD i false) ((wireList B.gates (oneEach u v)).getD j false) := by
  let g1 : Gate := ⟨GateOp.mod 2, [i, j]⟩
  have hg1f : g1.inputs.length ≤ 2 := by simp [g1]
  have hg1rb : ∀ h ∈ g1.inputs, h < m + 1 + n + B.gates.length := by
    intro h hh; simp only [g1, List.mem_cons, List.not_mem_nil, or_false] at hh
    rcases hh with rfl | rfl <;> assumption
  let B1 := B.pushGate g1 hg1f hg1rb
  let w1 := m + 1 + n + B.gates.length
  let g2 : Gate := ⟨GateOp.not, [w1]⟩
  have hg2f : g2.inputs.length ≤ 2 := by simp [g2]
  have hg2rb : ∀ h ∈ g2.inputs, h < m + 1 + n + B1.gates.length := by
    intro h hh; simp only [g2, List.mem_singleton] at hh; subst hh
    simp [B1, Builder.pushGate, w1]
  let B2 := B1.pushGate g2 hg2f hg2rb
  let w2 := m + 1 + n + B1.gates.length
  refine ⟨B2, w2, ⟨[g1, g2], by simp [B2, B1, Builder.pushGate, List.append_assoc]⟩,
    by simp [B2, Builder.pushGate, w2], ?_, ?_, ?_⟩
  · rw [pushGate_countP, pushGate_countP, nonlinear_mod2, nonlinear_not]; simp
  · rw [pushGate_depth, nonlinear_not]
    simp only [g2, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Nat.max_zero, Bool.toNat_false, add_zero]
    rw [pushGate_depth, nonlinear_mod2]
    simp [g1]
  · intro u v
    rw [pushGate_val]
    simp only [g2, List.map_cons, List.map_nil]
    rw [pushGate_val]
    simp only [g1, List.map_cons, List.map_nil]
    exact eval_not_mod2 _ _

lemma build_and {m n : ℕ} (B : Builder m n) (i j : ℕ)
    (hi : i < m + 1 + n + B.gates.length) (hj : j < m + 1 + n + B.gates.length) :
    ∃ (B' : Builder m n) (w : ℕ),
      (∃ ext, B'.gates = B.gates ++ ext) ∧
      w < m + 1 + n + B'.gates.length ∧
      B'.gates.countP nonlinear = B.gates.countP nonlinear + 1 ∧
      (depthList (m + 1 + n) B'.gates).getD w 0 =
        max ((depthList (m + 1 + n) B.gates).getD i 0) ((depthList (m + 1 + n) B.gates).getD j 0) + 1 ∧
      ∀ (u : Fin (m + 1)) (v : Fin n), (wireList B'.gates (oneEach u v)).getD w false =
        (((wireList B.gates (oneEach u v)).getD i false) && ((wireList B.gates (oneEach u v)).getD j false)) := by
  let g : Gate := ⟨GateOp.and, [i, j]⟩
  have hgf : g.inputs.length ≤ 2 := by simp [g]
  have hgrb : ∀ h ∈ g.inputs, h < m + 1 + n + B.gates.length := by
    intro h hh; simp only [g, List.mem_cons, List.not_mem_nil, or_false] at hh
    rcases hh with rfl | rfl <;> assumption
  let B' := B.pushGate g hgf hgrb
  let w := m + 1 + n + B.gates.length
  refine ⟨B', w, ⟨[g], rfl⟩, by simp [B', Builder.pushGate, w], ?_, ?_, ?_⟩
  · rw [pushGate_countP, nonlinear_and]; simp
  · rw [pushGate_depth, nonlinear_and]; simp [g]
  · intro u v
    rw [pushGate_val]
    simp only [g, List.map_cons, List.map_nil]
    exact eval_and2 _ _

lemma build_xor_wires {m n : ℕ} (B : Builder m n) (ws : List ℕ)
    (hws : ∀ i ∈ ws, i < m + 1 + n + B.gates.length)
    (hd : ∀ i ∈ ws, (depthList (m + 1 + n) B.gates).getD i 0 = 0) :
    ∃ (B' : Builder m n) (w : ℕ),
      (∃ ext, B'.gates = B.gates ++ ext) ∧
      w < m + 1 + n + B'.gates.length ∧
      B'.gates.countP nonlinear = B.gates.countP nonlinear ∧
      (depthList (m + 1 + n) B'.gates).getD w 0 = 0 ∧
      ∀ (u : Fin (m + 1)) (v : Fin n), b2z ((wireList B'.gates (oneEach u v)).getD w false) =
        (ws.map (fun i => b2z ((wireList B.gates (oneEach u v)).getD i false))).sum := by
  induction ws generalizing B with
  | nil =>
    obtain ⟨B', w, hext, hw, hcnt, hdw, hval⟩ := build_const_false B
    refine ⟨B', w, hext, hw, hcnt, hdw, fun u v => ?_⟩
    rw [hval u v]; rfl
  | cons i tl ih =>
    have hi_lt : i < m + 1 + n + B.gates.length := hws i (List.mem_cons_self ..)
    have hi_d0 : (depthList (m + 1 + n) B.gates).getD i 0 = 0 := hd i (List.mem_cons_self ..)
    obtain ⟨B1, w1, ⟨ext1, hext1⟩, hw1, hcnt1, hdw1, hval1⟩ :=
      ih B (fun x hx => hws x (List.mem_cons_of_mem i hx)) (fun x hx => hd x (List.mem_cons_of_mem i hx))
    have hi_lt1 : i < m + 1 + n + B1.gates.length := by rw [hext1, List.length_append]; omega
    obtain ⟨B2, w2, ⟨ext2, hext2⟩, hw2, hcnt2, hdw2, hval2⟩ := build_xor B1 i w1 hi_lt1 hw1
    refine ⟨B2, w2, ⟨ext1 ++ ext2, by rw [hext2, hext1, List.append_assoc]⟩, hw2,
      hcnt2.trans hcnt1, ?_, fun u v => ?_⟩
    · rw [hdw2, hdw1]
      have hdi1 : (depthList (m + 1 + n) B1.gates).getD i 0 = 0 := by
        rw [hext1, depthList_append_getD _ B.gates ext1 i hi_lt]; exact hi_d0
      rw [hdi1]; rfl
    · rw [hval2 u v, b2z_xor, hval1 u v]
      have hvi1 : (wireList B1.gates (oneEach u v)).getD i false = (wireList B.gates (oneEach u v)).getD i false := by
        rw [hext1, wireList_append_getD B.gates ext1 (oneEach u v) i (by rw [oneEach_length]; exact hi_lt)]
      rw [hvi1]; rfl

lemma list_sum_map_eq_toFinset {α : Type*} [DecidableEq α] (l : List α) (hnd : l.Nodup) (f : α → F) :
    (l.map f).sum = ∑ x ∈ l.toFinset, f x := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.nodup_cons] at hnd
    simp only [List.map_cons, List.sum_cons, List.toFinset_cons,
      Finset.sum_insert (show a ∉ l.toFinset by simpa [List.mem_toFinset] using hnd.1)]
    rw [ih hnd.2]

lemma build_row_fn {m n : ℕ} (B : Builder m n) (f : Fin (m + 1) → F) :
    ∃ (B' : Builder m n) (w : ℕ),
      (∃ ext, B'.gates = B.gates ++ ext) ∧
      w < m + 1 + n + B'.gates.length ∧
      B'.gates.countP nonlinear = B.gates.countP nonlinear ∧
      (depthList (m + 1 + n) B'.gates).getD w 0 = 0 ∧
      ∀ (u : Fin (m + 1)) (v : Fin n), b2z ((wireList B'.gates (oneEach u v)).getD w false) = f u := by
  let ws : List ℕ := ((List.finRange (m + 1)).filter (fun i => decide (f i = 1))).map Fin.val
  have hws : ∀ i ∈ ws, i < m + 1 + n + B.gates.length := by
    intro i hi
    rcases List.mem_map.mp hi with ⟨idx, _, rfl⟩
    omega
  have hd : ∀ i ∈ ws, (depthList (m + 1 + n) B.gates).getD i 0 = 0 := by
    intro i hi
    rcases List.mem_map.mp hi with ⟨idx, _, rfl⟩
    exact depthList_input (m + 1 + n) B.gates idx.val (by omega)
  obtain ⟨B', w, hext, hw, hcnt, hdw, hval⟩ := build_xor_wires B ws hws hd
  refine ⟨B', w, hext, hw, hcnt, hdw, fun u v => ?_⟩
  rw [hval u v]
  have hsum : (ws.map (fun i => b2z ((wireList B.gates (oneEach u v)).getD i false))).sum =
      ∑ idx : Fin (m + 1), if f idx = 1 then b2z (decide (idx.val = u.val)) else 0 := by
    have hmap : ws.map (fun i => b2z ((wireList B.gates (oneEach u v)).getD i false)) =
        ((List.finRange (m + 1)).filter (fun idx => decide (f idx = 1))).map
          (fun idx => b2z (decide (idx.val = u.val))) := by
      simp only [ws, List.map_map]
      apply List.map_congr_left
      intro idx _
      simp only [Function.comp_apply]
      rw [wireList_input B.gates (oneEach u v) idx.val (by rw [oneEach_length]; omega),
        oneEach_getD_left u v idx.val idx.isLt]
    rw [hmap]
    have hnodup : ((List.finRange (m + 1)).filter (fun idx => decide (f idx = 1))).Nodup :=
      (List.nodup_finRange (m + 1)).filter _
    have htoFinset : (((List.finRange (m + 1)).filter (fun idx => decide (f idx = 1))).map
        (fun idx => b2z (decide (idx.val = u.val)))).sum =
        ∑ idx ∈ ((List.finRange (m + 1)).filter (fun idx => decide (f idx = 1))).toFinset,
          b2z (decide (idx.val = u.val)) :=
      list_sum_map_eq_toFinset _ hnodup _
    rw [htoFinset]
    have hfilt : ((List.finRange (m + 1)).filter (fun idx => decide (f idx = 1))).toFinset =
        (Finset.univ : Finset (Fin (m + 1))).filter (fun idx => f idx = 1) := by
      ext idx; simp
    rw [hfilt, Finset.sum_filter]
  rw [hsum, Finset.sum_eq_single u]
  · simp only [decide_true, b2z, ite_true]
    rcases f_cases (f u) with h | h <;> simp [h]
  · intro idx _ hne
    have hne' : idx.val ≠ u.val := fun h => hne (Fin.ext h)
    simp [hne', b2z]
  · intro hni; exact (hni (Finset.mem_univ _)).elim

lemma build_col_fn {m n : ℕ} (B : Builder m n) (g : Fin n → F) :
    ∃ (B' : Builder m n) (w : ℕ),
      (∃ ext, B'.gates = B.gates ++ ext) ∧
      w < m + 1 + n + B'.gates.length ∧
      B'.gates.countP nonlinear = B.gates.countP nonlinear ∧
      (depthList (m + 1 + n) B'.gates).getD w 0 = 0 ∧
      ∀ (u : Fin (m + 1)) (v : Fin n), b2z ((wireList B'.gates (oneEach u v)).getD w false) = g v := by
  let ws : List ℕ := ((List.finRange n).filter (fun j => decide (g j = 1))).map (fun j => m + 1 + j.val)
  have hws : ∀ i ∈ ws, i < m + 1 + n + B.gates.length := by
    intro i hi
    rcases List.mem_map.mp hi with ⟨idx, _, rfl⟩
    omega
  have hd : ∀ i ∈ ws, (depthList (m + 1 + n) B.gates).getD i 0 = 0 := by
    intro i hi
    rcases List.mem_map.mp hi with ⟨idx, _, rfl⟩
    exact depthList_input (m + 1 + n) B.gates (m + 1 + idx.val) (by omega)
  obtain ⟨B', w, hext, hw, hcnt, hdw, hval⟩ := build_xor_wires B ws hws hd
  refine ⟨B', w, hext, hw, hcnt, hdw, fun u v => ?_⟩
  rw [hval u v]
  have hsum : (ws.map (fun i => b2z ((wireList B.gates (oneEach u v)).getD i false))).sum =
      ∑ idx : Fin n, if g idx = 1 then b2z (decide (idx.val = v.val)) else 0 := by
    have hmap : ws.map (fun i => b2z ((wireList B.gates (oneEach u v)).getD i false)) =
        ((List.finRange n).filter (fun idx => decide (g idx = 1))).map
          (fun idx => b2z (decide (idx.val = v.val))) := by
      simp only [ws, List.map_map]
      apply List.map_congr_left
      intro idx _
      simp only [Function.comp_apply]
      rw [wireList_input B.gates (oneEach u v) (m + 1 + idx.val) (by rw [oneEach_length]; omega),
        oneEach_getD_right u v (m + 1 + idx.val) (by omega) (by omega)]
      have hsub : m + 1 + idx.val - (m + 1) = idx.val := by omega
      rw [hsub]
    rw [hmap]
    have hnodup : ((List.finRange n).filter (fun idx => decide (g idx = 1))).Nodup :=
      (List.nodup_finRange n).filter _
    have htoFinset : (((List.finRange n).filter (fun idx => decide (g idx = 1))).map
        (fun idx => b2z (decide (idx.val = v.val)))).sum =
        ∑ idx ∈ ((List.finRange n).filter (fun idx => decide (g idx = 1))).toFinset,
          b2z (decide (idx.val = v.val)) :=
      list_sum_map_eq_toFinset _ hnodup _
    rw [htoFinset]
    have hfilt : ((List.finRange n).filter (fun idx => decide (g idx = 1))).toFinset =
        (Finset.univ : Finset (Fin n)).filter (fun idx => g idx = 1) := by
      ext idx; simp
    rw [hfilt, Finset.sum_filter]
  rw [hsum, Finset.sum_eq_single v]
  · simp only [decide_true, b2z, ite_true]
    rcases f_cases (g v) with h | h <;> simp [h]
  · intro idx _ hne
    have hne' : idx.val ≠ v.val := fun h => hne (Fin.ext h)
    simp [hne', b2z]
  · intro hni; exact (hni (Finset.mem_univ _)).elim

lemma build_pair_term {m n : ℕ} (B : Builder m n)
    (u1 u2 : Fin (m + 1) → F) (v1 v2 : Fin n → F) :
    ∃ (B' : Builder m n) (w : ℕ),
      (∃ ext, B'.gates = B.gates ++ ext) ∧
      w < m + 1 + n + B'.gates.length ∧
      B'.gates.countP nonlinear = B.gates.countP nonlinear + 1 ∧
      (depthList (m + 1 + n) B'.gates).getD w 0 = 1 ∧
      ∀ (u : Fin (m + 1)) (v : Fin n), b2z ((wireList B'.gates (oneEach u v)).getD w false) =
        (u1 u + v2 v) * (u2 u + v1 v) := by
  obtain ⟨B1, wu1, ⟨e1, he1⟩, hwu1, hc1, hdu1, hvu1⟩ := build_row_fn B u1
  obtain ⟨B2, wv2, ⟨e2, he2⟩, hwv2, hc2, hdv2, hvv2⟩ := build_col_fn B1 v2
  have hwu1_2 : wu1 < m + 1 + n + B2.gates.length := by rw [he2, List.length_append]; omega
  obtain ⟨B3, wx, ⟨e3, he3⟩, hwx, hc3, hdx, hvx⟩ := build_xor B2 wu1 wv2 hwu1_2 hwv2
  obtain ⟨B4, wu2, ⟨e4, he4⟩, hwu2, hc4, hdu2, hvu2⟩ := build_row_fn B3 u2
  obtain ⟨B5, wv1, ⟨e5, he5⟩, hwv1, hc5, hdv1, hvv1⟩ := build_col_fn B4 v1
  have hwu2_5 : wu2 < m + 1 + n + B5.gates.length := by rw [he5, List.length_append]; omega
  obtain ⟨B6, wy, ⟨e6, he6⟩, hwy, hc6, hdy, hvy⟩ := build_xor B5 wu2 wv1 hwu2_5 hwv1
  have hwx_6 : wx < m + 1 + n + B6.gates.length := by
    rw [he6, he5, he4, List.length_append, List.length_append, List.length_append]; omega
  obtain ⟨B7, wz, ⟨e7, he7⟩, hwz, hc7, hdz, hvz⟩ := build_and B6 wx wy hwx_6 hwy
  have hdx0 : (depthList (m + 1 + n) B3.gates).getD wx 0 = 0 := by
    rw [hdx, hdv2, he2, depthList_append_getD _ B1.gates e2 wu1 hwu1, hdu1]; rfl
  have hdy0 : (depthList (m + 1 + n) B6.gates).getD wy 0 = 0 := by
    rw [hdy, hdv1, he5, depthList_append_getD _ B4.gates e5 wu2 hwu2, hdu2]; rfl
  have hdx6 : (depthList (m + 1 + n) B6.gates).getD wx 0 = 0 := by
    have he36 : B6.gates = B3.gates ++ (e4 ++ e5 ++ e6) := by
      rw [he6, he5, he4]; simp [List.append_assoc]
    rw [he36, depthList_append_getD _ B3.gates _ wx hwx]; exact hdx0
  refine ⟨B7, wz, ⟨e1 ++ e2 ++ e3 ++ e4 ++ e5 ++ e6 ++ e7, by
    rw [he7, he6, he5, he4, he3, he2, he1]; simp [List.append_assoc]⟩, hwz, ?_, ?_, fun u v => ?_⟩
  · omega
  · rw [hdz, hdx6, hdy0]; rfl
  · rw [hvz u v, b2z_and]
    have h1 : (wireList B6.gates (oneEach u v)).getD wx false = (wireList B3.gates (oneEach u v)).getD wx false := by
      have he36 : B6.gates = B3.gates ++ (e4 ++ e5 ++ e6) := by
        rw [he6, he5, he4]; simp [List.append_assoc]
      rw [he36, wireList_append_getD B3.gates _ (oneEach u v) wx (by rw [oneEach_length]; exact hwx)]
    rw [h1, hvx u v, hvy u v, b2z_xor, b2z_xor, hvv2 u v, hvv1 u v]
    have h2 : (wireList B2.gates (oneEach u v)).getD wu1 false = (wireList B1.gates (oneEach u v)).getD wu1 false := by
      rw [he2, wireList_append_getD B1.gates e2 (oneEach u v) wu1 (by rw [oneEach_length]; exact hwu1)]
    have h3 : (wireList B5.gates (oneEach u v)).getD wu2 false = (wireList B4.gates (oneEach u v)).getD wu2 false := by
      rw [he5, wireList_append_getD B4.gates e5 (oneEach u v) wu2 (by rw [oneEach_length]; exact hwu2)]
    rw [h2, h3, hvu1 u v, hvu2 u v]

lemma build_pairs_sum {m n : ℕ} (k : ℕ) (B : Builder m n) (wAcc : ℕ)
    (hwAcc : wAcc < m + 1 + n + B.gates.length)
    (hdAcc : (depthList (m + 1 + n) B.gates).getD wAcc 0 ≤ 1)
    (U1 U2 : Fin k → Fin (m + 1) → F) (V1 V2 : Fin k → Fin n → F) :
    ∃ (B' : Builder m n) (w : ℕ),
      (∃ ext, B'.gates = B.gates ++ ext) ∧
      w < m + 1 + n + B'.gates.length ∧
      B'.gates.countP nonlinear = B.gates.countP nonlinear + k ∧
      (depthList (m + 1 + n) B'.gates).getD w 0 ≤ 1 ∧
      ∀ (u : Fin (m + 1)) (v : Fin n), b2z ((wireList B'.gates (oneEach u v)).getD w false) =
        b2z ((wireList B.gates (oneEach u v)).getD wAcc false) +
          ∑ j : Fin k, (U1 j u + V2 j v) * (U2 j u + V1 j v) := by
  induction k generalizing B wAcc with
  | zero =>
    refine ⟨B, wAcc, ⟨[], by simp⟩, hwAcc, by simp, hdAcc, fun u v => by simp⟩
  | succ k ih =>
    obtain ⟨B1, w1, ⟨e1, he1⟩, hw1, hc1, hd1, hv1⟩ :=
      build_pair_term B (U1 0) (U2 0) (V1 0) (V2 0)
    have hwAcc1 : wAcc < m + 1 + n + B1.gates.length := by rw [he1, List.length_append]; omega
    obtain ⟨B2, w2, ⟨e2, he2⟩, hw2, hc2, hd2, hv2⟩ := build_xor B1 wAcc w1 hwAcc1 hw1
    have hd2_le : (depthList (m + 1 + n) B2.gates).getD w2 0 ≤ 1 := by
      rw [hd2, hd1, he1, depthList_append_getD _ B.gates e1 wAcc hwAcc]; omega
    obtain ⟨B3, w3, ⟨e3, he3⟩, hw3, hc3, hd3, hv3⟩ :=
      ih B2 w2 hw2 hd2_le (fun j => U1 j.succ) (fun j => U2 j.succ) (fun j => V1 j.succ) (fun j => V2 j.succ)
    refine ⟨B3, w3, ⟨e1 ++ e2 ++ e3, by rw [he3, he2, he1]; simp [List.append_assoc]⟩,
      hw3, by omega, hd3, fun u v => ?_⟩
    rw [hv3 u v, hv2 u v, b2z_xor, hv1 u v, Fin.sum_univ_succ]
    have hacc1 : (wireList B1.gates (oneEach u v)).getD wAcc false = (wireList B.gates (oneEach u v)).getD wAcc false := by
      rw [he1, wireList_append_getD B.gates e1 (oneEach u v) wAcc (by rw [oneEach_length]; exact hwAcc)]
    rw [hacc1, add_assoc]

lemma rank2t_to_circuit {m n t : ℕ} (P : Fin (m + 1) → Fin n → Bool)
    (R : Fin (m + 1) → F) (C : Fin n → F)
    (U : Fin (m + 1) → Fin (2 * t) → F) (V : Fin n → Fin (2 * t) → F)
    (hP : ∀ u v, b2z (P u v) = R u + C v + ∑ k : Fin (2 * t), U u k * V v k) :
    ∃ Q : Circuit,
      (∀ g ∈ Q.gates, g.inputs.length ≤ 2) ∧
      ReadsBack (m + 1 + n) Q ∧ Represents P Q ∧
      (depthList (m + 1 + n) Q.gates).getD Q.output 0 ≤ 1 ∧
      Q.gates.countP nonlinear ≤ t := by
  let U1 : Fin t → Fin (m + 1) → F := fun k u => U u ⟨2 * k.val, by omega⟩
  let U2 : Fin t → Fin (m + 1) → F := fun k u => U u ⟨2 * k.val + 1, by omega⟩
  let V1 : Fin t → Fin n → F := fun k v => V v ⟨2 * k.val, by omega⟩
  let V2 : Fin t → Fin n → F := fun k v => V v ⟨2 * k.val + 1, by omega⟩
  let R' : Fin (m + 1) → F := fun u => R u + ∑ k : Fin t, U1 k u * U2 k u
  let C' : Fin n → F := fun v => C v + ∑ k : Fin t, V1 k v * V2 k v
  obtain ⟨B1, wR, _, hwR, hc1, hdR, hvR⟩ := build_row_fn (Builder.empty m n) R'
  obtain ⟨B2, wC, ⟨e2, he2⟩, hwC, hc2, hdC, hvC⟩ := build_col_fn B1 C'
  have hwR2 : wR < m + 1 + n + B2.gates.length := by rw [he2, List.length_append]; omega
  obtain ⟨B3, w0, _, hw0, hc3, hd0, hv0⟩ := build_xor B2 wR wC hwR2 hwC
  have hd0_le : (depthList (m + 1 + n) B3.gates).getD w0 0 ≤ 1 := by
    rw [hd0, hdC, he2, depthList_append_getD _ B1.gates e2 wR hwR, hdR]; omega
  obtain ⟨B4, wOut, _, _, hc4, hdOut, hvOut⟩ := build_pairs_sum t B3 w0 hw0 hd0_le U1 U2 V1 V2
  refine ⟨⟨B4.gates, wOut⟩, B4.hfan, B4.hrb, ?_, hdOut, ?_⟩
  · intro u v
    apply b2z_inj
    change b2z ((wireList B4.gates (oneEach u v)).getD wOut false) = b2z (P u v)
    rw [hvOut u v, hv0 u v, b2z_xor, hvC u v, hP u v]
    have hwR_val : (wireList B2.gates (oneEach u v)).getD wR false = (wireList B1.gates (oneEach u v)).getD wR false := by
      rw [he2, wireList_append_getD B1.gates e2 (oneEach u v) wR (by rw [oneEach_length]; exact hwR)]
    rw [hwR_val, hvR u v]
    have hsplit : ∑ k : Fin (2 * t), U u k * V v k =
        ∑ k : Fin t, (U1 k u * V1 k v + U2 k u * V2 k v) := by
      let evens := (Finset.univ : Finset (Fin (2 * t))).filter (fun k => k.val % 2 = 0)
      let odds := (Finset.univ : Finset (Fin (2 * t))).filter (fun k => k.val % 2 ≠ 0)
      have hdisj : Disjoint evens odds := by
        rw [Finset.disjoint_filter]; intro _ _ h1 h2; exact h2 h1
      have hunion : evens ∪ odds = Finset.univ := by
        ext k; simp only [evens, odds, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        by_cases h : k.val % 2 = 0 <;> simp [h]
      rw [← hunion, Finset.sum_union hdisj, Finset.sum_add_distrib]
      congr 1
      · symm
        apply Finset.sum_bij (fun idx _ => (⟨2 * idx.val, by omega⟩ : Fin (2 * t)))
        · intro _ _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only; omega⟩
        · intro i1 _ i2 _ heq; exact Fin.ext (by have := congrArg Fin.val heq; dsimp only at this; omega)
        · intro k hk
          have h0 : k.val % 2 = 0 := (Finset.mem_filter.mp hk).2
          exact ⟨⟨k.val / 2, by omega⟩, Finset.mem_univ _, Fin.ext (by dsimp only; omega)⟩
        · intro _ _; rfl
      · symm
        apply Finset.sum_bij (fun idx _ => (⟨2 * idx.val + 1, by omega⟩ : Fin (2 * t)))
        · intro _ _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only; omega⟩
        · intro i1 _ i2 _ heq; exact Fin.ext (by have := congrArg Fin.val heq; dsimp only at this; omega)
        · intro k hk
          have h0 : k.val % 2 ≠ 0 := (Finset.mem_filter.mp hk).2
          exact ⟨⟨k.val / 2, by omega⟩, Finset.mem_univ _, Fin.ext (by dsimp only; omega)⟩
        · intro _ _; rfl
    rw [hsplit]
    have hprod : ∀ k : Fin t, (U1 k u + V2 k v) * (U2 k u + V1 k v) =
        U1 k u * U2 k u + V1 k v * V2 k v + (U1 k u * V1 k v + U2 k u * V2 k v) := by
      intro k
      have h := f_foil (U1 k u) (V2 k v) (U2 k u) (V1 k v)
      rw [mul_comm (V2 k v) (V1 k v)] at h
      exact h
    simp_rw [hprod, Finset.sum_add_distrib]
    dsimp only [R', C']
    exact f_cancel2 (R u) (C v) (∑ k : Fin t, U1 k u * U2 k u) (∑ k : Fin t, V1 k v * V2 k v)
      (∑ k : Fin t, U1 k u * V1 k v + ∑ k : Fin t, U2 k u * V2 k v)
  · have hc0 : (Builder.empty m n).gates.countP nonlinear = 0 := rfl
    dsimp only
    omega

lemma exists_circuit_iff_exists_sL {n m t E : ℕ}
    (l r : Fin m → Fin n) (a b : Fin m → Bool)
    (wL wR : Fin m → ℕ) (target : Fin n → Bool) (pin : Fin n → ℕ) :
    let sign := fun e => xor (a e) (b e)
    let wt := fun e => min (wL e) (wR e)
    let vertexCost := fun (U : Finset (Fin n)) (s : Fin n → Bool) =>
      (U.filter (fun v => s v ≠ target v)).sum pin
    (∃ (P : Fin (m + 1) → Fin n → Bool) (Q : Circuit),
      (∀ g ∈ Q.gates, g.inputs.length ≤ 2) ∧
      ReadsBack (m + 1 + n) Q ∧ Represents P Q ∧
      (depthList (m + 1 + n) Q.gates).getD Q.output 0 ≤ 1 ∧ Q.gates.countP nonlinear ≤ t ∧
      vertexCost Finset.univ (P (Fin.last m)) +
        ((Finset.univ.filter (fun e : Fin m => P e.castSucc (l e) ≠ a e)).sum wL) +
        ((Finset.univ.filter (fun e : Fin m => P e.castSucc (r e) ≠ b e)).sum wR) ≤ E) ↔
    ∃ (s : Fin n → Bool) (L : Fin n → Fin (2 * t) → F),
      vertexCost Finset.univ s +
        ((Finset.univ.filter (fun e : Fin m => L (l e) = L (r e) ∧ xor (s (l e)) (s (r e)) ≠ sign e)).sum wt) ≤ E := by
  classical
  intro sign wt vertexCost
  constructor
  · rintro ⟨P, Q, hfan, hrb, hrep, hdep, hcnt, hcost⟩
    obtain ⟨R, C, U, V, hP⟩ := circuit_to_rank2t P Q hfan hrb hrep hdep hcnt
    refine ⟨P (Fin.last m), V, ?_⟩
    have hedge_le : ∀ e : Fin m,
        (if V (l e) = V (r e) ∧ xor (P (Fin.last m) (l e)) (P (Fin.last m) (r e)) ≠ sign e then wt e else 0) ≤
        (if P e.castSucc (l e) ≠ a e then wL e else 0) + (if P e.castSucc (r e) ≠ b e then wR e else 0) := by
      intro e
      by_cases hbad : V (l e) = V (r e) ∧ xor (P (Fin.last m) (l e)) (P (Fin.last m) (r e)) ≠ sign e
      · rw [ite_pos' hbad]
        by_cases hL : P e.castSucc (l e) ≠ a e
        · rw [ite_pos' hL]
          exact (Nat.min_le_left _ _).trans (Nat.le_add_right _ _)
        · by_cases hR : P e.castSucc (r e) ≠ b e
          · rw [ite_neg' hL, ite_pos' hR, zero_add]
            exact Nat.min_le_right _ _
          · exfalso
            have hPa : P e.castSucc (l e) = a e := not_not.mp hL
            have hPb : P e.castSucc (r e) = b e := not_not.mp hR
            have h1 := hP e.castSucc (l e)
            have h2 := hP e.castSucc (r e)
            have h3 := hP (Fin.last m) (l e)
            have h4 := hP (Fin.last m) (r e)
            have hsum_eq1 : ∑ k : Fin (2 * t), U e.castSucc k * V (l e) k =
                ∑ k : Fin (2 * t), U e.castSucc k * V (r e) k := by rw [hbad.1]
            have hsum_eq2 : ∑ k : Fin (2 * t), U (Fin.last m) k * V (l e) k =
                ∑ k : Fin (2 * t), U (Fin.last m) k * V (r e) k := by rw [hbad.1]
            have hdiff : b2z (P e.castSucc (l e)) + b2z (P e.castSucc (r e)) =
                b2z (P (Fin.last m) (l e)) + b2z (P (Fin.last m) (r e)) := by
              rw [h1, h2, h3, h4, hsum_eq1, hsum_eq2]
              exact f_cancel_row (R e.castSucc) (R (Fin.last m)) (C (l e)) (C (r e))
                (∑ k, U e.castSucc k * V (r e) k) (∑ k, U (Fin.last m) k * V (r e) k)
            rw [hPa, hPb, ← b2z_xor, ← b2z_xor] at hdiff
            exact hbad.2 (b2z_inj hdiff).symm
      · rw [ite_neg' hbad]; exact Nat.zero_le _
    have hsum_le : ((Finset.univ.filter (fun e : Fin m =>
        V (l e) = V (r e) ∧ xor (P (Fin.last m) (l e)) (P (Fin.last m) (r e)) ≠ sign e)).sum wt) ≤
        ((Finset.univ.filter (fun e : Fin m => P e.castSucc (l e) ≠ a e)).sum wL) +
        ((Finset.univ.filter (fun e : Fin m => P e.castSucc (r e) ≠ b e)).sum wR) := by
      simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum (fun e _ => hedge_le e)
    omega
  · rintro ⟨s, L, hcost⟩
    have hrow_choice : ∀ e : Fin m, ∃ (re : F) (αe : Fin (2 * t) → F),
        (if z2b (b2z (s (l e)) + re + ∑ k : Fin (2 * t), αe k * L (l e) k) ≠ a e then wL e else 0) +
        (if z2b (b2z (s (r e)) + re + ∑ k : Fin (2 * t), αe k * L (r e) k) ≠ b e then wR e else 0) ≤
        if L (l e) = L (r e) ∧ xor (s (l e)) (s (r e)) ≠ sign e then wt e else 0 := by
      intro e
      by_cases hLeq : L (l e) = L (r e)
      · by_cases hsig : xor (s (l e)) (s (r e)) = sign e
        · refine ⟨b2z (a e) + b2z (s (l e)), fun _ => 0, ?_⟩
          have h1 : z2b (b2z (s (l e)) + (b2z (a e) + b2z (s (l e))) + ∑ k : Fin (2 * t), 0 * L (l e) k) = a e := by
            simp only [zero_mul, Finset.sum_const_zero, add_zero]
            have : b2z (s (l e)) + (b2z (a e) + b2z (s (l e))) = b2z (a e) := by
              rw [add_comm (b2z (a e)), f_cancel_left]
            rw [this, z2b_b2z]
          have h2 : z2b (b2z (s (r e)) + (b2z (a e) + b2z (s (l e))) + ∑ k : Fin (2 * t), 0 * L (r e) k) = b e := by
            simp only [zero_mul, Finset.sum_const_zero, add_zero]
            have hxor : b2z (s (l e)) + b2z (s (r e)) = b2z (a e) + b2z (b e) := by
              rw [← b2z_xor, ← b2z_xor, hsig]
            have hsum : b2z (s (r e)) + (b2z (a e) + b2z (s (l e))) = b2z (b e) := by
              calc b2z (s (r e)) + (b2z (a e) + b2z (s (l e)))
                  = b2z (a e) + (b2z (s (l e)) + b2z (s (r e))) := by ac_rfl
                _ = b2z (a e) + (b2z (a e) + b2z (b e)) := by rw [hxor]
                _ = b2z (b e) := f_cancel_left _ _
            rw [hsum, z2b_b2z]
          simp only [h1, h2, ne_eq, not_true_eq_false, ite_false, add_zero]
          exact Nat.zero_le _
        · have hcond : L (l e) = L (r e) ∧ xor (s (l e)) (s (r e)) ≠ sign e := ⟨hLeq, hsig⟩
          by_cases hw : wL e ≤ wR e
          · refine ⟨b2z (b e) + b2z (s (r e)), fun _ => 0, ?_⟩
            have h2 : z2b (b2z (s (r e)) + (b2z (b e) + b2z (s (r e))) + ∑ k : Fin (2 * t), 0 * L (r e) k) = b e := by
              simp only [zero_mul, Finset.sum_const_zero, add_zero]
              have : b2z (s (r e)) + (b2z (b e) + b2z (s (r e))) = b2z (b e) := by
                rw [add_comm (b2z (b e)), f_cancel_left]
              rw [this, z2b_b2z]
            rw [ite_pos' hcond, ite_neg' (not_not.mpr h2), add_zero]
            have hmin : wt e = wL e := Nat.min_eq_left hw
            rw [hmin]
            split_ifs <;> omega
          · refine ⟨b2z (a e) + b2z (s (l e)), fun _ => 0, ?_⟩
            have h1 : z2b (b2z (s (l e)) + (b2z (a e) + b2z (s (l e))) + ∑ k : Fin (2 * t), 0 * L (l e) k) = a e := by
              simp only [zero_mul, Finset.sum_const_zero, add_zero]
              have : b2z (s (l e)) + (b2z (a e) + b2z (s (l e))) = b2z (a e) := by
                rw [add_comm (b2z (a e)), f_cancel_left]
              rw [this, z2b_b2z]
            rw [ite_pos' hcond, ite_neg' (not_not.mpr h1), zero_add]
            have hmin : wt e = wR e := Nat.min_eq_right (by omega)
            rw [hmin]
            split_ifs <;> omega
      · have hexk : ∃ k0 : Fin (2 * t), L (l e) k0 ≠ L (r e) k0 := by
          by_contra hnone
          apply hLeq
          funext k
          by_contra hne
          exact hnone ⟨k, hne⟩
        rcases hexk with ⟨k0, hk0⟩
        have hdiff1 : L (l e) k0 + L (r e) k0 = 1 := by
          rcases f_cases (L (l e) k0) with h1 | h1 <;> rcases f_cases (L (r e) k0) with h2 | h2
          · exact (hk0 (h1.trans h2.symm)).elim
          · rw [h1, h2]; decide
          · rw [h1, h2]; decide
          · exact (hk0 (h1.trans h2.symm)).elim
        let c : F := b2z (a e) + b2z (b e) + b2z (s (l e)) + b2z (s (r e))
        let αe : Fin (2 * t) → F := fun k => if k = k0 then c else 0
        let re : F := b2z (a e) + b2z (s (l e)) + c * L (l e) k0
        refine ⟨re, αe, ?_⟩
        have hsL : ∑ k : Fin (2 * t), αe k * L (l e) k = c * L (l e) k0 := by
          rw [Finset.sum_eq_single k0]
          · simp [αe]
          · intro k _ hne; simp [αe, hne]
          · intro hni; exact (hni (Finset.mem_univ _)).elim
        have hsR : ∑ k : Fin (2 * t), αe k * L (r e) k = c * L (r e) k0 := by
          rw [Finset.sum_eq_single k0]
          · simp [αe]
          · intro k _ hne; simp [αe, hne]
          · intro hni; exact (hni (Finset.mem_univ _)).elim
        have h1 : z2b (b2z (s (l e)) + re + ∑ k : Fin (2 * t), αe k * L (l e) k) = a e := by
          rw [hsL]
          have : b2z (s (l e)) + re + c * L (l e) k0 = b2z (a e) := by
            dsimp only [re]
            calc b2z (s (l e)) + (b2z (a e) + b2z (s (l e)) + c * L (l e) k0) + c * L (l e) k0
                = b2z (a e) + ((b2z (s (l e)) + b2z (s (l e))) + (c * L (l e) k0 + c * L (l e) k0)) := by ac_rfl
              _ = b2z (a e) := by rw [f_add_self, f_add_self, add_zero, add_zero]
          rw [this, z2b_b2z]
        have h2 : z2b (b2z (s (r e)) + re + ∑ k : Fin (2 * t), αe k * L (r e) k) = b e := by
          rw [hsR]
          have : b2z (s (r e)) + re + c * L (r e) k0 = b2z (b e) := by
            dsimp only [re]
            have hmul : c * L (l e) k0 + c * L (r e) k0 = c := by
              rw [← mul_add, hdiff1, mul_one]
            calc b2z (s (r e)) + (b2z (a e) + b2z (s (l e)) + c * L (l e) k0) + c * L (r e) k0
                = b2z (s (r e)) + b2z (a e) + b2z (s (l e)) + (c * L (l e) k0 + c * L (r e) k0) := by ac_rfl
              _ = b2z (s (r e)) + b2z (a e) + b2z (s (l e)) + (b2z (a e) + b2z (b e) + b2z (s (l e)) + b2z (s (r e))) := by
                rw [hmul]
              _ = b2z (b e) + ((b2z (a e) + b2z (a e)) + (b2z (s (l e)) + b2z (s (l e))) + (b2z (s (r e)) + b2z (s (r e)))) := by
                ac_rfl
              _ = b2z (b e) := by simp only [f_add_self, add_zero]
          rw [this, z2b_b2z]
        simp only [h1, h2, ne_eq, not_true_eq_false, ite_false, add_zero]
        exact Nat.zero_le _
    choose re αe hre using hrow_choice
    let R : Fin (m + 1) → F := Fin.lastCases 0 re
    let C : Fin n → F := fun v => b2z (s v)
    let U : Fin (m + 1) → Fin (2 * t) → F := Fin.lastCases (fun _ => 0) αe
    let P : Fin (m + 1) → Fin n → Bool := fun u v => z2b (R u + C v + ∑ k : Fin (2 * t), U u k * L v k)
    have hP_eq : ∀ u v, b2z (P u v) = R u + C v + ∑ k : Fin (2 * t), U u k * L v k :=
      fun u v => b2z_z2b _
    obtain ⟨Q, hfan, hrb, hrep, hdep, hcnt⟩ := rank2t_to_circuit P R C U L hP_eq
    refine ⟨P, Q, hfan, hrb, hrep, hdep, hcnt, ?_⟩
    have hPlast : P (Fin.last m) = s := by
      funext v
      simp [P, R, C, U, z2b_b2z]
    rw [hPlast]
    have hsum_le : ((Finset.univ.filter (fun e : Fin m => P e.castSucc (l e) ≠ a e)).sum wL) +
        ((Finset.univ.filter (fun e : Fin m => P e.castSucc (r e) ≠ b e)).sum wR) ≤
        ((Finset.univ.filter (fun e : Fin m => L (l e) = L (r e) ∧ xor (s (l e)) (s (r e)) ≠ sign e)).sum wt) := by
      simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro e _
      have h1 : P e.castSucc (l e) = z2b (b2z (s (l e)) + re e + ∑ k : Fin (2 * t), αe e k * L (l e) k) := by
        simp only [P, R, C, U, Fin.lastCases_castSucc]
        rw [add_comm (re e) (b2z (s (l e)))]
      have h2 : P e.castSucc (r e) = z2b (b2z (s (r e)) + re e + ∑ k : Fin (2 * t), αe e k * L (r e) k) := by
        simp only [P, R, C, U, Fin.lastCases_castSucc]
        rw [add_comm (re e) (b2z (s (r e)))]
      rw [h1, h2]
      exact hre e
    omega

lemma finset_prod_one_add {α R : Type*} [CommRing R] (s : Finset α) (f : α → R) :
    ∏ x ∈ s, (1 + f x) = ∑ t ∈ s.powerset, ∏ x ∈ t, f x := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, ih, Finset.powerset_insert,
      Finset.sum_union (Finset.disjoint_left.mpr (fun t ht1 ht2 => by
        rcases Finset.mem_image.mp ht2 with ⟨t', _, rfl⟩
        exact ha (Finset.mem_powerset.mp ht1 (Finset.mem_insert_self a t'))))]
    rw [add_mul, one_mul, Finset.mul_sum, Finset.sum_image]
    · congr 1
      apply Finset.sum_congr rfl; intro t ht
      have hna : a ∉ t := fun h => ha (Finset.mem_powerset.mp ht h)
      rw [Finset.prod_insert hna]
    · intro t1 ht1 t2 ht2 heq
      have h1 : a ∉ t1 := fun h => ha (Finset.mem_powerset.mp ht1 h)
      have h2 : a ∉ t2 := fun h => ha (Finset.mem_powerset.mp ht2 h)
      ext x
      have hx := Finset.ext_iff.mp heq x
      by_cases hxa : x = a
      · subst hxa; simp [h1, h2]
      · simpa [Finset.mem_insert, hxa] using hx

lemma comp_eqv {n m : ℕ} (l r : Fin m → Fin n) (S : Finset (Fin m)) :
    let rel := fun x z : Fin n => ∃ e ∈ S, l e = x ∧ r e = z
    let comp := fun v : Fin n => Finset.univ.filter (fun y : Fin n =>
      @decide (Relation.EqvGen rel v y) (Classical.propDecidable _) = true)
    (∀ v, v ∈ comp v) ∧
    (∀ v y, y ∈ comp v ↔ comp y = comp v) ∧
    (∀ U1 ∈ (Finset.univ : Finset (Fin n)).image comp,
      ∀ U2 ∈ (Finset.univ : Finset (Fin n)).image comp, U1 ≠ U2 → Disjoint U1 U2) ∧
    ((Finset.univ : Finset (Fin n)).image comp).biUnion id = Finset.univ := by
  intro rel comp
  have hmem : ∀ v y, y ∈ comp v ↔ Relation.EqvGen rel v y := fun v y => by
    simp only [comp, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨@of_decide_eq_true _ (Classical.propDecidable _), @decide_eq_true _ (Classical.propDecidable _)⟩
  have hv_mem : ∀ v, v ∈ comp v := fun v => (hmem v v).mpr (Relation.EqvGen.refl v)
  have hvy : ∀ v y, y ∈ comp v ↔ comp y = comp v := fun v y => by
    rw [hmem]
    constructor
    · intro h
      ext z; rw [hmem, hmem]
      exact ⟨fun hyz => Relation.EqvGen.trans _ _ _ h hyz,
        fun hvz => Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ h) hvz⟩
    · intro h
      exact (hmem v y).mp (h ▸ hv_mem y)
  refine ⟨hv_mem, hvy, ?_, ?_⟩
  · intro U1 hU1 U2 hU2 hne
    rcases Finset.mem_image.mp hU1 with ⟨v1, _, rfl⟩
    rcases Finset.mem_image.mp hU2 with ⟨v2, _, rfl⟩
    rw [Finset.disjoint_left]
    intro y hy1 hy2
    exact hne (((hvy v1 y).mp hy1).symm.trans ((hvy v2 y).mp hy2))
  · ext v
    simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and, id_eq, iff_true]
    exact ⟨comp v, ⟨v, rfl⟩, hv_mem v⟩

lemma phase_iff_xor_const {n m : ℕ} (l r : Fin m → Fin n) (sign : Fin m → Bool)
    (S : Finset (Fin m)) (s0 : Fin n → Bool) (hs0 : ∀ e ∈ S, xor (s0 (l e)) (s0 (r e)) ≠ sign e)
    (s : Fin n → Bool) :
    (∀ e ∈ S, xor (s (l e)) (s (r e)) ≠ sign e) ↔
      ∀ e ∈ S, xor (s (l e)) (s0 (l e)) = xor (s (r e)) (s0 (r e)) := by
  have hbool : ∀ x1 x2 y1 y2 sg : Bool, xor y1 y2 ≠ sg →
      (xor x1 x2 ≠ sg ↔ xor x1 y1 = xor x2 y2) := by
    intro x1 x2 y1 y2 sg
    cases x1 <;> cases x2 <;> cases y1 <;> cases y2 <;> cases sg <;> decide
  constructor
  · intro hs e he
    exact (hbool _ _ _ _ _ (hs0 e he)).mp (hs e he)
  · intro hc e he
    exact (hbool _ _ _ _ _ (hs0 e he)).mpr (hc e he)

lemma poly_identity {n m t : ℕ} (l r : Fin m → Fin n) (a b : Fin m → Bool)
    (wL wR : Fin m → ℕ) (target : Fin n → Bool) (pin : Fin n → ℕ) :
    let q := 2 ^ (2 * t)
    let sign := fun e => xor (a e) (b e)
    let wt := fun e => min (wL e) (wR e)
    let comp := fun (S : Finset (Fin m)) (v : Fin n) => Finset.univ.filter (fun y : Fin n =>
      @decide (Relation.EqvGen (fun x z : Fin n => ∃ e ∈ S, l e = x ∧ r e = z) v y)
        (Classical.propDecidable _) = true)
    let phase := fun (S : Finset (Fin m)) (s : Fin n → Bool) =>
      ∀ e ∈ S, xor (s (l e)) (s (r e)) ≠ sign e
    let X : Polynomial ℤ := Polynomial.X
    let vertexCost := fun (U : Finset (Fin n)) (s : Fin n → Bool) =>
      (U.filter (fun v => s v ≠ target v)).sum pin
    let fieldFactor := fun (S : Finset (Fin m)) =>
      if h : ∃ s : Fin n → Bool, phase S s then
        let s := Classical.choose h
        ∏ U ∈ Finset.univ.image (comp S),
          (Polynomial.C (q : ℤ)) * (X ^ vertexCost U s + X ^ vertexCost U (fun v => !(s v)))
      else 0
    let Z := ∑ S : Finset (Fin m), fieldFactor S * ∏ e ∈ S, (X ^ wt e - 1)
    ∑ s : Fin n → Bool, ∑ L : Fin n → Fin (2 * t) → F,
      X ^ (vertexCost Finset.univ s +
        ((Finset.univ.filter (fun e : Fin m => L (l e) = L (r e) ∧ xor (s (l e)) (s (r e)) ≠ sign e)).sum wt)) = Z := by
  classical
  intro q sign wt comp phase X vertexCost fieldFactor Z
  have hexpand : ∀ (s : Fin n → Bool) (L : Fin n → Fin (2 * t) → F),
      X ^ (vertexCost Finset.univ s +
        ((Finset.univ.filter (fun e : Fin m => L (l e) = L (r e) ∧ xor (s (l e)) (s (r e)) ≠ sign e)).sum wt)) =
      ∑ S : Finset (Fin m),
        (if (∀ e ∈ S, L (l e) = L (r e)) ∧ phase S s then X ^ vertexCost Finset.univ s else 0) *
          ∏ e ∈ S, (X ^ wt e - 1) := by
    intro s L
    let bad := Finset.univ.filter (fun e : Fin m => L (l e) = L (r e) ∧ xor (s (l e)) (s (r e)) ≠ sign e)
    rw [pow_add]
    have hpow : X ^ (bad.sum wt) = ∑ S ∈ bad.powerset, ∏ e ∈ S, (X ^ wt e - 1) := by
      rw [← Finset.prod_pow_eq_pow_sum]
      have h1 : ∏ e ∈ bad, X ^ wt e = ∏ e ∈ bad, (1 + (X ^ wt e - 1)) := by
        apply Finset.prod_congr rfl; intro e _; exact (add_sub_cancel _ _).symm
      rw [h1, finset_prod_one_add]
    rw [hpow, Finset.mul_sum]
    have hsub : ∑ S ∈ bad.powerset, X ^ vertexCost Finset.univ s * ∏ e ∈ S, (X ^ wt e - 1) =
        ∑ S : Finset (Fin m),
          (if S ∈ bad.powerset then X ^ vertexCost Finset.univ s else 0) * ∏ e ∈ S, (X ^ wt e - 1) := by
      simp only [ite_mul, zero_mul, ← Finset.sum_filter]
      have hfilt : (Finset.univ : Finset (Finset (Fin m))).filter (fun S => S ∈ bad.powerset) = bad.powerset := by
        ext S; simp
      rw [hfilt]
    rw [hsub]
    apply Finset.sum_congr rfl; intro S _
    have hiff : S ∈ bad.powerset ↔ (∀ e ∈ S, L (l e) = L (r e)) ∧ phase S s := by
      rw [Finset.mem_powerset]
      constructor
      · intro h
        exact ⟨fun e he => (Finset.mem_filter.mp (h he)).2.1, fun e he => (Finset.mem_filter.mp (h he)).2.2⟩
      · rintro ⟨h1, h2⟩ e he
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1 e he, h2 e he⟩
    simp [hiff]
  simp_rw [hexpand]
  conv_lhs =>
    arg 2; ext s
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  simp_rw [← Finset.sum_mul]
  congr 1
  let CS : Finset (Finset (Fin n)) := Finset.univ.image (comp S)
  obtain ⟨hv_mem, hvy, hdisj, hbiU⟩ := comp_eqv l r S
  have hGoodL : (((Finset.univ : Finset (Fin n → Fin (2 * t) → F)).filter (fun L => ∀ e ∈ S, L (l e) = L (r e))).card : ℤ) =
      q ^ CS.card := by
    have hne : ∀ U ∈ CS, U.Nonempty := fun U hU => by
      rcases Finset.mem_image.mp hU with ⟨v, _, rfl⟩
      exact ⟨v, hv_mem v⟩
    have hbij : ((Finset.univ : Finset (Fin n → Fin (2 * t) → F)).filter (fun L => ∀ e ∈ S, L (l e) = L (r e))).card =
        (Finset.univ : Finset (CS → (Fin (2 * t) → F))).card := by
      apply Finset.card_bij (fun L _ U => L (hne U.1 U.2).choose)
      · intro _ _; exact Finset.mem_univ _
      · intro L1 hL1 L2 hL2 heq
        have h1 : ∀ e ∈ S, L1 (l e) = L1 (r e) := (Finset.mem_filter.mp hL1).2
        have h2 : ∀ e ∈ S, L2 (l e) = L2 (r e) := (Finset.mem_filter.mp hL2).2
        have hconst : ∀ (L : Fin n → Fin (2 * t) → F), (∀ e ∈ S, L (l e) = L (r e)) →
            ∀ x y, Relation.EqvGen (fun x z : Fin n => ∃ e ∈ S, l e = x ∧ r e = z) x y → L x = L y := by
          intro L hL x y hxy
          induction hxy with
          | rel a b hab => rcases hab with ⟨e, he, rfl, rfl⟩; exact hL e he
          | refl _ => rfl
          | symm _ _ _ ih => exact ih.symm
          | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
        funext v
        let U : CS := ⟨comp S v, Finset.mem_image_of_mem _ (Finset.mem_univ v)⟩
        let rep := (hne U.1 U.2).choose
        have hrep_in : rep ∈ comp S v := (hne U.1 U.2).choose_spec
        have heqv : Relation.EqvGen (fun x z : Fin n => ∃ e ∈ S, l e = x ∧ r e = z) v rep :=
          @of_decide_eq_true _ (Classical.propDecidable _) (Finset.mem_filter.mp hrep_in).2
        rw [hconst L1 h1 v rep heqv, hconst L2 h2 v rep heqv]
        exact congrFun heq U
      · intro φ _
        let L : Fin n → Fin (2 * t) → F := fun v => φ ⟨comp S v, Finset.mem_image_of_mem _ (Finset.mem_univ v)⟩
        refine ⟨L, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun e he => ?_⟩, ?_⟩
        · have heqv : comp S (l e) = comp S (r e) := by
            have hrel : Relation.EqvGen (fun x z : Fin n => ∃ e ∈ S, l e = x ∧ r e = z) (r e) (l e) :=
              Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨e, he, rfl, rfl⟩)
            exact (hvy (r e) (l e)).mp (Finset.mem_filter.mpr ⟨Finset.mem_univ _, @decide_eq_true _ (Classical.propDecidable _) hrel⟩)
          dsimp only [L]
          congr 1
          exact Subtype.ext heqv
        · funext U
          dsimp only [L]
          let rep := (hne U.1 U.2).choose
          have hrep_in : rep ∈ U.1 := (hne U.1 U.2).choose_spec
          rcases Finset.mem_image.mp U.2 with ⟨v, _, hvU⟩
          have hrep_v : rep ∈ comp S v := hvU.symm ▸ hrep_in
          have hcomp_eq : comp S rep = U.1 := ((hvy v rep).mp hrep_v).trans hvU
          congr 1
          exact Subtype.ext hcomp_eq
    rw [hbij, Finset.card_univ, Fintype.card_fun, Fintype.card_fun, ZMod.card, Fintype.card_fin, Fintype.card_coe]
    push_cast
    rfl
  have hfactor : ∑ s : Fin n → Bool, ∑ L : Fin n → Fin (2 * t) → F,
      (if (∀ e ∈ S, L (l e) = L (r e)) ∧ phase S s then X ^ vertexCost Finset.univ s else 0) =
      Polynomial.C (q ^ CS.card) *
        ∑ s ∈ (Finset.univ : Finset (Fin n → Bool)).filter (phase S), X ^ vertexCost Finset.univ s := by
    rw [Finset.mul_sum]
    have h1 : ∀ s : Fin n → Bool,
        ∑ L : Fin n → Fin (2 * t) → F,
          (if (∀ e ∈ S, L (l e) = L (r e)) ∧ phase S s then X ^ vertexCost Finset.univ s else 0) =
        if phase S s then Polynomial.C (q ^ CS.card) * X ^ vertexCost Finset.univ s else 0 := by
      intro s
      by_cases hs : phase S s
      · simp only [hs, and_true, ite_true]
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        congr 1
        rw [← hGoodL, Polynomial.C_eq_natCast]
      · simp [hs]
    simp_rw [h1, ← Finset.sum_filter]
  rw [hfactor]
  dsimp only [fieldFactor]
  by_cases hph : ∃ s : Fin n → Bool, phase S s
  · simp only [hph, dite_true]
    let s0 := Classical.choose hph
    have hs0 : phase S s0 := Classical.choose_spec hph
    have hvc_split : ∀ s : Fin n → Bool, vertexCost Finset.univ s = ∑ U ∈ CS, vertexCost U s := by
      intro s
      dsimp only [vertexCost]
      simp only [Finset.sum_filter]
      have h1 := Finset.sum_biUnion (s := CS) (t := id)
        (f := fun v => if s v ≠ target v then pin v else 0)
        (fun U1 h1 U2 h2 hne => hdisj U1 h1 U2 h2 hne)
      rw [hbiU] at h1
      exact h1
    have hne : ∀ U ∈ CS, U.Nonempty := fun U hU => by
      rcases Finset.mem_image.mp hU with ⟨v, _, rfl⟩
      exact ⟨v, hv_mem v⟩
    have hS_sum : ∑ s ∈ (Finset.univ : Finset (Fin n → Bool)).filter (phase S), X ^ vertexCost Finset.univ s =
        ∑ φ : CS → Bool,
          ∏ U : CS, X ^ (if φ U then vertexCost U.1 (fun v => !(s0 v)) else vertexCost U.1 s0) := by
      symm
      apply Finset.sum_bij (fun φ _ v => if φ ⟨comp S v, Finset.mem_image_of_mem _ (Finset.mem_univ v)⟩ then !(s0 v) else s0 v)
      · intro φ _
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        let s_φ : Fin n → Bool := fun v => if φ ⟨comp S v, Finset.mem_image_of_mem _ (Finset.mem_univ v)⟩ then !(s0 v) else s0 v
        exact (phase_iff_xor_const l r sign S s0 hs0 s_φ).mpr (fun e he => by
          have heqv : comp S (l e) = comp S (r e) := by
            have hrel : Relation.EqvGen (fun x z : Fin n => ∃ e ∈ S, l e = x ∧ r e = z) (r e) (l e) :=
              Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨e, he, rfl, rfl⟩)
            exact (hvy (r e) (l e)).mp (Finset.mem_filter.mpr ⟨Finset.mem_univ _, @decide_eq_true _ (Classical.propDecidable _) hrel⟩)
          have hsub : (⟨comp S (l e), Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩ : CS) =
              ⟨comp S (r e), Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩ := Subtype.ext heqv
          dsimp only [s_φ]
          rw [hsub]
          cases φ ⟨comp S (r e), Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩ <;>
            cases s0 (l e) <;> cases s0 (r e) <;> decide)
      · intro φ1 _ φ2 _ heq
        funext U
        let rep := (hne U.1 U.2).choose
        have hrep_in : rep ∈ U.1 := (hne U.1 U.2).choose_spec
        rcases Finset.mem_image.mp U.2 with ⟨v, _, hvU⟩
        have hrep_v : rep ∈ comp S v := hvU.symm ▸ hrep_in
        have hcomp_eq : comp S rep = U.1 := ((hvy v rep).mp hrep_v).trans hvU
        have hsub : (⟨comp S rep, Finset.mem_image_of_mem _ (Finset.mem_univ rep)⟩ : CS) = U :=
          Subtype.ext hcomp_eq
        have hval := congrFun heq rep
        rw [hsub] at hval
        cases h1 : φ1 U <;> cases h2 : φ2 U <;> rw [h1, h2] at hval <;>
          cases hs : s0 rep <;> simp [hs] at hval ⊢
      · intro s hs
        have hph_s : phase S s := (Finset.mem_filter.mp hs).2
        have hxc := (phase_iff_xor_const l r sign S s0 hs0 s).mp hph_s
        let φ : CS → Bool := fun U => xor (s (hne U.1 U.2).choose) (s0 (hne U.1 U.2).choose)
        refine ⟨φ, Finset.mem_univ _, ?_⟩
        funext v
        have hconst : ∀ x y, Relation.EqvGen (fun x z : Fin n => ∃ e ∈ S, l e = x ∧ r e = z) x y →
            xor (s x) (s0 x) = xor (s y) (s0 y) := by
          intro x y hxy
          induction hxy with
          | rel a b hab => rcases hab with ⟨e, he, rfl, rfl⟩; exact hxc e he
          | refl _ => rfl
          | symm _ _ _ ih => exact ih.symm
          | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
        let U : CS := ⟨comp S v, Finset.mem_image_of_mem _ (Finset.mem_univ v)⟩
        let rep := (hne U.1 U.2).choose
        have hrep_in : rep ∈ comp S v := (hne U.1 U.2).choose_spec
        have heqv : Relation.EqvGen (fun x z : Fin n => ∃ e ∈ S, l e = x ∧ r e = z) v rep :=
          @of_decide_eq_true _ (Classical.propDecidable _) (Finset.mem_filter.mp hrep_in).2
        have hxor_eq : xor (s rep) (s0 rep) = xor (s v) (s0 v) := (hconst v rep heqv).symm
        change (if xor (s rep) (s0 rep) then !(s0 v) else s0 v) = s v
        rw [hxor_eq]
        cases s v <;> cases s0 v <;> decide
      · intro φ _
        rw [hvc_split, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_coe_sort CS]
        apply Finset.prod_congr rfl
        intro U _
        congr 1
        dsimp only [vertexCost]
        have hval_on_U : ∀ v ∈ U.1,
            (if φ ⟨comp S v, Finset.mem_image_of_mem _ (Finset.mem_univ v)⟩ then !(s0 v) else s0 v) =
            if φ U then !(s0 v) else s0 v := by
          intro v hvU
          rcases Finset.mem_image.mp U.2 with ⟨w, _, hwU⟩
          have hv_w : v ∈ comp S w := hwU.symm ▸ hvU
          have hcomp_eq : comp S v = U.1 := ((hvy w v).mp hv_w).trans hwU
          have hsub : (⟨comp S v, Finset.mem_image_of_mem _ (Finset.mem_univ v)⟩ : CS) = U :=
            Subtype.ext hcomp_eq
          rw [hsub]
        cases hφ : φ U
        · simp only [Bool.false_eq_true, ite_false]
          congr 1
          ext v; simp only [Finset.mem_filter]
          constructor <;> rintro ⟨hvU, hne_t⟩ <;> exact ⟨hvU, by simpa [hval_on_U v hvU, hφ] using hne_t⟩
        · simp only [ite_true]
          congr 1
          ext v; simp only [Finset.mem_filter]
          constructor <;> rintro ⟨hvU, hne_t⟩ <;> exact ⟨hvU, by simpa [hval_on_U v hvU, hφ] using hne_t⟩
    rw [hS_sum]
    have hprod_sum : ∑ φ : CS → Bool,
        ∏ U : CS, X ^ (if φ U then vertexCost U.1 (fun v => !(s0 v)) else vertexCost U.1 s0) =
        ∏ U : CS, (X ^ vertexCost U.1 s0 + X ^ vertexCost U.1 (fun v => !(s0 v))) := by
      have h := Finset.sum_prod_piFinset (ι := CS) (Finset.univ : Finset Bool)
        (fun U b => X ^ (if b then vertexCost U.1 (fun v => !(s0 v)) else vertexCost U.1 s0))
      rw [Fintype.piFinset_univ] at h
      rw [h]
      apply Finset.prod_congr rfl; intro U _
      rw [Fintype.sum_bool, add_comm]
      simp
    rw [hprod_sum, Finset.prod_coe_sort CS (fun U => X ^ vertexCost U s0 + X ^ vertexCost U (fun v => !(s0 v)))]
    have hq_prod : Polynomial.C (q ^ CS.card) = ∏ _U ∈ CS, Polynomial.C (q : ℤ) := by
      rw [Finset.prod_const, ← map_pow]
    rw [hq_prod, ← Finset.prod_mul_distrib]
  · simp only [hph, dite_false]
    have hempty : (Finset.univ : Finset (Fin n → Bool)).filter (phase S) = ∅ := by
      ext s; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      intro hs; exact hph ⟨s, hs⟩
    rw [hempty, Finset.sum_empty, mul_zero]

lemma poly_sum_coeff {α : Type*} (s : Finset α) (f : α → Polynomial ℤ) (j : ℕ) :
    (∑ x ∈ s, f x).coeff j = ∑ x ∈ s, (f x).coeff j := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Polynomial.coeff_add, ih]

lemma main_proof : (
let nonlinear := fun (g : Gate) =>
  (g.inputs.length == 2) &&
    xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
        (xor (g.op.eval [true, false]) (g.op.eval [true, true]))
let depth := fun (w : ℕ) (Q : Circuit) =>
  (Q.gates.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun h => ds.getD h 0)).foldr max 0 + (nonlinear g).toNat])
    (List.replicate w 0)).getD Q.output 0
∀ (n m t E : ℕ) (_ : 0 < n) (l r : Fin m → Fin n) (a b : Fin m → Bool)
  (wL wR : Fin m → ℕ) (target : Fin n → Bool) (pin : Fin n → ℕ),
  let q := 2^(2*t)
  let sign := fun e => xor (a e) (b e)
  let wt := fun e => min (wL e) (wR e)
  let comp := fun (S : Finset (Fin m)) (v : Fin n) => Finset.univ.filter (fun y : Fin n =>
    @decide (Relation.EqvGen (fun x z : Fin n => ∃ e ∈ S, l e = x ∧ r e = z) v y)
      (Classical.propDecidable _) = true)
  let phase := fun (S : Finset (Fin m)) (s : Fin n → Bool) =>
    ∀ e ∈ S, xor (s (l e)) (s (r e)) ≠ sign e
  let X : Polynomial ℤ := Polynomial.X
  let vertexCost := fun (U : Finset (Fin n)) (s : Fin n → Bool) =>
    (U.filter (fun v => s v ≠ target v)).sum pin
  let fieldFactor := fun (S : Finset (Fin m)) =>
    if h : ∃ s : Fin n → Bool, phase S s then
      let s := Classical.choose h
      ∏ U ∈ Finset.univ.image (comp S),
        (Polynomial.C (q : ℤ)) * (X ^ vertexCost U s + X ^ vertexCost U (fun v => !(s v)))
    else 0
  let Z := ∑ S : Finset (Fin m), fieldFactor S * ∏ e ∈ S, (X ^ wt e - 1)
  ((∃ (P : Fin (m+1) → Fin n → Bool) (Q : Circuit),
    (∀ g ∈ Q.gates, g.inputs.length ≤ 2) ∧
    ReadsBack (m+1+n) Q ∧ Represents P Q ∧
    depth (m+1+n) Q ≤ 1 ∧ Q.gates.countP nonlinear ≤ t ∧
    vertexCost Finset.univ (P (Fin.last m)) +
      ((Finset.univ.filter (fun e : Fin m => P e.castSucc (l e) ≠ a e)).sum wL) +
      ((Finset.univ.filter (fun e : Fin m => P e.castSucc (r e) ≠ b e)).sum wR) ≤ E) ↔
    ∃ j : ℕ, j ≤ E ∧ 0 < Z.coeff j)) := by
  classical
  intro nl dep n m t E _ l r a b wL wR target pin q sign wt comp phase X vertexCost fieldFactor Z
  have h1 : (∃ (P : Fin (m + 1) → Fin n → Bool) (Q : Circuit),
      (∀ g ∈ Q.gates, g.inputs.length ≤ 2) ∧
      ReadsBack (m + 1 + n) Q ∧ Represents P Q ∧
      dep (m + 1 + n) Q ≤ 1 ∧ Q.gates.countP nl ≤ t ∧
      vertexCost Finset.univ (P (Fin.last m)) +
        ((Finset.univ.filter (fun e : Fin m => P e.castSucc (l e) ≠ a e)).sum wL) +
        ((Finset.univ.filter (fun e : Fin m => P e.castSucc (r e) ≠ b e)).sum wR) ≤ E) ↔
    ∃ (s : Fin n → Bool) (L : Fin n → Fin (2 * t) → F),
      vertexCost Finset.univ s +
        ((Finset.univ.filter (fun e : Fin m => L (l e) = L (r e) ∧ xor (s (l e)) (s (r e)) ≠ sign e)).sum wt) ≤ E :=
    exists_circuit_iff_exists_sL (t := t) (E := E) l r a b wL wR target pin
  have h2 : ∑ s : Fin n → Bool, ∑ L : Fin n → Fin (2 * t) → F,
      X ^ (vertexCost Finset.univ s +
        ((Finset.univ.filter (fun e : Fin m => L (l e) = L (r e) ∧ xor (s (l e)) (s (r e)) ≠ sign e)).sum wt)) = Z :=
    poly_identity (t := t) l r a b wL wR target pin
  rw [h1]
  let totalCost : (Fin n → Bool) × (Fin n → Fin (2 * t) → F) → ℕ := fun p =>
    vertexCost Finset.univ p.1 +
      ((Finset.univ.filter (fun e : Fin m => p.2 (l e) = p.2 (r e) ∧ xor (p.1 (l e)) (p.1 (r e)) ≠ sign e)).sum wt)
  have hZ : Z = ∑ p : (Fin n → Bool) × (Fin n → Fin (2 * t) → F), X ^ totalCost p := by
    rw [← h2, Fintype.sum_prod_type]
  have hcoeff : ∀ j : ℕ, Z.coeff j =
      (((Finset.univ : Finset ((Fin n → Bool) × (Fin n → Fin (2 * t) → F))).filter (fun p => totalCost p = j)).card : ℤ) := by
    intro j
    rw [hZ, poly_sum_coeff]
    have hterm : ∀ p : (Fin n → Bool) × (Fin n → Fin (2 * t) → F),
        (X ^ totalCost p).coeff j = if totalCost p = j then (1 : ℤ) else 0 := fun p => by
      rw [Polynomial.coeff_X_pow]
      by_cases h : totalCost p = j
      · subst h; simp
      · have h' : j ≠ totalCost p := Ne.symm h
        simp [h, h']
    simp_rw [hterm]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  constructor
  · rintro ⟨s, L, hle⟩
    refine ⟨totalCost (s, L), hle, ?_⟩
    rw [hcoeff]
    have hmem : (s, L) ∈ (Finset.univ : Finset ((Fin n → Bool) × (Fin n → Fin (2 * t) → F))).filter
        (fun p => totalCost p = totalCost (s, L)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
    have hpos : 0 < ((Finset.univ : Finset ((Fin n → Bool) × (Fin n → Fin (2 * t) → F))).filter
        (fun p => totalCost p = totalCost (s, L))).card :=
      Finset.card_pos.mpr ⟨(s, L), hmem⟩
    exact Int.natCast_pos.mpr hpos
  · rintro ⟨j, hjE, hpos⟩
    rw [hcoeff j] at hpos
    have hcard_pos : 0 < ((Finset.univ : Finset ((Fin n → Bool) × (Fin n → Fin (2 * t) → F))).filter
        (fun p => totalCost p = j)).card :=
      Int.natCast_pos.mp hpos
    obtain ⟨⟨s, L⟩, hmem⟩ := Finset.card_pos.mp hcard_pos
    have heq : totalCost (s, L) = j := (Finset.mem_filter.mp hmem).2
    exact ⟨s, L, heq.le.trans hjE⟩

end PEqualNP.Outside.L_meta_33661_aux

theorem PEqualNP.Outside.L_meta_33661 : (
let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
  (g.inputs.length == 2) &&
    xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
        (xor (g.op.eval [true, false]) (g.op.eval [true, true]))
let depth := fun (w : ℕ) (Q : PEqualNP.CircuitLowerBounds.Circuit) =>
  (Q.gates.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun h => ds.getD h 0)).foldr max 0 + (nonlinear g).toNat])
    (List.replicate w 0)).getD Q.output 0
∀ (n m t E : ℕ) (_ : 0 < n) (l r : Fin m → Fin n) (a b : Fin m → Bool)
  (wL wR : Fin m → ℕ) (target : Fin n → Bool) (pin : Fin n → ℕ),
  let q := 2^(2*t)
  let sign := fun e => xor (a e) (b e)
  let wt := fun e => min (wL e) (wR e)
  let comp := fun (S : Finset (Fin m)) (v : Fin n) => Finset.univ.filter (fun y : Fin n =>
    @decide (Relation.EqvGen (fun x z : Fin n => ∃ e ∈ S, l e = x ∧ r e = z) v y)
      (Classical.propDecidable _) = true)
  let phase := fun (S : Finset (Fin m)) (s : Fin n → Bool) =>
    ∀ e ∈ S, xor (s (l e)) (s (r e)) ≠ sign e
  let X : Polynomial ℤ := Polynomial.X
  let vertexCost := fun (U : Finset (Fin n)) (s : Fin n → Bool) =>
    (U.filter (fun v => s v ≠ target v)).sum pin
  let fieldFactor := fun (S : Finset (Fin m)) =>
    if h : ∃ s : Fin n → Bool, phase S s then
      let s := Classical.choose h
      ∏ U ∈ Finset.univ.image (comp S),
        (Polynomial.C (q : ℤ)) * (X ^ vertexCost U s + X ^ vertexCost U (fun v => !(s v)))
    else 0
  let Z := ∑ S : Finset (Fin m), fieldFactor S * ∏ e ∈ S, (X ^ wt e - 1)
  ((∃ (P : Fin (m+1) → Fin n → Bool) (Q : PEqualNP.CircuitLowerBounds.Circuit),
    (∀ g ∈ Q.gates, g.inputs.length ≤ 2) ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (m+1+n) Q ∧ PEqualNP.Represents.Represents P Q ∧
    depth (m+1+n) Q ≤ 1 ∧ Q.gates.countP nonlinear ≤ t ∧
    vertexCost Finset.univ (P (Fin.last m)) +
      ((Finset.univ.filter (fun e : Fin m => P e.castSucc (l e) ≠ a e)).sum wL) +
      ((Finset.univ.filter (fun e : Fin m => P e.castSucc (r e) ≠ b e)).sum wR) ≤ E) ↔
    ∃ j : ℕ, j ≤ E ∧ 0 < Z.coeff j)) :=
  PEqualNP.Outside.L_meta_33661_aux.main_proof

import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27741

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def pm3 (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
  (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

def ext (y : Fin 8 → Bool) : Fin 9 → Bool :=
  Fin.cons true y

def f1 (y : Fin 8 → Bool) : Bool := pm3 (ext y)

def spec (u : Fin 4 → Bool) : Fin 8 → Bool :=
  ![true, true, u 0, u 2, false, u 3, false, u 1]

def g4 (u : Fin 4 → Bool) : Bool :=
  (u 0 && u 1) || (u 1 && u 2) || (u 2 && u 3)

lemma f1_spec (u : Fin 4 → Bool) : f1 (spec u) = g4 u := by
  revert u
  decide

lemma getElem_zero_of_head? {α : Type*} {l : List α} {x : α} (h : l.head? = some x)
    (h0 : 0 < l.length) : l[0]'h0 = x := by
  cases l with
  | nil => simp at h
  | cons a t => simp only [List.head?_cons, Option.some.injEq] at h; simpa using h

lemma getElem_one_of_tail_head? {α : Type*} {l : List α} {x : α} (h : l.tail.head? = some x)
    (h1 : 1 < l.length) : l[1]'h1 = x := by
  cases l with
  | nil => simp at h1
  | cons a t =>
    cases t with
    | nil => simp at h1
    | cons b t' => simp only [List.tail_cons, List.head?_cons, Option.some.injEq] at h; simpa using h

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl step w

lemma wires_eq_W (C : Circuit) (x : List Bool) : C.wires x = W C.gates x := rfl

lemma W_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    W (g :: gs) w = W gs (step w g) := rfl

lemma W_append (a b : List Gate) (w : List Bool) :
    W (a ++ b) w = W b (W a w) := by
  simp [W, List.foldl_append]

lemma W_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    W (gs ++ [g]) w = step (W gs w) g := by
  rw [W_append]; rfl

lemma step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

lemma W_len (gs : List Gate) : ∀ w : List Bool, (W gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [W]
  | cons g gs ih =>
    intro w
    rw [W_cons, ih, step_len, List.length_cons]
    omega

lemma getD_append_lt (l l2 : List Bool) (i : ℕ) (h : i < l.length) :
    (l ++ l2).getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_append_len (l : List Bool) (v : Bool) : (l ++ [v]).getD l.length false = v := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_ge (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

lemma W_prefix (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length → (W gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [W_cons, ih (step w g) i (by rw [step_len]; omega)]
    exact getD_append_lt w _ i hi

lemma W_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (W gs w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (W gs w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [W_cons]
    cases j with
    | zero =>
      have h1 : w.length < (step w g).length := by simp [step]
      rw [Nat.add_zero, W_prefix gs (step w g) w.length h1]
      simp only [List.getElem_cons_zero]
      rw [show (step w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) from
        getD_append_len w _]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, W_prefix gs (step w g) i (by simp [step]; omega)]
        exact (getD_append_lt w _ i hi).symm
      · rw [if_neg hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (step w g) j hj'
      rw [step_len] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def wval {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma wval_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    wval C x i = x ⟨i, hi⟩ := by
  unfold wval
  rw [wires_eq_W, W_prefix C.gates (List.ofFn x) i (by simp [hi])]
  rw [List.getD_eq_getElem _ _ (by simp [hi]), List.getElem_ofFn]

lemma wval_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) (hj : j < C.gates.length)
    (hback : ∀ a ∈ (C.gates[j]).inputs, a < n + j) :
    wval C x (n + j) = (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i => wval C x i) := by
  unfold wval
  rw [wires_eq_W]
  have hlen : (List.ofFn x).length = n := List.length_ofFn
  have h1 := W_gate C.gates (List.ofFn x) j hj
  rw [hlen] at h1
  rw [h1]
  congr 1
  apply List.map_congr_left
  intro a ha
  rw [if_pos (hback a ha)]

lemma wval_and {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j a b : ℕ) (hj : j < C.gates.length)
    (hop : (C.gates[j]).op = GateOp.and) (hins : (C.gates[j]).inputs = [a, b])
    (ha : a < n + j) (hb : b < n + j) :
    wval C x (n + j) = (wval C x a && wval C x b) := by
  rw [wval_gate C x j hj (by rw [hins]; simp [ha, hb]), hop, hins]
  simp [GateOp.eval]

lemma wval_or {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j a b : ℕ) (hj : j < C.gates.length)
    (hop : (C.gates[j]).op = GateOp.or) (hins : (C.gates[j]).inputs = [a, b])
    (ha : a < n + j) (hb : b < n + j) :
    wval C x (n + j) = (wval C x a || wval C x b) := by
  rw [wval_gate C x j hj (by rw [hins]; simp [ha, hb]), hop, hins]
  simp [GateOp.eval]

def WellStructured (n : ℕ) (D : Circuit) : Prop :=
  ∀ j : Fin D.gates.length,
    ((D.gates.get j).op = GateOp.not ∧ ∃ a, a < n + j.val ∧ (D.gates.get j).inputs = [a]) ∨
    (((D.gates.get j).op = GateOp.and ∨ (D.gates.get j).op = GateOp.or) ∧
      ∃ a b, a < n + j.val ∧ b < n + j.val ∧ (D.gates.get j).inputs = [a, b])

lemma ws_back {n : ℕ} {D : Circuit} (hws : WellStructured n D) (j : ℕ) (hj : j < D.gates.length) :
    ∀ a ∈ (D.gates[j]).inputs, a < n + j := by
  intro a ha
  rcases hws ⟨j, hj⟩ with ⟨_, u, hu, hins⟩ | ⟨_, u, v, hu, hv, hins⟩
  · dsimp only at hu
    simp only [List.get_eq_getElem] at hins
    rw [hins, List.mem_singleton] at ha
    omega
  · dsimp only at hu hv
    simp only [List.get_eq_getElem] at hins
    rw [hins, List.mem_cons, List.mem_singleton] at ha
    rcases ha with rfl | rfl <;> omega

lemma f1_essential (i : Fin 8) :
    ∃ y : Fin 8 → Bool, f1 y ≠ f1 (Function.update y i (!y i)) := by
  fin_cases i
  · exact ⟨![false, false, true, false, false, false, false, true], by decide⟩
  · exact ⟨![false, false, true, false, false, false, true, false], by decide⟩
  · exact ⟨![true, false, false, false, false, false, false, true], by decide⟩
  · exact ⟨![false, false, false, false, false, false, false, true], by decide⟩
  · exact ⟨![false, false, false, false, false, false, true, false], by decide⟩
  · exact ⟨![true, false, false, false, true, false, false, false], by decide⟩
  · exact ⟨![false, false, false, false, true, false, false, false], by decide⟩
  · exact ⟨![false, false, false, true, false, false, false, false], by decide⟩

lemma g4_essential (i : Fin 4) :
    ∃ u : Fin 4 → Bool, g4 u ≠ g4 (Function.update u i (!u i)) := by
  fin_cases i
  · exact ⟨![false, true, false, false], by decide⟩
  · exact ⟨![true, false, false, false], by decide⟩
  · exact ⟨![false, false, false, true], by decide⟩
  · exact ⟨![false, false, true, false], by decide⟩

lemma g4_class_and_bool (a0 a1 a2 a3 b0 b1 b2 b3 : Bool)
    (hneA : a0 || a1 || a2 || a3 = true) (hneB : b0 || b1 || b2 || b3 = true)
    (hd0 : !(a0 && b0) = true) (hd1 : !(a1 && b1) = true)
    (hd2 : !(a2 && b2) = true) (hd3 : !(a3 && b3) = true)
    (hu0 : a0 || b0 = true) (hu1 : a1 || b1 = true)
    (hu2 : a2 || b2 = true) (hu3 : a3 || b3 = true)
    (hgA : ((a0 && a1) || (a1 && a2) || (a2 && a3)) = false)
    (hgB : ((b0 && b1) || (b1 && b2) || (b2 && b3)) = false) :
    (a0 = true ∧ a1 = false ∧ a2 = true ∧ a3 = false ∧ b0 = false ∧ b1 = true ∧ b2 = false ∧ b3 = true) ∨
    (a0 = false ∧ a1 = true ∧ a2 = false ∧ a3 = true ∧ b0 = true ∧ b1 = false ∧ b2 = true ∧ b3 = false) := by
  cases a0 <;> cases a1 <;> cases a2 <;> cases a3 <;> cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
    simp_all

lemma g4_class_or_bool (a0 a1 a2 a3 b0 b1 b2 b3 : Bool)
    (hneA : a0 || a1 || a2 || a3 = true) (hneB : b0 || b1 || b2 || b3 = true)
    (hd0 : !(a0 && b0) = true) (hd1 : !(a1 && b1) = true)
    (hd2 : !(a2 && b2) = true) (hd3 : !(a3 && b3) = true)
    (hu0 : a0 || b0 = true) (hu1 : a1 || b1 = true)
    (hu2 : a2 || b2 = true) (hu3 : a3 || b3 = true)
    (hgA : ((a0 && a1) || (a1 && a2) || (a2 && a3)) = true)
    (hgB : ((b0 && b1) || (b1 && b2) || (b2 && b3)) = true) :
    (a0 = true ∧ a1 = true ∧ a2 = false ∧ a3 = false ∧ b0 = false ∧ b1 = false ∧ b2 = true ∧ b3 = true) ∨
    (a0 = false ∧ a1 = false ∧ a2 = true ∧ a3 = true ∧ b0 = true ∧ b1 = true ∧ b2 = false ∧ b3 = false) := by
  cases a0 <;> cases a1 <;> cases a2 <;> cases a3 <;> cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
    simp_all

lemma g4_class_and (A B : Finset (Fin 4)) (hneA : A.Nonempty) (hneB : B.Nonempty)
    (hdisj : Disjoint A B) (hunion : A ∪ B = Finset.univ)
    (hgA : g4 (fun k => decide (k ∈ A)) = false) (hgB : g4 (fun k => decide (k ∈ B)) = false) :
    (A = {0, 2} ∧ B = {1, 3}) ∨ (A = {1, 3} ∧ B = {0, 2}) := by
  have hneAb : decide ((0 : Fin 4) ∈ A) || decide ((1 : Fin 4) ∈ A) || decide ((2 : Fin 4) ∈ A) || decide ((3 : Fin 4) ∈ A) = true := by
    obtain ⟨k, hk⟩ := hneA
    fin_cases k
    · have h : (0 : Fin 4) ∈ A := hk; simp [h]
    · have h : (1 : Fin 4) ∈ A := hk; simp [h]
    · have h : (2 : Fin 4) ∈ A := hk; simp [h]
    · have h : (3 : Fin 4) ∈ A := hk; simp [h]
  have hneBb : decide ((0 : Fin 4) ∈ B) || decide ((1 : Fin 4) ∈ B) || decide ((2 : Fin 4) ∈ B) || decide ((3 : Fin 4) ∈ B) = true := by
    obtain ⟨k, hk⟩ := hneB
    fin_cases k
    · have h : (0 : Fin 4) ∈ B := hk; simp [h]
    · have h : (1 : Fin 4) ∈ B := hk; simp [h]
    · have h : (2 : Fin 4) ∈ B := hk; simp [h]
    · have h : (3 : Fin 4) ∈ B := hk; simp [h]
  have hd : ∀ k : Fin 4, !(decide (k ∈ A) && decide (k ∈ B)) = true := by
    intro k; by_cases h : k ∈ A
    · have h2 : k ∉ B := Finset.disjoint_left.mp hdisj h; simp [h, h2]
    · simp [h]
  have hu : ∀ k : Fin 4, (decide (k ∈ A) || decide (k ∈ B)) = true := by
    intro k
    have hk : k ∈ A ∪ B := by rw [hunion]; exact Finset.mem_univ k
    rw [Finset.mem_union] at hk
    rcases hk with h | h <;> simp [h]
  rcases g4_class_and_bool _ _ _ _ _ _ _ _ hneAb hneBb (hd 0) (hd 1) (hd 2) (hd 3)
      (hu 0) (hu 1) (hu 2) (hu 3) hgA hgB with
      ⟨h0, h1, h2, h3, g0, g1, g2, g3⟩ | ⟨h0, h1, h2, h3, g0, g1, g2, g3⟩
  · left; constructor <;> (ext k; fin_cases k <;> simp_all)
  · right; constructor <;> (ext k; fin_cases k <;> simp_all)

lemma g4_class_or (A B : Finset (Fin 4)) (hneA : A.Nonempty) (hneB : B.Nonempty)
    (hdisj : Disjoint A B) (hunion : A ∪ B = Finset.univ)
    (hgA : g4 (fun k => decide (k ∈ A)) = true) (hgB : g4 (fun k => decide (k ∈ B)) = true) :
    (A = {0, 1} ∧ B = {2, 3}) ∨ (A = {2, 3} ∧ B = {0, 1}) := by
  have hneAb : decide ((0 : Fin 4) ∈ A) || decide ((1 : Fin 4) ∈ A) || decide ((2 : Fin 4) ∈ A) || decide ((3 : Fin 4) ∈ A) = true := by
    obtain ⟨k, hk⟩ := hneA
    fin_cases k
    · have h : (0 : Fin 4) ∈ A := hk; simp [h]
    · have h : (1 : Fin 4) ∈ A := hk; simp [h]
    · have h : (2 : Fin 4) ∈ A := hk; simp [h]
    · have h : (3 : Fin 4) ∈ A := hk; simp [h]
  have hneBb : decide ((0 : Fin 4) ∈ B) || decide ((1 : Fin 4) ∈ B) || decide ((2 : Fin 4) ∈ B) || decide ((3 : Fin 4) ∈ B) = true := by
    obtain ⟨k, hk⟩ := hneB
    fin_cases k
    · have h : (0 : Fin 4) ∈ B := hk; simp [h]
    · have h : (1 : Fin 4) ∈ B := hk; simp [h]
    · have h : (2 : Fin 4) ∈ B := hk; simp [h]
    · have h : (3 : Fin 4) ∈ B := hk; simp [h]
  have hd : ∀ k : Fin 4, !(decide (k ∈ A) && decide (k ∈ B)) = true := by
    intro k; by_cases h : k ∈ A
    · have h2 : k ∉ B := Finset.disjoint_left.mp hdisj h; simp [h, h2]
    · simp [h]
  have hu : ∀ k : Fin 4, (decide (k ∈ A) || decide (k ∈ B)) = true := by
    intro k
    have hk : k ∈ A ∪ B := by rw [hunion]; exact Finset.mem_univ k
    rw [Finset.mem_union] at hk
    rcases hk with h | h <;> simp [h]
  rcases g4_class_or_bool _ _ _ _ _ _ _ _ hneAb hneBb (hd 0) (hd 1) (hd 2) (hd 3)
      (hu 0) (hu 1) (hu 2) (hu 3) hgA hgB with
      ⟨h0, h1, h2, h3, g0, g1, g2, g3⟩ | ⟨h0, h1, h2, h3, g0, g1, g2, g3⟩
  · left; constructor <;> (ext k; fin_cases k <;> simp_all)
  · right; constructor <;> (ext k; fin_cases k <;> simp_all)

lemma g4_not_and_split (fa fb : (Fin 4 → Bool) → Bool)
    (A B : Finset (Fin 4))
    (hdepA : ∀ u1 u2, (∀ k ∈ A, u1 k = u2 k) → fa u1 = fa u2)
    (hdepB : ∀ u1 u2, (∀ k ∈ B, u1 k = u2 k) → fb u1 = fb u2)
    (hA : A = {0, 2}) (hB : B = {1, 3})
    (hvg : ∀ u, (fa u && fb u) = g4 u) : False := by
  have h01 := hvg ![true, true, false, false]
  have ha01 : fa ![true, true, false, false] = true := by
    have h1 : g4 ![true, true, false, false] = true := rfl
    rw [h1, Bool.and_eq_true] at h01; exact h01.1
  have h23 := hvg ![false, false, true, true]
  have hb23 : fb ![false, false, true, true] = true := by
    have h1 : g4 ![false, false, true, true] = true := rfl
    rw [h1, Bool.and_eq_true] at h23; exact h23.2
  have ha03 : fa ![true, false, false, true] = true := by
    rw [hdepA ![true, false, false, true] ![true, true, false, false]
      (fun k hk => by rw [hA] at hk; fin_cases k <;> simp at hk ⊢)]
    exact ha01
  have hb03 : fb ![true, false, false, true] = true := by
    rw [hdepB ![true, false, false, true] ![false, false, true, true]
      (fun k hk => by rw [hB] at hk; fin_cases k <;> simp at hk ⊢)]
    exact hb23
  have h03 := hvg ![true, false, false, true]
  rw [ha03, hb03] at h03
  simp [g4] at h03

lemma g4_not_or_split (fa fb : (Fin 4 → Bool) → Bool)
    (A B : Finset (Fin 4))
    (hdepA : ∀ u1 u2, (∀ k ∈ A, u1 k = u2 k) → fa u1 = fa u2)
    (hdepB : ∀ u1 u2, (∀ k ∈ B, u1 k = u2 k) → fb u1 = fb u2)
    (hA : A = {0, 1}) (hB : B = {2, 3})
    (hvg : ∀ u, (fa u || fb u) = g4 u) : False := by
  have h1 := hvg ![false, true, false, false]
  have ha1 : fa ![false, true, false, false] = false := by
    have h0 : g4 ![false, true, false, false] = false := rfl
    rw [h0, Bool.or_eq_false_iff] at h1; exact h1.1
  have h2 := hvg ![false, false, true, false]
  have hb2 : fb ![false, false, true, false] = false := by
    have h0 : g4 ![false, false, true, false] = false := rfl
    rw [h0, Bool.or_eq_false_iff] at h2; exact h2.2
  have ha12 : fa ![false, true, true, false] = false := by
    rw [hdepA ![false, true, true, false] ![false, true, false, false]
      (fun k hk => by rw [hA] at hk; fin_cases k <;> simp at hk ⊢)]
    exact ha1
  have hb12 : fb ![false, true, true, false] = false := by
    rw [hdepB ![false, true, true, false] ![false, false, true, false]
      (fun k hk => by rw [hB] at hk; fin_cases k <;> simp at hk ⊢)]
    exact hb2
  have h12 := hvg ![false, true, true, false]
  rw [ha12, hb12] at h12
  simp [g4] at h12

lemma card_biUnion_eq_iff_disjoint {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (f : α → Finset β) :
    (s.biUnion f).card = s.sum (fun i => (f i).card) →
    (s : Set α).PairwiseDisjoint f := by
  classical
  induction s using Finset.induction_on with
  | empty => intro _; simp
  | insert a s ha ih =>
    intro h
    rw [Finset.biUnion_insert, Finset.sum_insert ha] at h
    have h1 : (f a ∪ s.biUnion f).card ≤ (f a).card + (s.biUnion f).card := Finset.card_union_le _ _
    have h2 : (s.biUnion f).card ≤ s.sum (fun i => (f i).card) := Finset.card_biUnion_le
    have heq1 : (f a ∪ s.biUnion f).card = (f a).card + (s.biUnion f).card := by omega
    have heq2 : (s.biUnion f).card = s.sum (fun i => (f i).card) := by omega
    have hdisj : Disjoint (f a) (s.biUnion f) := Finset.card_union_eq_card_add_card.mp heq1
    have hp := ih heq2
    intro x hx y hy hxy
    simp only [Finset.coe_insert, Set.mem_insert_iff] at hx hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · exact (hxy rfl).elim
    · exact Disjoint.mono_right (Finset.subset_biUnion_of_mem f hy) hdisj
    · exact (Disjoint.mono_right (Finset.subset_biUnion_of_mem f hx) hdisj).symm
    · exact hp hx hy hxy

def stepReach (D : Circuit) (u v : ℕ) : Prop :=
  ∃ j : Fin D.gates.length, v = 8 + j.val ∧ u ∈ (D.gates.get j).inputs

def Reach (D : Circuit) (u v : ℕ) : Prop :=
  Relation.ReflTransGen (stepReach D) u v

lemma reach_le {D : Circuit} (hws : WellStructured 8 D) {u v : ℕ} (h : Reach D u v) : u ≤ v := by
  induction h with
  | refl => exact le_rfl
  | tail _ hstep ih =>
    rcases hstep with ⟨j, rfl, hmem⟩
    have hlt := ws_back hws j.val j.isLt _ (by simpa using hmem)
    omega

lemma wval_eq_of_agree_on_reach {D : Circuit} (hws : WellStructured 8 D)
    {y1 y2 : Fin 8 → Bool} (v : ℕ) (hv : v < 8 + D.gates.length)
    (hagree : ∀ i : Fin 8, Reach D i.val v → y1 i = y2 i) :
    wval D y1 v = wval D y2 v := by
  induction v using Nat.strong_induction_on with
  | ind v ih =>
    by_cases h8 : v < 8
    · rw [wval_input D y1 v h8, wval_input D y2 v h8]
      exact hagree ⟨v, h8⟩ Relation.ReflTransGen.refl
    · have hj : v - 8 < D.gates.length := by omega
      have hv' : v = 8 + (v - 8) := by omega
      rw [hv', wval_gate D y1 (v - 8) hj (ws_back hws _ hj),
          wval_gate D y2 (v - 8) hj (ws_back hws _ hj)]
      congr 1
      apply List.map_congr_left
      intro a ha
      have halt : a < 8 + (v - 8) := ws_back hws (v - 8) hj a ha
      apply ih a (by omega) (by omega)
      intro i hi
      apply hagree i
      exact Relation.ReflTransGen.tail hi ⟨⟨v - 8, hj⟩, hv', by simpa using ha⟩

lemma f1_le7_structure (D : Circuit) (hws : WellStructured 8 D) (hsz : D.size ≤ 7)
    (hout_lt : D.output < 8 + D.gates.length)
    (heval : ∀ y : Fin 8 → Bool, wval D y D.output = f1 y) :
    (∀ j : Fin D.gates.length, Reach D (8 + j.val) D.output →
      ((D.gates.get j).op = GateOp.and ∨ (D.gates.get j).op = GateOp.or) ∧
      ∃ a b, a < 8 + j.val ∧ b < 8 + j.val ∧ a ≠ b ∧ (D.gates.get j).inputs = [a, b]) ∧
    (∀ j1 j2 : Fin D.gates.length, Reach D (8 + j1.val) D.output → Reach D (8 + j2.val) D.output →
      j1 ≠ j2 → ∀ w, w ∈ (D.gates.get j1).inputs → w ∈ (D.gates.get j2).inputs → False) := by
  classical
  have hout_ge8 : 8 ≤ D.output := by
    by_contra hlt
    have hlt' : D.output < 8 := by omega
    have h0 : ∃ i : Fin 8, i.val ≠ D.output := by
      by_cases h0 : D.output = 0
      · exact ⟨1, by omega⟩
      · exact ⟨0, by omega⟩
    obtain ⟨i, hi⟩ := h0
    obtain ⟨y, hy⟩ := f1_essential i
    have h1 := heval y
    have h2 := heval (Function.update y i (!y i))
    rw [wval_input D y D.output hlt'] at h1
    rw [wval_input D _ D.output hlt'] at h2
    have hne : (⟨D.output, hlt'⟩ : Fin 8) ≠ i := fun h => hi (congrArg Fin.val h).symm
    rw [Function.update_of_ne hne] at h2
    exact hy (h1.symm.trans h2)
  let R : Finset (Fin D.gates.length) :=
    Finset.univ.filter (fun j => Reach D (8 + j.val) D.output)
  have hout_idx_lt : D.output - 8 < D.gates.length := by omega
  have hout_mem : D.output ∈ R.image (fun j : Fin D.gates.length => 8 + j.val) := by
    rw [Finset.mem_image]
    refine ⟨⟨D.output - 8, hout_idx_lt⟩, ?_, by dsimp only; omega⟩
    simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]
    have : 8 + (D.output - 8) = D.output := by omega
    rw [this]
    exact Relation.ReflTransGen.refl
  have hin_read : ∀ i : Fin 8, ∃ j ∈ R, i.val ∈ (D.gates.get j).inputs := by
    intro i
    have hreach : Reach D i.val D.output := by
      by_contra hnr
      obtain ⟨y, hy⟩ := f1_essential i
      have heq := wval_eq_of_agree_on_reach hws D.output hout_lt
        (y1 := y) (y2 := Function.update y i (!y i)) (fun k hk => by
          have hne : k ≠ i := fun h => hnr (h ▸ hk)
          exact (Function.update_of_ne hne _ _).symm)
      rw [heval, heval] at heq
      exact hy heq
    rcases Relation.ReflTransGen.cases_head hreach with heq | ⟨w, hstep, htail⟩
    · have := i.isLt; omega
    · rcases hstep with ⟨j, rfl, hmem⟩
      exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, htail⟩, hmem⟩
  have hgate_read : ∀ j ∈ R, 8 + j.val ≠ D.output →
      ∃ k ∈ R, 8 + j.val ∈ (D.gates.get k).inputs := by
    intro j hj hne
    have hreach : Reach D (8 + j.val) D.output := (Finset.mem_filter.mp hj).2
    rcases Relation.ReflTransGen.cases_head hreach with heq | ⟨w, hstep, htail⟩
    · exact (hne heq).elim
    · rcases hstep with ⟨k, rfl, hmem⟩
      exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, htail⟩, hmem⟩
  let Wreq : Finset ℕ :=
    (Finset.range 8) ∪ ((R.image (fun j : Fin D.gates.length => 8 + j.val)).erase D.output)
  have hdisj_W : Disjoint (Finset.range 8)
      ((R.image (fun j : Fin D.gates.length => 8 + j.val)).erase D.output) := by
    rw [Finset.disjoint_left]
    intro w hw1 hw2
    rw [Finset.mem_range] at hw1
    rw [Finset.mem_erase, Finset.mem_image] at hw2
    rcases hw2.2 with ⟨j, _, rfl⟩
    omega
  have hWreq_card : Wreq.card = R.card + 7 := by
    rw [Finset.card_union_of_disjoint hdisj_W, Finset.card_range,
        Finset.card_erase_of_mem hout_mem,
        Finset.card_image_of_injective _ (fun a b h => Fin.ext (by omega))]
    have hRpos : 1 ≤ R.card := Finset.card_pos.mpr ⟨⟨D.output - 8, hout_idx_lt⟩, by
      simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]
      have : 8 + (D.output - 8) = D.output := by omega
      rw [this]; exact Relation.ReflTransGen.refl⟩
    omega
  let insFin (j : Fin D.gates.length) : Finset ℕ := (D.gates.get j).inputs.toFinset
  have hsub : Wreq ⊆ R.biUnion insFin := by
    intro w hw
    rw [Finset.mem_biUnion]
    simp only [Wreq, Finset.mem_union, Finset.mem_range, Finset.mem_erase, Finset.mem_image] at hw
    rcases hw with hw8 | ⟨hne, ⟨j, hjR, rfl⟩⟩
    · obtain ⟨k, hkR, hmem⟩ := hin_read ⟨w, hw8⟩
      exact ⟨k, hkR, List.mem_toFinset.mpr hmem⟩
    · obtain ⟨k, hkR, hmem⟩ := hgate_read j hjR hne
      exact ⟨k, hkR, List.mem_toFinset.mpr hmem⟩
  have hlen_le2 : ∀ j ∈ R, (D.gates.get j).inputs.length ≤ 2 := by
    intro j _
    rcases hws j with ⟨_, _, _, hins⟩ | ⟨_, _, _, _, _, hins⟩
    · rw [hins]; simp
    · rw [hins]; simp
  have hR_le7 : R.card ≤ 7 := by
    calc R.card ≤ (Finset.univ : Finset (Fin D.gates.length)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = D.gates.length := by simp
      _ ≤ 7 := hsz
  have hsum_le : R.sum (fun j => (insFin j).card) ≤ 2 * R.card := by
    calc R.sum (fun j => (insFin j).card)
        ≤ R.sum (fun j => (D.gates.get j).inputs.length) :=
          Finset.sum_le_sum (fun j _ => List.toFinset_card_le _)
      _ ≤ R.sum (fun _ => 2) := Finset.sum_le_sum hlen_le2
      _ = 2 * R.card := by simp [Nat.mul_comm]
  have hcard_chain : R.card + 7 ≤ (R.biUnion insFin).card := by
    rw [← hWreq_card]; exact Finset.card_le_card hsub
  have hbi_le : (R.biUnion insFin).card ≤ R.sum (fun j => (insFin j).card) := Finset.card_biUnion_le
  have hbi_eq : (R.biUnion insFin).card = R.sum (fun j => (insFin j).card) := by omega
  have hsum_eq : R.sum (fun j => (insFin j).card) = 2 * R.card := by omega
  have hpair_disj : (R : Set (Fin D.gates.length)).PairwiseDisjoint insFin :=
    card_biUnion_eq_iff_disjoint R insFin hbi_eq
  have hcard_eq2 : ∀ j ∈ R, (insFin j).card = 2 := by
    intro j hj
    by_contra hne
    have hlt : (insFin j).card < 2 := by
      have h1 : (insFin j).card ≤ 2 := (List.toFinset_card_le _).trans (hlen_le2 j hj)
      omega
    have hstrict : R.sum (fun k => (insFin k).card) < R.sum (fun _ => 2) :=
      Finset.sum_lt_sum (fun k hk => (List.toFinset_card_le _).trans (hlen_le2 k hk)) ⟨j, hj, hlt⟩
    simp [Nat.mul_comm] at hstrict
    omega
  constructor
  · intro j hjr
    have hj : j ∈ R := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjr⟩
    have hc2 := hcard_eq2 j hj
    dsimp only [insFin] at hc2
    rcases hws j with ⟨_, a, _, hins⟩ | ⟨hop, a, b, ha, hb, hins⟩
    · rw [hins] at hc2; simp at hc2
    · refine ⟨hop, a, b, ha, hb, ?_, hins⟩
      intro heq; subst heq
      rw [hins] at hc2; simp at hc2
  · intro j1 j2 hj1 hj2 hne w hw1 hw2
    have hd := hpair_disj
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj1⟩)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj2⟩) hne
    exact Finset.disjoint_left.mp hd (List.mem_toFinset.mpr hw1) (List.mem_toFinset.mpr hw2)

lemma spec_mono (u1 u2 : Fin 4 → Bool) (hle : ∀ k, u1 k = true → u2 k = true)
    (i : Fin 8) (h : spec u1 i = true) : spec u2 i = true := by
  fin_cases i
  · simpa [spec] using h
  · simpa [spec] using h
  · simpa [spec] using hle 0 (by simpa [spec] using h)
  · simpa [spec] using hle 2 (by simpa [spec] using h)
  · simpa [spec] using h
  · simpa [spec] using hle 3 (by simpa [spec] using h)
  · simpa [spec] using h
  · simpa [spec] using hle 1 (by simpa [spec] using h)

lemma reach_mono_spec (D : Circuit) (hws : WellStructured 8 D)
    (hout_lt : D.output < 8 + D.gates.length)
    (hall_ao : ∀ j : Fin D.gates.length, Reach D (8 + j.val) D.output →
      ((D.gates.get j).op = GateOp.and ∨ (D.gates.get j).op = GateOp.or) ∧
      ∃ a b, a < 8 + j.val ∧ b < 8 + j.val ∧ a ≠ b ∧ (D.gates.get j).inputs = [a, b])
    (v : ℕ) (hv : Reach D v D.output) (u1 u2 : Fin 4 → Bool)
    (hle : ∀ k, u1 k = true → u2 k = true)
    (hv1 : wval D (spec u1) v = true) : wval D (spec u2) v = true := by
  induction v using Nat.strong_induction_on with
  | ind v ih =>
    by_cases h8 : v < 8
    · rw [wval_input D (spec u1) v h8] at hv1
      rw [wval_input D (spec u2) v h8]
      exact spec_mono u1 u2 hle ⟨v, h8⟩ hv1
    · have hjlt : v - 8 < D.gates.length := by have := reach_le hws hv; omega
      have hv' : v = 8 + (v - 8) := by omega
      let j : Fin D.gates.length := ⟨v - 8, hjlt⟩
      have hjv : j.val = v - 8 := rfl
      have hjr : Reach D (8 + j.val) D.output := by simpa [j, ← hv'] using hv
      obtain ⟨hop, a, b, ha, hb, _, hins⟩ := hall_ao j hjr
      have ha' : a < v := by omega
      have hb' : b < v := by omega
      have haR : Reach D a D.output := Relation.ReflTransGen.head ⟨j, hv', by rw [hins]; simp⟩ hv
      have hbR : Reach D b D.output := Relation.ReflTransGen.head ⟨j, hv', by rw [hins]; simp⟩ hv
      rcases hop with hop | hop
      · rw [hv', wval_and D (spec u1) j.val a b j.isLt (by simpa using hop) (by simpa using hins) ha hb] at hv1
        rw [hv', wval_and D (spec u2) j.val a b j.isLt (by simpa using hop) (by simpa using hins) ha hb]
        rw [Bool.and_eq_true] at hv1 ⊢
        exact ⟨ih a ha' haR hv1.1, ih b hb' hbR hv1.2⟩
      · rw [hv', wval_or D (spec u1) j.val a b j.isLt (by simpa using hop) (by simpa using hins) ha hb] at hv1
        rw [hv', wval_or D (spec u2) j.val a b j.isLt (by simpa using hop) (by simpa using hins) ha hb]
        rw [Bool.or_eq_true] at hv1 ⊢
        rcases hv1 with h | h
        · exact Or.inl (ih a ha' haR h)
        · exact Or.inr (ih b hb' hbR h)

lemma reach_inputs_disj (D : Circuit) (hws : WellStructured 8 D)
    (hdisj_in : ∀ j1 j2 : Fin D.gates.length, Reach D (8 + j1.val) D.output → Reach D (8 + j2.val) D.output →
      j1 ≠ j2 → ∀ w, w ∈ (D.gates.get j1).inputs → w ∈ (D.gates.get j2).inputs → False)
    (j : Fin D.gates.length) (hjr : Reach D (8 + j.val) D.output)
    (a b : ℕ) (hab : a ≠ b) (ha : a ∈ (D.gates.get j).inputs) (hb : b ∈ (D.gates.get j).inputs)
    (w : ℕ) (hwa : Reach D w a) (hwb : Reach D w b) : False := by
  have hunique : ∀ x y1 y2, Reach D x y1 → Reach D x y2 →
      Reach D y1 D.output → Reach D y2 D.output →
      Reach D y1 y2 ∨ Reach D y2 y1 := by
    intro x y1 y2 h1
    induction h1 using Relation.ReflTransGen.head_induction_on with
    | refl => intro h2 _ _; exact Or.inl h2
    | head hst1 htl1 ih =>
      intro h2 hy1 hy2
      rcases Relation.ReflTransGen.cases_head h2 with rfl | ⟨z2, hst2, htl2⟩
      · exact Or.inr (Relation.ReflTransGen.head hst1 htl1)
      · rcases hst1 with ⟨k1, rfl, hm1⟩
        rcases hst2 with ⟨k2, rfl, hm2⟩
        have hk1 : Reach D (8 + k1.val) D.output := Relation.ReflTransGen.trans htl1 hy1
        have hk2 : Reach D (8 + k2.val) D.output := Relation.ReflTransGen.trans htl2 hy2
        have heqk : k1 = k2 := by
          by_contra hne
          exact hdisj_in k1 k2 hk1 hk2 hne _ hm1 hm2
        subst heqk
        exact ih htl2 hy1 hy2
  have haR : Reach D a D.output := Relation.ReflTransGen.head ⟨j, rfl, ha⟩ hjr
  have hbR : Reach D b D.output := Relation.ReflTransGen.head ⟨j, rfl, hb⟩ hjr
  have hle_ab : ∀ x y, x ≠ y → x ∈ (D.gates.get j).inputs → y ∈ (D.gates.get j).inputs →
      Reach D x y → False := by
    intro x y hxy hx hy hreach
    rcases Relation.ReflTransGen.cases_head hreach with rfl | ⟨z, hst, htl⟩
    · exact hxy rfl
    · rcases hst with ⟨k, rfl, hmk⟩
      have hk : Reach D (8 + k.val) D.output :=
        Relation.ReflTransGen.trans htl (Relation.ReflTransGen.head ⟨j, rfl, hy⟩ hjr)
      have hkj : k = j := by
        by_contra hne
        exact hdisj_in k j hk hjr hne x hmk hx
      rw [hkj] at htl
      have h1 := reach_le hws htl
      have h2 := ws_back hws j.val j.isLt y (by simpa using hy)
      omega
  rcases hunique w a b hwa hwb haR hbR with h1 | h2
  · exact hle_ab a b hab ha hb h1
  · exact hle_ab b a hab.symm hb ha h2

def idx4 (k : Fin 4) : Fin 8 := ![2, 7, 3, 5] k

lemma no_read_once_g4 (D : Circuit) (hws : WellStructured 8 D)
    (hout_lt : D.output < 8 + D.gates.length)
    (hall_ao : ∀ j : Fin D.gates.length, Reach D (8 + j.val) D.output →
      ((D.gates.get j).op = GateOp.and ∨ (D.gates.get j).op = GateOp.or) ∧
      ∃ a b, a < 8 + j.val ∧ b < 8 + j.val ∧ a ≠ b ∧ (D.gates.get j).inputs = [a, b])
    (hdisj_in : ∀ j1 j2 : Fin D.gates.length, Reach D (8 + j1.val) D.output → Reach D (8 + j2.val) D.output →
      j1 ≠ j2 → ∀ w, w ∈ (D.gates.get j1).inputs → w ∈ (D.gates.get j2).inputs → False)
    (v : ℕ) (hv : Reach D v D.output)
    (hvg : ∀ u : Fin 4 → Bool, wval D (spec u) v = g4 u) : False := by
  classical
  induction v using Nat.strong_induction_on with
  | ind v ih =>
    by_cases h8 : v < 8
    · have hconst_or_one : ∀ u : Fin 4 → Bool, wval D (spec u) v = spec u ⟨v, h8⟩ :=
        fun u => wval_input D (spec u) v h8
      interval_cases v
      · have h1 := (hconst_or_one ![false, false, false, false]).symm.trans (hvg _); simp [spec, g4] at h1
      · have h1 := (hconst_or_one ![false, false, false, false]).symm.trans (hvg _); simp [spec, g4] at h1
      · have h1 := (hconst_or_one ![true, false, false, false]).symm.trans (hvg _); simp [spec, g4] at h1
      · have h1 := (hconst_or_one ![false, false, true, false]).symm.trans (hvg _); simp [spec, g4] at h1
      · have h1 := (hconst_or_one ![true, true, false, false]).symm.trans (hvg _); simp [spec, g4] at h1
      · have h1 := (hconst_or_one ![false, false, false, true]).symm.trans (hvg _); simp [spec, g4] at h1
      · have h1 := (hconst_or_one ![true, true, false, false]).symm.trans (hvg _); simp [spec, g4] at h1
      · have h1 := (hconst_or_one ![false, true, false, false]).symm.trans (hvg _); simp [spec, g4] at h1
    · have hjlt : v - 8 < D.gates.length := by have := reach_le hws hv; omega
      have hv' : v = 8 + (v - 8) := by omega
      let j : Fin D.gates.length := ⟨v - 8, hjlt⟩
      have hjv : j.val = v - 8 := rfl
      have hjr : Reach D (8 + j.val) D.output := by simpa [j, ← hv'] using hv
      obtain ⟨hop, a, b, ha, hb, hab, hins⟩ := hall_ao j hjr
      have ha' : a < v := by omega
      have hb' : b < v := by omega
      have ha_lt : a < 8 + D.gates.length := by omega
      have hb_lt : b < 8 + D.gates.length := by omega
      have haR : Reach D a D.output := Relation.ReflTransGen.head ⟨j, hv', by rw [hins]; simp⟩ hv
      have hbR : Reach D b D.output := Relation.ReflTransGen.head ⟨j, hv', by rw [hins]; simp⟩ hv
      let A : Finset (Fin 4) := Finset.univ.filter (fun k => Reach D (idx4 k).val a)
      let B : Finset (Fin 4) := Finset.univ.filter (fun k => Reach D (idx4 k).val b)
      have hdepA : ∀ u1 u2 : Fin 4 → Bool, (∀ k ∈ A, u1 k = u2 k) → wval D (spec u1) a = wval D (spec u2) a := by
        intro u1 u2 hag
        apply wval_eq_of_agree_on_reach hws a ha_lt
        intro i hi
        fin_cases i
        all_goals simp [spec]
        · exact hag 0 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
        · exact hag 2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
        · exact hag 3 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
        · exact hag 1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
      have hdepB : ∀ u1 u2 : Fin 4 → Bool, (∀ k ∈ B, u1 k = u2 k) → wval D (spec u1) b = wval D (spec u2) b := by
        intro u1 u2 hag
        apply wval_eq_of_agree_on_reach hws b hb_lt
        intro i hi
        fin_cases i
        all_goals simp [spec]
        · exact hag 0 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
        · exact hag 2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
        · exact hag 3 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
        · exact hag 1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
      have hdisj4 : Disjoint A B := by
        rw [Finset.disjoint_left]
        intro k hka hkb
        exact reach_inputs_disj D hws hdisj_in j hjr a b hab (by rw [hins]; simp) (by rw [hins]; simp)
          (idx4 k).val (Finset.mem_filter.mp hka).2 (Finset.mem_filter.mp hkb).2
      have hstep_congr : ∀ u1 u2, wval D (spec u1) a = wval D (spec u2) a →
          wval D (spec u1) b = wval D (spec u2) b →
          wval D (spec u1) v = wval D (spec u2) v := by
        intro u1 u2 hae hbe
        rcases hop with hop' | hop'
        · rw [hv', wval_and D (spec u1) j.val a b j.isLt (by simpa using hop') (by simpa using hins) ha hb,
              wval_and D (spec u2) j.val a b j.isLt (by simpa using hop') (by simpa using hins) ha hb, hae, hbe]
        · rw [hv', wval_or D (spec u1) j.val a b j.isLt (by simpa using hop') (by simpa using hins) ha hb,
              wval_or D (spec u2) j.val a b j.isLt (by simpa using hop') (by simpa using hins) ha hb, hae, hbe]
      have hunion4 : A ∪ B = Finset.univ := by
        ext k
        simp only [Finset.mem_union, Finset.mem_univ, iff_true]
        by_contra hnot
        have hna : k ∉ A := fun h => hnot (Or.inl h)
        have hnb : k ∉ B := fun h => hnot (Or.inr h)
        obtain ⟨u, hu⟩ := g4_essential k
        have hae := hdepA u (Function.update u k (!u k)) (fun m hm => by
          have hne : m ≠ k := fun h => hna (h ▸ hm)
          exact (Function.update_of_ne hne _ _).symm)
        have hbe := hdepB u (Function.update u k (!u k)) (fun m hm => by
          have hne : m ≠ k := fun h => hnb (h ▸ hm)
          exact (Function.update_of_ne hne _ _).symm)
        have heq := hstep_congr u (Function.update u k (!u k)) hae hbe
        rw [hvg, hvg] at heq
        exact hu heq
      have hnonconstA : A.Nonempty → ∃ u1 u2 : Fin 4 → Bool, wval D (spec u1) a ≠ wval D (spec u2) a := by
        rintro ⟨k, hk⟩
        by_contra hall
        have hall' : ∀ u1 u2, wval D (spec u1) a = wval D (spec u2) a := fun u1 u2 => by
          by_contra hne; exact hall ⟨u1, u2, hne⟩
        obtain ⟨u, hu⟩ := g4_essential k
        have hbe := hdepB u (Function.update u k (!u k)) (fun m hm => by
          have hne : m ≠ k := fun h => Finset.disjoint_left.mp hdisj4 hk (h ▸ hm)
          exact (Function.update_of_ne hne _ _).symm)
        have hae := hall' u (Function.update u k (!u k))
        have heq := hstep_congr u (Function.update u k (!u k)) hae hbe
        rw [hvg, hvg] at heq
        exact hu heq
      have hnonconstB : B.Nonempty → ∃ u1 u2 : Fin 4 → Bool, wval D (spec u1) b ≠ wval D (spec u2) b := by
        rintro ⟨k, hk⟩
        by_contra hall
        have hall' : ∀ u1 u2, wval D (spec u1) b = wval D (spec u2) b := fun u1 u2 => by
          by_contra hne; exact hall ⟨u1, u2, hne⟩
        obtain ⟨u, hu⟩ := g4_essential k
        have hae := hdepA u (Function.update u k (!u k)) (fun m hm => by
          have hne : m ≠ k := fun h => Finset.disjoint_left.mp hdisj4 (h ▸ hm) hk
          exact (Function.update_of_ne hne _ _).symm)
        have hbe := hall' u (Function.update u k (!u k))
        have heq := hstep_congr u (Function.update u k (!u k)) hae hbe
        rw [hvg, hvg] at heq
        exact hu heq
      by_cases hae : A = ∅
      · have hca : ∀ u, wval D (spec u) a = wval D (spec (fun _ => false)) a :=
          fun u => hdepA u _ (by simp [hae])
        rcases hop with hop' | hop'
        · cases hval : wval D (spec (fun _ => false)) a
          · have h1 := hvg (fun _ => true)
            rw [hv', wval_and D _ j.val a b j.isLt (by simpa using hop') (by simpa using hins) ha hb, hca, hval] at h1
            simp [g4] at h1
          · exact ih b hb' hbR (fun u => by
              have h1 := hvg u
              rw [hv', wval_and D _ j.val a b j.isLt (by simpa using hop') (by simpa using hins) ha hb, hca, hval] at h1
              simpa using h1)
        · cases hval : wval D (spec (fun _ => false)) a
          · exact ih b hb' hbR (fun u => by
              have h1 := hvg u
              rw [hv', wval_or D _ j.val a b j.isLt (by simpa using hop') (by simpa using hins) ha hb, hca, hval] at h1
              simpa using h1)
          · have h1 := hvg (fun _ => false)
            rw [hv', wval_or D _ j.val a b j.isLt (by simpa using hop') (by simpa using hins) ha hb, hca, hval] at h1
            simp [g4] at h1
      · by_cases hbe : B = ∅
        · have hcb : ∀ u, wval D (spec u) b = wval D (spec (fun _ => false)) b :=
            fun u => hdepB u _ (by simp [hbe])
          rcases hop with hop' | hop'
          · cases hval : wval D (spec (fun _ => false)) b
            · have h1 := hvg (fun _ => true)
              rw [hv', wval_and D _ j.val a b j.isLt (by simpa using hop') (by simpa using hins) ha hb, hcb, hval] at h1
              simp [g4] at h1
            · exact ih a ha' haR (fun u => by
                have h1 := hvg u
                rw [hv', wval_and D _ j.val a b j.isLt (by simpa using hop') (by simpa using hins) ha hb, hcb, hval] at h1
                simpa using h1)
          · cases hval : wval D (spec (fun _ => false)) b
            · exact ih a ha' haR (fun u => by
                have h1 := hvg u
                rw [hv', wval_or D _ j.val a b j.isLt (by simpa using hop') (by simpa using hins) ha hb, hcb, hval] at h1
                simpa using h1)
            · have h1 := hvg (fun _ => false)
              rw [hv', wval_or D _ j.val a b j.isLt (by simpa using hop') (by simpa using hins) ha hb, hcb, hval] at h1
              simp [g4] at h1
        · have hneA : A.Nonempty := Finset.nonempty_iff_ne_empty.mpr hae
          have hneB : B.Nonempty := Finset.nonempty_iff_ne_empty.mpr hbe
          have hbot : ∀ x, Reach D x D.output →
              (∃ u1 u2 : Fin 4 → Bool, wval D (spec u1) x ≠ wval D (spec u2) x) →
              wval D (spec (fun _ => false)) x = false ∧ wval D (spec (fun _ => true)) x = true := by
            intro x hxR ⟨u1, u2, h12⟩
            constructor
            · cases h0 : wval D (spec (fun _ => false)) x
              · rfl
              · exfalso
                have hall : ∀ u, wval D (spec u) x = true := fun u =>
                  reach_mono_spec D hws hout_lt hall_ao x hxR (fun _ => false) u (by simp) h0
                exact h12 ((hall u1).trans (hall u2).symm)
            · cases h1 : wval D (spec (fun _ => true)) x
              · exfalso
                have hall : ∀ u, wval D (spec u) x = false := fun u => by
                  cases hu : wval D (spec u) x
                  · rfl
                  · have := reach_mono_spec D hws hout_lt hall_ao x hxR u (fun _ => true) (by simp) hu
                    rw [h1] at this; cases this
                exact h12 ((hall u1).trans (hall u2).symm)
              · rfl
          have hbotA := hbot a haR (hnonconstA hneA)
          have hbotB := hbot b hbR (hnonconstB hneB)
          have ha_on_B : wval D (spec (fun k => decide (k ∈ B))) a = false := by
            rw [hdepA _ (fun _ => false) (fun k hk => by
              simp only [decide_eq_false_iff_not]; exact Finset.disjoint_left.mp hdisj4 hk), hbotA.1]
          have hb_on_A : wval D (spec (fun k => decide (k ∈ A))) b = false := by
            rw [hdepB _ (fun _ => false) (fun k hk => by
              simp only [decide_eq_false_iff_not]; exact Finset.disjoint_right.mp hdisj4 hk), hbotB.1]
          have ha_on_A : wval D (spec (fun k => decide (k ∈ A))) a = true := by
            rw [hdepA _ (fun _ => true) (fun k hk => by simp only [decide_eq_true_eq]; exact hk), hbotA.2]
          have hb_on_B : wval D (spec (fun k => decide (k ∈ B))) b = true := by
            rw [hdepB _ (fun _ => true) (fun k hk => by simp only [decide_eq_true_eq]; exact hk), hbotB.2]
          rcases hop with hop' | hop'
          · have hvg_and : ∀ u, (wval D (spec u) a && wval D (spec u) b) = g4 u := fun u => by
              rw [← wval_and D (spec u) j.val a b j.isLt (by simpa using hop') (by simpa using hins) ha hb, ← hv']
              exact hvg u
            have hgA : g4 (fun k => decide (k ∈ A)) = false := by
              rw [← hvg_and, hb_on_A]; simp
            have hgB : g4 (fun k => decide (k ∈ B)) = false := by
              rw [← hvg_and, ha_on_B]; simp
            rcases g4_class_and A B hneA hneB hdisj4 hunion4 hgA hgB with ⟨hA, hB⟩ | ⟨hA, hB⟩
            · exact g4_not_and_split (fun u => wval D (spec u) a) (fun u => wval D (spec u) b) A B hdepA hdepB hA hB hvg_and
            · exact g4_not_and_split (fun u => wval D (spec u) b) (fun u => wval D (spec u) a) B A hdepB hdepA hB hA
                (fun u => by rw [Bool.and_comm]; exact hvg_and u)
          · have hvg_or : ∀ u, (wval D (spec u) a || wval D (spec u) b) = g4 u := fun u => by
              rw [← wval_or D (spec u) j.val a b j.isLt (by simpa using hop') (by simpa using hins) ha hb, ← hv']
              exact hvg u
            have hgA : g4 (fun k => decide (k ∈ A)) = true := by
              rw [← hvg_or, ha_on_A]; simp
            have hgB : g4 (fun k => decide (k ∈ B)) = true := by
              rw [← hvg_or, hb_on_B]; simp
            rcases g4_class_or A B hneA hneB hdisj4 hunion4 hgA hgB with ⟨hA, hB⟩ | ⟨hA, hB⟩
            · exact g4_not_or_split (fun u => wval D (spec u) a) (fun u => wval D (spec u) b) A B hdepA hdepB hA hB hvg_or
            · exact g4_not_or_split (fun u => wval D (spec u) b) (fun u => wval D (spec u) a) B A hdepB hdepA hB hA
                (fun u => by rw [Bool.or_comm]; exact hvg_or u)

lemma no_circuit_f1_le7 (D : Circuit) (hws : WellStructured 8 D) (hsz : D.size ≤ 7)
    (hout_lt : D.output < 8 + D.gates.length)
    (heval : ∀ y : Fin 8 → Bool, wval D y D.output = f1 y) : False := by
  obtain ⟨hall_ao, hdisj_in⟩ := f1_le7_structure D hws hsz hout_lt heval
  exact no_read_once_g4 D hws hout_lt hall_ao hdisj_in D.output Relation.ReflTransGen.refl
    (fun u => (heval (spec u)).trans (f1_spec u))

lemma reduce_prefix (gs : List Gate)
    (hws : ∀ j : Fin gs.length,
      ((gs.get j).op = GateOp.not ∧ ∃ a, a < 9 + j.val ∧ (gs.get j).inputs = [a]) ∨
      (((gs.get j).op = GateOp.and ∨ (gs.get j).op = GateOp.or) ∧
        ∃ a b, a < b ∧ b < 9 + j.val ∧ (gs.get j).inputs = [a, b]))
    (h0 : gs.head? = some ⟨GateOp.or, [0, 1]⟩)
    (h1 : gs.tail.head? = some ⟨GateOp.or, [0, 2]⟩) :
    let wC (y : Fin 8 → Bool) (w : ℕ) : Bool := (W gs (List.ofFn (ext y))).getD w false
    let isConst (w : ℕ) : Prop := ∃ b : Bool, ∀ y : Fin 8 → Bool, wC y w = b
    let S (j : Fin gs.length) : Prop :=
      2 ≤ j.val ∧ (isConst (9 + j.val) ∨ ∃ a ∈ (gs.get j).inputs, isConst a)
    ∃ (ds : List Gate) (mp : ℕ → ℕ),
      WellStructured 8 ⟨ds, 0⟩ ∧
      ds.length = (Finset.univ.filter (fun j : Fin gs.length => 2 ≤ j.val ∧ ¬ S j)).card ∧
      (∀ w < 9 + gs.length, ¬ isConst w → mp w < 8 + ds.length ∧
        ∀ y : Fin 8 → Bool, (W ds (List.ofFn y)).getD (mp w) false = wC y w) := by
  classical
  have hprefix : ∀ (k : ℕ) (hk : k ≤ gs.length),
      let wC (y : Fin 8 → Bool) (w : ℕ) : Bool := (W gs (List.ofFn (ext y))).getD w false
      let isConst (w : ℕ) : Prop := ∃ b : Bool, ∀ y : Fin 8 → Bool, wC y w = b
      let S (j : Fin gs.length) : Prop :=
        2 ≤ j.val ∧ (isConst (9 + j.val) ∨ ∃ a ∈ (gs.get j).inputs, isConst a)
      ∃ (ds : List Gate) (mp : ℕ → ℕ),
        WellStructured 8 ⟨ds, 0⟩ ∧
        ds.length = (Finset.univ.filter (fun j : Fin gs.length => j.val < k ∧ 2 ≤ j.val ∧ ¬ S j)).card ∧
        (∀ w < 9 + k, ¬ isConst w → mp w < 8 + ds.length ∧
          ∀ y : Fin 8 → Bool, (W ds (List.ofFn y)).getD (mp w) false = wC y w) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨[], fun w => w - 1, ?_, by simp, ?_⟩
      · intro j; exact Fin.elim0 j
      · intro w hw hnc
        dsimp only at hw hnc ⊢
        have hwne0 : w ≠ 0 := by
          intro h0'
          apply hnc
          refine ⟨true, fun y => ?_⟩
          rw [h0', W_prefix gs (List.ofFn (ext y)) 0 (by simp)]
          rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
          rfl
        refine ⟨by simp; omega, fun y => ?_⟩
        rw [W_prefix [] (List.ofFn y) (w - 1) (by simp; omega),
            W_prefix gs (List.ofFn (ext y)) w (by simp; omega)]
        rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn,
            List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
        cases w with
        | zero => omega
        | succ w' =>
          have hsucc : (⟨w' + 1, by omega⟩ : Fin 9) = Fin.succ ⟨w', by omega⟩ := rfl
          simp only [Nat.add_sub_cancel, ext, hsucc, Fin.cons_succ]
    | succ k ih =>
      intro hk
      obtain ⟨ds, mp, hds_ws, hds_len, hmp⟩ := ih (by omega)
      let j : Fin gs.length := ⟨k, hk⟩
      have hjv : j.val = k := rfl
      have hgate_eval : ∀ y : Fin 8 → Bool,
          (W gs (List.ofFn (ext y))).getD (9 + k) false =
            (gs.get j).op.eval ((gs.get j).inputs.map fun a => (W gs (List.ofFn (ext y))).getD a false) := by
        intro y
        have hg := W_gate gs (List.ofFn (ext y)) k hk
        rw [List.length_ofFn] at hg
        rw [hg]
        simp only [List.get_eq_getElem, hjv]
        congr 1
        apply List.map_congr_left
        intro a ha
        rcases hws j with ⟨_, u, hu, hins⟩ | ⟨_, u, v, hu, hv, hins⟩
        · simp only [List.get_eq_getElem, hjv] at hins hu
          rw [hins, List.mem_singleton] at ha
          rw [if_pos (by omega)]
        · simp only [List.get_eq_getElem, hjv] at hins hu hv
          rw [hins, List.mem_cons, List.mem_singleton] at ha
          rcases ha with rfl | rfl <;> rw [if_pos (by omega)]
      by_cases hk2 : k < 2
      · have hconst_k : ∃ b : Bool, ∀ y : Fin 8 → Bool, (W gs (List.ofFn (ext y))).getD (9 + k) false = b := by
          refine ⟨true, fun y => ?_⟩
          rw [hgate_eval y]
          have h0val : (W gs (List.ofFn (ext y))).getD 0 false = true := by
            rw [W_prefix gs (List.ofFn (ext y)) 0 (by simp)]
            rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]; rfl
          have hk01 : k = 0 ∨ k = 1 := by omega
          rcases hk01 with hk0 | hk1
          · have hg0 : gs.get j = ⟨GateOp.or, [0, 1]⟩ := by
              simp only [List.get_eq_getElem, hjv, hk0]
              exact getElem_zero_of_head? h0 (by omega)
            rw [hg0]
            simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, h0val, Bool.true_or]
          · have hg1 : gs.get j = ⟨GateOp.or, [0, 2]⟩ := by
              simp only [List.get_eq_getElem, hjv, hk1]
              exact getElem_one_of_tail_head? h1 (by omega)
            rw [hg1]
            simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, h0val, Bool.true_or]
        refine ⟨ds, mp, hds_ws, ?_, ?_⟩
        · rw [hds_len]
          congr 1; ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor <;> intro ⟨h1', h2', h3'⟩ <;> exact ⟨by omega, h2', h3'⟩
        · intro w hw hnc
          have hlt : w < 9 + k := by
            by_cases heq : w = 9 + k
            · subst heq; exact (hnc hconst_k).elim
            · omega
          exact hmp w hlt hnc
      · have hk2' : 2 ≤ k := by omega
        by_cases hS : (∃ b : Bool, ∀ y : Fin 8 → Bool, (W gs (List.ofFn (ext y))).getD (9 + k) false = b) ∨
            (∃ a ∈ (gs.get j).inputs, ∃ b : Bool, ∀ y : Fin 8 → Bool, (W gs (List.ofFn (ext y))).getD a false = b)
        · have hfilter_eq : (Finset.univ.filter (fun i : Fin gs.length => i.val < k + 1 ∧ 2 ≤ i.val ∧
              ¬ (2 ≤ i.val ∧ ((∃ b, ∀ y, (W gs (List.ofFn (ext y))).getD (9 + i.val) false = b) ∨
                ∃ a ∈ (gs.get i).inputs, ∃ b, ∀ y, (W gs (List.ofFn (ext y))).getD a false = b)))).card =
              (Finset.univ.filter (fun i : Fin gs.length => i.val < k ∧ 2 ≤ i.val ∧
              ¬ (2 ≤ i.val ∧ ((∃ b, ∀ y, (W gs (List.ofFn (ext y))).getD (9 + i.val) false = b) ∨
                ∃ a ∈ (gs.get i).inputs, ∃ b, ∀ y, (W gs (List.ofFn (ext y))).getD a false = b)))).card := by
            congr 1; ext i
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · rintro ⟨hlt, h2i, hni⟩
              refine ⟨?_, h2i, hni⟩
              by_contra hge
              have hieq : i = j := Fin.ext (by omega)
              subst hieq
              exact hni ⟨hk2', hS⟩
            · rintro ⟨hlt, h2i, hni⟩; exact ⟨by omega, h2i, hni⟩
          by_cases hck : ∃ b : Bool, ∀ y : Fin 8 → Bool, (W gs (List.ofFn (ext y))).getD (9 + k) false = b
          · refine ⟨ds, mp, hds_ws, hds_len.trans hfilter_eq.symm, ?_⟩
            intro w hw hnc
            have hlt : w < 9 + k := by
              by_cases heq : w = 9 + k
              · subst heq; exact (hnc hck).elim
              · omega
            exact hmp w hlt hnc
          · have hcopy : ∃ a < 9 + k, (¬ ∃ b : Bool, ∀ y : Fin 8 → Bool, (W gs (List.ofFn (ext y))).getD a false = b) ∧
                ∀ y : Fin 8 → Bool, (W gs (List.ofFn (ext y))).getD (9 + k) false = (W gs (List.ofFn (ext y))).getD a false := by
              rcases hws j with ⟨hop, a, ha, hins⟩ | ⟨hop, a, b, hab, hb, hins⟩
              · rw [hjv] at ha
                rcases hS with hc | ⟨u, hu, cu, hcu⟩
                · exact (hck hc).elim
                · rw [hins, List.mem_singleton] at hu; subst hu
                  exfalso; apply hck; refine ⟨!cu, fun y => ?_⟩
                  rw [hgate_eval y, hop, hins]
                  simp only [List.map_cons, List.map_nil, GateOp.eval, List.headD_cons, hcu y]
              · rw [hjv] at hb
                rcases hS with hc | ⟨u, hu, cu, hcu⟩
                · exact (hck hc).elim
                · rw [hins, List.mem_cons, List.mem_singleton] at hu
                  rcases hu with rfl | rfl
                  · by_cases hcb : ∃ cb : Bool, ∀ y : Fin 8 → Bool, (W gs (List.ofFn (ext y))).getD b false = cb
                    · obtain ⟨cb, hcb⟩ := hcb
                      exfalso; apply hck
                      refine ⟨(gs.get j).op.eval [cu, cb], fun y => ?_⟩
                      rw [hgate_eval y, hins]
                      simp only [List.map_cons, List.map_nil, hcu y, hcb y]
                    · refine ⟨b, hb, hcb, fun y => ?_⟩
                      rw [hgate_eval y, hins]
                      rcases hop with hop | hop
                      · rw [hop]; cases cu
                        · exfalso; apply hck; refine ⟨false, fun z => ?_⟩
                          rw [hgate_eval z, hop, hins]
                          simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, hcu z, Bool.false_and]
                        · simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, hcu y, Bool.true_and, Bool.and_true]
                      · rw [hop]; cases cu
                        · simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, hcu y, Bool.false_or, Bool.or_false]
                        · exfalso; apply hck; refine ⟨true, fun z => ?_⟩
                          rw [hgate_eval z, hop, hins]
                          simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, hcu z, Bool.true_or]
                  · by_cases hca : ∃ ca : Bool, ∀ y : Fin 8 → Bool, (W gs (List.ofFn (ext y))).getD a false = ca
                    · obtain ⟨ca, hca⟩ := hca
                      exfalso; apply hck
                      refine ⟨(gs.get j).op.eval [ca, cu], fun y => ?_⟩
                      rw [hgate_eval y, hins]
                      simp only [List.map_cons, List.map_nil, hca y, hcu y]
                    · refine ⟨a, by omega, hca, fun y => ?_⟩
                      rw [hgate_eval y, hins]
                      rcases hop with hop | hop
                      · rw [hop]; cases cu
                        · exfalso; apply hck; refine ⟨false, fun z => ?_⟩
                          rw [hgate_eval z, hop, hins]
                          simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, hcu z, Bool.and_false, Bool.false_and]
                        · simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, hcu y, Bool.and_true]
                      · rw [hop]; cases cu
                        · simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, hcu y, Bool.or_false]
                        · exfalso; apply hck; refine ⟨true, fun z => ?_⟩
                          rw [hgate_eval z, hop, hins]
                          simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, hcu z, Bool.or_true, Bool.true_or]
            obtain ⟨a, halt, hnca, hceq⟩ := hcopy
            obtain ⟨hmpa_lt, hmpa_ev⟩ := hmp a halt hnca
            let mp' (w : ℕ) : ℕ := if w = 9 + k then mp a else mp w
            refine ⟨ds, mp', hds_ws, hds_len.trans hfilter_eq.symm, ?_⟩
            intro w hw hnc
            by_cases heq : w = 9 + k
            · subst heq
              refine ⟨by simpa [mp'] using hmpa_lt, fun y => ?_⟩
              simp only [mp', ite_true]
              exact (hmpa_ev y).trans (hceq y).symm
            · simp only [mp', if_neg heq]
              exact hmp w (by omega) hnc
        · let gNew : Gate := ⟨(gs.get j).op, (gs.get j).inputs.map mp⟩
          let ds' : List Gate := ds ++ [gNew]
          let mp' (w : ℕ) : ℕ := if w = 9 + k then 8 + ds.length else mp w
          have hno_in_const : ∀ u ∈ (gs.get j).inputs,
              ¬ ∃ b : Bool, ∀ y : Fin 8 → Bool, (W gs (List.ofFn (ext y))).getD u false = b :=
            fun u hu hcu => hS (Or.inr ⟨u, hu, hcu⟩)
          have hds'_ws : WellStructured 8 ⟨ds', 0⟩ := by
            intro idx
            by_cases hlt : idx.val < ds.length
            · have hget : ds'.get idx = ds.get ⟨idx.val, hlt⟩ := by
                simp only [ds', List.get_eq_getElem, List.getElem_append_left hlt]
              rw [hget]; exact hds_ws ⟨idx.val, hlt⟩
            · have heq : idx.val = ds.length := by
                have := idx.isLt; simp [ds'] at this; omega
              have hget : ds'.get idx = gNew := by
                simp only [ds', List.get_eq_getElem, heq, List.getElem_append_right le_rfl,
                  Nat.sub_self, List.getElem_singleton]
              rw [hget, heq]
              rcases hws j with ⟨hop, a, ha, hins⟩ | ⟨hop, a, b, hab, hb, hins⟩
              · rw [hjv] at ha
                left
                refine ⟨hop, mp a, (hmp a ha (hno_in_const a (by rw [hins]; simp))).1, ?_⟩
                dsimp only [gNew]; rw [hins]; rfl
              · rw [hjv] at hb
                right
                refine ⟨hop, mp a, mp b,
                  (hmp a (by omega) (hno_in_const a (by rw [hins]; simp))).1,
                  (hmp b hb (hno_in_const b (by rw [hins]; simp))).1, ?_⟩
                dsimp only [gNew]; rw [hins]; rfl
          have hds'_len : ds'.length = (Finset.univ.filter (fun i : Fin gs.length => i.val < k + 1 ∧ 2 ≤ i.val ∧
              ¬ (2 ≤ i.val ∧ ((∃ b, ∀ y, (W gs (List.ofFn (ext y))).getD (9 + i.val) false = b) ∨
                ∃ a ∈ (gs.get i).inputs, ∃ b, ∀ y, (W gs (List.ofFn (ext y))).getD a false = b)))).card := by
            have hset : Finset.univ.filter (fun i : Fin gs.length => i.val < k + 1 ∧ 2 ≤ i.val ∧
                ¬ (2 ≤ i.val ∧ ((∃ b, ∀ y, (W gs (List.ofFn (ext y))).getD (9 + i.val) false = b) ∨
                  ∃ a ∈ (gs.get i).inputs, ∃ b, ∀ y, (W gs (List.ofFn (ext y))).getD a false = b))) =
              insert j (Finset.univ.filter (fun i : Fin gs.length => i.val < k ∧ 2 ≤ i.val ∧
                ¬ (2 ≤ i.val ∧ ((∃ b, ∀ y, (W gs (List.ofFn (ext y))).getD (9 + i.val) false = b) ∨
                  ∃ a ∈ (gs.get i).inputs, ∃ b, ∀ y, (W gs (List.ofFn (ext y))).getD a false = b)))) := by
              ext i
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
              constructor
              · rintro ⟨hlt, h2i, hni⟩
                by_cases heq : i.val = k
                · exact Or.inl (Fin.ext heq)
                · exact Or.inr ⟨by omega, h2i, hni⟩
              · rintro (rfl | ⟨hlt, h2i, hni⟩)
                · exact ⟨by simp [j], hk2', fun h => hS h.2⟩
                · exact ⟨by omega, h2i, hni⟩
            have hjnot : j ∉ Finset.univ.filter (fun i : Fin gs.length => i.val < k ∧ 2 ≤ i.val ∧
                ¬ (2 ≤ i.val ∧ ((∃ b, ∀ y, (W gs (List.ofFn (ext y))).getD (9 + i.val) false = b) ∨
                  ∃ a ∈ (gs.get i).inputs, ∃ b, ∀ y, (W gs (List.ofFn (ext y))).getD a false = b))) := by
              simp [j]
            rw [hset, Finset.card_insert_of_notMem hjnot, ← hds_len]
            simp [ds']
          refine ⟨ds', mp', hds'_ws, hds'_len, ?_⟩
          intro w hw hnc
          by_cases heq : w = 9 + k
          · subst heq
            refine ⟨by simp [mp', ds'], fun y => ?_⟩
            simp only [mp', ite_true, ds']
            rw [W_snoc]
            have hlen : (W ds (List.ofFn y)).length = 8 + ds.length := by
              rw [W_len, List.length_ofFn]
            have hstep : (step (W ds (List.ofFn y)) gNew).getD (8 + ds.length) false =
                gNew.op.eval (gNew.inputs.map fun i => (W ds (List.ofFn y)).getD i false) := by
              unfold step; rw [← hlen, getD_append_len]
            rw [hstep, hgate_eval y]
            simp only [gNew, List.map_map]
            congr 1
            apply List.map_congr_left
            intro a ha
            have halt : a < 9 + k := by
              rcases hws j with ⟨_, u, hu, hins⟩ | ⟨_, u, v, hu, hv, hins⟩
              · rw [hjv] at hu; rw [hins, List.mem_singleton] at ha; omega
              · rw [hjv] at hv; rw [hins, List.mem_cons, List.mem_singleton] at ha
                rcases ha with rfl | rfl <;> omega
            exact (hmp a halt (hno_in_const a ha)).2 y
          · have hlt : w < 9 + k := by omega
            obtain ⟨hltm, hevm⟩ := hmp w hlt hnc
            refine ⟨by simp [mp', if_neg heq, ds']; omega, fun y => ?_⟩
            simp only [mp', if_neg heq, ds']
            rw [W_snoc]
            have hlen : (W ds (List.ofFn y)).length = 8 + ds.length := by
              rw [W_len, List.length_ofFn]
            have hstep : (step (W ds (List.ofFn y)) gNew).getD (mp w) false =
                (W ds (List.ofFn y)).getD (mp w) false := by
              unfold step; exact getD_append_lt _ _ _ (by omega)
            rw [hstep]
            exact hevm y
  obtain ⟨ds, mp, h1', h2', h3'⟩ := hprefix gs.length le_rfl
  refine ⟨ds, mp, h1', ?_, h3'⟩
  rw [h2']
  congr 1; ext j
  simp [j.isLt]

end PEqualNP.Outside.L_meta_27741

theorem PEqualNP.Outside.L_meta_27741 : (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))) ∧
    C.output + 1 = 9 + C.size ∧
    (∀ j : Fin C.gates.length,
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
    (∀ j : Fin C.gates.length,
      (∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
      ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
    (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩)) := by
  classical
  open PEqualNP.Outside.L_meta_27741 in
  rintro ⟨C, _, hsz, heval, hout, hnf, _, hfanout, hhead0, hhead1⟩
  have hlen_ge2 : 2 ≤ C.gates.length := by
    cases h : C.gates with
    | nil => simp [h] at hhead0
    | cons a l =>
      cases l with
      | nil => simp [h] at hhead1
      | cons b l' => simp
  have h0read : ∃ j : Fin C.gates.length, 2 ≤ j.val ∧ 0 ∈ (C.gates.get j).inputs := by
    by_contra hnone
    have hnone' : ∀ j : Fin C.gates.length, 2 ≤ j.val → 0 ∉ (C.gates.get j).inputs :=
      fun j hj hmem => hnone ⟨j, hj, hmem⟩
    let xT : Fin 9 → Bool := ![true, true, true, false, true, false, false, false, true]
    let xF : Fin 9 → Bool := ![false, true, true, false, true, false, false, false, true]
    have hsame : ∀ w < 9 + C.gates.length, w ≠ 0 →
        wval C xT w = wval C xF w := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hw hne0
        by_cases h9 : w < 9
        · rw [wval_input C xT w h9, wval_input C xF w h9]
          interval_cases w <;> simp_all [xT, xF]
        · have hjlt : w - 9 < C.gates.length := by omega
          have hw' : w = 9 + (w - 9) := by omega
          let j : Fin C.gates.length := ⟨w - 9, hjlt⟩
          have hjv : j.val = w - 9 := rfl
          have hback : ∀ a ∈ (C.gates[w - 9]).inputs, a < 9 + (w - 9) := by
            intro a ha
            rcases hnf j with ⟨_, u, hu, hins⟩ | ⟨_, u, v, hu, hv, hins⟩
            · simp only [List.get_eq_getElem, hjv] at hins hu; rw [hins, List.mem_singleton] at ha; omega
            · simp only [List.get_eq_getElem, hjv] at hins hu hv; rw [hins, List.mem_cons, List.mem_singleton] at ha
              rcases ha with rfl | rfl <;> omega
          by_cases h2 : w - 9 < 2
          · rw [hw', wval_gate C xT (w - 9) hjlt hback, wval_gate C xF (w - 9) hjlt hback]
            have h1T : wval C xT 1 = true := by rw [wval_input C xT 1 (by omega)]; rfl
            have h1F : wval C xF 1 = true := by rw [wval_input C xF 1 (by omega)]; rfl
            have h2T : wval C xT 2 = true := by rw [wval_input C xT 2 (by omega)]; rfl
            have h2F : wval C xF 2 = true := by rw [wval_input C xF 2 (by omega)]; rfl
            have hw01 : w - 9 = 0 ∨ w - 9 = 1 := by omega
            rcases hw01 with hw0 | hw1
            · simp only [hw0]
              rw [getElem_zero_of_head? hhead0 (by omega)]
              simp [PEqualNP.CircuitLowerBounds.GateOp.eval, h1T, h1F]
            · simp only [hw1]
              rw [getElem_one_of_tail_head? hhead1 (by omega)]
              simp [PEqualNP.CircuitLowerBounds.GateOp.eval, h2T, h2F]
          · rw [hw', wval_gate C xT (w - 9) hjlt hback, wval_gate C xF (w - 9) hjlt hback]
            congr 1
            apply List.map_congr_left
            intro a ha
            have hne : a ≠ 0 := fun h => hnone' j (by omega) (by simpa [j, h] using ha)
            have halt : a < w := by have := hback a ha; omega
            exact ih a halt (by omega) hne
    have hout_eq : wval C xT C.output = wval C xF C.output :=
      hsame C.output (by change C.output + 1 = 9 + C.gates.length at hout; omega)
        (by change C.output + 1 = 9 + C.gates.length at hout; omega)
    have hT := heval xT
    have hF := heval xF
    change wval C xT C.output = _ at hT
    change wval C xF C.output = _ at hF
    rw [hout_eq, hF] at hT
    revert hT; decide
  have hlen_ge3 : 3 ≤ C.gates.length := by
    obtain ⟨j, hj2, _⟩ := h0read
    have := j.isLt; omega
  let wC (y : Fin 8 → Bool) (w : ℕ) : Bool := (W C.gates (List.ofFn (ext y))).getD w false
  let isConst (w : ℕ) : Prop := ∃ b : Bool, ∀ y : Fin 8 → Bool, wC y w = b
  let CK : Finset (Fin C.gates.length) :=
    Finset.univ.filter (fun j => 2 ≤ j.val ∧ isConst (9 + j.val))
  let S : Finset (Fin C.gates.length) :=
    Finset.univ.filter (fun j => 2 ≤ j.val ∧ (isConst (9 + j.val) ∨ ∃ a ∈ (C.gates.get j).inputs, isConst a))
  have hconst0 : isConst 0 := ⟨true, fun y => by
    show (W C.gates (List.ofFn (ext y))).getD 0 false = true
    rw [W_prefix C.gates (List.ofFn (ext y)) 0 (by simp)]
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]; rfl⟩
  have hconst9 : isConst 9 := ⟨true, fun y => by
    show (W C.gates (List.ofFn (ext y))).getD 9 false = true
    have h1 := wval_gate C (ext y) 0 (by omega) (by
      intro a ha
      rcases hnf ⟨0, by omega⟩ with ⟨_, u, hu, hins⟩ | ⟨_, u, v, hu, hv, hins⟩
      · simp only [List.get_eq_getElem] at hins; dsimp only at hu; rw [hins, List.mem_singleton] at ha; omega
      · simp only [List.get_eq_getElem] at hins; dsimp only at hu hv; rw [hins, List.mem_cons, List.mem_singleton] at ha
        rcases ha with rfl | rfl <;> omega)
    change (W C.gates (List.ofFn (ext y))).getD 9 false = _ at h1
    rw [h1, getElem_zero_of_head? hhead0 (by omega)]
    have h0v : wval C (ext y) 0 = true := by rw [wval_input C (ext y) 0 (by omega)]; rfl
    simp [PEqualNP.CircuitLowerBounds.GateOp.eval, h0v]⟩
  have hconst10 : isConst 10 := ⟨true, fun y => by
    show (W C.gates (List.ofFn (ext y))).getD 10 false = true
    have h1 := wval_gate C (ext y) 1 (by omega) (by
      intro a ha
      rcases hnf ⟨1, by omega⟩ with ⟨_, u, hu, hins⟩ | ⟨_, u, v, hu, hv, hins⟩
      · simp only [List.get_eq_getElem] at hins; dsimp only at hu; rw [hins, List.mem_singleton] at ha; omega
      · simp only [List.get_eq_getElem] at hins; dsimp only at hu hv; rw [hins, List.mem_cons, List.mem_singleton] at ha
        rcases ha with rfl | rfl <;> omega)
    change (W C.gates (List.ofFn (ext y))).getD 10 false = _ at h1
    rw [h1, getElem_one_of_tail_head? hhead1 (by omega)]
    have h0v : wval C (ext y) 0 = true := by rw [wval_input C (ext y) 0 (by omega)]; rfl
    simp [PEqualNP.CircuitLowerBounds.GateOp.eval, h0v]⟩
  have hout_nc : ¬ isConst C.output := by
    rintro ⟨b, hb⟩
    have hF := hb (fun _ => false)
    have hT := hb (fun _ => true)
    have eF : wC (fun _ => false) C.output = f1 (fun _ => false) := heval (ext (fun _ => false))
    have eT : wC (fun _ => true) C.output = f1 (fun _ => true) := heval (ext (fun _ => true))
    rw [eF] at hF; rw [eT] at hT
    have : f1 (fun _ => false) = f1 (fun _ => true) := hF.trans hT.symm
    revert this; decide
  let Kact : Finset ℕ := ({0, 9, 10} : Finset ℕ) ∪ CK.image (fun j : Fin C.gates.length => 9 + j.val)
  have hKact_card : Kact.card = 3 + CK.card := by
    have hdisj : Disjoint ({0, 9, 10} : Finset ℕ) (CK.image (fun j : Fin C.gates.length => 9 + j.val)) := by
      rw [Finset.disjoint_left]
      intro w hw1 hw2
      rw [Finset.mem_image] at hw2
      rcases hw2 with ⟨j, hjCK, rfl⟩
      have hj2 : 2 ≤ j.val := (Finset.mem_filter.mp hjCK).2.1
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw1
      omega
    have h3 : ({0, 9, 10} : Finset ℕ).card = 3 := by decide
    rw [Finset.card_union_of_disjoint hdisj,
        Finset.card_image_of_injective _ (fun a b h => Fin.ext (by omega)), h3]
  have hKact_const : ∀ w ∈ Kact, isConst w := by
    intro w hw
    simp only [Kact, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image] at hw
    rcases hw with (rfl | rfl | rfl) | ⟨j, hj, rfl⟩
    · exact hconst0
    · exact hconst9
    · exact hconst10
    · exact (Finset.mem_filter.mp hj).2.2
  have hKact_sub : Kact ⊆ S.biUnion (fun j => (C.gates.get j).inputs.toFinset ∩ Kact) := by
    intro w hw
    rw [Finset.mem_biUnion]
    simp only [Kact, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image] at hw
    rcases hw with (rfl | rfl | rfl) | ⟨j, hj, rfl⟩
    · obtain ⟨k, hk2, hmk⟩ := h0read
      refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk2, Or.inr ⟨0, hmk, hconst0⟩⟩,
        Finset.mem_inter.mpr ⟨List.mem_toFinset.mpr hmk, by simp [Kact]⟩⟩
    · obtain ⟨k, hk0, hmk⟩ := hfanout ⟨0, by omega⟩ (by dsimp only; omega)
      dsimp only at hk0 hmk
      have hk2 : 2 ≤ k.val := by
        by_contra hlt
        have hk1 : k.val = 1 := by omega
        have hg1 : C.gates.get k = ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩ := by
          simp only [List.get_eq_getElem, hk1]
          exact getElem_one_of_tail_head? hhead1 (by omega)
        rw [hg1] at hmk; simp at hmk
      refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk2, Or.inr ⟨9, hmk, hconst9⟩⟩,
        Finset.mem_inter.mpr ⟨List.mem_toFinset.mpr hmk, by simp [Kact]⟩⟩
    · obtain ⟨k, hk1, hmk⟩ := hfanout ⟨1, by omega⟩ (by dsimp only; omega)
      dsimp only at hk1 hmk
      refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega, Or.inr ⟨10, hmk, hconst10⟩⟩,
        Finset.mem_inter.mpr ⟨List.mem_toFinset.mpr hmk, by simp [Kact]⟩⟩
    · have hjlt : j.val + 1 < C.gates.length := by
        by_contra hge
        have heq : 9 + j.val = C.output := by
          have := j.isLt; change C.output + 1 = 9 + C.gates.length at hout; omega
        exact hout_nc (heq ▸ (Finset.mem_filter.mp hj).2.2)
      obtain ⟨k, hjk, hmk⟩ := hfanout j hjlt
      have hj2 : 2 ≤ j.val := (Finset.mem_filter.mp hj).2.1
      refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega, Or.inr ⟨9 + j.val, hmk, (Finset.mem_filter.mp hj).2.2⟩⟩,
        Finset.mem_inter.mpr ⟨List.mem_toFinset.mpr hmk, Finset.mem_union_right _ (Finset.mem_image_of_mem _ hj)⟩⟩
  have hCK_sub_S : CK ⊆ S := by
    intro j hj
    simp only [CK, S, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact ⟨hj.1, Or.inl hj.2⟩
  have hslot_bound : ∀ j ∈ S, ((C.gates.get j).inputs.toFinset ∩ Kact).card ≤ if j ∈ CK then 2 else 1 := by
    intro j hjS
    split_ifs with hjCK
    · calc ((C.gates.get j).inputs.toFinset ∩ Kact).card
          ≤ (C.gates.get j).inputs.toFinset.card := Finset.card_le_card Finset.inter_subset_left
        _ ≤ (C.gates.get j).inputs.length := List.toFinset_card_le _
        _ ≤ 2 := by
          rcases hnf j with ⟨_, _, _, hins⟩ | ⟨_, _, _, _, _, hins⟩
          · rw [hins]; simp
          · rw [hins]; simp
    · have hjnc : ¬ isConst (9 + j.val) := fun h =>
        hjCK (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hjS).2.1, h⟩)
      have hgate_ev : ∀ y : Fin 8 → Bool,
          wC y (9 + j.val) = (C.gates.get j).op.eval ((C.gates.get j).inputs.map fun a => wC y a) := by
        intro y
        have h1 := wval_gate C (ext y) j.val j.isLt (by
          intro a ha
          rcases hnf j with ⟨_, u, hu, hins⟩ | ⟨_, u, v, hu, hv, hins⟩
          · simp only [List.get_eq_getElem] at hins; rw [hins, List.mem_singleton] at ha; omega
          · simp only [List.get_eq_getElem] at hins; rw [hins, List.mem_cons, List.mem_singleton] at ha
            rcases ha with rfl | rfl <;> omega)
        simpa [wC, wval, wires_eq_W] using h1
      rcases hnf j with ⟨hop, a, _, hins⟩ | ⟨hop, a, b, _, _, hins⟩
      · by_cases haK : a ∈ Kact
        · obtain ⟨ca, hca⟩ := hKact_const a haK
          exfalso; apply hjnc; refine ⟨!ca, fun y => ?_⟩
          rw [hgate_ev y, hop, hins]; simp [PEqualNP.CircuitLowerBounds.GateOp.eval, hca y]
        · rw [hins]
          have hempty : ([a] : List ℕ).toFinset ∩ Kact = ∅ := by
            ext x; simp; rintro rfl; exact haK
          rw [hempty]; simp
      · by_cases haK : a ∈ Kact
        · by_cases hbK : b ∈ Kact
          · obtain ⟨ca, hca⟩ := hKact_const a haK
            obtain ⟨cb, hcb⟩ := hKact_const b hbK
            exfalso; apply hjnc; refine ⟨(C.gates.get j).op.eval [ca, cb], fun y => ?_⟩
            rw [hgate_ev y, hins]; simp [hca y, hcb y]
          · rw [hins]
            have hsub1 : ([a, b] : List ℕ).toFinset ∩ Kact ⊆ {a} := by
              intro x hx; simp at hx
              rcases hx.1 with rfl | rfl
              · simp
              · exact (hbK hx.2).elim
            exact (Finset.card_le_card hsub1).trans (by simp)
        · rw [hins]
          have hsub1 : ([a, b] : List ℕ).toFinset ∩ Kact ⊆ {b} := by
            intro x hx; simp at hx
            rcases hx.1 with rfl | rfl
            · exact (haK hx.2).elim
            · simp
          exact (Finset.card_le_card hsub1).trans (by simp)
  have hS_ge3 : 3 ≤ S.card := by
    have h1 : Kact.card ≤ S.sum (fun j => ((C.gates.get j).inputs.toFinset ∩ Kact).card) :=
      (Finset.card_le_card hKact_sub).trans Finset.card_biUnion_le
    have h2 : S.sum (fun j => ((C.gates.get j).inputs.toFinset ∩ Kact).card) ≤
        S.sum (fun j => if j ∈ CK then 2 else 1) := Finset.sum_le_sum hslot_bound
    have h3 : S.sum (fun j => if j ∈ CK then 2 else 1) = S.card + CK.card := by
      have hsplit : ∀ j : Fin C.gates.length, (if j ∈ CK then 2 else 1) = 1 + (if j ∈ CK then 1 else 0) := by
        intro j; split_ifs <;> rfl
      simp_rw [hsplit, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one,
        Finset.sum_boole, Nat.cast_id]
      have : S.filter (fun j => j ∈ CK) = CK := by
        ext j; simp only [Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨hCK_sub_S h, h⟩⟩
      rw [this]
    omega
  obtain ⟨ds, mp, hds_ws, hds_len, hmp⟩ := reduce_prefix C.gates hnf hhead0 hhead1
  have hkeep_card : (Finset.univ.filter (fun j : Fin C.gates.length => 2 ≤ j.val ∧
      ¬ (2 ≤ j.val ∧ (isConst (9 + j.val) ∨ ∃ a ∈ (C.gates.get j).inputs, isConst a)))).card ≤ 7 := by
    let G2 : Finset (Fin C.gates.length) := Finset.univ.filter (fun j => 2 ≤ j.val)
    have hG2_card : G2.card = C.gates.length - 2 := by
      have hcomp : G2 = Finset.univ \ ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin C.gates.length)) := by
        ext j; simp only [G2, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
          Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro h2 h; rcases h with rfl | rfl <;> simp at h2
        · intro h; by_contra hlt
          have hj01 : j.val = 0 ∨ j.val = 1 := by omega
          rcases hj01 with hv | hv
          · exact h (Or.inl (Fin.ext hv))
          · exact h (Or.inr (Fin.ext hv))
      rw [hcomp, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
      have hne01 : (⟨0, by omega⟩ : Fin C.gates.length) ≠ ⟨1, by omega⟩ := by simp
      rw [Finset.card_pair hne01]
    have hS_sub_G2 : S ⊆ G2 := fun j hj => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2.1⟩
    have hdiff : Finset.univ.filter (fun j : Fin C.gates.length => 2 ≤ j.val ∧
        ¬ (2 ≤ j.val ∧ (isConst (9 + j.val) ∨ ∃ a ∈ (C.gates.get j).inputs, isConst a))) = G2 \ S := by
      ext j; simp only [G2, S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
    rw [hdiff, Finset.card_sdiff_of_subset hS_sub_G2, hG2_card]
    change C.gates.length ≤ 12 at hsz
    omega
  have hds_le7 : ds.length ≤ 7 := by
    have heq_len : ds.length = (Finset.univ.filter (fun j : Fin C.gates.length => 2 ≤ j.val ∧
        ¬ (2 ≤ j.val ∧ (isConst (9 + j.val) ∨ ∃ a ∈ (C.gates.get j).inputs, isConst a)))).card := hds_len
    omega
  have hout_ltC : C.output < 9 + C.gates.length := by
    change C.output + 1 = 9 + C.gates.length at hout; omega
  obtain ⟨hout_ltD, hout_ev⟩ := hmp C.output hout_ltC hout_nc
  let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨ds, mp C.output⟩
  exact no_circuit_f1_le7 D hds_ws hds_le7 hout_ltD (fun y => by
    have h1 := hout_ev y
    have h2 := heval (ext y)
    exact h1.trans h2)

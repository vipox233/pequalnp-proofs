import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29952_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

private def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih]
    simp [stepWire]
    omega

private lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) {i : ℕ} (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih _ hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private lemma circuit_wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.size :=
  foldl_stepWire_length C.gates x

private lemma circuit_wires_getD_input (C : Circuit) (x : List Bool) {i : ℕ} (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false :=
  foldl_stepWire_getD_lt C.gates x hi

private lemma circuit_wires_getD_ge (C : Circuit) (x : List Bool) {i : ℕ}
    (hi : x.length + C.size ≤ i) :
    (C.wires x).getD i false = false := by
  have hlen : (C.wires x).length ≤ i := by rw [circuit_wires_length]; exact hi
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlen]

private lemma circuit_wires_getD_gate (C : Circuit) (x : List Bool) {j : ℕ}
    (hj : j < C.gates.length) :
    (C.wires x).getD (x.length + j) false =
      C.gates[j].op.eval
        (C.gates[j].inputs.map fun i =>
          if i < x.length + j then (C.wires x).getD i false else false) := by
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  set w1 := (C.gates.take j).foldl stepWire x
  have hw1_len : w1.length = x.length + j := by
    rw [foldl_stepWire_length, List.length_take_of_le (Nat.le_of_lt hj)]
  have hwires : C.wires x = (C.gates.drop (j + 1)).foldl stepWire (stepWire w1 C.gates[j]) := by
    unfold Circuit.wires
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
    rfl
  have hget_w1 : ∀ i, i < x.length + j → (C.wires x).getD i false = w1.getD i false := by
    intro i hi
    rw [hwires]
    have hlt1 : i < (stepWire w1 C.gates[j]).length := by simp [stepWire, hw1_len]; omega
    rw [foldl_stepWire_getD_lt _ _ hlt1]
    have hlt0 : i < w1.length := by omega
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt0]
  have hget_j : (C.wires x).getD (x.length + j) false =
      C.gates[j].op.eval (C.gates[j].inputs.map fun i => w1.getD i false) := by
    rw [hwires]
    have hlt : x.length + j < (stepWire w1 C.gates[j]).length := by simp [stepWire, hw1_len]
    rw [foldl_stepWire_getD_lt _ _ hlt]
    have hle : w1.length ≤ x.length + j := le_of_eq hw1_len
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_right hle, hw1_len]
  rw [hget_j]
  congr 1
  apply List.map_congr_left
  intro i _
  by_cases hi : i < x.length + j
  · simp only [hi, ↓reduceIte, hget_w1 i hi]
  · have hge : w1.length ≤ i := by omega
    simp [hi, List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]

private def isNotOp : GateOp → Bool
  | .not => true
  | _ => false

private def isNotGate (C : Circuit) (N g : ℕ) : Bool :=
  if h : g - N < C.gates.length then isNotOp C.gates[g - N].op else false

private def effInputs (N j : ℕ) (g : Gate) : List ℕ :=
  ((match g.op with
    | .not => g.inputs.take 1
    | _ => g.inputs).filter (· < N + j)).dedup

private lemma effInputs_nodup (N j : ℕ) (g : Gate) : (effInputs N j g).Nodup :=
  List.nodup_dedup _

private lemma effInputs_lt {N j : ℕ} {g : Gate} {u : ℕ} (hu : u ∈ effInputs N j g) :
    u < N + j := by
  simp [effInputs] at hu
  exact hu.2

private lemma effInputs_card_le (N j : ℕ) (g : Gate) (hlen : g.inputs.length ≤ 2) :
    (effInputs N j g).toFinset.card ≤ if isNotOp g.op then 1 else 2 := by
  have hsub : (effInputs N j g).toFinset.card ≤ (effInputs N j g).length :=
    List.toFinset_card_le _
  have h1 : (effInputs N j g).length ≤
      ((match g.op with | .not => g.inputs.take 1 | _ => g.inputs).filter (· < N + j)).length :=
    List.Sublist.length_le (List.dedup_sublist _)
  have h2 := List.length_filter_le (· < N + j)
    (match g.op with | .not => g.inputs.take 1 | _ => g.inputs)
  cases hop : g.op <;> simp only [hop, isNotOp, Bool.false_eq_true, ↓reduceIte] at h1 h2 ⊢
  · omega
  · omega
  · have htake : (g.inputs.take 1).length ≤ 1 := by simp
    omega
  · omega
  · omega

private lemma gate_eval_congr_effInputs {N j : ℕ} {g : Gate}
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    {v1 v2 : ℕ → Bool}
    (hagree : ∀ u ∈ effInputs N j g, v1 u = v2 u) :
    g.op.eval (g.inputs.map fun i => if i < N + j then v1 i else false) =
    g.op.eval (g.inputs.map fun i => if i < N + j then v2 i else false) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with hop | hop | hop
  · rw [hop]; simp only [GateOp.eval]
    congr 1
    apply List.map_congr_left
    intro i hi
    by_cases hlt : i < N + j
    · simp only [hlt, ↓reduceIte]
      exact hagree i (by simp [effInputs, hop, hi, hlt])
    · simp [hlt]
  · rw [hop]; simp only [GateOp.eval]
    congr 1
    apply List.map_congr_left
    intro i hi
    by_cases hlt : i < N + j
    · simp only [hlt, ↓reduceIte]
      exact hagree i (by simp [effInputs, hop, hi, hlt])
    · simp [hlt]
  · rw [hop]
    cases hgi : g.inputs with
    | nil => simp [GateOp.eval]
    | cons a tl =>
      simp only [GateOp.eval, List.map_cons, List.headD_cons]
      by_cases hlt : a < N + j
      · simp only [hlt, ↓reduceIte]
        have ha : a ∈ effInputs N j g := by simp [effInputs, hop, hgi, hlt]
        rw [hagree a ha]
      · simp [hlt]

private lemma gate_eval_and_two {N j : ℕ} {g : Gate} (hop : g.op = .and)
    (hlen : g.inputs.length ≤ 2) {a b : ℕ}
    (hcard : (effInputs N j g).toFinset.card = 2)
    (heff : effInputs N j g = [a, b])
    (v : ℕ → Bool) :
    g.op.eval (g.inputs.map fun i => if i < N + j then v i else false) = (v a && v b) := by
  have ha_lt : a < N + j := effInputs_lt (by rw [heff]; simp)
  have hb_lt : b < N + j := effInputs_lt (by rw [heff]; simp)
  have ha_in : a ∈ g.inputs := by
    have : a ∈ effInputs N j g := by rw [heff]; simp
    exact (by simpa [effInputs, hop] using this : a ∈ g.inputs ∧ a < N + j).1
  have hb_in : b ∈ g.inputs := by
    have : b ∈ effInputs N j g := by rw [heff]; simp
    exact (by simpa [effInputs, hop] using this : b ∈ g.inputs ∧ b < N + j).1
  have hne : a ≠ b := by
    have hnd := effInputs_nodup N j g
    rw [heff] at hnd
    simpa using hnd
  rcases hgi : g.inputs with _ | ⟨x, _ | ⟨y, _ | _⟩⟩
  · simp [hgi] at ha_in
  · simp [hgi] at ha_in hb_in; omega
  · rw [hgi] at ha_in hb_in
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha_in hb_in
    rcases ha_in with rfl | rfl <;> rcases hb_in with rfl | rfl
    · exact absurd rfl hne
    · simp [hop, GateOp.eval, ha_lt, hb_lt]
    · simp [hop, GateOp.eval, ha_lt, hb_lt, Bool.and_comm]
    · exact absurd rfl hne
  · simp [hgi] at hlen

private lemma gate_eval_or_two {N j : ℕ} {g : Gate} (hop : g.op = .or)
    (hlen : g.inputs.length ≤ 2) {a b : ℕ}
    (hcard : (effInputs N j g).toFinset.card = 2)
    (heff : effInputs N j g = [a, b])
    (v : ℕ → Bool) :
    g.op.eval (g.inputs.map fun i => if i < N + j then v i else false) = (v a || v b) := by
  have ha_lt : a < N + j := effInputs_lt (by rw [heff]; simp)
  have hb_lt : b < N + j := effInputs_lt (by rw [heff]; simp)
  have ha_in : a ∈ g.inputs := by
    have : a ∈ effInputs N j g := by rw [heff]; simp
    exact (by simpa [effInputs, hop] using this : a ∈ g.inputs ∧ a < N + j).1
  have hb_in : b ∈ g.inputs := by
    have : b ∈ effInputs N j g := by rw [heff]; simp
    exact (by simpa [effInputs, hop] using this : b ∈ g.inputs ∧ b < N + j).1
  have hne : a ≠ b := by
    have hnd := effInputs_nodup N j g
    rw [heff] at hnd
    simpa using hnd
  rcases hgi : g.inputs with _ | ⟨x, _ | ⟨y, _ | _⟩⟩
  · simp [hgi] at ha_in
  · simp [hgi] at ha_in hb_in; omega
  · rw [hgi] at ha_in hb_in
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha_in hb_in
    rcases ha_in with rfl | rfl <;> rcases hb_in with rfl | rfl
    · exact absurd rfl hne
    · simp [hop, GateOp.eval, ha_lt, hb_lt]
    · simp [hop, GateOp.eval, ha_lt, hb_lt, Bool.or_comm]
    · exact absurd rfl hne
  · simp [hgi] at hlen

private lemma gate_eval_not_one {N j : ℕ} {g : Gate} (hop : g.op = .not)
    {a : ℕ} (heff : effInputs N j g = [a]) (v : ℕ → Bool) :
    g.op.eval (g.inputs.map fun i => if i < N + j then v i else false) = !(v a) := by
  have ha_lt : a < N + j := effInputs_lt (by rw [heff]; simp)
  have ha_in : a ∈ g.inputs.take 1 := by
    have : a ∈ effInputs N j g := by rw [heff]; simp
    exact (by simpa [effInputs, hop] using this : a ∈ g.inputs.take 1 ∧ a < N + j).1
  cases hgi : g.inputs with
  | nil => simp [hgi] at ha_in
  | cons x tl =>
    rw [hgi] at ha_in
    simp only [List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil,
      or_false] at ha_in
    subst ha_in
    simp [hop, GateOp.eval, ha_lt]

private def refsList (C : Circuit) (N w : ℕ) : List ℕ :=
  if h : N ≤ w ∧ w - N < C.gates.length then
    effInputs N (w - N) C.gates[w - N]
  else []

private def refsOf (C : Circuit) (N w : ℕ) : Finset ℕ :=
  (refsList C N w).toFinset

private lemma refsOf_lt {C : Circuit} {N w u : ℕ} (hu : u ∈ refsOf C N w) : u < w := by
  unfold refsOf refsList at hu
  split_ifs at hu with h
  · rw [List.mem_toFinset] at hu
    have := effInputs_lt hu
    omega
  · simp at hu

private def reach (C : Circuit) (N : ℕ) (w : ℕ) : Finset ℕ :=
  if h : N ≤ w ∧ w - N < C.gates.length then
    insert w ((refsList C N w).attach.foldr (fun ⟨u, hu⟩ acc =>
      have : u < w := refsOf_lt (C := C) (N := N) (List.mem_toFinset.mpr hu)
      reach C N u ∪ acc) ∅)
  else if w < N then {w} else ∅
termination_by w

private lemma mem_reach_self {C : Circuit} {N w : ℕ} (hw : w < N + C.gates.length) :
    w ∈ reach C N w := by
  rw [reach]
  by_cases h1 : N ≤ w
  · have h2 : w - N < C.gates.length := by omega
    simp [h1, h2]
  · have hlt : w < N := by omega
    simp [h1, hlt]

private lemma mem_reach_iff_gate {C : Circuit} {N w u : ℕ}
    (h1 : N ≤ w) (h2 : w - N < C.gates.length) :
    u ∈ reach C N w ↔ u = w ∨ ∃ v ∈ refsOf C N w, u ∈ reach C N v := by
  rw [reach]
  simp only [h1, h2, and_self, ↓reduceDIte, Finset.mem_insert]
  have hfold : ∀ (l : List ℕ) (hl : ∀ x ∈ l, x < w),
      u ∈ l.attach.foldr (fun ⟨x, hx⟩ acc => reach C N x ∪ acc) ∅ ↔
      ∃ x ∈ l, u ∈ reach C N x := by
    intro l hl
    induction l with
    | nil => simp
    | cons a tl ih =>
      simp only [List.attach_cons, List.foldr_cons, Finset.mem_union, List.mem_cons]
      have htl : ∀ x ∈ tl, x < w := fun x hx => hl x (List.mem_cons_of_mem a hx)
      have hmap :
          (tl.attach.map (fun x => ⟨x.1, List.mem_cons_of_mem a x.2⟩)).foldr
            (fun (x : {y // y ∈ a :: tl}) acc => reach C N x.1 ∪ acc) ∅ =
          tl.attach.foldr (fun (x : {y // y ∈ tl}) acc => reach C N x.1 ∪ acc) ∅ := by
        rw [List.foldr_map]
      rw [hmap, ih htl]
      constructor
      · rintro (h | ⟨x, hx, hu⟩)
        · exact ⟨a, Or.inl rfl, h⟩
        · exact ⟨x, Or.inr hx, hu⟩
      · rintro ⟨x, rfl | hx, hu⟩
        · exact Or.inl hu
        · exact Or.inr ⟨x, hx, hu⟩
  rw [hfold (refsList C N w) (fun x hx => refsOf_lt (List.mem_toFinset.mpr hx))]
  simp [refsOf]

private lemma mem_reach_le {C : Circuit} {N w u : ℕ} (hu : u ∈ reach C N w) : u ≤ w := by
  induction w using Nat.strong_induction_on generalizing u with
  | _ w ih =>
    by_cases h1 : N ≤ w ∧ w - N < C.gates.length
    · rw [mem_reach_iff_gate h1.1 h1.2] at hu
      rcases hu with rfl | ⟨v, hv, huv⟩
      · exact le_rfl
      · have hvw : v < w := refsOf_lt hv
        exact le_trans (ih v hvw huv) (Nat.le_of_lt hvw)
    · rw [reach] at hu
      simp only [h1, ↓reduceDIte] at hu
      split_ifs at hu
      · simp at hu; omega
      · simp at hu

private lemma reach_subset_lt {C : Circuit} {N w u : ℕ}
    (hw : w < N + C.gates.length) (hu : u ∈ reach C N w) : u < N + C.gates.length :=
  lt_of_le_of_lt (mem_reach_le hu) hw

private lemma reach_trans {C : Circuit} {N w v u : ℕ}
    (hv : v ∈ reach C N w) (hu : u ∈ reach C N v) : u ∈ reach C N w := by
  induction w using Nat.strong_induction_on generalizing v u with
  | _ w ih =>
    by_cases h1 : N ≤ w ∧ w - N < C.gates.length
    · rw [mem_reach_iff_gate h1.1 h1.2] at hv ⊢
      rcases hv with rfl | ⟨z, hz, hvz⟩
      · exact (mem_reach_iff_gate h1.1 h1.2).mp hu
      · exact Or.inr ⟨z, hz, ih z (refsOf_lt hz) hvz hu⟩
    · rw [reach] at hv
      simp only [h1, ↓reduceDIte] at hv
      split_ifs at hv with hlt
      · simp only [Finset.mem_singleton] at hv
        subst hv
        rw [reach] at hu ⊢
        simp only [h1, hlt, ↓reduceDIte, ↓reduceIte] at hu ⊢
        exact hu
      · simp at hv

private lemma mem_reach_has_parent {C : Circuit} {N w u : ℕ}
    (hu : u ∈ reach C N w) (hne : u ≠ w) :
    ∃ g ∈ (reach C N w).filter (fun x => N ≤ x), u ∈ refsOf C N g := by
  induction w using Nat.strong_induction_on generalizing u with
  | _ w ih =>
    by_cases h1 : N ≤ w ∧ w - N < C.gates.length
    · rw [mem_reach_iff_gate h1.1 h1.2] at hu
      rcases hu with rfl | ⟨v, hv, huv⟩
      · exact absurd rfl hne
      · by_cases huv_eq : u = v
        · subst huv_eq
          refine ⟨w, Finset.mem_filter.mpr ⟨mem_reach_self (by omega), h1.1⟩, hv⟩
        · obtain ⟨g, hg, hug⟩ := ih v (refsOf_lt hv) huv huv_eq
          rw [Finset.mem_filter] at hg
          have hgw : g ∈ reach C N w := by
            rw [mem_reach_iff_gate h1.1 h1.2]
            exact Or.inr ⟨v, hv, hg.1⟩
          exact ⟨g, Finset.mem_filter.mpr ⟨hgw, hg.2⟩, hug⟩
    · rw [reach] at hu
      simp only [h1, ↓reduceDIte] at hu
      split_ifs at hu
      · simp at hu; exact absurd hu hne
      · simp at hu

private lemma wires_agree_on_reach {C : Circuit} {N : ℕ}
    (hfan : FanInTwo C) {x1 x2 : List Bool} (hx1 : x1.length = N) (hx2 : x2.length = N)
    {w : ℕ} (hw : w < N + C.gates.length)
    (hagree : ∀ i ∈ (reach C N w).filter (· < N), x1.getD i false = x2.getD i false) :
    ∀ u ∈ reach C N w, (C.wires x1).getD u false = (C.wires x2).getD u false := by
  intro u hu
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    by_cases hlt : u < N
    · rw [circuit_wires_getD_input C x1 (by omega), circuit_wires_getD_input C x2 (by omega)]
      exact hagree u (Finset.mem_filter.mpr ⟨hu, hlt⟩)
    · have hu_lt : u < N + C.gates.length := reach_subset_lt hw hu
      have hj : u - N < C.gates.length := by omega
      have hu_eq : x1.length + (u - N) = u := by omega
      have hu_eq2 : x2.length + (u - N) = u := by omega
      have h1 := circuit_wires_getD_gate C x1 hj
      have h2 := circuit_wires_getD_gate C x2 hj
      rw [hu_eq] at h1
      rw [hu_eq2] at h2
      rw [h1, h2]
      have hhop : C.gates[u - N].op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) :=
        (hfan _ (List.getElem_mem hj)).1
      have hagree_eff : ∀ v ∈ effInputs N (u - N) C.gates[u - N],
          (C.wires x1).getD v false = (C.wires x2).getD v false := by
        intro v hv
        have hv_ref : v ∈ refsOf C N u := by
          unfold refsOf refsList
          have hcond : N ≤ u ∧ u - N < C.gates.length := ⟨by omega, hj⟩
          simp [hcond, hv]
        have hv_lt : v < u := refsOf_lt hv_ref
        have hv_reach : v ∈ reach C N w := by
          apply reach_trans hu
          rw [mem_reach_iff_gate (by omega) hj]
          exact Or.inr ⟨v, hv_ref, mem_reach_self (by omega)⟩
        exact ih v hv_lt hv_reach
      have hge := gate_eval_congr_effInputs (N := N) (j := u - N) hhop hagree_eff
      have hNu : N + (u - N) = u := by omega
      simp only [hNu] at hge
      exact hge

private lemma bool_le_of_imp {a b : Bool} (h : a = true → b = true) : a ≤ b := by
  cases a <;> cases b <;> simp_all

private lemma bool_eq_false_of_le : ∀ {a : Bool}, a ≤ false → a = false := by decide

private lemma bool_eq_true_of_le : ∀ {a : Bool}, true ≤ a → a = true := by decide

private lemma wires_mono_of_no_not {C : Circuit} {N : ℕ}
    (hfan : FanInTwo C) {x1 x2 : List Bool} (hx1 : x1.length = N) (hx2 : x2.length = N)
    {w : ℕ} (hw : w < N + C.gates.length)
    (hno_not : ∀ g ∈ (reach C N w).filter (fun z => N ≤ z),
      ∀ h : g - N < C.gates.length, C.gates[g - N].op ≠ .not)
    (hle : ∀ i ∈ (reach C N w).filter (· < N), x1.getD i false ≤ x2.getD i false) :
    ∀ u ∈ reach C N w, (C.wires x1).getD u false ≤ (C.wires x2).getD u false := by
  intro u hu
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    by_cases hlt : u < N
    · rw [circuit_wires_getD_input C x1 (by omega), circuit_wires_getD_input C x2 (by omega)]
      exact hle u (Finset.mem_filter.mpr ⟨hu, hlt⟩)
    · have hu_lt : u < N + C.gates.length := reach_subset_lt hw hu
      have hj : u - N < C.gates.length := by omega
      have h1 := circuit_wires_getD_gate C x1 hj
      have h2 := circuit_wires_getD_gate C x2 hj
      have hu1 : x1.length + (u - N) = u := by omega
      have hu2 : x2.length + (u - N) = u := by omega
      rw [hu1] at h1
      rw [hu2] at h2
      rw [h1, h2]
      have hnot : C.gates[u - N].op ≠ .not :=
        hno_not u (Finset.mem_filter.mpr ⟨hu, by omega⟩) hj
      have hhop := (hfan _ (List.getElem_mem hj)).1
      have hstep : ∀ i ∈ C.gates[u - N].inputs,
          (if i < u then (C.wires x1).getD i false else false) ≤
          (if i < u then (C.wires x2).getD i false else false) := by
        intro i hi
        by_cases hilt : i < u
        · simp only [hilt, ↓reduceIte]
          have hi_ref : i ∈ refsOf C N u := by
            unfold refsOf refsList
            have hcond : N ≤ u ∧ u - N < C.gates.length := ⟨by omega, hj⟩
            simp only [hcond, and_self, ↓reduceDIte, List.mem_toFinset]
            rcases hhop with h' | h' | h'
            · simp [effInputs, h', hi, show i < N + (u - N) by omega]
            · simp [effInputs, h', hi, show i < N + (u - N) by omega]
            · exact absurd h' hnot
          have hi_reach : i ∈ reach C N w := by
            apply reach_trans hu
            rw [mem_reach_iff_gate (by omega) hj]
            exact Or.inr ⟨i, hi_ref, mem_reach_self (by omega)⟩
          exact ih i hilt hi_reach
        · simp [hilt]
      rcases hhop with h' | h' | h'
      · rw [h']; simp only [GateOp.eval]
        apply bool_le_of_imp
        intro hres
        rw [List.all_eq_true] at hres ⊢
        intro b hb
        rw [List.mem_map] at hb
        rcases hb with ⟨i, hi, rfl⟩
        have h1i : (if i < u then (C.wires x1).getD i false else false) = true :=
          hres _ (List.mem_map_of_mem hi)
        have hle_i := hstep i hi
        rw [h1i] at hle_i
        exact bool_eq_true_of_le hle_i
      · rw [h']; simp only [GateOp.eval]
        apply bool_le_of_imp
        intro hres
        rw [List.any_eq_true] at hres ⊢
        rcases hres with ⟨b, hb, hbt⟩
        rw [List.mem_map] at hb
        rcases hb with ⟨i, hi, rfl⟩
        refine ⟨_, List.mem_map_of_mem hi, ?_⟩
        have hle_i := hstep i hi
        simp only [id_eq] at hbt ⊢
        rw [hbt] at hle_i
        exact bool_eq_true_of_le hle_i
      · exact absurd h' hnot

private lemma slot_count_ineq {C : Circuit} {N : ℕ}
    (hfan : FanInTwo C) (hout_ge : N ≤ C.output) (hout_lt : C.output < N + C.gates.length) :
    let R := reach C N C.output
    let I := R.filter (· < N)
    let L := R.filter (fun z => N ≤ z)
    let Lnot := L.filter (fun g => isNotGate C N g = true)
    I.card + L.card - 1 ≤ (L.biUnion (refsOf C N)).card ∧
    (L.biUnion (refsOf C N)).card ≤ ∑ g ∈ L, (refsOf C N g).card ∧
    ∑ g ∈ L, (refsOf C N g).card ≤ 2 * L.card - Lnot.card ∧
    I.card + Lnot.card ≤ L.card + 1 ∧
    L.card ≤ C.gates.length := by
  intro R I L Lnot
  have hsub1 : R.erase C.output ⊆ L.biUnion (refsOf C N) := by
    intro u hu
    rw [Finset.mem_erase] at hu
    obtain ⟨g, hg, hug⟩ := mem_reach_has_parent hu.2 hu.1
    exact Finset.mem_biUnion.mpr ⟨g, hg, hug⟩
  have hout_in : C.output ∈ R := mem_reach_self hout_lt
  have hpart : I.card + L.card = R.card := by
    have hdisj : Disjoint I L := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      rw [Finset.mem_filter] at hx1 hx2
      omega
    have hunion : I ∪ L = R := by
      ext x
      simp only [I, L, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro h
        by_cases hlt : x < N
        · exact Or.inl ⟨h, hlt⟩
        · exact Or.inr ⟨h, by omega⟩
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
  have hcard_erase : (R.erase C.output).card = I.card + L.card - 1 := by
    rw [Finset.card_erase_of_mem hout_in, hpart]
  have hineq1 : I.card + L.card - 1 ≤ (L.biUnion (refsOf C N)).card := by
    rw [← hcard_erase]
    exact Finset.card_le_card hsub1
  have hineq2 : (L.biUnion (refsOf C N)).card ≤ ∑ g ∈ L, (refsOf C N g).card :=
    Finset.card_biUnion_le
  have hsum_le : ∑ g ∈ L, (refsOf C N g).card + Lnot.card ≤ 2 * L.card := by
    have hLnot_eq : Lnot.card = ∑ g ∈ L, (if isNotGate C N g then 1 else 0) := by
      rw [Finset.card_filter]
    rw [hLnot_eq, ← Finset.sum_add_distrib]
    have h2L : 2 * L.card = ∑ _g ∈ L, 2 := by simp [mul_comm]
    rw [h2L]
    apply Finset.sum_le_sum
    intro g hg
    have hgR : g ∈ R := (Finset.mem_filter.mp hg).1
    have hgN : N ≤ g := (Finset.mem_filter.mp hg).2
    have hg_lt : g < N + C.gates.length := reach_subset_lt hout_lt hgR
    have hgj : g - N < C.gates.length := by omega
    have hlen : C.gates[g - N].inputs.length ≤ 2 := (hfan _ (List.getElem_mem hgj)).2
    have hc := effInputs_card_le N (g - N) C.gates[g - N] hlen
    have href : refsOf C N g = (effInputs N (g - N) C.gates[g - N]).toFinset := by
      unfold refsOf refsList
      simp [hgN, hgj]
    rw [href]
    simp only [isNotGate, hgj, ↓reduceDIte]
    cases hnot : isNotOp C.gates[g - N].op <;>
      simp only [hnot, Bool.false_eq_true, ↓reduceIte] at hc ⊢ <;> omega
  have hLnot_le : Lnot.card ≤ L.card := Finset.card_filter_le _ _
  have hineq3 : ∑ g ∈ L, (refsOf C N g).card ≤ 2 * L.card - Lnot.card := by omega
  have hLpos : 1 ≤ L.card := by
    have : C.output ∈ L := Finset.mem_filter.mpr ⟨hout_in, hout_ge⟩
    exact Finset.card_pos.mpr ⟨C.output, this⟩
  have hineq4 : I.card + Lnot.card ≤ L.card + 1 := by omega
  have hL_le : L.card ≤ C.gates.length := by
    have hsubL : L ⊆ (Finset.range C.gates.length).image (fun j => N + j) := by
      intro g hg
      have hgR : g ∈ R := (Finset.mem_filter.mp hg).1
      have hgN : N ≤ g := (Finset.mem_filter.mp hg).2
      have hglt : g < N + C.gates.length := reach_subset_lt hout_lt hgR
      exact Finset.mem_image.mpr ⟨g - N, Finset.mem_range.mpr (by omega), by omega⟩
    calc L.card ≤ ((Finset.range C.gates.length).image (fun j => N + j)).card :=
          Finset.card_le_card hsubL
      _ ≤ (Finset.range C.gates.length).card := Finset.card_image_le
      _ = C.gates.length := Finset.card_range _
  exact ⟨hineq1, hineq2, hineq3, hineq4, hL_le⟩

private inductive FTree where
  | leaf (w : ℕ) : FTree
  | not (t : FTree) : FTree
  | and (l r : FTree) : FTree
  | or (l r : FTree) : FTree

private def FTree.eval (v : ℕ → Bool) : FTree → Bool
  | .leaf w => v w
  | .not t => !(t.eval v)
  | .and l r => l.eval v && r.eval v
  | .or l r => l.eval v || r.eval v

private def FTree.leaves : FTree → Finset ℕ
  | .leaf w => {w}
  | .not t => t.leaves
  | .and l r => l.leaves ∪ r.leaves
  | .or l r => l.leaves ∪ r.leaves

private def FTree.readOnce : FTree → Prop
  | .leaf _ => True
  | .not t => t.readOnce
  | .and l r => l.readOnce ∧ r.readOnce ∧ Disjoint l.leaves r.leaves
  | .or l r => l.readOnce ∧ r.readOnce ∧ Disjoint l.leaves r.leaves

private def FTree.notCount : FTree → ℕ
  | .leaf _ => 0
  | .not t => t.notCount + 1
  | .and l r => l.notCount + r.notCount
  | .or l r => l.notCount + r.notCount

private lemma FTree.leaves_nonempty (t : FTree) : t.leaves.Nonempty := by
  induction t with
  | leaf w => exact ⟨w, Finset.mem_singleton_self w⟩
  | not t ih => exact ih
  | and l r ihl _ =>
    rcases ihl with ⟨w, hw⟩
    exact ⟨w, Finset.mem_union_left _ hw⟩
  | or l r ihl _ =>
    rcases ihl with ⟨w, hw⟩
    exact ⟨w, Finset.mem_union_left _ hw⟩

private lemma FTree.eval_congr {t : FTree} {v1 v2 : ℕ → Bool}
    (h : ∀ w ∈ t.leaves, v1 w = v2 w) : t.eval v1 = t.eval v2 := by
  induction t with
  | leaf w => exact h w (Finset.mem_singleton_self w)
  | not t ih => simp [FTree.eval, ih h]
  | and l r ihl ihr =>
    simp [FTree.eval, ihl (fun w hw => h w (Finset.mem_union_left _ hw)),
      ihr (fun w hw => h w (Finset.mem_union_right _ hw))]
  | or l r ihl ihr =>
    simp [FTree.eval, ihl (fun w hw => h w (Finset.mem_union_left _ hw)),
      ihr (fun w hw => h w (Finset.mem_union_right _ hw))]

private lemma FTree.eval_mono_of_notCount_zero {t : FTree} (h0 : t.notCount = 0)
    {v1 v2 : ℕ → Bool} (hle : ∀ w ∈ t.leaves, v1 w ≤ v2 w) : t.eval v1 ≤ t.eval v2 := by
  induction t with
  | leaf w => exact hle w (Finset.mem_singleton_self w)
  | not t _ => simp [FTree.notCount] at h0
  | and l r ihl ihr =>
    simp only [FTree.notCount, Nat.add_eq_zero_iff] at h0
    have hl := ihl h0.1 (fun w hw => hle w (Finset.mem_union_left _ hw))
    have hr := ihr h0.2 (fun w hw => hle w (Finset.mem_union_right _ hw))
    simp only [FTree.eval]
    cases h1 : l.eval v1 <;> cases h2 : r.eval v1 <;>
      cases h3 : l.eval v2 <;> cases h4 : r.eval v2 <;> simp_all
  | or l r ihl ihr =>
    simp only [FTree.notCount, Nat.add_eq_zero_iff] at h0
    have hl := ihl h0.1 (fun w hw => hle w (Finset.mem_union_left _ hw))
    have hr := ihr h0.2 (fun w hw => hle w (Finset.mem_union_right _ hw))
    simp only [FTree.eval]
    cases h1 : l.eval v1 <;> cases h2 : r.eval v1 <;>
      cases h3 : l.eval v2 <;> cases h4 : r.eval v2 <;> simp_all

private lemma FTree.eval_false_of_notCount_zero {t : FTree} (h0 : t.notCount = 0) :
    t.eval (fun _ => false) = false := by
  induction t with
  | leaf _ => rfl
  | not _ _ => simp [FTree.notCount] at h0
  | and l r ihl ihr =>
    simp only [FTree.notCount, Nat.add_eq_zero_iff] at h0
    simp [FTree.eval, ihl h0.1, ihr h0.2]
  | or l r ihl ihr =>
    simp only [FTree.notCount, Nat.add_eq_zero_iff] at h0
    simp [FTree.eval, ihl h0.1, ihr h0.2]

private lemma FTree.unate_of_readOnce {t : FTree} (hro : t.readOnce) (w : ℕ) :
    (∀ v : ℕ → Bool, t.eval (Function.update v w false) ≤ t.eval (Function.update v w true)) ∨
    (∀ v : ℕ → Bool, t.eval (Function.update v w true) ≤ t.eval (Function.update v w false)) := by
  induction t with
  | leaf u =>
    by_cases h : u = w
    · subst h; left; intro v; simp [FTree.eval]
    · left; intro v; simp [FTree.eval, Function.update, h]
  | not t ih =>
    rcases ih hro with h | h
    · right; intro v; have := h v; simp only [FTree.eval]
      cases h1 : t.eval (Function.update v w false) <;> cases h2 : t.eval (Function.update v w true) <;> simp_all
    · left; intro v; have := h v; simp only [FTree.eval]
      cases h1 : t.eval (Function.update v w false) <;> cases h2 : t.eval (Function.update v w true) <;> simp_all
  | and l r ihl ihr =>
    rcases hro with ⟨hl, hr, hdisj⟩
    by_cases hwl : w ∈ l.leaves
    · have hwr : w ∉ r.leaves := Finset.disjoint_left.mp hdisj hwl
      have hreq : ∀ v b, r.eval (Function.update v w b) = r.eval v := by
        intro v b; apply FTree.eval_congr; intro u hu
        have hne : u ≠ w := fun heq => hwr (heq ▸ hu)
        simp [Function.update, hne]
      rcases ihl hl with h | h
      · left; intro v; simp only [FTree.eval, hreq]
        have := h v
        cases r.eval v <;> cases h1 : l.eval (Function.update v w false) <;>
          cases h2 : l.eval (Function.update v w true) <;> simp_all
      · right; intro v; simp only [FTree.eval, hreq]
        have := h v
        cases r.eval v <;> cases h1 : l.eval (Function.update v w false) <;>
          cases h2 : l.eval (Function.update v w true) <;> simp_all
    · have hleq : ∀ v b, l.eval (Function.update v w b) = l.eval v := by
        intro v b; apply FTree.eval_congr; intro u hu
        have hne : u ≠ w := fun heq => hwl (heq ▸ hu)
        simp [Function.update, hne]
      rcases ihr hr with h | h
      · left; intro v; simp only [FTree.eval, hleq]
        have := h v
        cases l.eval v <;> cases h1 : r.eval (Function.update v w false) <;>
          cases h2 : r.eval (Function.update v w true) <;> simp_all
      · right; intro v; simp only [FTree.eval, hleq]
        have := h v
        cases l.eval v <;> cases h1 : r.eval (Function.update v w false) <;>
          cases h2 : r.eval (Function.update v w true) <;> simp_all
  | or l r ihl ihr =>
    rcases hro with ⟨hl, hr, hdisj⟩
    by_cases hwl : w ∈ l.leaves
    · have hwr : w ∉ r.leaves := Finset.disjoint_left.mp hdisj hwl
      have hreq : ∀ v b, r.eval (Function.update v w b) = r.eval v := by
        intro v b; apply FTree.eval_congr; intro u hu
        have hne : u ≠ w := fun heq => hwr (heq ▸ hu)
        simp [Function.update, hne]
      rcases ihl hl with h | h
      · left; intro v; simp only [FTree.eval, hreq]
        have := h v
        cases r.eval v <;> cases h1 : l.eval (Function.update v w false) <;>
          cases h2 : l.eval (Function.update v w true) <;> simp_all
      · right; intro v; simp only [FTree.eval, hreq]
        have := h v
        cases r.eval v <;> cases h1 : l.eval (Function.update v w false) <;>
          cases h2 : l.eval (Function.update v w true) <;> simp_all
    · have hleq : ∀ v b, l.eval (Function.update v w b) = l.eval v := by
        intro v b; apply FTree.eval_congr; intro u hu
        have hne : u ≠ w := fun heq => hwl (heq ▸ hu)
        simp [Function.update, hne]
      rcases ihr hr with h | h
      · left; intro v; simp only [FTree.eval, hleq]
        have := h v
        cases l.eval v <;> cases h1 : r.eval (Function.update v w false) <;>
          cases h2 : r.eval (Function.update v w true) <;> simp_all
      · right; intro v; simp only [FTree.eval, hleq]
        have := h v
        cases l.eval v <;> cases h1 : r.eval (Function.update v w false) <;>
          cases h2 : r.eval (Function.update v w true) <;> simp_all

private def FTree.posLeaves : FTree → Finset ℕ
  | .leaf w => {w}
  | .not _ => ∅
  | .and l r => l.posLeaves ∪ r.posLeaves
  | .or l r => l.posLeaves ∪ r.posLeaves

private def FTree.negLeaves : FTree → Finset ℕ
  | .leaf _ => ∅
  | .not t => t.leaves
  | .and l r => l.negLeaves ∪ r.negLeaves
  | .or l r => l.negLeaves ∪ r.negLeaves

private lemma FTree.pos_of_notCount_zero {t : FTree} (h0 : t.notCount = 0) :
    t.posLeaves = t.leaves ∧ t.negLeaves = ∅ := by
  induction t with
  | leaf w => simp [FTree.posLeaves, FTree.negLeaves, FTree.leaves]
  | not _ _ => simp [FTree.notCount] at h0
  | and l r ihl ihr =>
    simp only [FTree.notCount, Nat.add_eq_zero_iff] at h0
    simp [FTree.posLeaves, FTree.negLeaves, FTree.leaves, (ihl h0.1).1, (ihl h0.1).2,
      (ihr h0.2).1, (ihr h0.2).2]
  | or l r ihl ihr =>
    simp only [FTree.notCount, Nat.add_eq_zero_iff] at h0
    simp [FTree.posLeaves, FTree.negLeaves, FTree.leaves, (ihl h0.1).1, (ihl h0.1).2,
      (ihr h0.2).1, (ihr h0.2).2]

private lemma FTree.pos_neg_partition {t : FTree} (h1 : t.notCount ≤ 1) :
    t.posLeaves ∪ t.negLeaves = t.leaves := by
  induction t with
  | leaf w => simp [FTree.posLeaves, FTree.negLeaves, FTree.leaves]
  | not t _ => simp [FTree.posLeaves, FTree.negLeaves, FTree.leaves]
  | and l r ihl ihr =>
    simp only [FTree.notCount] at h1
    simp only [FTree.posLeaves, FTree.negLeaves, FTree.leaves]
    rw [← ihl (by omega), ← ihr (by omega)]
    ext x; simp; tauto
  | or l r ihl ihr =>
    simp only [FTree.notCount] at h1
    simp only [FTree.posLeaves, FTree.negLeaves, FTree.leaves]
    rw [← ihl (by omega), ← ihr (by omega)]
    ext x; simp; tauto

private lemma FTree.posLeaf_mono {t : FTree} (hro : t.readOnce) (h1 : t.notCount ≤ 1)
    {w : ℕ} (hw : w ∈ t.posLeaves) (v : ℕ → Bool) :
    t.eval (Function.update v w false) ≤ t.eval (Function.update v w true) := by
  induction t with
  | leaf u =>
    simp only [FTree.posLeaves, Finset.mem_singleton] at hw
    subst hw; simp [FTree.eval]
  | not _ _ => simp [FTree.posLeaves] at hw
  | and l r ihl ihr =>
    rcases hro with ⟨hl, hr, hdisj⟩
    simp only [FTree.notCount] at h1
    simp only [FTree.posLeaves, Finset.mem_union] at hw
    have hsubl : l.posLeaves ⊆ l.leaves := by
      rw [← FTree.pos_neg_partition (by omega)]; exact Finset.subset_union_left
    have hsubr : r.posLeaves ⊆ r.leaves := by
      rw [← FTree.pos_neg_partition (by omega)]; exact Finset.subset_union_left
    rcases hw with hwl | hwr
    · have hnotin : w ∉ r.leaves := Finset.disjoint_left.mp hdisj (hsubl hwl)
      have hreq : ∀ b, r.eval (Function.update v w b) = r.eval v := fun b =>
        FTree.eval_congr fun u hu => by simp [Function.update, show u ≠ w from fun e => hnotin (e ▸ hu)]
      have hm := ihl hl (by omega) hwl
      simp only [FTree.eval, hreq]
      cases r.eval v <;> cases h1 : l.eval (Function.update v w false) <;>
        cases h2 : l.eval (Function.update v w true) <;> simp_all
    · have hnotin : w ∉ l.leaves := Finset.disjoint_right.mp hdisj (hsubr hwr)
      have hleq : ∀ b, l.eval (Function.update v w b) = l.eval v := fun b =>
        FTree.eval_congr fun u hu => by simp [Function.update, show u ≠ w from fun e => hnotin (e ▸ hu)]
      have hm := ihr hr (by omega) hwr
      simp only [FTree.eval, hleq]
      cases l.eval v <;> cases h1 : r.eval (Function.update v w false) <;>
        cases h2 : r.eval (Function.update v w true) <;> simp_all
  | or l r ihl ihr =>
    rcases hro with ⟨hl, hr, hdisj⟩
    simp only [FTree.notCount] at h1
    simp only [FTree.posLeaves, Finset.mem_union] at hw
    have hsubl : l.posLeaves ⊆ l.leaves := by
      rw [← FTree.pos_neg_partition (by omega)]; exact Finset.subset_union_left
    have hsubr : r.posLeaves ⊆ r.leaves := by
      rw [← FTree.pos_neg_partition (by omega)]; exact Finset.subset_union_left
    rcases hw with hwl | hwr
    · have hnotin : w ∉ r.leaves := Finset.disjoint_left.mp hdisj (hsubl hwl)
      have hreq : ∀ b, r.eval (Function.update v w b) = r.eval v := fun b =>
        FTree.eval_congr fun u hu => by simp [Function.update, show u ≠ w from fun e => hnotin (e ▸ hu)]
      have hm := ihl hl (by omega) hwl
      simp only [FTree.eval, hreq]
      cases r.eval v <;> cases h1 : l.eval (Function.update v w false) <;>
        cases h2 : l.eval (Function.update v w true) <;> simp_all
    · have hnotin : w ∉ l.leaves := Finset.disjoint_right.mp hdisj (hsubr hwr)
      have hleq : ∀ b, l.eval (Function.update v w b) = l.eval v := fun b =>
        FTree.eval_congr fun u hu => by simp [Function.update, show u ≠ w from fun e => hnotin (e ▸ hu)]
      have hm := ihr hr (by omega) hwr
      simp only [FTree.eval, hleq]
      cases l.eval v <;> cases h1 : r.eval (Function.update v w false) <;>
        cases h2 : r.eval (Function.update v w true) <;> simp_all

private lemma FTree.negLeaf_anti {t : FTree} (hro : t.readOnce) (h1 : t.notCount ≤ 1)
    {w : ℕ} (hw : w ∈ t.negLeaves) (v : ℕ → Bool) :
    t.eval (Function.update v w true) ≤ t.eval (Function.update v w false) := by
  induction t with
  | leaf _ => simp [FTree.negLeaves] at hw
  | not t _ =>
    simp only [FTree.notCount] at h1
    have h0 : t.notCount = 0 := by omega
    have hm : t.eval (Function.update v w false) ≤ t.eval (Function.update v w true) := by
      apply FTree.eval_mono_of_notCount_zero h0
      intro u _
      by_cases hu : u = w
      · subst hu; simp
      · simp [Function.update, hu]
    simp only [FTree.eval]
    cases h1' : t.eval (Function.update v w false) <;>
      cases h2' : t.eval (Function.update v w true) <;> simp_all
  | and l r ihl ihr =>
    rcases hro with ⟨hl, hr, hdisj⟩
    simp only [FTree.notCount] at h1
    simp only [FTree.negLeaves, Finset.mem_union] at hw
    have hsubl : l.negLeaves ⊆ l.leaves := by
      rw [← FTree.pos_neg_partition (by omega)]; exact Finset.subset_union_right
    have hsubr : r.negLeaves ⊆ r.leaves := by
      rw [← FTree.pos_neg_partition (by omega)]; exact Finset.subset_union_right
    rcases hw with hwl | hwr
    · have hnotin : w ∉ r.leaves := Finset.disjoint_left.mp hdisj (hsubl hwl)
      have hreq : ∀ b, r.eval (Function.update v w b) = r.eval v := fun b =>
        FTree.eval_congr fun u hu => by simp [Function.update, show u ≠ w from fun e => hnotin (e ▸ hu)]
      have hm := ihl hl (by omega) hwl
      simp only [FTree.eval, hreq]
      cases r.eval v <;> cases h1 : l.eval (Function.update v w false) <;>
        cases h2 : l.eval (Function.update v w true) <;> simp_all
    · have hnotin : w ∉ l.leaves := Finset.disjoint_right.mp hdisj (hsubr hwr)
      have hleq : ∀ b, l.eval (Function.update v w b) = l.eval v := fun b =>
        FTree.eval_congr fun u hu => by simp [Function.update, show u ≠ w from fun e => hnotin (e ▸ hu)]
      have hm := ihr hr (by omega) hwr
      simp only [FTree.eval, hleq]
      cases l.eval v <;> cases h1 : r.eval (Function.update v w false) <;>
        cases h2 : r.eval (Function.update v w true) <;> simp_all
  | or l r ihl ihr =>
    rcases hro with ⟨hl, hr, hdisj⟩
    simp only [FTree.notCount] at h1
    simp only [FTree.negLeaves, Finset.mem_union] at hw
    have hsubl : l.negLeaves ⊆ l.leaves := by
      rw [← FTree.pos_neg_partition (by omega)]; exact Finset.subset_union_right
    have hsubr : r.negLeaves ⊆ r.leaves := by
      rw [← FTree.pos_neg_partition (by omega)]; exact Finset.subset_union_right
    rcases hw with hwl | hwr
    · have hnotin : w ∉ r.leaves := Finset.disjoint_left.mp hdisj (hsubl hwl)
      have hreq : ∀ b, r.eval (Function.update v w b) = r.eval v := fun b =>
        FTree.eval_congr fun u hu => by simp [Function.update, show u ≠ w from fun e => hnotin (e ▸ hu)]
      have hm := ihl hl (by omega) hwl
      simp only [FTree.eval, hreq]
      cases r.eval v <;> cases h1 : l.eval (Function.update v w false) <;>
        cases h2 : l.eval (Function.update v w true) <;> simp_all
    · have hnotin : w ∉ l.leaves := Finset.disjoint_right.mp hdisj (hsubr hwr)
      have hleq : ∀ b, l.eval (Function.update v w b) = l.eval v := fun b =>
        FTree.eval_congr fun u hu => by simp [Function.update, show u ≠ w from fun e => hnotin (e ▸ hu)]
      have hm := ihr hr (by omega) hwr
      simp only [FTree.eval, hleq]
      cases l.eval v <;> cases h1 : r.eval (Function.update v w false) <;>
        cases h2 : r.eval (Function.update v w true) <;> simp_all

private lemma FTree.not_at_top_of_posLeaves_empty {t : FTree} (h1 : t.notCount = 1)
    (hpos : t.posLeaves = ∅) : ∃ t0 : FTree, t = .not t0 ∧ t0.notCount = 0 := by
  cases t with
  | leaf w => simp [FTree.notCount] at h1
  | not t0 =>
    simp only [FTree.notCount] at h1
    exact ⟨t0, rfl, by omega⟩
  | and l r =>
    simp only [FTree.notCount] at h1
    simp only [FTree.posLeaves, Finset.union_eq_empty] at hpos
    by_cases hl : l.notCount = 0
    · have hpl := (FTree.pos_of_notCount_zero hl).1
      rw [hpos.1] at hpl
      rcases l.leaves_nonempty with ⟨w, hw⟩
      rw [← hpl] at hw
      simp at hw
    · have hr : r.notCount = 0 := by omega
      have hpr := (FTree.pos_of_notCount_zero hr).1
      rw [hpos.2] at hpr
      rcases r.leaves_nonempty with ⟨w, hw⟩
      rw [← hpr] at hw
      simp at hw
  | or l r =>
    simp only [FTree.notCount] at h1
    simp only [FTree.posLeaves, Finset.union_eq_empty] at hpos
    by_cases hl : l.notCount = 0
    · have hpl := (FTree.pos_of_notCount_zero hl).1
      rw [hpos.1] at hpl
      rcases l.leaves_nonempty with ⟨w, hw⟩
      rw [← hpl] at hw
      simp at hw
    · have hr : r.notCount = 0 := by omega
      have hpr := (FTree.pos_of_notCount_zero hr).1
      rw [hpos.2] at hpr
      rcases r.leaves_nonempty with ⟨w, hw⟩
      rw [← hpr] at hw
      simp at hw

private lemma FTree.eval_factors_through_not {t : FTree} (h1 : t.notCount = 1) :
    ∃ (sub : FTree) (H : (ℕ → Bool) → Bool → Bool),
      sub.leaves = t.negLeaves ∧
      (∀ v1 v2 b, (∀ w ∈ t.posLeaves, v1 w = v2 w) → H v1 b = H v2 b) ∧
      ∀ v, t.eval v = H v (sub.eval v) := by
  induction t with
  | leaf _ => simp [FTree.notCount] at h1
  | not t0 =>
    refine ⟨t0, fun _ b => !b, rfl, fun _ _ _ _ => rfl, fun _ => rfl⟩
  | and l r ihl ihr =>
    simp only [FTree.notCount] at h1
    by_cases hl : l.notCount = 1
    · have hr0 : r.notCount = 0 := by omega
      obtain ⟨sub, H, hsub, hH, heval⟩ := ihl hl
      refine ⟨sub, fun v b => H v b && r.eval v, ?_, ?_, ?_⟩
      · simp [FTree.negLeaves, (FTree.pos_of_notCount_zero hr0).2, hsub]
      · intro v1 v2 b hagree
        have h1' := hH v1 v2 b (fun w hw => hagree w (Finset.mem_union_left _ hw))
        have h2' : r.eval v1 = r.eval v2 := FTree.eval_congr fun w hw => by
          apply hagree w
          rw [FTree.posLeaves, Finset.mem_union]
          exact Or.inr ((FTree.pos_of_notCount_zero hr0).1.symm ▸ hw)
        dsimp only; rw [h1', h2']
      · intro v; simp [FTree.eval, heval]
    · have hr1 : r.notCount = 1 := by omega
      have hl0 : l.notCount = 0 := by omega
      obtain ⟨sub, H, hsub, hH, heval⟩ := ihr hr1
      refine ⟨sub, fun v b => l.eval v && H v b, ?_, ?_, ?_⟩
      · simp [FTree.negLeaves, (FTree.pos_of_notCount_zero hl0).2, hsub]
      · intro v1 v2 b hagree
        have h2' := hH v1 v2 b (fun w hw => hagree w (Finset.mem_union_right _ hw))
        have h1' : l.eval v1 = l.eval v2 := FTree.eval_congr fun w hw => by
          apply hagree w
          rw [FTree.posLeaves, Finset.mem_union]
          exact Or.inl ((FTree.pos_of_notCount_zero hl0).1.symm ▸ hw)
        dsimp only; rw [h1', h2']
      · intro v; simp [FTree.eval, heval]
  | or l r ihl ihr =>
    simp only [FTree.notCount] at h1
    by_cases hl : l.notCount = 1
    · have hr0 : r.notCount = 0 := by omega
      obtain ⟨sub, H, hsub, hH, heval⟩ := ihl hl
      refine ⟨sub, fun v b => H v b || r.eval v, ?_, ?_, ?_⟩
      · simp [FTree.negLeaves, (FTree.pos_of_notCount_zero hr0).2, hsub]
      · intro v1 v2 b hagree
        have h1' := hH v1 v2 b (fun w hw => hagree w (Finset.mem_union_left _ hw))
        have h2' : r.eval v1 = r.eval v2 := FTree.eval_congr fun w hw => by
          apply hagree w
          rw [FTree.posLeaves, Finset.mem_union]
          exact Or.inr ((FTree.pos_of_notCount_zero hr0).1.symm ▸ hw)
        dsimp only; rw [h1', h2']
      · intro v; simp [FTree.eval, heval]
    · have hr1 : r.notCount = 1 := by omega
      have hl0 : l.notCount = 0 := by omega
      obtain ⟨sub, H, hsub, hH, heval⟩ := ihr hr1
      refine ⟨sub, fun v b => l.eval v || H v b, ?_, ?_, ?_⟩
      · simp [FTree.negLeaves, (FTree.pos_of_notCount_zero hl0).2, hsub]
      · intro v1 v2 b hagree
        have h2' := hH v1 v2 b (fun w hw => hagree w (Finset.mem_union_right _ hw))
        have h1' : l.eval v1 = l.eval v2 := FTree.eval_congr fun w hw => by
          apply hagree w
          rw [FTree.posLeaves, Finset.mem_union]
          exact Or.inl ((FTree.pos_of_notCount_zero hl0).1.symm ▸ hw)
        dsimp only; rw [h1', h2']
      · intro v; simp [FTree.eval, heval]

private lemma extract_ftree {C : Circuit} {N : ℕ}
    (hfan : FanInTwo C) (hout_ge : N ≤ C.output) (hout_lt : C.output < N + C.gates.length)
    (htight :
      let R := reach C N C.output
      let I := R.filter (· < N)
      let L := R.filter (fun z => N ≤ z)
      let Lnot := L.filter (fun g => isNotGate C N g = true)
      I.card + Lnot.card = L.card + 1) :
    ∃ T : FTree,
      T.readOnce ∧
      T.leaves = (reach C N C.output).filter (· < N) ∧
      T.notCount = (((reach C N C.output).filter (fun z => N ≤ z)).filter
        (fun g => isNotGate C N g = true)).card ∧
      ∀ x : List Bool, x.length = N → C.eval x = T.eval (fun i => x.getD i false) := by
  set R := reach C N C.output
  set I := R.filter (· < N)
  set L := R.filter (fun z => N ≤ z)
  set Lnot := L.filter (fun g => isNotGate C N g = true)
  have hslot := slot_count_ineq hfan hout_ge hout_lt
  rcases hslot with ⟨h1, h2, h3, h4, _⟩
  have h1' : I.card + L.card - 1 ≤ (L.biUnion (refsOf C N)).card := h1
  have h2' : (L.biUnion (refsOf C N)).card ≤ ∑ g ∈ L, (refsOf C N g).card := h2
  have h3' : ∑ g ∈ L, (refsOf C N g).card ≤ 2 * L.card - Lnot.card := h3
  have htight' : I.card + Lnot.card = L.card + 1 := htight
  have hLnot_le : Lnot.card ≤ L.card := Finset.card_filter_le _ _
  have hLpos : 1 ≤ L.card :=
    Finset.card_pos.mpr ⟨C.output, Finset.mem_filter.mpr ⟨mem_reach_self hout_lt, hout_ge⟩⟩
  have hbi_eq : (L.biUnion (refsOf C N)).card = ∑ g ∈ L, (refsOf C N g).card := by omega
  have hsum_eq : ∑ g ∈ L, (refsOf C N g).card = 2 * L.card - Lnot.card := by omega

  have hdisj : Set.PairwiseDisjoint (L : Set ℕ) (refsOf C N) := by
    by_contra hnd
    simp only [Set.PairwiseDisjoint, Set.Pairwise, Finset.mem_coe] at hnd
    push_neg at hnd
    rcases hnd with ⟨g1, hg1, g2, hg2, hne, hndisj⟩
    rw [Finset.not_disjoint_iff] at hndisj
    rcases hndisj with ⟨z, hz1, hz2⟩
    have hlt : (L.biUnion (refsOf C N)).card < ∑ g ∈ L, (refsOf C N g).card := by
      have hdecomp : L.biUnion (refsOf C N) =
          refsOf C N g1 ∪ (L.erase g1).biUnion (refsOf C N) := by
        ext u; simp only [Finset.mem_biUnion, Finset.mem_union, Finset.mem_erase]
        constructor
        · rintro ⟨g, hg, hu⟩
          by_cases heq : g = g1
          · exact Or.inl (heq ▸ hu)
          · exact Or.inr ⟨g, ⟨heq, hg⟩, hu⟩
        · rintro (hu | ⟨g, ⟨_, hg⟩, hu⟩)
          · exact ⟨g1, hg1, hu⟩
          · exact ⟨g, hg, hu⟩
      rw [hdecomp]
      have hz_in : z ∈ refsOf C N g1 ∩ (L.erase g1).biUnion (refsOf C N) :=
        Finset.mem_inter.mpr ⟨hz1, Finset.mem_biUnion.mpr ⟨g2, Finset.mem_erase.mpr ⟨hne.symm, hg2⟩, hz2⟩⟩
      have hinter_pos : 0 < (refsOf C N g1 ∩ (L.erase g1).biUnion (refsOf C N)).card :=
        Finset.card_pos.mpr ⟨z, hz_in⟩
      have hcu := Finset.card_union_add_card_inter (refsOf C N g1) ((L.erase g1).biUnion (refsOf C N))
      have hle2 : ((L.erase g1).biUnion (refsOf C N)).card ≤
          ∑ g ∈ L.erase g1, (refsOf C N g).card := Finset.card_biUnion_le
      have hsum_er : (refsOf C N g1).card + ∑ g ∈ L.erase g1, (refsOf C N g).card =
          ∑ g ∈ L, (refsOf C N g).card := Finset.add_sum_erase L (fun g => (refsOf C N g).card) hg1
      omega
    omega

  have hcard_each : ∀ g ∈ L, (refsOf C N g).card =
      if isNotGate C N g then 1 else 2 := by
    intro g hg
    have hle_all : ∀ x ∈ L, (refsOf C N x).card ≤
        (if isNotGate C N x then 1 else 2) := by
      intro x hx
      have hxR : x ∈ R := (Finset.mem_filter.mp hx).1
      have hxN : N ≤ x := (Finset.mem_filter.mp hx).2
      have hxlt : x < N + C.gates.length := reach_subset_lt hout_lt hxR
      have hxj : x - N < C.gates.length := by omega
      have hlen := (hfan _ (List.getElem_mem hxj)).2
      have hc := effInputs_card_le N (x - N) C.gates[x - N] hlen
      have href : refsOf C N x = (effInputs N (x - N) C.gates[x - N]).toFinset := by
        unfold refsOf refsList; simp [hxN, hxj]
      rw [href]; simp only [isNotGate, hxj, ↓reduceDIte]; exact hc
    have hsum_bound : ∑ x ∈ L, (if isNotGate C N x then 1 else 2) = 2 * L.card - Lnot.card := by
      have h1' : ∑ x ∈ L, ((if isNotGate C N x then 1 else 2) + (if isNotGate C N x then 1 else 0)) =
          2 * L.card := by
        calc ∑ x ∈ L, _ = ∑ _x ∈ L, 2 := by
              apply Finset.sum_congr rfl
              intro x _
              cases isNotGate C N x <;> simp
          _ = 2 * L.card := by simp [mul_comm]
      rw [Finset.sum_add_distrib] at h1'
      have hLnot_eq : Lnot.card = ∑ x ∈ L, (if isNotGate C N x then 1 else 0) := by
        rw [Finset.card_filter]
      omega
    by_contra hne
    have hlt_g : (refsOf C N g).card < (if isNotGate C N g then 1 else 2) :=
      lt_of_le_of_ne (hle_all g hg) hne
    have hlt_sum : ∑ x ∈ L, (refsOf C N x).card <
        ∑ x ∈ L, (if isNotGate C N x then 1 else 2) :=
      Finset.sum_lt_sum hle_all ⟨g, hg, hlt_g⟩
    omega

  have hreach_disj : ∀ g ∈ L, ∀ a ∈ refsOf C N g, ∀ b ∈ refsOf C N g, a ≠ b →
      Disjoint (reach C N a) (reach C N b) := by
    intro g hg a ha b hb hab
    rw [Finset.disjoint_left]
    intro z hza hzb
    set S := reach C N a ∩ reach C N b
    have hS : S.Nonempty := ⟨z, Finset.mem_inter.mpr ⟨hza, hzb⟩⟩
    set m := S.max' hS
    have hm : m ∈ S := Finset.max'_mem S hS
    have hma : m ∈ reach C N a := (Finset.mem_inter.mp hm).1
    have hmb : m ∈ reach C N b := (Finset.mem_inter.mp hm).2
    have hga : a < g := refsOf_lt ha
    have hgb : b < g := refsOf_lt hb
    have haR : a ∈ R := by
      apply reach_trans (Finset.mem_filter.mp hg).1
      have hgN := (Finset.mem_filter.mp hg).2
      have hgj : g - N < C.gates.length := by
        have := reach_subset_lt hout_lt (Finset.mem_filter.mp hg).1; omega
      rw [mem_reach_iff_gate hgN hgj]
      exact Or.inr ⟨a, ha, mem_reach_self (by omega)⟩
    have hbR : b ∈ R := by
      apply reach_trans (Finset.mem_filter.mp hg).1
      have hgN := (Finset.mem_filter.mp hg).2
      have hgj : g - N < C.gates.length := by
        have := reach_subset_lt hout_lt (Finset.mem_filter.mp hg).1; omega
      rw [mem_reach_iff_gate hgN hgj]
      exact Or.inr ⟨b, hb, mem_reach_self (by omega)⟩
    by_cases h1' : m = a
    · rw [h1'] at hmb
      obtain ⟨g2, hg2, hmg2⟩ := mem_reach_has_parent hmb hab
      rw [Finset.mem_filter] at hg2
      have hg2L : g2 ∈ L := Finset.mem_filter.mpr ⟨reach_trans hbR hg2.1, hg2.2⟩
      have hg2_ne : g2 ≠ g := by
        have := mem_reach_le hg2.1; omega
      exact Finset.disjoint_left.mp (hdisj hg2L hg hg2_ne) hmg2 ha
    · by_cases h2' : m = b
      · rw [h2'] at hma
        obtain ⟨g1, hg1, hmg1⟩ := mem_reach_has_parent hma (Ne.symm hab)
        rw [Finset.mem_filter] at hg1
        have hg1L : g1 ∈ L := Finset.mem_filter.mpr ⟨reach_trans haR hg1.1, hg1.2⟩
        have hg1_ne : g1 ≠ g := by
          have := mem_reach_le hg1.1; omega
        exact Finset.disjoint_left.mp (hdisj hg1L hg hg1_ne) hmg1 hb
      · obtain ⟨g1, hg1, hmg1⟩ := mem_reach_has_parent hma h1'
        obtain ⟨g2, hg2, hmg2⟩ := mem_reach_has_parent hmb h2'
        rw [Finset.mem_filter] at hg1 hg2
        have hg1L : g1 ∈ L := Finset.mem_filter.mpr ⟨reach_trans haR hg1.1, hg1.2⟩
        have hg2L : g2 ∈ L := Finset.mem_filter.mpr ⟨reach_trans hbR hg2.1, hg2.2⟩
        have heq : g1 = g2 := by
          by_contra hne
          exact Finset.disjoint_left.mp (hdisj hg1L hg2L hne) hmg1 hmg2
        subst heq
        have hg1_in : g1 ∈ S := Finset.mem_inter.mpr ⟨hg1.1, hg2.1⟩
        have hle_m : g1 ≤ m := Finset.le_max' S g1 hg1_in
        have hlt_m : m < g1 := refsOf_lt hmg1
        omega

  have hbuild : ∀ w, w ∈ R →
      ∃ T : FTree,
        T.readOnce ∧
        T.leaves = (reach C N w).filter (· < N) ∧
        T.notCount = (((reach C N w).filter (fun z => N ≤ z)).filter
          (fun g => isNotGate C N g = true)).card ∧
        ∀ x : List Bool, x.length = N → (C.wires x).getD w false = T.eval (fun i => x.getD i false) := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hwR
      by_cases hlt : w < N
      · refine ⟨.leaf w, trivial, ?_, ?_, ?_⟩
        · rw [reach]
          have hnot : ¬ (N ≤ w ∧ w - N < C.gates.length) := by omega
          simp [hnot, hlt, FTree.leaves, Finset.filter_singleton]
        · rw [reach]
          have hnot : ¬ (N ≤ w ∧ w - N < C.gates.length) := by omega
          simp [hnot, hlt, FTree.notCount, Finset.filter_singleton, show ¬ (N ≤ w) by omega]
        · intro x hx
          rw [circuit_wires_getD_input C x (by omega)]
          rfl
      · have hwN : N ≤ w := by omega
        have hw_lt : w < N + C.gates.length := reach_subset_lt hout_lt hwR
        have hwj : w - N < C.gates.length := by omega
        have hwL : w ∈ L := Finset.mem_filter.mpr ⟨hwR, hwN⟩
        have hhop := (hfan _ (List.getElem_mem hwj)).1
        have hlen := (hfan _ (List.getElem_mem hwj)).2
        have hcard_w := hcard_each w hwL
        simp only [isNotGate, hwj, ↓reduceDIte] at hcard_w
        have href_eq : refsOf C N w = (effInputs N (w - N) C.gates[w - N]).toFinset := by
          unfold refsOf refsList; simp [hwN, hwj]
        have hnodup := effInputs_nodup N (w - N) C.gates[w - N]
        have hlen_eff : (effInputs N (w - N) C.gates[w - N]).length = (refsOf C N w).card := by
          rw [href_eq, List.toFinset_card_of_nodup hnodup]
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hhop
        rcases hhop with hop_and | hop_or | hop_not
        · have hc2 : (refsOf C N w).card = 2 := by simpa [hop_and, isNotOp] using hcard_w
          rw [hc2] at hlen_eff
          rcases heff : effInputs N (w - N) C.gates[w - N] with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
          · simp [heff] at hlen_eff
          · simp [heff] at hlen_eff
          · have ha_ref : a ∈ refsOf C N w := by rw [href_eq, heff]; simp
            have hb_ref : b ∈ refsOf C N w := by rw [href_eq, heff]; simp
            have hab : a ≠ b := by rw [heff] at hnodup; simpa using hnodup
            have haR : a ∈ R := reach_trans hwR ((mem_reach_iff_gate hwN hwj).mpr (Or.inr ⟨a, ha_ref, mem_reach_self (by have := refsOf_lt ha_ref; omega)⟩))
            have hbR : b ∈ R := reach_trans hwR ((mem_reach_iff_gate hwN hwj).mpr (Or.inr ⟨b, hb_ref, mem_reach_self (by have := refsOf_lt hb_ref; omega)⟩))
            obtain ⟨Ta, hro_a, hlv_a, hnc_a, hev_a⟩ := ih a (refsOf_lt ha_ref) haR
            obtain ⟨Tb, hro_b, hlv_b, hnc_b, hev_b⟩ := ih b (refsOf_lt hb_ref) hbR
            have hdisj_ab : Disjoint (reach C N a) (reach C N b) := hreach_disj w hwL a ha_ref b hb_ref hab
            have hreach_w : reach C N w = insert w (reach C N a ∪ reach C N b) := by
              ext u
              rw [mem_reach_iff_gate hwN hwj, Finset.mem_insert, Finset.mem_union]
              have hrefs_set : ∀ v, v ∈ refsOf C N w ↔ v = a ∨ v = b := by
                intro v; rw [href_eq, heff]; simp
              simp only [hrefs_set]
              constructor
              · rintro (rfl | ⟨v, rfl | rfl, hu⟩)
                · exact Or.inl rfl
                · exact Or.inr (Or.inl hu)
                · exact Or.inr (Or.inr hu)
              · rintro (rfl | hu | hu)
                · exact Or.inl rfl
                · exact Or.inr ⟨a, Or.inl rfl, hu⟩
                · exact Or.inr ⟨b, Or.inr rfl, hu⟩
            refine ⟨.and Ta Tb, ⟨hro_a, hro_b, ?_⟩, ?_, ?_, ?_⟩
            · rw [hlv_a, hlv_b]
              exact Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _) hdisj_ab
            · simp only [FTree.leaves, hlv_a, hlv_b, hreach_w, Finset.filter_insert,
                show ¬ (w < N) by omega, ↓reduceIte, Finset.filter_union]
            · simp only [FTree.notCount, hnc_a, hnc_b, hreach_w]
              have hw_notin : w ∉ reach C N a ∪ reach C N b := by
                intro hw'
                rcases Finset.mem_union.mp hw' with hwa | hwb
                · have := mem_reach_le hwa; have := refsOf_lt ha_ref; omega
                · have := mem_reach_le hwb; have := refsOf_lt hb_ref; omega
              have hw_not_f : ¬ (isNotGate C N w = true) := by
                simp [isNotGate, hwj, hop_and, isNotOp]
              rw [Finset.filter_insert, if_pos hwN, Finset.filter_insert, if_neg hw_not_f]
              rw [Finset.filter_union, Finset.filter_union]
              rw [Finset.card_union_of_disjoint]
              exact Disjoint.mono
                (Finset.Subset.trans (Finset.filter_subset _ _) (Finset.filter_subset _ _))
                (Finset.Subset.trans (Finset.filter_subset _ _) (Finset.filter_subset _ _))
                hdisj_ab
            · intro x hx
              have hg := circuit_wires_getD_gate C x hwj
              have hweq : x.length + (w - N) = w := by omega
              rw [hweq] at hg
              rw [hg]
              have hge := gate_eval_and_two hop_and hlen (by rw [← href_eq]; exact hc2) heff
                (fun i => (C.wires x).getD i false)
              have hNw : N + (w - N) = w := by omega
              simp only [hNw] at hge
              rw [hge, hev_a x hx, hev_b x hx]; rfl
          · simp [heff] at hlen_eff
        ·
          have hc2 : (refsOf C N w).card = 2 := by simpa [hop_or, isNotOp] using hcard_w
          rw [hc2] at hlen_eff
          rcases heff : effInputs N (w - N) C.gates[w - N] with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
          · simp [heff] at hlen_eff
          · simp [heff] at hlen_eff
          · have ha_ref : a ∈ refsOf C N w := by rw [href_eq, heff]; simp
            have hb_ref : b ∈ refsOf C N w := by rw [href_eq, heff]; simp
            have hab : a ≠ b := by rw [heff] at hnodup; simpa using hnodup
            have haR : a ∈ R := reach_trans hwR ((mem_reach_iff_gate hwN hwj).mpr (Or.inr ⟨a, ha_ref, mem_reach_self (by have := refsOf_lt ha_ref; omega)⟩))
            have hbR : b ∈ R := reach_trans hwR ((mem_reach_iff_gate hwN hwj).mpr (Or.inr ⟨b, hb_ref, mem_reach_self (by have := refsOf_lt hb_ref; omega)⟩))
            obtain ⟨Ta, hro_a, hlv_a, hnc_a, hev_a⟩ := ih a (refsOf_lt ha_ref) haR
            obtain ⟨Tb, hro_b, hlv_b, hnc_b, hev_b⟩ := ih b (refsOf_lt hb_ref) hbR
            have hdisj_ab : Disjoint (reach C N a) (reach C N b) := hreach_disj w hwL a ha_ref b hb_ref hab
            have hreach_w : reach C N w = insert w (reach C N a ∪ reach C N b) := by
              ext u
              rw [mem_reach_iff_gate hwN hwj, Finset.mem_insert, Finset.mem_union]
              have hrefs_set : ∀ v, v ∈ refsOf C N w ↔ v = a ∨ v = b := by
                intro v; rw [href_eq, heff]; simp
              simp only [hrefs_set]
              constructor
              · rintro (rfl | ⟨v, rfl | rfl, hu⟩)
                · exact Or.inl rfl
                · exact Or.inr (Or.inl hu)
                · exact Or.inr (Or.inr hu)
              · rintro (rfl | hu | hu)
                · exact Or.inl rfl
                · exact Or.inr ⟨a, Or.inl rfl, hu⟩
                · exact Or.inr ⟨b, Or.inr rfl, hu⟩
            refine ⟨.or Ta Tb, ⟨hro_a, hro_b, ?_⟩, ?_, ?_, ?_⟩
            · rw [hlv_a, hlv_b]
              exact Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _) hdisj_ab
            · simp only [FTree.leaves, hlv_a, hlv_b, hreach_w, Finset.filter_insert,
                show ¬ (w < N) by omega, ↓reduceIte, Finset.filter_union]
            · simp only [FTree.notCount, hnc_a, hnc_b, hreach_w]
              have hw_not_f : ¬ (isNotGate C N w = true) := by
                simp [isNotGate, hwj, hop_or, isNotOp]
              rw [Finset.filter_insert, if_pos hwN, Finset.filter_insert, if_neg hw_not_f]
              rw [Finset.filter_union, Finset.filter_union]
              rw [Finset.card_union_of_disjoint]
              exact Disjoint.mono
                (Finset.Subset.trans (Finset.filter_subset _ _) (Finset.filter_subset _ _))
                (Finset.Subset.trans (Finset.filter_subset _ _) (Finset.filter_subset _ _))
                hdisj_ab
            · intro x hx
              have hg := circuit_wires_getD_gate C x hwj
              have hweq : x.length + (w - N) = w := by omega
              rw [hweq] at hg
              rw [hg]
              have hge := gate_eval_or_two hop_or hlen (by rw [← href_eq]; exact hc2) heff
                (fun i => (C.wires x).getD i false)
              have hNw : N + (w - N) = w := by omega
              simp only [hNw] at hge
              rw [hge, hev_a x hx, hev_b x hx]; rfl
          · simp [heff] at hlen_eff
        ·
          have hc1 : (refsOf C N w).card = 1 := by simpa [hop_not, isNotOp] using hcard_w
          rw [hc1] at hlen_eff
          rcases heff : effInputs N (w - N) C.gates[w - N] with _ | ⟨a, _ | _⟩
          · simp [heff] at hlen_eff
          · have ha_ref : a ∈ refsOf C N w := by rw [href_eq, heff]; simp
            have haR : a ∈ R := reach_trans hwR ((mem_reach_iff_gate hwN hwj).mpr (Or.inr ⟨a, ha_ref, mem_reach_self (by have := refsOf_lt ha_ref; omega)⟩))
            obtain ⟨Ta, hro_a, hlv_a, hnc_a, hev_a⟩ := ih a (refsOf_lt ha_ref) haR
            have hreach_w : reach C N w = insert w (reach C N a) := by
              ext u
              rw [mem_reach_iff_gate hwN hwj, Finset.mem_insert]
              have hrefs_set : ∀ v, v ∈ refsOf C N w ↔ v = a := by
                intro v; rw [href_eq, heff]; simp
              simp only [hrefs_set]
              constructor
              · rintro (rfl | ⟨v, rfl, hu⟩)
                · exact Or.inl rfl
                · exact Or.inr hu
              · rintro (rfl | hu)
                · exact Or.inl rfl
                · exact Or.inr ⟨a, rfl, hu⟩
            refine ⟨.not Ta, hro_a, ?_, ?_, ?_⟩
            · simp only [FTree.leaves, hlv_a, hreach_w, Finset.filter_insert,
                show ¬ (w < N) by omega, ↓reduceIte]
            · simp only [FTree.notCount, hnc_a, hreach_w]
              have hw_not_t : isNotGate C N w = true := by
                simp [isNotGate, hwj, hop_not, isNotOp]
              have hw_notin : w ∉ ((reach C N a).filter (fun z => N ≤ z)).filter
                  (fun g => isNotGate C N g = true) := by
                intro hmem
                have hwa : w ∈ reach C N a := (Finset.mem_filter.mp (Finset.mem_filter.mp hmem).1).1
                have := mem_reach_le hwa; have := refsOf_lt ha_ref; omega
              rw [Finset.filter_insert, if_pos hwN, Finset.filter_insert, if_pos hw_not_t,
                Finset.card_insert_of_notMem hw_notin]
            · intro x hx
              have hg := circuit_wires_getD_gate C x hwj
              have hweq : x.length + (w - N) = w := by omega
              rw [hweq] at hg
              rw [hg]
              have hge := gate_eval_not_one hop_not heff (fun i => (C.wires x).getD i false)
              have hNw : N + (w - N) = w := by omega
              simp only [hNw] at hge
              rw [hge, hev_a x hx]; rfl
          · simp [heff] at hlen_eff
  exact hbuild C.output (mem_reach_self hout_lt)

private def pairVec (nr : ℕ) (u v : ℕ) (w : ℕ) : Bool :=
  decide (w = u ∨ w = nr + v)

private def leftVec (u : ℕ) (w : ℕ) : Bool :=
  decide (w = u)

private def rightVec (nr : ℕ) (v : ℕ) (w : ℕ) : Bool :=
  decide (w = nr + v)

private lemma no_mono_tree_for_compl_id {k nr : ℕ} (hk : 3 ≤ k) (hnr : k ≤ nr)
    (T : FTree) (hro : T.readOnce) (h0 : T.notCount = 0)
    (hrep : ∀ u v : Fin k, T.eval (pairVec nr u.val v.val) = decide (u ≠ v)) : False := by
  induction T with
  | leaf w =>
    by_cases h1 : w < k
    · have := hrep ⟨w, h1⟩ ⟨w, h1⟩
      simp [FTree.eval, pairVec] at this
    · by_cases h2 : nr ≤ w ∧ w - nr < k
      · have := hrep ⟨w - nr, h2.2⟩ ⟨w - nr, h2.2⟩
        simp [FTree.eval, pairVec, show nr + (w - nr) = w by omega] at this
      · have := hrep ⟨0, by omega⟩ ⟨1, by omega⟩
        simp only [FTree.eval, pairVec, ne_eq, Fin.mk.injEq, zero_ne_one, not_false_eq_true,
          decide_true, decide_eq_true_eq] at this
        omega
  | not _ _ => simp [FTree.notCount] at h0
  | or l r ihl ihr =>
    rcases hro with ⟨hrol, hror, hdisj⟩
    simp only [FTree.notCount, Nat.add_eq_zero_iff] at h0
    have hdiag_l : ∀ u : Fin k, l.eval (pairVec nr u.val u.val) = false := by
      intro u
      have := hrep u u
      simp only [FTree.eval, ne_eq, not_true_eq_false, decide_false, Bool.or_eq_false_iff] at this
      exact this.1
    have hdiag_r : ∀ u : Fin k, r.eval (pairVec nr u.val u.val) = false := by
      intro u
      have := hrep u u
      simp only [FTree.eval, ne_eq, not_true_eq_false, decide_false, Bool.or_eq_false_iff] at this
      exact this.2
    have hleft_l : ∀ u : Fin k, l.eval (leftVec u.val) = false := by
      intro u
      have hm := FTree.eval_mono_of_notCount_zero h0.1 (v1 := leftVec u.val)
        (v2 := pairVec nr u.val u.val) (fun w _ => by
          by_cases hw : w = u.val <;> simp [leftVec, pairVec, hw])
      rw [hdiag_l u] at hm; exact bool_eq_false_of_le hm
    have hright_l : ∀ v : Fin k, l.eval (rightVec nr v.val) = false := by
      intro v
      have hm := FTree.eval_mono_of_notCount_zero h0.1 (v1 := rightVec nr v.val)
        (v2 := pairVec nr v.val v.val) (fun w _ => by
          by_cases hw : w = nr + v.val <;> simp [rightVec, pairVec, hw])
      rw [hdiag_l v] at hm; exact bool_eq_false_of_le hm
    have hleft_r : ∀ u : Fin k, r.eval (leftVec u.val) = false := by
      intro u
      have hm := FTree.eval_mono_of_notCount_zero h0.2 (v1 := leftVec u.val)
        (v2 := pairVec nr u.val u.val) (fun w _ => by
          by_cases hw : w = u.val <;> simp [leftVec, pairVec, hw])
      rw [hdiag_r u] at hm; exact bool_eq_false_of_le hm
    have hright_r : ∀ v : Fin k, r.eval (rightVec nr v.val) = false := by
      intro v
      have hm := FTree.eval_mono_of_notCount_zero h0.2 (v1 := rightVec nr v.val)
        (v2 := pairVec nr v.val v.val) (fun w _ => by
          by_cases hw : w = nr + v.val <;> simp [rightVec, pairVec, hw])
      rw [hdiag_r v] at hm; exact bool_eq_false_of_le hm
    have hl_needs : ∀ u v : Fin k, l.eval (pairVec nr u.val v.val) = true →
        u.val ∈ l.leaves ∧ nr + v.val ∈ l.leaves := by
      intro u v htrue
      constructor
      · by_contra hu
        have heq : l.eval (pairVec nr u.val v.val) = l.eval (rightVec nr v.val) :=
          FTree.eval_congr fun w hw => by
            have hne : w ≠ u.val := fun e => hu (e ▸ hw)
            simp [pairVec, rightVec, hne]
        rw [heq, hright_l v] at htrue; simp at htrue
      · by_contra hv
        have heq : l.eval (pairVec nr u.val v.val) = l.eval (leftVec u.val) :=
          FTree.eval_congr fun w hw => by
            have hne : w ≠ nr + v.val := fun e => hv (e ▸ hw)
            simp [pairVec, leftVec, hne]
        rw [heq, hleft_l u] at htrue; simp at htrue
    have hr_needs : ∀ u v : Fin k, r.eval (pairVec nr u.val v.val) = true →
        u.val ∈ r.leaves ∧ nr + v.val ∈ r.leaves := by
      intro u v htrue
      constructor
      · by_contra hu
        have heq : r.eval (pairVec nr u.val v.val) = r.eval (rightVec nr v.val) :=
          FTree.eval_congr fun w hw => by
            have hne : w ≠ u.val := fun e => hu (e ▸ hw)
            simp [pairVec, rightVec, hne]
        rw [heq, hright_r v] at htrue; simp at htrue
      · by_contra hv
        have heq : r.eval (pairVec nr u.val v.val) = r.eval (leftVec u.val) :=
          FTree.eval_congr fun w hw => by
            have hne : w ≠ nr + v.val := fun e => hv (e ▸ hw)
            simp [pairVec, leftVec, hne]
        rw [heq, hleft_r u] at htrue; simp at htrue
    by_cases hAl : ∃ u : Fin k, u.val ∈ l.leaves
    · by_cases hAr : ∃ u : Fin k, u.val ∈ r.leaves
      · rcases hAl with ⟨u1, hu1⟩
        rcases hAr with ⟨u2, hu2⟩
        have hne12 : u1 ≠ u2 := fun e => Finset.disjoint_left.mp hdisj hu1 (e ▸ hu2)
        have hexv : ∃ v : Fin k, v ≠ u1 ∧ v ≠ u2 := by
          by_cases h0' : (⟨0, by omega⟩ : Fin k) ≠ u1 ∧ (⟨0, by omega⟩ : Fin k) ≠ u2
          · exact ⟨⟨0, by omega⟩, h0'⟩
          · by_cases h1' : (⟨1, by omega⟩ : Fin k) ≠ u1 ∧ (⟨1, by omega⟩ : Fin k) ≠ u2
            · exact ⟨⟨1, by omega⟩, h1'⟩
            · refine ⟨⟨2, by omega⟩, ?_, ?_⟩
              · intro e
                have he : (2 : ℕ) = u1.val := congrArg Fin.val e
                have h0'' : u1.val = 0 ∨ u2.val = 0 := by
                  by_contra hc; push_neg at hc
                  exact h0' ⟨fun e' => hc.1 (congrArg Fin.val e').symm, fun e' => hc.2 (congrArg Fin.val e').symm⟩
                have h1'' : u1.val = 1 ∨ u2.val = 1 := by
                  by_contra hc; push_neg at hc
                  exact h1' ⟨fun e' => hc.1 (congrArg Fin.val e').symm, fun e' => hc.2 (congrArg Fin.val e').symm⟩
                omega
              · intro e
                have he : (2 : ℕ) = u2.val := congrArg Fin.val e
                have h0'' : u1.val = 0 ∨ u2.val = 0 := by
                  by_contra hc; push_neg at hc
                  exact h0' ⟨fun e' => hc.1 (congrArg Fin.val e').symm, fun e' => hc.2 (congrArg Fin.val e').symm⟩
                have h1'' : u1.val = 1 ∨ u2.val = 1 := by
                  by_contra hc; push_neg at hc
                  exact h1' ⟨fun e' => hc.1 (congrArg Fin.val e').symm, fun e' => hc.2 (congrArg Fin.val e').symm⟩
                omega
        rcases hexv with ⟨v, hv1, hv2⟩
        have h1v := hrep u1 v
        simp only [FTree.eval, hv1.symm, ne_eq, not_false_eq_true, decide_true,
          Bool.or_eq_true] at h1v
        have hv_l : nr + v.val ∈ l.leaves := by
          rcases h1v with h | h
          · exact (hl_needs u1 v h).2
          · exact absurd (hr_needs u1 v h).1 (Finset.disjoint_left.mp hdisj hu1)
        have h2v := hrep u2 v
        simp only [FTree.eval, hv2.symm, ne_eq, not_false_eq_true, decide_true,
          Bool.or_eq_true] at h2v
        have hv_r : nr + v.val ∈ r.leaves := by
          rcases h2v with h | h
          · exact absurd (hl_needs u2 v h).1 (Finset.disjoint_right.mp hdisj hu2)
          · exact (hr_needs u2 v h).2
        exact Finset.disjoint_left.mp hdisj hv_l hv_r
      · push_neg at hAr
        apply ihl hrol h0.1
        intro u v
        by_cases huv : u = v
        · subst huv; simp [hdiag_l u]
        · have h := hrep u v
          simp only [FTree.eval, huv, ne_eq, not_false_eq_true, decide_true,
            Bool.or_eq_true] at h ⊢
          rcases h with hl | hr
          · exact hl
          · exact absurd (hr_needs u v hr).1 (hAr u)
    · push_neg at hAl
      apply ihr hror h0.2
      intro u v
      by_cases huv : u = v
      · subst huv; simp [hdiag_r u]
      · have h := hrep u v
        simp only [FTree.eval, huv, ne_eq, not_false_eq_true, decide_true,
          Bool.or_eq_true] at h ⊢
        rcases h with hl | hr
        · exact absurd (hl_needs u v hl).1 (hAl u)
        · exact hr
  | and l r ihl ihr =>
    rcases hro with ⟨hrol, hror, hdisj⟩
    simp only [FTree.notCount, Nat.add_eq_zero_iff] at h0
    have hoff_l : ∀ u v : Fin k, u ≠ v → l.eval (pairVec nr u.val v.val) = true := by
      intro u v huv
      have := hrep u v
      simp only [FTree.eval, huv, ne_eq, not_false_eq_true, decide_true,
        Bool.and_eq_true] at this
      exact this.1
    have hoff_r : ∀ u v : Fin k, u ≠ v → r.eval (pairVec nr u.val v.val) = true := by
      intro u v huv
      have := hrep u v
      simp only [FTree.eval, huv, ne_eq, not_false_eq_true, decide_true,
        Bool.and_eq_true] at this
      exact this.2
    by_cases hl_ex : ∃ u1 : Fin k, l.eval (pairVec nr u1.val u1.val) = false
    · by_cases hr_ex : ∃ u2 : Fin k, r.eval (pairVec nr u2.val u2.val) = false
      · rcases hl_ex with ⟨u1, hu1⟩
        rcases hr_ex with ⟨u2, hu2⟩
        have hexv : ∃ v : Fin k, v ≠ u1 ∧ v ≠ u2 := by
          by_cases h0' : (⟨0, by omega⟩ : Fin k) ≠ u1 ∧ (⟨0, by omega⟩ : Fin k) ≠ u2
          · exact ⟨⟨0, by omega⟩, h0'⟩
          · by_cases h1' : (⟨1, by omega⟩ : Fin k) ≠ u1 ∧ (⟨1, by omega⟩ : Fin k) ≠ u2
            · exact ⟨⟨1, by omega⟩, h1'⟩
            · refine ⟨⟨2, by omega⟩, ?_, ?_⟩
              · intro e
                have he : (2 : ℕ) = u1.val := congrArg Fin.val e
                have h0'' : u1.val = 0 ∨ u2.val = 0 := by
                  by_contra hc; push_neg at hc
                  exact h0' ⟨fun e' => hc.1 (congrArg Fin.val e').symm, fun e' => hc.2 (congrArg Fin.val e').symm⟩
                have h1'' : u1.val = 1 ∨ u2.val = 1 := by
                  by_contra hc; push_neg at hc
                  exact h1' ⟨fun e' => hc.1 (congrArg Fin.val e').symm, fun e' => hc.2 (congrArg Fin.val e').symm⟩
                omega
              · intro e
                have he : (2 : ℕ) = u2.val := congrArg Fin.val e
                have h0'' : u1.val = 0 ∨ u2.val = 0 := by
                  by_contra hc; push_neg at hc
                  exact h0' ⟨fun e' => hc.1 (congrArg Fin.val e').symm, fun e' => hc.2 (congrArg Fin.val e').symm⟩
                have h1'' : u1.val = 1 ∨ u2.val = 1 := by
                  by_contra hc; push_neg at hc
                  exact h1' ⟨fun e' => hc.1 (congrArg Fin.val e').symm, fun e' => hc.2 (congrArg Fin.val e').symm⟩
                omega
        rcases hexv with ⟨v, hv1, hv2⟩
        have hvl : nr + v.val ∈ l.leaves := by
          by_contra hnotin
          have hm := FTree.eval_mono_of_notCount_zero h0.1 (v1 := pairVec nr u1.val v.val)
            (v2 := pairVec nr u1.val u1.val) (fun w hw => by
              have hne : w ≠ nr + v.val := fun e => hnotin (e ▸ hw)
              simp only [pairVec, hne, or_false]
              by_cases hw1 : w = u1.val <;> simp [hw1])
          rw [hoff_l u1 v hv1.symm, hu1] at hm
          exact Bool.noConfusion (bool_eq_false_of_le hm)
        have hvr : nr + v.val ∈ r.leaves := by
          by_contra hnotin
          have hm := FTree.eval_mono_of_notCount_zero h0.2 (v1 := pairVec nr u2.val v.val)
            (v2 := pairVec nr u2.val u2.val) (fun w hw => by
              have hne : w ≠ nr + v.val := fun e => hnotin (e ▸ hw)
              simp only [pairVec, hne, or_false]
              by_cases hw2 : w = u2.val <;> simp [hw2])
          rw [hoff_r u2 v hv2.symm, hu2] at hm
          exact Bool.noConfusion (bool_eq_false_of_le hm)
        exact Finset.disjoint_left.mp hdisj hvl hvr
      · push_neg at hr_ex
        apply ihl hrol h0.1
        intro u v
        by_cases huv : u = v
        · subst huv
          have := hrep u u
          have hr_t : r.eval (pairVec nr u.val u.val) = true := by
            cases h : r.eval (pairVec nr u.val u.val)
            · exact absurd h (hr_ex u)
            · rfl
          simp [FTree.eval, hr_t] at this
          simpa using this
        · simp [huv, hoff_l u v huv]
    · push_neg at hl_ex
      apply ihr hror h0.2
      intro u v
      by_cases huv : u = v
      · subst huv
        have := hrep u u
        have hl_t : l.eval (pairVec nr u.val u.val) = true := by
          cases h : l.eval (pairVec nr u.val u.val)
          · exact absurd h (hl_ex u)
          · rfl
        simp [FTree.eval, hl_t] at this
        simpa using this
      · simp [huv, hoff_r u v huv]

private lemma peel_or_leaf {T : FTree} (hro : T.readOnce) (h0 : T.notCount = 0)
    {w0 : ℕ} (hw0 : w0 ∈ T.leaves) (hcard : 2 ≤ T.leaves.card)
    (heval1 : T.eval (leftVec w0) = true) :
    ∃ T' : FTree, T'.readOnce ∧ T'.notCount = 0 ∧ T'.leaves = T.leaves.erase w0 ∧
      ∀ v : ℕ → Bool, T.eval v = (v w0 || T'.eval v) := by
  induction T with
  | leaf w =>
    simp [FTree.leaves] at hcard
  | not _ _ => simp [FTree.notCount] at h0
  | and l r _ _ =>
    rcases hro with ⟨_, _, hdisj⟩
    simp only [FTree.notCount, Nat.add_eq_zero_iff] at h0
    simp only [FTree.leaves, Finset.mem_union] at hw0
    simp only [FTree.eval, Bool.and_eq_true] at heval1
    rcases hw0 with hwl | hwr
    · have hnotin : w0 ∉ r.leaves := Finset.disjoint_left.mp hdisj hwl
      have heq : r.eval (leftVec w0) = r.eval (fun _ => false) :=
        FTree.eval_congr fun u hu => by
          simp [leftVec, show u ≠ w0 from fun e => hnotin (e ▸ hu)]
      rw [heq, FTree.eval_false_of_notCount_zero h0.2] at heval1
      simp at heval1
    · have hnotin : w0 ∉ l.leaves := Finset.disjoint_right.mp hdisj hwr
      have heq : l.eval (leftVec w0) = l.eval (fun _ => false) :=
        FTree.eval_congr fun u hu => by
          simp [leftVec, show u ≠ w0 from fun e => hnotin (e ▸ hu)]
      rw [heq, FTree.eval_false_of_notCount_zero h0.1] at heval1
      simp at heval1
  | or l r ihl ihr =>
    rcases hro with ⟨hrol, hror, hdisj⟩
    simp only [FTree.notCount, Nat.add_eq_zero_iff] at h0
    simp only [FTree.leaves, Finset.mem_union] at hw0
    simp only [FTree.eval, Bool.or_eq_true] at heval1
    rcases hw0 with hwl | hwr
    · have hnotin : w0 ∉ r.leaves := Finset.disjoint_left.mp hdisj hwl
      have hr0 : r.eval (leftVec w0) = false := by
        rw [FTree.eval_congr (v2 := fun _ => false) (fun u hu => by
          simp [leftVec, show u ≠ w0 from fun e => hnotin (e ▸ hu)])]
        exact FTree.eval_false_of_notCount_zero h0.2
      have hl1 : l.eval (leftVec w0) = true := by
        rcases heval1 with h | h
        · exact h
        · rw [hr0] at h; simp at h
      by_cases hlc : l.leaves.card = 1
      · have hl_eq : l.leaves = {w0} := Finset.card_eq_one.mp hlc |>.elim fun a ha => by
          rw [ha] at hwl; simp at hwl; subst hwl; exact ha
        have hl_eval : ∀ v, l.eval v = v w0 := by
          intro v
          cases hvw : v w0
          · rw [FTree.eval_congr (v2 := fun _ => false) (fun u hu => by
              rw [hl_eq] at hu; simp at hu; subst hu; exact hvw)]
            exact FTree.eval_false_of_notCount_zero h0.1
          · rw [FTree.eval_congr (v2 := leftVec w0) (fun u hu => by
              rw [hl_eq] at hu; simp at hu; subst hu; simp [leftVec, hvw])]
            exact hl1
        refine ⟨r, hror, h0.2, ?_, fun v => by simp [FTree.eval, hl_eval]⟩
        simp only [FTree.leaves, hl_eq]
        ext u; simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_singleton]
        constructor
        · intro hu; exact ⟨fun e => hnotin (e ▸ hu), Or.inr hu⟩
        · rintro ⟨hne, rfl | hu⟩
          · exact absurd rfl hne
          · exact hu
      · have hl_pos : 1 ≤ l.leaves.card := Finset.card_pos.mpr l.leaves_nonempty
        obtain ⟨l', hrol', h0l', hlv', hev'⟩ := ihl hrol h0.1 hwl (by omega) hl1
        refine ⟨.or l' r, ⟨hrol', hror, ?_⟩, by simp [FTree.notCount, h0l', h0.2], ?_, ?_⟩
        · rw [hlv']; exact Disjoint.mono_left (Finset.erase_subset _ _) hdisj
        · simp only [FTree.leaves, hlv']
          ext u; simp only [Finset.mem_union, Finset.mem_erase]
          constructor
          · rintro (⟨hne, hu⟩ | hu)
            · exact ⟨hne, Or.inl hu⟩
            · exact ⟨fun e => hnotin (e ▸ hu), Or.inr hu⟩
          · rintro ⟨hne, hu | hu⟩
            · exact Or.inl ⟨hne, hu⟩
            · exact Or.inr hu
        · intro v; simp [FTree.eval, hev', Bool.or_assoc]
    · have hnotin : w0 ∉ l.leaves := Finset.disjoint_right.mp hdisj hwr
      have hl0 : l.eval (leftVec w0) = false := by
        rw [FTree.eval_congr (v2 := fun _ => false) (fun u hu => by
          simp [leftVec, show u ≠ w0 from fun e => hnotin (e ▸ hu)])]
        exact FTree.eval_false_of_notCount_zero h0.1
      have hr1 : r.eval (leftVec w0) = true := by
        rcases heval1 with h | h
        · rw [hl0] at h; simp at h
        · exact h
      by_cases hrc : r.leaves.card = 1
      · have hr_eq : r.leaves = {w0} := Finset.card_eq_one.mp hrc |>.elim fun a ha => by
          rw [ha] at hwr; simp at hwr; subst hwr; exact ha
        have hr_eval : ∀ v, r.eval v = v w0 := by
          intro v
          cases hvw : v w0
          · rw [FTree.eval_congr (v2 := fun _ => false) (fun u hu => by
              rw [hr_eq] at hu; simp at hu; subst hu; exact hvw)]
            exact FTree.eval_false_of_notCount_zero h0.2
          · rw [FTree.eval_congr (v2 := leftVec w0) (fun u hu => by
              rw [hr_eq] at hu; simp at hu; subst hu; simp [leftVec, hvw])]
            exact hr1
        refine ⟨l, hrol, h0.1, ?_, fun v => by simp [FTree.eval, hr_eval, Bool.or_comm]⟩
        simp only [FTree.leaves, hr_eq]
        ext u; simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_singleton]
        constructor
        · intro hu; exact ⟨fun e => hnotin (e ▸ hu), Or.inl hu⟩
        · rintro ⟨hne, hu | rfl⟩
          · exact hu
          · exact absurd rfl hne
      · have hr_pos : 1 ≤ r.leaves.card := Finset.card_pos.mpr r.leaves_nonempty
        obtain ⟨r', hror', h0r', hlv', hev'⟩ := ihr hror h0.2 hwr (by omega) hr1
        refine ⟨.or l r', ⟨hrol, hror', ?_⟩, by simp [FTree.notCount, h0.1, h0r'], ?_, ?_⟩
        · rw [hlv']; exact Disjoint.mono_right (Finset.erase_subset _ _) hdisj
        · simp only [FTree.leaves, hlv']
          ext u; simp only [Finset.mem_union, Finset.mem_erase]
          constructor
          · rintro (hu | ⟨hne, hu⟩)
            · exact ⟨fun e => hnotin (e ▸ hu), Or.inl hu⟩
            · exact ⟨hne, Or.inr hu⟩
          · rintro ⟨hne, hu | hu⟩
            · exact Or.inl hu
            · exact Or.inr ⟨hne, hu⟩
        · intro v; simp only [FTree.eval, hev']
          cases v w0 <;> cases l.eval v <;> cases r'.eval v <;> rfl

private def matchEval (k nr : ℕ) (σ : Fin k → Fin k) (v : ℕ → Bool) : Bool :=
  decide (∃ u : Fin k, (v u.val = true ∧ v (nr + u.val) = true) ∨
    (u ≠ σ u ∧ ((v u.val = true ∧ v (σ u).val = true) ∨
                (v (nr + u.val) = true ∧ v (nr + (σ u).val) = true))))

private def matchEvalOn (k nr : ℕ) (U : Finset (Fin k)) (σ : Fin k → Fin k) (v : ℕ → Bool) : Bool :=
  decide (∃ u ∈ U, (v u.val = true ∧ v (nr + u.val) = true) ∨
    (u ≠ σ u ∧ ((v u.val = true ∧ v (σ u).val = true) ∨
                (v (nr + u.val) = true ∧ v (nr + (σ u).val) = true))))

private lemma mono_tree_card_one {T : FTree} (hro : T.readOnce) (h0 : T.notCount = 0)
    {a : ℕ} (hlv : T.leaves = {a}) (v : ℕ → Bool) : T.eval v = v a := by
  cases T with
  | leaf w =>
    simp only [FTree.leaves, Finset.singleton_inj] at hlv
    subst hlv; rfl
  | not _ => simp [FTree.notCount] at h0
  | and l r =>
    rcases hro with ⟨_, _, hdisj⟩
    have hc := Finset.card_union_of_disjoint hdisj
    rw [show l.leaves ∪ r.leaves = {a} from hlv] at hc
    have h1 : 1 ≤ l.leaves.card := Finset.card_pos.mpr l.leaves_nonempty
    have h2 : 1 ≤ r.leaves.card := Finset.card_pos.mpr r.leaves_nonempty
    simp at hc; omega
  | or l r =>
    rcases hro with ⟨_, _, hdisj⟩
    have hc := Finset.card_union_of_disjoint hdisj
    rw [show l.leaves ∪ r.leaves = {a} from hlv] at hc
    have h1 : 1 ≤ l.leaves.card := Finset.card_pos.mpr l.leaves_nonempty
    have h2 : 1 ≤ r.leaves.card := Finset.card_pos.mpr r.leaves_nonempty
    simp at hc; omega

private lemma mono_tree_card_two_or {T : FTree} (hro : T.readOnce) (h0 : T.notCount = 0)
    {a b : ℕ} (hab : a ≠ b) (hlv : T.leaves = {a, b})
    (ha : T.eval (leftVec a) = true) (v : ℕ → Bool) : T.eval v = (v a || v b) := by
  cases T with
  | leaf w =>
    have hc : ({w} : Finset ℕ).card = ({a, b} : Finset ℕ).card := congrArg Finset.card hlv
    rw [Finset.card_singleton, Finset.card_pair hab] at hc; omega
  | not _ => simp [FTree.notCount] at h0
  | and l r =>
    rcases hro with ⟨hrol, hror, hdisj⟩
    simp only [FTree.notCount, Nat.add_eq_zero_iff] at h0
    have hc := Finset.card_union_of_disjoint hdisj
    rw [show l.leaves ∪ r.leaves = {a, b} from hlv, Finset.card_pair hab] at hc
    have h1 : 1 ≤ l.leaves.card := Finset.card_pos.mpr l.leaves_nonempty
    have h2 : 1 ≤ r.leaves.card := Finset.card_pos.mpr r.leaves_nonempty
    have hlc : l.leaves.card = 1 := by omega
    have hrc : r.leaves.card = 1 := by omega
    rcases Finset.card_eq_one.mp hlc with ⟨x, hx⟩
    rcases Finset.card_eq_one.mp hrc with ⟨y, hy⟩
    have hxy : x ≠ y := fun e => Finset.disjoint_left.mp hdisj (hx ▸ Finset.mem_singleton_self x)
      (hy ▸ e ▸ Finset.mem_singleton_self x)
    have hset : ({x, y} : Finset ℕ) = {a, b} := by
      have : l.leaves ∪ r.leaves = {a, b} := hlv
      rw [hx, hy] at this
      simpa [Finset.union_singleton, Finset.pair_comm] using this
    simp only [FTree.eval, mono_tree_card_one hrol h0.1 hx, mono_tree_card_one hror h0.2 hy,
      leftVec, Bool.and_eq_true, decide_eq_true_eq] at ha
    omega
  | or l r =>
    rcases hro with ⟨hrol, hror, hdisj⟩
    simp only [FTree.notCount, Nat.add_eq_zero_iff] at h0
    have hc := Finset.card_union_of_disjoint hdisj
    rw [show l.leaves ∪ r.leaves = {a, b} from hlv, Finset.card_pair hab] at hc
    have h1 : 1 ≤ l.leaves.card := Finset.card_pos.mpr l.leaves_nonempty
    have h2 : 1 ≤ r.leaves.card := Finset.card_pos.mpr r.leaves_nonempty
    have hlc : l.leaves.card = 1 := by omega
    have hrc : r.leaves.card = 1 := by omega
    rcases Finset.card_eq_one.mp hlc with ⟨x, hx⟩
    rcases Finset.card_eq_one.mp hrc with ⟨y, hy⟩
    have hxy : x ≠ y := fun e => Finset.disjoint_left.mp hdisj (hx ▸ Finset.mem_singleton_self x)
      (hy ▸ e ▸ Finset.mem_singleton_self x)
    have hmem_x : x ∈ ({a, b} : Finset ℕ) := by
      rw [← hlv]; exact Finset.mem_union_left _ (hx ▸ Finset.mem_singleton_self x)
    have hmem_y : y ∈ ({a, b} : Finset ℕ) := by
      rw [← hlv]; exact Finset.mem_union_right _ (hy ▸ Finset.mem_singleton_self y)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem_x hmem_y
    simp only [FTree.eval, mono_tree_card_one hrol h0.1 hx, mono_tree_card_one hror h0.2 hy]
    rcases hmem_x with rfl | rfl <;> rcases hmem_y with rfl | rfl
    · exact absurd rfl hxy
    · rfl
    · exact Bool.or_comm _ _
    · exact absurd rfl hxy

private lemma mono_tree_id_matching {k nr : ℕ} (hnr : k ≤ nr)
    (T : FTree) (hro : T.readOnce) (h0 : T.notCount = 0)
    (U : Finset (Fin k)) (hU : U.Nonempty)
    (hlv : T.leaves = U.image (fun u : Fin k => u.val) ∪ U.image (fun u : Fin k => nr + u.val))
    (hrep : ∀ u ∈ U, ∀ v ∈ U, T.eval (pairVec nr u.val v.val) = decide (u = v))
    (hleft : ∀ u ∈ U, T.eval (leftVec u.val) = false)
    (hright : ∀ u ∈ U, T.eval (rightVec nr u.val) = false) :
    ∃ σ : Fin k → Fin k,
      (∀ u, σ (σ u) = u) ∧ (∀ u ∈ U, σ u ∈ U) ∧
      ∀ v : ℕ → Bool, T.eval v = matchEvalOn k nr U σ v := by
  induction T generalizing U with
  | leaf w =>
    rcases hU with ⟨u, hu⟩
    have h1 : u.val ∈ (FTree.leaf w).leaves := by
      rw [hlv]; exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hu)
    have h2 : nr + u.val ∈ (FTree.leaf w).leaves := by
      rw [hlv]; exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hu)
    simp [FTree.leaves] at h1 h2; omega
  | not _ _ => simp [FTree.notCount] at h0
  | or l r ihl ihr =>
    rcases hro with ⟨hrol, hror, hdisj⟩
    simp only [FTree.notCount, Nat.add_eq_zero_iff] at h0
    have hl_left : ∀ u ∈ U, l.eval (leftVec u.val) = false := by
      intro u hu; have := hleft u hu; simp [FTree.eval] at this; exact this.1
    have hl_right : ∀ u ∈ U, l.eval (rightVec nr u.val) = false := by
      intro u hu; have := hright u hu; simp [FTree.eval] at this; exact this.1
    have hr_left : ∀ u ∈ U, r.eval (leftVec u.val) = false := by
      intro u hu; have := hleft u hu; simp [FTree.eval] at this; exact this.2
    have hr_right : ∀ u ∈ U, r.eval (rightVec nr u.val) = false := by
      intro u hu; have := hright u hu; simp [FTree.eval] at this; exact this.2
    have hsame : ∀ u ∈ U, (u.val ∈ l.leaves ↔ nr + u.val ∈ l.leaves) ∧
        (u.val ∈ r.leaves ↔ nr + u.val ∈ r.leaves) := by
      intro u hu
      have hdiag := hrep u hu u hu
      simp only [FTree.eval, decide_true, Bool.or_eq_true] at hdiag
      have h1 : u.val ∈ l.leaves ∪ r.leaves := by
        rw [show l.leaves ∪ r.leaves = _ from hlv]
        exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hu)
      have h2 : nr + u.val ∈ l.leaves ∪ r.leaves := by
        rw [show l.leaves ∪ r.leaves = _ from hlv]
        exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hu)
      rcases hdiag with hl_t | hr_t
      · have hxl : u.val ∈ l.leaves := by
          by_contra hnotin
          have heq : l.eval (pairVec nr u.val u.val) = l.eval (rightVec nr u.val) :=
            FTree.eval_congr fun w hw => by
              simp [pairVec, rightVec, show w ≠ u.val from fun e => hnotin (e ▸ hw)]
          rw [heq, hl_right u hu] at hl_t; simp at hl_t
        have hyl : nr + u.val ∈ l.leaves := by
          by_contra hnotin
          have heq : l.eval (pairVec nr u.val u.val) = l.eval (leftVec u.val) :=
            FTree.eval_congr fun w hw => by
              simp [pairVec, leftVec, show w ≠ nr + u.val from fun e => hnotin (e ▸ hw)]
          rw [heq, hl_left u hu] at hl_t; simp at hl_t
        have hxr : u.val ∉ r.leaves := Finset.disjoint_left.mp hdisj hxl
        have hyr : nr + u.val ∉ r.leaves := Finset.disjoint_left.mp hdisj hyl
        simp [hxl, hyl, hxr, hyr]
      · have hxr : u.val ∈ r.leaves := by
          by_contra hnotin
          have heq : r.eval (pairVec nr u.val u.val) = r.eval (rightVec nr u.val) :=
            FTree.eval_congr fun w hw => by
              simp [pairVec, rightVec, show w ≠ u.val from fun e => hnotin (e ▸ hw)]
          rw [heq, hr_right u hu] at hr_t; simp at hr_t
        have hyr : nr + u.val ∈ r.leaves := by
          by_contra hnotin
          have heq : r.eval (pairVec nr u.val u.val) = r.eval (leftVec u.val) :=
            FTree.eval_congr fun w hw => by
              simp [pairVec, leftVec, show w ≠ nr + u.val from fun e => hnotin (e ▸ hw)]
          rw [heq, hr_left u hu] at hr_t; simp at hr_t
        have hxl : u.val ∉ l.leaves := Finset.disjoint_right.mp hdisj hxr
        have hyl : nr + u.val ∉ l.leaves := Finset.disjoint_right.mp hdisj hyr
        simp [hxl, hyl, hxr, hyr]
    set U1 := U.filter (fun u => u.val ∈ l.leaves)
    set U2 := U.filter (fun u => u.val ∈ r.leaves)
    have hlv1 : l.leaves = U1.image (fun u : Fin k => u.val) ∪ U1.image (fun u : Fin k => nr + u.val) := by
      ext w
      simp only [Finset.mem_union, Finset.mem_image, U1, Finset.mem_filter]
      constructor
      · intro hw
        have hwT : w ∈ l.leaves ∪ r.leaves := Finset.mem_union_left _ hw
        rw [show l.leaves ∪ r.leaves = _ from hlv] at hwT
        simp only [Finset.mem_union, Finset.mem_image] at hwT
        rcases hwT with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
        · exact Or.inl ⟨u, ⟨hu, hw⟩, rfl⟩
        · exact Or.inr ⟨u, ⟨hu, (hsame u hu).1.mpr hw⟩, rfl⟩
      · rintro (⟨u, ⟨_, hw⟩, rfl⟩ | ⟨u, ⟨hu, hw⟩, rfl⟩)
        · exact hw
        · exact (hsame u hu).1.mp hw
    have hlv2 : r.leaves = U2.image (fun u : Fin k => u.val) ∪ U2.image (fun u : Fin k => nr + u.val) := by
      ext w
      simp only [Finset.mem_union, Finset.mem_image, U2, Finset.mem_filter]
      constructor
      · intro hw
        have hwT : w ∈ l.leaves ∪ r.leaves := Finset.mem_union_right _ hw
        rw [show l.leaves ∪ r.leaves = _ from hlv] at hwT
        simp only [Finset.mem_union, Finset.mem_image] at hwT
        rcases hwT with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
        · exact Or.inl ⟨u, ⟨hu, hw⟩, rfl⟩
        · exact Or.inr ⟨u, ⟨hu, (hsame u hu).2.mpr hw⟩, rfl⟩
      · rintro (⟨u, ⟨_, hw⟩, rfl⟩ | ⟨u, ⟨hu, hw⟩, rfl⟩)
        · exact hw
        · exact (hsame u hu).2.mp hw
    have hU1_ne : U1.Nonempty := by
      rcases l.leaves_nonempty with ⟨w, hw⟩
      rw [hlv1] at hw
      simp only [Finset.mem_union, Finset.mem_image] at hw
      rcases hw with ⟨u, hu, _⟩ | ⟨u, hu, _⟩ <;> exact ⟨u, hu⟩
    have hU2_ne : U2.Nonempty := by
      rcases r.leaves_nonempty with ⟨w, hw⟩
      rw [hlv2] at hw
      simp only [Finset.mem_union, Finset.mem_image] at hw
      rcases hw with ⟨u, hu, _⟩ | ⟨u, hu, _⟩ <;> exact ⟨u, hu⟩
    have hrep1 : ∀ u ∈ U1, ∀ v ∈ U1, l.eval (pairVec nr u.val v.val) = decide (u = v) := by
      intro u hu v hv
      have huU : u ∈ U := (Finset.mem_filter.mp hu).1
      have hvU : v ∈ U := (Finset.mem_filter.mp hv).1
      have hr_zero : r.eval (pairVec nr u.val v.val) = false := by
        rw [FTree.eval_congr (v2 := fun _ => false) (fun w hw => by
          have hnotl : w ∉ l.leaves := Finset.disjoint_right.mp hdisj hw
          have h1 : w ≠ u.val := fun e => hnotl (e ▸ (Finset.mem_filter.mp hu).2)
          have h2 : w ≠ nr + v.val := fun e => hnotl (e ▸ (hsame v hvU).1.mp (Finset.mem_filter.mp hv).2)
          simp [pairVec, h1, h2])]
        exact FTree.eval_false_of_notCount_zero h0.2
      have := hrep u huU v hvU
      simpa [FTree.eval, hr_zero] using this
    have hrep2 : ∀ u ∈ U2, ∀ v ∈ U2, r.eval (pairVec nr u.val v.val) = decide (u = v) := by
      intro u hu v hv
      have huU : u ∈ U := (Finset.mem_filter.mp hu).1
      have hvU : v ∈ U := (Finset.mem_filter.mp hv).1
      have hl_zero : l.eval (pairVec nr u.val v.val) = false := by
        rw [FTree.eval_congr (v2 := fun _ => false) (fun w hw => by
          have hnotr : w ∉ r.leaves := Finset.disjoint_left.mp hdisj hw
          have h1 : w ≠ u.val := fun e => hnotr (e ▸ (Finset.mem_filter.mp hu).2)
          have h2 : w ≠ nr + v.val := fun e => hnotr (e ▸ (hsame v hvU).2.mp (Finset.mem_filter.mp hv).2)
          simp [pairVec, h1, h2])]
        exact FTree.eval_false_of_notCount_zero h0.1
      have := hrep u huU v hvU
      simpa [FTree.eval, hl_zero] using this
    obtain ⟨σ1, hinv1, hcl1, hev1⟩ := ihl hrol h0.1 U1 hU1_ne hlv1 hrep1
      (fun u hu => hl_left u (Finset.mem_filter.mp hu).1)
      (fun u hu => hl_right u (Finset.mem_filter.mp hu).1)
    obtain ⟨σ2, hinv2, hcl2, hev2⟩ := ihr hror h0.2 U2 hU2_ne hlv2 hrep2
      (fun u hu => hr_left u (Finset.mem_filter.mp hu).1)
      (fun u hu => hr_right u (Finset.mem_filter.mp hu).1)
    have hUdisj : Disjoint U1 U2 := by
      rw [Finset.disjoint_left]
      intro u hu1 hu2
      exact Finset.disjoint_left.mp hdisj (Finset.mem_filter.mp hu1).2 (Finset.mem_filter.mp hu2).2
    have hUunion : U = U1 ∪ U2 := by
      ext u
      simp only [Finset.mem_union, U1, U2, Finset.mem_filter]
      constructor
      · intro hu
        have hu_mem : u.val ∈ l.leaves ∪ r.leaves := by
          rw [show l.leaves ∪ r.leaves = _ from hlv]
          exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hu)
        rcases Finset.mem_union.mp hu_mem with h1 | h2
        · exact Or.inl ⟨hu, h1⟩
        · exact Or.inr ⟨hu, h2⟩
      · rintro (⟨hu, _⟩ | ⟨hu, _⟩) <;> exact hu
    let σ : Fin k → Fin k := fun u => if u ∈ U1 then σ1 u else if u ∈ U2 then σ2 u else u
    refine ⟨σ, ?_, ?_, ?_⟩
    · intro u
      by_cases h1 : u ∈ U1
      · have hs1 : σ1 u ∈ U1 := hcl1 u h1
        simp [σ, h1, hs1, hinv1 u]
      · by_cases h2 : u ∈ U2
        · have hs2 : σ2 u ∈ U2 := hcl2 u h2
          have hs2n : σ2 u ∉ U1 := Finset.disjoint_right.mp hUdisj hs2
          simp [σ, h1, h2, hs2, hs2n, hinv2 u]
        · simp [σ, h1, h2]
    · intro u hu
      rw [hUunion] at hu ⊢
      rcases Finset.mem_union.mp hu with h1 | h2
      · simp only [σ, h1, ↓reduceIte]; exact Finset.mem_union_left _ (hcl1 u h1)
      · have h1 : u ∉ U1 := Finset.disjoint_right.mp hUdisj h2
        simp only [σ, h1, h2, ↓reduceIte]; exact Finset.mem_union_right _ (hcl2 u h2)
    · intro v
      simp only [FTree.eval, hev1 v, hev2 v, matchEvalOn]
      rw [Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      constructor
      · rintro (⟨u, hu, h⟩ | ⟨u, hu, h⟩)
        · refine ⟨u, hUunion ▸ Finset.mem_union_left _ hu, ?_⟩
          simpa [σ, hu] using h
        · have h1 : u ∉ U1 := Finset.disjoint_right.mp hUdisj hu
          refine ⟨u, hUunion ▸ Finset.mem_union_right _ hu, ?_⟩
          simpa [σ, h1, hu] using h
      · rintro ⟨u, hu, h⟩
        rw [hUunion] at hu
        rcases Finset.mem_union.mp hu with h1 | h2
        · left; refine ⟨u, h1, ?_⟩; simpa [σ, h1] using h
        · have h1 : u ∉ U1 := Finset.disjoint_right.mp hUdisj h2
          right; refine ⟨u, h2, ?_⟩; simpa [σ, h1, h2] using h
  | and l r _ _ =>
    rcases hro with ⟨hrol, hror, hdisj⟩
    simp only [FTree.notCount, Nat.add_eq_zero_iff] at h0

    have hopp : ∀ u ∈ U, (u.val ∈ l.leaves ∧ nr + u.val ∈ r.leaves) ∨
        (u.val ∈ r.leaves ∧ nr + u.val ∈ l.leaves) := by
      intro u hu
      have hdiag := hrep u hu u hu
      simp only [FTree.eval, decide_true, Bool.and_eq_true] at hdiag
      have h1 : u.val ∈ l.leaves ∪ r.leaves := by
        rw [show l.leaves ∪ r.leaves = _ from hlv]
        exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hu)
      have h2 : nr + u.val ∈ l.leaves ∪ r.leaves := by
        rw [show l.leaves ∪ r.leaves = _ from hlv]
        exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hu)
      have hnot_both_l : ¬ (u.val ∈ l.leaves ∧ nr + u.val ∈ l.leaves) := by
        rintro ⟨hx, hy⟩
        have hx' : u.val ∉ r.leaves := Finset.disjoint_left.mp hdisj hx
        have hy' : nr + u.val ∉ r.leaves := Finset.disjoint_left.mp hdisj hy
        have hr0 : r.eval (pairVec nr u.val u.val) = false := by
          rw [FTree.eval_congr (v2 := fun _ => false) (fun w hw => by
            simp [pairVec, show w ≠ u.val from fun e => hx' (e ▸ hw),
              show w ≠ nr + u.val from fun e => hy' (e ▸ hw)])]
          exact FTree.eval_false_of_notCount_zero h0.2
        rw [hr0] at hdiag; simp at hdiag
      have hnot_both_r : ¬ (u.val ∈ r.leaves ∧ nr + u.val ∈ r.leaves) := by
        rintro ⟨hx, hy⟩
        have hx' : u.val ∉ l.leaves := Finset.disjoint_right.mp hdisj hx
        have hy' : nr + u.val ∉ l.leaves := Finset.disjoint_right.mp hdisj hy
        have hl0 : l.eval (pairVec nr u.val u.val) = false := by
          rw [FTree.eval_congr (v2 := fun _ => false) (fun w hw => by
            simp [pairVec, show w ≠ u.val from fun e => hx' (e ▸ hw),
              show w ≠ nr + u.val from fun e => hy' (e ▸ hw)])]
          exact FTree.eval_false_of_notCount_zero h0.1
        rw [hl0] at hdiag; simp at hdiag
      rcases Finset.mem_union.mp h1 with hx | hx <;> rcases Finset.mem_union.mp h2 with hy | hy
      · exact absurd ⟨hx, hy⟩ hnot_both_l
      · exact Or.inl ⟨hx, hy⟩
      · exact Or.inr ⟨hx, hy⟩
      · exact absurd ⟨hx, hy⟩ hnot_both_r

    have huniq_l : ∀ u1 ∈ U, ∀ u2 ∈ U, u1.val ∈ l.leaves → u2.val ∈ l.leaves → u1 = u2 := by
      intro u1 hu1 u2 hu2 h1 h2
      by_contra hne
      have hy1 : nr + u1.val ∈ r.leaves := by
        rcases hopp u1 hu1 with ⟨_, h⟩ | ⟨h, _⟩
        · exact h
        · exact absurd h (Finset.disjoint_left.mp hdisj h1)
      have hy2 : nr + u2.val ∈ r.leaves := by
        rcases hopp u2 hu2 with ⟨_, h⟩ | ⟨h, _⟩
        · exact h
        · exact absurd h (Finset.disjoint_left.mp hdisj h2)
      have hd1 := hrep u1 hu1 u1 hu1
      have hd2 := hrep u2 hu2 u2 hu2
      simp only [FTree.eval, decide_true, Bool.and_eq_true] at hd1 hd2
      have hl_1 : l.eval (pairVec nr u1.val u2.val) = true := by
        have hm := FTree.eval_mono_of_notCount_zero h0.1 (v1 := pairVec nr u1.val u1.val)
          (v2 := pairVec nr u1.val u2.val) (fun w hw => by
            have hny1 : w ≠ nr + u1.val := fun e => Finset.disjoint_left.mp hdisj hw (e ▸ hy1)
            simp only [pairVec, hny1, or_false]
            by_cases hwu : w = u1.val <;> simp [hwu])
        rw [hd1.1] at hm; exact bool_eq_true_of_le hm
      have hr_2 : r.eval (pairVec nr u1.val u2.val) = true := by
        have hm := FTree.eval_mono_of_notCount_zero h0.2 (v1 := pairVec nr u2.val u2.val)
          (v2 := pairVec nr u1.val u2.val) (fun w hw => by
            have hnx2 : w ≠ u2.val := fun e => Finset.disjoint_right.mp hdisj hw (e ▸ h2)
            simp only [pairVec, hnx2, false_or]
            by_cases hwy : w = nr + u2.val <;> simp [hwy])
        rw [hd2.2] at hm; exact bool_eq_true_of_le hm
      have hoff := hrep u1 hu1 u2 hu2
      simp [FTree.eval, hl_1, hr_2, hne] at hoff
    have huniq_r : ∀ u1 ∈ U, ∀ u2 ∈ U, u1.val ∈ r.leaves → u2.val ∈ r.leaves → u1 = u2 := by
      intro u1 hu1 u2 hu2 h1 h2
      by_contra hne
      have hy1 : nr + u1.val ∈ l.leaves := by
        rcases hopp u1 hu1 with ⟨h, _⟩ | ⟨_, h⟩
        · exact absurd h (Finset.disjoint_right.mp hdisj h1)
        · exact h
      have hy2 : nr + u2.val ∈ l.leaves := by
        rcases hopp u2 hu2 with ⟨h, _⟩ | ⟨_, h⟩
        · exact absurd h (Finset.disjoint_right.mp hdisj h2)
        · exact h
      have hd1 := hrep u1 hu1 u1 hu1
      have hd2 := hrep u2 hu2 u2 hu2
      simp only [FTree.eval, decide_true, Bool.and_eq_true] at hd1 hd2
      have hr_1 : r.eval (pairVec nr u1.val u2.val) = true := by
        have hm := FTree.eval_mono_of_notCount_zero h0.2 (v1 := pairVec nr u1.val u1.val)
          (v2 := pairVec nr u1.val u2.val) (fun w hw => by
            have hny1 : w ≠ nr + u1.val := fun e => Finset.disjoint_right.mp hdisj hw (e ▸ hy1)
            simp only [pairVec, hny1, or_false]
            by_cases hwu : w = u1.val <;> simp [hwu])
        rw [hd1.2] at hm; exact bool_eq_true_of_le hm
      have hl_2 : l.eval (pairVec nr u1.val u2.val) = true := by
        have hm := FTree.eval_mono_of_notCount_zero h0.1 (v1 := pairVec nr u2.val u2.val)
          (v2 := pairVec nr u1.val u2.val) (fun w hw => by
            have hnx2 : w ≠ u2.val := fun e => Finset.disjoint_left.mp hdisj hw (e ▸ h2)
            simp only [pairVec, hnx2, false_or]
            by_cases hwy : w = nr + u2.val <;> simp [hwy])
        rw [hd2.1] at hm; exact bool_eq_true_of_le hm
      have hoff := hrep u1 hu1 u2 hu2
      simp [FTree.eval, hl_2, hr_1, hne] at hoff

    rcases hU with ⟨u0, hu0⟩
    by_cases hother : ∃ u1 ∈ U, u1 ≠ u0
    · rcases hother with ⟨u1, hu1, hne⟩
      have hU_eq : U = {u0, u1} := by
        ext u
        simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro hu
          rcases hopp u0 hu0 with ⟨h0l, _⟩ | ⟨h0r, _⟩
          · have h1r : u1.val ∈ r.leaves := by
              rcases hopp u1 hu1 with ⟨h1l, _⟩ | ⟨h1r, _⟩
              · exact absurd (huniq_l u1 hu1 u0 hu0 h1l h0l) hne
              · exact h1r
            rcases hopp u hu with ⟨hul, _⟩ | ⟨hur, _⟩
            · exact Or.inl (huniq_l u hu u0 hu0 hul h0l)
            · exact Or.inr (huniq_r u hu u1 hu1 hur h1r)
          · have h1l : u1.val ∈ l.leaves := by
              rcases hopp u1 hu1 with ⟨h1l, _⟩ | ⟨h1r, _⟩
              · exact h1l
              · exact absurd (huniq_r u1 hu1 u0 hu0 h1r h0r) hne
            rcases hopp u hu with ⟨hul, _⟩ | ⟨hur, _⟩
            · exact Or.inr (huniq_l u hu u1 hu1 hul h1l)
            · exact Or.inl (huniq_r u hu u0 hu0 hur h0r)
        · rintro (rfl | rfl) <;> assumption

      let σ : Fin k → Fin k := fun u => if u = u0 then u1 else if u = u1 then u0 else u
      have hinv : ∀ u, σ (σ u) = u := by
        intro u
        by_cases h1 : u = u0
        · subst h1; simp [σ, hne]
        · by_cases h2 : u = u1
          · subst h2; simp [σ, hne.symm]
          · simp [σ, h1, h2]
      have hcl : ∀ u ∈ U, σ u ∈ U := by
        intro u hu; rw [hU_eq] at hu ⊢
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu ⊢
        rcases hu with rfl | rfl
        · simp [σ]
        · simp [σ, hne]
      have hpair_eval : ∀ (a b : Fin k), a ∈ U → b ∈ U → a ≠ b →
          a.val ∈ l.leaves → nr + a.val ∈ r.leaves →
          b.val ∈ r.leaves → nr + b.val ∈ l.leaves →
          ∀ v : ℕ → Bool,
            l.eval v = (v a.val || v (nr + b.val)) ∧ r.eval v = (v b.val || v (nr + a.val)) := by
        intro a b ha hb hab hal har hbr hbl v
        have hlv_l : l.leaves = {a.val, nr + b.val} := by
          ext w
          simp only [Finset.mem_insert, Finset.mem_singleton]
          constructor
          · intro hw
            have hwT : w ∈ l.leaves ∪ r.leaves := Finset.mem_union_left _ hw
            rw [show l.leaves ∪ r.leaves = _ from hlv, hU_eq] at hwT
            have hUab : ({u0, u1} : Finset (Fin k)) = {a, b} := by
              rw [← hU_eq]
              ext x; simp only [Finset.mem_insert, Finset.mem_singleton]
              constructor
              · intro hx
                rw [hU_eq] at hx ha hb
                simp only [Finset.mem_insert, Finset.mem_singleton] at hx ha hb
                rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
                · exact absurd rfl hab
                · exact hx
                · exact hx.symm
                · exact absurd rfl hab
              · rintro (rfl | rfl) <;> assumption
            rw [hUab] at hwT
            simp only [Finset.image_insert, Finset.image_singleton, Finset.mem_union,
              Finset.mem_insert, Finset.mem_singleton] at hwT
            rcases hwT with (rfl | rfl) | (rfl | rfl)
            · exact Or.inl rfl
            · exact absurd hw (Finset.disjoint_right.mp hdisj hbr)
            · exact absurd hw (Finset.disjoint_right.mp hdisj har)
            · exact Or.inr rfl
          · rintro (rfl | rfl) <;> assumption
        have hlv_r : r.leaves = {b.val, nr + a.val} := by
          ext w
          simp only [Finset.mem_insert, Finset.mem_singleton]
          constructor
          · intro hw
            have hwT : w ∈ l.leaves ∪ r.leaves := Finset.mem_union_right _ hw
            rw [show l.leaves ∪ r.leaves = _ from hlv, hU_eq] at hwT
            have hUab : ({u0, u1} : Finset (Fin k)) = {a, b} := by
              rw [← hU_eq]
              ext x; simp only [Finset.mem_insert, Finset.mem_singleton]
              constructor
              · intro hx
                rw [hU_eq] at hx ha hb
                simp only [Finset.mem_insert, Finset.mem_singleton] at hx ha hb
                rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
                · exact absurd rfl hab
                · exact hx
                · exact hx.symm
                · exact absurd rfl hab
              · rintro (rfl | rfl) <;> assumption
            rw [hUab] at hwT
            simp only [Finset.image_insert, Finset.image_singleton, Finset.mem_union,
              Finset.mem_insert, Finset.mem_singleton] at hwT
            rcases hwT with (rfl | rfl) | (rfl | rfl)
            · exact absurd hw (Finset.disjoint_left.mp hdisj hal)
            · exact Or.inl rfl
            · exact Or.inr rfl
            · exact absurd hw (Finset.disjoint_left.mp hdisj hbl)
          · rintro (rfl | rfl) <;> assumption
        have hla : l.eval (leftVec a.val) = true := by
          have hd := hrep a ha a ha
          simp only [FTree.eval, decide_true, Bool.and_eq_true] at hd
          rw [← hd.1]
          apply FTree.eval_congr
          intro w hw
          rw [hlv_l] at hw
          simp only [Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl
          · simp [leftVec, pairVec]
          · have hne1 : nr + b.val ≠ a.val := by have := a.isLt; omega
            have hne2 : nr + b.val ≠ nr + a.val := fun e => hab (Fin.ext (by omega))
            simp only [leftVec, pairVec, hne1, hne2, or_false, decide_false]
        have hrb : r.eval (leftVec b.val) = true := by
          have hd := hrep b hb b hb
          simp only [FTree.eval, decide_true, Bool.and_eq_true] at hd
          rw [← hd.2]
          apply FTree.eval_congr
          intro w hw
          rw [hlv_r] at hw
          simp only [Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl
          · simp [leftVec, pairVec]
          · have hne1 : nr + a.val ≠ b.val := by have := b.isLt; omega
            have hne2 : nr + a.val ≠ nr + b.val := fun e => hab (Fin.ext (by omega))
            simp only [leftVec, pairVec, hne1, hne2, or_false, decide_false]
        exact ⟨mono_tree_card_two_or hrol h0.1 (by have := a.isLt; omega) hlv_l hla v,
          mono_tree_card_two_or hror h0.2 (by have := b.isLt; omega) hlv_r hrb v⟩
      refine ⟨σ, hinv, hcl, ?_⟩
      intro v
      have hform : (l.eval v && r.eval v) =
          ((v u0.val || v (nr + u1.val)) && (v u1.val || v (nr + u0.val))) := by
        rcases hopp u0 hu0 with ⟨h0l, h0r⟩ | ⟨h0r, h0l⟩
        · have h1r : u1.val ∈ r.leaves ∧ nr + u1.val ∈ l.leaves := by
            rcases hopp u1 hu1 with ⟨h1l, _⟩ | h1
            · exact absurd (huniq_l u1 hu1 u0 hu0 h1l h0l) hne
            · exact h1
          have hp := hpair_eval u0 u1 hu0 hu1 hne.symm h0l h0r h1r.1 h1r.2 v
          rw [hp.1, hp.2]
        · have h1l : u1.val ∈ l.leaves ∧ nr + u1.val ∈ r.leaves := by
            rcases hopp u1 hu1 with h1 | ⟨h1r, _⟩
            · exact h1
            · exact absurd (huniq_r u1 hu1 u0 hu0 h1r h0r) hne
          have hp := hpair_eval u1 u0 hu1 hu0 hne h1l.1 h1l.2 h0r h0l v
          rw [hp.1, hp.2, Bool.and_comm]
      simp only [FTree.eval, hform, matchEvalOn, hU_eq]
      rw [Bool.eq_iff_iff]
      simp only [Finset.mem_insert, Finset.mem_singleton, decide_eq_true_eq]
      have hσ0 : σ u0 = u1 := by simp [σ]
      have hσ1 : σ u1 = u0 := by simp [σ, hne]
      constructor
      · intro h
        simp only [Bool.and_eq_true, Bool.or_eq_true] at h
        rcases h with ⟨hA | hB, hC | hD⟩
        · exact ⟨u0, Or.inl rfl, Or.inr ⟨by rw [hσ0]; exact hne.symm, Or.inl ⟨hA, by rw [hσ0]; exact hC⟩⟩⟩
        · exact ⟨u0, Or.inl rfl, Or.inl ⟨hA, hD⟩⟩
        · exact ⟨u1, Or.inr rfl, Or.inl ⟨hC, hB⟩⟩
        · exact ⟨u0, Or.inl rfl, Or.inr ⟨by rw [hσ0]; exact hne.symm, Or.inr ⟨hD, by rw [hσ0]; exact hB⟩⟩⟩
      · rintro ⟨u, rfl | rfl, h⟩
        · rw [hσ0] at h
          rcases h with ⟨h1, h2⟩ | ⟨_, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ <;> simp [h1, h2]
        · rw [hσ1] at h
          rcases h with ⟨h1, h2⟩ | ⟨_, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ <;> simp [h1, h2]
    · push_neg at hother
      have hU_eq : U = {u0} := by
        ext u; simp only [Finset.mem_singleton]
        exact ⟨fun hu => hother u hu, fun h => h ▸ hu0⟩
      refine ⟨id, fun _ => rfl, fun _ hu => hu, ?_⟩
      intro v
      have hpair_one : (l.eval v && r.eval v) = (v u0.val && v (nr + u0.val)) := by
        rcases hopp u0 hu0 with ⟨h0l, h0r⟩ | ⟨h0r, h0l⟩
        · have hlv_l : l.leaves = {u0.val} := by
            ext w; simp only [Finset.mem_singleton]
            constructor
            · intro hw
              have hwT : w ∈ l.leaves ∪ r.leaves := Finset.mem_union_left _ hw
              rw [show l.leaves ∪ r.leaves = _ from hlv, hU_eq] at hwT
              simp only [Finset.image_singleton, Finset.mem_union, Finset.mem_singleton] at hwT
              rcases hwT with rfl | rfl
              · rfl
              · exact absurd hw (Finset.disjoint_right.mp hdisj h0r)
            · rintro rfl; exact h0l
          have hlv_r : r.leaves = {nr + u0.val} := by
            ext w; simp only [Finset.mem_singleton]
            constructor
            · intro hw
              have hwT : w ∈ l.leaves ∪ r.leaves := Finset.mem_union_right _ hw
              rw [show l.leaves ∪ r.leaves = _ from hlv, hU_eq] at hwT
              simp only [Finset.image_singleton, Finset.mem_union, Finset.mem_singleton] at hwT
              rcases hwT with rfl | rfl
              · exact absurd hw (Finset.disjoint_left.mp hdisj h0l)
              · rfl
            · rintro rfl; exact h0r
          rw [mono_tree_card_one hrol h0.1 hlv_l v, mono_tree_card_one hror h0.2 hlv_r v]
        · have hlv_l : l.leaves = {nr + u0.val} := by
            ext w; simp only [Finset.mem_singleton]
            constructor
            · intro hw
              have hwT : w ∈ l.leaves ∪ r.leaves := Finset.mem_union_left _ hw
              rw [show l.leaves ∪ r.leaves = _ from hlv, hU_eq] at hwT
              simp only [Finset.image_singleton, Finset.mem_union, Finset.mem_singleton] at hwT
              rcases hwT with rfl | rfl
              · exact absurd hw (Finset.disjoint_right.mp hdisj h0r)
              · rfl
            · rintro rfl; exact h0l
          have hlv_r : r.leaves = {u0.val} := by
            ext w; simp only [Finset.mem_singleton]
            constructor
            · intro hw
              have hwT : w ∈ l.leaves ∪ r.leaves := Finset.mem_union_right _ hw
              rw [show l.leaves ∪ r.leaves = _ from hlv, hU_eq] at hwT
              simp only [Finset.image_singleton, Finset.mem_union, Finset.mem_singleton] at hwT
              rcases hwT with rfl | rfl
              · rfl
              · exact absurd hw (Finset.disjoint_left.mp hdisj h0l)
            · rintro rfl; exact h0r
          rw [mono_tree_card_one hrol h0.1 hlv_l v, mono_tree_card_one hror h0.2 hlv_r v, Bool.and_comm]
      simp [FTree.eval, hpair_one, matchEvalOn, hU_eq]

private def compileTree (base : ℕ) : FTree → List Gate × ℕ
  | .leaf w => ([], w)
  | .not t =>
    let (gt, wt) := compileTree base t
    (gt ++ [⟨.not, [wt]⟩], base + gt.length)
  | .and l r =>
    let (gl, wl) := compileTree base l
    let (gr, wr) := compileTree (base + gl.length) r
    (gl ++ gr ++ [⟨.and, [wl, wr]⟩], base + gl.length + gr.length)
  | .or l r =>
    let (gl, wl) := compileTree base l
    let (gr, wr) := compileTree (base + gl.length) r
    (gl ++ gr ++ [⟨.or, [wl, wr]⟩], base + gl.length + gr.length)

private def FTree.gateCount : FTree → ℕ
  | .leaf _ => 0
  | .not t => t.gateCount + 1
  | .and l r => l.gateCount + r.gateCount + 1
  | .or l r => l.gateCount + r.gateCount + 1

private lemma compileTree_length (base : ℕ) (t : FTree) :
    (compileTree base t).1.length = t.gateCount := by
  induction t generalizing base with
  | leaf _ => rfl
  | not t ih =>
    simp [compileTree, FTree.gateCount, ih]
  | and l r ihl ihr =>
    simp [compileTree, FTree.gateCount, ihl, ihr]; omega
  | or l r ihl ihr =>
    simp [compileTree, FTree.gateCount, ihl, ihr]; omega

private lemma compileTree_mono (base : ℕ) (t : FTree) (h0 : t.notCount = 0) :
    ∀ g ∈ (compileTree base t).1, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction t generalizing base with
  | leaf _ => intro g hg; simp [compileTree] at hg
  | not _ _ => simp [FTree.notCount] at h0
  | and l r ihl ihr =>
    simp only [FTree.notCount, Nat.add_eq_zero_iff] at h0
    intro g hg
    simp only [compileTree, List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | hg) | rfl
    · exact ihl base h0.1 g hg
    · exact ihr _ h0.2 g hg
    · simp
  | or l r ihl ihr =>
    simp only [FTree.notCount, Nat.add_eq_zero_iff] at h0
    intro g hg
    simp only [compileTree, List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | hg) | rfl
    · exact ihl base h0.1 g hg
    · exact ihr _ h0.2 g hg
    · simp

private lemma compileTree_fanInTwo (base : ℕ) (t : FTree) :
    ∀ g ∈ (compileTree base t).1,
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction t generalizing base with
  | leaf _ => intro g hg; simp [compileTree] at hg
  | not t ih =>
    intro g hg
    simp only [compileTree, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact ih base g hg
    · simp
  | and l r ihl ihr =>
    intro g hg
    simp only [compileTree, List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | hg) | rfl
    · exact ihl base g hg
    · exact ihr _ g hg
    · simp
  | or l r ihl ihr =>
    intro g hg
    simp only [compileTree, List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | hg) | rfl
    · exact ihl base g hg
    · exact ihr _ g hg
    · simp

private lemma compileTree_out_lt (base : ℕ) (t : FTree) (hlv : ∀ w ∈ t.leaves, w < base) :
    (compileTree base t).2 < base + (compileTree base t).1.length := by
  cases t with
  | leaf w =>
    simp only [compileTree, List.length_nil, add_zero]
    exact hlv w (Finset.mem_singleton_self w)
  | not t => simp [compileTree]
  | and l r => simp [compileTree]; omega
  | or l r => simp [compileTree]; omega

private lemma compileTree_eval (t : FTree) (w0 : List Bool)
    (hlv : ∀ w ∈ t.leaves, w < w0.length) :
    ((compileTree w0.length t).1.foldl stepWire w0).getD (compileTree w0.length t).2 false =
      t.eval (fun i => w0.getD i false) := by
  induction t generalizing w0 with
  | leaf w => rfl
  | not t ih =>
    simp only [compileTree, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set w1 := (compileTree w0.length t).1.foldl stepWire w0
    have hw1_len : w1.length = w0.length + (compileTree w0.length t).1.length :=
      foldl_stepWire_length _ _
    have hget : (stepWire w1 ⟨.not, [(compileTree w0.length t).2]⟩).getD
        (w0.length + (compileTree w0.length t).1.length) false =
        !(w1.getD (compileTree w0.length t).2 false) := by
      simp [stepWire, GateOp.eval, List.getD_eq_getElem?_getD, hw1_len]
    rw [hget, ih w0 hlv]; rfl
  | and l r ihl ihr =>
    simp only [compileTree, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlv_l : ∀ w ∈ l.leaves, w < w0.length := fun w hw => hlv w (Finset.mem_union_left _ hw)
    set w1 := (compileTree w0.length l).1.foldl stepWire w0
    have hw1_len : w1.length = w0.length + (compileTree w0.length l).1.length :=
      foldl_stepWire_length _ _
    have hlv_r : ∀ w ∈ r.leaves, w < w1.length := fun w hw => by
      have := hlv w (Finset.mem_union_right _ hw); omega
    set w2 := (compileTree (w0.length + (compileTree w0.length l).1.length) r).1.foldl stepWire w1
    have hw2_len : w2.length =
        w0.length + (compileTree w0.length l).1.length +
        (compileTree (w0.length + (compileTree w0.length l).1.length) r).1.length := by
      rw [foldl_stepWire_length, hw1_len]
    have hwl_lt : (compileTree w0.length l).2 < w1.length := by
      rw [hw1_len]; exact compileTree_out_lt w0.length l hlv_l
    have hw2_l : w2.getD (compileTree w0.length l).2 false = w1.getD (compileTree w0.length l).2 false :=
      foldl_stepWire_getD_lt _ _ hwl_lt
    have hw2_r : w2.getD (compileTree (w0.length + (compileTree w0.length l).1.length) r).2 false =
        r.eval (fun i => w0.getD i false) := by
      have h := ihr w1 hlv_r
      rw [hw1_len] at h
      rw [h]
      apply FTree.eval_congr
      intro i hi
      exact foldl_stepWire_getD_lt _ _ (hlv i (Finset.mem_union_right _ hi))
    have hget : (stepWire w2 ⟨.and, [(compileTree w0.length l).2,
        (compileTree (w0.length + (compileTree w0.length l).1.length) r).2]⟩).getD
        (w0.length + (compileTree w0.length l).1.length +
         (compileTree (w0.length + (compileTree w0.length l).1.length) r).1.length) false =
        (w2.getD (compileTree w0.length l).2 false &&
         w2.getD (compileTree (w0.length + (compileTree w0.length l).1.length) r).2 false) := by
      simp [stepWire, GateOp.eval, List.getD_eq_getElem?_getD, hw2_len]
    rw [hget, hw2_l, ihl w0 hlv_l, hw2_r]; rfl
  | or l r ihl ihr =>
    simp only [compileTree, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlv_l : ∀ w ∈ l.leaves, w < w0.length := fun w hw => hlv w (Finset.mem_union_left _ hw)
    set w1 := (compileTree w0.length l).1.foldl stepWire w0
    have hw1_len : w1.length = w0.length + (compileTree w0.length l).1.length :=
      foldl_stepWire_length _ _
    have hlv_r : ∀ w ∈ r.leaves, w < w1.length := fun w hw => by
      have := hlv w (Finset.mem_union_right _ hw); omega
    set w2 := (compileTree (w0.length + (compileTree w0.length l).1.length) r).1.foldl stepWire w1
    have hw2_len : w2.length =
        w0.length + (compileTree w0.length l).1.length +
        (compileTree (w0.length + (compileTree w0.length l).1.length) r).1.length := by
      rw [foldl_stepWire_length, hw1_len]
    have hwl_lt : (compileTree w0.length l).2 < w1.length := by
      rw [hw1_len]; exact compileTree_out_lt w0.length l hlv_l
    have hw2_l : w2.getD (compileTree w0.length l).2 false = w1.getD (compileTree w0.length l).2 false :=
      foldl_stepWire_getD_lt _ _ hwl_lt
    have hw2_r : w2.getD (compileTree (w0.length + (compileTree w0.length l).1.length) r).2 false =
        r.eval (fun i => w0.getD i false) := by
      have h := ihr w1 hlv_r
      rw [hw1_len] at h
      rw [h]
      apply FTree.eval_congr
      intro i hi
      exact foldl_stepWire_getD_lt _ _ (hlv i (Finset.mem_union_right _ hi))
    have hget : (stepWire w2 ⟨.or, [(compileTree w0.length l).2,
        (compileTree (w0.length + (compileTree w0.length l).1.length) r).2]⟩).getD
        (w0.length + (compileTree w0.length l).1.length +
         (compileTree (w0.length + (compileTree w0.length l).1.length) r).1.length) false =
        (w2.getD (compileTree w0.length l).2 false ||
         w2.getD (compileTree (w0.length + (compileTree w0.length l).1.length) r).2 false) := by
      simp [stepWire, GateOp.eval, List.getD_eq_getElem?_getD, hw2_len]
    rw [hget, hw2_l, ihl w0 hlv_l, hw2_r]; rfl

private lemma compileTree_circuit_eval (t : FTree) (x : List Bool) (N : ℕ)
    (hx : x.length = N) (hlv : ∀ w ∈ t.leaves, w < N) :
    (Circuit.mk (compileTree N t).1 (compileTree N t).2).eval x =
      t.eval (fun i => x.getD i false) := by
  subst hx
  exact compileTree_eval t x hlv

private def orList : FTree → List FTree → FTree
  | t, [] => t
  | t, t' :: ts => .or t (orList t' ts)

private lemma orList_notCount (t : FTree) (ts : List FTree)
    (ht : t.notCount = 0) (hts : ∀ s ∈ ts, s.notCount = 0) :
    (orList t ts).notCount = 0 := by
  induction ts generalizing t with
  | nil => exact ht
  | cons s ts ih =>
    simp only [orList, FTree.notCount]
    rw [ht, ih s (hts s List.mem_cons_self) (fun x hx => hts x (List.mem_cons_of_mem s hx))]

private lemma orList_gateCount (t : FTree) (ts : List FTree) :
    (orList t ts).gateCount + 1 = (t.gateCount + 1) + (ts.map fun s => s.gateCount + 1).sum := by
  induction ts generalizing t with
  | nil => simp [orList]
  | cons s ts ih =>
    simp only [orList, FTree.gateCount, List.map_cons, List.sum_cons]
    have := ih s
    omega

private lemma orList_leaves (t : FTree) (ts : List FTree) (w : ℕ) :
    w ∈ (orList t ts).leaves ↔ w ∈ t.leaves ∨ ∃ s ∈ ts, w ∈ s.leaves := by
  induction ts generalizing t with
  | nil => simp [orList]
  | cons s ts ih =>
    simp only [orList, FTree.leaves, Finset.mem_union, ih, List.mem_cons]
    constructor
    · rintro (h | h | ⟨x, hx, hwx⟩)
      · exact Or.inl h
      · exact Or.inr ⟨s, Or.inl rfl, h⟩
      · exact Or.inr ⟨x, Or.inr hx, hwx⟩
    · rintro (h | ⟨x, rfl | hx, hwx⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl hwx)
      · exact Or.inr (Or.inr ⟨x, hx, hwx⟩)

private lemma orList_eval (t : FTree) (ts : List FTree) (v : ℕ → Bool) :
    (orList t ts).eval v = true ↔ t.eval v = true ∨ ∃ s ∈ ts, s.eval v = true := by
  induction ts generalizing t with
  | nil => simp [orList]
  | cons s ts ih =>
    simp only [orList, FTree.eval, Bool.or_eq_true, ih, List.mem_cons]
    constructor
    · rintro (h | h | ⟨x, hx, hwx⟩)
      · exact Or.inl h
      · exact Or.inr ⟨s, Or.inl rfl, h⟩
      · exact Or.inr ⟨x, Or.inr hx, hwx⟩
    · rintro (h | ⟨x, rfl | hx, hwx⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl hwx)
      · exact Or.inr (Or.inr ⟨x, hx, hwx⟩)

private def termTree (nr : ℕ) {k : ℕ} (σ : Fin k → Fin k) (u : Fin k) : FTree :=
  if u = σ u then .and (.leaf u.val) (.leaf (nr + u.val))
  else .and (.or (.leaf u.val) (.leaf (nr + (σ u).val)))
            (.or (.leaf (nr + u.val)) (.leaf (σ u).val))

private lemma build_match_tree {k nr : ℕ} (hk : 1 ≤ k) (σ : Fin k → Fin k)
    (hinv : ∀ u, σ (σ u) = u) :
    ∃ T : FTree,
      T.notCount = 0 ∧
      T.gateCount + 1 = 2 * k ∧
      (∀ w ∈ T.leaves, w < nr + k) ∧
      ∀ v : ℕ → Bool, T.eval v = matchEval k nr σ v := by
  let reps : List (Fin k) := (List.finRange k).filter (fun u => decide (u.val ≤ (σ u).val))
  have h0_mem : (⟨0, hk⟩ : Fin k) ∈ reps := by
    simp only [reps, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
    exact Nat.zero_le _
  rcases hreps : reps with _ | ⟨u0, rest⟩
  · rw [hreps] at h0_mem; simp at h0_mem
  let T := orList (termTree nr σ u0) (rest.map (termTree nr σ))
  have hreps_nodup : reps.Nodup := (List.nodup_finRange k).filter _
  have hreps_mem : ∀ u : Fin k, u ∈ reps ↔ u.val ≤ (σ u).val := by
    intro u; simp [reps]
  refine ⟨T, ?_, ?_, ?_, ?_⟩
  · apply orList_notCount
    · unfold termTree; split_ifs <;> rfl
    · intro s hs
      rw [List.mem_map] at hs
      rcases hs with ⟨u, _, rfl⟩
      unfold termTree; split_ifs <;> rfl
  · have hgc := orList_gateCount (termTree nr σ u0) (rest.map (termTree nr σ))
    have hsum_eq : (termTree nr σ u0).gateCount + 1 +
        ((rest.map (termTree nr σ)).map fun s => s.gateCount + 1).sum =
        (reps.map fun u => (termTree nr σ u).gateCount + 1).sum := by
      rw [hreps]; simp [List.map_map, Function.comp_def]
    rw [hgc, hsum_eq]
    have hterm_gc : ∀ u : Fin k, (termTree nr σ u).gateCount + 1 =
        2 * (if u = σ u then 1 else 2) := by
      intro u; unfold termTree; split_ifs <;> rfl
    have hfinset : (reps.map fun u => (termTree nr σ u).gateCount + 1).sum =
        ∑ u ∈ reps.toFinset, 2 * (if u = σ u then 1 else 2) := by
      rw [← List.sum_toFinset _ hreps_nodup]
      congr 1; ext u; exact hterm_gc u
    rw [hfinset, ← Finset.mul_sum]
    suffices hcount : ∑ u ∈ reps.toFinset, (if u = σ u then 1 else 2) = k by omega
    have hsum_all : ∑ u : Fin k, (if u.val ≤ (σ u).val then (if u = σ u then 1 else 2) else 0) =
        ∑ u ∈ reps.toFinset, (if u = σ u then 1 else 2) := by
      rw [← Finset.sum_filter]
      congr 1; ext u; simp [hreps_mem]
    rw [← hsum_all]
    have hlt_eq : ∑ u : Fin k, (if u.val < (σ u).val then 1 else 0) =
        ∑ u : Fin k, (if (σ u).val < u.val then 1 else 0) := by
      let e : Fin k ≃ Fin k := ⟨σ, σ, hinv, hinv⟩
      refine Fintype.sum_equiv e _ _ (fun u => ?_)
      simp [e, hinv u]
    have hsplit : ∑ u : Fin k, (if u.val ≤ (σ u).val then (if u = σ u then 1 else 2) else 0) =
        (∑ u : Fin k, if u = σ u then 1 else 0) +
        (∑ u : Fin k, if u.val < (σ u).val then 1 else 0) +
        (∑ u : Fin k, if u.val < (σ u).val then 1 else 0) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro u _
      by_cases h1 : u = σ u
      · have hval : (σ u).val = u.val := (congrArg Fin.val h1).symm
        rw [if_pos (by omega), if_pos h1, if_pos h1, if_neg (by omega)]
      · have hne : u.val ≠ (σ u).val := fun e => h1 (Fin.ext e)
        by_cases h2 : u.val < (σ u).val
        · have hle : u.val ≤ (σ u).val := Nat.le_of_lt h2
          simp [h1, h2, hle]
        · have hnle : ¬ u.val ≤ (σ u).val := by omega
          simp [h1, h2, hnle]
    rw [hsplit]
    conv_lhs => rhs; rw [hlt_eq]
    have htot : (∑ u : Fin k, if u = σ u then 1 else 0) +
        (∑ u : Fin k, if u.val < (σ u).val then 1 else 0) +
        (∑ u : Fin k, if (σ u).val < u.val then 1 else 0) = ∑ _u : Fin k, 1 := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro u _
      by_cases h1 : u = σ u
      · have hval : (σ u).val = u.val := (congrArg Fin.val h1).symm
        rw [if_pos h1, if_neg (by omega), if_neg (by omega)]
      · have hne : u.val ≠ (σ u).val := fun e => h1 (Fin.ext e)
        by_cases h2 : u.val < (σ u).val
        · have h3 : ¬ (σ u).val < u.val := by omega
          simp [h1, h2, h3]
        · have h3 : (σ u).val < u.val := by omega
          simp [h1, h2, h3]
    rw [htot]; simp
  · intro w hw
    rw [orList_leaves] at hw
    have hterm_lt : ∀ u : Fin k, ∀ x ∈ (termTree nr σ u).leaves, x < nr + k := by
      intro u x hx
      unfold termTree at hx
      split_ifs at hx <;> simp [FTree.leaves] at hx <;> rcases hx with rfl | rfl | rfl | rfl <;> omega
    rcases hw with h | ⟨s, hs, hws⟩
    · exact hterm_lt u0 w h
    · rw [List.mem_map] at hs
      rcases hs with ⟨u, _, rfl⟩
      exact hterm_lt u w hws
  · intro v
    rw [Bool.eq_iff_iff]
    rw [orList_eval]
    have hlist : ((termTree nr σ u0).eval v = true ∨
        ∃ s ∈ rest.map (termTree nr σ), s.eval v = true) ↔
        ∃ u ∈ reps, (termTree nr σ u).eval v = true := by
      rw [hreps]
      simp only [List.mem_map, List.mem_cons]
      constructor
      · rintro (h | ⟨_, ⟨u, hu, rfl⟩, h⟩)
        · exact ⟨u0, Or.inl rfl, h⟩
        · exact ⟨u, Or.inr hu, h⟩
      · rintro ⟨u, rfl | hu, h⟩
        · exact Or.inl h
        · exact Or.inr ⟨termTree nr σ u, ⟨u, hu, rfl⟩, h⟩
    rw [hlist]
    simp only [matchEval, decide_eq_true_eq]
    have hterm_eval : ∀ u : Fin k, (termTree nr σ u).eval v = true ↔
        ((v u.val = true ∧ v (nr + u.val) = true) ∨
         (u ≠ σ u ∧ ((v (σ u).val = true ∧ v (nr + (σ u).val) = true) ∨
           (v u.val = true ∧ v (σ u).val = true) ∨
           (v (nr + u.val) = true ∧ v (nr + (σ u).val) = true)))) := by
      intro u
      unfold termTree
      split_ifs with heq
      · simp only [FTree.eval, Bool.and_eq_true, ne_eq, not_and]
        constructor
        · intro h; exact Or.inl h
        · rintro (h | ⟨hne, _⟩)
          · exact h
          · exact absurd heq hne
      · simp only [FTree.eval, Bool.and_eq_true, Bool.or_eq_true, ne_eq, heq, not_false_eq_true,
          true_and]
        tauto
    constructor
    · rintro ⟨u, _, hu⟩
      rw [hterm_eval] at hu
      rcases hu with h | ⟨hne, h1 | h2 | h3⟩
      · exact ⟨u, Or.inl h⟩
      · exact ⟨σ u, Or.inl h1⟩
      · exact ⟨u, Or.inr ⟨hne, Or.inl h2⟩⟩
      · exact ⟨u, Or.inr ⟨hne, Or.inr h3⟩⟩
    · rintro ⟨u, hu⟩
      by_cases hle : u.val ≤ (σ u).val
      · refine ⟨u, (hreps_mem u).mpr hle, (hterm_eval u).mpr ?_⟩
        rcases hu with h | ⟨hne, h1 | h2⟩
        · exact Or.inl h
        · exact Or.inr ⟨hne, Or.inr (Or.inl h1)⟩
        · exact Or.inr ⟨hne, Or.inr (Or.inr h2)⟩
      · have hle' : (σ u).val ≤ (σ (σ u)).val := by rw [hinv u]; omega
        have hne : σ u ≠ u := fun e => by rw [e] at hle; exact hle le_rfl
        refine ⟨σ u, (hreps_mem (σ u)).mpr hle', (hterm_eval (σ u)).mpr ?_⟩
        rw [hinv u]
        rcases hu with h | ⟨_, h1 | h2⟩
        · exact Or.inr ⟨hne, Or.inl h⟩
        · exact Or.inr ⟨hne, Or.inr (Or.inl ⟨h1.2, h1.1⟩)⟩
        · exact Or.inr ⟨hne, Or.inr (Or.inr ⟨h2.2, h2.1⟩)⟩

private def getInput {nr nc : ℕ} (x : Fin nr → Bool) (y : Fin nc → Bool) (i : ℕ) : Bool :=
  (List.ofFn x ++ List.ofFn y).getD i false

private lemma getInput_left {nr nc : ℕ} (x : Fin nr → Bool) (y : Fin nc → Bool) (u : Fin nr) :
    getInput x y u.val = x u := by
  simp [getInput, List.getD_eq_getElem?_getD, List.getElem?_append_left (show u.val < (List.ofFn x).length by simp)]

private lemma getInput_right {nr nc : ℕ} (x : Fin nr → Bool) (y : Fin nc → Bool) (v : Fin nc) :
    getInput x y (nr + v.val) = y v := by
  have h1 : (List.ofFn x).length ≤ nr + v.val := by simp
  have h2 : nr + v.val - (List.ofFn x).length = v.val := by simp
  simp [getInput, List.getD_eq_getElem?_getD, List.getElem?_append_right h1, h2]

private lemma getInput_oneEach {nr nc : ℕ} (u : Fin nr) (v : Fin nc) (w : ℕ) :
    (oneEach u v).getD w false = pairVec nr u.val v.val w := by
  unfold oneEach pairVec
  by_cases h1 : w < nr
  · have hlt : w < (List.ofFn (fun i : Fin nr => decide (i = u))).length := by simp [h1]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt, List.getElem?_ofFn, h1,
      ↓reduceDIte, Option.getD_some]
    have hne : w ≠ nr + v.val := by omega
    simp [hne, Fin.ext_iff]
  · by_cases h2 : w < nr + nc
    · have hge : (List.ofFn (fun i : Fin nr => decide (i = u))).length ≤ w := by simp; omega
      have hlt2 : w - nr < nc := by omega
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hge, List.length_ofFn,
        List.getElem?_ofFn, hlt2, ↓reduceDIte, Option.getD_some]
      have hne : w ≠ u.val := by omega
      simp [hne, Fin.ext_iff]; omega
    · have hge : (List.ofFn (fun i : Fin nr => decide (i = u)) ++
          List.ofFn (fun j : Fin nc => decide (j = v))).length ≤ w := by simp; omega
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge, Option.getD_none]
      have hne1 : w ≠ u.val := by omega
      have hne2 : w ≠ nr + v.val := by omega
      simp [hne1, hne2]

private def matchFn (k : ℕ) (σ : Fin k → Fin k) (x y : Fin k → Bool) : Bool :=
  decide (∃ u : Fin k, (x u = true ∧ y u = true) ∨
    (u ≠ σ u ∧ ((x u = true ∧ x (σ u) = true) ∨ (y u = true ∧ y (σ u) = true))))

private lemma matchEval_eq_matchFn {k nr nc : ℕ} (hnr : k ≤ nr) (hnc : k ≤ nc)
    (σ : Fin k → Fin k) (x : Fin nr → Bool) (y : Fin nc → Bool) :
    matchEval k nr σ (getInput x y) =
      matchFn k σ (fun u => x ⟨u.val, by omega⟩) (fun v => y ⟨v.val, by omega⟩) := by
  unfold matchEval matchFn
  congr 1; apply propext
  constructor <;> rintro ⟨u, hu⟩ <;> refine ⟨u, ?_⟩
  · rwa [getInput_left x y ⟨u.val, by omega⟩, getInput_right x y ⟨u.val, by omega⟩,
      getInput_left x y ⟨(σ u).val, by omega⟩, getInput_right x y ⟨(σ u).val, by omega⟩] at hu
  · rwa [getInput_left x y ⟨u.val, by omega⟩, getInput_right x y ⟨u.val, by omega⟩,
      getInput_left x y ⟨(σ u).val, by omega⟩, getInput_right x y ⟨(σ u).val, by omega⟩]

private def canonicalFn (k : ℕ) (crown : Bool) (σ : Fin k → Fin k) :
    (Fin (if crown then k + 2 else k) → Bool) →
    (Fin (if crown then k + 1 else k) → Bool) → Bool :=
  match crown with
  | false => fun x y => matchFn k σ x y
  | true => fun x y =>
      !(x (⟨k + 1, by dsimp; omega⟩ : Fin (if true then k + 2 else k)) ||
        matchFn k σ
          (fun u => x (⟨u.val, by dsimp; omega⟩ : Fin (if true then k + 2 else k)))
          (fun v => y (⟨v.val, by dsimp; omega⟩ : Fin (if true then k + 1 else k))))

private lemma eligible_iff_involution_false {k : ℕ} (hk : 7 ≤ k)
    (f : (Fin k → Bool) → (Fin k → Bool) → Bool) :
    let A := fun (i : Fin k) (j : Fin k) => decide (i.val = j.val)
    (∃ C : Circuit,
      (Monotone2 C ∧ C.size + 1 ≤ 2 * k) ∧
      Represents A C ∧
      ∀ x y, f x y = C.eval (List.ofFn x ++ List.ofFn y)) ↔
    ∃ σ : Fin k → Fin k, (∀ u, σ (σ u) = u) ∧ f = canonicalFn k false σ := by
  intro A
  constructor
  · rintro ⟨C, ⟨hmono, hsize⟩, hrep, hfeq⟩
    have hfan : FanInTwo C := fun g hg =>
      ⟨by rcases (hmono g hg).1 with h | h; exact Or.inl h; exact Or.inr (Or.inl h),
       (hmono g hg).2⟩
    set N := k + k
    have hout_lt : C.output < N + C.gates.length := by
      by_contra hge
      have h0 := hrep ⟨0, by omega⟩ ⟨0, by omega⟩
      have hev : C.eval (oneEach (⟨0, by omega⟩ : Fin k) (⟨0, by omega⟩ : Fin k)) = false := by
        unfold Circuit.eval
        apply circuit_wires_getD_ge
        have hlen : (oneEach (⟨0, by omega⟩ : Fin k) (⟨0, by omega⟩ : Fin k)).length = N := by
          simp only [oneEach, List.length_append, List.length_ofFn, N]
        change _ + C.gates.length ≤ C.output
        rw [hlen]
        omega
      simp [A, hev] at h0
    have hout_ge : N ≤ C.output := by
      by_contra hlt
      have h00 := hrep ⟨0, by omega⟩ ⟨0, by omega⟩
      have h11 := hrep ⟨1, by omega⟩ ⟨1, by omega⟩
      have h01 := hrep ⟨0, by omega⟩ ⟨1, by omega⟩
      have h10 := hrep ⟨1, by omega⟩ ⟨0, by omega⟩
      have hev : ∀ u v : Fin k, C.eval (oneEach u v) = pairVec k u.val v.val C.output := by
        intro u v
        unfold Circuit.eval
        rw [circuit_wires_getD_input C _ (by simp only [oneEach, List.length_append, List.length_ofFn, N]; omega), getInput_oneEach]
      rw [hev] at h00 h11 h01 h10
      simp [A, pairVec] at h00 h11 h01 h10
      omega
    set R := reach C N C.output
    set I := R.filter (· < N)
    set L := R.filter (fun z => N ≤ z)
    set Lnot := L.filter (fun g => isNotGate C N g = true)
    have hno_not : ∀ g ∈ L, ∀ h : g - N < C.gates.length, C.gates[g - N].op ≠ .not := by
      intro g _ hg
      rcases (hmono _ (List.getElem_mem hg)).1 with h | h <;> rw [h] <;> intro e <;> cases e
    have hLnot_empty : Lnot = ∅ := by
      ext g; simp only [Lnot, Finset.mem_filter, Finset.notMem_empty, iff_false]
      rintro ⟨hgL, h⟩
      simp only [isNotGate] at h
      split_ifs at h with hgj
      · cases hop : C.gates[g - N].op
        · simp [hop, isNotOp] at h
        · simp [hop, isNotOp] at h
        · exact hno_not g hgL hgj hop
        · simp [hop, isNotOp] at h
        · simp [hop, isNotOp] at h
    have hLnot_card : Lnot.card = 0 := by rw [hLnot_empty]; rfl

    have hI_all : ∀ w < N, w ∈ I := by
      intro w hw
      by_contra hnotin
      by_cases hw_k : w < k
      · let u : Fin k := ⟨w, hw_k⟩
        let v : Fin k := ⟨if w = 0 then 1 else 0, by split_ifs <;> omega⟩
        have huv : u ≠ v := by intro e; have := congrArg Fin.val e; simp [u, v] at this; split_ifs at this <;> omega
        have hle : ∀ i ∈ I, (oneEach u u).getD i false ≤ (oneEach v u).getD i false := by
          intro i hi
          have hne : i ≠ w := fun e => hnotin (e ▸ hi)
          rw [getInput_oneEach, getInput_oneEach]
          simp only [pairVec, show u.val = w from rfl, hne, false_or]
          by_cases h2 : i = k + w <;> simp [h2, Bool.false_le]
        have hm := wires_mono_of_no_not hfan (x1 := oneEach u u) (x2 := oneEach v u)
          (by simp only [oneEach, List.length_append, List.length_ofFn, N])
          (by simp only [oneEach, List.length_append, List.length_ofFn, N])
          hout_lt hno_not hle C.output (mem_reach_self hout_lt)
        have h1 : (C.wires (oneEach u u)).getD C.output false = true := by
          simpa [Circuit.eval, A] using hrep u u
        have h2 : (C.wires (oneEach v u)).getD C.output false = false := by
          have hne' : v.val ≠ u.val := fun e => huv (Fin.ext e.symm)
          simpa [Circuit.eval, A, hne'] using hrep v u
        rw [h1, h2] at hm; exact Bool.noConfusion (bool_eq_false_of_le hm)
      · let u : Fin k := ⟨w - k, by omega⟩
        let v : Fin k := ⟨if w - k = 0 then 1 else 0, by split_ifs <;> omega⟩
        have huv : u ≠ v := by intro e; have := congrArg Fin.val e; simp [u, v] at this; split_ifs at this <;> omega
        have hle : ∀ i ∈ I, (oneEach u u).getD i false ≤ (oneEach u v).getD i false := by
          intro i hi
          have hne : i ≠ w := fun e => hnotin (e ▸ hi)
          rw [getInput_oneEach, getInput_oneEach]
          simp only [pairVec, show k + u.val = w by change k + (w - k) = w; omega, hne, or_false]
          by_cases h2 : i = u.val <;> simp [h2]
        have hm := wires_mono_of_no_not hfan (x1 := oneEach u u) (x2 := oneEach u v)
          (by simp only [oneEach, List.length_append, List.length_ofFn, N])
          (by simp only [oneEach, List.length_append, List.length_ofFn, N])
          hout_lt hno_not hle C.output (mem_reach_self hout_lt)
        have h1 : (C.wires (oneEach u u)).getD C.output false = true := by
          simpa [Circuit.eval, A] using hrep u u
        have h2 : (C.wires (oneEach u v)).getD C.output false = false := by
          have hne' : u.val ≠ v.val := fun e => huv (Fin.ext e)
          simpa [Circuit.eval, A, hne'] using hrep u v
        rw [h1, h2] at hm; exact Bool.noConfusion (bool_eq_false_of_le hm)
    have hI_eq : I = Finset.range N := by
      ext w; simp only [Finset.mem_range]
      exact ⟨fun hw => (Finset.mem_filter.mp hw).2, hI_all w⟩
    have hI_card : I.card = 2 * k := by rw [hI_eq, Finset.card_range]; omega
    have hslot := slot_count_ineq hfan hout_ge hout_lt
    have htight : I.card + Lnot.card = L.card + 1 := by
      have h4 : I.card + Lnot.card ≤ L.card + 1 := hslot.2.2.2.1
      have h5 : L.card ≤ C.gates.length := hslot.2.2.2.2
      have hsz : C.gates.length + 1 ≤ 2 * k := hsize
      omega
    obtain ⟨T, hro, hlv, hnc, hev⟩ := extract_ftree hfan hout_ge hout_lt htight
    have h0 : T.notCount = 0 := by rw [hnc]; exact hLnot_card
    have hlv_eq : T.leaves =
        (Finset.univ : Finset (Fin k)).image (fun u : Fin k => u.val) ∪
        (Finset.univ : Finset (Fin k)).image (fun u : Fin k => k + u.val) := by
      rw [hlv]
      change I = _
      rw [hI_eq]
      ext w; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · intro hw
        by_cases h1 : w < k
        · exact Or.inl ⟨⟨w, h1⟩, rfl⟩
        · exact Or.inr ⟨⟨w - k, by omega⟩, by change k + (w - k) = w; omega⟩
      · rintro (⟨u, rfl⟩ | ⟨u, rfl⟩) <;> omega
    have hrepT : ∀ u ∈ (Finset.univ : Finset (Fin k)), ∀ v ∈ (Finset.univ : Finset (Fin k)),
        T.eval (pairVec k u.val v.val) = decide (u = v) := by
      intro u _ v _
      have h1 := hrep u v
      rw [hev (oneEach u v) (by simp only [oneEach, List.length_append, List.length_ofFn, N])] at h1
      have hcon : T.eval (fun i => (oneEach u v).getD i false) = T.eval (pairVec k u.val v.val) :=
        FTree.eval_congr fun i _ => getInput_oneEach u v i
      rw [hcon] at h1
      simpa [A, Fin.ext_iff] using h1
    have hleftT : ∀ u ∈ (Finset.univ : Finset (Fin k)), T.eval (leftVec u.val) = false := by
      intro u _
      let v : Fin k := ⟨if u.val = 0 then 1 else 0, by split_ifs <;> omega⟩
      have huv : u ≠ v := by intro e; have := congrArg Fin.val e; simp [v] at this; split_ifs at this <;> omega
      have hm := FTree.eval_mono_of_notCount_zero h0 (v1 := leftVec u.val)
        (v2 := pairVec k u.val v.val) (fun w _ => by
          unfold leftVec pairVec; by_cases h : w = u.val <;> simp [h])
      rw [hrepT u (Finset.mem_univ _) v (Finset.mem_univ _)] at hm
      simp only [huv, decide_false] at hm; exact bool_eq_false_of_le hm
    have hrightT : ∀ u ∈ (Finset.univ : Finset (Fin k)), T.eval (rightVec k u.val) = false := by
      intro u _
      let v : Fin k := ⟨if u.val = 0 then 1 else 0, by split_ifs <;> omega⟩
      have hvu : v ≠ u := by intro e; have := congrArg Fin.val e; simp [v] at this; split_ifs at this <;> omega
      have hm := FTree.eval_mono_of_notCount_zero h0 (v1 := rightVec k u.val)
        (v2 := pairVec k v.val u.val) (fun w _ => by
          unfold rightVec pairVec; by_cases h : w = k + u.val <;> simp [h])
      rw [hrepT v (Finset.mem_univ _) u (Finset.mem_univ _)] at hm
      simp only [hvu, decide_false] at hm; exact bool_eq_false_of_le hm
    obtain ⟨σ, hinv, _, hTeq⟩ := mono_tree_id_matching (le_refl k) T hro h0 Finset.univ
      ⟨⟨0, by omega⟩, Finset.mem_univ _⟩ hlv_eq hrepT hleftT hrightT
    refine ⟨σ, hinv, ?_⟩
    funext x y
    rw [hfeq x y, hev (List.ofFn x ++ List.ofFn y) (by simp only [List.length_append, List.length_ofFn, N]), hTeq]
    have hme : matchEvalOn k k Finset.univ σ (getInput x y) = matchEval k k σ (getInput x y) := by
      simp [matchEvalOn, matchEval]
    change matchEvalOn k k Finset.univ σ (getInput x y) = matchFn k σ x y
    rw [hme, matchEval_eq_matchFn (le_refl k) (le_refl k) σ x y]
  · rintro ⟨σ, hinv, rfl⟩
    obtain ⟨T, h0, hgc, hlv, hev⟩ := build_match_tree (nr := k) (by omega) σ hinv
    let compiled := compileTree (k + k) T
    let C : Circuit := ⟨compiled.1, compiled.2⟩
    refine ⟨C, ⟨?_, ?_⟩, ?_, ?_⟩
    · exact compileTree_mono (k + k) T h0
    · simp only [Circuit.size, C, compiled, compileTree_length]; omega
    · intro u v
      have hlen : (oneEach u v).length = k + k := by simp only [oneEach, List.length_append, List.length_ofFn]
      have hce : C.eval (oneEach u v) = T.eval (fun i => (oneEach u v).getD i false) :=
        compileTree_circuit_eval T (oneEach u v) (k + k) hlen hlv
      rw [hce, hev]
      have hcon : matchEval k k σ (fun i => (oneEach u v).getD i false) =
          matchEval k k σ (pairVec k u.val v.val) := by
        unfold matchEval; congr 1; apply propext
        simp only [getInput_oneEach]
      rw [hcon]
      simp only [matchEval, pairVec, A]
      rw [Bool.eq_iff_iff]
      simp only [decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨h1, h2⟩ | ⟨hne, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩⟩
        · rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> omega
        · rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
          · exact absurd (Fin.ext (by omega)) hne
          · omega
          · omega
          · omega
        · rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
          · omega
          · omega
          · omega
          · exact absurd (Fin.ext (by omega)) hne
      · intro huv
        exact ⟨u, Or.inl ⟨Or.inl rfl, Or.inr (by omega)⟩⟩
    · intro x y
      have hlen : (List.ofFn x ++ List.ofFn y).length = k + k := by simp only [List.length_append, List.length_ofFn]
      have hce : C.eval (List.ofFn x ++ List.ofFn y) = T.eval (getInput x y) :=
        compileTree_circuit_eval T (List.ofFn x ++ List.ofFn y) (k + k) hlen hlv
      rw [hce, hev, matchEval_eq_matchFn (le_refl k) (le_refl k) σ x y]
      rfl

private lemma eligible_iff_involution_true {k : ℕ} (hk : 7 ≤ k)
    (f : (Fin (k + 2) → Bool) → (Fin (k + 1) → Bool) → Bool) :
    let A := fun (i : Fin (k + 2)) (j : Fin (k + 1)) =>
      decide (i.val ≠ k + 1 ∧ ¬ (i.val < k ∧ i.val = j.val))
    (∃ C : Circuit,
      (FanInTwo C ∧ C.size ≤ 2 * k + 1) ∧
      Represents A C ∧
      ∀ x y, f x y = C.eval (List.ofFn x ++ List.ofFn y)) ↔
    ∃ σ : Fin k → Fin k, (∀ u, σ (σ u) = u) ∧ f = canonicalFn k true σ := by
  intro A
  constructor
  · rintro ⟨C, ⟨hfan, hsize⟩, hrep, hfeq⟩
    set N := (k + 2) + (k + 1)
    have hout_lt : C.output < N + C.gates.length := by
      by_contra hge
      have h0 := hrep ⟨0, by omega⟩ ⟨1, by omega⟩
      have hev : C.eval (oneEach (⟨0, by omega⟩ : Fin (k + 2)) (⟨1, by omega⟩ : Fin (k + 1))) = false := by
        unfold Circuit.eval
        apply circuit_wires_getD_ge
        have hlen : (oneEach (⟨0, by omega⟩ : Fin (k + 2)) (⟨1, by omega⟩ : Fin (k + 1))).length = N := by
          simp only [oneEach, List.length_append, List.length_ofFn, N]
        change _ + C.gates.length ≤ C.output
        rw [hlen]
        omega
      rw [hev] at h0
      simp [A] at h0
    have hout_ge : N ≤ C.output := by
      by_contra hlt
      have hev : ∀ u : Fin (k + 2), ∀ v : Fin (k + 1),
          C.eval (oneEach u v) = pairVec (k + 2) u.val v.val C.output := by
        intro u v
        unfold Circuit.eval
        rw [circuit_wires_getD_input C _ (by simp only [oneEach, List.length_append, List.length_ofFn, N]; omega), getInput_oneEach]
      have h01 := hrep ⟨0, by omega⟩ ⟨1, by omega⟩
      have h12 := hrep ⟨1, by omega⟩ ⟨2, by omega⟩
      have h20 := hrep ⟨2, by omega⟩ ⟨0, by omega⟩
      rw [hev] at h01 h12 h20
      have ha01 : A ⟨0, by omega⟩ ⟨1, by omega⟩ = true := by simp [A]
      have ha12 : A ⟨1, by omega⟩ ⟨2, by omega⟩ = true := by simp [A]; omega
      have ha20 : A ⟨2, by omega⟩ ⟨0, by omega⟩ = true := by simp [A]; omega
      rw [ha01] at h01; rw [ha12] at h12; rw [ha20] at h20
      simp only [pairVec, decide_eq_true_eq] at h01 h12 h20
      rcases h01 with h01 | h01 <;> rcases h12 with h12 | h12 <;> rcases h20 with h20 | h20 <;> omega
    set R := reach C N C.output
    set I := R.filter (· < N)
    set L := R.filter (fun z => N ≤ z)
    set Lnot := L.filter (fun g => isNotGate C N g = true)
    set Irow := I.filter (· < k + 2)
    set Icol := I.filter (fun w => k + 2 ≤ w)

    have hrow_distinct : ∀ u1 u2 : Fin (k + 2), u1 ≠ u2 → ∃ v : Fin (k + 1), A u1 v ≠ A u2 v := by
      intro u1 u2 hne
      by_cases h1 : u1.val < k
      · by_cases h2 : u2.val < k
        · refine ⟨⟨u1.val, by omega⟩, ?_⟩
          have hne' : u2.val ≠ u1.val := fun e => hne (Fin.ext e.symm)
          simp [A, h1, h2, hne', show u1.val ≠ k + 1 by omega, show u2.val ≠ k + 1 by omega]
        · by_cases h2k : u2.val = k
          · refine ⟨⟨u1.val, by omega⟩, ?_⟩
            simp [A, h1, h2k, show u1.val ≠ k + 1 by omega, show ¬ (k < k) by omega]
          · have h2k1 : u2.val = k + 1 := by omega
            refine ⟨⟨k, by omega⟩, ?_⟩
            simp [A, h1, h2k1, show u1.val ≠ k + 1 by omega, show u1.val ≠ k by omega]
      · by_cases h2 : u2.val < k
        · by_cases h1k : u1.val = k
          · refine ⟨⟨u2.val, by omega⟩, ?_⟩
            simp [A, h2, h1k, show u2.val ≠ k + 1 by omega, show ¬ (k < k) by omega]
          · have h1k1 : u1.val = k + 1 := by omega
            refine ⟨⟨k, by omega⟩, ?_⟩
            simp [A, h2, h1k1, show u2.val ≠ k + 1 by omega, show u2.val ≠ k by omega]
        · refine ⟨⟨0, by omega⟩, ?_⟩
          have : (u1.val = k ∧ u2.val = k + 1) ∨ (u1.val = k + 1 ∧ u2.val = k) := by
            have hne' : u1.val ≠ u2.val := fun e => hne (Fin.ext e)
            omega
          rcases this with ⟨h1', h2'⟩ | ⟨h1', h2'⟩ <;> simp [A, h1', h2']
    have hcol_distinct : ∀ v1 v2 : Fin (k + 1), v1 ≠ v2 → ∃ u : Fin (k + 2), A u v1 ≠ A u v2 := by
      intro v1 v2 hne
      by_cases h1 : v1.val < k
      · refine ⟨⟨v1.val, by omega⟩, ?_⟩
        have hne' : v1.val ≠ v2.val := fun e => hne (Fin.ext e)
        simp [A, h1, hne', show v1.val ≠ k + 1 by omega]
      · have h1k : v1.val = k := by omega
        have h2 : v2.val < k := by
          have hne' : v1.val ≠ v2.val := fun e => hne (Fin.ext e)
          omega
        refine ⟨⟨v2.val, by omega⟩, ?_⟩
        simp [A, h1k, h2, show v2.val ≠ k + 1 by omega, show v2.val ≠ k by omega]
    have hrow_miss : ∀ u1 u2 : Fin (k + 2), u1.val ∉ I → u2.val ∉ I → u1 = u2 := by
      intro u1 u2 hu1 hu2
      by_contra hne
      obtain ⟨v, hv⟩ := hrow_distinct u1 u2 hne
      have hagree : ∀ i ∈ I, (oneEach u1 v).getD i false = (oneEach u2 v).getD i false := by
        intro i hi
        rw [getInput_oneEach, getInput_oneEach]
        have h1 : i ≠ u1.val := fun e => hu1 (e ▸ hi)
        have h2 : i ≠ u2.val := fun e => hu2 (e ▸ hi)
        simp [pairVec, h1, h2]
      have heq := wires_agree_on_reach hfan
        (by simp only [oneEach, List.length_append, List.length_ofFn, N])
        (by simp only [oneEach, List.length_append, List.length_ofFn, N])
        hout_lt hagree C.output (mem_reach_self hout_lt)
      have ha1 := hrep u1 v
      have ha2 := hrep u2 v
      simp only [Circuit.eval] at ha1 ha2
      rw [heq, ha2] at ha1
      exact hv ha1.symm
    have hcol_miss : ∀ v1 v2 : Fin (k + 1), (k + 2) + v1.val ∉ I → (k + 2) + v2.val ∉ I → v1 = v2 := by
      intro v1 v2 hv1 hv2
      by_contra hne
      obtain ⟨u, hu⟩ := hcol_distinct v1 v2 hne
      have hagree : ∀ i ∈ I, (oneEach u v1).getD i false = (oneEach u v2).getD i false := by
        intro i hi
        rw [getInput_oneEach, getInput_oneEach]
        have h1 : i ≠ (k + 2) + v1.val := fun e => hv1 (e ▸ hi)
        have h2 : i ≠ (k + 2) + v2.val := fun e => hv2 (e ▸ hi)
        simp [pairVec, h1, h2]
      have heq := wires_agree_on_reach hfan
        (by simp only [oneEach, List.length_append, List.length_ofFn, N])
        (by simp only [oneEach, List.length_append, List.length_ofFn, N])
        hout_lt hagree C.output (mem_reach_self hout_lt)
      have ha1 := hrep u v1
      have ha2 := hrep u v2
      simp only [Circuit.eval] at ha1 ha2
      rw [heq, ha2] at ha1
      exact hu ha1.symm
    have hIrow_card : k + 1 ≤ Irow.card := by
      set miss := (Finset.univ : Finset (Fin (k + 2))).filter (fun u => u.val ∉ I)
      have hmiss_le : miss.card ≤ 1 := Finset.card_le_one.mpr fun a ha b hb =>
        hrow_miss a b (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
      have hcompl : (Finset.univ.filter (fun u : Fin (k + 2) => u.val ∈ I)).card + miss.card = k + 2 := by
        have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (k + 2))))
          (p := fun u => u.val ∈ I)
        simpa [miss] using this
      have hbij : (Finset.univ.filter (fun u : Fin (k + 2) => u.val ∈ I)).card ≤ Irow.card := by
        calc (Finset.univ.filter (fun u : Fin (k + 2) => u.val ∈ I)).card
            = ((Finset.univ.filter (fun u : Fin (k + 2) => u.val ∈ I)).image Fin.val).card :=
              (Finset.card_image_of_injective _ Fin.val_injective).symm
          _ ≤ Irow.card := Finset.card_le_card fun w hw => by
              rcases Finset.mem_image.mp hw with ⟨u, hu, rfl⟩
              exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hu).2, u.isLt⟩
      omega
    have hIcol_card : k ≤ Icol.card := by
      set miss := (Finset.univ : Finset (Fin (k + 1))).filter (fun v => (k + 2) + v.val ∉ I)
      have hmiss_le : miss.card ≤ 1 := Finset.card_le_one.mpr fun a ha b hb =>
        hcol_miss a b (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
      have hcompl : (Finset.univ.filter (fun v : Fin (k + 1) => (k + 2) + v.val ∈ I)).card + miss.card = k + 1 := by
        have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (k + 1))))
          (p := fun v => (k + 2) + v.val ∈ I)
        simpa [miss] using this
      have hbij : (Finset.univ.filter (fun v : Fin (k + 1) => (k + 2) + v.val ∈ I)).card ≤ Icol.card := by
        have hinj : Function.Injective (fun v : Fin (k + 1) => (k + 2) + v.val) := fun a b h =>
          Fin.ext (by dsimp only at h; omega)
        calc (Finset.univ.filter (fun v : Fin (k + 1) => (k + 2) + v.val ∈ I)).card
            = ((Finset.univ.filter (fun v : Fin (k + 1) => (k + 2) + v.val ∈ I)).image
                (fun v => (k + 2) + v.val)).card := (Finset.card_image_of_injective _ hinj).symm
          _ ≤ Icol.card := Finset.card_le_card fun w hw => by
              rcases Finset.mem_image.mp hw with ⟨v, hv, rfl⟩
              exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hv).2, by omega⟩
      omega
    have hI_part : I.card = Irow.card + Icol.card := by
      have hdisj : Disjoint Irow Icol := Finset.disjoint_left.mpr fun w h1 h2 => by
        rw [Finset.mem_filter] at h1 h2; omega
      have hunion : Irow ∪ Icol = I := by
        ext w; simp only [Irow, Icol, Finset.mem_union, Finset.mem_filter]
        constructor
        · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
        · intro h; by_cases hlt : w < k + 2
          · exact Or.inl ⟨h, hlt⟩
          · exact Or.inr ⟨h, by omega⟩
      rw [← hunion, Finset.card_union_of_disjoint hdisj]
    have hslot := slot_count_ineq hfan hout_ge hout_lt
    have hslot4 : I.card + Lnot.card ≤ L.card + 1 := hslot.2.2.2.1
    have hslot5 : L.card ≤ C.gates.length := hslot.2.2.2.2
    have hsz : C.gates.length ≤ 2 * k + 1 := hsize
    have hLnot_le1 : Lnot.card ≤ 1 := by omega

    have hLnot_eq1 : Lnot.card = 1 := by
      by_contra hne1
      have hLnot0 : Lnot.card = 0 := by omega
      have hno_not : ∀ g ∈ L, ∀ h : g - N < C.gates.length, C.gates[g - N].op ≠ .not := by
        intro g hgL hgj hop
        have hmem : g ∈ Lnot := Finset.mem_filter.mpr ⟨hgL, by simp [isNotGate, hgj, hop, isNotOp]⟩
        have : 0 < Lnot.card := Finset.card_pos.mpr ⟨g, hmem⟩
        omega

      have hall_row : ∀ u : Fin (k + 1), u.val ∈ I := by
        intro u
        by_contra hnotin
        let v : Fin (k + 1) := ⟨if u.val = 0 then 1 else 0, by split_ifs <;> omega⟩
        have h1 : A ⟨u.val, by omega⟩ v = true := by
          have hu_lt := u.isLt
          simp only [A, decide_eq_true_eq]
          refine ⟨by omega, fun ⟨_, heq⟩ => ?_⟩
          simp only [v] at heq
          split_ifs at heq <;> omega
        have h2 : A ⟨k + 1, by omega⟩ v = false := by simp [A]
        have hle : ∀ i ∈ I, (oneEach (⟨u.val, by omega⟩ : Fin (k + 2)) v).getD i false ≤
            (oneEach (⟨k + 1, by omega⟩ : Fin (k + 2)) v).getD i false := by
          intro i hi
          rw [getInput_oneEach, getInput_oneEach]
          have hne : i ≠ u.val := fun e => hnotin (e ▸ hi)
          simp only [pairVec, hne, false_or]
          by_cases h' : i = (k + 2) + v.val <;> simp [h']
        have hm := wires_mono_of_no_not hfan
          (by simp only [oneEach, List.length_append, List.length_ofFn, N])
          (by simp only [oneEach, List.length_append, List.length_ofFn, N])
          hout_lt hno_not hle C.output (mem_reach_self hout_lt)
        have hr1 := hrep ⟨u.val, by omega⟩ v
        have hr2 := hrep ⟨k + 1, by omega⟩ v
        simp only [Circuit.eval] at hr1 hr2
        rw [hr1, hr2, h1, h2] at hm; exact Bool.noConfusion (bool_eq_false_of_le hm)
      have hall_col : ∀ v : Fin (k + 1), (k + 2) + v.val ∈ I := by
        intro v
        by_contra hnotin
        let u : Fin (k + 2) := ⟨if v.val = 0 then 1 else 0, by split_ifs <;> omega⟩
        let v0 : Fin (k + 1) := ⟨u.val, by simp [u]; split_ifs <;> omega⟩
        have h1 : A u v = true := by simp only [A, u]; split_ifs <;> simp <;> omega
        have h2 : A u v0 = false := by simp only [A, u, v0]; split_ifs <;> simp <;> omega
        have hle : ∀ i ∈ I, (oneEach u v).getD i false ≤ (oneEach u v0).getD i false := by
          intro i hi
          rw [getInput_oneEach, getInput_oneEach]
          have hne : i ≠ (k + 2) + v.val := fun e => hnotin (e ▸ hi)
          simp only [pairVec, hne, or_false]
          by_cases h' : i = u.val <;> simp [h']
        have hm := wires_mono_of_no_not hfan
          (by simp only [oneEach, List.length_append, List.length_ofFn, N])
          (by simp only [oneEach, List.length_append, List.length_ofFn, N])
          hout_lt hno_not hle C.output (mem_reach_self hout_lt)
        have hr1 := hrep u v
        have hr2 := hrep u v0
        simp only [Circuit.eval] at hr1 hr2
        rw [hr1, hr2, h1, h2] at hm; exact Bool.noConfusion (bool_eq_false_of_le hm)
      have hI_ge : 2 * k + 2 ≤ I.card := by
        have hsub1 : (Finset.univ.image (fun u : Fin (k + 1) => u.val)) ⊆ Irow := by
          intro w hw; rcases Finset.mem_image.mp hw with ⟨u, _, rfl⟩
          exact Finset.mem_filter.mpr ⟨hall_row u, by omega⟩
        have hsub2 : (Finset.univ.image (fun v : Fin (k + 1) => (k + 2) + v.val)) ⊆ Icol := by
          intro w hw; rcases Finset.mem_image.mp hw with ⟨v, _, rfl⟩
          exact Finset.mem_filter.mpr ⟨hall_col v, by omega⟩
        have hc1 : k + 1 ≤ Irow.card := by
          calc k + 1 = (Finset.univ.image (fun u : Fin (k + 1) => u.val)).card := by
                rw [Finset.card_image_of_injective _ Fin.val_injective]; simp
            _ ≤ Irow.card := Finset.card_le_card hsub1
        have hc2 : k + 1 ≤ Icol.card := by
          have hinj : Function.Injective (fun v : Fin (k + 1) => (k + 2) + v.val) :=
            fun a b h => Fin.ext (by dsimp only at h; omega)
          calc k + 1 = (Finset.univ.image (fun v : Fin (k + 1) => (k + 2) + v.val)).card := by
                rw [Finset.card_image_of_injective _ hinj]; simp
            _ ≤ Icol.card := Finset.card_le_card hsub2
        omega
      have htight0 : I.card + Lnot.card = L.card + 1 := by omega
      obtain ⟨T, hro, _, hnc, hev⟩ := extract_ftree hfan hout_ge hout_lt htight0
      have h0 : T.notCount = 0 := by rw [hnc]; exact hLnot0
      apply no_mono_tree_for_compl_id (k := k) (nr := k + 2) (by omega) (by omega) T hro h0
      intro u v
      have h1 := hrep ⟨u.val, by omega⟩ ⟨v.val, by omega⟩
      rw [hev _ (by simp only [oneEach, List.length_append, List.length_ofFn, N])] at h1
      have hcon : T.eval (fun i => (oneEach (⟨u.val, by omega⟩ : Fin (k + 2))
          (⟨v.val, by omega⟩ : Fin (k + 1))).getD i false) =
          T.eval (pairVec (k + 2) u.val v.val) :=
        FTree.eval_congr fun i _ => getInput_oneEach _ _ i
      rw [hcon] at h1
      simpa [A, show u.val ≠ k + 1 by omega, show u.val < k from u.isLt, Fin.ext_iff] using h1

    have htight : I.card + Lnot.card = L.card + 1 := by omega
    have hIrow_eq : Irow.card = k + 1 := by omega
    have hIcol_eq : Icol.card = k := by omega
    obtain ⟨T, hro, hlv, hnc, hev⟩ := extract_ftree hfan hout_ge hout_lt htight
    have hlvI : T.leaves = I := hlv
    have hT_not1 : T.notCount = 1 := by rw [hnc]; exact hLnot_eq1
    have hT_rep : ∀ (u : Fin (k + 2)) (v : Fin (k + 1)),
        T.eval (pairVec (k + 2) u.val v.val) = A u v := by
      intro u v
      have h1 := hrep u v
      rw [hev _ (by simp only [oneEach, List.length_append, List.length_ofFn, N])] at h1
      rw [FTree.eval_congr (v2 := pairVec (k + 2) u.val v.val) (fun i _ => getInput_oneEach u v i)] at h1
      exact h1

    have hex_vstar : ∃ vstar : Fin (k + 1), (k + 2) + vstar.val ∉ I := by
      by_contra hall
      push_neg at hall
      have hinj : Function.Injective (fun v : Fin (k + 1) => (k + 2) + v.val) :=
        fun a b h => Fin.ext (by dsimp only at h; omega)
      have hsub : Finset.univ.image (fun v : Fin (k + 1) => (k + 2) + v.val) ⊆ Icol := by
        intro w hw; rcases Finset.mem_image.mp hw with ⟨v, _, rfl⟩
        exact Finset.mem_filter.mpr ⟨hall v, by omega⟩
      have hc : k + 1 ≤ Icol.card := by
        calc k + 1 = (Finset.univ.image (fun v : Fin (k + 1) => (k + 2) + v.val)).card := by
              rw [Finset.card_image_of_injective _ hinj]; simp
          _ ≤ Icol.card := Finset.card_le_card hsub
      omega
    rcases hex_vstar with ⟨vstar, hvstar_out⟩
    have hvstar_eq : vstar.val = k := by
      by_contra hne
      have hvstar_lt : vstar.val < k := by omega
      let v1 : Fin (k + 1) := ⟨if vstar.val = 0 then 1 else 0, by split_ifs <;> omega⟩
      have hv1_lt : v1.val < k := by simp [v1]; split_ifs <;> omega
      have hv1_ne : v1 ≠ vstar := by
        intro e; have hval := congrArg Fin.val e; change (if vstar.val = 0 then 1 else 0) = vstar.val at hval
        split_ifs at hval <;> omega
      have hleft_val : ∀ u : Fin (k + 2), T.eval (leftVec u.val) = A u vstar := by
        intro u
        rw [← hT_rep u vstar]
        apply FTree.eval_congr
        intro w hw
        rw [hlv] at hw
        have hnw : w ≠ (k + 2) + vstar.val := fun e => hvstar_out (e ▸ hw)
        simp [leftVec, pairVec, hnw]

      let w1 := (k + 2) + v1.val
      have hneg : T.eval (Function.update (leftVec v1.val) w1 false) = true ∧
          T.eval (Function.update (leftVec v1.val) w1 true) = false := by
        have hf : Function.update (leftVec v1.val) w1 false = leftVec v1.val := by
          funext i; by_cases hi : i = w1
          · subst hi; simp [Function.update, leftVec, w1]
          · simp [Function.update, hi]
        have ht : Function.update (leftVec v1.val) w1 true = pairVec (k + 2) v1.val v1.val := by
          funext i; by_cases hi : i = w1
          · subst hi; simp [Function.update, pairVec, w1]
          · simp [Function.update, hi, leftVec, pairVec, w1]
        rw [hf, ht, hleft_val ⟨v1.val, by omega⟩, hT_rep ⟨v1.val, by omega⟩ v1]
        have hne' : v1.val ≠ vstar.val := fun e => hv1_ne (Fin.ext e)
        simp [A, hv1_lt, hne', show v1.val ≠ k + 1 by omega]
      have hpos : T.eval (Function.update (leftVec vstar.val) w1 false) = false ∧
          T.eval (Function.update (leftVec vstar.val) w1 true) = true := by
        have hf : Function.update (leftVec vstar.val) w1 false = leftVec vstar.val := by
          funext i; by_cases hi : i = w1
          · subst hi; simp [Function.update, leftVec, w1]; omega
          · simp [Function.update, hi]
        have ht : Function.update (leftVec vstar.val) w1 true = pairVec (k + 2) vstar.val v1.val := by
          funext i; by_cases hi : i = w1
          · subst hi; simp [Function.update, pairVec, w1]
          · simp [Function.update, hi, leftVec, pairVec, w1]
        rw [hf, ht, hleft_val ⟨vstar.val, by omega⟩, hT_rep ⟨vstar.val, by omega⟩ v1]
        have hne' : vstar.val ≠ v1.val := fun e => hv1_ne (Fin.ext e.symm)
        simp [A, hvstar_lt, hne', show vstar.val ≠ k + 1 by omega]
      rcases FTree.unate_of_readOnce hro w1 with hmono_w | hanti_w
      · have := hmono_w (leftVec v1.val); rw [hneg.1, hneg.2] at this
        exact Bool.noConfusion (bool_eq_false_of_le this)
      · have := hanti_w (leftVec vstar.val); rw [hpos.1, hpos.2] at this
        exact Bool.noConfusion (bool_eq_false_of_le this)
    have hyk_out : (k + 2) + k ∉ I := by simpa [hvstar_eq] using hvstar_out
    have hy_in : ∀ v : Fin k, (k + 2) + v.val ∈ I := by
      intro v; by_contra hnotin
      have heq := hcol_miss ⟨v.val, by omega⟩ vstar hnotin hvstar_out
      have hval : v.val = vstar.val := congrArg Fin.val heq
      omega
    have hleft_eval : ∀ u : Fin (k + 2), T.eval (leftVec u.val) = decide (u.val ≠ k + 1) := by
      intro u
      have hcon : T.eval (leftVec u.val) = T.eval (pairVec (k + 2) u.val k) :=
        FTree.eval_congr fun w hw => by
          rw [hlvI] at hw
          have hnw : w ≠ (k + 2) + k := fun e => hyk_out (e ▸ hw)
          simp [leftVec, pairVec, hnw]
      rw [hcon, hT_rep u ⟨k, by omega⟩]
      simp only [A]
      by_cases h1 : u.val < k
      · have hne1 : u.val ≠ k := by omega
        have hne2 : u.val ≠ k + 1 := by omega
        simp [h1, hne1, hne2]
      · by_cases h2 : u.val = k
        · simp [h2]
        · have h3 : u.val = k + 1 := by omega
          simp [h3]

    have hex_ustar : ∃ ustar : Fin (k + 2), ustar.val ∉ I := by
      by_contra hall
      push_neg at hall
      have hsub : Finset.univ.image (fun u : Fin (k + 2) => u.val) ⊆ Irow := by
        intro w hw; rcases Finset.mem_image.mp hw with ⟨u, _, rfl⟩
        exact Finset.mem_filter.mpr ⟨hall u, u.isLt⟩
      have hc : k + 2 ≤ Irow.card := by
        calc k + 2 = (Finset.univ.image (fun u : Fin (k + 2) => u.val)).card := by
              rw [Finset.card_image_of_injective _ Fin.val_injective]; simp
          _ ≤ Irow.card := Finset.card_le_card hsub
      omega
    rcases hex_ustar with ⟨ustar, hustar_out⟩
    have hustar_eq : ustar.val = k := by
      have hright_val : ∀ v : Fin (k + 1), T.eval (rightVec (k + 2) v.val) = A ustar v := by
        intro v
        rw [← hT_rep ustar v]
        apply FTree.eval_congr
        intro w hw
        rw [hlv] at hw
        have hnw : w ≠ ustar.val := fun e => hustar_out (e ▸ hw)
        simp [rightVec, pairVec, hnw]
      by_cases hu_lt : ustar.val < k
      ·
        let u1 : Fin (k + 2) := ⟨if ustar.val = 0 then 1 else 0, by split_ifs <;> omega⟩
        have hu1_lt : u1.val < k := by simp [u1]; split_ifs <;> omega
        have hu1_ne : u1.val ≠ ustar.val := by
          change (if ustar.val = 0 then 1 else 0) ≠ ustar.val
          split_ifs <;> omega
        have hneg : T.eval (Function.update (rightVec (k + 2) u1.val) u1.val false) = true ∧
            T.eval (Function.update (rightVec (k + 2) u1.val) u1.val true) = false := by
          have hf : Function.update (rightVec (k + 2) u1.val) u1.val false = rightVec (k + 2) u1.val := by
            funext i; by_cases hi : i = u1.val
            · subst hi; simp [Function.update, rightVec]
            · simp [Function.update, hi]
          have ht : Function.update (rightVec (k + 2) u1.val) u1.val true = pairVec (k + 2) u1.val u1.val := by
            funext i; by_cases hi : i = u1.val
            · subst hi; simp [Function.update, pairVec]
            · simp [Function.update, hi, rightVec, pairVec]
          rw [hf, ht, hright_val ⟨u1.val, by omega⟩, hT_rep u1 ⟨u1.val, by omega⟩]
          simp [A, hu_lt, hu1_lt, hu1_ne.symm, show ustar.val ≠ k + 1 by omega, show u1.val ≠ k + 1 by omega]
        have hpos : T.eval (Function.update (rightVec (k + 2) ustar.val) u1.val false) = false ∧
            T.eval (Function.update (rightVec (k + 2) ustar.val) u1.val true) = true := by
          have hf : Function.update (rightVec (k + 2) ustar.val) u1.val false = rightVec (k + 2) ustar.val := by
            funext i; by_cases hi : i = u1.val
            · subst hi; simp [Function.update, rightVec]; omega
            · simp [Function.update, hi]
          have ht : Function.update (rightVec (k + 2) ustar.val) u1.val true = pairVec (k + 2) u1.val ustar.val := by
            funext i; by_cases hi : i = u1.val
            · subst hi; simp [Function.update, pairVec]
            · simp [Function.update, hi, rightVec, pairVec]
          rw [hf, ht, hright_val ⟨ustar.val, by omega⟩, hT_rep u1 ⟨ustar.val, by omega⟩]
          simp [A, hu_lt, hu1_lt, hu1_ne, show ustar.val ≠ k + 1 by omega, show u1.val ≠ k + 1 by omega]
        rcases FTree.unate_of_readOnce hro u1.val with hmono_w | hanti_w
        · have := hmono_w (rightVec (k + 2) u1.val); rw [hneg.1, hneg.2] at this
          exact Bool.noConfusion (bool_eq_false_of_le this)
        · have := hanti_w (rightVec (k + 2) ustar.val); rw [hpos.1, hpos.2] at this
          exact Bool.noConfusion (bool_eq_false_of_le this)
      · by_cases hu_eq : ustar.val = k
        · exact hu_eq
        ·
          have hu_k1 : ustar.val = k + 1 := by omega
          have hcol_neg : ∀ v : Fin k, (k + 2) + v.val ∈ T.negLeaves := by
            intro v
            have hv_in : (k + 2) + v.val ∈ T.leaves := by rw [hlvI]; exact hy_in v
            rw [← FTree.pos_neg_partition (by omega), Finset.mem_union] at hv_in
            rcases hv_in with hpos | hneg
            · have hm := FTree.posLeaf_mono hro (by omega) hpos (leftVec v.val)
              have hf : Function.update (leftVec v.val) ((k + 2) + v.val) false = leftVec v.val := by
                funext i; by_cases hi : i = (k + 2) + v.val
                · subst hi; simp [Function.update, leftVec]
                · simp [Function.update, hi]
              have ht : Function.update (leftVec v.val) ((k + 2) + v.val) true = pairVec (k + 2) v.val v.val := by
                funext i; by_cases hi : i = (k + 2) + v.val
                · subst hi; simp [Function.update, pairVec]
                · simp [Function.update, hi, leftVec, pairVec]
              rw [hf, ht, hleft_eval ⟨v.val, by omega⟩, hT_rep ⟨v.val, by omega⟩ ⟨v.val, by omega⟩] at hm
              have hne1 : v.val ≠ k + 1 := by omega
              have hlt1 : v.val < k := v.isLt
              simp only [A, hne1, ne_eq, not_false_eq_true, decide_true, hlt1, and_self,
                not_true_eq_false, and_false, decide_false] at hm
              exact Bool.noConfusion (bool_eq_false_of_le hm)
            · exact hneg
          have hpos_no_col : ∀ w ∈ T.posLeaves, w < k + 2 := by
            intro w hw
            have hw_in : w ∈ I := by
              rw [← hlvI, ← FTree.pos_neg_partition (by omega)]
              exact Finset.mem_union_left _ hw
            have hw_lt : w < N := (Finset.mem_filter.mp hw_in).2
            by_contra hge
            have hvk : w - (k + 2) < k := by
              have hne : w ≠ (k + 2) + k := fun e => hyk_out (e ▸ hw_in)
              omega

            have hw_neg : w ∈ T.negLeaves := by
              have := hcol_neg ⟨w - (k + 2), hvk⟩
              rwa [show (k + 2) + (w - (k + 2)) = w by omega] at this

            let v : Fin k := ⟨w - (k + 2), hvk⟩
            have hv_eq : (k + 2) + v.val = w := by change (k + 2) + (w - (k + 2)) = w; omega
            have hm := FTree.posLeaf_mono hro (by omega) hw (leftVec v.val)
            have hf : Function.update (leftVec v.val) w false = leftVec v.val := by
              funext i; by_cases hi : i = w
              · subst hi; simp [Function.update, leftVec, v]; omega
              · simp [Function.update, hi]
            have ht : Function.update (leftVec v.val) w true = pairVec (k + 2) v.val v.val := by
              funext i; by_cases hi : i = w
              · subst hi; simp [Function.update, pairVec, hv_eq]
              · simp [Function.update, hi, leftVec, pairVec, hv_eq]
            rw [hf, ht, hleft_eval ⟨v.val, by omega⟩, hT_rep ⟨v.val, by omega⟩ ⟨v.val, by omega⟩] at hm
            have hne1 : v.val ≠ k + 1 := by omega
            have hlt1 : v.val < k := v.isLt
            simp only [A, hne1, ne_eq, not_false_eq_true, decide_true, hlt1, and_self,
              not_true_eq_false, and_false, decide_false] at hm
            exact Bool.noConfusion (bool_eq_false_of_le hm)
          obtain ⟨sub, H, _, hH_dep, hTeval⟩ := FTree.eval_factors_through_not hT_not1

          have hrow_pos : ∀ u : Fin (k + 1), u.val ∈ T.posLeaves := by
            intro u
            have hu_in : u.val ∈ T.leaves := by
              rw [hlvI]
              by_contra hnotin
              have heq := hrow_miss ⟨u.val, by omega⟩ ustar hnotin hustar_out
              have hval : u.val = ustar.val := congrArg Fin.val heq
              omega
            rw [← FTree.pos_neg_partition (by omega), Finset.mem_union] at hu_in
            rcases hu_in with hpos | hneg
            · exact hpos
            · let v : Fin (k + 1) := ⟨if u.val = 0 then 1 else 0, by split_ifs <;> omega⟩
              have hm := FTree.negLeaf_anti hro (by omega) hneg (rightVec (k + 2) v.val)
              have hf : Function.update (rightVec (k + 2) v.val) u.val false = rightVec (k + 2) v.val := by
                funext i; by_cases hi : i = u.val
                · subst hi; simp [Function.update, rightVec]; omega
                · simp [Function.update, hi]
              have ht : Function.update (rightVec (k + 2) v.val) u.val true = pairVec (k + 2) u.val v.val := by
                funext i; by_cases hi : i = u.val
                · subst hi; simp [Function.update, pairVec]
                · simp [Function.update, hi, rightVec, pairVec]
              rw [hf, ht, hright_val v, hT_rep ⟨u.val, by omega⟩ v] at hm
              have hA : A ⟨u.val, by omega⟩ v = true := by
                have hu_lt := u.isLt
                simp only [A, decide_eq_true_eq]
                refine ⟨by omega, fun ⟨_, heq⟩ => ?_⟩
                simp only [v] at heq
                split_ifs at heq <;> omega
              simp only [A, hu_k1, ne_eq, not_true_eq_false, false_and, decide_false, hA] at hm
              exact Bool.noConfusion (bool_eq_false_of_le hm)

          have hsub_ge : ∀ w ∈ sub.leaves, k + 2 ≤ w := by
            intro w hw
            by_contra hlt
            have hw_in : w ∈ I := by
              rw [← hlvI, ← FTree.pos_neg_partition (by omega)]
              exact Finset.mem_union_right _ (by rwa [← ‹sub.leaves = T.negLeaves›])
            have hne_k1 : w ≠ k + 1 := fun e => hustar_out (hu_k1 ▸ e ▸ hw_in)
            have hwk : w < k + 1 := by omega

            have hw_neg : w ∈ T.negLeaves := by rwa [← ‹sub.leaves = T.negLeaves›]
            let v : Fin (k + 1) := ⟨if w = 0 then 1 else 0, by split_ifs <;> omega⟩
            have hm := FTree.negLeaf_anti hro (by omega) hw_neg (rightVec (k + 2) v.val)
            have hf : Function.update (rightVec (k + 2) v.val) w false = rightVec (k + 2) v.val := by
              funext i; by_cases hi : i = w
              · subst hi; simp [Function.update, rightVec]; omega
              · simp [Function.update, hi]
            have ht : Function.update (rightVec (k + 2) v.val) w true = pairVec (k + 2) w v.val := by
              funext i; by_cases hi : i = w
              · subst hi; simp [Function.update, pairVec]
              · simp [Function.update, hi, rightVec, pairVec]
            rw [hf, ht, hright_val v, hT_rep ⟨w, by omega⟩ v] at hm
            have hA : A ⟨w, by omega⟩ v = true := by simp only [A, v]; split_ifs <;> simp <;> omega
            simp only [A, hu_k1, ne_eq, not_true_eq_false, false_and, decide_false, hA] at hm
            exact Bool.noConfusion (bool_eq_false_of_le hm)

          have hpig : ∃ v1 v2 : Fin 3, v1 ≠ v2 ∧
              sub.eval (rightVec (k + 2) v1.val) = sub.eval (rightVec (k + 2) v2.val) := by
            cases h0 : sub.eval (rightVec (k + 2) 0) <;>
            cases h1 : sub.eval (rightVec (k + 2) 1) <;>
            cases h2 : sub.eval (rightVec (k + 2) 2)
            · exact ⟨0, 1, by decide, by simpa [h0, h1]⟩
            · exact ⟨0, 1, by decide, by simpa [h0, h1]⟩
            · exact ⟨0, 2, by decide, by simpa [h0, h2]⟩
            · exact ⟨1, 2, by decide, by simpa [h1, h2]⟩
            · exact ⟨1, 2, by decide, by simpa [h1, h2]⟩
            · exact ⟨0, 2, by decide, by simpa [h0, h2]⟩
            · exact ⟨0, 1, by decide, by simpa [h0, h1]⟩
            · exact ⟨0, 1, by decide, by simpa [h0, h1]⟩
          rcases hpig with ⟨v1, v2, hvne, hsubeq⟩

          have hcoleq : ∀ u : Fin (k + 2), A u ⟨v1.val, by omega⟩ = A u ⟨v2.val, by omega⟩ := by
            intro u
            rw [← hT_rep u ⟨v1.val, by omega⟩, ← hT_rep u ⟨v2.val, by omega⟩, hTeval, hTeval]
            have hs1 : sub.eval (pairVec (k + 2) u.val v1.val) = sub.eval (rightVec (k + 2) v1.val) :=
              FTree.eval_congr fun w hw => by
                have := hsub_ge w hw
                simp [pairVec, rightVec, show w ≠ u.val by omega]
            have hs2 : sub.eval (pairVec (k + 2) u.val v2.val) = sub.eval (rightVec (k + 2) v2.val) :=
              FTree.eval_congr fun w hw => by
                have := hsub_ge w hw
                simp [pairVec, rightVec, show w ≠ u.val by omega]
            rw [hs1, hs2, hsubeq]
            apply hH_dep
            intro w hw
            have := hpos_no_col w hw
            simp [pairVec, show w ≠ (k + 2) + v1.val by omega, show w ≠ (k + 2) + v2.val by omega]
          have hcontra := hcoleq ⟨v1.val, by omega⟩
          have hne_val : v1.val ≠ v2.val := fun e => hvne (Fin.ext e)
          simp [A, show v1.val ≠ k + 1 by omega, show v1.val < k by omega, hne_val] at hcontra

    have hxk_out : k ∉ I := by simpa [hustar_eq] using hustar_out
    have hright_eval : ∀ v : Fin (k + 1), T.eval (rightVec (k + 2) v.val) = true := by
      intro v
      have hcon : T.eval (rightVec (k + 2) v.val) = T.eval (pairVec (k + 2) k v.val) :=
        FTree.eval_congr fun w hw => by
          rw [hlvI] at hw
          have hnw : w ≠ k := fun e => hxk_out (e ▸ hw)
          simp [rightVec, pairVec, hnw]
      rw [hcon, hT_rep ⟨k, by omega⟩ v]
      simp [A]
    have hzero_eval : T.eval (fun _ => false) = true := by
      rw [← hright_eval ⟨k, by omega⟩]
      apply FTree.eval_congr
      intro w hw
      rw [hlvI] at hw
      have hnw : w ≠ (k + 2) + k := fun e => hyk_out (e ▸ hw)
      simp [rightVec, hnw]

    have hpos_empty : T.posLeaves = ∅ := by
      ext w; simp only [Finset.notMem_empty, iff_false]
      intro hw
      have hw_in : w ∈ I := by
        rw [← hlvI, ← FTree.pos_neg_partition (by omega)]
        exact Finset.mem_union_left _ hw
      have hw_lt : w < N := (Finset.mem_filter.mp hw_in).2
      by_cases h1 : w < k
      · have hm := FTree.posLeaf_mono hro (by omega) hw (rightVec (k + 2) w)
        have hf : Function.update (rightVec (k + 2) w) w false = rightVec (k + 2) w := by
          funext i; by_cases hi : i = w
          · subst hi; simp [Function.update, rightVec]
          · simp [Function.update, hi]
        have ht : Function.update (rightVec (k + 2) w) w true = pairVec (k + 2) w w := by
          funext i; by_cases hi : i = w
          · subst hi; simp [Function.update, pairVec]
          · simp [Function.update, hi, rightVec, pairVec]
        rw [hf, ht, hright_eval ⟨w, by omega⟩, hT_rep ⟨w, by omega⟩ ⟨w, by omega⟩] at hm
        simp only [A, h1, show w ≠ k + 1 by omega, and_self, not_true_eq_false, and_false,
          decide_false] at hm
        exact Bool.noConfusion (bool_eq_false_of_le hm)
      · by_cases h2 : w = k
        · exact hxk_out (h2 ▸ hw_in)
        · by_cases h3 : w = k + 1
          · have hm := FTree.posLeaf_mono hro (by omega) hw (fun _ => false)
            have hf : Function.update (fun _ => false) w false = fun _ => false := by
              funext i; by_cases hi : i = w <;> simp [Function.update, hi]
            have ht : Function.update (fun _ => false) w true = leftVec (k + 1) := by
              funext i; by_cases hi : i = w <;> simp [Function.update, hi, leftVec, h3]
            rw [hf, ht, hzero_eval, hleft_eval ⟨k + 1, by omega⟩] at hm
            simp only [ne_eq, not_true_eq_false, decide_false] at hm
            exact Bool.noConfusion (bool_eq_false_of_le hm)
          · have hvk : w - (k + 2) < k := by
              have hne : w ≠ (k + 2) + k := fun e => hyk_out (e ▸ hw_in)
              omega
            let v : Fin k := ⟨w - (k + 2), hvk⟩
            have hv_eq : (k + 2) + v.val = w := by change (k + 2) + (w - (k + 2)) = w; omega
            have hm := FTree.posLeaf_mono hro (by omega) hw (leftVec v.val)
            have hf : Function.update (leftVec v.val) w false = leftVec v.val := by
              funext i; by_cases hi : i = w
              · subst hi; simp [Function.update, leftVec, v]; omega
              · simp [Function.update, hi]
            have ht : Function.update (leftVec v.val) w true = pairVec (k + 2) v.val v.val := by
              funext i; by_cases hi : i = w
              · subst hi; simp [Function.update, pairVec, hv_eq]
              · simp [Function.update, hi, leftVec, pairVec, hv_eq]
            rw [hf, ht, hleft_eval ⟨v.val, by omega⟩, hT_rep ⟨v.val, by omega⟩ ⟨v.val, by omega⟩] at hm
            have hne1 : v.val ≠ k + 1 := by omega
            have hlt1 : v.val < k := v.isLt
            simp only [A, hne1, ne_eq, not_false_eq_true, decide_true, hlt1, and_self,
              not_true_eq_false, and_false, decide_false] at hm
            exact Bool.noConfusion (bool_eq_false_of_le hm)

    obtain ⟨T0, rfl, hT0_0⟩ := FTree.not_at_top_of_posLeaves_empty hT_not1 hpos_empty
    have hT0_ro : T0.readOnce := hro
    have hT0_lv : T0.leaves = insert (k + 1)
        ((Finset.univ : Finset (Fin k)).image (fun u : Fin k => u.val) ∪
         (Finset.univ : Finset (Fin k)).image (fun u : Fin k => (k + 2) + u.val)) := by
      have hlv0 : T0.leaves = I := hlvI
      rw [hlv0]
      ext w; simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · intro hw
        have hw_lt : w < N := (Finset.mem_filter.mp hw).2
        by_cases h1 : w = k + 1
        · exact Or.inl h1
        · by_cases h2 : w < k
          · exact Or.inr (Or.inl ⟨⟨w, h2⟩, rfl⟩)
          · have hne1 : w ≠ k := fun e => hxk_out (e ▸ hw)
            have hne2 : w ≠ (k + 2) + k := fun e => hyk_out (e ▸ hw)
            exact Or.inr (Or.inr ⟨⟨w - (k + 2), by omega⟩, by change (k + 2) + (w - (k + 2)) = w; omega⟩)
      · rintro (rfl | ⟨u, rfl⟩ | ⟨v, rfl⟩)
        · by_contra hnotin
          have heq := hrow_miss ⟨k + 1, by omega⟩ ustar hnotin hustar_out
          have hval : k + 1 = ustar.val := congrArg Fin.val heq
          omega
        · by_contra hnotin
          have heq := hrow_miss ⟨u.val, by omega⟩ ustar hnotin hustar_out
          have hval : u.val = ustar.val := congrArg Fin.val heq
          omega
        · exact hy_in v
    have hxk1_mem : k + 1 ∈ T0.leaves := by rw [hT0_lv]; exact Finset.mem_insert_self _ _
    have hcard2 : 2 ≤ T0.leaves.card := by
      have h0in : 0 ∈ T0.leaves := by
        rw [hT0_lv]; exact Finset.mem_insert_of_mem (Finset.mem_union_left _
          (Finset.mem_image_of_mem _ (Finset.mem_univ (⟨0, by omega⟩ : Fin k))))
      have hsub : ({0, k + 1} : Finset ℕ) ⊆ T0.leaves := by
        intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption
      calc 2 = ({0, k + 1} : Finset ℕ).card := (Finset.card_pair (by omega)).symm
        _ ≤ T0.leaves.card := Finset.card_le_card hsub
    have hT0_k1 : T0.eval (leftVec (k + 1)) = true := by
      have := hleft_eval ⟨k + 1, by omega⟩
      simp [FTree.eval] at this; exact this
    obtain ⟨T', hro', h0', hlv', hT0_eq⟩ := peel_or_leaf hT0_ro hT0_0 hxk1_mem hcard2 hT0_k1
    have hlv'_eq : T'.leaves =
        (Finset.univ : Finset (Fin k)).image (fun u : Fin k => u.val) ∪
        (Finset.univ : Finset (Fin k)).image (fun u : Fin k => (k + 2) + u.val) := by
      rw [hlv', hT0_lv]
      ext w
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_union, Finset.mem_image,
        Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hne, rfl | h⟩
        · exact absurd rfl hne
        · exact h
      · intro h
        refine ⟨?_, Or.inr h⟩
        rcases h with ⟨u, rfl⟩ | ⟨v, rfl⟩ <;> omega
    have hrepT' : ∀ u ∈ (Finset.univ : Finset (Fin k)), ∀ v ∈ (Finset.univ : Finset (Fin k)),
        T'.eval (pairVec (k + 2) u.val v.val) = decide (u = v) := by
      intro u _ v _
      have h1 := hT_rep ⟨u.val, by omega⟩ ⟨v.val, by omega⟩
      simp only [FTree.eval, hT0_eq] at h1
      have hp : pairVec (k + 2) u.val v.val (k + 1) = false := by
        simp [pairVec]; omega
      rw [hp, Bool.false_or] at h1
      have ha : A ⟨u.val, by omega⟩ ⟨v.val, by omega⟩ = !(decide (u = v)) := by
        simp [A, show u.val ≠ k + 1 by omega, u.isLt, Fin.ext_iff]
      rw [ha] at h1
      exact Bool.not_inj h1
    have hleftT' : ∀ u ∈ (Finset.univ : Finset (Fin k)), T'.eval (leftVec u.val) = false := by
      intro u _
      have h1 := hleft_eval ⟨u.val, by omega⟩
      have hne1 : u.val ≠ k + 1 := by omega
      have hne2 : k + 1 ≠ u.val := by omega
      simp only [FTree.eval, hT0_eq, leftVec, hne1, hne2, ne_eq, not_false_eq_true,
        decide_false, decide_true, Bool.false_or, Bool.not_eq_true'] at h1
      exact h1
    have hrightT' : ∀ u ∈ (Finset.univ : Finset (Fin k)), T'.eval (rightVec (k + 2) u.val) = false := by
      intro u _
      have h1 := hright_eval ⟨u.val, by omega⟩
      simp only [FTree.eval, hT0_eq, rightVec, show k + 1 ≠ (k + 2) + u.val by omega,
        decide_false, Bool.false_or, Bool.not_eq_true'] at h1
      exact h1
    obtain ⟨σ, hinv, _, hT'eq⟩ := mono_tree_id_matching (k := k) (nr := k + 2) (by omega)
      T' hro' h0' Finset.univ ⟨⟨0, by omega⟩, Finset.mem_univ _⟩ hlv'_eq hrepT' hleftT' hrightT'
    refine ⟨σ, hinv, ?_⟩
    funext x y
    rw [hfeq x y, hev (List.ofFn x ++ List.ofFn y) (by simp only [List.length_append, List.length_ofFn, N])]
    simp only [FTree.eval, hT0_eq, hT'eq]
    have hme : matchEvalOn k (k + 2) Finset.univ σ (getInput x y) =
        matchEval k (k + 2) σ (getInput x y) := by
      simp [matchEvalOn, matchEval]
    change (!(getInput x y (k + 1) || matchEvalOn k (k + 2) Finset.univ σ (getInput x y))) =
      (!(x ⟨k + 1, by omega⟩ || matchFn k σ (fun u => x ⟨u.val, by omega⟩) (fun v => y ⟨v.val, by omega⟩)))
    rw [hme, getInput_left x y ⟨k + 1, by omega⟩, matchEval_eq_matchFn (by omega) (by omega) σ x y]
  · rintro ⟨σ, hinv, rfl⟩
    obtain ⟨T0, h0, hgc, hlv, hev⟩ := build_match_tree (nr := k + 2) (by omega) σ hinv
    let T : FTree := .not (.or (.leaf (k + 1)) T0)
    let N := (k + 2) + (k + 1)
    let compiled := compileTree N T
    let C : Circuit := ⟨compiled.1, compiled.2⟩
    have hlv_T : ∀ w ∈ T.leaves, w < N := by
      intro w hw
      simp only [T, FTree.leaves, Finset.mem_union, Finset.mem_singleton] at hw
      rcases hw with rfl | hw0
      · omega
      · have := hlv w hw0; omega
    refine ⟨C, ⟨?_, ?_⟩, ?_, ?_⟩
    · exact compileTree_fanInTwo N T
    · simp only [Circuit.size, C, compiled, compileTree_length, T, FTree.gateCount]; omega
    · intro u v
      have hlen : (oneEach u v).length = N := by simp only [oneEach, List.length_append, List.length_ofFn, N]
      have hce : C.eval (oneEach u v) = T.eval (fun i => (oneEach u v).getD i false) :=
        compileTree_circuit_eval T (oneEach u v) N hlen hlv_T
      rw [hce]
      simp only [T, FTree.eval, hev, getInput_oneEach]
      simp only [matchEval, pairVec, A]
      rw [Bool.eq_iff_iff]
      simp only [Bool.not_eq_true', Bool.or_eq_false_iff, decide_eq_false_iff_not,
        decide_eq_true_eq, not_exists]
      constructor
      · rintro ⟨hne1, hno⟩
        refine ⟨fun e => hne1 (Or.inl e.symm), fun ⟨hu, huv⟩ => ?_⟩
        exact hno ⟨u.val, hu⟩ (Or.inl ⟨Or.inl rfl, Or.inr (congrArg (k + 2 + ·) huv)⟩)
      · rintro ⟨hne1, hdiag⟩
        refine ⟨fun h => by rcases h with h | h; exact hne1 h.symm; omega, fun w hw => ?_⟩
        rcases hw with ⟨h1, h2⟩ | ⟨hne, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
        · rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
          · exact hdiag ⟨by omega, by omega⟩
          · omega
          · omega
          · omega
        · rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
          · exact hne (Fin.ext (by omega))
          · omega
          · omega
          · omega
        · rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
          · omega
          · omega
          · omega
          · exact hne (Fin.ext (by omega))
    · intro x y
      have hlen : (List.ofFn x ++ List.ofFn y).length = N := by simp only [List.length_append, List.length_ofFn, N]
      have hce : C.eval (List.ofFn x ++ List.ofFn y) = T.eval (getInput x y) :=
        compileTree_circuit_eval T (List.ofFn x ++ List.ofFn y) N hlen hlv_T
      rw [hce]
      simp only [T, FTree.eval, hev, getInput_left x y ⟨k + 1, by omega⟩,
        matchEval_eq_matchFn (by omega) (by omega) σ x y]
      rfl

private lemma eligible_iff_involution {k : ℕ} (hk : 7 ≤ k) (crown : Bool) :
    let nr := if crown then k + 2 else k
    let nc := if crown then k + 1 else k
    let A := fun (i : Fin nr) (j : Fin nc) => if crown then
      decide (i.val ≠ k + 1 ∧ ¬ (i.val < k ∧ i.val = j.val)) else decide (i.val = j.val)
    ∀ f : (Fin nr → Bool) → (Fin nc → Bool) → Bool,
      (∃ C : Circuit,
        (if crown then FanInTwo C ∧ C.size ≤ 2 * k + 1
         else Monotone2 C ∧ C.size + 1 ≤ 2 * k) ∧
        Represents A C ∧
        ∀ x y, f x y = C.eval (List.ofFn x ++ List.ofFn y)) ↔
      ∃ σ : Fin k → Fin k, (∀ u, σ (σ u) = u) ∧ f = canonicalFn k crown σ := by
  cases crown with
  | false => exact eligible_iff_involution_false hk
  | true => exact eligible_iff_involution_true hk

private def inTriple6 (s r : Fin 6) : Bool :=
  decide (r.val = s.val ∨ r.val = (s.val + 1) % 6 ∨ r.val = (s.val + 2) % 6)

private def phaseMate6 (b : Bool) (r : Fin 6) : Fin 6 :=
  if b then
    match r.val with
    | 0 => ⟨1, by omega⟩ | 1 => ⟨0, by omega⟩
    | 2 => ⟨3, by omega⟩ | 3 => ⟨2, by omega⟩
    | 4 => ⟨5, by omega⟩ | _ => ⟨4, by omega⟩
  else
    match r.val with
    | 0 => ⟨5, by omega⟩ | 5 => ⟨0, by omega⟩
    | 1 => ⟨2, by omega⟩ | 2 => ⟨1, by omega⟩
    | 3 => ⟨4, by omega⟩ | _ => ⟨3, by omega⟩

private lemma six_cycle_partial_involution (g : Fin 6 → Option (Fin 6))
    (hinv : ∀ r r', g r = some r' → g r' = some r ∧ r ≠ r')
    (hcov : ∀ s : Fin 6, ∃ a b : Fin 6, inTriple6 s a = true ∧ inTriple6 s b = true ∧ g a = some b) :
    ∃ b : Bool, ∀ r : Fin 6, g r = some (phaseMate6 b r) := by
  let cov (r : Fin 6) : Finset (Fin 6) :=
    match g r with
    | none => ∅
    | some r' => Finset.univ.filter (fun s => inTriple6 s r = true ∧ inTriple6 s r' = true)
  have hpair_le : ∀ r r' : Fin 6, r ≠ r' →
      (Finset.univ.filter (fun s : Fin 6 => inTriple6 s r = true ∧ inTriple6 s r' = true)).card ≤ 2 := by
    decide
  have hpair_eq2 : ∀ r r' : Fin 6, r ≠ r' →
      (Finset.univ.filter (fun s : Fin 6 => inTriple6 s r = true ∧ inTriple6 s r' = true)).card = 2 →
      r'.val = (r.val + 1) % 6 ∨ r.val = (r'.val + 1) % 6 := by
    decide
  have hcov_le : ∀ r : Fin 6, (cov r).card ≤ 2 := by
    intro r
    cases hgr : g r with
    | none => simp [cov, hgr]
    | some r' =>
      simp only [cov, hgr]
      exact hpair_le r r' (hinv r r' hgr).2
  have hsum_ge : 12 ≤ ∑ r : Fin 6, (cov r).card := by
    have hswap : ∑ r : Fin 6, (cov r).card =
        ∑ s : Fin 6, (Finset.univ.filter (fun r : Fin 6 => s ∈ cov r)).card := by
      have hcard_r : ∀ r : Fin 6, (cov r).card = ∑ s : Fin 6, if s ∈ cov r then 1 else 0 := by
        intro r
        rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
          Finset.sum_const, smul_eq_mul, mul_one]
      have hcard_s : ∀ s : Fin 6, (Finset.univ.filter (fun r : Fin 6 => s ∈ cov r)).card =
          ∑ r : Fin 6, if s ∈ cov r then 1 else 0 := by
        intro s
        rw [Finset.card_filter]
      simp_rw [hcard_r, hcard_s]
      exact Finset.sum_comm
    rw [hswap]
    have h2 : ∀ s : Fin 6, 2 ≤ (Finset.univ.filter (fun r : Fin 6 => s ∈ cov r)).card := by
      intro s
      obtain ⟨a, b, ha, hb, hab⟩ := hcov s
      have hba := (hinv a b hab).1
      have hne := (hinv a b hab).2
      have hma : s ∈ cov a := by simp [cov, hab, ha, hb]
      have hmb : s ∈ cov b := by simp [cov, hba, ha, hb]
      have hsub : ({a, b} : Finset (Fin 6)) ⊆ Finset.univ.filter (fun r : Fin 6 => s ∈ cov r) := by
        intro x hx; simp at hx; rcases hx with rfl | rfl <;> simp [hma, hmb]
      calc 2 = ({a, b} : Finset (Fin 6)).card := (Finset.card_pair hne).symm
        _ ≤ _ := Finset.card_le_card hsub
    calc 12 = ∑ _s : Fin 6, 2 := by decide
      _ ≤ ∑ s : Fin 6, (Finset.univ.filter (fun r : Fin 6 => s ∈ cov r)).card :=
        Finset.sum_le_sum fun s _ => h2 s
  have hcov_eq2 : ∀ r : Fin 6, (cov r).card = 2 := by
    intro r
    by_contra hne
    have hlt : (cov r).card < 2 := lt_of_le_of_ne (hcov_le r) hne
    have hsum_lt : ∑ x : Fin 6, (cov x).card < ∑ _x : Fin 6, 2 :=
      Finset.sum_lt_sum (fun x _ => hcov_le x) ⟨r, Finset.mem_univ r, hlt⟩
    have h12 : ∑ _x : Fin 6, 2 = 12 := by decide
    omega
  have hadj : ∀ r : Fin 6, ∃ r' : Fin 6, g r = some r' ∧
      (r'.val = (r.val + 1) % 6 ∨ r.val = (r'.val + 1) % 6) := by
    intro r
    cases hgr : g r with
    | none =>
      have := hcov_eq2 r
      simp [cov, hgr] at this
    | some r' =>
      have hc := hcov_eq2 r
      simp only [cov, hgr] at hc
      exact ⟨r', rfl, hpair_eq2 r r' (hinv r r' hgr).2 hc⟩
  obtain ⟨r0, hg0, hadj0⟩ := hadj 0
  have hr0 : r0 = 1 ∨ r0 = 5 := by
    fin_cases r0 <;> simp at hadj0 ⊢
  rcases hr0 with rfl | rfl
  · refine ⟨true, ?_⟩
    have hg1 : g 1 = some 0 := (hinv 0 1 hg0).1
    obtain ⟨r2, hg2, hadj2⟩ := hadj 2
    have hr2 : r2 = 3 := by
      have hne1 : r2 ≠ 1 := by
        intro e; subst e
        have := (hinv 2 1 hg2).1
        rw [hg1] at this; simp at this
      fin_cases r2 <;> simp_all
    subst hr2
    have hg3 : g 3 = some 2 := (hinv 2 3 hg2).1
    obtain ⟨r4, hg4, hadj4⟩ := hadj 4
    have hr4 : r4 = 5 := by
      have hne3 : r4 ≠ 3 := by
        intro e; subst e
        have := (hinv 4 3 hg4).1
        rw [hg3] at this; simp at this
      fin_cases r4 <;> simp_all
    subst hr4
    have hg5 : g 5 = some 4 := (hinv 4 5 hg4).1
    intro r; fin_cases r <;> simpa [phaseMate6]
  · refine ⟨false, ?_⟩
    have hg5 : g 5 = some 0 := (hinv 0 5 hg0).1
    obtain ⟨r1, hg1, hadj1⟩ := hadj 1
    have hr1 : r1 = 2 := by
      have hne0 : r1 ≠ 0 := by
        intro e; subst e
        have := (hinv 1 0 hg1).1
        rw [hg0] at this; simp at this
      fin_cases r1 <;> simp_all
    subst hr1
    have hg2 : g 2 = some 1 := (hinv 1 2 hg1).1
    obtain ⟨r3, hg3, hadj3⟩ := hadj 3
    have hr3 : r3 = 4 := by
      have hne2 : r3 ≠ 2 := by
        intro e; subst e
        have := (hinv 3 2 hg3).1
        rw [hg2] at this; simp at this
      fin_cases r3 <;> simp_all
    subst hr3
    have hg4 : g 4 = some 3 := (hinv 3 4 hg3).1
    intro r; fin_cases r <;> simpa [phaseMate6]

private def phaseInv {blocks : ℕ} (p : Fin blocks → Bool) (u : Fin (6 * blocks + 1)) :
    Fin (6 * blocks + 1) :=
  if h : u.val < 6 * blocks then
    let i : Fin blocks := ⟨u.val / 6, by omega⟩
    let r : Fin 6 := ⟨u.val % 6, by omega⟩
    ⟨6 * i.val + (phaseMate6 (p i) r).val, by have := (phaseMate6 (p i) r).isLt; omega⟩
  else u

private lemma phaseMate6_inv (b : Bool) (r : Fin 6) : phaseMate6 b (phaseMate6 b r) = r := by
  cases b <;> fin_cases r <;> rfl

private lemma phaseMate6_ne (b : Bool) (r : Fin 6) : phaseMate6 b r ≠ r := by
  cases b <;> fin_cases r <;> decide

private lemma phaseInv_block {blocks : ℕ} (p : Fin blocks → Bool) (i : Fin blocks) (r : Fin 6) :
    phaseInv p ⟨6 * i.val + r.val, by omega⟩ =
      ⟨6 * i.val + (phaseMate6 (p i) r).val, by have := (phaseMate6 (p i) r).isLt; omega⟩ := by
  unfold phaseInv
  have hlt : 6 * i.val + r.val < 6 * blocks := by omega
  simp only [hlt, ↓reduceDIte]
  have hdiv : (6 * i.val + r.val) / 6 = i.val := by omega
  have hmod : (6 * i.val + r.val) % 6 = r.val := by omega
  apply Fin.ext
  simp [hdiv, hmod]

private lemma phaseInv_inv {blocks : ℕ} (p : Fin blocks → Bool) (u : Fin (6 * blocks + 1)) :
    phaseInv p (phaseInv p u) = u := by
  by_cases h1 : u.val < 6 * blocks
  · set i : Fin blocks := ⟨u.val / 6, by omega⟩
    set r : Fin 6 := ⟨u.val % 6, by omega⟩
    have hueq : u = ⟨6 * i.val + r.val, by omega⟩ := Fin.ext (by simp [i, r]; omega)
    apply Fin.ext
    rw [hueq, phaseInv_block, phaseInv_block]
    simp [phaseMate6_inv]
  · have hfix : phaseInv p u = u := by unfold phaseInv; rw [dif_neg h1]
    rw [hfix, hfix]

private def phaseFn (blocks : ℕ) (crown : Bool) (p : Fin blocks → Bool) :
    (Fin (if crown then 6 * blocks + 1 + 2 else 6 * blocks + 1) → Bool) →
    (Fin (if crown then 6 * blocks + 1 + 1 else 6 * blocks + 1) → Bool) → Bool :=
  canonicalFn (6 * blocks + 1) crown (phaseInv p)

private lemma test_canonicalFn {k : ℕ} (crown : Bool) (σ : Fin k → Fin k)
    (probe : Fin (if crown then k + 2 else k) → Bool)
    (hlast : ∀ h : crown = true, probe ⟨k + 1, by simp [h]⟩ = false) :
    (canonicalFn k crown σ probe (fun _ => false) = !crown) ↔
      ∃ u : Fin k, u ≠ σ u ∧
        probe ⟨u.val, by cases crown <;> simp <;> omega⟩ = true ∧
        probe ⟨(σ u).val, by cases crown <;> simp <;> omega⟩ = true := by
  cases crown with
  | false =>
    simp [canonicalFn, matchFn]
  | true =>
    have h0 := hlast rfl
    simp [canonicalFn, matchFn, h0]

private lemma six_cycle_phase_char {blocks : ℕ} (hblocks : 1 ≤ blocks) (crown : Bool) :
    let k := 6 * blocks + 1
    let nr := if crown then k + 2 else k
    let nc := if crown then k + 1 else k
    let triple := fun (i : Fin blocks) (s : Fin 6) (u : Fin nr) =>
      decide (u.val = 6 * i.val + s.val ∨ u.val = 6 * i.val + (s.val + 1) % 6 ∨
        u.val = 6 * i.val + (s.val + 2) % 6)
    let litWord := fun (i : Fin blocks) (sgn : Bool) (u : Fin nr) =>
      decide (u.val = 6 * i.val ∨ u.val = 6 * i.val + (if sgn then 1 else 5))
    ∀ σ : Fin k → Fin k, (∀ u, σ (σ u) = u) →
      ((∀ i s, canonicalFn k crown σ (triple i s) (fun _ => false) = !crown) ↔
        ∃ p : Fin blocks → Bool, σ = phaseInv p) := by
  intro k nr nc triple litWord σ hinv
  constructor
  · intro hall
    have hblock : ∀ i : Fin blocks, ∃ b : Bool, ∀ r : Fin 6,
        σ ⟨6 * i.val + r.val, by omega⟩ =
          ⟨6 * i.val + (phaseMate6 b r).val, by have := (phaseMate6 b r).isLt; omega⟩ := by
      intro i
      let g : Fin 6 → Option (Fin 6) := fun r =>
        let w := σ ⟨6 * i.val + r.val, by omega⟩
        if h : 6 * i.val ≤ w.val ∧ w.val < 6 * i.val + 6 ∧ w.val ≠ 6 * i.val + r.val then
          some ⟨w.val - 6 * i.val, by omega⟩
        else none
      have hg_inv : ∀ r r', g r = some r' → g r' = some r ∧ r ≠ r' := by
        intro r r' hgr
        simp only [g] at hgr
        split_ifs at hgr with h
        · injection hgr with hr'
          have hr'_val : (σ ⟨6 * i.val + r.val, by omega⟩).val - 6 * i.val = r'.val :=
            congrArg Fin.val hr'
          have hge_w : 6 * i.val ≤ (σ ⟨6 * i.val + r.val, by omega⟩).val := h.1
          have hweq : σ ⟨6 * i.val + r.val, by omega⟩ = ⟨6 * i.val + r'.val, by omega⟩ :=
            Fin.ext (by change (σ ⟨6 * i.val + r.val, by omega⟩).val = 6 * i.val + r'.val; omega)
          have hinv_r : σ ⟨6 * i.val + r'.val, by omega⟩ = ⟨6 * i.val + r.val, by omega⟩ := by
            rw [← hweq, hinv]
          have hne : r ≠ r' := fun e => h.2.2 (by have := congrArg Fin.val e; omega)
          refine ⟨?_, hne⟩
          simp only [g, hinv_r]
          have hcond : 6 * i.val ≤ 6 * i.val + r.val ∧ 6 * i.val + r.val < 6 * i.val + 6 ∧
              6 * i.val + r.val ≠ 6 * i.val + r'.val := ⟨by omega, by omega, fun e => hne (Fin.ext (by omega))⟩
          rw [dif_pos hcond]
          congr 1; exact Fin.ext (by change 6 * i.val + r.val - 6 * i.val = r.val; omega)
      have hg_cov : ∀ s : Fin 6, ∃ a b : Fin 6,
          inTriple6 s a = true ∧ inTriple6 s b = true ∧ g a = some b := by
        intro s
        have hs := hall i s
        rw [test_canonicalFn crown σ (triple i s) (fun hc => by
          simp only [triple, decide_eq_false_iff_not]; omega)] at hs
        rcases hs with ⟨u, hne, hu1, hu2⟩
        simp only [triple, decide_eq_true_eq] at hu1 hu2
        have hu_ge : 6 * i.val ≤ u.val ∧ u.val < 6 * i.val + 6 := by
          rcases hu1 with h | h | h <;> omega
        have hsu_ge : 6 * i.val ≤ (σ u).val ∧ (σ u).val < 6 * i.val + 6 := by
          rcases hu2 with h | h | h <;> omega
        let a : Fin 6 := ⟨u.val - 6 * i.val, by omega⟩
        let b : Fin 6 := ⟨(σ u).val - 6 * i.val, by omega⟩
        refine ⟨a, b, ?_, ?_, ?_⟩
        · simp only [inTriple6, decide_eq_true_eq, a]; rcases hu1 with h | h | h <;> omega
        · simp only [inTriple6, decide_eq_true_eq, b]; rcases hu2 with h | h | h <;> omega
        · have hueq : (⟨6 * i.val + a.val, by omega⟩ : Fin k) = u := Fin.ext (by simp [a]; omega)
          simp only [g, hueq]
          have hcond : 6 * i.val ≤ (σ u).val ∧ (σ u).val < 6 * i.val + 6 ∧
              (σ u).val ≠ 6 * i.val + a.val :=
            ⟨hsu_ge.1, hsu_ge.2, fun e => hne (Fin.ext (by simp [a] at e; omega))⟩
          simp [hcond, b]
      obtain ⟨b, hb⟩ := six_cycle_partial_involution g hg_inv hg_cov
      refine ⟨b, fun r => ?_⟩
      have hbr := hb r
      simp only [g] at hbr
      split_ifs at hbr with h
      · injection hbr with heq
        apply Fin.ext
        have hval := congrArg Fin.val heq
        have hge_w : 6 * i.val ≤ (σ ⟨6 * i.val + r.val, by omega⟩).val := h.1
        change (σ ⟨6 * i.val + r.val, by omega⟩).val = 6 * i.val + (phaseMate6 b r).val
        simp only at hval
        omega
    choose p hp using hblock
    refine ⟨p, ?_⟩
    funext u
    by_cases hlt : u.val < 6 * blocks
    · let i : Fin blocks := ⟨u.val / 6, by omega⟩
      let r : Fin 6 := ⟨u.val % 6, by omega⟩
      have hueq : u = ⟨6 * i.val + r.val, by omega⟩ := Fin.ext (by simp [i, r]; omega)
      rw [hueq, hp i r, phaseInv_block]
    · have hu_last : u.val = 6 * blocks := by omega
      have hsu_last : (σ u).val = 6 * blocks := by
        by_contra hne
        have hlt' : (σ u).val < 6 * blocks := by omega
        let i : Fin blocks := ⟨(σ u).val / 6, by omega⟩
        let r : Fin 6 := ⟨(σ u).val % 6, by omega⟩
        have h1 : σ u = ⟨6 * i.val + r.val, by omega⟩ := Fin.ext (by simp [i, r]; omega)
        have h2 := congrArg σ h1
        rw [hinv u, hp i r] at h2
        have h3 := congrArg Fin.val h2
        have hlt6 := (phaseMate6 (p i) r).isLt
        have hi_lt : i.val < blocks := i.isLt
        simp only at h3
        omega
      apply Fin.ext
      rw [hsu_last]
      simp [phaseInv, hlt, hu_last]
  · rintro ⟨p, rfl⟩ i s
    rw [test_canonicalFn crown (phaseInv p) (triple i s) (fun hc => by
      simp only [triple, decide_eq_false_iff_not]; omega)]
    have hex : ∃ r : Fin 6, inTriple6 s r = true ∧ inTriple6 s (phaseMate6 (p i) r) = true := by
      cases p i <;> fin_cases s <;> decide
    rcases hex with ⟨r, hr1, hr2⟩
    have hpb_val : (phaseInv p ⟨6 * i.val + r.val, by omega⟩).val =
        6 * i.val + (phaseMate6 (p i) r).val :=
      congrArg Fin.val (phaseInv_block p i r)
    refine ⟨⟨6 * i.val + r.val, by omega⟩, ?_, ?_, ?_⟩
    · intro e
      have hval := congrArg Fin.val e
      rw [hpb_val] at hval
      simp only at hval
      exact phaseMate6_ne (p i) r (Fin.ext (by omega))
    · simp only [triple, decide_eq_true_eq]
      simp only [inTriple6, decide_eq_true_eq] at hr1
      rcases hr1 with h | h | h <;> omega
    · simp only [triple, decide_eq_true_eq, hpb_val]
      simp only [inTriple6, decide_eq_true_eq] at hr2
      rcases hr2 with h | h | h <;> omega

private lemma phaseFn_litWord {blocks : ℕ} (crown : Bool) (p : Fin blocks → Bool)
    (i : Fin blocks) (sgn : Bool) :
    let k := 6 * blocks + 1
    let nr := if crown then k + 2 else k
    let litWord := fun (i : Fin blocks) (sgn : Bool) (u : Fin nr) =>
      decide (u.val = 6 * i.val ∨ u.val = 6 * i.val + (if sgn then 1 else 5))
    (phaseFn blocks crown p (litWord i sgn) (fun _ => false) = !crown) ↔ p i = sgn := by
  intro k nr litWord
  rw [phaseFn, test_canonicalFn crown (phaseInv p) (litWord i sgn) (fun hc => by
    simp only [litWord, decide_eq_false_iff_not]; split_ifs <;> omega)]
  constructor
  · rintro ⟨u, hne, h1, h2⟩
    simp only [litWord, decide_eq_true_eq] at h1 h2
    have hcase : ∀ r : Fin 6, u.val = 6 * i.val + r.val → (r = 0 ∨ r = if sgn then 1 else 5) →
        (phaseMate6 (p i) r = 0 ∨ phaseMate6 (p i) r = if sgn then 1 else 5) → p i = sgn := by
      intro r hr hr1 hr2
      cases hp : p i <;> cases sgn <;> fin_cases r <;> simp_all [phaseMate6]
    rcases h1 with h1 | h1
    · have hu_eq : u = ⟨6 * i.val + (0 : Fin 6).val, by omega⟩ := Fin.ext (by simp [h1])
      have hpb_val : (phaseInv p u).val = 6 * i.val + (phaseMate6 (p i) 0).val := by
        rw [hu_eq]; exact congrArg Fin.val (phaseInv_block p i 0)
      rw [hpb_val] at h2
      apply hcase 0 (by simp [h1]) (Or.inl rfl)
      rcases h2 with h2 | h2
      · left; exact Fin.ext (by change (phaseMate6 (p i) 0).val = 0; omega)
      · right; apply Fin.ext; cases sgn <;> simp at h2 ⊢ <;> omega
    · let r0 : Fin 6 := if sgn then 1 else 5
      have hr0_val : r0.val = if sgn then 1 else 5 := by cases sgn <;> rfl
      have hu_eq : u = ⟨6 * i.val + r0.val, by omega⟩ := Fin.ext (by change u.val = 6 * i.val + r0.val; rw [hr0_val]; exact h1)
      have hpb_val : (phaseInv p u).val = 6 * i.val + (phaseMate6 (p i) r0).val := by
        rw [hu_eq]; exact congrArg Fin.val (phaseInv_block p i r0)
      rw [hpb_val] at h2
      apply hcase r0 (by rw [hr0_val]; exact h1) (Or.inr rfl)
      rcases h2 with h2 | h2
      · left; exact Fin.ext (by change (phaseMate6 (p i) r0).val = 0; omega)
      · right; apply Fin.ext; cases sgn <;> simp [r0] at h2 ⊢ <;> omega
  · intro hp
    have hpb_val : (phaseInv p ⟨6 * i.val + (0 : Fin 6).val, by omega⟩).val =
        6 * i.val + (phaseMate6 (p i) 0).val :=
      congrArg Fin.val (phaseInv_block p i 0)
    refine ⟨⟨6 * i.val + (0 : Fin 6).val, by omega⟩, ?_, ?_, ?_⟩
    · intro e
      have hval := congrArg Fin.val e
      rw [hpb_val] at hval
      simp only at hval
      exact phaseMate6_ne (p i) 0 (Fin.ext (by change (phaseMate6 (p i) 0).val = 0; omega))
    · simp [litWord]
    · simp only [litWord, decide_eq_true_eq, hpb_val, hp]
      right; cases sgn <;> simp [phaseMate6]

private def blockWeight {blocks m : ℕ} (hm : 6 * blocks ≤ m) (v : Fin m → Bool)
    (i : Fin blocks) : ℕ :=
  (Finset.univ.filter (fun r : Fin 6 => v ⟨6 * i.val + r.val, by omega⟩ = true)).card

private lemma sum_blockWeight_le {blocks m : ℕ} (hm : 6 * blocks ≤ m) (v : Fin m → Bool) :
    ∑ i : Fin blocks, blockWeight hm v i ≤ (Finset.univ.filter (fun u : Fin m => v u = true)).card := by
  let f : Fin blocks × Fin 6 → Fin m := fun ir => ⟨6 * ir.1.val + ir.2.val, by omega⟩
  have hfinj : Function.Injective f := by
    rintro ⟨i1, r1⟩ ⟨i2, r2⟩ h
    have hval := congrArg Fin.val h
    simp only [f] at hval
    have hi : i1 = i2 := Fin.ext (by omega)
    have hr : r1 = r2 := Fin.ext (by omega)
    exact Prod.ext hi hr
  set S := (Finset.univ : Finset (Fin blocks × Fin 6)).filter (fun ir => v (f ir) = true)
  have hsum : ∑ i : Fin blocks, blockWeight hm v i = S.card := by
    have hfiber : S.card = ∑ i : Fin blocks, (S.filter (fun ir => ir.1 = i)).card := by
      rw [← Finset.card_biUnion]
      · congr 1; ext ir; simp
      · intro i1 _ i2 _ hne
        exact Finset.disjoint_left.mpr fun x hx1 hx2 => by
          simp only [Finset.mem_filter] at hx1 hx2
          exact hne (hx1.2.symm.trans hx2.2)
    rw [hfiber]
    apply Finset.sum_congr rfl
    intro i _
    have hbij : (Finset.univ.filter (fun r : Fin 6 => v ⟨6 * i.val + r.val, by omega⟩ = true)).card =
        (S.filter (fun ir => ir.1 = i)).card := by
      apply Finset.card_bij (fun r _ => (i, r))
      · intro r hr; simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, f] at hr ⊢
        exact ⟨hr, trivial⟩
      · intro r1 _ r2 _ h; exact congrArg Prod.snd h
      · intro ir hir; simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, f] at hir
        rcases ir with ⟨i', r'⟩
        simp only at hir
        rcases hir with ⟨hv, rfl⟩
        exact ⟨r', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, rfl⟩
    exact hbij
  rw [hsum]
  calc S.card = (S.image f).card := (Finset.card_image_of_injective S hfinj).symm
    _ ≤ (Finset.univ.filter (fun u : Fin m => v u = true)).card := Finset.card_le_card fun u hu => by
        rcases Finset.mem_image.mp hu with ⟨ir, hir, rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hir).2⟩

private def heavyBlocks {blocks : ℕ} (crown : Bool)
    (x : Fin (if crown then 6 * blocks + 1 + 2 else 6 * blocks + 1) → Bool)
    (y : Fin (if crown then 6 * blocks + 1 + 1 else 6 * blocks + 1) → Bool) : Finset (Fin blocks) :=
  Finset.univ.filter (fun i : Fin blocks =>
    2 ≤ blockWeight (by cases crown <;> simp <;> omega) x i +
        blockWeight (by cases crown <;> simp <;> omega) y i)

private lemma phaseFn_depends_on_heavy_blocks {blocks : ℕ} (crown : Bool)
    (x : Fin (if crown then 6 * blocks + 1 + 2 else 6 * blocks + 1) → Bool)
    (y : Fin (if crown then 6 * blocks + 1 + 1 else 6 * blocks + 1) → Bool)
    (p1 p2 : Fin blocks → Bool)
    (hagree : ∀ i ∈ heavyBlocks crown x y, p1 i = p2 i) :
    phaseFn blocks crown p1 x y = phaseFn blocks crown p2 x y := by
  have hagree' : ∀ i : Fin blocks,
      2 ≤ blockWeight (by cases crown <;> simp <;> omega) x i +
          blockWeight (by cases crown <;> simp <;> omega) y i → p1 i = p2 i :=
    fun i hi => hagree i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
  have hmatch : ∀ (x' y' : Fin (6 * blocks + 1) → Bool),
      (∀ i : Fin blocks, 2 ≤ blockWeight (by omega) x' i + blockWeight (by omega) y' i → p1 i = p2 i) →
      matchFn (6 * blocks + 1) (phaseInv p1) x' y' = matchFn (6 * blocks + 1) (phaseInv p2) x' y' := by
    intro x' y' hag
    have hdir : ∀ q1 q2 : Fin blocks → Bool,
        (∀ i : Fin blocks, 2 ≤ blockWeight (by omega) x' i + blockWeight (by omega) y' i → q1 i = q2 i) →
        matchFn (6 * blocks + 1) (phaseInv q1) x' y' = true →
        matchFn (6 * blocks + 1) (phaseInv q2) x' y' = true := by
      intro q1 q2 hq hm
      simp only [matchFn, decide_eq_true_eq] at hm ⊢
      rcases hm with ⟨u, hdiag | ⟨hne, hx2 | hy2⟩⟩
      · exact ⟨u, Or.inl hdiag⟩
      · have hlt : u.val < 6 * blocks := by
          by_contra hge
          have : phaseInv q1 u = u := by simp [phaseInv, hge]
          exact hne this.symm
        let i : Fin blocks := ⟨u.val / 6, by omega⟩
        let r : Fin 6 := ⟨u.val % 6, by omega⟩
        have hueq : u = ⟨6 * i.val + r.val, by omega⟩ := Fin.ext (by simp [i, r]; omega)
        have hsub : ({r, phaseMate6 (q1 i) r} : Finset (Fin 6)) ⊆
            Finset.univ.filter (fun s : Fin 6 => x' ⟨6 * i.val + s.val, by omega⟩ = true) := by
          intro s hs; simp at hs
          rcases hs with rfl | rfl
          · simp [← hueq, hx2.1]
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            rw [hueq, phaseInv_block] at hx2; exact hx2.2
        have hbw : 2 ≤ blockWeight (by omega) x' i := by
          calc 2 = ({r, phaseMate6 (q1 i) r} : Finset (Fin 6)).card :=
                (Finset.card_pair (phaseMate6_ne (q1 i) r).symm).symm
            _ ≤ blockWeight (by omega) x' i := Finset.card_le_card hsub
        have hpi : q1 i = q2 i := hq i (by omega)
        refine ⟨u, Or.inr ?_⟩
        have hpeq : phaseInv q1 u = phaseInv q2 u := by
          apply Fin.ext
          rw [hueq, phaseInv_block, phaseInv_block]
          simp [hpi]
        rw [← hpeq]; exact ⟨hne, Or.inl hx2⟩
      · have hlt : u.val < 6 * blocks := by
          by_contra hge
          have : phaseInv q1 u = u := by simp [phaseInv, hge]
          exact hne this.symm
        let i : Fin blocks := ⟨u.val / 6, by omega⟩
        let r : Fin 6 := ⟨u.val % 6, by omega⟩
        have hueq : u = ⟨6 * i.val + r.val, by omega⟩ := Fin.ext (by simp [i, r]; omega)
        have hsub : ({r, phaseMate6 (q1 i) r} : Finset (Fin 6)) ⊆
            Finset.univ.filter (fun s : Fin 6 => y' ⟨6 * i.val + s.val, by omega⟩ = true) := by
          intro s hs; simp at hs
          rcases hs with rfl | rfl
          · simp [← hueq, hy2.1]
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            rw [hueq, phaseInv_block] at hy2; exact hy2.2
        have hbw : 2 ≤ blockWeight (by omega) y' i := by
          calc 2 = ({r, phaseMate6 (q1 i) r} : Finset (Fin 6)).card :=
                (Finset.card_pair (phaseMate6_ne (q1 i) r).symm).symm
            _ ≤ blockWeight (by omega) y' i := Finset.card_le_card hsub
        have hpi : q1 i = q2 i := hq i (by omega)
        refine ⟨u, Or.inr ?_⟩
        have hpeq : phaseInv q1 u = phaseInv q2 u := by
          apply Fin.ext
          rw [hueq, phaseInv_block, phaseInv_block]
          simp [hpi]
        rw [← hpeq]; exact ⟨hne, Or.inr hy2⟩
    rw [Bool.eq_iff_iff]
    exact ⟨hdir p1 p2 hag, hdir p2 p1 fun i hi => (hag i hi).symm⟩
  cases crown with
  | false =>
    exact hmatch x y hagree'
  | true =>
    simp only [phaseFn, canonicalFn]
    congr 2
    exact hmatch _ _ fun i hi => hagree' i hi

private lemma heavy_blocks_card_le {blocks : ℕ} (crown : Bool) {w : ℕ}
    (x : Fin (if crown then 6 * blocks + 1 + 2 else 6 * blocks + 1) → Bool)
    (y : Fin (if crown then 6 * blocks + 1 + 1 else 6 * blocks + 1) → Bool)
    (hw : (Finset.univ.filter (fun i => x i = true)).card +
          (Finset.univ.filter (fun i => y i = true)).card ≤ w) :
    2 * (heavyBlocks crown x y).card ≤ w := by
  have hmx : 6 * blocks ≤ (if crown then 6 * blocks + 1 + 2 else 6 * blocks + 1) := by
    cases crown <;> simp <;> omega
  have hmy : 6 * blocks ≤ (if crown then 6 * blocks + 1 + 1 else 6 * blocks + 1) := by
    cases crown <;> simp <;> omega
  have h1 : 2 * (heavyBlocks crown x y).card ≤
      ∑ i ∈ heavyBlocks crown x y, (blockWeight hmx x i + blockWeight hmy y i) := by
    calc 2 * (heavyBlocks crown x y).card = ∑ _i ∈ heavyBlocks crown x y, 2 := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun i hi => (Finset.mem_filter.mp hi).2
  have h2 : ∑ i ∈ heavyBlocks crown x y, (blockWeight hmx x i + blockWeight hmy y i) ≤
      (∑ i : Fin blocks, blockWeight hmx x i) + (∑ i : Fin blocks, blockWeight hmy y i) := by
    calc ∑ i ∈ heavyBlocks crown x y, (blockWeight hmx x i + blockWeight hmy y i)
        ≤ ∑ i : Fin blocks, (blockWeight hmx x i + blockWeight hmy y i) :=
          Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ = (∑ i : Fin blocks, blockWeight hmx x i) + (∑ i : Fin blocks, blockWeight hmy y i) :=
          Finset.sum_add_distrib
  have hx := sum_blockWeight_le hmx x
  have hy := sum_blockWeight_le hmy y
  exact le_trans h1 (le_trans h2 (le_trans (Nat.add_le_add hx hy) hw))

private lemma maj_agree_two (a1 a2 a3 b1 b2 b3 : Bool) :
    let ma := (a1 && a2) || (a2 && a3) || (a1 && a3)
    let mb := (b1 && b2) || (b2 && b3) || (b1 && b3)
    (a1 = ma ∧ b1 = mb) ∨ (a2 = ma ∧ b2 = mb) ∨ (a3 = ma ∧ b3 = mb) := by
  cases a1 <;> cases a2 <;> cases a3 <;> cases b1 <;> cases b2 <;> cases b3 <;> decide

private def litWordFn {blocks nr : ℕ} (i : Fin blocks) (sgn : Bool) (u : Fin nr) : Bool :=
  decide (u.val = 6 * i.val ∨ u.val = 6 * i.val + (if sgn then 1 else 5))

private def clauseX {blocks nr : ℕ} (L : List (Fin blocks × Bool)) (u : Fin nr) : Bool :=
  decide (∃ lb ∈ L, litWordFn lb.1 lb.2 u = true)

private lemma clauseX_weight_le {blocks nr : ℕ} (L : List (Fin blocks × Bool)) :
    (Finset.univ.filter (fun u : Fin nr => clauseX L u = true)).card ≤ 2 * L.length := by
  induction L with
  | nil => simp [clauseX]
  | cons lb tl ih =>
    have hsub : Finset.univ.filter (fun u : Fin nr => clauseX (lb :: tl) u = true) ⊆
        Finset.univ.filter (fun u : Fin nr => litWordFn lb.1 lb.2 u = true) ∪
        Finset.univ.filter (fun u : Fin nr => clauseX tl u = true) := by
      intro u hu
      simp only [clauseX, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq,
        List.mem_cons, Finset.mem_union] at hu ⊢
      rcases hu with ⟨x, rfl | hx, hxtrue⟩
      · exact Or.inl hxtrue
      · exact Or.inr ⟨x, hx, hxtrue⟩
    have hlit_le : (Finset.univ.filter (fun u : Fin nr => litWordFn lb.1 lb.2 u = true)).card ≤ 2 := by
      have hinj : Function.Injective (Fin.val : Fin nr → ℕ) := Fin.val_injective
      calc (Finset.univ.filter (fun u : Fin nr => litWordFn lb.1 lb.2 u = true)).card
          = ((Finset.univ.filter (fun u : Fin nr => litWordFn lb.1 lb.2 u = true)).image Fin.val).card :=
            (Finset.card_image_of_injective _ hinj).symm
        _ ≤ ({6 * lb.1.val, 6 * lb.1.val + (if lb.2 then 1 else 5)} : Finset ℕ).card := by
            apply Finset.card_le_card
            intro w hw; rcases Finset.mem_image.mp hw with ⟨u, hu, rfl⟩
            simp only [litWordFn, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at hu
            simp [hu]
        _ ≤ 2 := Finset.card_le_two
    calc (Finset.univ.filter (fun u : Fin nr => clauseX (lb :: tl) u = true)).card
        ≤ (Finset.univ.filter (fun u : Fin nr => litWordFn lb.1 lb.2 u = true) ∪
           Finset.univ.filter (fun u : Fin nr => clauseX tl u = true)).card := Finset.card_le_card hsub
      _ ≤ (Finset.univ.filter (fun u : Fin nr => litWordFn lb.1 lb.2 u = true)).card +
          (Finset.univ.filter (fun u : Fin nr => clauseX tl u = true)).card := Finset.card_union_le _ _
      _ ≤ 2 + 2 * tl.length := by omega
      _ = 2 * (lb :: tl).length := by simp; omega

private lemma phaseFn_clauseX {blocks : ℕ} (crown : Bool) (p : Fin blocks → Bool)
    (L : List (Fin blocks × Bool)) (hnd : (L.map Prod.fst).Nodup) :
    (phaseFn blocks crown p (clauseX L) (fun _ => false) = !crown) ↔
      ∃ lb ∈ L, p lb.1 = lb.2 := by
  rw [phaseFn, test_canonicalFn crown (phaseInv p) (clauseX L) (fun hc => by
    simp only [clauseX, litWordFn, decide_eq_false_iff_not, decide_eq_true_eq]
    rintro ⟨⟨i, sgn⟩, _, h | h⟩ <;> cases sgn <;> simp at h <;> omega)]
  constructor
  · rintro ⟨u, hne, h1, h2⟩
    simp only [clauseX, decide_eq_true_eq] at h1 h2
    rcases h1 with ⟨⟨i1, s1⟩, hmem1, hl1⟩
    rcases h2 with ⟨⟨i2, s2⟩, hmem2, hl2⟩
    simp only [litWordFn, decide_eq_true_eq] at hl1 hl2
    have hu_lt : u.val < 6 * blocks := by
      rcases hl1 with h | h
      · omega
      · cases s1 <;> simp at h <;> omega
    have hu_div : u.val / 6 = i1.val := by
      rcases hl1 with h | h
      · omega
      · cases s1 <;> simp at h <;> omega
    have hsu_div : (phaseInv p u).val / 6 = i1.val := by
      have hi1_lt : i1.val < blocks := i1.isLt
      have hueq : u = ⟨6 * i1.val + (u.val % 6), by omega⟩ :=
        Fin.ext (by change u.val = 6 * i1.val + u.val % 6; omega)
      have hbl := phaseInv_block p i1 ⟨u.val % 6, by omega⟩
      have hval := congrArg Fin.val hbl
      have hlt6 := (phaseMate6 (p i1) ⟨u.val % 6, by omega⟩).isLt
      rw [hueq, hval]; simp only; omega
    have hi_eq : i1 = i2 := Fin.ext (by
      have : (phaseInv p u).val / 6 = i2.val := by
        rcases hl2 with h | h
        · omega
        · cases s2 <;> simp at h <;> omega
      omega)
    subst hi_eq
    have hs_eq : s1 = s2 := by
      suffices ∀ L' : List (Fin blocks × Bool), (L'.map Prod.fst).Nodup →
          (i1, s1) ∈ L' → (i1, s2) ∈ L' → s1 = s2 from this L hnd hmem1 hmem2
      intro L'
      induction L' with
      | nil => intro _ h1'; simp at h1'
      | cons hd tl ih =>
        intro hnd' h1' h2'
        rcases hd with ⟨di, ds⟩
        simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd'
        simp only [List.mem_cons] at h1' h2'
        rcases h1' with h1' | h1' <;> rcases h2' with h2' | h2'
        · exact congrArg Prod.snd (h1'.trans h2'.symm)
        · cases h1'; exact absurd ⟨(i1, s2), h2', rfl⟩ hnd'.1
        · cases h2'; exact absurd ⟨(i1, s1), h1', rfl⟩ hnd'.1
        · exact ih hnd'.2 h1' h2'
    subst hs_eq
    refine ⟨(i1, s1), hmem1, ?_⟩
    have hlit := (phaseFn_litWord crown p i1 s1).mp
    apply hlit
    rw [phaseFn, test_canonicalFn crown (phaseInv p) _ (fun hc => by
      simp only [decide_eq_false_iff_not]; split_ifs <;> omega)]
    exact ⟨u, hne, by simp [hl1], by simp [hl2]⟩
  · rintro ⟨⟨i, sgn⟩, hmem, hp⟩
    have hlit := (phaseFn_litWord crown p i sgn).mpr hp
    rw [phaseFn, test_canonicalFn crown (phaseInv p) _ (fun hc => by
      simp only [decide_eq_false_iff_not]; split_ifs <;> omega)] at hlit
    rcases hlit with ⟨u, hne, h1, h2⟩
    refine ⟨u, hne, ?_, ?_⟩
    · simp only [clauseX, decide_eq_true_eq]
      exact ⟨(i, sgn), hmem, by simpa [litWordFn] using h1⟩
    · simp only [clauseX, decide_eq_true_eq]
      exact ⟨(i, sgn), hmem, by simpa [litWordFn] using h2⟩

private lemma baker_pixley {n : ℕ} (P : (Fin n → Bool) → Prop)
    (hclosed : ∀ a b c, P a → P b → P c →
      P (fun i => (a i && b i) || (b i && c i) || (a i && c i)))
    (hne : ∃ x0, P x0) (a : Fin n → Bool)
    (hpair : ∀ i j : Fin n, ∃ x, P x ∧ x i = a i ∧ x j = a j) : P a := by
  suffices hS : ∀ (m : ℕ) (S : Finset (Fin n)), S.card = m → ∃ x, P x ∧ ∀ i ∈ S, x i = a i by
    obtain ⟨x, hx, heq⟩ := hS n Finset.univ (by simp)
    have hxa : x = a := funext fun i => heq i (Finset.mem_univ i)
    rwa [← hxa]
  intro m
  induction m with
  | zero =>
    intro S hS
    rw [Finset.card_eq_zero.mp hS]
    rcases hne with ⟨x0, hx0⟩
    exact ⟨x0, hx0, by simp⟩
  | succ m ih =>
    intro S hS
    by_cases hm1 : m = 0
    · subst hm1
      rcases Finset.card_eq_one.mp hS with ⟨i, rfl⟩
      obtain ⟨x, hx, hxi, _⟩ := hpair i i
      exact ⟨x, hx, fun j hj => by rw [Finset.mem_singleton.mp hj]; exact hxi⟩
    · by_cases hm2 : m = 1
      · subst hm2
        rcases Finset.card_eq_two.mp hS with ⟨i, j, _, rfl⟩
        obtain ⟨x, hx, hxi, hxj⟩ := hpair i j
        refine ⟨x, hx, fun u hu => ?_⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl <;> assumption
      ·
        have hc3 : 3 ≤ S.card := by omega
        obtain ⟨i1, hi1⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
        obtain ⟨i2, hi2⟩ := Finset.card_pos.mp (by
          rw [Finset.card_erase_of_mem hi1]; omega : 0 < (S.erase i1).card)
        obtain ⟨i3, hi3⟩ := Finset.card_pos.mp (by
          rw [Finset.card_erase_of_mem hi2, Finset.card_erase_of_mem hi1]; omega :
          0 < ((S.erase i1).erase i2).card)
        have hi2_S : i2 ∈ S := (Finset.mem_erase.mp hi2).2
        have h12 : i2 ≠ i1 := (Finset.mem_erase.mp hi2).1
        have hi3_e1 : i3 ∈ S.erase i1 := (Finset.mem_erase.mp hi3).2
        have hi3_S : i3 ∈ S := (Finset.mem_erase.mp hi3_e1).2
        have h23 : i3 ≠ i2 := (Finset.mem_erase.mp hi3).1
        have h13 : i3 ≠ i1 := (Finset.mem_erase.mp hi3_e1).1
        obtain ⟨x1, hx1, heq1⟩ := ih (S.erase i1) (by rw [Finset.card_erase_of_mem hi1]; omega)
        obtain ⟨x2, hx2, heq2⟩ := ih (S.erase i2) (by rw [Finset.card_erase_of_mem hi2_S]; omega)
        obtain ⟨x3, hx3, heq3⟩ := ih (S.erase i3) (by rw [Finset.card_erase_of_mem hi3_S]; omega)
        refine ⟨fun i => (x1 i && x2 i) || (x2 i && x3 i) || (x1 i && x3 i),
          hclosed x1 x2 x3 hx1 hx2 hx3, fun i hi => ?_⟩
        by_cases h1 : i = i1
        · subst h1
          have h2 : x2 i = a i := heq2 i (Finset.mem_erase.mpr ⟨h12.symm, hi⟩)
          have h3 : x3 i = a i := heq3 i (Finset.mem_erase.mpr ⟨h13.symm, hi⟩)
          dsimp only; rw [h2, h3]; cases x1 i <;> cases a i <;> rfl
        · by_cases h2 : i = i2
          · subst h2
            have h1' : x1 i = a i := heq1 i (Finset.mem_erase.mpr ⟨h1, hi⟩)
            have h3 : x3 i = a i := heq3 i (Finset.mem_erase.mpr ⟨h23.symm, hi⟩)
            dsimp only; rw [h1', h3]; cases x2 i <;> cases a i <;> rfl
          · have h1' : x1 i = a i := heq1 i (Finset.mem_erase.mpr ⟨h1, hi⟩)
            have h2' : x2 i = a i := heq2 i (Finset.mem_erase.mpr ⟨h2, hi⟩)
            dsimp only; rw [h1', h2']; cases x3 i <;> cases a i <;> rfl

private lemma realize_from_clauses {n : ℕ} (hn : 0 < n) (P : (Fin n → Bool) → Prop)
    (crown : Bool) (w : ℕ) (h : ℕ)
    (clauses : List (List (Fin (n + h) × Bool)))
    (hnd : ∀ c ∈ clauses, (c.map Prod.fst).Nodup)
    (hlen : ∀ c ∈ clauses, 2 * c.length ≤ w)
    (hiff : ∀ a : Fin n → Bool, P a ↔
      ∃ p : Fin (n + h) → Bool,
        (∀ c ∈ clauses, ∃ lb ∈ c, p lb.1 = lb.2) ∧
        ∀ i : Fin n, a i = p (i.castAdd h)) :
    let blocks := n + h
    let k := 6 * blocks + 1
    let nr := if crown then k + 2 else k
    let nc := if crown then k + 1 else k
    let A := fun (i : Fin nr) (j : Fin nc) => if crown then
      decide (i.val ≠ k + 1 ∧ ¬ (i.val < k ∧ i.val = j.val)) else decide (i.val = j.val)
    let Fn := (Fin nr → Bool) → (Fin nc → Bool) → Bool
    let eligible := fun f : Fn => ∃ C : Circuit,
      (if crown then FanInTwo C ∧ C.size ≤ 2 * k + 1
       else Monotone2 C ∧ C.size + 1 ≤ 2 * k) ∧ Represents A C ∧
      ∀ x y, f x y = C.eval (List.ofFn x ++ List.ofFn y)
    let test := fun (f : Fn) (probe : Fin nr → Bool) => f probe (fun _ => false) = !crown
    let triple := fun (i : Fin blocks) (s : Fin 6) (u : Fin nr) =>
      decide (u.val = 6 * i.val + s.val ∨ u.val = 6 * i.val + (s.val + 1) % 6 ∨
        u.val = 6 * i.val + (s.val + 2) % 6)
    let litWord := fun (i : Fin blocks) (sgn : Bool) (u : Fin nr) =>
      decide (u.val = 6 * i.val ∨ u.val = 6 * i.val + (if sgn then 1 else 5))
    ∃ (q : ℕ) (X : Fin q → Fin nr → Bool) (Y : Fin q → Fin nc → Bool) (label : Fin q → Bool),
      (∀ j, (Finset.univ.filter (fun i => X j i = true)).card +
        (Finset.univ.filter (fun i => Y j i = true)).card ≤ w) ∧
      ∀ a : Fin n → Bool, P a ↔ ∃ f : Fn,
        eligible f ∧ (∀ i s, test f (triple i s)) ∧
        (∀ j, f (X j) (Y j) = label j) ∧
        ∀ i : Fin n, a i = decide (test f (litWord (i.castAdd h) true)) := by
  intro blocks k nr nc A Fn eligible test triple litWord
  refine ⟨clauses.length, fun j => clauseX clauses[j.val], fun _ _ => false, fun _ => !crown, ?_, ?_⟩
  · intro j
    have hy : (Finset.univ.filter (fun _ : Fin nc => (false : Bool) = true)).card = 0 := by simp
    rw [hy, add_zero]
    exact le_trans (clauseX_weight_le clauses[j.val]) (hlen clauses[j.val] (List.getElem_mem j.isLt))
  · intro a
    rw [hiff a]
    have hblocks : 1 ≤ blocks := by omega
    have hk7 : 7 ≤ k := by omega
    constructor
    · rintro ⟨p, hp_sat, hp_read⟩
      refine ⟨phaseFn blocks crown p, ?_, ?_, ?_, ?_⟩
      · exact (eligible_iff_involution hk7 crown (phaseFn blocks crown p)).mpr
          ⟨phaseInv p, phaseInv_inv p, rfl⟩
      · exact (six_cycle_phase_char hblocks crown (phaseInv p) (phaseInv_inv p)).mpr ⟨p, rfl⟩
      · intro j
        exact (phaseFn_clauseX crown p clauses[j.val]
          (hnd _ (List.getElem_mem j.isLt))).mpr (hp_sat _ (List.getElem_mem j.isLt))
      · intro i
        have hlt : test (phaseFn blocks crown p) (litWord (i.castAdd h) true) ↔ p (i.castAdd h) = true :=
          phaseFn_litWord crown p (i.castAdd h) true
        rw [hp_read i]
        cases hp : p (i.castAdd h)
        · have hf : ¬ test (phaseFn blocks crown p) (litWord (i.castAdd h) true) := by
            rw [hlt, hp]; decide
          simp [hf]
        · have ht : test (phaseFn blocks crown p) (litWord (i.castAdd h) true) := by
            rw [hlt, hp]
          simp [ht]
    · rintro ⟨f, helig, htri, hsam, hread⟩
      obtain ⟨σ, hinv, rfl⟩ := (eligible_iff_involution hk7 crown f).mp helig
      obtain ⟨p, rfl⟩ := (six_cycle_phase_char hblocks crown σ hinv).mp htri
      refine ⟨p, ?_, ?_⟩
      · intro c hc
        obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hc
        exact (phaseFn_clauseX crown p clauses[idx] (hnd _ hc)).mp (hsam ⟨idx, hidx⟩)
      · intro i
        have hr := hread i
        have hlt : test (canonicalFn k crown (phaseInv p)) (litWord (i.castAdd h) true) ↔
            p (i.castAdd h) = true :=
          phaseFn_litWord crown p (i.castAdd h) true
        rw [hr]
        cases hp : p (i.castAdd h)
        · have hf : ¬ test (canonicalFn k crown (phaseInv p)) (litWord (i.castAdd h) true) := by
            rw [hlt, hp]; decide
          simp [hf]
        · have ht : test (canonicalFn k crown (phaseInv p)) (litWord (i.castAdd h) true) := by
            rw [hlt, hp]
          simp [ht]

theorem main_proof : ∀ (n : Nat), 0 < n → ∀ (P : (Fin n → Bool) → Prop) (crown : Bool) (w : Nat),
  let realizes := ∃ h q : Nat,
    let blocks := n+h
    let k := 6*blocks+1
    let nr := if crown then k+2 else k
    let nc := if crown then k+1 else k
    let A := fun (i : Fin nr) (j : Fin nc) => if crown then
      decide (i.val ≠ k+1 ∧ ¬ (i.val < k ∧ i.val = j.val)) else decide (i.val = j.val)
    let Fn := (Fin nr → Bool) → (Fin nc → Bool) → Bool
    let eligible := fun f : Fn => ∃ C : Circuit,
      (if crown then FanInTwo C ∧ C.size ≤ 2*k+1
       else Monotone2 C ∧ C.size+1 ≤ 2*k) ∧ Represents A C ∧
      ∀ x y, f x y = C.eval (List.ofFn x ++ List.ofFn y)
    let test := fun (f : Fn) (probe : Fin nr → Bool) => f probe (fun _ => false) = !crown
    let triple := fun (i : Fin blocks) (s : Fin 6) (u : Fin nr) =>
      decide (u.val = 6*i.val+s.val ∨ u.val = 6*i.val+(s.val+1)%6 ∨ u.val = 6*i.val+(s.val+2)%6)
    let litWord := fun (i : Fin blocks) (sgn : Bool) (u : Fin nr) =>
      decide (u.val = 6*i.val ∨ u.val = 6*i.val+(if sgn then 1 else 5))
    ∃ (X : Fin q → Fin nr → Bool) (Y : Fin q → Fin nc → Bool) (label : Fin q → Bool),
      (∀ j, (Finset.univ.filter (fun i => X j i = true)).card +
        (Finset.univ.filter (fun i => Y j i = true)).card ≤ w) ∧
      ∀ a : Fin n → Bool, P a ↔ ∃ f : Fn,
        eligible f ∧ (∀ i s, test f (triple i s)) ∧
        (∀ j, f (X j) (Y j) = label j) ∧
        ∀ i : Fin n, a i = decide (test f (litWord (i.castAdd h) true))
  let empty := ∀ a, ¬ P a
  let constant := empty ∨ ∀ a, P a
  let box := empty ∨ ∃ allow : Fin n → Bool → Bool, ∀ a, P a ↔ ∀ i, allow i (a i) = true
  let maj := fun (a b c : Fin n → Bool) (i : Fin n) =>
    (a i && b i) || (b i && c i) || (a i && c i)
  let closed := ∀ a b c, P a → P b → P c → P (maj a b c)
  realizes ↔ (if w < 2 then constant else if w < 4 then box else if w < 6 then closed else True) := by
  intro n hn P crown w realizes empty constant box maj closed
  constructor
  ·
    rintro ⟨h, q, X, Y, label, hw, hP⟩
    let blocks := n + h
    have hblocks : 1 ≤ blocks := by omega
    have hk7 : 7 ≤ 6 * blocks + 1 := by omega

    have hP_phase : ∀ a : Fin n → Bool, P a ↔
        ∃ p : Fin blocks → Bool,
          (∀ j : Fin q, phaseFn blocks crown p (X j) (Y j) = label j) ∧
          ∀ i : Fin n, a i = p (i.castAdd h) := by
      intro a
      rw [hP a]
      constructor
      · rintro ⟨f, helig, htri, hsam, hread⟩
        obtain ⟨σ, hinv, rfl⟩ := (eligible_iff_involution hk7 crown f).mp helig
        obtain ⟨p, rfl⟩ := (six_cycle_phase_char hblocks crown σ hinv).mp htri
        refine ⟨p, hsam, fun i => ?_⟩
        have hr := hread i
        have hlt := phaseFn_litWord crown p (i.castAdd h) true
        unfold phaseFn at hlt
        dsimp only at hlt hr
        rw [hr]
        cases hp : p (i.castAdd h)
        · exact decide_eq_false (by rw [hlt, hp]; decide)
        · exact decide_eq_true (by rw [hlt, hp])
      · rintro ⟨p, hsam, hread⟩
        refine ⟨phaseFn blocks crown p,
          (eligible_iff_involution hk7 crown _).mpr ⟨phaseInv p, phaseInv_inv p, rfl⟩,
          (six_cycle_phase_char hblocks crown _ (phaseInv_inv p)).mpr ⟨p, rfl⟩,
          hsam, fun i => ?_⟩
        have hlt := phaseFn_litWord crown p (i.castAdd h) true
        dsimp only at hlt
        rw [hread i]
        cases hp : p (i.castAdd h)
        · exact (decide_eq_false (by dsimp only; rw [hlt, hp]; decide)).symm
        · exact (decide_eq_true (by dsimp only; rw [hlt, hp])).symm
    split_ifs with hw2 hw4 hw6
    ·
      by_cases hemp : empty
      · exact Or.inl hemp
      · right
        simp only [empty, not_forall, not_not] at hemp
        rcases hemp with ⟨a0, ha0⟩
        obtain ⟨p0, hp0, _⟩ := (hP_phase a0).mp ha0
        intro a
        rw [hP_phase a]
        let p : Fin blocks → Bool := fun idx =>
          if hlt : idx.val < n then a ⟨idx.val, hlt⟩ else false
        refine ⟨p, fun j => ?_, fun i => by simp [p, i.isLt]⟩
        rw [← hp0 j]
        apply phaseFn_depends_on_heavy_blocks crown (X j) (Y j) p p0
        intro i hi
        have hcard := heavy_blocks_card_le crown (X j) (Y j) (hw j)
        have hpos : 1 ≤ (heavyBlocks crown (X j) (Y j)).card :=
          Finset.card_pos.mpr ⟨i, hi⟩
        omega
    ·
      by_cases hemp : empty
      · exact Or.inl hemp
      · right
        simp only [empty, not_forall, not_not] at hemp
        rcases hemp with ⟨a0, ha0⟩
        obtain ⟨p0, hp0, _⟩ := (hP_phase a0).mp ha0
        classical
        let allow : Fin n → Bool → Bool := fun i b => decide (∃ x, P x ∧ x i = b)
        refine ⟨allow, fun a => ?_⟩
        constructor
        · intro ha i
          simp only [allow, decide_eq_true_eq]
          exact ⟨a, ha, rfl⟩
        · intro hall
          have hex : ∀ i : Fin n, ∃ pi : Fin blocks → Bool,
              (∀ j, phaseFn blocks crown pi (X j) (Y j) = label j) ∧ pi (i.castAdd h) = a i := by
            intro i
            have hi := hall i
            simp only [allow, decide_eq_true_eq] at hi
            rcases hi with ⟨x, hx, hxi⟩
            obtain ⟨pi, hpi, hread⟩ := (hP_phase x).mp hx
            exact ⟨pi, hpi, (hread i).symm.trans hxi⟩
          choose pi hpi_sat hpi_val using hex
          rw [hP_phase a]
          let p : Fin blocks → Bool := fun idx =>
            if hlt : idx.val < n then a ⟨idx.val, hlt⟩ else p0 idx
          refine ⟨p, fun j => ?_, fun i => by simp [p, i.isLt]⟩
          set S := heavyBlocks crown (X j) (Y j)
          have hcard : S.card ≤ 1 := by
            have := heavy_blocks_card_le crown (X j) (Y j) (hw j)
            change 2 * S.card ≤ w at this
            omega
          by_cases hS : S.Nonempty
          · rcases Finset.card_eq_one.mp (le_antisymm hcard (Finset.card_pos.mpr hS)) with ⟨b, hb⟩
            by_cases hbn : b.val < n
            · let i0 : Fin n := ⟨b.val, hbn⟩
              rw [← hpi_sat i0 j]
              apply phaseFn_depends_on_heavy_blocks crown (X j) (Y j) p (pi i0)
              intro idx hidx
              have hmem : idx ∈ S := hidx
              rw [hb, Finset.mem_singleton] at hmem
              have hcast : i0.castAdd h = b := Fin.ext rfl
              rw [hmem]
              simp only [p, hbn, ↓reduceDIte]
              rw [← hpi_val i0, hcast]
            · rw [← hp0 j]
              apply phaseFn_depends_on_heavy_blocks crown (X j) (Y j) p p0
              intro idx hidx
              have hmem : idx ∈ S := hidx
              rw [hb, Finset.mem_singleton] at hmem
              rw [hmem]
              simp [p, hbn]
          · rw [← hp0 j]
            apply phaseFn_depends_on_heavy_blocks crown (X j) (Y j) p p0
            intro idx hidx
            exact absurd ⟨idx, hidx⟩ hS
    ·
      intro a1 a2 a3 ha1 ha2 ha3
      obtain ⟨p1, hp1, hr1⟩ := (hP_phase a1).mp ha1
      obtain ⟨p2, hp2, hr2⟩ := (hP_phase a2).mp ha2
      obtain ⟨p3, hp3, hr3⟩ := (hP_phase a3).mp ha3
      rw [hP_phase (maj a1 a2 a3)]
      let pm : Fin blocks → Bool := fun idx =>
        (p1 idx && p2 idx) || (p2 idx && p3 idx) || (p1 idx && p3 idx)
      refine ⟨pm, fun j => ?_, fun i => by simp [maj, pm, hr1 i, hr2 i, hr3 i]⟩
      set S := heavyBlocks crown (X j) (Y j)
      have hcard : S.card ≤ 2 := by
        have := heavy_blocks_card_le crown (X j) (Y j) (hw j)
        change 2 * S.card ≤ w at this
        omega

      have hex2 : ∃ u v : Fin blocks, ∀ idx ∈ S, idx = u ∨ idx = v := by
        by_cases h0 : S.card = 0
        · refine ⟨⟨0, by omega⟩, ⟨0, by omega⟩, fun idx hidx => ?_⟩
          rw [Finset.card_eq_zero.mp h0] at hidx; simp at hidx
        · by_cases h1 : S.card = 1
          · rcases Finset.card_eq_one.mp h1 with ⟨u, hu⟩
            exact ⟨u, u, fun idx hidx => Or.inl (Finset.mem_singleton.mp (hu ▸ hidx))⟩
          · have h2 : S.card = 2 := by omega
            rcases Finset.card_eq_two.mp h2 with ⟨u, v, _, huv⟩
            refine ⟨u, v, fun idx hidx => ?_⟩
            rw [huv, Finset.mem_insert, Finset.mem_singleton] at hidx
            exact hidx
      rcases hex2 with ⟨u, v, huv⟩
      rcases maj_agree_two (p1 u) (p2 u) (p3 u) (p1 v) (p2 v) (p3 v) with ⟨h1u, h1v⟩ | ⟨h2u, h2v⟩ | ⟨h3u, h3v⟩
      · rw [← hp1 j]
        apply phaseFn_depends_on_heavy_blocks crown (X j) (Y j) pm p1
        intro idx hidx
        rcases huv idx hidx with rfl | rfl
        · exact h1u.symm
        · exact h1v.symm
      · rw [← hp2 j]
        apply phaseFn_depends_on_heavy_blocks crown (X j) (Y j) pm p2
        intro idx hidx
        rcases huv idx hidx with rfl | rfl
        · exact h2u.symm
        · exact h2v.symm
      · rw [← hp3 j]
        apply phaseFn_depends_on_heavy_blocks crown (X j) (Y j) pm p3
        intro idx hidx
        rcases huv idx hidx with rfl | rfl
        · exact h3u.symm
        · exact h3v.symm
  ·

    have hrealize_empty : empty → realizes := by
      intro hemp
      have h := realize_from_clauses hn P crown w 0 [[]]
        (by simp) (by simp) (fun a => by simp [hemp a])
      rcases h with ⟨q, X, Y, label, hw, hP⟩
      exact ⟨0, q, X, Y, label, hw, hP⟩
    split_ifs with hw2 hw4 hw6
    ·
      rintro (hemp | huniv)
      · exact hrealize_empty hemp
      · have h := realize_from_clauses hn P crown w 0 []
          (by simp) (by simp) (fun a => by
            simp only [huniv a, List.not_mem_nil, false_implies, implies_true, true_and, true_iff]
            exact ⟨fun i => a ⟨i.val, by omega⟩, fun i => by simp⟩)
        rcases h with ⟨q, X, Y, label, hw, hP⟩
        exact ⟨0, q, X, Y, label, hw, hP⟩
    ·
      rintro (hemp | ⟨allow, hallow⟩)
      · exact hrealize_empty hemp
      · let bad : List (Fin n × Bool) :=
          ((Finset.univ : Finset (Fin n × Bool)).filter (fun ib => allow ib.1 ib.2 = false)).toList
        let clauses : List (List (Fin (n + 0) × Bool)) :=
          bad.map (fun ib => [(ib.1.castAdd 0, !ib.2)])
        have h := realize_from_clauses hn P crown w 0 clauses
          (by intro c hc; rw [List.mem_map] at hc; rcases hc with ⟨ib, _, rfl⟩; simp)
          (by intro c hc; rw [List.mem_map] at hc; rcases hc with ⟨ib, _, rfl⟩; simp; omega)
          (fun a => by
            rw [hallow a]
            constructor
            · intro ha
              refine ⟨fun i => a ⟨i.val, by omega⟩, ?_, fun i => by simp⟩
              intro c hc
              rw [List.mem_map] at hc
              rcases hc with ⟨⟨i, b⟩, hib, rfl⟩
              have hbad : allow i b = false := by
                have := Finset.mem_toList.mp hib
                exact (Finset.mem_filter.mp this).2
              refine ⟨(i.castAdd 0, !b), List.mem_cons_self, ?_⟩
              have hai := ha i
              cases hb : b <;> cases h : a i <;> simp_all
            · rintro ⟨p, hp_sat, hp_read⟩ i
              by_contra hne
              have hf : allow i (a i) = false := by cases h : allow i (a i) <;> simp_all
              have hmem : (i, a i) ∈ bad :=
                Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf⟩)
              have hc : [(i.castAdd 0, !(a i))] ∈ clauses := List.mem_map_of_mem hmem
              rcases hp_sat _ hc with ⟨lb, hlb, hplb⟩
              simp only [List.mem_singleton] at hlb
              subst hlb
              rw [← hp_read i] at hplb
              cases a i <;> simp at hplb)
        rcases h with ⟨q, X, Y, label, hw, hP⟩
        exact ⟨0, q, X, Y, label, hw, hP⟩
    ·
      intro hcl
      by_cases hemp : empty
      · exact hrealize_empty hemp
      · simp only [empty, not_forall, not_not] at hemp
        classical
        let bad2 : List ((Fin n × Bool) × (Fin n × Bool)) :=
          ((Finset.univ : Finset ((Fin n × Bool) × (Fin n × Bool))).filter
            (fun q => (q.1.1 ≠ q.2.1 ∨ q.1.2 = q.2.2) ∧
              ¬ ∃ x, P x ∧ x q.1.1 = q.1.2 ∧ x q.2.1 = q.2.2)).toList
        let mkClause : ((Fin n × Bool) × (Fin n × Bool)) → List (Fin (n + 0) × Bool) := fun q =>
          if q.1.1 = q.2.1 then [(q.1.1.castAdd 0, !q.1.2)]
          else [(q.1.1.castAdd 0, !q.1.2), (q.2.1.castAdd 0, !q.2.2)]
        let clauses := bad2.map mkClause
        have h := realize_from_clauses hn P crown w 0 clauses
          (by
            intro c hc
            rw [List.mem_map] at hc
            rcases hc with ⟨q, _, rfl⟩
            simp only [mkClause]
            split_ifs with heq
            · simp
            · simp [Fin.ext_iff]; exact fun e => heq (Fin.ext e))
          (by
            intro c hc
            rw [List.mem_map] at hc
            rcases hc with ⟨q, _, rfl⟩
            simp only [mkClause]
            split_ifs <;> simp <;> omega)
          (fun a => by
            constructor
            · intro ha
              refine ⟨fun i => a ⟨i.val, by omega⟩, ?_, fun i => by simp⟩
              intro c hc
              rw [List.mem_map] at hc
              rcases hc with ⟨⟨⟨i1, b1⟩, ⟨i2, b2⟩⟩, hmem, rfl⟩
              have hf := (Finset.mem_filter.mp (Finset.mem_toList.mp hmem)).2
              simp only [mkClause]
              split_ifs with heq
              · subst heq
                have hb : b1 = b2 := by rcases hf.1 with h | h; exact absurd rfl h; exact h
                subst hb
                refine ⟨(i1.castAdd 0, !b1), List.mem_cons_self, ?_⟩
                have hne : a i1 ≠ b1 := fun e => hf.2 ⟨a, ha, e, e⟩
                cases hb1 : b1 <;> cases ha1 : a i1 <;> simp_all
              · have hnot : ¬ (a i1 = b1 ∧ a i2 = b2) := fun ⟨e1, e2⟩ => hf.2 ⟨a, ha, e1, e2⟩
                by_cases h1 : a i1 = b1
                · have h2 : a i2 ≠ b2 := fun e2 => hnot ⟨h1, e2⟩
                  refine ⟨(i2.castAdd 0, !b2), List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
                  cases hb2 : b2 <;> cases ha2 : a i2 <;> simp_all
                · refine ⟨(i1.castAdd 0, !b1), List.mem_cons_self, ?_⟩
                  cases hb1 : b1 <;> cases ha1 : a i1 <;> simp_all
            · rintro ⟨p, hp_sat, hp_read⟩
              apply baker_pixley P hcl hemp a
              intro i1 i2
              by_contra hno
              have hmem : ((i1, a i1), (i2, a i2)) ∈ bad2 := by
                apply Finset.mem_toList.mpr
                apply Finset.mem_filter.mpr
                refine ⟨Finset.mem_univ _, ?_, hno⟩
                by_cases h : i1 = i2
                · right; rw [h]
                · left; exact h
              have hc : mkClause ((i1, a i1), (i2, a i2)) ∈ clauses := List.mem_map_of_mem hmem
              rcases hp_sat _ hc with ⟨lb, hlb, hplb⟩
              simp only [mkClause] at hlb
              split_ifs at hlb with heq
              · simp only [List.mem_singleton] at hlb
                subst hlb
                rw [← hp_read i1] at hplb
                cases a i1 <;> simp at hplb
              · simp only [List.mem_cons, List.not_mem_nil, or_false] at hlb
                rcases hlb with rfl | rfl
                · rw [← hp_read i1] at hplb; cases a i1 <;> simp at hplb
                · rw [← hp_read i2] at hplb; cases a i2 <;> simp at hplb)
        rcases h with ⟨q, X, Y, label, hw, hP⟩
        exact ⟨0, q, X, Y, label, hw, hP⟩
    ·
      intro _
      classical
      let Z : Finset (Fin n → Bool) := Finset.univ.filter (fun z => ¬ P z)
      let m := Z.card
      let eZ : Fin m ≃ Z := Z.equivFin.symm
      let h := m * n
      let auxBlock (idx : Fin m) (r : Fin n) : Fin (n + h) :=
        ⟨n + idx.val * n + r.val, by
          have hi : idx.val + 1 ≤ m := idx.isLt
          have hmul : (idx.val + 1) * n ≤ m * n := Nat.mul_le_mul_right n hi
          have h1 : idx.val * n + n = (idx.val + 1) * n := by ring
          omega⟩
      have haux_inj : ∀ idx1 idx2 r1 r2, auxBlock idx1 r1 = auxBlock idx2 r2 →
          idx1 = idx2 ∧ r1 = r2 := by
        intro idx1 idx2 r1 r2 heq
        have hval := congrArg Fin.val heq
        simp only [auxBlock] at hval
        have hdiv : (n * idx1.val + r1.val) / n = (n * idx2.val + r2.val) / n := by
          congr 1; nlinarith
        have hmod : (n * idx1.val + r1.val) % n = (n * idx2.val + r2.val) % n := by
          congr 1; nlinarith
        rw [Nat.mul_add_div hn, Nat.div_eq_of_lt r1.isLt, Nat.mul_add_div hn,
          Nat.div_eq_of_lt r2.isLt, add_zero, add_zero] at hdiv
        rw [Nat.mul_add_mod, Nat.mod_eq_of_lt r1.isLt, Nat.mul_add_mod,
          Nat.mod_eq_of_lt r2.isLt] at hmod
        exact ⟨Fin.ext hdiv, Fin.ext hmod⟩
      let clausesFor (idx : Fin m) : List (List (Fin (n + h) × Bool)) :=
        let z := (eZ idx).1
        let c0 : List (Fin (n + h) × Bool) :=
          [(auxBlock idx ⟨0, hn⟩, false), ((⟨0, hn⟩ : Fin n).castAdd h, !(z ⟨0, hn⟩))]
        let cstep : List (List (Fin (n + h) × Bool)) :=
          (List.finRange (n - 1)).map fun r =>
            [(auxBlock idx ⟨r.val + 1, by omega⟩, false),
             (auxBlock idx ⟨r.val, by omega⟩, true),
             ((⟨r.val + 1, by omega⟩ : Fin n).castAdd h, !(z ⟨r.val + 1, by omega⟩))]
        let clast : List (Fin (n + h) × Bool) :=
          [(auxBlock idx ⟨n - 1, by omega⟩, true)]
        c0 :: clast :: cstep
      let clauses : List (List (Fin (n + h) × Bool)) :=
        (List.finRange m).flatMap clausesFor
      have hres := realize_from_clauses hn P crown w h clauses
        (by
          intro c hc
          rw [List.mem_flatMap] at hc
          rcases hc with ⟨idx, _, hci⟩
          simp only [clausesFor, List.mem_cons, List.mem_map] at hci
          rcases hci with rfl | rfl | ⟨r, _, rfl⟩
          · simp [auxBlock, Fin.ext_iff]; omega
          · simp
          · simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
              List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true]
            refine ⟨⟨?_, ?_⟩, ?_, by simp⟩
            · intro e; have := (haux_inj idx idx _ _ e).2; simp at this
            · intro e; have := congrArg Fin.val e; simp [auxBlock] at this; omega
            · intro e; have := congrArg Fin.val e; simp [auxBlock] at this; omega)
        (by
          intro c hc
          rw [List.mem_flatMap] at hc
          rcases hc with ⟨idx, _, hci⟩
          simp only [clausesFor, List.mem_cons, List.mem_map] at hci
          rcases hci with rfl | rfl | ⟨r, _, rfl⟩ <;> simp <;> omega)
        (fun a => by
          constructor
          · intro ha
            let p : Fin (n + h) → Bool := fun blk =>
              if hlt : blk.val < n then a ⟨blk.val, hlt⟩
              else
                let idx_val := (blk.val - n) / n
                let r_val := (blk.val - n) % n
                if hidx : idx_val < m then
                  let z := (eZ ⟨idx_val, hidx⟩).1
                  decide (∃ s : Fin n, s.val ≤ r_val ∧ a s ≠ z s)
                else false
            have hp_aux : ∀ idx r, p (auxBlock idx r) =
                decide (∃ s : Fin n, s.val ≤ r.val ∧ a s ≠ (eZ idx).1 s) := by
              intro idx r
              simp only [p, auxBlock]
              have hge : ¬ (n + idx.val * n + r.val < n) := by omega
              have hsub : n + idx.val * n + r.val - n = idx.val * n + r.val := by omega
              have hdiv : (idx.val * n + r.val) / n = idx.val := by
                rw [Nat.mul_comm idx.val n, Nat.mul_add_div hn, Nat.div_eq_of_lt r.isLt, add_zero]
              have hmod : (idx.val * n + r.val) % n = r.val := by
                rw [Nat.mul_comm idx.val n, Nat.mul_add_mod, Nat.mod_eq_of_lt r.isLt]
              simp [hge, hsub, hdiv, hmod, idx.isLt]
            refine ⟨p, ?_, fun i => by simp [p, i.isLt]⟩
            intro c hc
            rw [List.mem_flatMap] at hc
            rcases hc with ⟨idx, _, hci⟩
            simp only [clausesFor, List.mem_cons, List.mem_map] at hci
            rcases hci with rfl | rfl | ⟨r, _, rfl⟩
            ·
              by_cases h0 : a ⟨0, hn⟩ = (eZ idx).1 ⟨0, hn⟩
              · refine ⟨(auxBlock idx ⟨0, hn⟩, false), List.mem_cons_self, ?_⟩
                rw [hp_aux, decide_eq_false_iff_not]
                rintro ⟨s, hs0, hsne⟩
                have hs : s = ⟨0, hn⟩ := Fin.ext (by change s.val = 0; change s.val ≤ 0 at hs0; omega)
                exact hsne (hs ▸ h0)
              · refine ⟨((⟨0, hn⟩ : Fin n).castAdd h, !((eZ idx).1 ⟨0, hn⟩)),
                  List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
                simp only [p, Fin.val_castAdd, hn, ↓reduceDIte]
                cases ha0 : a ⟨0, hn⟩ <;> cases hz0 : (eZ idx).1 ⟨0, hn⟩ <;> simp_all
            ·
              refine ⟨(auxBlock idx ⟨n - 1, by omega⟩, true), List.mem_cons_self, ?_⟩
              rw [hp_aux, decide_eq_true_eq]
              have hne : a ≠ (eZ idx).1 := fun e => by
                have hz : ¬ P (eZ idx).1 := (Finset.mem_filter.mp (eZ idx).2).2
                exact hz (e ▸ ha)
              have hex : ∃ s : Fin n, a s ≠ (eZ idx).1 s := by
                by_contra hall; push_neg at hall; exact hne (funext hall)
              rcases hex with ⟨s, hs⟩
              have hslt : s.val < n := s.isLt
              exact ⟨s, by change s.val ≤ n - 1; omega, hs⟩
            ·
              by_cases hex : ∃ s : Fin n, s.val ≤ r.val + 1 ∧ a s ≠ (eZ idx).1 s
              · rcases hex with ⟨s, hsle, hsne⟩
                by_cases hsr : s.val ≤ r.val
                · refine ⟨(auxBlock idx ⟨r.val, by omega⟩, true),
                    List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
                  rw [hp_aux, decide_eq_true_eq]
                  exact ⟨s, hsr, hsne⟩
                · have hseq : s = ⟨r.val + 1, by omega⟩ := Fin.ext (by change s.val = r.val + 1; omega)
                  rw [hseq] at hsne
                  refine ⟨((⟨r.val + 1, by omega⟩ : Fin n).castAdd h,
                      !((eZ idx).1 ⟨r.val + 1, by omega⟩)),
                    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), ?_⟩
                  simp only [p, Fin.val_castAdd, show r.val + 1 < n by omega, ↓reduceDIte]
                  cases ha1 : a ⟨r.val + 1, by omega⟩ <;>
                    cases hz1 : (eZ idx).1 ⟨r.val + 1, by omega⟩ <;> simp_all
              · refine ⟨(auxBlock idx ⟨r.val + 1, by omega⟩, false), List.mem_cons_self, ?_⟩
                rw [hp_aux, decide_eq_false_iff_not]
                exact hex
          · rintro ⟨p, hp_sat, hp_read⟩
            by_contra hnotP
            have haZ : a ∈ Z := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnotP⟩
            let idx : Fin m := eZ.symm ⟨a, haZ⟩
            have hz_eq : (eZ idx).1 = a := by simp [idx]
            have hfalse : ∀ (r : ℕ) (hr : r < n), p (auxBlock idx ⟨r, hr⟩) = false := by
              intro r
              induction r with
              | zero =>
                intro hr
                have hc0 : [(auxBlock idx ⟨0, hn⟩, false),
                    ((⟨0, hn⟩ : Fin n).castAdd h, !((eZ idx).1 ⟨0, hn⟩))] ∈ clauses := by
                  rw [List.mem_flatMap]
                  exact ⟨idx, List.mem_finRange idx, by simp [clausesFor]⟩
                rcases hp_sat _ hc0 with ⟨lb, hlb, hplb⟩
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hlb
                rcases hlb with rfl | rfl
                · exact hplb
                · rw [← hp_read ⟨0, hn⟩, hz_eq] at hplb
                  cases a ⟨0, hn⟩ <;> simp at hplb
              | succ r ih =>
                intro hr
                have hprev := ih (by omega)
                have hcr : [(auxBlock idx ⟨r + 1, hr⟩, false),
                    (auxBlock idx ⟨r, by omega⟩, true),
                    ((⟨r + 1, hr⟩ : Fin n).castAdd h, !((eZ idx).1 ⟨r + 1, hr⟩))] ∈ clauses := by
                  rw [List.mem_flatMap]
                  refine ⟨idx, List.mem_finRange idx, ?_⟩
                  simp only [clausesFor, List.mem_cons, List.mem_map]
                  right; right
                  exact ⟨⟨r, by omega⟩, List.mem_finRange _, rfl⟩
                rcases hp_sat _ hcr with ⟨lb, hlb, hplb⟩
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hlb
                rcases hlb with rfl | rfl | rfl
                · exact hplb
                · rw [hprev] at hplb; simp at hplb
                · rw [← hp_read ⟨r + 1, hr⟩, hz_eq] at hplb
                  cases a ⟨r + 1, hr⟩ <;> simp at hplb
            have hclast : [(auxBlock idx ⟨n - 1, by omega⟩, true)] ∈ clauses := by
              rw [List.mem_flatMap]
              exact ⟨idx, List.mem_finRange idx, by simp [clausesFor]⟩
            rcases hp_sat _ hclast with ⟨lb, hlb, hplb⟩
            simp only [List.mem_singleton] at hlb
            subst hlb
            rw [hfalse (n - 1) (by omega)] at hplb
            simp at hplb)
      rcases hres with ⟨q, X, Y, label, hw, hP⟩
      exact ⟨h, q, X, Y, label, hw, hP⟩

end PEqualNP.Outside.L_meta_29952_aux

theorem PEqualNP.Outside.L_meta_29952 : (∀ (n : Nat), 0 < n → ∀ (P : (Fin n → Bool) → Prop) (crown : Bool) (w : Nat),
  let realizes := ∃ h q : Nat,
    let blocks := n+h
    let k := 6*blocks+1
    let nr := if crown then k+2 else k
    let nc := if crown then k+1 else k
    let A := fun (i : Fin nr) (j : Fin nc) => if crown then
      decide (i.val ≠ k+1 ∧ ¬ (i.val < k ∧ i.val = j.val)) else decide (i.val = j.val)
    let Fn := (Fin nr → Bool) → (Fin nc → Bool) → Bool
    let eligible := fun f : Fn => ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      (if crown then PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 2*k+1
       else PEqualNP.MetaComplexity.Monotone2 C ∧ C.size+1 ≤ 2*k) ∧ PEqualNP.Represents.Represents A C ∧
      ∀ x y, f x y = C.eval (List.ofFn x ++ List.ofFn y)
    let test := fun (f : Fn) (probe : Fin nr → Bool) => f probe (fun _ => false) = !crown
    let triple := fun (i : Fin blocks) (s : Fin 6) (u : Fin nr) =>
      decide (u.val = 6*i.val+s.val ∨ u.val = 6*i.val+(s.val+1)%6 ∨ u.val = 6*i.val+(s.val+2)%6)
    let litWord := fun (i : Fin blocks) (sgn : Bool) (u : Fin nr) =>
      decide (u.val = 6*i.val ∨ u.val = 6*i.val+(if sgn then 1 else 5))
    ∃ (X : Fin q → Fin nr → Bool) (Y : Fin q → Fin nc → Bool) (label : Fin q → Bool),
      (∀ j, (Finset.univ.filter (fun i => X j i = true)).card +
        (Finset.univ.filter (fun i => Y j i = true)).card ≤ w) ∧
      ∀ a : Fin n → Bool, P a ↔ ∃ f : Fn,
        eligible f ∧ (∀ i s, test f (triple i s)) ∧
        (∀ j, f (X j) (Y j) = label j) ∧
        ∀ i : Fin n, a i = decide (test f (litWord (i.castAdd h) true))
  let empty := ∀ a, ¬ P a
  let constant := empty ∨ ∀ a, P a
  let box := empty ∨ ∃ allow : Fin n → Bool → Bool, ∀ a, P a ↔ ∀ i, allow i (a i) = true
  let maj := fun (a b c : Fin n → Bool) (i : Fin n) =>
    (a i && b i) || (b i && c i) || (a i && c i)
  let closed := ∀ a b c, P a → P b → P c → P (maj a b c)
  realizes ↔ (if w < 2 then constant else if w < 4 then box else if w < 6 then closed else True)) :=
  PEqualNP.Outside.L_meta_29952_aux.main_proof

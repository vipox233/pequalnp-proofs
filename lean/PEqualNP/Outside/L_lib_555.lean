import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_555_aux

open scoped BigOperators
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

def stepWires (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_stepWires_length (gs : List Gate) :
    ∀ (w : List Bool), (gs.foldl stepWires w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    simp only [List.foldl_cons, ih, stepWires, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_stepWires_getD_lt (gs : List Gate) :
    ∀ (w : List Bool) (k : ℕ), k < w.length →
      (gs.foldl stepWires w).getD k false = w.getD k false := by
  induction gs with
  | nil => intro w k _; rfl
  | cons g gs ih =>
    intro w k hk
    have hk' : k < (stepWires w g).length := by
      simp only [stepWires, List.length_append, List.length_singleton]
      omega
    rw [List.foldl_cons, ih (stepWires w g) k hk']
    simp only [stepWires, List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

lemma getD_eq_false_of_le (l : List Bool) (k : ℕ) (hk : l.length ≤ k) :
    l.getD k false = false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hk, Option.getD_none]

def wireVal {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma wireVal_eq_eval {n : ℕ} (C : Circuit) (x : Fin n → Bool) :
    C.eval (List.ofFn x) = wireVal C x C.output := rfl

lemma wireVal_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : Fin n) :
    wireVal C x j.val = x j := by
  unfold wireVal Circuit.wires
  have hlt : j.val < (List.ofFn x).length := by simp
  have h := foldl_stepWires_getD_lt C.gates (List.ofFn x) j.val hlt
  change (C.gates.foldl stepWires (List.ofFn x)).getD j.val false = x j
  rw [h]
  simp [List.getD_eq_getElem?_getD]

lemma wireVal_out_of_range {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.gates.length ≤ w) :
    wireVal C x w = false := by
  unfold wireVal Circuit.wires
  apply getD_eq_false_of_le
  change (C.gates.foldl stepWires (List.ofFn x)).length ≤ w
  rw [foldl_stepWires_length, List.length_ofFn]
  exact hw

lemma wireVal_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < C.gates.length) :
    let g := C.gates[i]
    wireVal C x (n + i) =
      g.op.eval (g.inputs.map fun u => if u < n + i then wireVal C x u else false) := by
  dsimp only
  let pre := C.gates.take i
  let g := C.gates[i]
  let post := C.gates.drop (i + 1)
  have hsplit : C.gates = pre ++ g :: post := by
    have h1 := List.take_append_drop i C.gates
    have h2 : C.gates.drop i = g :: post := List.drop_eq_getElem_cons hi
    rw [h2] at h1
    exact h1.symm
  let wpre := pre.foldl stepWires (List.ofFn x)
  have hlen_pre : wpre.length = n + i := by
    simp only [wpre, foldl_stepWires_length, List.length_ofFn, pre, List.length_take, Nat.min_eq_left hi.le]
  have hwires_eq : C.wires (List.ofFn x) = post.foldl stepWires (stepWires wpre g) := by
    unfold Circuit.wires
    change C.gates.foldl stepWires (List.ofFn x) = _
    rw [hsplit, List.foldl_append, List.foldl_cons]
  have hval_ni : wireVal C x (n + i) = g.op.eval (g.inputs.map fun u => wpre.getD u false) := by
    unfold wireVal
    rw [hwires_eq]
    have hlt : n + i < (stepWires wpre g).length := by
      simp only [stepWires, List.length_append, List.length_singleton, hlen_pre]
      omega
    rw [foldl_stepWires_getD_lt post (stepWires wpre g) (n + i) hlt]
    simp only [stepWires, List.getD_eq_getElem?_getD, ← hlen_pre]
    rw [List.getElem?_append_right le_rfl]
    simp
  rw [hval_ni]
  congr 1
  apply List.map_congr_left
  intro u _
  by_cases hu : u < n + i
  · simp only [hu, ↓reduceIte]
    unfold wireVal
    rw [hwires_eq]
    have hu1 : u < (stepWires wpre g).length := by
      simp only [stepWires, List.length_append, List.length_singleton, hlen_pre]
      omega
    rw [foldl_stepWires_getD_lt post (stepWires wpre g) u hu1]
    have hu2 : u < wpre.length := by omega
    simp only [stepWires, List.getD_eq_getElem?_getD, List.getElem?_append_left hu2]
  · simp only [hu, ↓reduceIte]
    apply getD_eq_false_of_le
    omega

def gateDeps (n : ℕ) (C : Circuit) (i : Fin C.gates.length) : Finset ℕ :=
  match C.gates[i.val].op with
  | GateOp.not =>
    match C.gates[i.val].inputs with
    | u :: _ => if u < n + i.val then {u} else ∅
    | [] => ∅
  | _ => (C.gates[i.val].inputs.filter (fun u => decide (u < n + i.val))).toFinset

lemma gateDeps_lt (n : ℕ) (C : Circuit) (i : Fin C.gates.length) {u : ℕ}
    (hu : u ∈ gateDeps n C i) : u < n + i.val := by
  unfold gateDeps at hu
  cases h : C.gates[i.val].op with
  | not =>
    rw [h] at hu
    cases hin : C.gates[i.val].inputs with
    | nil => simp [hin] at hu
    | cons v vs =>
      simp only [hin] at hu
      by_cases hv : v < n + i.val
      · simp only [hv, ↓reduceIte, Finset.mem_singleton] at hu
        omega
      · simp [hv] at hu
  | and =>
    rw [h] at hu
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hu
    exact hu.2
  | or =>
    rw [h] at hu
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hu
    exact hu.2
  | mod m =>
    rw [h] at hu
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hu
    exact hu.2
  | maj =>
    rw [h] at hu
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hu
    exact hu.2

lemma gateDeps_card_le_not (n : ℕ) (C : Circuit) (i : Fin C.gates.length)
    (hnot : C.gates[i.val].op = GateOp.not) :
    (gateDeps n C i).card ≤ 1 := by
  unfold gateDeps
  rw [hnot]
  cases C.gates[i.val].inputs with
  | nil => simp
  | cons u us =>
    by_cases hu : u < n + i.val <;> simp [hu]

lemma gateDeps_card_le_two (n : ℕ) (C : Circuit) (hfit : FanInTwo C) (i : Fin C.gates.length) :
    (gateDeps n C i).card ≤ 2 := by
  have hmem : C.gates[i.val] ∈ C.gates := List.getElem_mem i.isLt
  have hlen : C.gates[i.val].inputs.length ≤ 2 := (hfit _ hmem).2
  unfold gateDeps
  cases h : C.gates[i.val].op with
  | not =>
    cases C.gates[i.val].inputs with
    | nil => simp
    | cons u us =>
      by_cases hu : u < n + i.val <;> simp [hu]
  | and =>
    exact (List.toFinset_card_le _).trans ((List.length_filter_le _ _).trans hlen)
  | or =>
    exact (List.toFinset_card_le _).trans ((List.length_filter_le _ _).trans hlen)
  | mod m =>
    exact (List.toFinset_card_le _).trans ((List.length_filter_le _ _).trans hlen)
  | maj =>
    exact (List.toFinset_card_le _).trans ((List.length_filter_le _ _).trans hlen)

def Edge (n : ℕ) (C : Circuit) (u v : ℕ) : Prop :=
  ∃ i : Fin C.gates.length, u = n + i.val ∧ v ∈ gateDeps n C i

def Reaches (n : ℕ) (C : Circuit) : ℕ → ℕ → Prop :=
  Relation.ReflTransGen (Edge n C)

lemma edge_lt {n : ℕ} {C : Circuit} {u v : ℕ} (h : Edge n C u v) : v < u := by
  rcases h with ⟨i, rfl, hv⟩
  exact gateDeps_lt n C i hv

lemma reaches_le {n : ℕ} {C : Circuit} {u v : ℕ} (h : Reaches n C u v) : v ≤ u := by
  induction h with
  | refl => exact le_rfl
  | tail _ hstep ih => exact (edge_lt hstep).le.trans ih

lemma reaches_antisymm {n : ℕ} {C : Circuit} {u v : ℕ}
    (h1 : Reaches n C u v) (h2 : Reaches n C v u) : u = v :=
  le_antisymm (reaches_le h2) (reaches_le h1)

lemma wireVal_gate_eq_of_deps {n : ℕ} (C : Circuit) (hfit : FanInTwo C)
    (i : Fin C.gates.length) (x y : Fin n → Bool)
    (hdeps : ∀ v ∈ gateDeps n C i, wireVal C x v = wireVal C y v) :
    wireVal C x (n + i.val) = wireVal C y (n + i.val) := by
  rw [wireVal_gate C x i.val i.isLt, wireVal_gate C y i.val i.isLt]
  have hop := (hfit _ (List.getElem_mem i.isLt)).1
  cases h : C.gates[i.val].op with
  | not =>
    cases hin : C.gates[i.val].inputs with
    | nil => simp [GateOp.eval]
    | cons u us =>
      simp only [List.map_cons, GateOp.eval, List.headD_cons]
      by_cases hu : u < n + i.val
      · simp only [hu, ↓reduceIte]
        have hu_mem : u ∈ gateDeps n C i := by
          unfold gateDeps
          rw [h, hin]
          simp [hu]
        rw [hdeps u hu_mem]
      · simp [hu]
  | and =>
    congr 1
    apply List.map_congr_left
    intro u hu
    by_cases hlt : u < n + i.val
    · simp only [hlt, ↓reduceIte]
      have hu_mem : u ∈ gateDeps n C i := by
        unfold gateDeps
        rw [h]
        simp [hu, hlt]
      exact hdeps u hu_mem
    · simp [hlt]
  | or =>
    congr 1
    apply List.map_congr_left
    intro u hu
    by_cases hlt : u < n + i.val
    · simp only [hlt, ↓reduceIte]
      have hu_mem : u ∈ gateDeps n C i := by
        unfold gateDeps
        rw [h]
        simp [hu, hlt]
      exact hdeps u hu_mem
    · simp [hlt]
  | mod m =>
    simp [h] at hop
  | maj =>
    simp [h] at hop

lemma list_all_mono : ∀ {l1 l2 : List Bool},
    l1.length = l2.length → (∀ k (h1 : k < l1.length) (h2 : k < l2.length), l1[k] ≤ l2[k]) →
    l1.all id ≤ l2.all id
  | [], [], _, _ => le_rfl
  | a :: as, b :: bs, hlen, hle => by
    simp only [List.all_cons, id_eq]
    have hab : a ≤ b := hle 0 (by simp) (by simp)
    have hrest : as.all id ≤ bs.all id :=
      list_all_mono (by simp at hlen; exact hlen)
        (fun k h1 h2 => hle (k + 1) (by simp; omega) (by simp; omega))
    cases a <;> cases b <;> cases h1 : as.all id <;> cases h2 : bs.all id <;> simp_all

lemma list_any_mono : ∀ {l1 l2 : List Bool},
    l1.length = l2.length → (∀ k (h1 : k < l1.length) (h2 : k < l2.length), l1[k] ≤ l2[k]) →
    l1.any id ≤ l2.any id
  | [], [], _, _ => le_rfl
  | a :: as, b :: bs, hlen, hle => by
    simp only [List.any_cons, id_eq]
    have hab : a ≤ b := hle 0 (by simp) (by simp)
    have hrest : as.any id ≤ bs.any id :=
      list_any_mono (by simp at hlen; exact hlen)
        (fun k h1 h2 => hle (k + 1) (by simp; omega) (by simp; omega))
    cases a <;> cases b <;> cases h1 : as.any id <;> cases h2 : bs.any id <;> simp_all

lemma wireVal_gate_mono_of_deps {n : ℕ} (C : Circuit) (hfit : FanInTwo C)
    (i : Fin C.gates.length) (hnot : C.gates[i.val].op ≠ GateOp.not)
    (x y : Fin n → Bool)
    (hdeps : ∀ v ∈ gateDeps n C i, wireVal C x v ≤ wireVal C y v) :
    wireVal C x (n + i.val) ≤ wireVal C y (n + i.val) := by
  rw [wireVal_gate C x i.val i.isLt, wireVal_gate C y i.val i.isLt]
  have hop := (hfit _ (List.getElem_mem i.isLt)).1
  have hpoint :
      ∀ (k : ℕ)
        (h1 : k < (C.gates[i.val].inputs.map fun u => if u < n + i.val then wireVal C x u else false).length)
        (h2 : k < (C.gates[i.val].inputs.map fun u => if u < n + i.val then wireVal C y u else false).length),
        (C.gates[i.val].inputs.map fun u => if u < n + i.val then wireVal C x u else false)[k] ≤
        (C.gates[i.val].inputs.map fun u => if u < n + i.val then wireVal C y u else false)[k] := by
    intro k h1 h2
    simp only [List.getElem_map]
    set u := C.gates[i.val].inputs[k]'(by simp at h1; exact h1)
    by_cases hlt : u < n + i.val
    · simp only [hlt, ↓reduceIte]
      have hu_mem : u ∈ gateDeps n C i := by
        unfold gateDeps
        cases h : C.gates[i.val].op with
        | not => exact False.elim (hnot h)
        | and =>
          simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
          exact ⟨List.getElem_mem _, hlt⟩
        | or =>
          simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
          exact ⟨List.getElem_mem _, hlt⟩
        | mod m => simp [h] at hop
        | maj => simp [h] at hop
      exact hdeps u hu_mem
    · simp [hlt]
  cases h : C.gates[i.val].op with
  | not => exact False.elim (hnot h)
  | and =>
    simp only [GateOp.eval]
    exact list_all_mono (by simp) hpoint
  | or =>
    simp only [GateOp.eval]
    exact list_any_mono (by simp) hpoint
  | mod m => simp [h] at hop
  | maj => simp [h] at hop

lemma wireVal_gate_anti_not {n : ℕ} (C : Circuit)
    (i : Fin C.gates.length) (hnot : C.gates[i.val].op = GateOp.not)
    (x y : Fin n → Bool)
    (hdeps : ∀ v ∈ gateDeps n C i, wireVal C y v ≤ wireVal C x v) :
    wireVal C x (n + i.val) ≤ wireVal C y (n + i.val) := by
  rw [wireVal_gate C x i.val i.isLt, wireVal_gate C y i.val i.isLt, hnot]
  cases hin : C.gates[i.val].inputs with
  | nil => simp [GateOp.eval]
  | cons u us =>
    simp only [List.map_cons, GateOp.eval, List.headD_cons]
    by_cases hu : u < n + i.val
    · simp only [hu, ↓reduceIte]
      have hu_mem : u ∈ gateDeps n C i := by
        unfold gateDeps
        rw [hnot, hin]
        simp [hu]
      have hle := hdeps u hu_mem
      cases hx : wireVal C x u <;> cases hy : wireVal C y u <;> simp_all
    · simp [hu]

lemma wireVal_congr_of_cone {n : ℕ} (C : Circuit) (hfit : FanInTwo C)
    (x y : Fin n → Bool) :
    ∀ u : ℕ, u < n + C.gates.length →
      (∀ j : Fin n, Reaches n C u j.val → x j = y j) →
      wireVal C x u = wireVal C y u := by
  intro u
  induction u using Nat.strong_induction_on with
  | ind u ih =>
    intro hu hxy
    by_cases hun : u < n
    · have h1 := wireVal_input C x ⟨u, hun⟩
      have h2 := wireVal_input C y ⟨u, hun⟩
      rw [h1, h2]
      exact hxy ⟨u, hun⟩ Relation.ReflTransGen.refl
    · let i : Fin C.gates.length := ⟨u - n, by omega⟩
      have hui : u = n + i.val := by simp [i]; omega
      rw [hui]
      apply wireVal_gate_eq_of_deps C hfit i x y
      intro v hv
      have hv_lt : v < u := by
        have := gateDeps_lt n C i hv
        omega
      apply ih v hv_lt (by omega)
      intro j hj
      apply hxy j
      exact Relation.ReflTransGen.head ⟨i, hui, hv⟩ hj

lemma wireVal_mono_of_no_not {n : ℕ} (C : Circuit) (hfit : FanInTwo C)
    (x y : Fin n → Bool) :
    ∀ u : ℕ, u < n + C.gates.length →
      (∀ i : Fin C.gates.length, Reaches n C u (n + i.val) → C.gates[i.val].op ≠ GateOp.not) →
      (∀ j : Fin n, Reaches n C u j.val → x j ≤ y j) →
      wireVal C x u ≤ wireVal C y u := by
  intro u
  induction u using Nat.strong_induction_on with
  | ind u ih =>
    intro hu hnonot hxy
    by_cases hun : u < n
    · have h1 := wireVal_input C x ⟨u, hun⟩
      have h2 := wireVal_input C y ⟨u, hun⟩
      rw [h1, h2]
      exact hxy ⟨u, hun⟩ Relation.ReflTransGen.refl
    · let i : Fin C.gates.length := ⟨u - n, by omega⟩
      have hui : u = n + i.val := by simp [i]; omega
      rw [hui]
      have hnot_i : C.gates[i.val].op ≠ GateOp.not :=
        hnonot i (by rw [← hui]; exact Relation.ReflTransGen.refl)
      apply wireVal_gate_mono_of_deps C hfit i hnot_i x y
      intro v hv
      have hv_lt : v < u := by
        have := gateDeps_lt n C i hv
        omega
      apply ih v hv_lt (by omega)
      · intro i' hi'
        exact hnonot i' (Relation.ReflTransGen.head ⟨i, hui, hv⟩ hi')
      · intro j hj
        exact hxy j (Relation.ReflTransGen.head ⟨i, hui, hv⟩ hj)

def outdegIn (n : ℕ) (C : Circuit) (r : ℕ) [DecidablePred (Reaches n C r)] (w : ℕ) : ℕ :=
  (Finset.univ.filter (fun i : Fin C.gates.length => Reaches n C r (n + i.val) ∧ w ∈ gateDeps n C i)).card

lemma single_exit_of_outdeg_one {n : ℕ} (C : Circuit) (r s : ℕ)
    [DecidablePred (Reaches n C r)]
    (hs_reach : Reaches n C r s)
    (hdeg1 : ∀ w, Reaches n C r w → w ≠ s → Reaches n C s w → outdegIn n C r w ≤ 1)
    {i : Fin C.gates.length} (hi_r : Reaches n C r (n + i.val))
    (hi_not_s : ¬ Reaches n C s (n + i.val))
    {v : ℕ} (hv_dep : v ∈ gateDeps n C i) (hv_s : Reaches n C s v) :
    v = s := by
  by_contra hv_ne
  cases Relation.ReflTransGen.cases_tail hv_s with
  | inl heq => exact hv_ne heq
  | inr hex =>
    rcases hex with ⟨u, hsu, huv⟩
    rcases huv with ⟨i', rfl, hv_dep'⟩
    have hi_ne : i ≠ i' := by
      intro heq
      subst heq
      exact hi_not_s hsu
    have hi'_r : Reaches n C r (n + i'.val) := Relation.ReflTransGen.trans hs_reach hsu
    have hv_r : Reaches n C r v := Relation.ReflTransGen.trans hs_reach hv_s
    let S := Finset.univ.filter
      (fun k : Fin C.gates.length => Reaches n C r (n + k.val) ∧ v ∈ gateDeps n C k)
    have hsub : ({i, i'} : Finset (Fin C.gates.length)) ⊆ S := by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with hk1 | hk2
      · rw [hk1]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi_r, hv_dep⟩
      · rw [hk2]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ i', hi'_r, hv_dep'⟩
    have h2 : 2 ≤ outdegIn n C r v := by
      calc 2 = ({i, i'} : Finset (Fin C.gates.length)).card := (Finset.card_pair hi_ne).symm
        _ ≤ S.card := Finset.card_le_card hsub
    have h1 := hdeg1 v hv_r hv_ne hv_s
    omega

lemma wireVal_congr_outside_cone {n : ℕ} (C : Circuit) (hfit : FanInTwo C)
    (r s : ℕ) [DecidablePred (Reaches n C r)]
    (hr : r < n + C.gates.length)
    (hs_reach : Reaches n C r s)
    (hdeg1 : ∀ w, Reaches n C r w → w ≠ s → Reaches n C s w → outdegIn n C r w ≤ 1)
    (x y : Fin n → Bool)
    (hs_eq : wireVal C x s = wireVal C y s)
    (hout_eq : ∀ j : Fin n, Reaches n C r j.val → ¬ Reaches n C s j.val → x j = y j) :
    ∀ u : ℕ, Reaches n C r u → ¬ Reaches n C s u → wireVal C x u = wireVal C y u := by
  intro u
  induction u using Nat.strong_induction_on with
  | ind u ih =>
    intro hu_r hu_ns
    have hu_lt : u < n + C.gates.length := lt_of_le_of_lt (reaches_le hu_r) hr
    by_cases hun : u < n
    · rw [wireVal_input C x ⟨u, hun⟩, wireVal_input C y ⟨u, hun⟩]
      exact hout_eq ⟨u, hun⟩ hu_r hu_ns
    · let i : Fin C.gates.length := ⟨u - n, by omega⟩
      have hui : u = n + i.val := by simp [i]; omega
      rw [hui]
      apply wireVal_gate_eq_of_deps C hfit i x y
      intro v hv
      have hv_lt : v < u := by
        have := gateDeps_lt n C i hv
        omega
      have hv_r : Reaches n C r v := Relation.ReflTransGen.tail hu_r ⟨i, hui, hv⟩
      by_cases hv_s : Reaches n C s v
      · have hvs : v = s :=
          single_exit_of_outdeg_one C r s hs_reach hdeg1 (hui ▸ hu_r) (hui ▸ hu_ns) hv hv_s
        rw [hvs]
        exact hs_eq
      · exact ih v hv_lt hv_r hv_s

lemma wireVal_mono_outside_cone {n : ℕ} (C : Circuit) (hfit : FanInTwo C)
    (r s : ℕ) [DecidablePred (Reaches n C r)]
    (hr : r < n + C.gates.length)
    (hs_reach : Reaches n C r s)
    (hdeg1 : ∀ w, Reaches n C r w → w ≠ s → Reaches n C s w → outdegIn n C r w ≤ 1)
    (hnonot : ∀ i : Fin C.gates.length, Reaches n C r (n + i.val) →
      ¬ Reaches n C s (n + i.val) → C.gates[i.val].op ≠ GateOp.not)
    (x y : Fin n → Bool)
    (hs_le : wireVal C x s ≤ wireVal C y s)
    (hout_eq : ∀ j : Fin n, Reaches n C r j.val → ¬ Reaches n C s j.val → x j = y j) :
    ∀ u : ℕ, Reaches n C r u → ¬ Reaches n C s u → wireVal C x u ≤ wireVal C y u := by
  intro u
  induction u using Nat.strong_induction_on with
  | ind u ih =>
    intro hu_r hu_ns
    have hu_lt : u < n + C.gates.length := lt_of_le_of_lt (reaches_le hu_r) hr
    by_cases hun : u < n
    · rw [wireVal_input C x ⟨u, hun⟩, wireVal_input C y ⟨u, hun⟩, hout_eq ⟨u, hun⟩ hu_r hu_ns]
    · let i : Fin C.gates.length := ⟨u - n, by omega⟩
      have hui : u = n + i.val := by simp [i]; omega
      rw [hui]
      have hnot_i : C.gates[i.val].op ≠ GateOp.not := hnonot i (hui ▸ hu_r) (hui ▸ hu_ns)
      apply wireVal_gate_mono_of_deps C hfit i hnot_i x y
      intro v hv
      have hv_lt : v < u := by
        have := gateDeps_lt n C i hv
        omega
      have hv_r : Reaches n C r v := Relation.ReflTransGen.tail hu_r ⟨i, hui, hv⟩
      by_cases hv_s : Reaches n C s v
      · have hvs : v = s :=
          single_exit_of_outdeg_one C r s hs_reach hdeg1 (hui ▸ hu_r) (hui ▸ hu_ns) hv hv_s
        rw [hvs]
        exact hs_le
      · exact ih v hv_lt hv_r hv_s

lemma unique_dep_reaching {n : ℕ} (C : Circuit) (r : ℕ)
    [DecidablePred (Reaches n C r)]
    (target : ℕ)
    (hdeg1 : ∀ w, Reaches n C r w → w ≠ r → Reaches n C w target → outdegIn n C r w ≤ 1)
    {i : Fin C.gates.length} (hi_r : Reaches n C r (n + i.val))
    {v1 v2 : ℕ} (hv1 : v1 ∈ gateDeps n C i) (hv2 : v2 ∈ gateDeps n C i)
    (hr1 : Reaches n C v1 target) (hr2 : Reaches n C v2 target) :
    v1 = v2 := by
  classical
  by_contra hne
  let common : Finset ℕ := (Finset.range (n + i.val)).filter (fun w =>
    Reaches n C v1 w ∧ Reaches n C v2 w ∧ Reaches n C w target)
  have ht_lt : target < n + i.val :=
    lt_of_le_of_lt (reaches_le hr1) (gateDeps_lt n C i hv1)
  have hne_common : common.Nonempty :=
    ⟨target, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ht_lt, hr1, hr2, Relation.ReflTransGen.refl⟩⟩
  obtain ⟨w, hw_mem, hw_max⟩ := Finset.exists_max_image common id hne_common
  rcases Finset.mem_filter.mp hw_mem with ⟨_, h1w, h2w, hwt⟩
  have hw_r : Reaches n C r w :=
    Relation.ReflTransGen.trans (Relation.ReflTransGen.tail hi_r ⟨i, rfl, hv1⟩) h1w
  have hw_ne_r : w ≠ r := by
    have hlt1 : w < n + i.val := lt_of_le_of_lt (reaches_le h1w) (gateDeps_lt n C i hv1)
    have hle2 : n + i.val ≤ r := reaches_le hi_r
    omega
  have hstep1 : ∃ i1 : Fin C.gates.length, Reaches n C r (n + i1.val) ∧ w ∈ gateDeps n C i1 ∧
      ((i1 = i ∧ w = v1) ∨ Reaches n C v1 (n + i1.val)) := by
    cases Relation.ReflTransGen.cases_tail h1w with
    | inl heq =>
      exact ⟨i, hi_r, heq ▸ hv1, Or.inl ⟨rfl, heq⟩⟩
    | inr hex =>
      rcases hex with ⟨u1, hv1_u1, hu1_w⟩
      rcases hu1_w with ⟨i1, rfl, hw_dep1⟩
      have hi1_r : Reaches n C r (n + i1.val) :=
        Relation.ReflTransGen.trans (Relation.ReflTransGen.tail hi_r ⟨i, rfl, hv1⟩) hv1_u1
      exact ⟨i1, hi1_r, hw_dep1, Or.inr hv1_u1⟩
  have hstep2 : ∃ i2 : Fin C.gates.length, Reaches n C r (n + i2.val) ∧ w ∈ gateDeps n C i2 ∧
      ((i2 = i ∧ w = v2) ∨ Reaches n C v2 (n + i2.val)) := by
    cases Relation.ReflTransGen.cases_tail h2w with
    | inl heq =>
      exact ⟨i, hi_r, heq ▸ hv2, Or.inl ⟨rfl, heq⟩⟩
    | inr hex =>
      rcases hex with ⟨u2, hv2_u2, hu2_w⟩
      rcases hu2_w with ⟨i2, rfl, hw_dep2⟩
      have hi2_r : Reaches n C r (n + i2.val) :=
        Relation.ReflTransGen.trans (Relation.ReflTransGen.tail hi_r ⟨i, rfl, hv2⟩) hv2_u2
      exact ⟨i2, hi2_r, hw_dep2, Or.inr hv2_u2⟩
  rcases hstep1 with ⟨i1, hi1_r, hw1, hcase1⟩
  rcases hstep2 with ⟨i2, hi2_r, hw2, hcase2⟩
  have hi12 : i1 ≠ i2 := by
    intro heq
    subst heq
    rcases hcase1 with ⟨hi1_eq, hwv1⟩ | hv1_i1 <;> rcases hcase2 with ⟨hi2_eq, hwv2⟩ | hv2_i1
    · exact hne (hwv1.symm.trans hwv2)
    · subst hi1_eq
      have := reaches_le hv2_i1
      have := gateDeps_lt n C i1 hv2
      omega
    · subst hi2_eq
      have := reaches_le hv1_i1
      have := gateDeps_lt n C i1 hv1
      omega
    · have hmem' : n + i1.val ∈ common := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_range.mpr ?_, hv1_i1, hv2_i1, Relation.ReflTransGen.head ⟨i1, rfl, hw1⟩ hwt⟩
        exact lt_of_le_of_lt (reaches_le hv1_i1) (gateDeps_lt n C i hv1)
      have hle_max : n + i1.val ≤ w := hw_max (n + i1.val) hmem'
      have hlt_w : w < n + i1.val := gateDeps_lt n C i1 hw1
      omega
  let S := Finset.univ.filter
    (fun k : Fin C.gates.length => Reaches n C r (n + k.val) ∧ w ∈ gateDeps n C k)
  have hsub : ({i1, i2} : Finset (Fin C.gates.length)) ⊆ S := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with hk1 | hk2
    · rw [hk1]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ i1, hi1_r, hw1⟩
    · rw [hk2]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ i2, hi2_r, hw2⟩
  have h2 : 2 ≤ outdegIn n C r w := by
    calc 2 = ({i1, i2} : Finset (Fin C.gates.length)).card := (Finset.card_pair hi12).symm
      _ ≤ S.card := Finset.card_le_card hsub
  have h1 := hdeg1 w hw_r hw_ne_r hwt
  omega

lemma unate_of_no_fork_above {n : ℕ} (C : Circuit) (hfit : FanInTwo C)
    (r : ℕ) [DecidablePred (Reaches n C r)]
    (hr : r < n + C.gates.length)
    (j : Fin n)
    (hdeg1 : ∀ w, Reaches n C r w → w ≠ r → Reaches n C w j.val → outdegIn n C r w ≤ 1) :
    ∀ u : ℕ, Reaches n C r u →
      ∃ pol : Bool, ∀ x : Fin n → Bool,
        if pol then
          wireVal C (Function.update x j true) u ≤ wireVal C (Function.update x j false) u
        else
          wireVal C (Function.update x j false) u ≤ wireVal C (Function.update x j true) u := by
  classical
  intro u
  induction u using Nat.strong_induction_on with
  | ind u ih =>
    intro hu_r
    have hu_lt : u < n + C.gates.length := lt_of_le_of_lt (reaches_le hu_r) hr
    by_cases huj : Reaches n C u j.val
    · by_cases hun : u < n
      · have heq_uj : u = j.val := by
          cases Relation.ReflTransGen.cases_head huj with
          | inl h => exact h
          | inr hex =>
            rcases hex with ⟨_, hedge, _⟩
            rcases hedge with ⟨i, hi, _⟩
            omega
        refine ⟨false, ?_⟩
        intro x
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [heq_uj, wireVal_input, wireVal_input, Function.update_self, Function.update_self]
        decide
      · let i : Fin C.gates.length := ⟨u - n, by omega⟩
        have hui : u = n + i.val := by simp [i]; omega
        have hex_v : ∃ v ∈ gateDeps n C i, Reaches n C v j.val := by
          cases Relation.ReflTransGen.cases_head (hui ▸ huj) with
          | inl heq => omega
          | inr hex =>
            rcases hex with ⟨v, hedge, hvj⟩
            rcases hedge with ⟨i', hi', hv_dep⟩
            have hii' : i = i' := Fin.ext (by omega)
            subst hii'
            exact ⟨v, hv_dep, hvj⟩
        rcases hex_v with ⟨v, hv_dep, hv_j⟩
        have hv_lt : v < u := by
          have := gateDeps_lt n C i hv_dep
          omega
        have hv_r : Reaches n C r v := Relation.ReflTransGen.tail hu_r ⟨i, hui, hv_dep⟩
        obtain ⟨pol_v, hpol_v⟩ := ih v hv_lt hv_r
        have huniq : ∀ v' ∈ gateDeps n C i, v' ≠ v → ¬ Reaches n C v' j.val := by
          intro v' hv' hne hv'j
          exact hne (unique_dep_reaching C r j.val hdeg1 (hui ▸ hu_r) hv' hv_dep hv'j hv_j)
        have hother_eq : ∀ v' ∈ gateDeps n C i, v' ≠ v → ∀ x : Fin n → Bool,
            wireVal C (Function.update x j false) v' = wireVal C (Function.update x j true) v' := by
          intro v' hv' hne x
          apply wireVal_congr_of_cone C hfit _ _ v'
            (lt_trans (gateDeps_lt n C i hv') (by omega))
          intro k hk
          have hkj : k ≠ j := by
            rintro rfl
            exact huniq v' hv' hne hk
          rw [Function.update_of_ne hkj, Function.update_of_ne hkj]
        by_cases hnot : C.gates[i.val].op = GateOp.not
        · refine ⟨!pol_v, ?_⟩
          intro x
          rw [hui]
          cases hpv : pol_v
          · simp only [Bool.not_false, ↓reduceIte]
            apply wireVal_gate_anti_not C i hnot
            intro v' hv'
            by_cases hvv : v' = v
            · subst hvv
              have hvx := hpol_v x
              simpa [hpv] using hvx
            · rw [hother_eq v' hv' hvv x]
          · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            apply wireVal_gate_anti_not C i hnot
            intro v' hv'
            by_cases hvv : v' = v
            · subst hvv
              have hvx := hpol_v x
              simpa [hpv] using hvx
            · rw [hother_eq v' hv' hvv x]
        · refine ⟨pol_v, ?_⟩
          intro x
          rw [hui]
          cases hpv : pol_v
          · simp only [Bool.false_eq_true, ↓reduceIte]
            apply wireVal_gate_mono_of_deps C hfit i hnot
            intro v' hv'
            by_cases hvv : v' = v
            · subst hvv
              have hvx := hpol_v x
              simpa [hpv] using hvx
            · rw [hother_eq v' hv' hvv x]
          · simp only [↓reduceIte]
            apply wireVal_gate_mono_of_deps C hfit i hnot
            intro v' hv'
            by_cases hvv : v' = v
            · subst hvv
              have hvx := hpol_v x
              simpa [hpv] using hvx
            · rw [hother_eq v' hv' hvv x]
    · refine ⟨false, ?_⟩
      intro x
      simp only [Bool.false_eq_true, ↓reduceIte]
      have heq : wireVal C (Function.update x j false) u = wireVal C (Function.update x j true) u := by
        apply wireVal_congr_of_cone C hfit _ _ u hu_lt
        intro k hk
        have hkj : k ≠ j := by
          rintro rfl
          exact huj hk
        rw [Function.update_of_ne hkj, Function.update_of_ne hkj]
      rw [heq]

lemma exists_unique_of_sum_eq_one {α : Type*} [DecidableEq α] (S : Finset α) (f : α → ℕ)
    (hsum : ∑ x ∈ S, f x = 1) :
    ∃ s ∈ S, f s = 1 ∧ ∀ w ∈ S, w ≠ s → f w = 0 := by
  have hex : ∃ s ∈ S, f s ≠ 0 := by
    by_contra hall
    push Not at hall
    have h0 : ∑ x ∈ S, f x = 0 := Finset.sum_eq_zero hall
    omega
  rcases hex with ⟨s, hsS, hfs_ne⟩
  have hsplit := Finset.add_sum_erase S f hsS
  have hfs1 : f s = 1 := by omega
  have hrest0 : ∑ x ∈ S.erase s, f x = 0 := by omega
  refine ⟨s, hsS, hfs1, ?_⟩
  intro w hwS hne
  exact (Finset.sum_eq_zero_iff.mp hrest0) w (Finset.mem_erase.mpr ⟨hne, hwS⟩)

lemma non_monotone_contradiction {n : ℕ} (f : (Fin n → Bool) → Bool) (j : Fin n)
    (hup : ∃ x, f (Function.update x j false) = false ∧ f (Function.update x j true) = true)
    (hdown : ∃ x, f (Function.update x j false) = true ∧ f (Function.update x j true) = false)
    (hunate : ∃ pol : Bool, ∀ x,
      if pol then f (Function.update x j true) ≤ f (Function.update x j false)
      else f (Function.update x j false) ≤ f (Function.update x j true)) :
    False := by
  rcases hunate with ⟨pol, hpol⟩
  cases pol
  · rcases hdown with ⟨x, h0, h1⟩
    have hle := hpol x
    simp only [Bool.false_eq_true, ↓reduceIte, h0, h1] at hle
    exact absurd hle (by decide)
  · rcases hup with ⟨x, h0, h1⟩
    have hle := hpol x
    simp only [↓reduceIte, h0, h1] at hle
    exact absurd hle (by decide)

lemma main_proof (n : Nat) (C : Circuit) (hfit : FanInTwo C) :
    let W := Fin n → Bool
    let f := fun (x : W) => C.eval (List.ofFn x)
    let essential := (Finset.univ : Finset (Fin n)).filter (fun j =>
      ∃ x : W, f (Function.update x j false) ≠ f (Function.update x j true))
    ∀ (a b c : Fin n) (x : W) (t : Bool), a ≠ b → a ≠ c → b ≠ c →
      let atBits := fun (u v w : Bool) =>
        f (Function.update (Function.update (Function.update x a u) b v) c w)
      atBits true false false = t → atBits false true true = t →
      atBits false true false = !t → atBits false false true = !t →
      atBits true true false = !t →
      (∃ y : W, f (Function.update y c false) = t ∧ f (Function.update y c true) = !t) →
      essential.card + 2 ≤ C.size := by
  classical
  dsimp only
  intro a b c x t hab hac hbc h100 h011 h010 h001 h110 hy_c
  let W := Fin n → Bool
  let f : W → Bool := fun z => C.eval (List.ofFn z)
  let essential : Finset (Fin n) := (Finset.univ : Finset (Fin n)).filter (fun j =>
    ∃ z : W, f (Function.update z j false) ≠ f (Function.update z j true))
  let x0 : Bool → Bool → Bool → W := fun u v w =>
    Function.update (Function.update (Function.update x a u) b v) c w
  change f (x0 true false false) = t at h100
  change f (x0 false true true) = t at h011
  change f (x0 false true false) = !t at h010
  change f (x0 false false true) = !t at h001
  change f (x0 true true false) = !t at h110
  have hb_t_nt : ∃ z : W, f (Function.update z b false) = t ∧ f (Function.update z b true) = !t := by
    refine ⟨x0 true false false, ?_, ?_⟩
    · have heq : Function.update (x0 true false false) b false = x0 true false false := by
        ext k
        by_cases hkc : k = c
        · subst hkc; simp [x0, hbc.symm]
        · by_cases hkb : k = b
          · subst hkb; simp [x0, hbc]
          · simp [x0, hkc, hkb]
      rw [heq]; exact h100
    · have heq : Function.update (x0 true false false) b true = x0 true true false := by
        ext k
        by_cases hkc : k = c
        · subst hkc; simp [x0, hbc.symm]
        · by_cases hkb : k = b
          · subst hkb; simp [x0, hbc]
          · simp [x0, hkc, hkb]
      rw [heq]; exact h110
  have hb_nt_t : ∃ z : W, f (Function.update z b false) = !t ∧ f (Function.update z b true) = t := by
    refine ⟨x0 false false true, ?_, ?_⟩
    · have heq : Function.update (x0 false false true) b false = x0 false false true := by
        ext k
        by_cases hkc : k = c
        · subst hkc; simp [x0, hbc.symm]
        · by_cases hkb : k = b
          · subst hkb; simp [x0, hbc]
          · simp [x0, hkc, hkb]
      rw [heq]; exact h001
    · have heq : Function.update (x0 false false true) b true = x0 false true true := by
        ext k
        by_cases hkc : k = c
        · subst hkc; simp [x0, hbc.symm]
        · by_cases hkb : k = b
          · subst hkb; simp [x0, hbc]
          · simp [x0, hkc, hkb]
      rw [heq]; exact h011
  have hc_nt_t : ∃ z : W, f (Function.update z c false) = !t ∧ f (Function.update z c true) = t := by
    refine ⟨x0 false true false, ?_, ?_⟩
    · have heq : Function.update (x0 false true false) c false = x0 false true false := by
        ext k
        by_cases hkc : k = c
        · subst hkc; simp [x0]
        · simp [x0, hkc]
      rw [heq]; exact h010
    · have heq : Function.update (x0 false true false) c true = x0 false true true := by
        ext k
        by_cases hkc : k = c
        · subst hkc; simp [x0]
        · simp [x0, hkc]
      rw [heq]; exact h011
  have hb_up : ∃ z : W, f (Function.update z b false) = false ∧ f (Function.update z b true) = true := by
    cases t
    · exact hb_t_nt
    · exact hb_nt_t
  have hb_down : ∃ z : W, f (Function.update z b false) = true ∧ f (Function.update z b true) = false := by
    cases t
    · exact hb_nt_t
    · exact hb_t_nt
  have hc_up : ∃ z : W, f (Function.update z c false) = false ∧ f (Function.update z c true) = true := by
    cases t
    · exact hy_c
    · exact hc_nt_t
  have hc_down : ∃ z : W, f (Function.update z c false) = true ∧ f (Function.update z c true) = false := by
    cases t
    · exact hc_nt_t
    · exact hy_c
  have hout_lt : C.output < n + C.gates.length := by
    by_contra hge
    push Not at hge
    rcases hb_up with ⟨z, _, h1⟩
    have hfalse : f (Function.update z b true) = false := wireVal_out_of_range C _ C.output hge
    rw [hfalse] at h1
    exact absurd h1 (by decide)
  have hout_ge : n ≤ C.output := by
    by_contra hlt
    push Not at hlt
    have hproj : ∀ z : W, f z = z ⟨C.output, hlt⟩ := fun z => wireVal_input C z ⟨C.output, hlt⟩
    rcases hb_down with ⟨z, h0, h1⟩
    rw [hproj] at h0
    rw [hproj] at h1
    by_cases hbo : ⟨C.output, hlt⟩ = b
    · rw [hbo, Function.update_self] at h0
      exact absurd h0 (by decide)
    · rw [Function.update_of_ne hbo] at h0 h1
      rw [h0] at h1
      exact absurd h1 (by decide)
  let r := C.output
  let Reach : Finset ℕ := (Finset.range (n + C.gates.length)).filter (fun w => Reaches n C r w)
  let G : Finset (Fin C.gates.length) :=
    Finset.univ.filter (fun i : Fin C.gates.length => n + i.val ∈ Reach)
  let Gnot : Finset (Fin C.gates.length) := G.filter (fun i => C.gates[i.val].op = GateOp.not)
  let Ein : Finset (Fin n) := Finset.univ.filter (fun j : Fin n => j.val ∈ Reach)
  have hr_mem : r ∈ Reach :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hout_lt, Relation.ReflTransGen.refl⟩
  have hmem_Reach : ∀ w : ℕ, w ∈ Reach ↔ Reaches n C r w := by
    intro w
    simp only [Reach, Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
    intro hw
    exact lt_of_le_of_lt (reaches_le hw) hout_lt
  have hess_sub : essential ⊆ Ein := by
    intro j hj
    rcases (Finset.mem_filter.mp hj).2 with ⟨z, hne⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ j, (hmem_Reach j.val).mpr ?_⟩
    by_contra hnr
    apply hne
    apply wireVal_congr_of_cone C hfit _ _ r hout_lt
    intro k hk
    have hkj : k ≠ j := by
      rintro rfl
      exact hnr hk
    rw [Function.update_of_ne hkj, Function.update_of_ne hkj]
  have hess_le_Ein : essential.card ≤ Ein.card := Finset.card_le_card hess_sub
  have hReach_card : Reach.card = Ein.card + G.card := by
    let R_in := Ein.image (fun j : Fin n => j.val)
    let R_g := G.image (fun i : Fin C.gates.length => n + i.val)
    have hunion : Reach = R_in ∪ R_g := by
      ext w
      simp only [R_in, R_g, Ein, G, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · intro hw
        have hw_lt : w < n + C.gates.length := (Finset.mem_range.mp (Finset.mem_filter.mp hw).1)
        by_cases hwn : w < n
        · exact Or.inl ⟨⟨w, hwn⟩, hw, rfl⟩
        · exact Or.inr ⟨⟨w - n, by omega⟩, by simpa [show n + (w - n) = w by omega] using hw,
            by dsimp; omega⟩
      · rintro (⟨j, hj, rfl⟩ | ⟨i, hi, rfl⟩) <;> exact ‹_›
    have hdisj : Disjoint R_in R_g := by
      rw [Finset.disjoint_left]
      intro w hw1 hw2
      rcases Finset.mem_image.mp hw1 with ⟨j, _, rfl⟩
      rcases Finset.mem_image.mp hw2 with ⟨i, _, heq⟩
      have := j.isLt
      omega
    rw [hunion, Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ Fin.val_injective,
      Finset.card_image_of_injective _ (fun x y h => Fin.ext (by omega))]
  have houtdeg_eq : ∀ w : ℕ, outdegIn n C r w = (G.filter (fun i => w ∈ gateDeps n C i)).card := by
    intro w
    unfold outdegIn
    congr 1
    ext i
    simp [G, hmem_Reach]
  have houtdeg_r : outdegIn n C r r = 0 := by
    rw [houtdeg_eq, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i hi hdep
    have h1 : n + i.val ≤ r := reaches_le ((hmem_Reach _).mp (Finset.mem_filter.mp hi).2)
    have h2 : r < n + i.val := gateDeps_lt n C i hdep
    omega
  have houtdeg_pos : ∀ w ∈ Reach.erase r, 1 ≤ outdegIn n C r w := by
    intro w hw
    rcases Finset.mem_erase.mp hw with ⟨hne, hwR⟩
    have hrw : Reaches n C r w := (hmem_Reach w).mp hwR
    cases Relation.ReflTransGen.cases_tail hrw with
    | inl heq => exact False.elim (hne heq)
    | inr hex =>
      rcases hex with ⟨u, hru, huw⟩
      rcases huw with ⟨i, rfl, hw_dep⟩
      rw [houtdeg_eq]
      exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ i, (hmem_Reach _).mpr hru⟩, hw_dep⟩⟩
  have hsum_deg : ∑ w ∈ Reach, outdegIn n C r w = ∑ i ∈ G, (gateDeps n C i).card := by
    simp_rw [houtdeg_eq]
    have h1 : ∑ w ∈ Reach, (G.filter (fun i => w ∈ gateDeps n C i)).card =
        ∑ w ∈ Reach, ∑ i ∈ G, if w ∈ gateDeps n C i then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro w _
      rw [Finset.card_filter]
    rw [h1, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    have hi_r : Reaches n C r (n + i.val) := (hmem_Reach _).mp (Finset.mem_filter.mp hi).2
    have hsub : gateDeps n C i ⊆ Reach := by
      intro w hw
      exact (hmem_Reach w).mpr (Relation.ReflTransGen.tail hi_r ⟨i, rfl, hw⟩)
    rw [← Finset.card_filter]
    have heq : Reach.filter (fun w => w ∈ gateDeps n C i) = gateDeps n C i := by
      ext w
      simp only [Finset.mem_filter, and_iff_right_iff_imp]
      exact fun hw => hsub hw
    rw [heq]
  have hsum_in_bound : ∑ i ∈ G, (gateDeps n C i).card + Gnot.card ≤ 2 * G.card := by
    have hsplit : ∑ i ∈ G, (gateDeps n C i).card =
        (∑ i ∈ Gnot, (gateDeps n C i).card) +
        (∑ i ∈ G.filter (fun i => ¬ C.gates[i.val].op = GateOp.not), (gateDeps n C i).card) :=
      (Finset.sum_filter_add_sum_filter_not G (fun i => C.gates[i.val].op = GateOp.not) _).symm
    have h1 : ∑ i ∈ Gnot, (gateDeps n C i).card ≤ Gnot.card := by
      calc ∑ i ∈ Gnot, (gateDeps n C i).card
          ≤ ∑ _i ∈ Gnot, 1 := Finset.sum_le_sum (fun i hi =>
            gateDeps_card_le_not n C i (Finset.mem_filter.mp hi).2)
        _ = Gnot.card := by simp
    have h2 : ∑ i ∈ G.filter (fun i => ¬ C.gates[i.val].op = GateOp.not), (gateDeps n C i).card ≤
        2 * (G.filter (fun i => ¬ C.gates[i.val].op = GateOp.not)).card := by
      calc ∑ i ∈ G.filter (fun i => ¬ C.gates[i.val].op = GateOp.not), (gateDeps n C i).card
          ≤ ∑ _i ∈ G.filter (fun i => ¬ C.gates[i.val].op = GateOp.not), 2 :=
            Finset.sum_le_sum (fun i _ => gateDeps_card_le_two n C hfit i)
        _ = 2 * (G.filter (fun i => ¬ C.gates[i.val].op = GateOp.not)).card := by
            rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    have hcard_split : Gnot.card + (G.filter (fun i => ¬ C.gates[i.val].op = GateOp.not)).card = G.card := by
      have hdisj : Disjoint Gnot (G.filter (fun i => ¬ C.gates[i.val].op = GateOp.not)) :=
        Finset.disjoint_filter.mpr (fun _ _ h1 h2 => h2 h1)
      rw [← Finset.card_union_of_disjoint hdisj, Finset.filter_union_filter_not_eq]
    omega
  let excess : ℕ := ∑ w ∈ Reach.erase r, (outdegIn n C r w - 1)
  have hsum_out_eq : ∑ w ∈ Reach, outdegIn n C r w = (Reach.card - 1) + excess := by
    have h1 := Finset.add_sum_erase Reach (outdegIn n C r) hr_mem
    rw [houtdeg_r, zero_add] at h1
    rw [← h1]
    have h2 : ∑ w ∈ Reach.erase r, outdegIn n C r w =
        ∑ w ∈ Reach.erase r, (1 + (outdegIn n C r w - 1)) := by
      apply Finset.sum_congr rfl
      intro w hw
      have := houtdeg_pos w hw
      omega
    rw [h2, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one,
      Finset.card_erase_of_mem hr_mem]
  have hG_le : G.card ≤ C.gates.length := by
    calc G.card ≤ (Finset.univ : Finset (Fin C.gates.length)).card := Finset.card_le_univ _
      _ = C.gates.length := by rw [Finset.card_univ, Fintype.card_fin]
  have hReach_pos : 1 ≤ Reach.card := Finset.card_pos.mpr ⟨r, hr_mem⟩
  have hmaster : essential.card + Gnot.card + excess ≤ C.gates.length + 1 := by
    omega
  by_contra hlt_size
  have hC_le : C.gates.length ≤ essential.card + 1 := by
    change ¬ essential.card + 2 ≤ C.gates.length at hlt_size
    omega
  have hGnot_pos : 1 ≤ Gnot.card := by
    by_contra h0
    have hGnot_empty : Gnot = ∅ := Finset.card_eq_zero.mp (by omega)
    have hnonot : ∀ i : Fin C.gates.length, Reaches n C r (n + i.val) →
        C.gates[i.val].op ≠ GateOp.not := by
      intro i hi hnot
      have hmem : i ∈ Gnot := Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ i, (hmem_Reach _).mpr hi⟩, hnot⟩
      rw [hGnot_empty] at hmem
      exact Finset.notMem_empty i hmem
    rcases hb_down with ⟨z, hz0, hz1⟩
    have hle : f (Function.update z b false) ≤ f (Function.update z b true) := by
      apply wireVal_mono_of_no_not C hfit _ _ r hout_lt hnonot
      intro k _
      by_cases hkb : k = b
      · subst hkb; simp
      · rw [Function.update_of_ne hkb, Function.update_of_ne hkb]
    rw [hz0, hz1] at hle
    exact absurd hle (by decide)
  have hexcess_le : excess ≤ 1 := by omega
  have hexcess_ne_zero : excess ≠ 0 := by
    intro hzero
    have hdeg1 : ∀ w, Reaches n C r w → w ≠ r → Reaches n C w b.val → outdegIn n C r w ≤ 1 := by
      intro w hwr hne _
      have hwE : w ∈ Reach.erase r := Finset.mem_erase.mpr ⟨hne, (hmem_Reach w).mpr hwr⟩
      have h0 : outdegIn n C r w - 1 = 0 := (Finset.sum_eq_zero_iff.mp hzero) w hwE
      omega
    have hunate := unate_of_no_fork_above C hfit r hout_lt b hdeg1 r Relation.ReflTransGen.refl
    exact non_monotone_contradiction f b hb_up hb_down hunate
  have hexcess_eq_one : excess = 1 := by omega
  have hGnot_eq_one : Gnot.card = 1 := by omega
  obtain ⟨s, hsE, hdeg_s_sub, hdeg_other⟩ :=
    exists_unique_of_sum_eq_one (Reach.erase r) (fun w => outdegIn n C r w - 1) hexcess_eq_one
  have hs_ne_r : s ≠ r := (Finset.mem_erase.mp hsE).1
  have hs_r : Reaches n C r s := (hmem_Reach s).mp (Finset.mem_erase.mp hsE).2
  have hs_lt_r : s < r := lt_of_le_of_ne (reaches_le hs_r) hs_ne_r
  have hs_lt : s < n + C.gates.length := lt_trans hs_lt_r hout_lt
  have hnot_s_r : ¬ Reaches n C s r := fun h => by
    have := reaches_le h
    omega
  have hdeg_non_s : ∀ w, Reaches n C r w → w ≠ r → w ≠ s → outdegIn n C r w ≤ 1 := by
    intro w hwr hnr hns
    have hwE : w ∈ Reach.erase r := Finset.mem_erase.mpr ⟨hnr, (hmem_Reach w).mpr hwr⟩
    have h0 := hdeg_other w hwE hns
    omega
  have hdeg_below_s : ∀ w, Reaches n C r w → w ≠ s → Reaches n C s w → outdegIn n C r w ≤ 1 := by
    intro w hwr hns hsw
    have hnr : w ≠ r := by
      have := reaches_le hsw
      omega
    exact hdeg_non_s w hwr hnr hns
  have hb_in_s : Reaches n C s b.val := by
    by_contra hnb
    have hdeg1 : ∀ w, Reaches n C r w → w ≠ r → Reaches n C w b.val → outdegIn n C r w ≤ 1 := by
      intro w hwr hnr hwb
      have hns : w ≠ s := by
        rintro rfl
        exact hnb hwb
      exact hdeg_non_s w hwr hnr hns
    have hunate := unate_of_no_fork_above C hfit r hout_lt b hdeg1 r Relation.ReflTransGen.refl
    exact non_monotone_contradiction f b hb_up hb_down hunate
  have hc_in_s : Reaches n C s c.val := by
    by_contra hnc
    have hdeg1 : ∀ w, Reaches n C r w → w ≠ r → Reaches n C w c.val → outdegIn n C r w ≤ 1 := by
      intro w hwr hnr hwc
      have hns : w ≠ s := by
        rintro rfl
        exact hnc hwc
      exact hdeg_non_s w hwr hnr hns
    have hunate := unate_of_no_fork_above C hfit r hout_lt c hdeg1 r Relation.ReflTransGen.refl
    exact non_monotone_contradiction f c hc_up hc_down hunate
  obtain ⟨iN, hiN_eq⟩ := Finset.card_eq_one.mp hGnot_eq_one
  have hiN_mem : iN ∈ Gnot := by rw [hiN_eq]; exact Finset.mem_singleton_self iN
  have hnot_below_s : ¬ Reaches n C s (n + iN.val) := by
    intro hiN_s
    have hnonot_out : ∀ i : Fin C.gates.length, Reaches n C r (n + i.val) →
        ¬ Reaches n C s (n + i.val) → C.gates[i.val].op ≠ GateOp.not := by
      intro i hir hins hnot
      have hi_mem : i ∈ Gnot := Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ i, (hmem_Reach _).mpr hir⟩, hnot⟩
      rw [hiN_eq, Finset.mem_singleton] at hi_mem
      subst hi_mem
      exact hins hiN_s
    have hdeg_in_s : ∀ w, Reaches n C s w → w ≠ s → Reaches n C w b.val → outdegIn n C s w ≤ 1 := by
      intro w hsw hns _
      have hsub :
          Finset.univ.filter (fun i : Fin C.gates.length => Reaches n C s (n + i.val) ∧ w ∈ gateDeps n C i) ⊆
          Finset.univ.filter (fun i : Fin C.gates.length => Reaches n C r (n + i.val) ∧ w ∈ gateDeps n C i) := by
        intro i hi
        rcases Finset.mem_filter.mp hi with ⟨_, his, hdep⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, Relation.ReflTransGen.trans hs_r his, hdep⟩
      have hle1 : outdegIn n C s w ≤ outdegIn n C r w := Finset.card_le_card hsub
      have hle2 := hdeg_below_s w (Relation.ReflTransGen.trans hs_r hsw) hns hsw
      omega
    obtain ⟨pol_s, hpol_s⟩ :=
      unate_of_no_fork_above C hfit s hs_lt b hdeg_in_s s Relation.ReflTransGen.refl
    have hunate_b : ∃ pol : Bool, ∀ z : W,
        if pol then f (Function.update z b true) ≤ f (Function.update z b false)
        else f (Function.update z b false) ≤ f (Function.update z b true) := by
      refine ⟨pol_s, ?_⟩
      intro z
      cases hps : pol_s
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have hs_le : wireVal C (Function.update z b false) s ≤ wireVal C (Function.update z b true) s := by
          have hz := hpol_s z
          simpa [hps] using hz
        apply wireVal_mono_outside_cone C hfit r s hout_lt hs_r hdeg_below_s hnonot_out
          _ _ hs_le _ r Relation.ReflTransGen.refl hnot_s_r
        intro k _ hks
        have hkb : k ≠ b := by
          rintro rfl
          exact hks hb_in_s
        rw [Function.update_of_ne hkb, Function.update_of_ne hkb]
      · simp only [↓reduceIte]
        have hs_le : wireVal C (Function.update z b true) s ≤ wireVal C (Function.update z b false) s := by
          have hz := hpol_s z
          simpa [hps] using hz
        apply wireVal_mono_outside_cone C hfit r s hout_lt hs_r hdeg_below_s hnonot_out
          _ _ hs_le _ r Relation.ReflTransGen.refl hnot_s_r
        intro k _ hks
        have hkb : k ≠ b := by
          rintro rfl
          exact hks hb_in_s
        rw [Function.update_of_ne hkb, Function.update_of_ne hkb]
    exact non_monotone_contradiction f b hb_up hb_down hunate_b
  have hnonot_s : ∀ i : Fin C.gates.length, Reaches n C s (n + i.val) →
      C.gates[i.val].op ≠ GateOp.not := by
    intro i his hnot
    have hi_mem : i ∈ Gnot := Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ i, (hmem_Reach _).mpr (Relation.ReflTransGen.trans hs_r his)⟩, hnot⟩
    rw [hiN_eq, Finset.mem_singleton] at hi_mem
    subst hi_mem
    exact hnot_below_s his
  have hs_mono : ∀ z1 z2 : W, (∀ k : Fin n, z1 k ≤ z2 k) → wireVal C z1 s ≤ wireVal C z2 s := by
    intro z1 z2 hle
    exact wireVal_mono_of_no_not C hfit z1 z2 s hs_lt hnonot_s (fun k _ => hle k)
  let sv : Bool → Bool → Bool → Bool := fun u v w => wireVal C (x0 u v w) s
  have hsv_mono : ∀ u1 v1 w1 u2 v2 w2 : Bool,
      u1 ≤ u2 → v1 ≤ v2 → w1 ≤ w2 → sv u1 v1 w1 ≤ sv u2 v2 w2 := by
    intro u1 v1 w1 u2 v2 w2 hu hv hw
    apply hs_mono
    intro k
    by_cases hkc : k = c
    · subst hkc; simp [x0, hw]
    · by_cases hkb : k = b
      · subst hkb; simp [x0, hkc, hv]
      · by_cases hka : k = a
        · subst hka; simp [x0, hkc, hkb, hu]
        · simp [x0, hkc, hkb, hka]
  have hf_eq_of_sv_same_u : ∀ u v1 w1 v2 w2 : Bool,
      sv u v1 w1 = sv u v2 w2 → f (x0 u v1 w1) = f (x0 u v2 w2) := by
    intro u v1 w1 v2 w2 hseq
    apply wireVal_congr_outside_cone C hfit r s hout_lt hs_r hdeg_below_s
      (x0 u v1 w1) (x0 u v2 w2) hseq _ r Relation.ReflTransGen.refl hnot_s_r
    intro k _ hks
    have hkb : k ≠ b := by rintro rfl; exact hks hb_in_s
    have hkc : k ≠ c := by rintro rfl; exact hks hc_in_s
    simp [x0, hkc, hkb]
  have hsv_010_011 : sv false true false ≠ sv false true true := by
    intro heq
    have hfeq := hf_eq_of_sv_same_u false true false true true heq
    rw [h010, h011] at hfeq
    cases t <;> exact absurd hfeq (by decide)
  have hsv_010_le : sv false true false ≤ sv false true true :=
    hsv_mono false true false false true true le_rfl le_rfl (by decide)
  have hsv_010 : sv false true false = false := by
    cases h1 : sv false true false
    · rfl
    · cases h2 : sv false true true
      · rw [h1, h2] at hsv_010_le
        exact absurd hsv_010_le (by decide)
      · exact absurd (h1.trans h2.symm) hsv_010_011
  have hsv_011 : sv false true true = true := by
    cases h2 : sv false true true
    · exact absurd (hsv_010.trans h2.symm) hsv_010_011
    · rfl
  have hsv_000 : sv false false false = false := by
    have hle : sv false false false ≤ sv false true false :=
      hsv_mono false false false false true false le_rfl (by decide) le_rfl
    rw [hsv_010] at hle
    cases h : sv false false false
    · rfl
    · rw [h] at hle
      exact absurd hle (by decide)
  by_cases ha_s : Reaches n C s a.val
  · have hf_eq_of_sv : ∀ u1 v1 w1 u2 v2 w2 : Bool,
        sv u1 v1 w1 = sv u2 v2 w2 → f (x0 u1 v1 w1) = f (x0 u2 v2 w2) := by
      intro u1 v1 w1 u2 v2 w2 hseq
      apply wireVal_congr_outside_cone C hfit r s hout_lt hs_r hdeg_below_s
        (x0 u1 v1 w1) (x0 u2 v2 w2) hseq _ r Relation.ReflTransGen.refl hnot_s_r
      intro k _ hks
      have hka : k ≠ a := by rintro rfl; exact hks ha_s
      have hkb : k ≠ b := by rintro rfl; exact hks hb_in_s
      have hkc : k ≠ c := by rintro rfl; exact hks hc_in_s
      simp [x0, hkc, hkb, hka]
    have hsv_100 : sv true false false = true := by
      cases h : sv true false false
      · have hfeq := hf_eq_of_sv true false false false true false (h.trans hsv_010.symm)
        rw [h100, h010] at hfeq
        cases t <;> exact absurd hfeq (by decide)
      · rfl
    have hsv_110 : sv true true false = false := by
      cases h : sv true true false
      · rfl
      · have hfeq := hf_eq_of_sv true true false false true true (h.trans hsv_011.symm)
        rw [h110, h011] at hfeq
        cases t <;> exact absurd hfeq (by decide)
    have hle := hsv_mono true false false true true false le_rfl (by decide) le_rfl
    rw [hsv_100, hsv_110] at hle
    exact absurd hle (by decide)
  · have hsv_indep_a : ∀ v w : Bool, sv true v w = sv false v w := by
      intro v w
      apply wireVal_congr_of_cone C hfit (x0 true v w) (x0 false v w) s hs_lt
      intro k hk
      have hka : k ≠ a := by rintro rfl; exact ha_s hk
      by_cases hkc : k = c
      · subst hkc; simp [x0]
      · by_cases hkb : k = b
        · subst hkb; simp [x0, hkc]
        · simp [x0, hkc, hkb, hka]
    have hsv_100 : sv true false false = false := (hsv_indep_a false false).trans hsv_000
    have hsv_110 : sv true true false = false := (hsv_indep_a true false).trans hsv_010
    have hfeq := hf_eq_of_sv_same_u true false false true false (hsv_100.trans hsv_110.symm)
    rw [h100, h110] at hfeq
    cases t <;> exact absurd hfeq (by decide)

end PEqualNP.Outside.L_lib_555_aux

namespace PEqualNP.Outside.L_lib_555
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
private def pair {n : ℕ} (i j : Fin n) (k : Fin n) := decide (k = i ∨ k = j)
private def target {n : ℕ} (h : ℕ) (i j : Fin n) :=
  decide ((min i.val j.val = 0 ∧ (max i.val j.val = 0 ∨ 3+h ≤ max i.val j.val)) ∨
    (min i.val j.val = 1 ∧ max i.val j.val = 2))
private def val {n : ℕ} (C : Circuit) (x : Fin n → Bool) := C.eval (List.ofFn x)
private def essentials (n : ℕ) (C : Circuit) := (Finset.univ : Finset (Fin n)).filter
  (fun j => ∃ x : Fin n → Bool, val C (Function.update x j false) ≠ val C (Function.update x j true))
private def leaves (h t : ℕ) := (Finset.univ : Finset (Fin (3+h+t))).filter (fun j => 3+h ≤ j.val)
private def active (h t : ℕ) (C : Circuit) := (leaves h t).filter (fun j =>
  ∃ x : Fin (3+h+t) → Bool, val C (Function.update x j false) ≠ val C (Function.update x j true))

private theorem diff_at {n : ℕ} {C : Circuit} {i : Fin n} {x y : Fin n → Bool}
    (he : ∀ j, j ≠ i → x j = y j) (hx : x i = false) (hy : y i = true)
    (hf : val C x ≠ val C y) : i ∈ essentials n C := by
  have e0 : Function.update x i false = x := by ext j; by_cases h : j = i <;> simp_all
  have e1 : Function.update x i true = y := by ext j; by_cases h : j = i <;> simp_all
  exact Finset.mem_filter.mpr ⟨by simp,x,by simpa [e0,e1] using hf⟩

private theorem lower (h t : ℕ) (ht : 0 < t) (C : Circuit) (hf : FanInTwo C)
    (hp : ∀ i j : Fin (3+h+t), val C (pair i j) = target h i j) :
    h + 5 + (active h t C).card ≤ C.size := by
  let n := 3+h+t
  let a : Fin n := ⟨0,by dsimp [n]; omega⟩
  let b : Fin n := ⟨1,by dsimp [n]; omega⟩
  let c : Fin n := ⟨2,by dsimp [n]; omega⟩
  have hab : a ≠ b := fun he => by have := congrArg Fin.val he; simp [a,b] at this
  have hac : a ≠ c := fun he => by have := congrArg Fin.val he; simp [a,c] at this
  have hbc : b ≠ c := fun he => by have := congrArg Fin.val he; simp [b,c] at this
  have edge : ∀ (i j : Fin n), val C (pair i j) = target h i j := hp
  let at3 (u v w : Bool) := Function.update (Function.update (Function.update
    (fun _ : Fin n => false) a u) b v) c w
  have ha0 : at3 true false false = pair a a := by
    ext k; by_cases h1 : k = a <;> by_cases h2 : k = b <;> by_cases h3 : k = c <;> simp_all [at3,pair]
  have hb0 : at3 false true false = pair b b := by
    ext k; by_cases h1 : k = a <;> by_cases h2 : k = b <;> by_cases h3 : k = c <;> simp_all [at3,pair]
  have hc0 : at3 false false true = pair c c := by
    ext k; by_cases h1 : k = a <;> by_cases h2 : k = b <;> by_cases h3 : k = c <;> simp_all [at3,pair]
  have hbc0 : at3 false true true = pair b c := by
    ext k; by_cases h1 : k = a <;> by_cases h2 : k = b <;> by_cases h3 : k = c <;> simp_all [at3,pair]
  have hab0 : at3 true true false = pair a b := by
    ext k; by_cases h1 : k = a <;> by_cases h2 : k = b <;> by_cases h3 : k = c <;> simp_all [at3,pair]
  have h10 : val C (at3 true false false) = true := by simp [ha0,edge,target,a]
  have h01 : val C (at3 false true true) = true := by simp [hbc0,edge,target,b,c]
  have h010 : val C (at3 false true false) = false := by simp [hb0,edge,target,b]
  have h001 : val C (at3 false false true) = false := by simp [hc0,edge,target,c]
  have h110 : val C (at3 true true false) = false := by simp [hab0,edge,target,a,b]; omega
  have hflip (i : Fin n) (hn : i ≠ a) :
      Function.update (pair a a) i false = pair a a ∧ Function.update (pair a a) i true = pair a i := by
    constructor <;> ext k <;> by_cases hki : k = i <;> simp_all [pair]
  have hrev : ∃ y : Fin n → Bool, val C (Function.update y c false) = true ∧
      val C (Function.update y c true) = false := by
    refine ⟨pair a a,?_,?_⟩
    · rw [(hflip c hac.symm).1,edge]; simp [target,a]
    · rw [(hflip c hac.symm).2,edge]; simp [target,a,c]; omega
  have size : (essentials n C).card + 2 ≤ C.size :=
    PEqualNP.Outside.L_lib_555_aux.main_proof n C hf a b c (fun _ => false) true
      hab hac hbc h10 h01 h010 h001 h110 hrev
  let first : Finset (Fin n) := (Finset.univ : Finset (Fin (3+h))).map
    (Fin.castLEEmb (show 3+h ≤ n by dsimp [n]; omega))
  have firstmem (k : Fin n) : k ∈ first ↔ k.val < 3+h := by
    simp only [first,Finset.mem_map,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨v,rfl⟩; exact v.isLt
    · intro hv; exact ⟨⟨k.val,hv⟩,Fin.ext rfl⟩
  have fsub : first ⊆ essentials n C := by
    intro i hi
    have hi' := (firstmem i).mp hi
    by_cases hia : i = a
    · subst i
      let d : Fin n := ⟨3+h,by dsimp [n]; omega⟩
      have had : a ≠ d := fun he => by have := congrArg Fin.val he; simp [a,d] at this; omega
      apply diff_at (x := pair d d) (y := pair a d)
      · intro j hj; simp [pair,hj]
      · simp [pair,had]
      · simp [pair]
      · rw [edge,edge]; simp [target,a,d]; omega
    · refine Finset.mem_filter.mpr ⟨by simp,pair a a,?_⟩
      rw [(hflip i hia).1,(hflip i hia).2,edge,edge]
      have hi0 : i.val ≠ 0 := fun he => hia (Fin.ext he)
      simp [target,a,hi0,hi'.not_ge]
  have asub : active h t C ⊆ essentials n C := fun i hi =>
    Finset.mem_filter.mpr ⟨by simp,(Finset.mem_filter.mp hi).2⟩
  have hdis : Disjoint first (active h t C) := by
    apply Finset.disjoint_left.mpr
    intro k hf ha
    have := (firstmem k).mp hf
    have := (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).2
    omega
  have hh := Finset.card_le_card (Finset.union_subset fsub asub)
  have cf : first.card = 3+h := by simp [first]
  rw [Finset.card_union_of_disjoint hdis,cf] at hh
  omega

open PEqualNP.Outside.L_lib_555_aux
private def nextWire {n : ℕ} (gs : List Gate) : ℕ := n + gs.length
private def read {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (k : ℕ) :=
  (gs.foldl stepWires (List.ofFn x)).getD k false
private theorem read_input {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : Fin n) :
    read gs x i.val = x i := by
  unfold read
  rw [foldl_stepWires_getD_lt gs _ _ (by simpa using i.isLt)]
  simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem,i.isLt]
private theorem read_snoc {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (g : Gate) :
    read (gs ++ [g]) x (@nextWire n gs) = g.op.eval (g.inputs.map (read gs x)) := by
  unfold read nextWire
  simp only [List.foldl_append,List.foldl_cons,List.foldl_nil,stepWires]
  have hl : (gs.foldl stepWires (List.ofFn x)).length = n + gs.length := by
    rw [foldl_stepWires_length]; simp
  rw [←hl]
  simp [List.getD_eq_getElem?_getD]
private theorem read_keep {n : ℕ} (gs extras : List Gate) (x : Fin n → Bool) (k : ℕ)
    (hk : k < @nextWire n gs) : read (gs ++ extras) x k = read gs x k := by
  unfold read
  rw [List.foldl_append,foldl_stepWires_getD_lt]
  rw [foldl_stepWires_length]
  simpa [nextWire] using hk

private def gOr (u v : ℕ) : Gate := ⟨.or,[u,v]⟩
private def gAnd (u v : ℕ) : Gate := ⟨.and,[u,v]⟩
private def gNot (u : ℕ) : Gate := ⟨.not,[u]⟩
private def good (g : Gate) :=
  g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2
private theorem goodOr (i j : ℕ) : good (gOr i j) := by simp [good,gOr]
private theorem goodAnd (i j : ℕ) : good (gAnd i j) := by simp [good,gAnd]
private theorem goodNot (i : ℕ) : good (gNot i) := by simp [good,gNot]

private theorem appendOr {n : ℕ} (gs : List Gate) (u : ℕ) (xs : List (Fin n))
    (hu : u < @nextWire n gs) :
    ∃ (more : List Gate) (v : ℕ), more.length = xs.length ∧
      (∀ g ∈ more, good g) ∧ v < @nextWire n (gs ++ more) ∧
      ∀ x : Fin n → Bool, read (gs ++ more) x v = (read gs x u || xs.any x) := by
  induction xs generalizing gs u with
  | nil => exact ⟨[],u,rfl,by simp,by simpa using hu,by simp⟩
  | cons i xs ih =>
    let g := gOr u i.val
    let gs' := gs ++ [g]
    let z := @nextWire n gs
    obtain ⟨tail,v,hlen,hgood,hv,hvalue⟩ := ih gs' z (by simp [gs',z,nextWire])
    refine ⟨g :: tail,v,by simp [hlen],?_,?_,?_⟩
    · intro gate hgate
      rcases List.mem_cons.mp hgate with h | h
      · exact h ▸ goodOr u i.val
      · exact hgood gate h
    · simpa [gs',List.append_assoc] using hv
    · intro x
      have he : read gs' x z = (read gs x u || x i) := by
        rw [show read gs' x z = _ from read_snoc gs x g]
        simp [g,gOr,GateOp.eval,read_input]
      simpa [gs',he,List.append_assoc,Bool.or_assoc] using hvalue x

private def blockers (h t : ℕ) : List (Fin (3+h+t)) :=
  List.ofFn (fun j : Fin h => ⟨3+j.val,by omega⟩)
private theorem blocker_mem {h t : ℕ} (i : Fin (3+h+t)) :
    i ∈ blockers h t ↔ 3 ≤ i.val ∧ i.val < 3+h := by
  simp only [blockers,List.mem_ofFn]
  constructor
  · rintro ⟨j,rfl⟩; exact ⟨by simp,by change 3+j.val < 3+h; omega⟩
  · rintro ⟨h1,h2⟩; exact ⟨⟨i.val-3,by omega⟩,Fin.ext (by simp; omega)⟩

private def funStar {n : ℕ} (a b c : Fin n) (black white : List (Fin n)) (x : Fin n → Bool) :=
  (x a && (!(x b || black.any x) || white.any x)) || (x b && x c)

private theorem makeStar {n : ℕ} (a b c : Fin n) (black white : List (Fin n)) :
    ∃ C : Circuit, FanInTwo C ∧ C.size = black.length + white.length + 4 ∧
      ∀ x : Fin n → Bool, val C x = funStar a b c black white x := by
  obtain ⟨g0,v,h0,hg0,hv,hvval⟩ := appendOr ([] : List Gate) b.val black (by simpa [nextWire] using b.isLt)
  simp only [List.nil_append] at hv hvval
  let notGate := gNot v
  let q := @nextWire n g0
  let g1 := g0 ++ [notGate]
  have hq : q < @nextWire n g1 := by simp [q,g1,nextWire]
  obtain ⟨more,w,hm,hgm,hw,hwm⟩ := appendOr g1 q white hq
  let g2 := g1 ++ more
  let u := @nextWire n g2
  let both := gAnd a.val w
  let ends := gAnd b.val c.val
  let g3 := g2 ++ [both]
  let e := @nextWire n g3
  let g4 := g3 ++ [ends]
  let gs := g4 ++ [gOr u e]
  refine ⟨⟨gs,@nextWire n g4⟩,?_,?_,?_⟩
  · intro g hg
    simp only [gs,g4,g3,g2,g1,List.mem_append,List.mem_singleton] at hg
    rcases hg with ((((h|rfl)|h)|rfl)|rfl)|rfl
    · exact hg0 _ h
    · exact goodNot v
    · exact hgm _ h
    · exact goodAnd _ _
    · exact goodAnd _ _
    · exact goodOr _ _
  · simp [Circuit.size,gs,g4,g3,g2,g1,h0,hm]; omega
  · intro x
    have hb : read g0 x v = (x b || black.any x) := by simpa [read_input] using hvval x
    have hqval : read g1 x q = !(x b || black.any x) := by
      rw [show read g1 x q = _ from read_snoc g0 x notGate]
      simp [notGate,gNot,GateOp.eval,hb]
    have hww : read g2 x w = (!(x b || black.any x) || white.any x) := by simpa [hqval] using hwm x
    have hua : read g3 x u = (x a && (!(x b || black.any x) || white.any x)) := by
      rw [show read g3 x u = _ from read_snoc g2 x both]
      simp [both,gAnd,GateOp.eval,read_input,hww]
    have huu : read g4 x u = read g3 x u := by
      apply read_keep; simp [u,g3,nextWire]
    have hee : read g4 x e = (x b && x c) := by
      rw [show read g4 x e = _ from read_snoc g3 x ends]
      simp [ends,gAnd,GateOp.eval,read_input]
    change read gs x (@nextWire n g4) = _
    rw [show read gs x (@nextWire n g4) = _ from read_snoc g4 x (gOr u e)]
    simp [gOr,GateOp.eval,huu,hua,hee,funStar]

private theorem anyPair {n : ℕ} (lst : List (Fin n)) (i j : Fin n) :
    lst.any (pair i j) = decide (i ∈ lst ∨ j ∈ lst) := by
  apply Bool.eq_iff_iff.mpr
  simp [List.any_eq_true,pair]
  aesop

private theorem edge_arithmetic (x y h : ℕ) (p q : Prop) (hp : p → 3+h ≤ x) (hq : q → 3+h ≤ y) :
 (0 = x ∨ 0 = y) ∧ (((¬1=x ∧ ¬1=y) ∧ (¬x=2 ∧ ¬(3≤x ∧ x<3+h)) ∧ ¬y=2 ∧ ¬(3≤y ∧ y<3+h)) ∨ p ∨ q)
 ∨ (1=x ∨ 1=y) ∧ (2=x ∨ 2=y) ↔
 (x=0 ∨ y=0) ∧ (x=0 ∧ y=0 ∨ 3+h≤x ∨ 3+h≤y) ∨ min x y=1 ∧ max x y=2 := by
 grind

private theorem upper (h t : ℕ) (ht : 0 < t) (S : Finset (Fin (3+h+t))) (hs : S ⊆ leaves h t) :
    ∃ C : Circuit, (FanInTwo C ∧ ∀ i j : Fin (3+h+t), val C (pair i j) = target h i j) ∧
      active h t C = S ∧ C.size = h+5+S.card := by
  let n := 3+h+t
  let a : Fin n := ⟨0,by dsimp [n]; omega⟩
  let b : Fin n := ⟨1,by dsimp [n]; omega⟩
  let c : Fin n := ⟨2,by dsimp [n]; omega⟩
  let black := c :: blockers h t
  obtain ⟨C,hC,hsize,he⟩ := makeStar a b c black S.toList
  have hleaf (i : Fin n) (hh : i ∈ S) : 3+h ≤ i.val := (Finset.mem_filter.mp (hs hh)).2
  refine ⟨C,⟨hC,?_⟩,?_,?_⟩
  · intro i j
    have hi := hleaf i
    have hj := hleaf j
    rw [he]
    apply Bool.eq_iff_iff.mpr
    simp only [funStar, anyPair,black,List.mem_cons,blocker_mem,Finset.mem_toList,target,pair,Fin.ext_iff]
    simp [a,b,c]
    have hbi : i ∈ blockers h t ↔ 3 ≤ i.val ∧ i.val < 3+h := blocker_mem i
    have hbj : j ∈ blockers h t ↔ 3 ≤ j.val ∧ j.val < 3+h := blocker_mem j
    rw [hbi,hbj]
    simp only [Fin.ext_iff,Fin.val_zero]
    exact edge_arithmetic i.val j.val h (i ∈ S) (j ∈ S) hi hj
  · ext j
    constructor
    · intro hj
      obtain ⟨hl,x,hx⟩ := Finset.mem_filter.mp hj
      have hjv := (Finset.mem_filter.mp hl).2
      by_contra hn
      have hja : a ≠ j := by intro hh; have := congrArg Fin.val hh; simp [a] at this; omega
      have hjb : b ≠ j := by intro hh; have := congrArg Fin.val hh; simp [b] at this; omega
      have hjc : c ≠ j := by intro hh; have := congrArg Fin.val hh; simp [c] at this; omega
      have hbl : j ∉ black := by
        intro hh
        rcases List.mem_cons.mp hh with hc | hh
        · exact hjc hc.symm
        · have := (blocker_mem j).mp hh; omega
      have hnever (l : List (Fin n)) (hl : j ∉ l) (v : Bool) :
          l.any (Function.update x j v) = l.any x := by
        induction l with
        | nil => rfl
        | cons k l ih =>
          have hk : k ≠ j := fun he => hl (by simp [he])
          simp [List.any_cons,Function.update_of_ne hk,ih (fun hm => hl (by simp [hm]))]
      apply hx
      rw [he,he]
      simp [funStar,hnever black hbl,hnever S.toList (by simpa using hn),Function.update_of_ne hja,
        Function.update_of_ne hjb,Function.update_of_ne hjc]
    · intro hj
      have hjv := hleaf j hj
      have hja : a ≠ j := by intro hh; have := congrArg Fin.val hh; simp [a] at this; omega
      have hjb : b ≠ j := by intro hh; have := congrArg Fin.val hh; simp [b] at this; omega
      have hjc : c ≠ j := by intro hh; have := congrArg Fin.val hh; simp [c] at this; omega
      let x := pair a b
      have hw0 : S.toList.any (Function.update x j false) = false := by
        apply Bool.eq_false_iff.mpr
        intro hh
        obtain ⟨k,hk,hkval⟩ := List.any_eq_true.mp hh
        have hk' := hleaf k (by simpa using hk)
        by_cases hh : k = j
        · simp [hh] at hkval
        · rw [Function.update_of_ne hh] at hkval
          simp only [x,pair,decide_eq_true_eq,Fin.ext_iff] at hkval
          dsimp [a,b] at hkval
          omega
      have hw1 : S.toList.any (Function.update x j true) = true :=
        List.any_eq_true.mpr ⟨j,by simpa using hj,by simp⟩
      refine Finset.mem_filter.mpr ⟨hs hj,x,?_⟩
      rw [he,he]
      simp only [funStar,hw0,hw1,Function.update_of_ne hja,Function.update_of_ne hjb,Function.update_of_ne hjc]
      simp only [x,pair,Fin.ext_iff]
      simp [a,b,c]
  · simp [black,blockers] at hsize; omega
end PEqualNP.Outside.L_lib_555


theorem PEqualNP.Outside.L_lib_555 : (∀ (h t : ℕ), 0 < t →
  let n := 3+h+t
  let leaves := (Finset.univ : Finset (Fin n)).filter (fun i => 3+h ≤ i.val)
  let visible := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
    PEqualNP.MetaComplexity.FanInTwo C ∧ ∀ i j : Fin n,
      let u := min i.val j.val
      let v := max i.val j.val
      C.eval (List.ofFn fun s : Fin n => decide (s = i ∨ s = j)) =
        decide ((u = 0 ∧ (v = 0 ∨ 3+h ≤ v)) ∨ (u = 1 ∧ v = 2))
  let active := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
    leaves.filter (fun j => ∃ x : Fin n → Bool,
      C.eval (List.ofFn (Function.update x j false)) ≠ C.eval (List.ofFn (Function.update x j true)))
  (∀ C, visible C → h + 5 + (active C).card ≤ C.size) ∧
    ∀ S : Finset (Fin n), S ⊆ leaves →
      ∃ C, visible C ∧ active C = S ∧ C.size = h+5+S.card) := by
  intro h t ht
  exact ⟨fun C hv => PEqualNP.Outside.L_lib_555.lower h t ht C hv.1 hv.2, PEqualNP.Outside.L_lib_555.upper h t ht⟩

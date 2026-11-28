import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1191_aux

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.NotBracket

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma circuit_wires_eq (C : Circuit) (x : List Bool) :
    C.wires x = wiresFrom C.gates x := rfl

lemma wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

lemma wiresFrom_append (gs1 gs2 : List Gate) (w : List Bool) :
    wiresFrom (gs1 ++ gs2) w = wiresFrom gs2 (wiresFrom gs1 w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    rw [wiresFrom_cons, ih]
    simp
    omega

lemma getD_append_left {α : Type*} (l1 l2 : List α) (i : ℕ) (d : α) (hi : i < l1.length) :
    (l1 ++ l2).getD i d = l1.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_right {α : Type*} (l1 l2 : List α) (i : ℕ) (d : α) (hi : l1.length ≤ i) :
    (l1 ++ l2).getD i d = l2.getD (i - l1.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right hi]

lemma wiresFrom_getD_lt (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < w.length) :
    (wiresFrom gs w).getD k false = w.getD k false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [wiresFrom_cons, ih]
    · exact getD_append_left _ _ k false hk
    · simp; omega

lemma gateAt_eq_getElem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

lemma wiresFrom_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (wiresFrom gs w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i => (wiresFrom (gs.take j) w).getD i false) := by
  have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by
    have h1 : gs.take j ++ gs.drop j = gs := List.take_append_drop j gs
    have h2 : gs.drop j = gs[j] :: gs.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    exact h1.symm
  conv_lhs => rw [hsplit]
  rw [wiresFrom_append, wiresFrom_cons]
  have hlen : (wiresFrom (gs.take j) w).length = w.length + j := by
    rw [wiresFrom_length, List.length_take, Nat.min_eq_left (le_of_lt hj)]
  rw [wiresFrom_getD_lt _ _ (w.length + j) (by simp [hlen])]
  rw [getD_append_right _ _ (w.length + j) false (by omega)]
  simp [hlen]

lemma wiresFrom_getD_gate_readsBack (gs : List Gate) (w : List Bool)
    (hrb : ReadsBack w.length ⟨gs, 0⟩) (j : ℕ) (hj : j < gs.length) :
    (wiresFrom gs w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i => (wiresFrom gs w).getD i false) := by
  rw [wiresFrom_getD_gate gs w j hj]
  congr 1
  refine List.map_congr_left (fun i hi => ?_)
  have hi_lt : i < w.length + j := by
    have h := hrb j hj
    rw [gateAt_eq_getElem _ j hj] at h
    exact h i hi
  have hsplit : gs = gs.take j ++ gs.drop j := (List.take_append_drop j gs).symm
  conv_rhs => rw [hsplit, wiresFrom_append]
  have hlen : (wiresFrom (gs.take j) w).length = w.length + j := by
    rw [wiresFrom_length, List.length_take, Nat.min_eq_left (le_of_lt hj)]
  symm
  exact wiresFrom_getD_lt (gs.drop j) (wiresFrom (gs.take j) w) i (by omega)

lemma notCount_append (gs1 gs2 : List Gate) (o : ℕ) :
    notCount ⟨gs1 ++ gs2, o⟩ = notCount ⟨gs1, 0⟩ + notCount ⟨gs2, 0⟩ := by
  simp [notCount, List.filter_append]

lemma notCount_map_inputs (gs : List Gate) (f : List ℕ → List ℕ) (o : ℕ) :
    notCount ⟨gs.map (fun g => ⟨g.op, f g.inputs⟩), o⟩ = notCount ⟨gs, 0⟩ := by
  induction gs with
  | nil => simp [notCount]
  | cons g gs ih =>
    simp only [notCount, List.map_cons, List.filter_cons] at ih ⊢
    by_cases h : g.op = GateOp.not
    · simp [h, ih]
    · simp [h, ih]

lemma notCount_and_gates (gs : List Gate) (h : ∀ g ∈ gs, g.op = GateOp.and) (o : ℕ) :
    notCount ⟨gs, o⟩ = 0 := by
  induction gs with
  | nil => simp [notCount]
  | cons g gs ih =>
    have hg : g.op = GateOp.and := h g (List.mem_cons_self ..)
    have hgs : ∀ g' ∈ gs, g'.op = GateOp.and := fun g' hg' => h g' (List.mem_cons_of_mem _ hg')
    cases g with
    | mk op ins =>
      dsimp only at hg
      subst hg
      exact ih hgs

lemma notCount_remove_one (gs : List Gate) (j0 : ℕ) (hj0 : j0 < gs.length) (o : ℕ) :
    notCount ⟨gs.take j0 ++ gs.drop (j0 + 1), o⟩ ≤ notCount ⟨gs, 0⟩ := by
  have hsplit : gs = gs.take j0 ++ (gs[j0] :: gs.drop (j0 + 1)) := by
    have h1 := List.take_append_drop j0 gs
    rw [List.drop_eq_getElem_cons hj0] at h1
    exact h1.symm
  conv_rhs => rw [hsplit]
  rw [notCount_append, notCount_append]
  have hstep : notCount ⟨gs.drop (j0 + 1), 0⟩ ≤ notCount ⟨gs[j0] :: gs.drop (j0 + 1), 0⟩ := by
    simp only [notCount, List.filter_cons]
    split_ifs <;> simp
  omega

lemma fanInTwo_append {gs1 gs2 : List Gate} {o : ℕ}
    (h1 : FanInTwo ⟨gs1, 0⟩) (h2 : FanInTwo ⟨gs2, 0⟩) :
    FanInTwo ⟨gs1 ++ gs2, o⟩ := by
  intro g hg
  rcases List.mem_append.mp hg with hg1 | hg2
  · exact h1 g hg1
  · exact h2 g hg2

lemma fanInTwo_map_inputs {gs : List Gate} {φ : ℕ → ℕ} {o : ℕ}
    (h : FanInTwo ⟨gs, 0⟩) :
    FanInTwo ⟨gs.map (fun g => ⟨g.op, g.inputs.map φ⟩), o⟩ := by
  intro g hg
  rcases List.mem_map.mp hg with ⟨g0, hg0, rfl⟩
  have h0 := h g0 hg0
  exact ⟨h0.1, by simpa using h0.2⟩

lemma readsBack_append {m : ℕ} {gs1 gs2 : List Gate} {o : ℕ}
    (h1 : ReadsBack m ⟨gs1, 0⟩) (h2 : ReadsBack (m + gs1.length) ⟨gs2, 0⟩) :
    ReadsBack m ⟨gs1 ++ gs2, o⟩ := by
  intro j hj i hi
  rw [gateAt_eq_getElem _ j hj] at hi
  by_cases hj1 : j < gs1.length
  · have hget : (gs1 ++ gs2)[j] = gs1[j] := List.getElem_append_left hj1
    rw [hget] at hi
    have h1' := h1 j hj1
    rw [gateAt_eq_getElem _ j hj1] at h1'
    exact h1' i hi
  · have hj1' : gs1.length ≤ j := Nat.le_of_not_lt hj1
    have hj2 : j - gs1.length < gs2.length := by
      simp only [List.length_append] at hj
      omega
    have hget : (gs1 ++ gs2)[j] = gs2[j - gs1.length] := List.getElem_append_right hj1'
    rw [hget] at hi
    have h2' := h2 (j - gs1.length) hj2
    rw [gateAt_eq_getElem _ (j - gs1.length) hj2] at h2'
    have hlt := h2' i hi
    omega

lemma wiresFrom_remap_full (gs : List Gate) (w1 W0 : List Bool) (φ : ℕ → ℕ)
    (hrb : ReadsBack w1.length ⟨gs, 0⟩)
    (hφ_lt : ∀ k < w1.length, φ k < W0.length)
    (hφ_gate : ∀ j < gs.length, φ (w1.length + j) = W0.length + j)
    (hφ_val : ∀ k < w1.length, W0.getD (φ k) false = w1.getD k false) :
    let gs' := gs.map (fun g => ⟨g.op, g.inputs.map φ⟩)
    ReadsBack W0.length ⟨gs', 0⟩ ∧
    ∀ t < w1.length + gs.length,
      (wiresFrom gs' W0).getD (φ t) false = (wiresFrom gs w1).getD t false := by
  intro gs'
  have hrb' : ReadsBack W0.length ⟨gs', 0⟩ := by
    intro j hj i hi
    have hj0 : j < gs.length := by simpa [gs'] using hj
    rw [gateAt_eq_getElem _ j hj] at hi
    simp only [gs', List.getElem_map, List.mem_map] at hi
    rcases hi with ⟨k, hk, rfl⟩
    have hk_lt : k < w1.length + j := by
      have h := hrb j hj0
      rw [gateAt_eq_getElem _ j hj0] at h
      exact h k hk
    by_cases hkw : k < w1.length
    · exact lt_of_lt_of_le (hφ_lt k hkw) (Nat.le_add_right _ _)
    · have hj' : k - w1.length < gs.length := by omega
      have hkeq : k = w1.length + (k - w1.length) := by omega
      rw [hkeq, hφ_gate (k - w1.length) hj']
      omega
  refine ⟨hrb', ?_⟩
  intro t
  induction t using Nat.strong_induction_on with
  | ind t ih =>
    intro ht
    by_cases htw : t < w1.length
    · rw [wiresFrom_getD_lt gs' W0 (φ t) (hφ_lt t htw)]
      rw [wiresFrom_getD_lt gs w1 t htw]
      exact hφ_val t htw
    · let j := t - w1.length
      have hj : j < gs.length := by omega
      have hteq : t = w1.length + j := by omega
      rw [hteq, hφ_gate j hj]
      have hj' : j < gs'.length := by simpa [gs'] using hj
      rw [wiresFrom_getD_gate_readsBack gs' W0 hrb' j hj']
      rw [wiresFrom_getD_gate_readsBack gs w1 hrb j hj]
      simp only [gs', List.getElem_map, List.map_map]
      congr 1
      refine List.map_congr_left (fun k hk => ?_)
      have hk_lt : k < w1.length + j := by
        have h := hrb j hj
        rw [gateAt_eq_getElem _ j hj] at h
        exact h k hk
      exact ih k (by omega) (by omega)

def effInputs (g : Gate) : List ℕ :=
  match g.op with
  | GateOp.not => g.inputs.take 1
  | _ => g.inputs

lemma gate_eval_congr_eff (g : Gate) (f1 f2 : ℕ → Bool)
    (h : ∀ i ∈ effInputs g, f1 i = f2 i) :
    g.op.eval (g.inputs.map f1) = g.op.eval (g.inputs.map f2) := by
  cases hop : g.op with
  | not =>
    cases hin : g.inputs with
    | nil => simp [GateOp.eval]
    | cons a tl =>
      simp only [GateOp.eval, List.map_cons, List.headD_cons]
      have ha : a ∈ effInputs g := by simp [effInputs, hop, hin]
      rw [h a ha]
  | and =>
    simp only [GateOp.eval]
    congr 1
    refine List.map_congr_left (fun i hi => h i ?_)
    simp [effInputs, hop, hi]
  | or =>
    simp only [GateOp.eval]
    congr 1
    refine List.map_congr_left (fun i hi => h i ?_)
    simp [effInputs, hop, hi]
  | mod m =>
    have hmap : g.inputs.map f1 = g.inputs.map f2 :=
      List.map_congr_left (fun i hi => h i (by simp [effInputs, hop, hi]))
    rw [hmap]
  | maj =>
    have hmap : g.inputs.map f1 = g.inputs.map f2 :=
      List.map_congr_left (fun i hi => h i (by simp [effInputs, hop, hi]))
    rw [hmap]

lemma exists_gate_reading_eff_wire {m : ℕ} (C : Circuit) (w1 w2 : List Bool) (u tgt : ℕ)
    (hw1 : w1.length = m) (hw2 : w2.length = m)
    (hrb : ReadsBack m C)
    (htgt_ne : tgt ≠ u) (htgt_lt : tgt < m + C.size)
    (hagree : ∀ k < m, k ≠ u → w1.getD k false = w2.getD k false)
    (hdiff : (C.wires w1).getD tgt false ≠ (C.wires w2).getD tgt false) :
    ∃ (j0 : ℕ) (hj0 : j0 < C.gates.length), u ∈ effInputs (C.gates[j0]'hj0) := by
  by_contra hnone
  push Not at hnone
  have hsame : ∀ t < m + C.size, t ≠ u → (C.wires w1).getD t false = (C.wires w2).getD t false := by
    intro t
    induction t using Nat.strong_induction_on with
    | ind t ih =>
      intro ht htu
      by_cases htm : t < m
      · rw [circuit_wires_eq, wiresFrom_getD_lt C.gates w1 t (by omega)]
        rw [circuit_wires_eq, wiresFrom_getD_lt C.gates w2 t (by omega)]
        exact hagree t htm htu
      · let j := t - m
        have hj : j < C.gates.length := by
          simp only [Circuit.size] at ht; omega
        have hteq : t = m + j := by omega
        rw [hteq, circuit_wires_eq, circuit_wires_eq]
        have hrb1 : ReadsBack w1.length ⟨C.gates, 0⟩ := by rw [hw1]; exact hrb
        have hrb2 : ReadsBack w2.length ⟨C.gates, 0⟩ := by rw [hw2]; exact hrb
        have h1 := wiresFrom_getD_gate_readsBack C.gates w1 hrb1 j hj
        have h2 := wiresFrom_getD_gate_readsBack C.gates w2 hrb2 j hj
        rw [hw1] at h1; rw [hw2] at h2
        rw [h1, h2]
        refine gate_eval_congr_eff (C.gates[j]) _ _ (fun i hi => ?_)
        have hi_in : i ∈ (C.gates[j]).inputs := by
          cases hop : (C.gates[j]).op <;> simp [effInputs, hop] at hi
          · exact hi
          · exact hi
          · exact List.mem_of_mem_take hi
          · exact hi
          · exact hi
        have hi_lt : i < m + j := by
          have h := hrb j hj
          rw [gateAt_eq_getElem _ j hj] at h
          exact h i hi_in
        have hi_ne : i ≠ u := fun heq => hnone j hj (heq ▸ hi)
        exact ih i (by omega) (by omega) hi_ne
  exact hdiff (hsame tgt htgt_lt htgt_ne)

lemma gate_simplify_when_true {n : ℕ} (g : Gate) (u : ℕ) (hu : u < n) (j0 : ℕ)
    (hfit : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hrb : ∀ i ∈ g.inputs, i < n + 2 + j0)
    (heff : u ∈ effInputs g) :
    ∃ rep : ℕ, rep < n + 2 + j0 ∧ rep ≠ u ∧
      ∀ w : List Bool, w.getD n false = false → w.getD (n + 1) false = true →
        w.getD u false = true →
        g.op.eval (g.inputs.map fun i => w.getD i false) = w.getD rep false := by
  rcases hfit with ⟨hop, hlen⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with hop | hop | hop
  · -- AND
    have hu_in : u ∈ g.inputs := by simpa [effInputs, hop] using heff
    cases hin : g.inputs with
    | nil => simp [hin] at hu_in
    | cons a tl =>
      cases tl with
      | nil =>
        have hau : u = a := by simpa [hin] using hu_in
        refine ⟨n + 1, by omega, by omega, fun w _ ht hwu => ?_⟩
        rw [hop, ← hau]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          id_eq, Bool.and_true, hwu, ht]
      | cons b tl2 =>
        cases tl2 with
        | nil =>
          have hab : u = a ∨ u = b := by simpa [hin] using hu_in
          rcases hab with hau | hbu
          · by_cases hb_eq : b = u
            · refine ⟨n + 1, by omega, by omega, fun w _ ht hwu => ?_⟩
              rw [hop, ← hau, hb_eq]
              simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
                id_eq, Bool.and_true, hwu, ht]
            · have hb_lt : b < n + 2 + j0 := hrb b (by simp [hin])
              refine ⟨b, hb_lt, hb_eq, fun w _ _ hwu => ?_⟩
              rw [hop, ← hau]
              simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
                id_eq, Bool.and_true, Bool.true_and, hwu]
          · by_cases ha_eq : a = u
            · refine ⟨n + 1, by omega, by omega, fun w _ ht hwu => ?_⟩
              rw [hop, ha_eq, ← hbu]
              simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
                id_eq, Bool.and_true, hwu, ht]
            · have ha_lt : a < n + 2 + j0 := hrb a (by simp [hin])
              refine ⟨a, ha_lt, ha_eq, fun w _ _ hwu => ?_⟩
              rw [hop, ← hbu]
              simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
                id_eq, Bool.and_true, hwu]
        | cons c tl3 =>
          simp [hin] at hlen
  · -- OR
    have hu_in : u ∈ g.inputs := by simpa [effInputs, hop] using heff
    refine ⟨n + 1, by omega, by omega, fun w _ ht hwu => ?_⟩
    rw [hop, ht]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
    exact ⟨true, ⟨u, hu_in, hwu⟩, rfl⟩
  · -- NOT
    cases hin : g.inputs with
    | nil => simp [effInputs, hop, hin] at heff
    | cons a tl =>
      have hau : u = a := by simpa [effInputs, hop, hin] using heff
      refine ⟨n, by omega, by omega, fun w hf _ hwu => ?_⟩
      rw [hop, ← hau]
      simp only [GateOp.eval, List.map_cons, List.headD_cons, hwu, hf, Bool.not_true]

lemma elim_one_true_input {n : ℕ} (C : Circuit) (u : Fin n) (j0 : ℕ)
    (hj0 : j0 < C.gates.length)
    (hfit : FanInTwo C)
    (hrb : ReadsBack (n + 2) C)
    (hout : C.output < n + 2 + C.size)
    (heff : u.val ∈ effInputs (C.gates[j0])) :
    ∃ (C' : Circuit) (ψ : ℕ → ℕ),
      FanInTwo C' ∧ ReadsBack (n + 2) C' ∧ C'.output < n + 2 + C'.size ∧
      C'.size + 1 = C.size ∧ notCount C' ≤ notCount C ∧
      (∀ w < n + 2 + C.size, ψ w < n + 2 + C'.size) ∧
      ∀ x : Fin n → Bool, x u = true →
        ∀ w < n + 2 + C.size,
          (C'.wires (List.ofFn x ++ [false, true])).getD (ψ w) false =
          (C.wires (List.ofFn x ++ [false, true])).getD w false := by
  have hg_fit := hfit (C.gates[j0]) (List.getElem_mem hj0)
  have hg_rb : ∀ i ∈ (C.gates[j0]).inputs, i < n + 2 + j0 := by
    intro i hi
    have h := hrb j0 hj0
    rw [gateAt_eq_getElem _ j0 hj0] at h
    exact h i hi
  rcases gate_simplify_when_true (C.gates[j0]) u.val u.isLt j0 hg_fit hg_rb heff with
    ⟨rep, hrep_lt, hrep_ne, hrep_eval⟩
  let subU : ℕ → ℕ := fun w => if w = u.val then n + 1 else w
  let ψ : ℕ → ℕ := fun w =>
    if w < n + 2 + j0 then subU w
    else if w = n + 2 + j0 then subU rep
    else w - 1
  let raw : List Gate := C.gates.take j0 ++ C.gates.drop (j0 + 1)
  let gs' : List Gate := raw.map (fun g => ⟨g.op, g.inputs.map ψ⟩)
  let C' : Circuit := ⟨gs', ψ C.output⟩
  have hraw_len : raw.length = C.gates.length - 1 := by
    simp only [raw, List.length_append, List.length_take, List.length_drop,
      Nat.min_eq_left (le_of_lt hj0)]
    omega
  have hC_sz : C.size = C.gates.length := rfl
  have hC'_size : C'.size + 1 = C.size := by
    simp only [C', Circuit.size, gs', List.length_map, hraw_len]
    omega
  have hψ_lt : ∀ w < n + 2 + C.size, ψ w < n + 2 + C'.size := by
    intro w hw
    dsimp only [ψ, subU]
    split_ifs <;> omega
  have hψ_bound : ∀ k w : ℕ, w < n + 2 + k →
      (k < j0 → ψ w < n + 2 + k) ∧ (j0 < k → ψ w < n + 2 + (k - 1)) := by
    intro k w hw
    constructor
    · intro hkj
      dsimp only [ψ, subU]
      rw [if_pos (by omega)]
      split_ifs <;> omega
    · intro hjk
      dsimp only [ψ, subU]
      split_ifs <;> omega
  have hfit' : FanInTwo C' := by
    refine fanInTwo_map_inputs (o := ψ C.output) ?_
    intro g hg
    rcases List.mem_append.mp hg with h1 | h2
    · exact hfit g (List.mem_of_mem_take h1)
    · exact hfit g (List.mem_of_mem_drop h2)
  have hnot' : notCount C' ≤ notCount C := by
    calc
      notCount C' = notCount ⟨raw, 0⟩ := notCount_map_inputs raw _ _
      _ ≤ notCount ⟨C.gates, 0⟩ := notCount_remove_one C.gates j0 hj0 0
      _ = notCount C := rfl
  have hrb' : ReadsBack (n + 2) C' := by
    intro j hj i hi
    have hj_raw : j < raw.length := by simpa [C', gs'] using hj
    rw [gateAt_eq_getElem _ j hj] at hi
    simp only [C', gs', List.getElem_map, List.mem_map] at hi
    rcases hi with ⟨w, hw, rfl⟩
    by_cases hjj0 : j < j0
    · have hget : raw[j] = C.gates[j] := by
        have hlt1 : j < (C.gates.take j0).length := by
          rw [List.length_take, Nat.min_eq_left (le_of_lt hj0)]; exact hjj0
        rw [List.getElem_append_left hlt1, List.getElem_take]
      rw [hget] at hw
      have hw_lt : w < n + 2 + j := by
        have h := hrb j (lt_trans hjj0 hj0)
        rw [gateAt_eq_getElem _ j (lt_trans hjj0 hj0)] at h
        exact h w hw
      exact (hψ_bound j w hw_lt).1 hjj0
    · have hj1 : j + 1 < C.gates.length := by omega
      have hget : raw[j] = C.gates[j + 1] := by
        have hle1 : (C.gates.take j0).length ≤ j := by
          rw [List.length_take, Nat.min_eq_left (le_of_lt hj0)]; omega
        rw [List.getElem_append_right hle1, List.getElem_drop]
        congr 1
        rw [List.length_take, Nat.min_eq_left (le_of_lt hj0)]
        omega
      rw [hget] at hw
      have hw_lt : w < n + 2 + (j + 1) := by
        have h := hrb (j + 1) hj1
        rw [gateAt_eq_getElem _ (j + 1) hj1] at h
        exact h w hw
      have hres := (hψ_bound (j + 1) w hw_lt).2 (by omega)
      omega
  refine ⟨C', ψ, hfit', hrb', hψ_lt C.output hout, hC'_size, hnot', hψ_lt, ?_⟩
  intro x hxu w
  let inp : List Bool := List.ofFn x ++ [false, true]
  have hinp_len : inp.length = n + 2 := by simp [inp]
  have hinp_n : inp.getD n false = false := by
    have h := getD_append_right (List.ofFn x) [false, true] n false (by simp)
    simpa [inp] using h
  have hinp_n1 : inp.getD (n + 1) false = true := by
    have h := getD_append_right (List.ofFn x) [false, true] (n + 1) false (by simp)
    simpa [inp] using h
  have hinp_u : inp.getD u.val false = true := by
    have h := getD_append_left (List.ofFn x) [false, true] u.val false (by simp [u.isLt])
    simp only [inp, h, List.getD_eq_getElem?_getD, List.getElem?_ofFn, u.isLt, ↓reduceDIte,
      Option.getD_some, hxu]
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hwin : w < n + 2
    · have hψw : ψ w = subU w := if_pos (by omega)
      rw [hψw]
      by_cases hwu : w = u.val
      · subst hwu
        have hsub : subU u.val = n + 1 := if_pos rfl
        rw [hsub, circuit_wires_eq, circuit_wires_eq]
        rw [wiresFrom_getD_lt C'.gates inp (n + 1) (by omega)]
        rw [wiresFrom_getD_lt C.gates inp u.val (by omega)]
        rw [hinp_n1, hinp_u]
      · have hsub : subU w = w := if_neg hwu
        rw [hsub, circuit_wires_eq, circuit_wires_eq]
        rw [wiresFrom_getD_lt C'.gates inp w (by omega)]
        rw [wiresFrom_getD_lt C.gates inp w (by omega)]
    · let j := w - (n + 2)
      have hj : j < C.gates.length := by
        simp only [Circuit.size] at hw; omega
      have hweq : w = n + 2 + j := by omega
      by_cases hjj0 : j < j0
      · have hψw : ψ w = n + 2 + j := by
          dsimp only [ψ, subU]
          rw [if_pos (by omega), if_neg (by omega)]
          omega
        rw [hψw, hweq, circuit_wires_eq, circuit_wires_eq]
        have hj' : j < C'.gates.length := by
          simp only [Circuit.size] at hC'_size; omega
        have hrbC' : ReadsBack inp.length ⟨C'.gates, 0⟩ := by rw [hinp_len]; exact hrb'
        have hrbC : ReadsBack inp.length ⟨C.gates, 0⟩ := by rw [hinp_len]; exact hrb
        have h1 := wiresFrom_getD_gate_readsBack C'.gates inp hrbC' j hj'
        have h2 := wiresFrom_getD_gate_readsBack C.gates inp hrbC j hj
        rw [hinp_len] at h1 h2
        rw [h1, h2]
        have hget : C'.gates[j] = ⟨(C.gates[j]).op, (C.gates[j]).inputs.map ψ⟩ := by
          have hlt1 : j < (C.gates.take j0).length := by
            rw [List.length_take, Nat.min_eq_left (le_of_lt hj0)]; exact hjj0
          simp only [C', gs', raw, List.getElem_map, List.getElem_append_left hlt1,
            List.getElem_take]
        rw [hget]
        simp only [List.map_map]
        congr 1
        refine List.map_congr_left (fun k hk => ?_)
        have hk_lt : k < n + 2 + j := by
          have h := hrb j hj
          rw [gateAt_eq_getElem _ j hj] at h
          exact h k hk
        exact ih k (by omega) (by omega)
      · by_cases hjeq : j = j0
        · have hweq0 : w = n + 2 + j0 := by omega
          have hψw : ψ w = ψ rep := by
            dsimp only [ψ]
            rw [if_neg (by omega), if_pos (by omega), if_pos hrep_lt]
          rw [hψw, ih rep (by omega) (by omega), hweq0, circuit_wires_eq]
          have hrbC : ReadsBack inp.length ⟨C.gates, 0⟩ := by rw [hinp_len]; exact hrb
          have h2 := wiresFrom_getD_gate_readsBack C.gates inp hrbC j0 hj0
          rw [hinp_len] at h2
          rw [h2]
          have hwn : (wiresFrom C.gates inp).getD n false = false := by
            rw [wiresFrom_getD_lt _ _ n (by omega), hinp_n]
          have hwn1 : (wiresFrom C.gates inp).getD (n + 1) false = true := by
            rw [wiresFrom_getD_lt _ _ (n + 1) (by omega), hinp_n1]
          have hwu : (wiresFrom C.gates inp).getD u.val false = true := by
            rw [wiresFrom_getD_lt _ _ u.val (by omega), hinp_u]
          exact (hrep_eval (wiresFrom C.gates inp) hwn hwn1 hwu).symm
        · have hjgt : j0 < j := by omega
          have hψw : ψ w = n + 2 + (j - 1) := by
            dsimp only [ψ]
            rw [if_neg (by omega), if_neg (by omega)]
            omega
          rw [hψw, hweq, circuit_wires_eq, circuit_wires_eq]
          have hj' : j - 1 < C'.gates.length := by
            simp only [Circuit.size] at hC'_size; omega
          have hrbC' : ReadsBack inp.length ⟨C'.gates, 0⟩ := by rw [hinp_len]; exact hrb'
          have hrbC : ReadsBack inp.length ⟨C.gates, 0⟩ := by rw [hinp_len]; exact hrb
          have h1 := wiresFrom_getD_gate_readsBack C'.gates inp hrbC' (j - 1) hj'
          have h2 := wiresFrom_getD_gate_readsBack C.gates inp hrbC j hj
          rw [hinp_len] at h1 h2
          rw [h1, h2]
          have hget : C'.gates[j - 1] = ⟨(C.gates[j]).op, (C.gates[j]).inputs.map ψ⟩ := by
            have hle1 : (C.gates.take j0).length ≤ j - 1 := by
              rw [List.length_take, Nat.min_eq_left (le_of_lt hj0)]; omega
            have hidx_eq : j0 + 1 + (j - 1 - (C.gates.take j0).length) = j := by
              rw [List.length_take, Nat.min_eq_left (le_of_lt hj0)]; omega
            simp only [C', gs', raw, List.getElem_map, List.getElem_append_right hle1,
              List.getElem_drop, hidx_eq]
          rw [hget]
          simp only [List.map_map]
          congr 1
          refine List.map_congr_left (fun k hk => ?_)
          have hk_lt : k < n + 2 + j := by
            have h := hrb j hj
            rw [gateAt_eq_getElem _ j hj] at h
            exact h k hk
          exact ih k (by omega) (by omega)

lemma getD_ofFn_append_const {m : ℕ} (x : Fin m → Bool) :
    (List.ofFn x ++ [false, true]).length = m + 2 ∧
    (∀ i : Fin m, (List.ofFn x ++ [false, true]).getD i.val false = x i) ∧
    (List.ofFn x ++ [false, true]).getD m false = false ∧
    (List.ofFn x ++ [false, true]).getD (m + 1) false = true := by
  refine ⟨by simp, ?_, ?_, ?_⟩
  · intro i
    rw [getD_append_left (List.ofFn x) [false, true] i.val false (by simp [i.isLt])]
    simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt]
  · rw [getD_append_right (List.ofFn x) [false, true] m false (by simp)]
    simp
  · rw [getD_append_right (List.ofFn x) [false, true] (m + 1) false (by simp)]
    simp

theorem main (n m : Nat) (G : Finset (Fin n × Fin n)) (v : (Fin m × Bool) ↪ Fin n)
    (hG : ∀ e ∈ G, e.1 < e.2)
    (hpair : ∀ i, (v (i, false), v (i, true)) ∈ G ∨ (v (i, true), v (i, false)) ∈ G)
    (c : Fin m → Bool) :
    let adj := fun (a b : Fin n) => (a, b) ∈ G ∨ (b, a) ∈ G
    let joined := fun (i j : Fin m) => i ≠ j ∧ ∀ b d : Bool, adj (v (i, b)) (v (j, d))
    let cover := fun (x : Fin n → Bool) => ∀ e ∈ G, x e.1 = true ∨ x e.2 = true
    let quotient := fun (y : Fin m → Bool) => ∀ i j, joined i j → y i = true ∨ y j = true
    let project := fun (x : Fin n → Bool) (i : Fin m) => x (v (i, false)) && x (v (i, true))
    let fits := fun (k : Nat) (P : (Fin k → Bool) → Prop) (out : (Fin k → Bool) → Fin m → Bool)
        (s r : Nat) =>
      ∃ (C : Circuit) (tap : Fin m → Fin (k + 2 + C.size)),
        FanInTwo C ∧ ReadsBack (k + 2) C ∧ C.output < k + 2 + C.size ∧
        C.size ≤ s ∧ notCount C ≤ r ∧
        ∀ x, P x → ∀ i, (C.wires (List.ofFn x ++ [false, true])).getD (tap i).val false = out x i
    let embedBits := fun (y : Fin m → Bool) (u : Fin n) =>
      decide (∀ i, v (i, c i) = u → y i = true)
    let legal := ∀ i j, i ≠ j → adj (v (i, c i)) (v (j, c j)) → joined i j
    (legal ↔ ∀ x, cover x → cover (embedBits (project x))) ∧
    (legal → (∀ y, quotient y ↔ cover (embedBits y)) ∧
      ∀ s r, fits n cover (fun x i => xor (x (v (i, false))) (x (v (i, true)))) s r ↔
        ∃ t, t + m ≤ s ∧ fits m quotient (fun y i => !(y i)) t r) := by
  dsimp only
  let adj : Fin n → Fin n → Prop := fun a b => (a, b) ∈ G ∨ (b, a) ∈ G
  let joined : Fin m → Fin m → Prop := fun i j => i ≠ j ∧ ∀ b d : Bool, adj (v (i, b)) (v (j, d))
  let cover : (Fin n → Bool) → Prop := fun x => ∀ e ∈ G, x e.1 = true ∨ x e.2 = true
  let quotient : (Fin m → Bool) → Prop := fun y => ∀ i j, joined i j → y i = true ∨ y j = true
  let project : (Fin n → Bool) → Fin m → Bool := fun x i => x (v (i, false)) && x (v (i, true))
  let embedBits : (Fin m → Bool) → Fin n → Bool := fun y u =>
    decide (∀ i, v (i, c i) = u → y i = true)
  let legal : Prop := ∀ i j, i ≠ j → adj (v (i, c i)) (v (j, c j)) → joined i j
  have hembed_chosen : ∀ (y : Fin m → Bool) (i : Fin m), embedBits y (v (i, c i)) = y i := by
    intro y i
    apply Bool.eq_iff_iff.mpr
    simp only [embedBits, decide_eq_true_eq]
    constructor
    · intro h; exact h i rfl
    · intro hy j hj
      have hij : j = i := congrArg Prod.fst (v.injective hj)
      subst hij
      exact hy
  have hembed_other : ∀ (y : Fin m → Bool) (u : Fin n),
      (∀ i : Fin m, v (i, c i) ≠ u) → embedBits y u = true := by
    intro y u hu
    simp only [embedBits, decide_eq_true_eq]
    intro i hi
    exact absurd hi (hu i)
  have hembed_unchosen : ∀ (y : Fin m → Bool) (i : Fin m),
      embedBits y (v (i, !(c i))) = true := by
    intro y i
    refine hembed_other y _ (fun j hj => ?_)
    have hp := v.injective hj
    have hij : j = i := congrArg Prod.fst hp
    subst hij
    have hb : c j = !(c j) := congrArg Prod.snd hp
    cases hc : c j <;> simp [hc] at hb
  have hembed_false : ∀ (y : Fin m → Bool) (u : Fin n),
      embedBits y u = false → ∃ i : Fin m, v (i, c i) = u ∧ y i = false := by
    intro y u hu
    simp only [embedBits, decide_eq_false_iff_not, not_forall] at hu
    rcases hu with ⟨i, hi⟩
    push Not at hi
    exact ⟨i, hi.1, Bool.eq_false_iff.mpr hi.2⟩
  have hquot_iff : legal → ∀ y : Fin m → Bool, quotient y ↔ cover (embedBits y) := by
    intro hleg y
    constructor
    · intro hq e he
      by_contra hboth
      push Not at hboth
      have h1 : embedBits y e.1 = false := Bool.eq_false_iff.mpr hboth.1
      have h2 : embedBits y e.2 = false := Bool.eq_false_iff.mpr hboth.2
      rcases hembed_false y e.1 h1 with ⟨i, hi, hyi⟩
      rcases hembed_false y e.2 h2 with ⟨j, hj, hyj⟩
      have hij : i ≠ j := by
        rintro rfl
        have hlt := hG e he
        rw [← hi, ← hj] at hlt
        exact lt_irrefl _ hlt
      have hadj : adj (v (i, c i)) (v (j, c j)) := Or.inl (by rw [hi, hj]; exact he)
      have hjn := hleg i j hij hadj
      rcases hq i j hjn with h | h <;> simp [hyi, hyj] at h
    · intro hcov i j hjn
      have hadj : adj (v (i, c i)) (v (j, c j)) := hjn.2 (c i) (c j)
      rcases hadj with h1 | h2
      · rcases hcov _ h1 with h | h
        · left; rwa [hembed_chosen] at h
        · right; rwa [hembed_chosen] at h
      · rcases hcov _ h2 with h | h
        · right; rwa [hembed_chosen] at h
        · left; rwa [hembed_chosen] at h
  have hleg_iff : legal ↔ ∀ x, cover x → cover (embedBits (project x)) := by
    constructor
    · intro hleg x hcov
      rw [← hquot_iff hleg (project x)]
      intro i j hjn
      by_contra hboth
      push Not at hboth
      have hpi : project x i = false := Bool.eq_false_iff.mpr hboth.1
      have hpj : project x j = false := Bool.eq_false_iff.mpr hboth.2
      have hbi : ∃ b : Bool, x (v (i, b)) = false := by
        cases hf : x (v (i, false))
        · exact ⟨false, hf⟩
        · cases ht : x (v (i, true))
          · exact ⟨true, ht⟩
          · simp [project, hf, ht] at hpi
      have hbj : ∃ d : Bool, x (v (j, d)) = false := by
        cases hf : x (v (j, false))
        · exact ⟨false, hf⟩
        · cases ht : x (v (j, true))
          · exact ⟨true, ht⟩
          · simp [project, hf, ht] at hpj
      rcases hbi with ⟨b, hb⟩
      rcases hbj with ⟨d, hd⟩
      rcases hjn.2 b d with h1 | h2
      · rcases hcov _ h1 with h | h <;> simp [hb, hd] at h
      · rcases hcov _ h2 with h | h <;> simp [hb, hd] at h
    · intro hproj i j hij hadj
      refine ⟨hij, fun b d => ?_⟩
      by_contra hnadj
      let x : Fin n → Bool := fun u => decide (u ≠ v (i, b) ∧ u ≠ v (j, d))
      have hcov_x : cover x := by
        intro e he
        by_contra hboth
        push Not at hboth
        have h1 : x e.1 = false := Bool.eq_false_iff.mpr hboth.1
        have h2 : x e.2 = false := Bool.eq_false_iff.mpr hboth.2
        have he1 : e.1 = v (i, b) ∨ e.1 = v (j, d) := by
          simp only [x, decide_eq_false_iff_not, not_and_or, not_not] at h1; exact h1
        have he2 : e.2 = v (i, b) ∨ e.2 = v (j, d) := by
          simp only [x, decide_eq_false_iff_not, not_and_or, not_not] at h2; exact h2
        have hne_e : e.1 ≠ e.2 := ne_of_lt (hG e he)
        rcases he1 with h1' | h1' <;> rcases he2 with h2' | h2'
        · exact hne_e (h1'.trans h2'.symm)
        · exact hnadj (Or.inl (by rw [← h1', ← h2']; exact he))
        · exact hnadj (Or.inr (by rw [← h2', ← h1']; exact he))
        · exact hne_e (h1'.trans h2'.symm)
      have hcov_emb : cover (embedBits (project x)) := hproj x hcov_x
      have hxi : x (v (i, b)) = false := by simp [x]
      have hxj : x (v (j, d)) = false := by simp [x]
      have hpi : project x i = false := by cases b <;> simp [project, hxi]
      have hpj : project x j = false := by cases d <;> simp [project, hxj]
      rcases hadj with h1 | h2
      · rcases hcov_emb _ h1 with h | h
        · rw [hembed_chosen, hpi] at h; cases h
        · rw [hembed_chosen, hpj] at h; cases h
      · rcases hcov_emb _ h2 with h | h
        · rw [hembed_chosen, hpj] at h; cases h
        · rw [hembed_chosen, hpi] at h; cases h
  refine ⟨hleg_iff, fun hleg => ⟨hquot_iff hleg, fun s r => ?_⟩⟩
  constructor
  · -- Forward: cover-parity circuit -> quotient inverter eliminating m unchosen ends
    rintro ⟨C0, tap0, hfit0, hrb0, hout0, hsize0, hnot0, hsem0⟩
    have hstep : ∀ k ≤ m,
        ∃ (Ck : Circuit) (tapk : Fin m → Fin (n + 2 + Ck.size)),
          FanInTwo Ck ∧ ReadsBack (n + 2) Ck ∧ Ck.output < n + 2 + Ck.size ∧
          Ck.size + k ≤ C0.size ∧ notCount Ck ≤ notCount C0 ∧
          ∀ x : Fin n → Bool, cover x →
            (∀ h : Fin m, h.val < k → x (v (h, !(c h))) = true) →
            ∀ i : Fin m, (Ck.wires (List.ofFn x ++ [false, true])).getD (tapk i).val false =
              xor (x (v (i, false))) (x (v (i, true))) := by
      intro k
      induction k with
      | zero =>
        intro _
        exact ⟨C0, tap0, hfit0, hrb0, hout0, by omega, le_rfl, fun x hcov _ => hsem0 x hcov⟩
      | succ k ih =>
        intro hk1
        rcases ih (by omega) with ⟨Ck, tapk, hfitk, hrbk, houtk, hszk, hnotk, hsemk⟩
        have hkm : k < m := by omega
        let idx : Fin m := ⟨k, hkm⟩
        let u : Fin n := v (idx, !(c idx))
        let xtop : Fin n → Bool := fun _ => true
        let xdrop : Fin n → Bool := fun w => decide (w ≠ u)
        have hcov_top : cover xtop := fun e _ => Or.inl rfl
        have hcov_drop : cover xdrop := by
          intro e he
          have hne := ne_of_lt (hG e he)
          by_cases h1 : e.1 = u
          · right; simp [xdrop, h1 ▸ hne.symm]
          · left; simp [xdrop, h1]
        have htop_prev : ∀ h : Fin m, h.val < k → xtop (v (h, !(c h))) = true := fun _ _ => rfl
        have hdrop_prev : ∀ h : Fin m, h.val < k → xdrop (v (h, !(c h))) = true := by
          intro h hh
          have hne : v (h, !(c h)) ≠ u := fun heq => by
            have := congrArg Prod.fst (v.injective heq)
            have : h.val = k := congrArg Fin.val this
            omega
          simp [xdrop, hne]
        have hval_top : (Ck.wires (List.ofFn xtop ++ [false, true])).getD (tapk idx).val false = false := by
          rw [hsemk xtop hcov_top htop_prev idx]
          rfl
        have hval_drop : (Ck.wires (List.ofFn xdrop ++ [false, true])).getD (tapk idx).val false = true := by
          rw [hsemk xdrop hcov_drop hdrop_prev idx]
          have hne_c : v (idx, c idx) ≠ u := fun heq => by
            have hb : c idx = !(c idx) := congrArg Prod.snd (v.injective heq)
            cases hc : c idx <;> simp [hc] at hb
          have hxc : xdrop (v (idx, c idx)) = true := by simp [xdrop, hne_c]
          have hxu : xdrop (v (idx, !(c idx))) = false := by simp [xdrop, u]
          cases hc : c idx
          · rw [hc] at hxc hxu; simp at hxu; simp [hxc, hxu]
          · rw [hc] at hxc hxu; simp at hxu; simp [hxc, hxu]
        have htgt_ne : (tapk idx).val ≠ u.val := by
          intro heq
          have h1 : (Ck.wires (List.ofFn xtop ++ [false, true])).getD (tapk idx).val false = true := by
            rw [heq, circuit_wires_eq, wiresFrom_getD_lt _ _ u.val (by simp; omega)]
            exact (getD_ofFn_append_const xtop).2.1 u
          rw [hval_top] at h1
          cases h1
        have hagree : ∀ w < n + 2, w ≠ u.val →
            (List.ofFn xtop ++ [false, true]).getD w false =
            (List.ofFn xdrop ++ [false, true]).getD w false := by
          intro w hw hne
          by_cases hlt : w < n
          · rw [(getD_ofFn_append_const xtop).2.1 ⟨w, hlt⟩,
              (getD_ofFn_append_const xdrop).2.1 ⟨w, hlt⟩]
            have hne' : (⟨w, hlt⟩ : Fin n) ≠ u := fun h => hne (congrArg Fin.val h)
            simp [xtop, xdrop, hne']
          · by_cases h0 : w = n
            · rw [h0, (getD_ofFn_append_const xtop).2.2.1, (getD_ofFn_append_const xdrop).2.2.1]
            · have h1 : w = n + 1 := by omega
              rw [h1, (getD_ofFn_append_const xtop).2.2.2, (getD_ofFn_append_const xdrop).2.2.2]
        have hdiff :
            (Ck.wires (List.ofFn xtop ++ [false, true])).getD (tapk idx).val false ≠
            (Ck.wires (List.ofFn xdrop ++ [false, true])).getD (tapk idx).val false := by
          intro h; rw [hval_top, hval_drop] at h; cases h
        rcases exists_gate_reading_eff_wire Ck _ _ u.val (tapk idx).val (by simp) (by simp) hrbk
            htgt_ne (tapk idx).isLt hagree hdiff with ⟨j0, hj0, heff⟩
        rcases elim_one_true_input Ck u j0 hj0 hfitk hrbk houtk heff with
          ⟨Ck1, ψ, hfit1, hrb1, hout1, hsz1, hnot1, hψ_lt, hψ_sem⟩
        let tapk1 : Fin m → Fin (n + 2 + Ck1.size) := fun i => ⟨ψ (tapk i).val, hψ_lt _ (tapk i).isLt⟩
        refine ⟨Ck1, tapk1, hfit1, hrb1, hout1, by omega, le_trans hnot1 hnotk, ?_⟩
        intro x hcov hx i
        have hx_prev : ∀ h : Fin m, h.val < k → x (v (h, !(c h))) = true := fun h hh => hx h (by omega)
        have hxu_t : x u = true := hx idx (by show k < k + 1; omega)
        dsimp only [tapk1]
        rw [hψ_sem x hxu_t (tapk i).val (tapk i).isLt]
        exact hsemk x hcov hx_prev i
    rcases hstep m le_rfl with ⟨Cm, tapm, hfitm, hrbm, _, hszm, hnotm, hsemm⟩
    classical
    let φ : ℕ → ℕ := fun w =>
      if hw : w < n then
        if h : ∃ i : Fin m, v (i, c i) = ⟨w, hw⟩ then (Classical.choose h).val else m + 1
      else if w = n then m
      else if w = n + 1 then m + 1
      else m + 2 + (w - (n + 2))
    let Cinv : Circuit := ⟨Cm.gates.map (fun g => ⟨g.op, g.inputs.map φ⟩), 0⟩
    have hCinv_size : Cinv.size = Cm.size := by simp [Cinv, Circuit.size]
    have hφ_in_lt : ∀ w < n + 2, φ w < m + 2 := by
      intro w hw
      dsimp only [φ]
      split_ifs with h1 h2 h3 h4
      · have := (Classical.choose h2).isLt; omega
      · omega
      · omega
      · omega
      · omega
    have hφ_gate : ∀ j < Cm.gates.length, φ (n + 2 + j) = m + 2 + j := by
      intro j _
      dsimp only [φ]
      rw [dif_neg (by omega), if_neg (by omega), if_neg (by omega)]
      omega
    have hφ_all_lt : ∀ t < n + 2 + Cm.size, φ t < m + 2 + Cinv.size := by
      intro t ht
      rw [hCinv_size]
      by_cases hlt : t < n + 2
      · exact lt_of_lt_of_le (hφ_in_lt t hlt) (Nat.le_add_right _ _)
      · have hj : t - (n + 2) < Cm.gates.length := by simp only [Circuit.size] at ht; omega
        have heq : t = n + 2 + (t - (n + 2)) := by omega
        rw [heq, hφ_gate _ hj]
        simp only [Circuit.size]; omega
    have hfit_inv : FanInTwo Cinv := fanInTwo_map_inputs (o := 0) hfitm
    have hnot_inv : notCount Cinv ≤ r := by
      have h1 : notCount Cinv = notCount Cm := notCount_map_inputs Cm.gates _ _
      omega
    have hrb_inv : ReadsBack (m + 2) Cinv := by
      intro j hj i hi
      have hj0 : j < Cm.gates.length := by simpa [Cinv] using hj
      rw [gateAt_eq_getElem _ j hj] at hi
      simp only [Cinv, List.getElem_map, List.mem_map] at hi
      rcases hi with ⟨w, hw, rfl⟩
      have hw_lt : w < n + 2 + j := by
        have h := hrbm j hj0
        rw [gateAt_eq_getElem _ j hj0] at h
        exact h w hw
      by_cases hwn : w < n + 2
      · exact lt_of_lt_of_le (hφ_in_lt w hwn) (Nat.le_add_right _ _)
      · have hj' : w - (n + 2) < Cm.gates.length := by omega
        have hweq : w = n + 2 + (w - (n + 2)) := by omega
        rw [hweq, hφ_gate (w - (n + 2)) hj']
        omega
    let tapInv : Fin m → Fin (m + 2 + Cinv.size) := fun i => ⟨φ (tapm i).val, hφ_all_lt _ (tapm i).isLt⟩
    refine ⟨Cinv.size, by omega, Cinv, tapInv, hfit_inv, hrb_inv, by simp [Cinv],
      le_rfl, hnot_inv, ?_⟩
    intro y hy i
    let X : Fin n → Bool := embedBits y
    have hX_cov : cover X := (hquot_iff hleg y).mp hy
    have hX_unch : ∀ h : Fin m, h.val < m → X (v (h, !(c h))) = true := fun h _ =>
      hembed_unchosen y h
    let inp1 : List Bool := List.ofFn X ++ [false, true]
    let inp2 : List Bool := List.ofFn y ++ [false, true]
    have hinp1 := getD_ofFn_append_const X
    have hinp2 := getD_ofFn_append_const y
    have hinp1_len : inp1.length = n + 2 := hinp1.1
    have hinp2_len : inp2.length = m + 2 := hinp2.1
    have hφ_lt_inp : ∀ k < inp1.length, φ k < inp2.length := by
      intro k hk; rw [hinp2_len]; exact hφ_in_lt k (by omega)
    have hφ_gate_inp : ∀ j < Cm.gates.length, φ (inp1.length + j) = inp2.length + j := by
      intro j hj; rw [hinp1_len, hinp2_len]; exact hφ_gate j hj
    have hφ_val_inp : ∀ k < inp1.length, inp2.getD (φ k) false = inp1.getD k false := by
      intro k hk
      rw [hinp1_len] at hk
      by_cases hkn : k < n
      · rw [hinp1.2.1 ⟨k, hkn⟩]
        dsimp only [φ]
        rw [dif_pos hkn]
        by_cases hex : ∃ j : Fin m, v (j, c j) = ⟨k, hkn⟩
        · rw [dif_pos hex, hinp2.2.1 (Classical.choose hex)]
          have hspec := Classical.choose_spec hex
          have hch := hembed_chosen y (Classical.choose hex)
          rw [hspec] at hch
          exact hch.symm
        · rw [dif_neg hex, hinp2.2.2.2]
          dsimp only [X]
          rw [hembed_other y ⟨k, hkn⟩ (fun j hj => hex ⟨j, hj⟩)]
      · by_cases hk0 : k = n
        · rw [hk0]
          have hφk : φ n = m := by dsimp only [φ]; rw [dif_neg (by omega), if_pos rfl]
          rw [hφk, hinp2.2.2.1, hinp1.2.2.1]
        · have hk1 : k = n + 1 := by omega
          rw [hk1]
          have hφk : φ (n + 1) = m + 1 := by
            dsimp only [φ]; rw [dif_neg (by omega), if_neg (by omega), if_pos rfl]
          rw [hφk, hinp2.2.2.2, hinp1.2.2.2]
    have hrb_inp1 : ReadsBack inp1.length ⟨Cm.gates, 0⟩ := by rw [hinp1_len]; exact hrbm
    have hsim := (wiresFrom_remap_full Cm.gates inp1 inp2 φ
      hrb_inp1 hφ_lt_inp hφ_gate_inp hφ_val_inp).2
    have hlt_tap : (tapm i).val < inp1.length + Cm.gates.length := by
      rw [hinp1_len]; exact (tapm i).isLt
    change (wiresFrom Cinv.gates inp2).getD (φ (tapm i).val) false = !(y i)
    rw [hsim (tapm i).val hlt_tap, ← circuit_wires_eq, hsemm X hX_cov hX_unch i]
    have hch := hembed_chosen y i
    have hunch := hembed_unchosen y i
    dsimp only [X]
    cases hc : c i
    · rw [hc] at hch hunch; simp at hunch; rw [hch, hunch]; cases y i <;> rfl
    · rw [hc] at hch hunch; simp at hunch; rw [hch, hunch]; cases y i <;> rfl
  · -- Backward: quotient inverter + m AND gates -> cover-parity circuit
    rintro ⟨t, htm, C2, tap2, hfit2, hrb2, _, hsize2, hnot2, hsem2⟩
    let gs1 : List Gate := (List.finRange m).map (fun i =>
      ⟨GateOp.and, [(v (i, false)).val, (v (i, true)).val]⟩)
    have hgs1_len : gs1.length = m := by simp [gs1]
    let φ : ℕ → ℕ := fun k =>
      if k < m then n + 2 + k
      else if k = m then n
      else if k = m + 1 then n + 1
      else n + 2 + m + (k - (m + 2))
    let gs2 : List Gate := C2.gates.map (fun g => ⟨g.op, g.inputs.map φ⟩)
    let C : Circuit := ⟨gs1 ++ gs2, 0⟩
    have hC_size : C.size = m + C2.size := by
      simp [C, Circuit.size, gs2, hgs1_len]
    have hφ_in_lt : ∀ k < m + 2, φ k < n + 2 + m := by
      intro k hk; dsimp only [φ]; split_ifs <;> omega
    have hφ_gate : ∀ j < C2.gates.length, φ (m + 2 + j) = n + 2 + m + j := by
      intro j _; dsimp only [φ]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]; omega
    have hφ_all_lt : ∀ k < m + 2 + C2.size, φ k < n + 2 + C.size := by
      intro k hk
      rw [hC_size]
      by_cases hkm : k < m + 2
      · exact lt_of_lt_of_le (hφ_in_lt k hkm) (by omega)
      · have hj : k - (m + 2) < C2.gates.length := by simp only [Circuit.size] at hk; omega
        have hkeq : k = m + 2 + (k - (m + 2)) := by omega
        rw [hkeq, hφ_gate _ hj]
        simp only [Circuit.size]; omega
    have hfit1 : FanInTwo ⟨gs1, 0⟩ := by
      intro g hg
      rcases List.mem_map.mp hg with ⟨i, _, rfl⟩
      exact ⟨by simp, by simp⟩
    have hfitC : FanInTwo C := fanInTwo_append hfit1 (fanInTwo_map_inputs (o := 0) hfit2)
    have hnot1 : notCount ⟨gs1, 0⟩ = 0 := by
      refine notCount_and_gates gs1 ?_ 0
      intro g hg
      rcases List.mem_map.mp hg with ⟨_, _, rfl⟩
      rfl
    have hnotC : notCount C ≤ r := by
      have h1 : notCount C = 0 + notCount C2 := by
        simp only [C]
        rw [notCount_append, hnot1, notCount_map_inputs]
        rfl
      omega
    have hrb1 : ReadsBack (n + 2) ⟨gs1, 0⟩ := by
      intro j hj i hi
      have hjm : j < m := by rw [← hgs1_len]; exact hj
      rw [gateAt_eq_getElem _ j hj] at hi
      simp only [gs1, List.getElem_map, List.getElem_finRange, List.mem_cons, List.not_mem_nil,
        or_false] at hi
      rcases hi with rfl | rfl
      · have := (v (⟨j, hjm⟩, false)).isLt; omega
      · have := (v (⟨j, hjm⟩, true)).isLt; omega
    have hrb2' : ReadsBack (n + 2 + gs1.length) ⟨gs2, 0⟩ := by
      intro j hj i hi
      have hj0 : j < C2.gates.length := by simpa [gs2] using hj
      rw [gateAt_eq_getElem _ j hj] at hi
      simp only [gs2, List.getElem_map, List.mem_map] at hi
      rcases hi with ⟨k, hk, rfl⟩
      have hk_lt : k < m + 2 + j := by
        have h := hrb2 j hj0
        rw [gateAt_eq_getElem _ j hj0] at h
        exact h k hk
      rw [hgs1_len]
      by_cases hkm : k < m + 2
      · exact lt_of_lt_of_le (hφ_in_lt k hkm) (Nat.le_add_right _ _)
      · have hj' : k - (m + 2) < C2.gates.length := by omega
        have hkeq : k = m + 2 + (k - (m + 2)) := by omega
        rw [hkeq, hφ_gate _ hj']
        omega
    have hrbC : ReadsBack (n + 2) C := readsBack_append hrb1 hrb2'
    let tapC : Fin m → Fin (n + 2 + C.size) := fun i => ⟨φ (tap2 i).val, hφ_all_lt _ (tap2 i).isLt⟩
    refine ⟨C, tapC, hfitC, hrbC, by simp [C], by omega, hnotC, ?_⟩
    intro x hcov i
    let inp : List Bool := List.ofFn x ++ [false, true]
    let y : Fin m → Bool := project x
    let inp2 : List Bool := List.ofFn y ++ [false, true]
    have hinp := getD_ofFn_append_const x
    have hinp2 := getD_ofFn_append_const y
    have hinp_len : inp.length = n + 2 := hinp.1
    have hinp2_len : inp2.length = m + 2 := hinp2.1
    let W1 : List Bool := wiresFrom gs1 inp
    have hW1_len : W1.length = n + 2 + m := by
      rw [wiresFrom_length, hinp_len, hgs1_len]
    have hW1_gate : ∀ j : Fin m, W1.getD (n + 2 + j.val) false = y j := by
      intro j
      have hj_lt : j.val < gs1.length := by rw [hgs1_len]; exact j.isLt
      have h := wiresFrom_getD_gate gs1 inp j.val hj_lt
      rw [hinp_len] at h
      change W1.getD (n + 2 + j.val) false = y j
      rw [h]
      have hget : gs1[j.val]'hj_lt = ⟨GateOp.and, [(v (j, false)).val, (v (j, true)).val]⟩ := by
        simp [gs1, List.getElem_map, List.getElem_finRange]
      rw [hget]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
        Bool.and_true]
      rw [wiresFrom_getD_lt _ _ _ (by have := (v (j, false)).isLt; omega)]
      rw [wiresFrom_getD_lt _ _ _ (by have := (v (j, true)).isLt; omega)]
      rw [hinp.2.1 (v (j, false)), hinp.2.1 (v (j, true))]
    have hφ_lt_W1 : ∀ k < inp2.length, φ k < W1.length := by
      intro k hk; rw [hW1_len]; exact hφ_in_lt k (by omega)
    have hφ_gate_W1 : ∀ j < C2.gates.length, φ (inp2.length + j) = W1.length + j := by
      intro j hj; rw [hinp2_len, hW1_len]; exact hφ_gate j hj
    have hφ_val_W1 : ∀ k < inp2.length, W1.getD (φ k) false = inp2.getD k false := by
      intro k hk
      rw [hinp2_len] at hk
      by_cases hkm : k < m
      · have hφk : φ k = n + 2 + k := if_pos hkm
        rw [hφk, hW1_gate ⟨k, hkm⟩, hinp2.2.1 ⟨k, hkm⟩]
      · by_cases hk0 : k = m
        · rw [hk0]
          have hφk : φ m = n := by dsimp only [φ]; rw [if_neg (by omega), if_pos rfl]
          rw [hφk, wiresFrom_getD_lt gs1 inp n (by omega), hinp.2.2.1, hinp2.2.2.1]
        · have hk1 : k = m + 1 := by omega
          rw [hk1]
          have hφk : φ (m + 1) = n + 1 := by
            dsimp only [φ]; rw [if_neg (by omega), if_neg (by omega), if_pos rfl]
          rw [hφk, wiresFrom_getD_lt gs1 inp (n + 1) (by omega), hinp.2.2.2, hinp2.2.2.2]
    have hrb2_inp2 : ReadsBack inp2.length ⟨C2.gates, 0⟩ := by rw [hinp2_len]; exact hrb2
    have hsim := (wiresFrom_remap_full C2.gates inp2 W1 φ
      hrb2_inp2 hφ_lt_W1 hφ_gate_W1 hφ_val_W1).2
    have hqy : quotient y := (hquot_iff hleg y).mpr (hleg_iff.mp hleg x hcov)
    have hlt_tap : (tap2 i).val < inp2.length + C2.gates.length := by
      rw [hinp2_len]; exact (tap2 i).isLt
    change (wiresFrom (gs1 ++ gs2) inp).getD (φ (tap2 i).val) false = _
    rw [wiresFrom_append]
    change (wiresFrom gs2 W1).getD (φ (tap2 i).val) false = _
    rw [hsim (tap2 i).val hlt_tap, ← circuit_wires_eq, hsem2 y hqy i]
    have hedge : x (v (i, false)) = true ∨ x (v (i, true)) = true := by
      rcases hpair i with h1 | h2
      · exact hcov _ h1
      · rcases hcov _ h2 with h | h
        · exact Or.inr h
        · exact Or.inl h
    dsimp only [y, project]
    cases h1 : x (v (i, false)) <;> cases h2 : x (v (i, true)) <;> simp [h1, h2] at hedge ⊢

end PEqualNP.Outside.L_lib_1191_aux

theorem PEqualNP.Outside.L_lib_1191 :
∀ (n m : Nat) (G : Finset (Fin n × Fin n)) (v : (Fin m × Bool) ↪ Fin n),
  (∀ e ∈ G, e.1 < e.2) →
  let adj := fun (a b : Fin n) => (a,b) ∈ G ∨ (b,a) ∈ G
  (∀ i, adj (v (i,false)) (v (i,true))) →
  let joined := fun (i j : Fin m) => i ≠ j ∧ ∀ b c : Bool, adj (v (i,b)) (v (j,c))
  let cover := fun (x : Fin n → Bool) => ∀ e ∈ G, x e.1 = true ∨ x e.2 = true
  let quotient := fun (y : Fin m → Bool) => ∀ i j, joined i j → y i = true ∨ y j = true
  let project := fun (x : Fin n → Bool) (i : Fin m) => x (v (i,false)) && x (v (i,true))
  let fits := fun (k : Nat) (P : (Fin k → Bool) → Prop) (out : (Fin k → Bool) → Fin m → Bool)
      (s r : Nat) =>
    ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin m → Fin (k+2+C.size)),
      PEqualNP.MetaComplexity.FanInTwo C ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (k+2) C ∧ C.output < k+2+C.size ∧
      C.size ≤ s ∧ PEqualNP.NotBracket.notCount C ≤ r ∧
      ∀ x, P x → ∀ i, (C.wires (List.ofFn x ++ [false,true])).getD (tap i).val false = out x i
  ∀ c : Fin m → Bool,
    let embedBits := fun (y : Fin m → Bool) (u : Fin n) =>
      decide (∀ i, v (i,c i) = u → y i = true)
    let legal := ∀ i j, i ≠ j → adj (v (i,c i)) (v (j,c j)) → joined i j
    (legal ↔ ∀ x, cover x → cover (embedBits (project x))) ∧
    (legal → (∀ y, quotient y ↔ cover (embedBits y)) ∧
      ∀ s r, fits n cover (fun x i => xor (x (v (i,false))) (x (v (i,true)))) s r ↔
        ∃ t, t + m ≤ s ∧ fits m quotient (fun y i => !(y i)) t r) := by
  intro n m G v hG adj hpair joined cover quotient project fits c embedBits legal
  exact PEqualNP.Outside.L_lib_1191_aux.main n m G v hG hpair c

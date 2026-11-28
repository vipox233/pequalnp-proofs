import PEqualNP.Defs
import Mathlib.Data.Fintype.EquivFin

namespace PEqualNP.Outside.L_lib_1186

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.NotBracket

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def runGates (gs : List Gate) (init : List Bool) : List Bool :=
  gs.foldl stepWire init

def mkInput {k : Nat} (x : Fin k → Bool) : List Bool :=
  List.ofFn x ++ [false, true]

lemma getD_append_lt {α : Type*} (l1 l2 : List α) (i : Nat) (d : α) (h : i < l1.length) :
    (l1 ++ l2).getD i d = l1.getD i d := by
  have h1 : i < (l1 ++ l2).length := by simp; omega
  rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h, List.getElem_append_left h]

lemma getD_append_ge {α : Type*} (l1 l2 : List α) (i : Nat) (d : α) (h : l1.length ≤ i) :
    (l1 ++ l2).getD i d = l2.getD (i - l1.length) d := by
  by_cases h2 : i < (l1 ++ l2).length
  · have h3 : i - l1.length < l2.length := by simp at h2; omega
    rw [List.getD_eq_getElem _ _ h2, List.getD_eq_getElem _ _ h3, List.getElem_append_right h]
  · have h3 : ¬ (i - l1.length < l2.length) := by simp at h2; omega
    rw [List.getD_eq_default _ _ (Nat.le_of_not_lt h2),
        List.getD_eq_default _ _ (Nat.le_of_not_lt h3)]

lemma mkInput_length {k : Nat} (x : Fin k → Bool) :
    (mkInput x).length = k + 2 := by
  simp [mkInput]

lemma mkInput_getD_lt {k : Nat} (x : Fin k → Bool) (i : Nat) (hi : i < k) :
    (mkInput x).getD i false = x ⟨i, hi⟩ := by
  have hlen : i < (List.ofFn x).length := by simp [hi]
  rw [mkInput, getD_append_lt _ _ _ _ hlen, List.getD_eq_getElem _ _ hlen]
  simp

lemma mkInput_getD_false {k : Nat} (x : Fin k → Bool) :
    (mkInput x).getD k false = false := by
  have hle : (List.ofFn x).length ≤ k := by simp
  rw [mkInput, getD_append_ge _ _ _ _ hle]
  simp

lemma mkInput_getD_true {k : Nat} (x : Fin k → Bool) :
    (mkInput x).getD (k + 1) false = true := by
  have hle : (List.ofFn x).length ≤ k + 1 := by simp
  rw [mkInput, getD_append_ge _ _ _ _ hle]
  simp

lemma wires_eq_runGates (C : Circuit) (x : List Bool) :
    C.wires x = runGates C.gates x := rfl

lemma runGates_nil (init : List Bool) :
    runGates [] init = init := rfl

lemma runGates_cons (g : Gate) (gs : List Gate) (init : List Bool) :
    runGates (g :: gs) init = runGates gs (stepWire init g) := rfl

lemma runGates_append (gs1 gs2 : List Gate) (init : List Bool) :
    runGates (gs1 ++ gs2) init = runGates gs2 (runGates gs1 init) := by
  simp [runGates, List.foldl_append]

lemma runGates_length (gs : List Gate) (init : List Bool) :
    (runGates gs init).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp [runGates]
  | cons g gs ih =>
    rw [runGates_cons, ih]
    simp [stepWire]
    omega

lemma runGates_getD_lt (gs : List Gate) (init : List Bool) (i : Nat) (hi : i < init.length) :
    (runGates gs init).getD i false = init.getD i false := by
  induction gs generalizing init with
  | nil => rfl
  | cons g gs ih =>
    have hi' : i < (stepWire init g).length := by simp [stepWire]; omega
    rw [runGates_cons, ih (stepWire init g) hi', stepWire, getD_append_lt _ _ _ _ hi]

lemma runGates_getD_gate (gs : List Gate) (init : List Bool) (j : Nat) (hj : j < gs.length) :
    (runGates gs init).getD (init.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i => (runGates (gs.take j) init).getD i false) := by
  induction gs generalizing init j with
  | nil => cases hj
  | cons g gs ih =>
    cases j with
    | zero =>
      have hi : init.length < (stepWire init g).length := by simp [stepWire]
      rw [Nat.add_zero, runGates_cons, runGates_getD_lt gs (stepWire init g) init.length hi]
      rw [stepWire, getD_append_ge _ _ _ _ (le_refl _), Nat.sub_self]
      rfl
    | succ j' =>
      have hj' : j' < gs.length := Nat.lt_of_succ_lt_succ hj
      have heq : init.length + (j' + 1) = (stepWire init g).length + j' := by
        simp [stepWire]
        omega
      rw [runGates_cons, heq, ih (stepWire init g) j' hj']
      rfl

lemma runGates_remap
    (gs : List Gate) (init1 init2 : List Bool) (f : Nat → Nat)
    (hmap_gate : ∀ j < gs.length, f (init2.length + j) = init1.length + j)
    (hreads : ∀ j (hj : j < gs.length), ∀ i ∈ (gs[j]).inputs, i < init2.length + j)
    (hinit : ∀ w < init2.length, f w < init1.length ∧ init1.getD (f w) false = init2.getD w false) :
    ∀ k ≤ gs.length, ∀ w < init2.length + k,
      f w < init1.length + k ∧
      (runGates ((gs.take k).map fun g => ⟨g.op, g.inputs.map f⟩) init1).getD (f w) false =
      (runGates (gs.take k) init2).getD w false := by
  intro k hk
  induction k with
  | zero =>
    intro w hw
    simpa [runGates] using hinit w hw
  | succ k ih =>
    have hk_lt : k < gs.length := Nat.lt_of_succ_le hk
    have ihk := ih (Nat.le_of_lt hk_lt)
    let g := gs[k]
    have htake : gs.take (k + 1) = gs.take k ++ [g] := List.take_succ_eq_append_getElem hk_lt
    let fm : Gate → Gate := fun g => ⟨g.op, g.inputs.map f⟩
    let W1 := runGates ((gs.take k).map fm) init1
    let W2 := runGates (gs.take k) init2
    have hW1_len : W1.length = init1.length + k := by
      simp [W1, runGates_length, Nat.min_eq_left (Nat.le_of_lt hk_lt)]
    have hW2_len : W2.length = init2.length + k := by
      simp [W2, runGates_length, Nat.min_eq_left (Nat.le_of_lt hk_lt)]
    have hrun1 : runGates ((gs.take (k + 1)).map fm) init1 = stepWire W1 (fm g) := by
      rw [htake, List.map_append, runGates_append]
      rfl
    have hrun2 : runGates (gs.take (k + 1)) init2 = stepWire W2 g := by
      rw [htake, runGates_append]
      rfl
    intro w hw
    rw [hrun1, hrun2]
    by_cases hlt : w < init2.length + k
    · obtain ⟨hfw_lt, hval⟩ := ihk w hlt
      refine ⟨by omega, ?_⟩
      have hfw_W1 : f w < W1.length := by omega
      have hw_W2 : w < W2.length := by omega
      rw [stepWire, getD_append_lt _ _ _ _ hfw_W1, stepWire, getD_append_lt _ _ _ _ hw_W2]
      exact hval
    · have hweq : w = init2.length + k := by omega
      subst hweq
      have hfw_eq : f (init2.length + k) = init1.length + k := hmap_gate k hk_lt
      refine ⟨by omega, ?_⟩
      rw [hfw_eq]
      have h1 : W1.length ≤ init1.length + k := by omega
      have h2 : W2.length ≤ init2.length + k := by omega
      rw [stepWire, getD_append_ge _ _ _ _ h1, stepWire, getD_append_ge _ _ _ _ h2]
      rw [show init1.length + k - W1.length = 0 by omega,
          show init2.length + k - W2.length = 0 by omega]
      simp only [List.getD_cons_zero, fm, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i hi
      have hilt : i < init2.length + k := hreads k hk_lt i hi
      exact (ihk i hilt).2

lemma notCount_append (gs1 gs2 : List Gate) (o : Nat) :
    notCount ⟨gs1 ++ gs2, o⟩ = notCount ⟨gs1, 0⟩ + notCount ⟨gs2, 0⟩ := by
  simp [notCount, List.filter_append]

lemma filter_map_length {α : Type*} (p : α → Bool) (f : α → α) (gs : List α)
    (hp : ∀ a, p (f a) = p a) :
    ((gs.map f).filter p).length = (gs.filter p).length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, List.filter_cons, hp g]
    cases p g <;> simp [ih]

lemma filter_all_false_length {α : Type*} (p : α → Bool) (gs : List α)
    (hp : ∀ a ∈ gs, p a = false) :
    (gs.filter p).length = 0 := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.filter_cons, hp g List.mem_cons_self]
    exact ih (fun a ha => hp a (List.mem_cons_of_mem _ ha))

lemma notCount_map_same_op (gs : List Gate) (f : Gate → Gate) (hf : ∀ g, (f g).op = g.op) (o : Nat) :
    notCount ⟨gs.map f, o⟩ = notCount ⟨gs, 0⟩ := by
  dsimp only [notCount]
  apply filter_map_length
  intro g
  rw [hf g]

lemma notCount_or_gates (gs : List Gate) (hor : ∀ g ∈ gs, g.op = GateOp.or) (o : Nat) :
    notCount ⟨gs, o⟩ = 0 := by
  dsimp only [notCount]
  apply filter_all_false_length
  intro g hg
  rw [hor g hg]
  rfl

lemma notCount_delete (gs : List Gate) (k : Nat) (hk : k < gs.length) (o : Nat) :
    notCount ⟨gs.take k ++ gs.drop (k + 1), o⟩ ≤ notCount ⟨gs, 0⟩ := by
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    simp
  rw [notCount_append]
  have hfull : notCount ⟨gs, 0⟩ =
      notCount ⟨gs.take k, 0⟩ + notCount ⟨[gs[k]], 0⟩ + notCount ⟨gs.drop (k + 1), 0⟩ := by
    conv_lhs => rw [hsplit]
    rw [show gs.take k ++ gs[k] :: gs.drop (k + 1) = (gs.take k ++ [gs[k]]) ++ gs.drop (k + 1) by
          simp,
        notCount_append, notCount_append]
  omega

lemma gateAt_eq_getElem (C : Circuit) (j : Nat) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  dsimp only [gateAt]
  exact List.getD_eq_getElem _ _ hj

def remapWire1 {n m : Nat} {active : Finset (Fin n)} (emb : Fin m ≃ {v : Fin n // v ∈ active})
    (sDec : Nat) (w : Nat) : Nat :=
  if h : w < m then (emb ⟨w, h⟩).val.val
  else if w = m then n
  else if w = m + 1 then n + 1
  else n + 2 + sDec + (w - (m + 2))

lemma remapWire1_lt {n m : Nat} {active : Finset (Fin n)}
    (emb : Fin m ≃ {v : Fin n // v ∈ active}) (sDec j w : Nat) (hw : w < m + 2 + j) :
    remapWire1 emb sDec w < n + 2 + sDec + j := by
  dsimp only [remapWire1]
  split_ifs with h1 h2 h3
  · have hv : (emb ⟨w, h1⟩).val.val < n := (emb ⟨w, h1⟩).val.isLt
    omega
  · omega
  · omega
  · omega

lemma forward_part
    (n : Nat) (G H : Finset (Fin n × Fin n)) (_hG : ∀ e ∈ G, e.1 < e.2) (hHG : H ⊆ G)
    (a s l p q : Nat)
    (hInd : ∀ I : Finset (Fin n),
      I ⊆ H.image Prod.fst ∪ H.image Prod.snd →
      (∀ e ∈ G, ¬ (e.1 ∈ I ∧ e.2 ∈ I)) → I.card ≤ a)
    (C_dec : Circuit)
    (hdec_fit : FanInTwo C_dec)
    (hdec_rb : ReadsBack (n + 2) C_dec)
    (hdec_out : C_dec.output < n + 2 + C_dec.size)
    (hdec_sz : C_dec.size ≤ s)
    (hdec_not : notCount C_dec ≤ p)
    (hdec_ev : ∀ x : Fin n → Bool,
      C_dec.eval (mkInput x) = true ↔ ∀ e ∈ G, x e.1 = true ∨ x e.2 = true)
    (C_inv : Circuit)
    (tap_inv : Fin (H.image Prod.fst ∪ H.image Prod.snd).card →
      Fin ((H.image Prod.fst ∪ H.image Prod.snd).card + 2 + C_inv.size))
    (hinv_fit : FanInTwo C_inv)
    (hinv_rb : ReadsBack ((H.image Prod.fst ∪ H.image Prod.snd).card + 2) C_inv)
    (hinv_sz : C_inv.size ≤ l)
    (hinv_not : notCount C_inv ≤ q)
    (hinv_ev : ∀ x : Fin (H.image Prod.fst ∪ H.image Prod.snd).card → Bool,
      ((Finset.univ : Finset (Fin (H.image Prod.fst ∪ H.image Prod.snd).card)).filter
        (fun i => x i = false)).card ≤ a →
      ∀ i, (C_inv.wires (mkInput x)).getD (tap_inv i).val false = !x i) :
    ∃ C : Circuit,
      (FanInTwo C ∧ ReadsBack (n + 2) C ∧ C.output < n + 2 + C.size) ∧
      (∃ tap : ↥H → Fin (n + 2 + C.size), ∀ x : Fin n → Bool,
        (C.eval (mkInput x) = true ↔ ∀ e ∈ G, x e.1 = true ∨ x e.2 = true) ∧
        ((∀ e ∈ G, x e.1 = true ∨ x e.2 = true) →
          ∀ e, (C.wires (mkInput x)).getD (tap e).val false = xor (x e.val.1) (x e.val.2))) ∧
      C.size ≤ s + l + H.card ∧ notCount C ≤ p + q := by
  classical
  let active := H.image Prod.fst ∪ H.image Prod.snd
  let m := active.card
  let emb : Fin m ≃ ↥active := active.equivFin.symm
  let eH : Fin H.card ≃ ↥H := H.equivFin.symm
  let rw1 : Nat → Nat := remapWire1 emb C_dec.size
  let rg1 : Gate → Gate := fun g => ⟨g.op, g.inputs.map rw1⟩
  let gs_inv : List Gate := C_inv.gates.map rg1
  have hmem_fst : ∀ e : ↥H, e.val.1 ∈ active := fun e =>
    Finset.mem_union_left _ (Finset.mem_image_of_mem Prod.fst e.property)
  have hmem_snd : ∀ e : ↥H, e.val.2 ∈ active := fun e =>
    Finset.mem_union_right _ (Finset.mem_image_of_mem Prod.snd e.property)
  let negW : (v : Fin n) → v ∈ active → Nat := fun v hv =>
    rw1 (tap_inv (emb.symm ⟨v, hv⟩)).val
  have hnegW_lt : ∀ (v : Fin n) (hv : v ∈ active),
      negW v hv < n + 2 + C_dec.size + C_inv.size := by
    intro v hv
    exact remapWire1_lt emb C_dec.size C_inv.size _ (tap_inv (emb.symm ⟨v, hv⟩)).isLt
  let orGates : List Gate :=
    (List.finRange H.card).map fun k =>
      ⟨GateOp.or, [negW (eH k).val.1 (hmem_fst (eH k)), negW (eH k).val.2 (hmem_snd (eH k))]⟩
  have horGates_len : orGates.length = H.card := by simp [orGates]
  let C_comb : Circuit := ⟨C_dec.gates ++ gs_inv ++ orGates, C_dec.output⟩
  have hsz_comb : C_comb.size = C_dec.size + C_inv.size + H.card := by
    simp [C_comb, Circuit.size, gs_inv, horGates_len]
    omega
  have hfit_comb : FanInTwo C_comb := by
    intro g hg
    simp only [C_comb, List.mem_append] at hg
    rcases hg with (hg | hg) | hg
    · exact hdec_fit g hg
    · rcases List.mem_map.mp hg with ⟨g0, hg0, rfl⟩
      obtain ⟨hop, hlen⟩ := hinv_fit g0 hg0
      exact ⟨hop, by simpa [rg1] using hlen⟩
    · rcases List.mem_map.mp hg with ⟨k, _, rfl⟩
      exact ⟨by simp, by simp⟩
  have hrb_comb : ReadsBack (n + 2) C_comb := by
    intro j hj i hi
    rw [gateAt_eq_getElem _ _ hj] at hi
    have hj' : j < (C_dec.gates ++ gs_inv).length + orGates.length := by
      simp [C_comb] at hj ⊢
      omega
    by_cases h1 : j < (C_dec.gates ++ gs_inv).length
    · have hget1 : C_comb.gates[j] = (C_dec.gates ++ gs_inv)[j] := by
        simp only [C_comb]
        exact List.getElem_append_left h1
      rw [hget1] at hi
      by_cases h2 : j < C_dec.gates.length
      · have hget2 : (C_dec.gates ++ gs_inv)[j] = C_dec.gates[j] :=
          List.getElem_append_left h2
        rw [hget2] at hi
        exact hdec_rb j h2 i (by rwa [gateAt_eq_getElem _ _ h2])
      · have hj_inv : j - C_dec.gates.length < C_inv.gates.length := by
          simp [gs_inv] at h1
          omega
        have hj_gsinv : j - C_dec.gates.length < gs_inv.length := by
          simp [gs_inv]
          exact hj_inv
        have hget2 : (C_dec.gates ++ gs_inv)[j] = gs_inv[j - C_dec.gates.length] :=
          List.getElem_append_right (Nat.le_of_not_lt h2)
        rw [hget2] at hi
        simp only [gs_inv, List.getElem_map, rg1] at hi
        rcases List.mem_map.mp hi with ⟨i0, hi0, rfl⟩
        have hi0_lt : i0 < m + 2 + (j - C_dec.gates.length) :=
          hinv_rb (j - C_dec.gates.length) hj_inv i0 (by rwa [gateAt_eq_getElem _ _ hj_inv])
        have hlt := remapWire1_lt emb C_dec.size (j - C_dec.gates.length) i0 hi0_lt
        dsimp only [rw1, Circuit.size] at hlt ⊢
        omega
    · have hj_or : j - (C_dec.gates ++ gs_inv).length < orGates.length := by omega
      have hget1 : C_comb.gates[j] = orGates[j - (C_dec.gates ++ gs_inv).length] := by
        simp only [C_comb]
        exact List.getElem_append_right (Nat.le_of_not_lt h1)
      rw [hget1] at hi
      simp only [orGates, List.getElem_map, List.mem_cons, List.not_mem_nil, or_false] at hi
      have hlen_mid : (C_dec.gates ++ gs_inv).length = C_dec.size + C_inv.size := by
        simp [Circuit.size, gs_inv]
      rcases hi with rfl | rfl
      · exact Nat.lt_of_lt_of_le (hnegW_lt _ _) (by omega)
      · exact Nat.lt_of_lt_of_le (hnegW_lt _ _) (by omega)
  have hout_comb : C_comb.output < n + 2 + C_comb.size := by
    rw [hsz_comb]
    dsimp only [C_comb]
    omega
  have hnot_comb : notCount C_comb ≤ p + q := by
    have h1 : notCount C_comb =
        notCount ⟨C_dec.gates, 0⟩ + notCount ⟨gs_inv, 0⟩ + notCount ⟨orGates, 0⟩ := by
      dsimp only [C_comb]
      rw [notCount_append, notCount_append]
    have h2 : notCount ⟨gs_inv, 0⟩ = notCount C_inv := by
      exact notCount_map_same_op C_inv.gates rg1 (fun _ => rfl) 0
    have h3 : notCount ⟨orGates, 0⟩ = 0 := by
      apply notCount_or_gates
      intro g hg
      rcases List.mem_map.mp hg with ⟨k, _, rfl⟩
      rfl
    have h4 : notCount ⟨C_dec.gates, 0⟩ = notCount C_dec := rfl
    omega
  let tap_comb : ↥H → Fin (n + 2 + C_comb.size) := fun e =>
    ⟨n + 2 + C_dec.size + C_inv.size + (eH.symm e).val, by
      rw [hsz_comb]
      have := (eH.symm e).isLt
      omega⟩
  refine ⟨C_comb, ⟨hfit_comb, hrb_comb, hout_comb⟩, ⟨tap_comb, ?_⟩, by omega, hnot_comb⟩
  intro x
  have heval_eq : C_comb.eval (mkInput x) = C_dec.eval (mkInput x) := by
    dsimp only [Circuit.eval]
    rw [wires_eq_runGates, wires_eq_runGates]
    dsimp only [C_comb]
    rw [show C_dec.gates ++ gs_inv ++ orGates = C_dec.gates ++ (gs_inv ++ orGates) by
          simp [List.append_assoc],
        runGates_append]
    have hlen : C_dec.output < (runGates C_dec.gates (mkInput x)).length := by
      rw [runGates_length, mkInput_length]
      exact hdec_out
    exact runGates_getD_lt (gs_inv ++ orGates) (runGates C_dec.gates (mkInput x)) C_dec.output hlen
  refine ⟨by rw [heval_eq]; exact hdec_ev x, ?_⟩
  intro hcov e
  let y : Fin m → Bool := fun i => x (emb i).val
  have hy_card : ((Finset.univ : Finset (Fin m)).filter (fun i => y i = false)).card ≤ a := by
    let I : Finset (Fin n) := active.filter (fun v => x v = false)
    have hI_le : I.card ≤ a := by
      apply hInd I (Finset.filter_subset _ _)
      intro e' he' hboth
      have h1 : x e'.1 = false := (Finset.mem_filter.mp hboth.1).2
      have h2 : x e'.2 = false := (Finset.mem_filter.mp hboth.2).2
      rcases hcov e' he' with h1' | h2'
      · rw [h1'] at h1; cases h1
      · rw [h2'] at h2; cases h2
    have hcard_eq : ((Finset.univ : Finset (Fin m)).filter (fun i => y i = false)).card = I.card := by
      apply Finset.card_bij (fun i _ => (emb i).val)
      · intro i hi
        have hyi : x (emb i).val = false := (Finset.mem_filter.mp hi).2
        exact Finset.mem_filter.mpr ⟨(emb i).property, hyi⟩
      · intro i1 _ i2 _ heq
        exact emb.injective (Subtype.ext heq)
      · intro v hv
        obtain ⟨hv_act, hxv⟩ := Finset.mem_filter.mp hv
        refine ⟨emb.symm ⟨v, hv_act⟩, ?_, ?_⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [y, hxv]⟩
        · simp
    omega
  let W_dec := runGates C_dec.gates (mkInput x)
  have hW_dec_len : W_dec.length = n + 2 + C_dec.size := by
    rw [runGates_length, mkInput_length]; rfl
  let W_mid := runGates gs_inv W_dec
  have hW_mid_len : W_mid.length = n + 2 + C_dec.size + C_inv.size := by
    rw [runGates_length, hW_dec_len]; simp [gs_inv, Circuit.size]
  have hmid_sim : ∀ w < m + 2 + C_inv.size,
      W_mid.getD (rw1 w) false = (C_inv.wires (mkInput y)).getD w false := by
    have hrem := runGates_remap C_inv.gates W_dec (mkInput y) rw1
      (by
        intro j _
        rw [mkInput_length, hW_dec_len]
        dsimp only [rw1, remapWire1]
        have h1 : ¬ (m + 2 + j < m) := by omega
        have h2 : ¬ (m + 2 + j = m) := by omega
        have h3 : ¬ (m + 2 + j = m + 1) := by omega
        simp [h1, h2, h3])
      (by
        intro j hj i hi
        rw [mkInput_length]
        exact hinv_rb j hj i (by rwa [gateAt_eq_getElem _ _ hj]))
      (by
        intro w hw
        rw [mkInput_length] at hw
        by_cases h1 : w < m
        · have hv : (emb ⟨w, h1⟩).val.val < n := (emb ⟨w, h1⟩).val.isLt
          have hrw : rw1 w = (emb ⟨w, h1⟩).val.val := by simp [rw1, remapWire1, h1]
          rw [hrw]
          refine ⟨by omega, ?_⟩
          have hlt_in : (emb ⟨w, h1⟩).val.val < (mkInput x).length := by
            rw [mkInput_length]; omega
          rw [runGates_getD_lt C_dec.gates (mkInput x) _ hlt_in,
              mkInput_getD_lt x _ hv, mkInput_getD_lt y w h1]
        · by_cases h2 : w = m
          · rw [h2]
            have hrw : rw1 m = n := by simp [rw1, remapWire1]
            rw [hrw]
            refine ⟨by omega, ?_⟩
            have hlt_in : n < (mkInput x).length := by rw [mkInput_length]; omega
            rw [runGates_getD_lt C_dec.gates (mkInput x) n hlt_in,
                mkInput_getD_false x, mkInput_getD_false y]
          · have h3 : w = m + 1 := by omega
            rw [h3]
            have hrw : rw1 (m + 1) = n + 1 := by simp [rw1, remapWire1]
            rw [hrw]
            refine ⟨by omega, ?_⟩
            have hlt_in : n + 1 < (mkInput x).length := by rw [mkInput_length]; omega
            rw [runGates_getD_lt C_dec.gates (mkInput x) (n + 1) hlt_in,
                mkInput_getD_true x, mkInput_getD_true y])
      C_inv.gates.length (le_refl _)
    intro w hw
    have htake : C_inv.gates.take C_inv.gates.length = C_inv.gates := List.take_length
    have hres := (hrem w (by rw [mkInput_length]; exact hw)).2
    rw [htake] at hres
    exact hres
  have hneg_val : ∀ (v : Fin n) (hv : v ∈ active), W_mid.getD (negW v hv) false = !x v := by
    intro v hv
    let i := emb.symm ⟨v, hv⟩
    have h1 := hmid_sim (tap_inv i).val (tap_inv i).isLt
    have h2 := hinv_ev y hy_card i
    dsimp only [negW]
    rw [h1, h2]
    have hemb : (emb i).val = v := by simp [i]
    simp [y, hemb]
  have hcomb_wires : C_comb.wires (mkInput x) = runGates orGates W_mid := by
    rw [wires_eq_runGates]
    dsimp only [C_comb, W_mid, W_dec]
    rw [runGates_append, runGates_append]
  rw [hcomb_wires]
  let k := (eH.symm e).val
  have hk_lt : k < orGates.length := by rw [horGates_len]; exact (eH.symm e).isLt
  have htap_eq : (tap_comb e).val = W_mid.length + k := by
    dsimp only [tap_comb, k]
    omega
  rw [htap_eq, runGates_getD_gate orGates W_mid k hk_lt]
  have hget_or : orGates[k] =
      ⟨GateOp.or, [negW e.val.1 (hmem_fst e), negW e.val.2 (hmem_snd e)]⟩ := by
    have hk' : k < H.card := (eH.symm e).isLt
    have hek : eH ⟨k, hk'⟩ = e := by simp [k]
    simp only [orGates, List.getElem_map, List.getElem_finRange]
    simp [hek]
  rw [hget_or]
  have hw1_lt : negW e.val.1 (hmem_fst e) < W_mid.length := by
    rw [hW_mid_len]; exact hnegW_lt _ _
  have hw2_lt : negW e.val.2 (hmem_snd e) < W_mid.length := by
    rw [hW_mid_len]; exact hnegW_lt _ _
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
    Bool.or_false]
  rw [runGates_getD_lt _ W_mid _ hw1_lt, runGates_getD_lt _ W_mid _ hw2_lt,
      hneg_val e.val.1 (hmem_fst e), hneg_val e.val.2 (hmem_snd e)]
  have heG : e.val ∈ G := hHG e.property
  rcases hcov e.val heG with h1 | h2
  · cases x e.val.2 <;> simp [h1]
  · cases x e.val.1 <;> simp [h2]

def cleanGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

def cleanNot (C : Circuit) : Circuit :=
  ⟨C.gates.map cleanGate, C.output⟩

def CleanNotProp (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1

lemma cleanGate_op (g : Gate) : (cleanGate g).op = g.op := by
  cases h : g.op <;> simp [cleanGate, h]

lemma cleanGate_eval (g : Gate) (w : List Bool) :
    (cleanGate g).op.eval ((cleanGate g).inputs.map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false) := by
  cases h : g.op
  · simp [cleanGate, h]
  · simp [cleanGate, h]
  · simp only [cleanGate, h, GateOp.eval]
    cases g.inputs with
    | nil => rfl
    | cons a rest => rfl
  · simp [cleanGate, h]
  · simp [cleanGate, h]

lemma runGates_clean (gs : List Gate) (init : List Bool) :
    runGates (gs.map cleanGate) init = runGates gs init := by
  induction gs generalizing init with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, runGates_cons, stepWire]
    rw [cleanGate_eval]
    exact ih _

lemma cleanNot_wires (C : Circuit) (x : List Bool) :
    (cleanNot C).wires x = C.wires x :=
  runGates_clean C.gates x

lemma cleanNot_size (C : Circuit) : (cleanNot C).size = C.size := by
  simp [cleanNot, Circuit.size]

lemma cleanNot_notCount (C : Circuit) : notCount (cleanNot C) = notCount C :=
  notCount_map_same_op C.gates cleanGate cleanGate_op C.output

lemma cleanNot_fanInTwo (C : Circuit) (h : FanInTwo C) : FanInTwo (cleanNot C) := by
  intro g hg
  rcases List.mem_map.mp hg with ⟨g0, hg0, rfl⟩
  obtain ⟨hop, hlen⟩ := h g0 hg0
  refine ⟨by rwa [cleanGate_op], ?_⟩
  cases h0 : g0.op <;> simp [cleanGate, h0, hlen]

lemma cleanNot_readsBack (N : Nat) (C : Circuit) (h : ReadsBack N C) :
    ReadsBack N (cleanNot C) := by
  intro j hj i hi
  rw [gateAt_eq_getElem _ _ hj] at hi
  have hj0 : j < C.gates.length := by simpa [cleanNot] using hj
  simp only [cleanNot, List.getElem_map] at hi
  have hi0 : i ∈ (C.gates[j]).inputs := by
    cases hop : (C.gates[j]).op <;> simp [cleanGate, hop] at hi
    · exact hi
    · exact hi
    · exact List.mem_of_mem_take hi
    · exact hi
    · exact hi
  exact h j hj0 i (by rwa [gateAt_eq_getElem _ _ hj0])

lemma cleanNot_prop (C : Circuit) : CleanNotProp (cleanNot C) := by
  intro g hg hop
  rcases List.mem_map.mp hg with ⟨g0, _, rfl⟩
  rw [cleanGate_op] at hop
  simp [cleanGate, hop]

def ext {n : Nat} (T : Finset (Fin n)) (x : Fin n → Bool) (w : Fin n) : Bool :=
  if w ∈ T then true else x w

lemma ext_empty {n : Nat} (x : Fin n → Bool) : ext (∅ : Finset (Fin n)) x = x := by
  funext w
  simp [ext]

lemma ext_update_true {n : Nat} (T : Finset (Fin n)) (x : Fin n → Bool) (u : Fin n) :
    ext T (Function.update x u true) = ext (insert u T) x := by
  funext w
  by_cases hw : w = u
  · subst hw; simp [ext]
  · simp [ext, hw]

lemma runGates_eq_except (gs : List Gate) (init1 init2 : List Bool) (u_idx : Nat)
    (hlen : init1.length = init2.length) (hu : u_idx < init1.length)
    (hinit : ∀ w, w ≠ u_idx → init1.getD w false = init2.getD w false)
    (hno : ∀ g ∈ gs, u_idx ∉ g.inputs) :
    ∀ w, w ≠ u_idx → (runGates gs init1).getD w false = (runGates gs init2).getD w false := by
  induction gs generalizing init1 init2 with
  | nil => exact hinit
  | cons g gs ih =>
    have hg_no : u_idx ∉ g.inputs := hno g List.mem_cons_self
    have hval : g.op.eval (g.inputs.map fun i => init1.getD i false) =
        g.op.eval (g.inputs.map fun i => init2.getD i false) := by
      congr 1
      apply List.map_congr_left
      intro i hi
      exact hinit i (fun heq => hg_no (heq ▸ hi))
    apply ih (stepWire init1 g) (stepWire init2 g)
    · simp [stepWire, hlen]
    · simp [stepWire]; omega
    · intro w hw
      by_cases hlt : w < init1.length
      · have hlt2 : w < init2.length := by omega
        rw [stepWire, getD_append_lt _ _ _ _ hlt, stepWire, getD_append_lt _ _ _ _ hlt2]
        exact hinit w hw
      · have hge1 : init1.length ≤ w := Nat.le_of_not_lt hlt
        have hge2 : init2.length ≤ w := by omega
        rw [stepWire, getD_append_ge _ _ _ _ hge1, stepWire, getD_append_ge _ _ _ _ hge2]
        rw [hlen, hval]
    · intro g' hg'
      exact hno g' (List.mem_cons_of_mem _ hg')

def substWire (n u_val k0 rep w : Nat) : Nat :=
  if w = u_val then n + 1
  else if w < n + 2 + k0 then w
  else if w = n + 2 + k0 then rep
  else w - 1

lemma substWire_lt_before (n u_val k0 rep j w : Nat) (hj : j < k0) (hw : w < n + 2 + j) :
    substWire n u_val k0 rep w < n + 2 + j := by
  dsimp only [substWire]
  split_ifs <;> omega

lemma substWire_lt_after (n u_val k0 rep j w : Nat)
    (hrep : rep < n + 2 + k0) (hj : k0 ≤ j) (hw : w < n + 2 + (j + 1)) :
    substWire n u_val k0 rep w < n + 2 + j := by
  dsimp only [substWire]
  split_ifs <;> omega

def GoodCircuit (n : Nat) (G H : Finset (Fin n × Fin n)) (T : Finset (Fin n))
    (C : Circuit) (tap : ↥H → Fin (n + 2 + C.size)) : Prop :=
  FanInTwo C ∧ ReadsBack (n + 2) C ∧ C.output < n + 2 + C.size ∧ CleanNotProp C ∧
  ∀ x : Fin n → Bool,
    (C.eval (mkInput x) = true ↔ ∀ e ∈ G, ext T x e.1 = true ∨ ext T x e.2 = true) ∧
    ((∀ e ∈ G, ext T x e.1 = true ∨ ext T x e.2 = true) →
      ∀ e : ↥H, (C.wires (mkInput x)).getD (tap e).val false =
        xor (ext T x e.val.1) (ext T x e.val.2))

lemma dropStep
    (n : Nat) (G H : Finset (Fin n × Fin n)) (hG : ∀ e ∈ G, e.1 < e.2)
    (T : Finset (Fin n)) (C : Circuit) (tap : ↥H → Fin (n + 2 + C.size))
    (hGood : GoodCircuit n G H T C tap)
    (u v : Fin n) (huT : u ∉ T) (hvT : v ∉ T) (huv : (u, v) ∈ G ∨ (v, u) ∈ G) :
    ∃ (C' : Circuit) (tap' : ↥H → Fin (n + 2 + C'.size)),
      GoodCircuit n G H (insert u T) C' tap' ∧
      C'.size + 1 = C.size ∧ notCount C' ≤ notCount C := by
  obtain ⟨hfit, hrb, hout, hclean, hev⟩ := hGood
  have huv_ne : u ≠ v := by
    rcases huv with h | h
    · exact ne_of_lt (hG (u, v) h)
    · exact ne_of_gt (hG (v, u) h)
  let x0 : Fin n → Bool := fun w => decide (w ≠ u ∧ w ≠ v)
  let x1 : Fin n → Bool := fun w => decide (w ≠ v)
  let x2 : Fin n → Bool := fun w => decide (w ≠ u)
  have hx0_uncov : ¬ (∀ e ∈ G, ext T x0 e.1 = true ∨ ext T x0 e.2 = true) := by
    intro hcov
    rcases huv with h | h
    · rcases hcov (u, v) h with h1 | h2
      · simp [ext, huT, x0] at h1
      · simp [ext, hvT, x0] at h2
    · rcases hcov (v, u) h with h1 | h2
      · simp [ext, hvT, x0] at h1
      · simp [ext, huT, x0] at h2
  have hx0_eval : C.eval (mkInput x0) = false := by
    cases h : C.eval (mkInput x0)
    · rfl
    · exact False.elim (hx0_uncov ((hev x0).1.mp h))
  have hx1_cov : ∀ e ∈ G, ext T x1 e.1 = true ∨ ext T x1 e.2 = true := by
    intro e he
    have hne : e.1 ≠ e.2 := ne_of_lt (hG e he)
    by_cases h1 : e.1 = v
    · right
      have h2 : e.2 ≠ v := fun h2 => hne (h1.trans h2.symm)
      by_cases ht : e.2 ∈ T <;> simp [ext, ht, x1, h2]
    · left
      by_cases ht : e.1 ∈ T <;> simp [ext, ht, x1, h1]
  have hx1_eval : C.eval (mkInput x1) = true := (hev x1).1.mpr hx1_cov
  have hx2_cov : ∀ e ∈ G, ext T x2 e.1 = true ∨ ext T x2 e.2 = true := by
    intro e he
    have hne : e.1 ≠ e.2 := ne_of_lt (hG e he)
    by_cases h1 : e.1 = u
    · right
      have h2 : e.2 ≠ u := fun h2 => hne (h1.trans h2.symm)
      by_cases ht : e.2 ∈ T <;> simp [ext, ht, x2, h2]
    · left
      by_cases ht : e.1 ∈ T <;> simp [ext, ht, x2, h1]
  have hx2_eval : C.eval (mkInput x2) = true := (hev x2).1.mpr hx2_cov
  have hout_ne : C.output ≠ u.val := by
    intro heq
    have hval : C.eval (mkInput x2) = false := by
      dsimp only [Circuit.eval]
      rw [heq, wires_eq_runGates]
      have hlt : u.val < (mkInput x2).length := by rw [mkInput_length]; exact Nat.lt_trans u.isLt (by omega)
      rw [runGates_getD_lt C.gates (mkInput x2) u.val hlt, mkInput_getD_lt x2 u.val u.isLt]
      simp [x2]
    rw [hval] at hx2_eval
    cases hx2_eval
  have hex_gate : ∃ (k0 : Nat) (hk0 : k0 < C.gates.length), u.val ∈ (C.gates[k0]'hk0).inputs := by
    by_contra hno
    have hno' : ∀ g ∈ C.gates, u.val ∉ g.inputs := by
      intro g hg hmem
      rcases List.mem_iff_getElem.mp hg with ⟨k0, hk0, rfl⟩
      exact hno ⟨k0, hk0, hmem⟩
    have heq_wires : C.eval (mkInput x0) = C.eval (mkInput x1) := by
      dsimp only [Circuit.eval]
      rw [wires_eq_runGates, wires_eq_runGates]
      apply runGates_eq_except C.gates (mkInput x0) (mkInput x1) u.val
      · simp [mkInput_length]
      · rw [mkInput_length]; have := u.isLt; omega
      · intro w hw
        by_cases hlt : w < n
        · rw [mkInput_getD_lt x0 w hlt, mkInput_getD_lt x1 w hlt]
          have hwne : (⟨w, hlt⟩ : Fin n) ≠ u := fun h => hw (congrArg Fin.val h)
          simp [x0, x1, hwne]
        · by_cases hwn : w = n
          · subst hwn; rw [mkInput_getD_false, mkInput_getD_false]
          · by_cases hwn1 : w = n + 1
            · subst hwn1; rw [mkInput_getD_true, mkInput_getD_true]
            · have hge0 : (mkInput x0).length ≤ w := by rw [mkInput_length]; omega
              have hge1 : (mkInput x1).length ≤ w := by rw [mkInput_length]; omega
              rw [List.getD_eq_default _ _ hge0, List.getD_eq_default _ _ hge1]
      · exact hno'
      · exact hout_ne
    rw [hx0_eval, hx1_eval] at heq_wires
    cases heq_wires
  rcases hex_gate with ⟨k0, hk0, hu_mem⟩
  let g0 := C.gates[k0]
  have hg0_mem : g0 ∈ C.gates := List.getElem_mem hk0
  obtain ⟨hg0_op, hg0_len⟩ := hfit g0 hg0_mem
  have hg0_rb : ∀ i ∈ g0.inputs, i < n + 2 + k0 := fun i hi =>
    hrb k0 hk0 i (by rwa [gateAt_eq_getElem _ _ hk0])
  have hrep_ex : ∃ rep : Nat, rep < n + 2 + k0 ∧ rep ≠ u.val ∧
      ∀ x : Fin n → Bool,
        let W := runGates (C.gates.take k0) (mkInput (Function.update x u true))
        W.getD rep false = g0.op.eval (g0.inputs.map fun i => W.getD i false) := by
    have hW_u : ∀ x : Fin n → Bool,
        (runGates (C.gates.take k0) (mkInput (Function.update x u true))).getD u.val false = true := by
      intro x
      have hlt : u.val < (mkInput (Function.update x u true)).length := by
        rw [mkInput_length]; have := u.isLt; omega
      rw [runGates_getD_lt _ _ _ hlt, mkInput_getD_lt _ _ u.isLt]
      simp
    have hW_n : ∀ x : Fin n → Bool,
        (runGates (C.gates.take k0) (mkInput (Function.update x u true))).getD n false = false := by
      intro x
      have hlt : n < (mkInput (Function.update x u true)).length := by rw [mkInput_length]; omega
      rw [runGates_getD_lt _ _ _ hlt, mkInput_getD_false]
    have hW_n1 : ∀ x : Fin n → Bool,
        (runGates (C.gates.take k0) (mkInput (Function.update x u true))).getD (n + 1) false = true := by
      intro x
      have hlt : n + 1 < (mkInput (Function.update x u true)).length := by rw [mkInput_length]; omega
      rw [runGates_getD_lt _ _ _ hlt, mkInput_getD_true]
    have hu_lt : u.val < n := u.isLt
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg0_op
    rcases hg0_op with hop | hop | hop
    · cases hlist : g0.inputs with
      | nil => rw [hlist] at hu_mem; cases hu_mem
      | cons a rest =>
        cases rest with
        | nil =>
          have ha : a = u.val := by
            rw [hlist, List.mem_singleton] at hu_mem
            exact hu_mem.symm
          refine ⟨n + 1, by omega, by omega, ?_⟩
          intro x
          simp only [hop, ha, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
            List.all_nil, id_eq, Bool.and_true]
          rw [hW_n1, hW_u]
        | cons b rest2 =>
          cases rest2 with
          | nil =>
            rw [hlist] at hu_mem hg0_rb
            have ha_lt : a < n + 2 + k0 := hg0_rb a (by simp)
            have hb_lt : b < n + 2 + k0 := hg0_rb b (by simp)
            by_cases hau : a = u.val
            · let rep := if b = u.val then n + 1 else b
              refine ⟨rep, ?_, ?_, ?_⟩
              · dsimp only [rep]; split_ifs <;> omega
              · dsimp only [rep]; split_ifs <;> omega
              · intro x
                simp only [hop, hau, GateOp.eval, List.map_cons, List.map_nil,
                  List.all_cons, List.all_nil, id_eq, Bool.and_true, hW_u, Bool.true_and]
                dsimp only [rep]
                split_ifs with hbu
                · rw [hbu, hW_n1, hW_u]
                · rfl
            · have hbu : b = u.val := by
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hu_mem
                rcases hu_mem with h | h
                · exact False.elim (hau h.symm)
                · exact h.symm
              refine ⟨a, ha_lt, hau, ?_⟩
              intro x
              simp only [hop, hbu, GateOp.eval, List.map_cons, List.map_nil,
                List.all_cons, List.all_nil, id_eq, Bool.and_true, hW_u]
          | cons c rest3 =>
            rw [hlist] at hg0_len
            simp at hg0_len
    · refine ⟨n + 1, by omega, by omega, ?_⟩
      intro x
      simp only [hop, GateOp.eval]
      rw [hW_n1]
      symm
      rw [List.any_eq_true]
      exact ⟨true, List.mem_map.mpr ⟨u.val, hu_mem, hW_u x⟩, rfl⟩
    · have hlen1 : g0.inputs.length ≤ 1 := hclean g0 hg0_mem hop
      cases hlist : g0.inputs with
      | nil => rw [hlist] at hu_mem; cases hu_mem
      | cons a rest =>
        cases rest with
        | nil =>
          have ha : a = u.val := by
            rw [hlist, List.mem_singleton] at hu_mem
            exact hu_mem.symm
          refine ⟨n, by omega, by omega, ?_⟩
          intro x
          simp only [hop, ha, GateOp.eval, List.map_cons, List.map_nil, List.headD_cons]
          rw [hW_n, hW_u]
          rfl
        | cons b rest2 =>
          rw [hlist] at hlen1
          simp at hlen1
  rcases hrep_ex with ⟨rep, hrep_lt, hrep_ne, hrep_val⟩
  let sw : Nat → Nat := substWire n u.val k0 rep
  let fm : Gate → Gate := fun g => ⟨g.op, g.inputs.map sw⟩
  let gs1 := C.gates.take k0
  let gs2 := C.gates.drop (k0 + 1)
  have hgs1_len : gs1.length = k0 := by
    simp [gs1, Nat.min_eq_left (Nat.le_of_lt hk0)]
  have hgs2_len : gs2.length = C.gates.length - (k0 + 1) := by
    simp [gs2]
  let C' : Circuit := ⟨(gs1 ++ gs2).map fm, sw C.output⟩
  have hsz' : C'.size + 1 = C.size := by
    simp only [C', Circuit.size, List.length_map, List.length_append, hgs1_len, hgs2_len]
    omega
  have hnot' : notCount C' ≤ notCount C := by
    have h1 : notCount C' = notCount ⟨gs1 ++ gs2, 0⟩ :=
      notCount_map_same_op (gs1 ++ gs2) fm (fun _ => rfl) (sw C.output)
    rw [h1]
    exact notCount_delete C.gates k0 hk0 0
  have hfit' : FanInTwo C' := by
    intro g hg
    rcases List.mem_map.mp hg with ⟨g1, hg1, rfl⟩
    have hg1_in : g1 ∈ C.gates := by
      rcases List.mem_append.mp hg1 with h1 | h2
      · exact List.mem_of_mem_take h1
      · exact List.mem_of_mem_drop h2
    obtain ⟨hop, hlen⟩ := hfit g1 hg1_in
    exact ⟨hop, by simpa [fm] using hlen⟩
  have hclean' : CleanNotProp C' := by
    intro g hg hop
    rcases List.mem_map.mp hg with ⟨g1, hg1, rfl⟩
    have hg1_in : g1 ∈ C.gates := by
      rcases List.mem_append.mp hg1 with h1 | h2
      · exact List.mem_of_mem_take h1
      · exact List.mem_of_mem_drop h2
    simpa [fm] using hclean g1 hg1_in hop
  have hrb' : ReadsBack (n + 2) C' := by
    intro j hj i hi
    rw [gateAt_eq_getElem _ _ hj] at hi
    have hj' : j < (gs1 ++ gs2).length := by simpa [C'] using hj
    simp only [C', List.getElem_map, fm] at hi
    rcases List.mem_map.mp hi with ⟨i0, hi0, rfl⟩
    by_cases hjk : j < k0
    · have hget : (gs1 ++ gs2)[j] = gs1[j] := by
        exact List.getElem_append_left (by rw [hgs1_len]; exact hjk)
      rw [hget] at hi0
      have hjC : j < C.gates.length := Nat.lt_trans hjk hk0
      have hget1 : gs1[j] = C.gates[j] := List.getElem_take
      rw [hget1] at hi0
      have hi0_lt : i0 < n + 2 + j := hrb j hjC i0 (by rwa [gateAt_eq_getElem _ _ hjC])
      exact substWire_lt_before n u.val k0 rep j i0 hjk hi0_lt
    · have hge : gs1.length ≤ j := by rw [hgs1_len]; exact Nat.le_of_not_lt hjk
      have hj_gs2 : j - gs1.length < gs2.length := by
        simp only [List.length_append] at hj'
        omega
      have hget : (gs1 ++ gs2)[j] = gs2[j - gs1.length] := List.getElem_append_right hge
      rw [hget] at hi0
      have hj1_lt : j + 1 < C.gates.length := by
        simp only [List.length_append, hgs1_len, hgs2_len] at hj'
        omega
      have hget2 : gs2[j - gs1.length] = C.gates[j + 1] := by
        simp only [gs2, List.getElem_drop, hgs1_len]
        congr 1
        omega
      rw [hget2] at hi0
      have hi0_lt : i0 < n + 2 + (j + 1) :=
        hrb (j + 1) hj1_lt i0 (by rwa [gateAt_eq_getElem _ _ hj1_lt])
      exact substWire_lt_after n u.val k0 rep j i0 hrep_lt (Nat.le_of_not_lt hjk) hi0_lt
  have hsw_bound : ∀ w < n + 2 + C.size, sw w < n + 2 + C'.size := by
    intro w hw
    have hCsz : C.size = C.gates.length := rfl
    have hk0_le : k0 ≤ C'.size := by omega
    have hw' : w < n + 2 + (C'.size + 1) := by omega
    exact substWire_lt_after n u.val k0 rep C'.size w hrep_lt hk0_le hw'
  have hout' : C'.output < n + 2 + C'.size := hsw_bound C.output hout
  let tap' : ↥H → Fin (n + 2 + C'.size) := fun e => ⟨sw (tap e).val, hsw_bound (tap e).val (tap e).isLt⟩
  have hsim : ∀ (x : Fin n → Bool) (w : Nat), w < n + 2 + C.size →
      (C'.wires (mkInput x)).getD (sw w) false =
        (C.wires (mkInput (Function.update x u true))).getD w false := by
    intro x
    let x' := Function.update x u true
    have hpre := runGates_remap gs1 (mkInput x) (mkInput x') sw
      (by
        intro j hj
        rw [mkInput_length, mkInput_length]
        have hjk : j < k0 := by rwa [hgs1_len] at hj
        have hu_lt : u.val < n := u.isLt
        dsimp only [sw, substWire]
        have h1 : ¬ (n + 2 + j = u.val) := by omega
        have h2 : n + 2 + j < n + 2 + k0 := by omega
        simp [h1, h2])
      (by
        intro j hj i hi
        rw [mkInput_length]
        have hjk : j < k0 := by rwa [hgs1_len] at hj
        have hjC : j < C.gates.length := Nat.lt_trans hjk hk0
        have hget : gs1[j] = C.gates[j] := List.getElem_take
        rw [hget] at hi
        exact hrb j hjC i (by rwa [gateAt_eq_getElem _ _ hjC]))
      (by
        intro w hw
        rw [mkInput_length] at hw
        have hu_lt : u.val < n := u.isLt
        by_cases hwu : w = u.val
        · subst hwu
          have hswu : sw u.val = n + 1 := by simp [sw, substWire]
          rw [hswu]
          refine ⟨by rw [mkInput_length]; omega, ?_⟩
          rw [mkInput_getD_true, mkInput_getD_lt x' u.val u.isLt]
          simp [x']
        · have hsw_id : sw w = w := by
            dsimp only [sw, substWire]
            have hlt : w < n + 2 + k0 := by omega
            simp [hwu, hlt]
          rw [hsw_id]
          refine ⟨by rw [mkInput_length]; omega, ?_⟩
          by_cases hwn : w < n
          · rw [mkInput_getD_lt x w hwn, mkInput_getD_lt x' w hwn]
            have hwne : (⟨w, hwn⟩ : Fin n) ≠ u := fun h => hwu (congrArg Fin.val h)
            simp [x', Function.update_of_ne hwne]
          · by_cases hwn0 : w = n
            · subst hwn0; rw [mkInput_getD_false, mkInput_getD_false]
            · have hwn1 : w = n + 1 := by omega
              subst hwn1; rw [mkInput_getD_true, mkInput_getD_true])
      gs1.length (le_refl _)
    let W1 := runGates (gs1.map fm) (mkInput x)
    let W2_pre := runGates gs1 (mkInput x')
    let W2 := stepWire W2_pre g0
    have hW1_len : W1.length = n + 2 + k0 := by
      rw [runGates_length, mkInput_length, List.length_map, hgs1_len]
    have hW2_pre_len : W2_pre.length = n + 2 + k0 := by
      rw [runGates_length, mkInput_length, hgs1_len]
    have hW2_len : W2.length = n + 2 + k0 + 1 := by
      simp [W2, stepWire, hW2_pre_len]
    have hpre' : ∀ w < n + 2 + k0, sw w < n + 2 + k0 ∧ W1.getD (sw w) false = W2_pre.getD w false := by
      intro w hw
      have htake : gs1.take gs1.length = gs1 := List.take_length
      have hres := hpre w (by rw [mkInput_length, hgs1_len]; exact hw)
      rw [htake, mkInput_length, hgs1_len] at hres
      exact hres
    have hbridge : ∀ w < W2.length, sw w < W1.length ∧ W1.getD (sw w) false = W2.getD w false := by
      intro w hw
      rw [hW2_len] at hw
      rw [hW1_len]
      by_cases hlt : w < n + 2 + k0
      · obtain ⟨h1, h2⟩ := hpre' w hlt
        refine ⟨h1, ?_⟩
        rw [h2]
        have hw_lt : w < W2_pre.length := by omega
        rw [show W2 = stepWire W2_pre g0 from rfl, stepWire, getD_append_lt _ _ _ _ hw_lt]
      · have hweq : w = n + 2 + k0 := by omega
        subst hweq
        have hu_lt : u.val < n := u.isLt
        have hsw_k0 : sw (n + 2 + k0) = rep := by
          dsimp only [sw, substWire]
          have h1 : ¬ (n + 2 + k0 = u.val) := by omega
          simp [h1]
        rw [hsw_k0]
        refine ⟨hrep_lt, ?_⟩
        have hsw_rep : sw rep = rep := by
          dsimp only [sw, substWire]
          simp [hrep_ne, hrep_lt]
        have hrep_W1 : W1.getD rep false = W2_pre.getD rep false := by
          have := (hpre' rep hrep_lt).2
          rwa [hsw_rep] at this
        rw [hrep_W1, hrep_val x]
        have hge : W2_pre.length ≤ n + 2 + k0 := by omega
        rw [show W2 = stepWire W2_pre g0 from rfl, stepWire, getD_append_ge _ _ _ _ hge,
            show n + 2 + k0 - W2_pre.length = 0 by omega]
        rfl
    have hsuf := runGates_remap gs2 W1 W2 sw
      (by
        intro j _
        rw [hW2_len, hW1_len]
        have hu_lt : u.val < n := u.isLt
        dsimp only [sw, substWire]
        have h1 : ¬ (n + 2 + k0 + 1 + j = u.val) := by omega
        have h2 : ¬ (n + 2 + k0 + 1 + j < n + 2 + k0) := by omega
        have h3 : ¬ (n + 2 + k0 + 1 + j = n + 2 + k0) := by omega
        simp [h1, h2, h3])
      (by
        intro j hj i hi
        rw [hW2_len]
        have hjC : k0 + 1 + j < C.gates.length := by rw [hgs2_len] at hj; omega
        have hget : gs2[j] = C.gates[k0 + 1 + j] := List.getElem_drop
        rw [hget] at hi
        have hlt := hrb (k0 + 1 + j) hjC i (by rwa [gateAt_eq_getElem _ _ hjC])
        omega)
      hbridge gs2.length (le_refl _)
    have hC_split : C.gates = gs1 ++ g0 :: gs2 := by
      simp [gs1, gs2, g0]
    have hC'_wires : C'.wires (mkInput x) = runGates (gs2.map fm) W1 := by
      rw [wires_eq_runGates]
      dsimp only [C', W1]
      rw [List.map_append, runGates_append]
    have hC_wires : C.wires (mkInput x') = runGates gs2 W2 := by
      rw [wires_eq_runGates, hC_split, runGates_append, runGates_cons]
    intro w hw
    have hw' : w < W2.length + gs2.length := by
      rw [hW2_len, hgs2_len]
      dsimp only [Circuit.size] at hw
      omega
    have hres := (hsuf w hw').2
    rw [List.take_length] at hres
    rw [hC'_wires, hC_wires]
    exact hres
  refine ⟨C', tap', ⟨hfit', hrb', hout', hclean', ?_⟩, hsz', hnot'⟩
  intro x
  have hext : ext (insert u T) x = ext T (Function.update x u true) :=
    (ext_update_true T x u).symm
  have hev_x := hev (Function.update x u true)
  have heval_eq : C'.eval (mkInput x) = C.eval (mkInput (Function.update x u true)) := by
    dsimp only [Circuit.eval, C']
    exact hsim x C.output hout
  rw [hext, heval_eq]
  refine ⟨hev_x.1, ?_⟩
  intro hcov e
  rw [hsim x (tap e).val (tap e).isLt]
  exact hev_x.2 hcov e

def dropSet {n d : Nat} (drop : Fin d ↪ Fin n) (t : Nat) : Finset (Fin n) :=
  (Finset.univ.filter (fun h : Fin d => h.val < t)).image drop

lemma dropIter
    (n : Nat) (G H : Finset (Fin n × Fin n)) (hG : ∀ e ∈ G, e.1 < e.2)
    (d : Nat) (drop : Fin d ↪ Fin n)
    (hdrop : ∀ j : Fin d, ∃ v : Fin n,
      ((drop j, v) ∈ G ∨ (v, drop j) ∈ G) ∧ ∀ h : Fin d, h.val < j.val → drop h ≠ v)
    (C0 : Circuit) (tap0 : ↥H → Fin (n + 2 + C0.size))
    (hGood0 : GoodCircuit n G H ∅ C0 tap0) :
    ∀ t ≤ d, ∃ (C : Circuit) (tap : ↥H → Fin (n + 2 + C.size)),
      GoodCircuit n G H (dropSet drop t) C tap ∧
      C.size + t ≤ C0.size ∧ notCount C ≤ notCount C0 := by
  intro t
  induction t with
  | zero =>
    intro _
    have hempty : dropSet drop 0 = ∅ := by
      ext w
      simp [dropSet]
    rw [hempty]
    exact ⟨C0, tap0, hGood0, by omega, le_refl _⟩
  | succ t ih =>
    intro ht
    have ht_lt : t < d := Nat.lt_of_succ_le ht
    obtain ⟨Ct, tapt, hGoodt, hsz_t, hnot_t⟩ := ih (Nat.le_of_lt ht_lt)
    let j : Fin d := ⟨t, ht_lt⟩
    obtain ⟨v, huv, hv_ne⟩ := hdrop j
    have huT : drop j ∉ dropSet drop t := by
      intro hmem
      rcases Finset.mem_image.mp hmem with ⟨h, hh, heq⟩
      have hh_lt : h.val < t := (Finset.mem_filter.mp hh).2
      have hhj : h = j := drop.injective heq
      rw [hhj] at hh_lt
      exact Nat.lt_irrefl t hh_lt
    have hvT : v ∉ dropSet drop t := by
      intro hmem
      rcases Finset.mem_image.mp hmem with ⟨h, hh, heq⟩
      have hh_lt : h.val < t := (Finset.mem_filter.mp hh).2
      exact hv_ne h hh_lt heq
    obtain ⟨Ct1, tapt1, hGoodt1, hsz_step, hnot_step⟩ :=
      dropStep n G H hG (dropSet drop t) Ct tapt hGoodt (drop j) v huT hvT huv
    have hins : insert (drop j) (dropSet drop t) = dropSet drop (t + 1) := by
      ext w
      simp only [Finset.mem_insert, dropSet, Finset.mem_image, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · rintro (rfl | ⟨h, hh, rfl⟩)
        · exact ⟨j, Nat.lt_succ_self t, rfl⟩
        · exact ⟨h, Nat.lt_succ_of_lt hh, rfl⟩
      · rintro ⟨h, hh, rfl⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hh with hlt | heq
        · right; exact ⟨h, hlt, rfl⟩
        · left
          have hhj : h = j := Fin.ext heq
          rw [hhj]
    rw [hins] at hGoodt1
    exact ⟨Ct1, tapt1, hGoodt1, by omega, le_trans hnot_step hnot_t⟩

noncomputable def inMap {n m : Nat} (keep : Fin m ↪ Fin n) (w : Nat) : Nat :=
  letI := Classical.propDecidable
  if w < n then
    if h : ∃ i : Fin m, (keep i).val = w then (Classical.choose h).val else m + 1
  else if w = n then m
  else if w = n + 1 then m + 1
  else m + 2 + (w - (n + 2))

noncomputable def liftInput {n m : Nat} (keep : Fin m ↪ Fin n) (y : Fin m → Bool) (v : Fin n) : Bool :=
  letI := Classical.propDecidable
  if h : ∃ i : Fin m, keep i = v then y (Classical.choose h) else true

lemma liftInput_keep {n m : Nat} (keep : Fin m ↪ Fin n) (y : Fin m → Bool) (i : Fin m) :
    liftInput keep y (keep i) = y i := by
  classical
  dsimp only [liftInput]
  split_ifs with h
  · rw [keep.injective (Classical.choose_spec h)]
  · exact False.elim (h ⟨i, rfl⟩)

lemma liftInput_not_mem {n m : Nat} (keep : Fin m ↪ Fin n) (y : Fin m → Bool)
    (v : Fin n) (hv : ∀ i : Fin m, keep i ≠ v) :
    liftInput keep y v = true := by
  classical
  dsimp only [liftInput]
  split_ifs with h
  · rcases h with ⟨i, hi⟩
    exact False.elim (hv i hi)
  · rfl

lemma inMap_lt {n m : Nat} (keep : Fin m ↪ Fin n) (j w : Nat) (hw : w < n + 2 + j) :
    inMap keep w < m + 2 + j := by
  classical
  dsimp only [inMap]
  split_ifs with h1 h2 h3 h4
  · have := (Classical.choose h2).isLt
    omega
  · omega
  · omega
  · omega
  · omega

lemma converse_part
    (n : Nat) (G H : Finset (Fin n × Fin n)) (hG : ∀ e ∈ G, e.1 < e.2) (hHG : H ⊆ G)
    (m d : Nat) (keep : Fin m ↪ Fin n) (drop : Fin d ↪ Fin n)
    (hkeep_act : ∀ i, keep i ∈ H.image Prod.fst ∪ H.image Prod.snd)
    (hkeep_ind : ∀ i j, ¬ ((keep i, keep j) ∈ G ∨ (keep j, keep i) ∈ G))
    (hkeep_disj : ∀ i j, keep i ≠ drop j)
    (hdrop : ∀ j : Fin d, ∃ v : Fin n,
      ((drop j, v) ∈ G ∨ (v, drop j) ∈ G) ∧ ∀ h : Fin d, h.val < j.val → drop h ≠ v)
    (s r : Nat)
    (C0 : Circuit)
    (h0_fit : FanInTwo C0) (h0_rb : ReadsBack (n + 2) C0) (h0_out : C0.output < n + 2 + C0.size)
    (tap0 : ↥H → Fin (n + 2 + C0.size))
    (h0_ev : ∀ x : Fin n → Bool,
      (C0.eval (mkInput x) = true ↔ ∀ e ∈ G, x e.1 = true ∨ x e.2 = true) ∧
      ((∀ e ∈ G, x e.1 = true ∨ x e.2 = true) →
        ∀ e : ↥H, (C0.wires (mkInput x)).getD (tap0 e).val false = xor (x e.val.1) (x e.val.2)))
    (h0_sz : C0.size ≤ s) (h0_not : notCount C0 ≤ r) :
    ∃ l : Nat, l + d ≤ s ∧
      ∃ (C : Circuit) (tap : Fin m → Fin (m + 2 + C.size)),
        (FanInTwo C ∧ ReadsBack (m + 2) C ∧ C.output < m + 2 + C.size) ∧
        C.size ≤ l ∧ notCount C ≤ r ∧
        ∀ y : Fin m → Bool,
          ((Finset.univ : Finset (Fin m)).filter (fun i => y i = false)).card ≤ m →
          ∀ i, (C.wires (mkInput y)).getD (tap i).val false = !y i := by
  classical
  let C_clean := cleanNot C0
  let tap_clean : ↥H → Fin (n + 2 + C_clean.size) := fun e =>
    ⟨(tap0 e).val, by rw [cleanNot_size]; exact (tap0 e).isLt⟩
  have hGood0 : GoodCircuit n G H ∅ C_clean tap_clean := by
    refine ⟨cleanNot_fanInTwo C0 h0_fit, cleanNot_readsBack (n + 2) C0 h0_rb,
      by rw [cleanNot_size]; exact h0_out, cleanNot_prop C0, ?_⟩
    intro x
    rw [ext_empty]
    have hweq : C_clean.wires (mkInput x) = C0.wires (mkInput x) := cleanNot_wires C0 (mkInput x)
    have heeq : C_clean.eval (mkInput x) = C0.eval (mkInput x) := by
      dsimp only [Circuit.eval, C_clean]
      rw [cleanNot_wires C0 (mkInput x)]
      rfl
    rw [heeq]
    refine ⟨(h0_ev x).1, ?_⟩
    intro hcov e
    rw [hweq]
    exact (h0_ev x).2 hcov e
  obtain ⟨Cd, tapd, hGoodd, hsz_d, hnot_d⟩ :=
    dropIter n G H hG d drop hdrop C_clean tap_clean hGood0 d (le_refl d)
  rw [cleanNot_size] at hsz_d
  rw [cleanNot_notCount] at hnot_d
  obtain ⟨hd_fit, hd_rb, hd_out, _, hd_ev⟩ := hGoodd
  let imap : Nat → Nat := inMap keep
  let fm : Gate → Gate := fun g => ⟨g.op, g.inputs.map imap⟩
  let C_inv : Circuit := ⟨Cd.gates.map fm, imap Cd.output⟩
  have hsz_inv : C_inv.size = Cd.size := by simp [C_inv, Circuit.size]
  have hnot_inv : notCount C_inv ≤ r := by
    have h1 : notCount C_inv = notCount Cd :=
      notCount_map_same_op Cd.gates fm (fun _ => rfl) (imap Cd.output)
    omega
  have hfit_inv : FanInTwo C_inv := by
    intro g hg
    rcases List.mem_map.mp hg with ⟨g0, hg0, rfl⟩
    obtain ⟨hop, hlen⟩ := hd_fit g0 hg0
    exact ⟨hop, by simpa [fm] using hlen⟩
  have hrb_inv : ReadsBack (m + 2) C_inv := by
    intro j hj i hi
    rw [gateAt_eq_getElem _ _ hj] at hi
    have hj' : j < Cd.gates.length := by simpa [C_inv] using hj
    simp only [C_inv, List.getElem_map, fm] at hi
    rcases List.mem_map.mp hi with ⟨i0, hi0, rfl⟩
    have hi0_lt : i0 < n + 2 + j := hd_rb j hj' i0 (by rwa [gateAt_eq_getElem _ _ hj'])
    exact inMap_lt keep j i0 hi0_lt
  have hout_inv : C_inv.output < m + 2 + C_inv.size := by
    rw [hsz_inv]
    exact inMap_lt keep Cd.size Cd.output hd_out
  have hedge_ex : ∀ i : Fin m, ∃ e : ↥H, e.val.1 = keep i ∨ e.val.2 = keep i := by
    intro i
    rcases Finset.mem_union.mp (hkeep_act i) with h1 | h2
    · rcases Finset.mem_image.mp h1 with ⟨e, he, heq⟩
      exact ⟨⟨e, he⟩, Or.inl heq⟩
    · rcases Finset.mem_image.mp h2 with ⟨e, he, heq⟩
      exact ⟨⟨e, he⟩, Or.inr heq⟩
  let edgeOf : Fin m → ↥H := fun i => Classical.choose (hedge_ex i)
  let tap_inv : Fin m → Fin (m + 2 + C_inv.size) := fun i =>
    ⟨imap (tapd (edgeOf i)).val, by
      rw [hsz_inv]
      exact inMap_lt keep Cd.size _ (tapd (edgeOf i)).isLt⟩
  refine ⟨Cd.size, by omega, C_inv, tap_inv, ⟨hfit_inv, hrb_inv, hout_inv⟩, by omega, hnot_inv, ?_⟩
  intro y _ i
  let xy : Fin n → Bool := liftInput keep y
  have hsim : ∀ w < n + 2 + Cd.size,
      (C_inv.wires (mkInput y)).getD (imap w) false = (Cd.wires (mkInput xy)).getD w false := by
    have hrem := runGates_remap Cd.gates (mkInput y) (mkInput xy) imap
      (by
        intro j _
        rw [mkInput_length, mkInput_length]
        dsimp only [imap, inMap]
        have h1 : ¬ (n + 2 + j < n) := by omega
        have h2 : ¬ (n + 2 + j = n) := by omega
        have h3 : ¬ (n + 2 + j = n + 1) := by omega
        simp [h1, h2, h3])
      (by
        intro j hj i0 hi0
        rw [mkInput_length]
        exact hd_rb j hj i0 (by rwa [gateAt_eq_getElem _ _ hj]))
      (by
        intro w hw
        rw [mkInput_length] at hw
        by_cases hwn : w < n
        · by_cases hex : ∃ k : Fin m, (keep k).val = w
          · have him : imap w = (Classical.choose hex).val := by
              dsimp only [imap, inMap]
              simp [hwn, hex]
            rw [him]
            have hk_lt : (Classical.choose hex).val < m := (Classical.choose hex).isLt
            refine ⟨by rw [mkInput_length]; omega, ?_⟩
            rw [mkInput_getD_lt y _ hk_lt, mkInput_getD_lt xy w hwn]
            have hkeep_eq : keep (Classical.choose hex) = ⟨w, hwn⟩ :=
              Fin.ext (Classical.choose_spec hex)
            rw [← hkeep_eq]
            exact (liftInput_keep keep y (Classical.choose hex)).symm
          · have him : imap w = m + 1 := by
              dsimp only [imap, inMap]
              simp [hwn, hex]
            rw [him]
            refine ⟨by rw [mkInput_length]; omega, ?_⟩
            rw [mkInput_getD_true y, mkInput_getD_lt xy w hwn]
            have hno : ∀ k : Fin m, keep k ≠ ⟨w, hwn⟩ := fun k hk =>
              hex ⟨k, congrArg Fin.val hk⟩
            exact (liftInput_not_mem keep y ⟨w, hwn⟩ hno).symm
        · by_cases hwn0 : w = n
          · rw [hwn0]
            have him : imap n = m := by simp [imap, inMap]
            rw [him]
            refine ⟨by rw [mkInput_length]; omega, ?_⟩
            rw [mkInput_getD_false y, mkInput_getD_false xy]
          · have hwn1 : w = n + 1 := by omega
            rw [hwn1]
            have him : imap (n + 1) = m + 1 := by simp [imap, inMap]
            rw [him]
            refine ⟨by rw [mkInput_length]; omega, ?_⟩
            rw [mkInput_getD_true y, mkInput_getD_true xy])
      Cd.gates.length (le_refl _)
    intro w hw
    have hres := (hrem w (by rw [mkInput_length]; exact hw)).2
    rw [List.take_length] at hres
    exact hres
  have hext_xy : ext (dropSet drop d) xy = xy := by
    funext v
    by_cases hv : v ∈ dropSet drop d
    · rcases Finset.mem_image.mp hv with ⟨h, _, rfl⟩
      have hno : ∀ k : Fin m, keep k ≠ drop h := fun k => hkeep_disj k h
      simp [ext, hv, xy, liftInput_not_mem keep y (drop h) hno]
    · simp [ext, hv]
  have hcov_xy : ∀ e ∈ G, ext (dropSet drop d) xy e.1 = true ∨ ext (dropSet drop d) xy e.2 = true := by
    rw [hext_xy]
    intro e he
    by_cases h1 : ∃ k1 : Fin m, keep k1 = e.1
    · by_cases h2 : ∃ k2 : Fin m, keep k2 = e.2
      · rcases h1 with ⟨k1, hk1⟩
        rcases h2 with ⟨k2, hk2⟩
        have hadj : (keep k1, keep k2) ∈ G := by
          rw [hk1, hk2]
          exact he
        exact False.elim (hkeep_ind k1 k2 (Or.inl hadj))
      · right
        exact liftInput_not_mem keep y e.2 (fun k hk => h2 ⟨k, hk⟩)
    · left
      exact liftInput_not_mem keep y e.1 (fun k hk => h1 ⟨k, hk⟩)
  have h1 := hsim (tapd (edgeOf i)).val (tapd (edgeOf i)).isLt
  have h2 := (hd_ev xy).2 hcov_xy (edgeOf i)
  dsimp only [tap_inv]
  rw [h1, h2, hext_xy]
  have heG : (edgeOf i).val ∈ G := hHG (edgeOf i).property
  have hspec : (edgeOf i).val.1 = keep i ∨ (edgeOf i).val.2 = keep i :=
    Classical.choose_spec (hedge_ex i)
  rcases hspec with hfst | hsnd
  · have hother : ∀ k : Fin m, keep k ≠ (edgeOf i).val.2 := by
      intro k hk
      have hadj : (keep i, keep k) ∈ G := by
        rw [← hfst, hk]
        exact heG
      exact hkeep_ind i k (Or.inl hadj)
    rw [hfst]
    dsimp only [xy]
    rw [liftInput_keep, liftInput_not_mem keep y (edgeOf i).val.2 hother]
    cases y i <;> rfl
  · have hother : ∀ k : Fin m, keep k ≠ (edgeOf i).val.1 := by
      intro k hk
      have hadj : (keep k, keep i) ∈ G := by
        rw [hk, ← hsnd]
        exact heG
      exact hkeep_ind k i (Or.inl hadj)
    rw [hsnd]
    dsimp only [xy]
    rw [liftInput_keep, liftInput_not_mem keep y (edgeOf i).val.1 hother]
    cases y i <;> rfl

end PEqualNP.Outside.L_lib_1186

theorem PEqualNP.Outside.L_lib_1186 : (∀ (n : Nat) (G H : Finset (Fin n × Fin n)), (∀ e ∈ G, e.1 < e.2) → H ⊆ G →
  let V := Fin n
  let active := H.image Prod.fst ∪ H.image Prod.snd
  let adj := fun (u v : V) => (u,v) ∈ G ∨ (v,u) ∈ G
  let cover := fun (x : V → Bool) => ∀ e ∈ G, x e.1 = true ∨ x e.2 = true
  let shape := fun (m : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
    PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (m + 2) C ∧ C.output < m + 2 + C.size
  let invert := fun (m a s r : Nat) =>
    ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin m → Fin (m + 2 + C.size)),
      shape m C ∧ C.size ≤ s ∧ PEqualNP.NotBracket.notCount C ≤ r ∧
      ∀ x : Fin m → Bool, ((Finset.univ : Finset (Fin m)).filter (fun i => x i = false)).card ≤ a →
        ∀ i, (C.wires (List.ofFn x ++ [false,true])).getD (tap i).val false = !x i
  let marked := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
    shape n C ∧ ∃ tap : ↥H → Fin (n + 2 + C.size), ∀ x : V → Bool,
      let wires := List.ofFn x ++ [false,true]
      (C.eval wires = true ↔ cover x) ∧
      (cover x → ∀ e, (C.wires wires).getD (tap e).val false = xor (x e.val.1) (x e.val.2))
  let fits := fun (s r : Nat) => ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    marked C ∧ C.size ≤ s ∧ PEqualNP.NotBracket.notCount C ≤ r
  (∀ (a s l p q : Nat),
    (∀ I : Finset V, I ⊆ active → (∀ e ∈ G, ¬ (e.1 ∈ I ∧ e.2 ∈ I)) → I.card ≤ a) →
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit, shape n C ∧ C.size ≤ s ∧
      PEqualNP.NotBracket.notCount C ≤ p ∧
      ∀ x, C.eval (List.ofFn x ++ [false,true]) = true ↔ cover x) →
    invert active.card a l q → fits (s + l + H.card) (p + q)) ∧
  (∀ (m d : Nat) (keep : Fin m ↪ V) (drop : Fin d ↪ V),
    (∀ i, keep i ∈ active) → (∀ i j, ¬ adj (keep i) (keep j)) →
    (∀ i j, keep i ≠ drop j) →
    (∀ j : Fin d, ∃ v : V, adj (drop j) v ∧ ∀ h : Fin d, h.val < j.val → drop h ≠ v) →
    ∀ s r : Nat, fits s r → ∃ l : Nat, l + d ≤ s ∧ invert m m l r)) := by
  intro n G H hG hHG
  refine ⟨?_, ?_⟩
  · intro a s l p q hInd hDec hInv
    rcases hDec with ⟨C_dec, ⟨hdec_fit, hdec_rb, hdec_out⟩, hdec_sz, hdec_not, hdec_ev⟩
    rcases hInv with ⟨C_inv, tap_inv, ⟨hinv_fit, hinv_rb, _⟩, hinv_sz, hinv_not, hinv_ev⟩
    rcases PEqualNP.Outside.L_lib_1186.forward_part n G H hG hHG a s l p q hInd
      C_dec hdec_fit hdec_rb hdec_out hdec_sz hdec_not hdec_ev
      C_inv tap_inv hinv_fit hinv_rb hinv_sz hinv_not hinv_ev with
      ⟨C, hsh, htap, hsz, hnot⟩
    exact ⟨C, ⟨hsh, htap⟩, hsz, hnot⟩
  · intro m d keep drop hkeep_act hkeep_ind hkeep_disj hdrop s r hFits
    rcases hFits with ⟨C0, ⟨⟨h0_fit, h0_rb, h0_out⟩, ⟨tap0, h0_ev⟩⟩, h0_sz, h0_not⟩
    exact PEqualNP.Outside.L_lib_1186.converse_part n G H hG hHG m d keep drop
      hkeep_act hkeep_ind hkeep_disj hdrop s r C0 h0_fit h0_rb h0_out tap0 h0_ev h0_sz h0_not

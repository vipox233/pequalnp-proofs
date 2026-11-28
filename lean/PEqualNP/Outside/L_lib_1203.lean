import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1203_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.NotBracket

private def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def wiresOf (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl stepWire x

private lemma wiresOf_length (gs : List Gate) (x : List Bool) :
    (wiresOf gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [wiresOf]
  | cons g gs ih =>
    simp only [wiresOf, List.foldl_cons] at ih ⊢
    rw [ih]
    simp [stepWire]
    omega

private lemma wiresOf_append (gs1 gs2 : List Gate) (x : List Bool) :
    wiresOf (gs1 ++ gs2) x = wiresOf gs2 (wiresOf gs1 x) := by
  simp [wiresOf, List.foldl_append]

private lemma wiresOf_prefix (gs : List Gate) (x : List Bool) :
    ∃ t : List Bool, wiresOf gs x = x ++ t := by
  induction gs generalizing x with
  | nil => exact ⟨[], by simp [wiresOf]⟩
  | cons g gs ih =>
    obtain ⟨t, ht⟩ := ih (stepWire x g)
    refine ⟨[g.op.eval (g.inputs.map fun i => x.getD i false)] ++ t, ?_⟩
    simp only [wiresOf, List.foldl_cons] at ht ⊢
    rw [ht]
    simp [stepWire, List.append_assoc]

private lemma wiresOf_getD_lt (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (wiresOf gs x).getD w false = x.getD w false := by
  obtain ⟨t, ht⟩ := wiresOf_prefix gs x
  rw [ht, List.getD_append _ _ _ _ hw]

private lemma wiresOf_getD_gate (gs : List Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length) :
    (wiresOf gs x).getD (x.length + j) false =
      (gs[j]'hj).op.eval ((gs[j]'hj).inputs.map fun i => (wiresOf (gs.take j) x).getD i false) := by
  have hsplit : gs = gs.take j ++ (gs[j]'hj) :: gs.drop (j + 1) := by
    have := (List.take_append_drop j gs).symm
    rw [List.drop_eq_getElem_cons hj] at this
    exact this
  conv_lhs => rw [hsplit, wiresOf_append]
  change (wiresOf (gs.drop (j + 1)) (stepWire (wiresOf (gs.take j) x) (gs[j]'hj))).getD (x.length + j) false = _
  have hlen : (wiresOf (gs.take j) x).length = x.length + j := by
    rw [wiresOf_length, List.length_take]
    omega
  rw [wiresOf_getD_lt (gs.drop (j + 1)) (stepWire (wiresOf (gs.take j) x) (gs[j]'hj)) (x.length + j)
    (by simp [stepWire, hlen])]
  simp [stepWire, hlen]

private lemma wiresOf_getD_gate_rb (gs : List Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length)
    (hrb : ∀ i ∈ (gs[j]'hj).inputs, i < x.length + j) :
    (wiresOf gs x).getD (x.length + j) false =
      (gs[j]'hj).op.eval ((gs[j]'hj).inputs.map fun i => (wiresOf gs x).getD i false) := by
  rw [wiresOf_getD_gate gs x j hj]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hilt : i < x.length + j := hrb i hi
  have hsplit : gs = gs.take j ++ gs.drop j := (List.take_append_drop j gs).symm
  have hlen : (wiresOf (gs.take j) x).length = x.length + j := by
    rw [wiresOf_length, List.length_take]
    omega
  conv_rhs => rw [hsplit, wiresOf_append]
  rw [wiresOf_getD_lt (gs.drop j) (wiresOf (gs.take j) x) i (by omega)]

private lemma gateAt_eq_getElem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j]'hj := by
  unfold gateAt
  simp [List.getD_eq_getElem?_getD, hj]

private lemma circuit_wires_getD_lt (C : Circuit) (raw : List Bool) (w : ℕ) (hw : w < raw.length) :
    (C.wires raw).getD w false = raw.getD w false := by
  unfold Circuit.wires
  exact wiresOf_getD_lt C.gates raw w hw

private lemma circuit_wires_getD_gate (C : Circuit) (raw : List Bool)
    (hrb : ReadsBack raw.length C) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires raw).getD (raw.length + j) false =
      (C.gates[j]'hj).op.eval ((C.gates[j]'hj).inputs.map fun i => (C.wires raw).getD i false) := by
  unfold Circuit.wires
  refine wiresOf_getD_gate_rb C.gates raw j hj ?_
  intro i hi
  have := hrb j hj i
  rw [gateAt_eq_getElem C j hj] at this
  exact this hi

private def isNotGate (g : Gate) : Bool :=
  match g.op with
  | .not => true
  | _ => false

private lemma notCount_eq_filter_isNotGate (C : Circuit) :
    notCount C = (C.gates.filter isNotGate).length := by
  unfold notCount
  congr 1
  apply List.filter_congr
  intro g _
  cases h : g.op <;> simp [isNotGate, h]

private lemma notCount_le_size (C : Circuit) : notCount C ≤ C.size := by
  rw [notCount_eq_filter_isNotGate]
  exact List.length_filter_le isNotGate C.gates

private lemma filter_isNotGate_map (gs : List Gate) (f : ℕ → ℕ) :
    ((gs.map fun g => (⟨g.op, g.inputs.map f⟩ : Gate)).filter isNotGate).length =
      (gs.filter isNotGate).length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    simp only [List.map_cons, List.filter_cons]
    have heq : isNotGate ⟨g.op, g.inputs.map f⟩ = isNotGate g := by
      unfold isNotGate; rfl
    rw [heq]
    cases isNotGate g <;> simp [ih]

private def rawVec {n d : ℕ} (x : Fin n → Bool) (u : Fin d → Bool) : List Bool :=
  List.ofFn x ++ List.ofFn u ++ [false, true]

private lemma rawVec_length {n d : ℕ} (x : Fin n → Bool) (u : Fin d → Bool) :
    (rawVec x u).length = n + d + 2 := by
  simp [rawVec]; omega

private lemma rawVec_getD_x {n d : ℕ} (x : Fin n → Bool) (u : Fin d → Bool) (i : ℕ) (hi : i < n) :
    (rawVec x u).getD i false = x ⟨i, hi⟩ := by
  unfold rawVec
  rw [List.append_assoc, List.getD_append _ _ _ _ (by simp [hi])]
  simp [hi]

private lemma rawVec_getD_u {n d : ℕ} (x : Fin n → Bool) (u : Fin d → Bool) (k : ℕ) (hk : k < d) :
    (rawVec x u).getD (n + k) false = u ⟨k, hk⟩ := by
  unfold rawVec
  rw [List.append_assoc, List.getD_append_right _ _ _ _ (by simp)]
  simp only [List.length_ofFn, Nat.add_sub_cancel_left]
  rw [List.getD_append _ _ _ _ (by simp [hk])]
  simp [hk]

private lemma rawVec_getD_false {n d : ℕ} (x : Fin n → Bool) (u : Fin d → Bool) :
    (rawVec x u).getD (n + d) false = false := by
  unfold rawVec
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

private lemma rawVec_getD_true {n d : ℕ} (x : Fin n → Bool) (u : Fin d → Bool) :
    (rawVec x u).getD (n + d + 1) false = true := by
  unfold rawVec
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

private def upWire (n : ℕ) (w : ℕ) : ℕ :=
  if w < n then w
  else if w = n then n + 4
  else if w = n + 1 then n + 2
  else if w = n + 2 then n + 3
  else w + 2

private lemma upWire_lt_gate (n j w : ℕ) (hw : w < n + 3 + j) :
    upWire n w < n + 4 + (j + 1) := by
  unfold upWire
  split_ifs <;> omega

private lemma upWire_lt_total (n sz w : ℕ) (hw : w < n + 1 + 2 + sz) :
    upWire n w < n + 2 + 2 + (sz + 1) := by
  unfold upWire
  split_ifs <;> omega

private lemma backward_dir {n m : ℕ} {D : (Fin n → Bool) → Bool → Bool}
    {R : (Fin n → Bool) → Bool → (Fin m → Bool) → Prop}
    (useAnd : Bool) (s b r : ℕ)
    (hs1 : 1 ≤ s) (hb1 : 1 ≤ b)
    (C : Circuit) (tap : Fin m → Fin (n + 1 + 2 + C.size))
    (hfan : FanInTwo C) (hrb : ReadsBack (n + 1 + 2) C)
    (hout : C.output < n + 1 + 2 + C.size)
    (hsz : C.size ≤ s - 1) (hb : C.size - notCount C ≤ b - 1) (hr : notCount C ≤ r)
    (hsem : ∀ (x : Fin n → Bool) (u : Fin 1 → Bool),
      C.eval (rawVec x u) = D x (u 0) ∧
      R x (u 0) (fun j => (C.wires (rawVec x u)).getD (tap j).val false)) :
    ∃ (C2 : Circuit) (tap2 : Fin m → Fin (n + 2 + 2 + C2.size)),
      FanInTwo C2 ∧ ReadsBack (n + 2 + 2) C2 ∧ C2.output < n + 2 + 2 + C2.size ∧
      C2.size ≤ s ∧ C2.size - notCount C2 ≤ b ∧ notCount C2 ≤ r ∧
      ∀ (x : Fin n → Bool) (u : Fin 2 → Bool),
        C2.eval (rawVec x u) = D x (if useAnd then u 0 && u 1 else u 0 || u 1) ∧
        R x (if useAnd then u 0 && u 1 else u 0 || u 1)
          (fun j => (C2.wires (rawVec x u)).getD (tap2 j).val false) := by
  let g0 : Gate := ⟨if useAnd then .and else .or, [n, n + 1]⟩
  let C2 : Circuit :=
    ⟨g0 :: C.gates.map (fun g => ⟨g.op, g.inputs.map (upWire n)⟩), upWire n C.output⟩
  have hC2size : C2.size = C.size + 1 := by
    simp [C2, Circuit.size]
  let tap2 : Fin m → Fin (n + 2 + 2 + C2.size) := fun j =>
    ⟨upWire n (tap j).val, by rw [hC2size]; exact upWire_lt_total n C.size (tap j).val (tap j).isLt⟩
  have hfan2 : FanInTwo C2 := by
    intro g hg
    simp only [C2, List.mem_cons, List.mem_map] at hg
    rcases hg with rfl | ⟨g', hg', rfl⟩
    · cases useAnd <;> simp [g0]
    · obtain ⟨hop, hlen⟩ := hfan g' hg'
      exact ⟨hop, by simpa using hlen⟩
  have hrb2 : ReadsBack (n + 2 + 2) C2 := by
    intro j hj i hi
    rw [gateAt_eq_getElem C2 j hj] at hi
    cases j with
    | zero =>
      simp only [C2, List.getElem_cons_zero, g0, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
    | succ j' =>
      have hj' : j' < C.gates.length := by simp [C2] at hj; omega
      simp only [C2, List.getElem_cons_succ, List.getElem_map, List.mem_map] at hi
      obtain ⟨i', hi', rfl⟩ := hi
      have h1 : i' < n + 1 + 2 + j' := by
        have := hrb j' hj' i'
        rw [gateAt_eq_getElem C j' hj'] at this
        exact this hi'
      have h2 := upWire_lt_gate n j' i' (by omega)
      omega
  have hnot2 : notCount C2 = notCount C := by
    rw [notCount_eq_filter_isNotGate, notCount_eq_filter_isNotGate]
    simp only [C2, List.filter_cons]
    have hg0not : isNotGate g0 = false := by cases useAnd <;> rfl
    rw [hg0not]
    simpa using filter_isNotGate_map C.gates (upWire n)
  have hout2 : C2.output < n + 2 + 2 + C2.size := by
    rw [hC2size]
    exact upWire_lt_total n C.size C.output hout
  have hnotle : notCount C ≤ C.size := notCount_le_size C
  refine ⟨C2, tap2, hfan2, hrb2, hout2, by omega, by rw [hC2size, hnot2]; omega, by rw [hnot2]; exact hr, ?_⟩
  intro x u
  let mergeVal : Bool := if useAnd then u 0 && u 1 else u 0 || u 1
  let u1 : Fin 1 → Bool := fun _ => mergeVal
  have hagree : ∀ w < n + 1 + 2 + C.size,
      (C2.wires (rawVec x u)).getD (upWire n w) false =
        (C.wires (rawVec x u1)).getD w false := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw
      by_cases h1 : w < n
      · have huw : upWire n w = w := by unfold upWire; simp [h1]
        rw [huw]
        rw [circuit_wires_getD_lt C2 (rawVec x u) w (by rw [rawVec_length]; omega)]
        rw [circuit_wires_getD_lt C (rawVec x u1) w (by rw [rawVec_length]; omega)]
        rw [rawVec_getD_x x u w h1, rawVec_getD_x x u1 w h1]
      · by_cases h2 : w = n
        · subst w
          have huw : upWire n n = n + 4 := by unfold upWire; simp
          rw [huw]
          have hlen2 : (rawVec x u).length = n + 4 := by rw [rawVec_length]
          have hj0 : 0 < C2.gates.length := by simp [C2]
          have hgate := circuit_wires_getD_gate C2 (rawVec x u) (by rw [hlen2]; exact hrb2) 0 hj0
          rw [hlen2, Nat.add_zero] at hgate
          rw [hgate]
          simp only [C2, List.getElem_cons_zero, g0, List.map_cons, List.map_nil]
          rw [circuit_wires_getD_lt C2 (rawVec x u) n (by rw [rawVec_length]; omega)]
          rw [circuit_wires_getD_lt C2 (rawVec x u) (n + 1) (by rw [rawVec_length]; omega)]
          have hu0 : (rawVec x u).getD n false = u 0 := by
            simpa using rawVec_getD_u x u 0 (by decide)
          have hu1' : (rawVec x u).getD (n + 1) false = u 1 := by
            simpa using rawVec_getD_u x u 1 (by decide)
          rw [hu0, hu1']
          rw [circuit_wires_getD_lt C (rawVec x u1) n (by rw [rawVec_length]; omega)]
          have hv0 : (rawVec x u1).getD n false = u1 0 := by
            simpa using rawVec_getD_u x u1 0 (by decide)
          rw [hv0]
          cases useAnd <;> simp [GateOp.eval, u1, mergeVal]
        · by_cases h3 : w = n + 1
          · subst h3
            have huw : upWire n (n + 1) = n + 2 := by unfold upWire; simp
            rw [huw]
            rw [circuit_wires_getD_lt C2 (rawVec x u) (n + 2) (by rw [rawVec_length]; omega)]
            rw [circuit_wires_getD_lt C (rawVec x u1) (n + 1) (by rw [rawVec_length]; omega)]
            rw [rawVec_getD_false x u, rawVec_getD_false x u1]
          · by_cases h4 : w = n + 2
            · subst h4
              have huw : upWire n (n + 2) = n + 3 := by unfold upWire; simp
              rw [huw]
              rw [circuit_wires_getD_lt C2 (rawVec x u) (n + 3) (by rw [rawVec_length]; omega)]
              rw [circuit_wires_getD_lt C (rawVec x u1) (n + 2) (by rw [rawVec_length]; omega)]
              have hf2 := rawVec_getD_true x u
              have hf1 := rawVec_getD_true x u1
              simpa [Nat.add_assoc] using hf2.trans hf1.symm
            · have hwge : n + 3 ≤ w := by omega
              let k := w - (n + 3)
              have hwk : w = n + 3 + k := by omega
              have hklt : k < C.gates.length := by
                change k < C.size
                omega
              have huw : upWire n w = n + 4 + (k + 1) := by
                unfold upWire; split_ifs <;> omega
              rw [huw]
              have hlen2 : (rawVec x u).length = n + 4 := by rw [rawVec_length]
              have hlen1 : (rawVec x u1).length = n + 3 := by rw [rawVec_length]
              have hk1lt : k + 1 < C2.gates.length := by simp [C2]; omega
              have hg2 := circuit_wires_getD_gate C2 (rawVec x u) (by rw [hlen2]; exact hrb2) (k + 1) hk1lt
              rw [hlen2] at hg2
              have hg1 := circuit_wires_getD_gate C (rawVec x u1) (by rw [hlen1]; exact hrb) k hklt
              rw [hlen1, ← hwk] at hg1
              rw [hg2, hg1]
              simp only [C2, List.getElem_cons_succ, List.getElem_map, List.map_map]
              congr 1
              apply List.map_congr_left
              intro i hi
              have hilt : i < n + 3 + k := by
                have := hrb k hklt i
                rw [gateAt_eq_getElem C k hklt] at this
                exact this hi
              exact ih i (by omega) (by omega)
  have hsem1 := hsem x u1
  constructor
  · unfold Circuit.eval
    change (C2.wires (rawVec x u)).getD (upWire n C.output) false = D x mergeVal
    rw [hagree C.output hout]
    exact hsem1.1
  · have htap : (fun j => (C2.wires (rawVec x u)).getD (tap2 j).val false) =
        (fun j => (C.wires (rawVec x u1)).getD (tap j).val false) := by
      funext j
      exact hagree (tap j).val (tap j).isLt
    rw [htap]
    exact hsem1.2

private def lit1 (n : ℕ) (C : Circuit) (w : ℕ) : Option Bool :=
  if w = n + 1 then some true
  else if hw : n + 4 ≤ w then
    let j := w - (n + 4)
    if hj : j < C.gates.length then
      match (C.gates[j]'hj).op, (C.gates[j]'hj).inputs with
      | .not, i :: _ =>
        if hi : i < w then
          (lit1 n C i).map Bool.not
        else none
      | _, _ => none
    else none
  else none
termination_by w

private lemma lit1_eq_some_eval {n : ℕ} (C : Circuit) (hrb : ReadsBack (n + 2 + 2) C)
    (w : ℕ) (hw : w < n + 2 + 2 + C.size) (pol : Bool) (hlit : lit1 n C w = some pol) :
    ∀ (x : Fin n → Bool) (u : Fin 2 → Bool),
      (C.wires (rawVec x u)).getD w false = if pol then u 1 else !(u 1) := by
  induction w using Nat.strong_induction_on generalizing pol with
  | ind w ih =>
    intro x u
    rw [lit1] at hlit
    by_cases h1 : w = n + 1
    · rw [if_pos h1] at hlit
      have hpol : pol = true := by simpa using hlit.symm
      subst h1; subst hpol
      rw [circuit_wires_getD_lt C (rawVec x u) (n + 1) (by rw [rawVec_length]; omega)]
      simpa using rawVec_getD_u x u 1 (by decide)
    · rw [if_neg h1] at hlit
      by_cases h2 : n + 4 ≤ w
      · rw [dif_pos h2] at hlit
        have hjl : w - (n + 4) < C.gates.length := by change w - (n + 4) < C.size; omega
        rw [dif_pos hjl] at hlit
        cases hop : (C.gates[w - (n + 4)]'hjl).op <;> rw [hop] at hlit
        · simp at hlit
        · simp at hlit
        · cases hinp : (C.gates[w - (n + 4)]'hjl).inputs with
          | nil => rw [hinp] at hlit; simp at hlit
          | cons i rest =>
            rw [hinp] at hlit
            have hiw : i < w := by
              have := hrb (w - (n + 4)) hjl i
              rw [gateAt_eq_getElem C (w - (n + 4)) hjl, hinp] at this
              have := this List.mem_cons_self
              omega
            simp only [hiw, ↓reduceDIte] at hlit
            cases hli : lit1 n C i with
            | none => rw [hli] at hlit; simp at hlit
            | some pol0 =>
              rw [hli] at hlit
              have hpol : (!pol0) = pol := by cases pol0 <;> cases pol <;> simp at hlit ⊢
              have hlen : (rawVec x u).length = n + 4 := by rw [rawVec_length]
              have hgw := circuit_wires_getD_gate C (rawVec x u) (by rw [hlen]; exact hrb) (w - (n + 4)) hjl
              have hwj : n + 4 + (w - (n + 4)) = w := by omega
              rw [hlen, hwj] at hgw
              rw [hgw, hop, hinp]
              simp only [GateOp.eval, List.map_cons, List.headD_cons]
              rw [ih i hiw (by omega) pol0 hli x u, ← hpol]
              cases pol0 <;> simp
        · simp at hlit
        · simp at hlit
      · rw [dif_neg h2] at hlit; simp at hlit

private lemma lit1_not_gate_eq {n : ℕ} (C : Circuit) (hrb : ReadsBack (n + 2 + 2) C)
    (j : ℕ) (hj : j < C.gates.length) (hop : (C.gates[j]'hj).op = .not)
    (i : ℕ) (rest : List ℕ) (hinp : (C.gates[j]'hj).inputs = i :: rest) :
    lit1 n C (n + 4 + j) = (lit1 n C i).map Bool.not := by
  rw [lit1]
  have h1 : n + 4 + j ≠ n + 1 := by omega
  have h2 : n + 4 ≤ n + 4 + j := by omega
  rw [if_neg h1, dif_pos h2]
  have hsub : n + 4 + j - (n + 4) = j := by omega
  have hj' : n + 4 + j - (n + 4) < C.gates.length := by omega
  rw [dif_pos hj']
  have heq : C.gates[n + 4 + j - (n + 4)]'hj' = C.gates[j]'hj := by congr 1
  have hiw : i < n + 4 + j := by
    have := hrb j hj i
    rw [gateAt_eq_getElem C j hj, hinp] at this
    exact this List.mem_cons_self
  simp only [heq, hop, hinp, hiw, ↓reduceDIte]

private lemma exists_nonnot_reading_lit1 {n : ℕ} {D : (Fin n → Bool) → Bool → Bool}
    (useAnd : Bool)
    (x0 : Fin n → Bool) (hdiff : D x0 false ≠ D x0 true)
    (C : Circuit) (hfan : FanInTwo C) (hrb : ReadsBack (n + 2 + 2) C)
    (hout : C.output < n + 2 + 2 + C.size)
    (heval : ∀ (x : Fin n → Bool) (u : Fin 2 → Bool),
      C.eval (rawVec x u) = D x (if useAnd then u 0 && u 1 else u 0 || u 1)) :
    ∃ (k : ℕ) (hk : k < C.gates.length) (i0 : ℕ) (pol : Bool),
      ((C.gates[k]'hk).op = .and ∨ (C.gates[k]'hk).op = .or) ∧
      i0 ∈ (C.gates[k]'hk).inputs ∧
      lit1 n C i0 = some pol := by
  let neu : Bool := useAnd
  have hmerge_neu : ∀ a : Bool,
      (if useAnd then neu && a else neu || a) = a := by
    intro a; cases useAnd <;> simp [neu]
  have hmerge_abs : ∀ a : Bool,
      (if useAnd then (!neu) && a else (!neu) || a) = !neu := by
    intro a; cases useAnd <;> simp [neu]
  let uAbsF : Fin 2 → Bool := fun i => if i = 0 then !neu else false
  let uAbsT : Fin 2 → Bool := fun i => if i = 0 then !neu else true
  have hout_none : lit1 n C C.output = none := by
    cases h : lit1 n C C.output with
    | none => rfl
    | some pol =>
      exfalso
      have hF := lit1_eq_some_eval C hrb C.output hout pol h x0 uAbsF
      have hT := lit1_eq_some_eval C hrb C.output hout pol h x0 uAbsT
      have heF : C.eval (rawVec x0 uAbsF) = D x0 (!neu) := by
        rw [heval x0 uAbsF]; simpa [uAbsF] using congrArg (D x0) (hmerge_abs false)
      have heT : C.eval (rawVec x0 uAbsT) = D x0 (!neu) := by
        rw [heval x0 uAbsT]; simpa [uAbsT] using congrArg (D x0) (hmerge_abs true)
      have hsame : (C.wires (rawVec x0 uAbsF)).getD C.output false =
          (C.wires (rawVec x0 uAbsT)).getD C.output false := heF.trans heT.symm
      rw [hF, hT] at hsame
      cases pol <;> simp [uAbsF, uAbsT] at hsame
  by_contra hnone
  push_neg at hnone
  let uNeuF : Fin 2 → Bool := fun i => if i = 0 then neu else false
  let uNeuT : Fin 2 → Bool := fun i => if i = 0 then neu else true
  have hagree : ∀ w < n + 2 + 2 + C.size, lit1 n C w = none →
      (C.wires (rawVec x0 uNeuF)).getD w false =
        (C.wires (rawVec x0 uNeuT)).getD w false := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw hlit
      by_cases h1 : w < n
      · rw [circuit_wires_getD_lt C (rawVec x0 uNeuF) w (by rw [rawVec_length]; omega)]
        rw [circuit_wires_getD_lt C (rawVec x0 uNeuT) w (by rw [rawVec_length]; omega)]
        rw [rawVec_getD_x x0 uNeuF w h1, rawVec_getD_x x0 uNeuT w h1]
      · by_cases h2 : w = n
        · subst w
          rw [circuit_wires_getD_lt C (rawVec x0 uNeuF) n (by rw [rawVec_length]; omega)]
          rw [circuit_wires_getD_lt C (rawVec x0 uNeuT) n (by rw [rawVec_length]; omega)]
          have a := rawVec_getD_u x0 uNeuF 0 (by decide)
          have b := rawVec_getD_u x0 uNeuT 0 (by decide)
          simpa [uNeuF, uNeuT] using a.trans b.symm
        · by_cases h3 : w = n + 1
          · subst h3
            rw [lit1] at hlit
            simp at hlit
          · by_cases h4 : w = n + 2
            · subst h4
              rw [circuit_wires_getD_lt C (rawVec x0 uNeuF) (n + 2) (by rw [rawVec_length]; omega)]
              rw [circuit_wires_getD_lt C (rawVec x0 uNeuT) (n + 2) (by rw [rawVec_length]; omega)]
              rw [rawVec_getD_false x0 uNeuF, rawVec_getD_false x0 uNeuT]
            · by_cases h5 : w = n + 3
              · subst h5
                rw [circuit_wires_getD_lt C (rawVec x0 uNeuF) (n + 3) (by rw [rawVec_length]; omega)]
                rw [circuit_wires_getD_lt C (rawVec x0 uNeuT) (n + 3) (by rw [rawVec_length]; omega)]
                have a := rawVec_getD_true x0 uNeuF
                have b := rawVec_getD_true x0 uNeuT
                simpa [Nat.add_assoc] using a.trans b.symm
              · let j := w - (n + 4)
                have hwj : w = n + 4 + j := by omega
                have hjlt : j < C.gates.length := by change j < C.size; omega
                have hlenF : (rawVec x0 uNeuF).length = n + 4 := by rw [rawVec_length]
                have hlenT : (rawVec x0 uNeuT).length = n + 4 := by rw [rawVec_length]
                have hgF := circuit_wires_getD_gate C (rawVec x0 uNeuF) (by rw [hlenF]; exact hrb) j hjlt
                have hgT := circuit_wires_getD_gate C (rawVec x0 uNeuT) (by rw [hlenT]; exact hrb) j hjlt
                rw [hlenF, ← hwj] at hgF
                rw [hlenT, ← hwj] at hgT
                rw [hgF, hgT]
                have hgf := (hfan (C.gates[j]'hjlt) (List.getElem_mem hjlt)).1
                simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hgf
                rcases hgf with hop | hop | hop
                · congr 1
                  apply List.map_congr_left
                  intro i hi
                  have hilt : i < w := by
                    have := hrb j hjlt i
                    rw [gateAt_eq_getElem C j hjlt] at this
                    have := this hi; omega
                  have hli : lit1 n C i = none := by
                    cases h : lit1 n C i with
                    | none => rfl
                    | some pol => exact False.elim (hnone j hjlt i pol (Or.inl hop) hi h)
                  exact ih i hilt (by omega) hli
                · congr 1
                  apply List.map_congr_left
                  intro i hi
                  have hilt : i < w := by
                    have := hrb j hjlt i
                    rw [gateAt_eq_getElem C j hjlt] at this
                    have := this hi; omega
                  have hli : lit1 n C i = none := by
                    cases h : lit1 n C i with
                    | none => rfl
                    | some pol => exact False.elim (hnone j hjlt i pol (Or.inr hop) hi h)
                  exact ih i hilt (by omega) hli
                · rw [hop]
                  cases hinp : (C.gates[j]'hjlt).inputs with
                  | nil => simp [GateOp.eval]
                  | cons i rest =>
                    simp only [GateOp.eval, List.map_cons, List.headD_cons]
                    have heq := lit1_not_gate_eq C hrb j hjlt hop i rest hinp
                    rw [← hwj, hlit] at heq
                    have hli : lit1 n C i = none := by
                      cases h : lit1 n C i with
                      | none => rfl
                      | some pol => rw [h] at heq; simp at heq
                    have hilt : i < w := by
                      have := hrb j hjlt i
                      rw [gateAt_eq_getElem C j hjlt, hinp] at this
                      have := this List.mem_cons_self; omega
                    rw [ih i hilt (by omega) hli]
  have hsame := hagree C.output hout hout_none
  have heF : C.eval (rawVec x0 uNeuF) = D x0 false := by
    rw [heval x0 uNeuF]; simpa [uNeuF] using congrArg (D x0) (hmerge_neu false)
  have heT : C.eval (rawVec x0 uNeuT) = D x0 true := by
    rw [heval x0 uNeuT]; simpa [uNeuT] using congrArg (D x0) (hmerge_neu true)
  exact hdiff (heF.symm.trans (hsame.trans heT))

private lemma exists_gate_replacement {n : ℕ} (C : Circuit) (hfan : FanInTwo C)
    (hrb : ReadsBack (n + 2 + 2) C) (neu : Bool)
    (k : ℕ) (hk : k < C.gates.length) (i0 : ℕ) (pol : Bool)
    (hop : (C.gates[k]'hk).op = .and ∨ (C.gates[k]'hk).op = .or)
    (hi0 : i0 ∈ (C.gates[k]'hk).inputs) (hlit : lit1 n C i0 = some pol) :
    ∃ rep < n + 4 + k,
      ∀ (x : Fin n → Bool) (v : Fin 1 → Bool),
        let u : Fin 2 → Bool := fun t => if t = 0 then v 0 else neu
        (C.wires (rawVec x u)).getD (n + 4 + k) false =
          (C.wires (rawVec x u)).getD rep false := by
  have hi0_lt : i0 < n + 4 + k := by
    have := hrb k hk i0
    rw [gateAt_eq_getElem C k hk] at this
    exact this hi0
  let c0 : Bool := if pol then neu else !neu
  have hi0_val : ∀ (x : Fin n → Bool) (v : Fin 1 → Bool),
      let u : Fin 2 → Bool := fun t => if t = 0 then v 0 else neu
      (C.wires (rawVec x u)).getD i0 false = c0 := by
    intro x v u
    have h := lit1_eq_some_eval C hrb i0 (by change i0 < n + 2 + 2 + C.gates.length; omega) pol hlit x u
    simpa [u, c0] using h
  have hlen_in : (C.gates[k]'hk).inputs.length ≤ 2 :=
    (hfan (C.gates[k]'hk) (List.getElem_mem hk)).2
  have hgate_eval : ∀ (x : Fin n → Bool) (v : Fin 1 → Bool),
      let u : Fin 2 → Bool := fun t => if t = 0 then v 0 else neu
      (C.wires (rawVec x u)).getD (n + 4 + k) false =
        (C.gates[k]'hk).op.eval ((C.gates[k]'hk).inputs.map fun i => (C.wires (rawVec x u)).getD i false) := by
    intro x v u
    have hlen : (rawVec x u).length = n + 4 := by rw [rawVec_length]
    have h := circuit_wires_getD_gate C (rawVec x u) (by rw [hlen]; exact hrb) k hk
    rwa [hlen] at h
  cases hinp : (C.gates[k]'hk).inputs with
  | nil => rw [hinp] at hi0; simp at hi0
  | cons a tl =>
    cases tl with
    | nil =>
      rw [hinp] at hi0
      have ha : i0 = a := by simpa using hi0
      subst ha
      cases hc0 : c0
      · refine ⟨n + 2, by omega, ?_⟩
        intro x v u
        rw [hgate_eval x v, hinp]
        have hv := hi0_val x v
        rw [hc0] at hv
        cases hop with
        | inl hand =>
          rw [hand]
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
          rw [hv, circuit_wires_getD_lt C (rawVec x u) (n + 2) (by rw [rawVec_length]; omega)]
          exact (rawVec_getD_false x u).symm
        | inr hor =>
          rw [hor]
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
          rw [hv, circuit_wires_getD_lt C (rawVec x u) (n + 2) (by rw [rawVec_length]; omega)]
          exact (rawVec_getD_false x u).symm
      · refine ⟨n + 3, by omega, ?_⟩
        intro x v u
        rw [hgate_eval x v, hinp]
        have hv := hi0_val x v
        rw [hc0] at hv
        cases hop with
        | inl hand =>
          rw [hand]
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
          rw [hv, circuit_wires_getD_lt C (rawVec x u) (n + 3) (by rw [rawVec_length]; omega)]
          have ht := rawVec_getD_true x u
          simpa [Nat.add_assoc] using ht.symm
        | inr hor =>
          rw [hor]
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
          rw [hv, circuit_wires_getD_lt C (rawVec x u) (n + 3) (by rw [rawVec_length]; omega)]
          have ht := rawVec_getD_true x u
          simpa [Nat.add_assoc] using ht.symm
    | cons b tl2 =>
      cases tl2 with
      | cons c tl3 =>
        rw [hinp] at hlen_in; simp at hlen_in
      | nil =>
        have ha_lt : a < n + 4 + k := by
          have := hrb k hk a
          rw [gateAt_eq_getElem C k hk, hinp] at this
          exact this (by simp)
        have hb_lt : b < n + 4 + k := by
          have := hrb k hk b
          rw [gateAt_eq_getElem C k hk, hinp] at this
          exact this (by simp)
        rw [hinp] at hi0
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi0
        rcases hi0 with rfl | rfl
        · cases hop with
          | inl hand =>
            cases hc0 : c0
            · refine ⟨n + 2, by omega, ?_⟩
              intro x v u
              rw [hgate_eval x v, hand, hinp]
              have hv := hi0_val x v
              rw [hc0] at hv
              simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
              rw [hv, Bool.false_and]
              rw [circuit_wires_getD_lt C (rawVec x u) (n + 2) (by rw [rawVec_length]; omega)]
              exact (rawVec_getD_false x u).symm
            · refine ⟨b, hb_lt, ?_⟩
              intro x v u
              rw [hgate_eval x v, hand, hinp]
              have hv := hi0_val x v
              rw [hc0] at hv
              simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
              rw [hv, Bool.true_and]
          | inr hor =>
            cases hc0 : c0
            · refine ⟨b, hb_lt, ?_⟩
              intro x v u
              rw [hgate_eval x v, hor, hinp]
              have hv := hi0_val x v
              rw [hc0] at hv
              simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
              rw [hv, Bool.false_or]
            · refine ⟨n + 3, by omega, ?_⟩
              intro x v u
              rw [hgate_eval x v, hor, hinp]
              have hv := hi0_val x v
              rw [hc0] at hv
              simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
              rw [hv, Bool.true_or]
              rw [circuit_wires_getD_lt C (rawVec x u) (n + 3) (by rw [rawVec_length]; omega)]
              have ht := rawVec_getD_true x u
              simpa [Nat.add_assoc] using ht.symm
        · cases hop with
          | inl hand =>
            cases hc0 : c0
            · refine ⟨n + 2, by omega, ?_⟩
              intro x v u
              rw [hgate_eval x v, hand, hinp]
              have hv := hi0_val x v
              rw [hc0] at hv
              simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
              rw [hv, Bool.and_false]
              rw [circuit_wires_getD_lt C (rawVec x u) (n + 2) (by rw [rawVec_length]; omega)]
              exact (rawVec_getD_false x u).symm
            · refine ⟨a, ha_lt, ?_⟩
              intro x v u
              rw [hgate_eval x v, hand, hinp]
              have hv := hi0_val x v
              rw [hc0] at hv
              simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
              rw [hv, Bool.and_true]
          | inr hor =>
            cases hc0 : c0
            · refine ⟨a, ha_lt, ?_⟩
              intro x v u
              rw [hgate_eval x v, hor, hinp]
              have hv := hi0_val x v
              rw [hc0] at hv
              simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
              rw [hv, Bool.or_false]
            · refine ⟨n + 3, by omega, ?_⟩
              intro x v u
              rw [hgate_eval x v, hor, hinp]
              have hv := hi0_val x v
              rw [hc0] at hv
              simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
              rw [hv, Bool.or_true]
              rw [circuit_wires_getD_lt C (rawVec x u) (n + 3) (by rw [rawVec_length]; omega)]
              have ht := rawVec_getD_true x u
              simpa [Nat.add_assoc] using ht.symm

private def baseDrop (n k : ℕ) (neu : Bool) (w : ℕ) : ℕ :=
  if w < n then w
  else if w = n then n
  else if w = n + 1 then (if neu then n + 2 else n + 1)
  else if w = n + 2 then n + 1
  else if w = n + 3 then n + 2
  else if w < n + 4 + k then w - 1
  else w - 2

private def dropWire (n k rep : ℕ) (neu : Bool) (w : ℕ) : ℕ :=
  if w = n + 4 + k then baseDrop n k neu rep
  else baseDrop n k neu w

private lemma baseDrop_lt_before (n k j w : ℕ) (neu : Bool)
    (hjk : j ≤ k) (hw : w < n + 4 + j) :
    baseDrop n k neu w < n + 3 + j := by
  unfold baseDrop
  cases neu <;> split_ifs <;> omega

private lemma dropWire_lt_before (n k rep j w : ℕ) (neu : Bool)
    (hjk : j ≤ k) (hw : w < n + 4 + j) :
    dropWire n k rep neu w < n + 3 + j := by
  unfold dropWire
  have hne : w ≠ n + 4 + k := by omega
  rw [if_neg hne]
  exact baseDrop_lt_before n k j w neu hjk hw

private lemma dropWire_lt_after (n k rep j' w : ℕ) (neu : Bool)
    (hrep : rep < n + 4 + k) (hkj : k ≤ j') (hw : w < n + 4 + (j' + 1)) :
    dropWire n k rep neu w < n + 3 + j' := by
  unfold dropWire
  split_ifs with h
  · have := baseDrop_lt_before n k k rep neu le_rfl hrep
    omega
  · unfold baseDrop
    cases neu <;> split_ifs <;> omega

private lemma dropWire_lt_total (n k rep sz w : ℕ) (neu : Bool)
    (hrep : rep < n + 4 + k) (hk : k < sz) (hw : w < n + 2 + 2 + sz) :
    dropWire n k rep neu w < n + 1 + 2 + (sz - 1) := by
  have h1 := dropWire_lt_after n k rep (sz - 1) w neu hrep (by omega) (by omega)
  omega

private lemma forward_dir {n m : ℕ} {D : (Fin n → Bool) → Bool → Bool}
    {R : (Fin n → Bool) → Bool → (Fin m → Bool) → Prop}
    (x0 : Fin n → Bool) (hdiff : D x0 false ≠ D x0 true)
    (useAnd : Bool) (s b r : ℕ)
    (C : Circuit) (tap : Fin m → Fin (n + 2 + 2 + C.size))
    (hfan : FanInTwo C) (hrb : ReadsBack (n + 2 + 2) C)
    (hout : C.output < n + 2 + 2 + C.size)
    (hsz : C.size ≤ s) (hb : C.size - notCount C ≤ b) (hr : notCount C ≤ r)
    (hsem : ∀ (x : Fin n → Bool) (u : Fin 2 → Bool),
      C.eval (rawVec x u) = D x (if useAnd then u 0 && u 1 else u 0 || u 1) ∧
      R x (if useAnd then u 0 && u 1 else u 0 || u 1)
        (fun j => (C.wires (rawVec x u)).getD (tap j).val false)) :
    1 ≤ s ∧ 1 ≤ b ∧
    ∃ (C1 : Circuit) (tap1 : Fin m → Fin (n + 1 + 2 + C1.size)),
      FanInTwo C1 ∧ ReadsBack (n + 1 + 2) C1 ∧ C1.output < n + 1 + 2 + C1.size ∧
      C1.size ≤ s - 1 ∧ C1.size - notCount C1 ≤ b - 1 ∧ notCount C1 ≤ r ∧
      ∀ (x : Fin n → Bool) (v : Fin 1 → Bool),
        C1.eval (rawVec x v) = D x (v 0) ∧
        R x (v 0) (fun j => (C1.wires (rawVec x v)).getD (tap1 j).val false) := by
  obtain ⟨k, hk, i0, pol, hop, hi0, hlit⟩ :=
    exists_nonnot_reading_lit1 useAnd x0 hdiff C hfan hrb hout (fun x u => (hsem x u).1)
  let neu : Bool := useAnd
  obtain ⟨rep, hrep_lt, hrep_eq⟩ :=
    exists_gate_replacement C hfan hrb neu k hk i0 pol hop hi0 hlit
  let f : ℕ → ℕ := dropWire n k rep neu
  let rawGs : List Gate := C.gates.take k ++ C.gates.drop (k + 1)
  let gs1 : List Gate := rawGs.map (fun g => ⟨g.op, g.inputs.map f⟩)
  let C1 : Circuit := ⟨gs1, f C.output⟩
  have hrawGs_len : rawGs.length = C.gates.length - 1 := by
    simp only [rawGs, List.length_append, List.length_take, List.length_drop]
    omega
  have hC1size : C1.size = C.size - 1 := by
    change gs1.length = C.gates.length - 1
    simp [gs1, hrawGs_len]
  have hnot1 : notCount C1 = notCount C := by
    rw [notCount_eq_filter_isNotGate, notCount_eq_filter_isNotGate]
    change (gs1.filter isNotGate).length = (C.gates.filter isNotGate).length
    rw [show gs1 = rawGs.map (fun g => ⟨g.op, g.inputs.map f⟩) from rfl]
    rw [filter_isNotGate_map]
    have hsplit : C.gates = C.gates.take k ++ (C.gates[k]'hk) :: C.gates.drop (k + 1) := by
      have := (List.take_append_drop k C.gates).symm
      rw [List.drop_eq_getElem_cons hk] at this
      exact this
    have hgk_not : isNotGate (C.gates[k]'hk) = false := by
      rcases hop with h | h <;> simp [isNotGate, h]
    have hfilt : C.gates.filter isNotGate =
        (C.gates.take k).filter isNotGate ++ (C.gates.drop (k + 1)).filter isNotGate := by
      conv_lhs => rw [hsplit]
      rw [List.filter_append, List.filter_cons, hgk_not]
      simp
    rw [hfilt]
    simp [rawGs, List.filter_append]
  have hnot_le1 : notCount C ≤ C.size - 1 := by
    rw [← hnot1, ← hC1size]
    exact notCount_le_size C1
  have h1s : 1 ≤ s := by change k < C.size at hk; omega
  have h1b : 1 ≤ b := by change k < C.size at hk; omega
  have hfan1 : FanInTwo C1 := by
    intro g hg
    simp only [C1, gs1, List.mem_map] at hg
    obtain ⟨g', hg', rfl⟩ := hg
    have hg'C : g' ∈ C.gates := by
      simp only [rawGs, List.mem_append] at hg'
      rcases hg' with h | h
      · exact List.mem_of_mem_take h
      · exact List.mem_of_mem_drop h
    obtain ⟨hop', hlen'⟩ := hfan g' hg'C
    exact ⟨hop', by simpa using hlen'⟩
  have hget_raw_lt : ∀ (j : ℕ) (hj : j < k),
      rawGs[j]'(by omega) = C.gates[j]'(by omega) := by
    intro j hj
    have hlen_take : (C.gates.take k).length = k := by simp; omega
    simp only [rawGs, List.getElem_append_left (by omega : j < (C.gates.take k).length),
      List.getElem_take]
  have hget_raw_ge : ∀ (j : ℕ) (hjk : k ≤ j) (hj : j < rawGs.length),
      rawGs[j]'hj = C.gates[j + 1]'(by omega) := by
    intro j hjk hj
    have hlen_take : (C.gates.take k).length = k := by simp; omega
    simp only [rawGs, List.getElem_append_right (by omega : (C.gates.take k).length ≤ j),
      List.getElem_drop, hlen_take]
    congr 1
    omega
  have hrb1 : ReadsBack (n + 1 + 2) C1 := by
    intro j hj i hi
    rw [gateAt_eq_getElem C1 j hj] at hi
    have hj_raw : j < rawGs.length := by simpa [C1, gs1] using hj
    simp only [C1, gs1, List.getElem_map, List.mem_map] at hi
    obtain ⟨i', hi', rfl⟩ := hi
    by_cases hjk : j < k
    · rw [hget_raw_lt j hjk] at hi'
      have hjC : j < C.gates.length := by omega
      have hilt : i' < n + 4 + j := by
        have := hrb j hjC i'
        rw [gateAt_eq_getElem C j hjC] at this
        exact this hi'
      have := dropWire_lt_before n k rep j i' neu (by omega) hilt
      omega
    · rw [hget_raw_ge j (by omega) hj_raw] at hi'
      have hjC : j + 1 < C.gates.length := by omega
      have hilt : i' < n + 4 + (j + 1) := by
        have := hrb (j + 1) hjC i'
        rw [gateAt_eq_getElem C (j + 1) hjC] at this
        exact this hi'
      have := dropWire_lt_after n k rep j i' neu hrep_lt (by omega) hilt
      omega
  have hout1 : C1.output < n + 1 + 2 + C1.size := by
    rw [hC1size]
    exact dropWire_lt_total n k rep C.size C.output neu hrep_lt hk hout
  let tap1 : Fin m → Fin (n + 1 + 2 + C1.size) := fun j =>
    ⟨f (tap j).val, by rw [hC1size]; exact dropWire_lt_total n k rep C.size (tap j).val neu hrep_lt hk (tap j).isLt⟩
  refine ⟨h1s, h1b, C1, tap1, hfan1, hrb1, hout1, by omega, by rw [hC1size, hnot1]; omega, by rw [hnot1]; exact hr, ?_⟩
  intro x v
  let u : Fin 2 → Bool := fun t => if t = 0 then v 0 else neu
  have hmerge_u : (if useAnd then u 0 && u 1 else u 0 || u 1) = v 0 := by
    cases useAnd <;> simp [u, neu]
  have hagree : ∀ w < n + 2 + 2 + C.size,
      (C1.wires (rawVec x v)).getD (f w) false =
        (C.wires (rawVec x u)).getD w false := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw
      by_cases h1 : w < n
      · have hfw : f w = w := by simp [f, dropWire, baseDrop, h1, show w ≠ n + 4 + k by omega]
        rw [hfw]
        rw [circuit_wires_getD_lt C1 (rawVec x v) w (by rw [rawVec_length]; omega)]
        rw [circuit_wires_getD_lt C (rawVec x u) w (by rw [rawVec_length]; omega)]
        rw [rawVec_getD_x x v w h1, rawVec_getD_x x u w h1]
      · by_cases h2 : w = n
        · subst w
          have hfw : f n = n := by simp only [f, dropWire, baseDrop]; split_ifs <;> omega
          rw [hfw]
          rw [circuit_wires_getD_lt C1 (rawVec x v) n (by rw [rawVec_length]; omega)]
          rw [circuit_wires_getD_lt C (rawVec x u) n (by rw [rawVec_length]; omega)]
          have a := rawVec_getD_u x v 0 (by decide)
          have b := rawVec_getD_u x u 0 (by decide)
          simpa [u] using a.trans b.symm
        · by_cases h3 : w = n + 1
          · subst h3
            have hfw : f (n + 1) = if neu then n + 2 else n + 1 := by
              simp [f, dropWire, baseDrop, show n + 1 ≠ n + 4 + k by omega]
            rw [hfw]
            rw [circuit_wires_getD_lt C (rawVec x u) (n + 1) (by rw [rawVec_length]; omega)]
            have bu : (rawVec x u).getD (n + 1) false = neu := by
              simpa [u] using rawVec_getD_u x u 1 (by decide)
            rw [bu]
            cases hneu : neu
            · simp only [Bool.false_eq_true, ↓reduceIte]
              rw [circuit_wires_getD_lt C1 (rawVec x v) (n + 1) (by rw [rawVec_length]; omega)]
              exact rawVec_getD_false x v
            · simp only [↓reduceIte]
              rw [circuit_wires_getD_lt C1 (rawVec x v) (n + 2) (by rw [rawVec_length]; omega)]
              simpa [Nat.add_assoc] using rawVec_getD_true x v
          · by_cases h4 : w = n + 2
            · subst h4
              have hfw : f (n + 2) = n + 1 := by
                simp [f, dropWire, baseDrop, show n + 2 ≠ n + 4 + k by omega]
              rw [hfw]
              rw [circuit_wires_getD_lt C1 (rawVec x v) (n + 1) (by rw [rawVec_length]; omega)]
              rw [circuit_wires_getD_lt C (rawVec x u) (n + 2) (by rw [rawVec_length]; omega)]
              rw [rawVec_getD_false x v, rawVec_getD_false x u]
            · by_cases h5 : w = n + 3
              · subst h5
                have hfw : f (n + 3) = n + 2 := by
                  simp [f, dropWire, baseDrop, show n + 3 ≠ n + 4 + k by omega]
                rw [hfw]
                rw [circuit_wires_getD_lt C1 (rawVec x v) (n + 2) (by rw [rawVec_length]; omega)]
                rw [circuit_wires_getD_lt C (rawVec x u) (n + 3) (by rw [rawVec_length]; omega)]
                have a := rawVec_getD_true x v
                have b := rawVec_getD_true x u
                simpa [Nat.add_assoc] using a.trans b.symm
              · let j := w - (n + 4)
                have hwj : w = n + 4 + j := by omega
                have hjC : j < C.gates.length := by change j < C.size; omega
                by_cases hjk : j < k
                · have hfw : f w = n + 3 + j := by
                    simp only [f, dropWire, baseDrop]; split_ifs <;> omega
                  rw [hfw]
                  have hlen1 : (rawVec x v).length = n + 3 := by rw [rawVec_length]
                  have hlen2 : (rawVec x u).length = n + 4 := by rw [rawVec_length]
                  have hj1 : j < C1.gates.length := by change j < C1.size; rw [hC1size]; change j < C.gates.length - 1; omega
                  have hg1 := circuit_wires_getD_gate C1 (rawVec x v) (by rw [hlen1]; exact hrb1) j hj1
                  have hg2 := circuit_wires_getD_gate C (rawVec x u) (by rw [hlen2]; exact hrb) j hjC
                  rw [hlen1] at hg1
                  rw [hlen2, ← hwj] at hg2
                  rw [hg1, hg2]
                  simp only [C1, gs1, List.getElem_map, hget_raw_lt j hjk, List.map_map]
                  congr 1
                  apply List.map_congr_left
                  intro i hi
                  have hilt : i < w := by
                    have := hrb j hjC i
                    rw [gateAt_eq_getElem C j hjC] at this
                    have := this hi; omega
                  exact ih i hilt (by omega)
                · by_cases hjeq : j = k
                  · rw [hjeq] at hwj
                    have hfw : f w = f rep := by
                      simp [f, dropWire, hwj, show rep ≠ n + 4 + k by omega]
                    rw [hfw, hwj, hrep_eq x v]
                    exact ih rep (by omega) (by omega)
                  · have hfw : f w = n + 3 + (j - 1) := by
                      simp only [f, dropWire, baseDrop]; split_ifs <;> omega
                    rw [hfw]
                    have hlen1 : (rawVec x v).length = n + 3 := by rw [rawVec_length]
                    have hlen2 : (rawVec x u).length = n + 4 := by rw [rawVec_length]
                    have hj1 : j - 1 < C1.gates.length := by change j - 1 < C1.size; rw [hC1size]; change j - 1 < C.gates.length - 1; omega
                    have hj1_raw : j - 1 < rawGs.length := by omega
                    have hg1 := circuit_wires_getD_gate C1 (rawVec x v) (by rw [hlen1]; exact hrb1) (j - 1) hj1
                    have hg2 := circuit_wires_getD_gate C (rawVec x u) (by rw [hlen2]; exact hrb) j hjC
                    rw [hlen1] at hg1
                    rw [hlen2, ← hwj] at hg2
                    rw [hg1, hg2]
                    have hraw_eq : rawGs[j - 1]'hj1_raw = C.gates[j]'hjC := by
                      have h := hget_raw_ge (j - 1) (by omega) hj1_raw
                      have hidx : j - 1 + 1 = j := by omega
                      simpa [hidx] using h
                    simp only [C1, gs1, List.getElem_map, hraw_eq, List.map_map]
                    congr 1
                    apply List.map_congr_left
                    intro i hi
                    have hilt : i < w := by
                      have := hrb j hjC i
                      rw [gateAt_eq_getElem C j hjC] at this
                      have := this hi; omega
                    exact ih i hilt (by omega)
  have hsem2 := hsem x u
  rw [hmerge_u] at hsem2
  constructor
  · unfold Circuit.eval
    change (C1.wires (rawVec x v)).getD (f C.output) false = D x (v 0)
    rw [hagree C.output hout]
    exact hsem2.1
  · have htap : (fun j => (C1.wires (rawVec x v)).getD (tap1 j).val false) =
        (fun j => (C.wires (rawVec x u)).getD (tap j).val false) := by
      funext j
      exact hagree (tap j).val (tap j).isLt
    rw [htap]
    exact hsem2.2

end PEqualNP.Outside.L_lib_1203_aux

theorem PEqualNP.Outside.L_lib_1203 : (∀ n m : Nat, ∀ (D : (Fin n → Bool) → Bool → Bool)
    (R : (Fin n → Bool) → Bool → (Fin m → Bool) → Prop),
  (∃ x : Fin n → Bool, D x false ≠ D x true) →
  let fits := fun (d : Nat) (merge : (Fin d → Bool) → Bool) (s b r : Nat) =>
    ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin m → Fin (n+d+2+C.size)),
      PEqualNP.MetaComplexity.FanInTwo C ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+d+2) C ∧
      C.output < n+d+2+C.size ∧ C.size ≤ s ∧
      C.size - PEqualNP.NotBracket.notCount C ≤ b ∧ PEqualNP.NotBracket.notCount C ≤ r ∧
      ∀ (x : Fin n → Bool) (u : Fin d → Bool),
        let raw := List.ofFn x ++ List.ofFn u ++ [false,true]
        C.eval raw = D x (merge u) ∧
        R x (merge u) (fun j => (C.wires raw).getD (tap j).val false)
  ∀ (useAnd : Bool) (s b r : Nat),
    fits 2 (fun u => if useAnd then u 0 && u 1 else u 0 || u 1) s b r ↔
      1 ≤ s ∧ 1 ≤ b ∧ fits 1 (fun u => u 0) (s-1) (b-1) r) := by
  intro n m D R ⟨x0, hdiff⟩ fits useAnd s b r
  constructor
  · rintro ⟨C, tap, hfan, hrb, hout, hsz, hb, hr, hsem⟩
    exact PEqualNP.Outside.L_lib_1203_aux.forward_dir x0 hdiff useAnd s b r C tap hfan hrb hout hsz hb hr hsem
  · rintro ⟨hs1, hb1, C, tap, hfan, hrb, hout, hsz, hb, hr, hsem⟩
    exact PEqualNP.Outside.L_lib_1203_aux.backward_dir useAnd s b r hs1 hb1 C tap hfan hrb hout hsz hb hr hsem

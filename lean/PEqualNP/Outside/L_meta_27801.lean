import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27801_aux

open PEqualNP.CircuitLowerBounds

private def oneHot (p : ℕ) (x : Fin p) : List Bool :=
  List.ofFn (fun h : Fin p => decide (h = x))

private def isOr (g : Gate) : Prop :=
  g.op = GateOp.or ∧ g.inputs.length ≤ 2

private def isNot (g : Gate) : Prop :=
  g.op = GateOp.not ∧ g.inputs.length ≤ 1

private def hits (p q : ℕ) (A : Fin p → Fin q → Bool) (E : Circuit) : Prop :=
  ∀ y : Fin q, ∃ w : ℕ, ∀ x : Fin p, (E.wires (oneHot p x)).getD w false = A x y

private def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [List.foldl_cons, ih, stepW]; omega

private lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length :=
  foldl_length C.gates x

private lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < w.length) :
    (gs.foldl stepW w).getD k false = w.getD k false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (stepW w g) (by simp [stepW]; omega)]
    exact List.getD_append _ _ _ _ hk

private lemma wires_getD_input (C : Circuit) (x : List Bool) (k : ℕ) (hk : k < x.length) :
    (C.wires x).getD k false = x.getD k false :=
  foldl_getD_lt C.gates x k hk

private lemma wires_getD_gate (C : Circuit) (x : List Bool) (k : ℕ) (hk : k < C.gates.length) :
    (C.wires x).getD (x.length + k) false =
      (C.gates[k]).op.eval ((C.gates[k]).inputs.map fun i =>
        if i < x.length + k then (C.wires x).getD i false else false) := by
  have hsplit : C.gates = C.gates.take k ++ [C.gates[k]] ++ C.gates.drop (k + 1) := by
    simp [List.take_append_getElem, List.take_append_drop]
  unfold Circuit.wires
  change (C.gates.foldl stepW x).getD (x.length + k) false = _
  let pref := (C.gates.take k).foldl stepW x
  have hpref_len : pref.length = x.length + k := by
    simp [pref, foldl_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
  have hW_eq : C.gates.foldl stepW x = (C.gates.drop (k + 1)).foldl stepW (stepW pref C.gates[k]) := by
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_append]
    rfl
  have hstep_len : (stepW pref C.gates[k]).length = x.length + k + 1 := by
    simp [stepW, hpref_len]
  have hlt : x.length + k < (stepW pref C.gates[k]).length := by omega
  have hW_k : (C.gates.foldl stepW x).getD (x.length + k) false =
      (C.gates[k]).op.eval ((C.gates[k]).inputs.map fun i => pref.getD i false) := by
    rw [hW_eq, foldl_getD_lt _ _ _ hlt]
    simp [stepW, List.getD_append_right _ _ _ _ (Nat.le_of_eq hpref_len), hpref_len]
  rw [hW_k]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  change pref.getD i false = if i < x.length + k then (C.gates.foldl stepW x).getD i false else false
  by_cases hi : i < x.length + k
  · rw [if_pos hi, hW_eq]
    rw [foldl_getD_lt (C.gates.drop (k + 1)) (stepW pref C.gates[k]) i (by omega)]
    rw [stepW, List.getD_append _ _ _ _ (by omega)]
  · rw [if_neg hi, List.getD_eq_default _ _ (by omega)]

private lemma getD_ofFn {p : ℕ} (f : Fin p → Bool) (k : ℕ) (hk : k < p) :
    (List.ofFn f).getD k false = f ⟨k, hk⟩ := by
  rw [List.getD_eq_getElem _ _ (by simp [hk]), List.getElem_ofFn]

private lemma oneHot_getD (p : ℕ) (x : Fin p) (k : ℕ) :
    (oneHot p x).getD k false = decide (k = x.val) := by
  by_cases hk : k < p
  · unfold oneHot
    rw [getD_ofFn _ k hk]
    simp [Fin.ext_iff]
  · rw [List.getD_eq_default _ _ (by simp [oneHot]; omega)]
    have hne : k ≠ x.val := by omega
    simp [hne]

private lemma oneHot_length (p : ℕ) (x : Fin p) : (oneHot p x).length = p := by
  simp [oneHot]

private lemma or_circuit_linear (p : ℕ) (E : Circuit) (hor : ∀ g ∈ E.gates, isOr g)
    (v : Fin p → Bool) (w : ℕ) :
    (E.wires (List.ofFn v)).getD w false =
      decide (∃ x : Fin p, v x = true ∧ (E.wires (oneHot p x)).getD w false = true) := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hwp : w < p
    · rw [wires_getD_input E _ w (by simp [hwp]), getD_ofFn _ w hwp]
      have hrhs : ∀ x : Fin p, (E.wires (oneHot p x)).getD w false = decide (w = x.val) := fun x => by
        rw [wires_getD_input E _ w (by simp [oneHot_length, hwp]), oneHot_getD]
      simp only [hrhs, decide_eq_true_eq]
      cases hv : v ⟨w, hwp⟩
      · simp only [Bool.false_eq, decide_eq_false_iff_not, not_exists, not_and]
        intro x hx heq
        have : x = ⟨w, hwp⟩ := Fin.ext heq.symm
        subst this; simp [hv] at hx
      · simp only [Bool.true_eq, decide_eq_true_eq]
        exact ⟨⟨w, hwp⟩, hv, rfl⟩
    · by_cases hwN : w < p + E.gates.length
      · have hk : w - p < E.gates.length := by omega
        have hwk : p + (w - p) = w := by omega
        have h1 := wires_getD_gate E (List.ofFn v) (w - p) hk
        simp only [List.length_ofFn, hwk] at h1
        rw [h1]
        have hop : (E.gates[w - p]).op = GateOp.or := (hor _ (List.getElem_mem hk)).1
        rw [hop, GateOp.eval]
        have hstep : ∀ x : Fin p, (E.wires (oneHot p x)).getD w false =
            ((E.gates[w - p]).inputs.map fun i =>
              if i < w then (E.wires (oneHot p x)).getD i false else false).any id := fun x => by
          have hx := wires_getD_gate E (oneHot p x) (w - p) hk
          simp only [oneHot_length, hwk, hop, GateOp.eval] at hx
          exact hx
        apply Bool.eq_iff_iff.mpr
        simp only [List.any_eq_true, List.mem_map, id_eq, decide_eq_true_eq, hstep]
        constructor
        · rintro ⟨_, ⟨i, hi, heq⟩, rfl⟩
          by_cases hil : i < w
          · rw [if_pos hil, ih i hil, decide_eq_true_eq] at heq
            obtain ⟨x, hvx, hxi⟩ := heq
            exact ⟨x, hvx, true, ⟨i, hi, by rw [if_pos hil]; exact hxi⟩, rfl⟩
          · rw [if_neg hil] at heq; cases heq
        · rintro ⟨x, hvx, _, ⟨i, hi, heq⟩, rfl⟩
          by_cases hil : i < w
          · rw [if_pos hil] at heq
            refine ⟨true, ⟨i, hi, ?_⟩, rfl⟩
            rw [if_pos hil, ih i hil, decide_eq_true_eq]
            exact ⟨x, hvx, heq⟩
          · rw [if_neg hil] at heq; cases heq
      · rw [List.getD_eq_default _ _ (by rw [wires_length, List.length_ofFn]; omega)]
        symm
        simp only [decide_eq_false_iff_not, not_exists, not_and]
        intro x _
        rw [List.getD_eq_default _ _ (by rw [wires_length, oneHot_length]; omega)]
        exact Bool.false_ne_true

private def dagEdge (p : ℕ) (E : Circuit) (a b : Fin (p + E.gates.length)) : Bool :=
  if h : p ≤ b.val then
    decide (a.val < b.val ∧ a.val ∈ (E.gates[b.val - p]'(by omega)).inputs)
  else false

private def dagReach (p : ℕ) (E : Circuit) (a b : Fin (p + E.gates.length)) : Prop :=
  Relation.ReflTransGen (fun u v => dagEdge p E u v = true) a b

private lemma dagEdge_lt {p : ℕ} {E : Circuit} {a b : Fin (p + E.gates.length)}
    (h : dagEdge p E a b = true) : a.val < b.val := by
  unfold dagEdge at h
  split_ifs at h with hp
  exact (decide_eq_true_eq.mp h).1

private lemma dagReach_le {p : ℕ} {E : Circuit} {a b : Fin (p + E.gates.length)}
    (h : dagReach p E a b) : a.val ≤ b.val := by
  induction h with
  | refl => exact le_rfl
  | tail _ hstep ih => exact le_trans ih (Nat.le_of_lt (dagEdge_lt hstep))

private lemma wires_iff_dagReach (p : ℕ) (E : Circuit) (hor : ∀ g ∈ E.gates, isOr g)
    (x : Fin p) (b : Fin (p + E.gates.length)) :
    (E.wires (oneHot p x)).getD b.val false = true ↔
      dagReach p E ⟨x.val, by omega⟩ b := by
  induction hb : b.val using Nat.strong_induction_on generalizing b with
  | ind n ih =>
    by_cases hnp : n < p
    · have h1 : (E.wires (oneHot p x)).getD n false = decide (n = x.val) := by
        rw [wires_getD_input E _ n (by rw [oneHot_length]; omega), oneHot_getD]
      rw [h1, decide_eq_true_eq]
      constructor
      · intro heq
        have hb_eq : b = ⟨x.val, by omega⟩ := Fin.ext (hb.trans heq)
        rw [hb_eq]; exact Relation.ReflTransGen.refl
      · intro hr
        rcases Relation.ReflTransGen.cases_tail hr with rfl | ⟨c, _, hedge⟩
        · exact hb.symm
        · unfold dagEdge at hedge
          rw [dif_neg (by omega)] at hedge
          cases hedge
    · have hk : b.val - p < E.gates.length := by omega
      have hbk : p + (b.val - p) = n := by omega
      have h1 := wires_getD_gate E (oneHot p x) (b.val - p) hk
      simp only [oneHot_length, hbk] at h1
      have hop : (E.gates[b.val - p]).op = GateOp.or := (hor _ (List.getElem_mem hk)).1
      rw [h1, hop, GateOp.eval]
      simp only [List.any_eq_true, List.mem_map, id_eq]
      constructor
      · rintro ⟨_, ⟨i, hi, heq⟩, rfl⟩
        by_cases hil : i < n
        · rw [if_pos hil] at heq
          have hr := (ih i (by omega) ⟨i, by omega⟩ rfl).mp heq
          refine Relation.ReflTransGen.tail hr ?_
          unfold dagEdge
          rw [dif_pos (by omega), decide_eq_true_eq]
          exact ⟨by dsimp only; omega, hi⟩
        · rw [if_neg hil] at heq; cases heq
      · intro hr
        rcases Relation.ReflTransGen.cases_tail hr with heq | ⟨c, hrc, hedge⟩
        · have : b.val = x.val := congrArg Fin.val heq
          omega
        · unfold dagEdge at hedge
          rw [dif_pos (by omega), decide_eq_true_eq] at hedge
          have hc := (ih c.val (by omega) c rfl).mpr hrc
          refine ⟨true, ⟨c.val, hedge.2, ?_⟩, rfl⟩
          rw [if_pos (by omega : c.val < n)]
          exact hc

private lemma dagEdge_inDeg_le (p : ℕ) (E : Circuit) (hor : ∀ g ∈ E.gates, isOr g)
    (b : Fin (p + E.gates.length)) :
    (Finset.univ.filter (fun a : Fin (p + E.gates.length) => dagEdge p E a b = true)).card ≤
      if p ≤ b.val then 2 else 0 := by
  split_ifs with hbp
  · have hk : b.val - p < E.gates.length := by omega
    have hlen : (E.gates[b.val - p]).inputs.length ≤ 2 := (hor _ (List.getElem_mem hk)).2
    have hsub : (Finset.univ.filter (fun a : Fin (p + E.gates.length) => dagEdge p E a b = true)).image Fin.val ⊆
        (E.gates[b.val - p]).inputs.toFinset := by
      intro i hi
      rw [Finset.mem_image] at hi
      obtain ⟨a, ha, rfl⟩ := hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, dagEdge, dif_pos hbp, decide_eq_true_eq] at ha
      exact List.mem_toFinset.mpr ha.2
    calc (Finset.univ.filter (fun a : Fin (p + E.gates.length) => dagEdge p E a b = true)).card
        = ((Finset.univ.filter (fun a : Fin (p + E.gates.length) => dagEdge p E a b = true)).image Fin.val).card :=
          (Finset.card_image_of_injective _ Fin.val_injective).symm
      _ ≤ (E.gates[b.val - p]).inputs.toFinset.card := Finset.card_le_card hsub
      _ ≤ (E.gates[b.val - p]).inputs.length := List.toFinset_card_le _
      _ ≤ 2 := hlen
  · have hemp : Finset.univ.filter (fun a : Fin (p + E.gates.length) => dagEdge p E a b = true) = ∅ := by
      ext a
      simp [dagEdge, dif_neg hbp]
    rw [hemp, Finset.card_empty]

private def orFold (base : ℕ) (acc : ℕ) : List ℕ → List Gate × ℕ
  | [] => ([], acc)
  | w :: rest =>
    let g : Gate := ⟨GateOp.or, [acc, w]⟩
    let res := orFold (base + 1) base rest
    (g :: res.1, res.2)

private lemma orFold_len (base acc : ℕ) (ws : List ℕ) :
    (orFold base acc ws).1.length = ws.length := by
  induction ws generalizing base acc with
  | nil => rfl
  | cons w rest ih => simp [orFold, ih]

private lemma orFold_isOr (base acc : ℕ) (ws : List ℕ) :
    ∀ g ∈ (orFold base acc ws).1, isOr g := by
  induction ws generalizing base acc with
  | nil => intro g hg; cases hg
  | cons w rest ih =>
    intro g hg
    simp only [orFold, List.mem_cons] at hg
    rcases hg with rfl | hrest
    · exact ⟨rfl, by simp⟩
    · exact ih _ _ g hrest

private lemma orFold_out_lt (base acc : ℕ) (ws : List ℕ) (hacc : acc < base) :
    (orFold base acc ws).2 < base + ws.length := by
  induction ws generalizing base acc with
  | nil => simpa [orFold] using hacc
  | cons w rest ih =>
    simp only [orFold, List.length_cons]
    have h := ih (base + 1) base (by omega)
    omega

private lemma orFold_eval (W : List Bool) (acc : ℕ) (ws : List ℕ)
    (hacc : acc < W.length) (hws : ∀ u ∈ ws, u < W.length) :
    (((orFold W.length acc ws).1).foldl stepW W).getD (orFold W.length acc ws).2 false =
      (W.getD acc false || ws.any (fun u => W.getD u false)) := by
  induction ws generalizing W acc with
  | nil => simp [orFold]
  | cons w rest ih =>
    simp only [orFold, List.foldl_cons, List.any_cons]
    let g : Gate := ⟨GateOp.or, [acc, w]⟩
    let W' := stepW W g
    have hW'_len : W'.length = W.length + 1 := by simp [W', stepW]
    have hlt_w : w < W.length := hws w List.mem_cons_self
    have hW'_acc : W'.getD W.length false = (W.getD acc false || W.getD w false) := by
      simp [W', stepW, g, GateOp.eval, List.getD_append_right _ _ _ _ (le_refl W.length)]
    have hW'_lt : ∀ u < W.length, W'.getD u false = W.getD u false := fun u hu => by
      exact List.getD_append _ _ _ _ hu
    have ih' := ih W' W.length (by omega) (fun u hu => by
      have := hws u (List.mem_cons_of_mem _ hu); omega)
    rw [hW'_len] at ih'
    rw [ih', hW'_acc]
    have hany : rest.any (fun u => W'.getD u false) = rest.any (fun u => W.getD u false) := by
      have haux : ∀ l : List ℕ, (∀ u ∈ l, u < W.length) →
          l.any (fun u => W'.getD u false) = l.any (fun u => W.getD u false) := by
        intro l hl
        induction l with
        | nil => rfl
        | cons a t iht =>
          simp only [List.any_cons, hW'_lt a (hl a List.mem_cons_self),
            iht (fun u hu => hl u (List.mem_cons_of_mem _ hu))]
      exact haux rest (fun u hu => hws u (List.mem_cons_of_mem _ hu))
    rw [hany, Bool.or_assoc]

private theorem or_transpose (p q : ℕ) (R : Fin p → Fin q → Bool) (E : Circuit)
    (hhits : hits p q R E) (hor : ∀ g ∈ E.gates, isOr g) :
    ∃ D : Circuit, hits q p (fun y x => R x y) D ∧ (∀ g ∈ D.gates, isOr g) ∧
      D.size + ((Finset.univ : Finset (Fin p)).filter (fun u => ∃ v, R u v = true)).card ≤
        E.size + ((Finset.univ : Finset (Fin q)).filter (fun v => ∃ u, R u v = true)).card := by
  classical
  let N := p + E.gates.length
  let NZRow : Finset (Fin p) := Finset.univ.filter (fun x => ∃ y, R x y = true)
  let NZCol : Finset (Fin q) := Finset.univ.filter (fun y => ∃ x, R x y = true)
  choose wOf hwOf using hhits
  have hwOf_lt : ∀ y ∈ NZCol, wOf y < N := by
    intro y hy
    simp only [NZCol, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    obtain ⟨x, hxy⟩ := hy
    have hev := hwOf y x
    rw [hxy] at hev
    by_contra hge
    have hdef : (E.wires (oneHot p x)).getD (wOf y) false = false :=
      List.getD_eq_default _ _ (by rw [wires_length, oneHot_length]; omega)
    rw [hdef] at hev
    exact Bool.false_ne_true hev
  let Act : Finset (Fin N) := Finset.univ.filter (fun a =>
    (∃ x : Fin p, dagReach p E ⟨x.val, by omega⟩ a) ∧
    (∃ y : Fin q, ∃ hy : y ∈ NZCol, dagReach p E a ⟨wOf y, hwOf_lt y hy⟩))

  have hbuild : ∀ k ≤ N,
      ∃ (gs : List Gate) (wireOf : Fin N → ℕ),
        (∀ g ∈ gs, isOr g) ∧
        (∀ a ∈ Act, N - k ≤ a.val →
          wireOf a < q + gs.length ∧
          ∀ y : Fin q, ((gs.foldl stepW (oneHot q y)).getD (wireOf a) false = true ↔
            ∃ hy : y ∈ NZCol, dagReach p E a ⟨wOf y, hwOf_lt y hy⟩)) ∧
        gs.length + (Act.filter (fun a => N - k ≤ a.val)).card =
          ∑ a ∈ Act.filter (fun a => N - k ≤ a.val),
            ((NZCol.filter (fun y => wOf y = a.val)).card +
             (Act.filter (fun b => dagEdge p E a b = true)).card) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨[], fun _ => 0, ?_, ?_, ?_⟩
      · intro _ h; cases h
      · intro a _ hge; omega
      · have hemp : Act.filter (fun a : Fin N => N - 0 ≤ a.val) = ∅ := by
          ext a; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]; intro _; omega
        rw [hemp]; simp
    | succ k' ih =>
      intro hk
      obtain ⟨gs, wireOf, hgs_or, hgs_spec, hgs_len⟩ := ih (by omega)
      let a0 : Fin N := ⟨N - 1 - k', by omega⟩
      by_cases ha0 : a0 ∈ Act
      ·
        let sinks : List (Fin q) := (NZCol.filter (fun y => wOf y = a0.val)).toList
        let outs : List (Fin N) := (Act.filter (fun b => dagEdge p E a0 b = true)).toList
        let kids : List ℕ := sinks.map Fin.val ++ outs.map wireOf
        have hkids_len : kids.length =
            (NZCol.filter (fun y => wOf y = a0.val)).card +
            (Act.filter (fun b => dagEdge p E a0 b = true)).card := by
          simp [kids, sinks, outs]
        have hkids_ne : kids ≠ [] := by
          intro hemp
          have h0 : kids.length = 0 := by rw [hemp]; rfl
          rw [hkids_len] at h0
          have ha0_spec := (Finset.mem_filter.mp ha0).2
          obtain ⟨y, hy, hr⟩ := ha0_spec.2
          rcases Relation.ReflTransGen.cases_head hr with heq | ⟨b, hedge, hrb⟩
          · have hwy : wOf y = a0.val := (congrArg Fin.val heq).symm
            have hmem : y ∈ NZCol.filter (fun y => wOf y = a0.val) := Finset.mem_filter.mpr ⟨hy, hwy⟩
            have hpos := Finset.card_pos.mpr ⟨y, hmem⟩
            omega
          · have hb_act : b ∈ Act := by
              rw [Finset.mem_filter]
              refine ⟨Finset.mem_univ _, ?_, ⟨y, hy, hrb⟩⟩
              obtain ⟨x, hrx⟩ := ha0_spec.1
              exact ⟨x, Relation.ReflTransGen.tail hrx hedge⟩
            have hmem : b ∈ Act.filter (fun b => dagEdge p E a0 b = true) :=
              Finset.mem_filter.mpr ⟨hb_act, hedge⟩
            have hpos := Finset.card_pos.mpr ⟨b, hmem⟩
            omega
        cases hkids_cons : kids with
        | nil => exact absurd hkids_cons hkids_ne
        | cons w0 rest =>
          have hkids_lt : ∀ u ∈ kids, u < q + gs.length := by
            intro u hu
            simp only [kids, List.mem_append, List.mem_map] at hu
            rcases hu with ⟨y, _, rfl⟩ | ⟨b, hb, rfl⟩
            · omega
            · have hb' : b ∈ Act.filter (fun b => dagEdge p E a0 b = true) :=
                Finset.mem_toList.mp hb
              rw [Finset.mem_filter] at hb'
              have hlt := dagEdge_lt hb'.2
              exact (hgs_spec b hb'.1 (by dsimp [a0] at hlt; omega)).1
          have hw0_lt : w0 < q + gs.length := hkids_lt w0 (by rw [hkids_cons]; simp)
          have hrest_lt : ∀ u ∈ rest, u < q + gs.length := fun u hu =>
            hkids_lt u (by rw [hkids_cons]; exact List.mem_cons_of_mem _ hu)
          let res := orFold (q + gs.length) w0 rest
          let gs' := gs ++ res.1
          let wireOf' : Fin N → ℕ := fun a => if a = a0 then res.2 else wireOf a
          have hres_len : res.1.length + 1 = kids.length := by
            have := congrArg List.length hkids_cons
            simp only [List.length_cons] at this
            rw [orFold_len]
            omega
          refine ⟨gs', wireOf', ?_, ?_, ?_⟩
          · intro g hg
            rw [List.mem_append] at hg
            rcases hg with h1 | h2
            · exact hgs_or g h1
            · exact orFold_isOr _ _ _ g h2
          · intro a ha hge
            by_cases ha_eq : a = a0
            · subst ha_eq
              simp only [wireOf', ite_true]
              refine ⟨?_, ?_⟩
              · have := orFold_out_lt (q + gs.length) w0 rest hw0_lt
                simp only [gs', List.length_append, res, orFold_len]; omega
              · intro y
                let W := gs.foldl stepW (oneHot q y)
                have hW_len : W.length = q + gs.length := by
                  simp [W, foldl_length, oneHot_length]
                have hev : (gs'.foldl stepW (oneHot q y)).getD res.2 false =
                    (W.getD w0 false || rest.any (fun u => W.getD u false)) := by
                  simp only [gs', List.foldl_append, res]
                  have := orFold_eval W w0 rest (by omega) (fun u hu => by
                    have := hrest_lt u hu; omega)
                  simpa only [hW_len] using this
                rw [hev]
                have hany_kids : (W.getD w0 false || rest.any (fun u => W.getD u false)) =
                    kids.any (fun u => W.getD u false) := by
                  rw [hkids_cons, List.any_cons]
                rw [hany_kids, List.any_eq_true]
                constructor
                · rintro ⟨u, hu, hWu⟩
                  simp only [kids, List.mem_append, List.mem_map] at hu
                  rcases hu with ⟨y', hy', rfl⟩ | ⟨b, hb, rfl⟩
                  · have hy'_mem := Finset.mem_filter.mp (Finset.mem_toList.mp hy')
                    have hW_y' : W.getD y'.val false = decide (y'.val = y.val) := by
                      rw [foldl_getD_lt _ _ _ (by rw [oneHot_length]; exact y'.isLt), oneHot_getD]
                    rw [hW_y', decide_eq_true_eq] at hWu
                    have hy_eq : y' = y := Fin.ext hWu
                    subst hy_eq
                    refine ⟨hy'_mem.1, ?_⟩
                    have ha0_eq : a0 = ⟨wOf y', hwOf_lt y' hy'_mem.1⟩ := Fin.ext hy'_mem.2.symm
                    exact ha0_eq ▸ Relation.ReflTransGen.refl
                  · have hb_mem := Finset.mem_filter.mp (Finset.mem_toList.mp hb)
                    have hlt := dagEdge_lt hb_mem.2
                    obtain ⟨hy, hrb⟩ := ((hgs_spec b hb_mem.1 (by dsimp [a0] at hlt; omega)).2 y).mp hWu
                    exact ⟨hy, Relation.ReflTransGen.head hb_mem.2 hrb⟩
                · rintro ⟨hy, hr⟩
                  rcases Relation.ReflTransGen.cases_head hr with heq | ⟨b, hedge, hrb⟩
                  · have hwy : wOf y = a0.val := (congrArg Fin.val heq).symm
                    refine ⟨y.val, ?_, ?_⟩
                    · simp only [kids, List.mem_append, List.mem_map]
                      left
                      exact ⟨y, Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨hy, hwy⟩), rfl⟩
                    · rw [foldl_getD_lt _ _ _ (by rw [oneHot_length]; exact y.isLt), oneHot_getD]
                      simp
                  · have hb_act : b ∈ Act := by
                      rw [Finset.mem_filter]
                      refine ⟨Finset.mem_univ _, ?_, ⟨y, hy, hrb⟩⟩
                      obtain ⟨x, hrx⟩ := (Finset.mem_filter.mp ha0).2.1
                      exact ⟨x, Relation.ReflTransGen.tail hrx hedge⟩
                    have hlt := dagEdge_lt hedge
                    have hWb := ((hgs_spec b hb_act (by dsimp [a0] at hlt; omega)).2 y).mpr ⟨hy, hrb⟩
                    refine ⟨wireOf b, ?_, hWb⟩
                    simp only [kids, List.mem_append, List.mem_map]
                    right
                    exact ⟨b, Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨hb_act, hedge⟩), rfl⟩
            · simp only [wireOf', if_neg ha_eq]
              have hge' : N - k' ≤ a.val := by
                have hne : a.val ≠ N - 1 - k' := fun h => ha_eq (Fin.ext h)
                omega
              have hsp := hgs_spec a ha hge'
              refine ⟨by simp [gs']; omega, fun y => ?_⟩
              have hsame : (gs'.foldl stepW (oneHot q y)).getD (wireOf a) false =
                  (gs.foldl stepW (oneHot q y)).getD (wireOf a) false := by
                simp only [gs', List.foldl_append]
                apply foldl_getD_lt
                rw [foldl_length, oneHot_length]
                exact hsp.1
              rw [hsame]
              exact hsp.2 y
          · have hfilt : Act.filter (fun a => N - (k' + 1) ≤ a.val) =
                insert a0 (Act.filter (fun a => N - k' ≤ a.val)) := by
              ext a
              simp only [Finset.mem_filter, Finset.mem_insert]
              constructor
              · rintro ⟨ha, hle⟩
                by_cases heq : a.val = N - 1 - k'
                · exact Or.inl (Fin.ext heq)
                · exact Or.inr ⟨ha, by omega⟩
              · rintro (rfl | ⟨ha, hle⟩)
                · exact ⟨ha0, by dsimp [a0]; omega⟩
                · exact ⟨ha, by omega⟩
            have hnotmem : a0 ∉ Act.filter (fun a => N - k' ≤ a.val) := by
              simp only [Finset.mem_filter, not_and]; intro _; dsimp [a0]; omega
            rw [hfilt, Finset.card_insert_of_notMem hnotmem, Finset.sum_insert hnotmem]
            simp only [gs', List.length_append]
            omega
      ·
        have hfilt : Act.filter (fun a => N - (k' + 1) ≤ a.val) =
            Act.filter (fun a => N - k' ≤ a.val) := by
          ext a
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨ha, hle⟩
            have hne : a.val ≠ N - 1 - k' := fun heq => ha0 ((Fin.ext (by dsimp [a0]; exact heq) : a = a0) ▸ ha)
            exact ⟨ha, by omega⟩
          · rintro ⟨ha, hle⟩
            exact ⟨ha, by omega⟩
        refine ⟨gs, wireOf, hgs_or, ?_, ?_⟩
        · intro a ha hle
          have hne : a.val ≠ N - 1 - k' := fun heq => ha0 ((Fin.ext (by dsimp [a0]; exact heq) : a = a0) ▸ ha)
          exact hgs_spec a ha (by omega)
        · rw [hfilt]; exact hgs_len

  obtain ⟨gs, wireOf, hgs_or, hgs_spec, hgs_len⟩ := hbuild N le_rfl
  have hAct_all : Act.filter (fun a : Fin N => N - N ≤ a.val) = Act := by
    ext a; simp
  rw [hAct_all] at hgs_len
  let D : Circuit := ⟨gs, 0⟩
  refine ⟨D, ?_, hgs_or, ?_⟩
  ·
    intro x
    by_cases hx : x ∈ NZRow
    · have hx_act : (⟨x.val, by omega⟩ : Fin N) ∈ Act := by
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ⟨x, Relation.ReflTransGen.refl⟩, ?_⟩
        obtain ⟨y, hxy⟩ := (Finset.mem_filter.mp hx).2
        have hy : y ∈ NZCol := Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, hxy⟩
        have hev := hwOf y x
        rw [hxy] at hev
        exact ⟨y, hy, (wires_iff_dagReach p E hor x ⟨wOf y, hwOf_lt y hy⟩).mp hev⟩
      refine ⟨wireOf ⟨x.val, by omega⟩, fun y => ?_⟩
      have hspec := (hgs_spec ⟨x.val, by omega⟩ hx_act (by omega)).2 y
      apply Bool.eq_iff_iff.mpr
      change ((gs.foldl stepW (oneHot q y)).getD (wireOf ⟨x.val, by omega⟩) false = true) ↔ R x y = true
      rw [hspec]
      constructor
      · rintro ⟨hy, hr⟩
        have h1 := (wires_iff_dagReach p E hor x ⟨wOf y, hwOf_lt y hy⟩).mpr hr
        rw [hwOf y x] at h1; exact h1
      · intro hxy
        have hy : y ∈ NZCol := Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, hxy⟩
        have h1 : (E.wires (oneHot p x)).getD (wOf y) false = true := by rw [hwOf y x]; exact hxy
        exact ⟨hy, (wires_iff_dagReach p E hor x ⟨wOf y, hwOf_lt y hy⟩).mp h1⟩
    · refine ⟨q + gs.length, fun y => ?_⟩
      have hfalse : R x y = false := by
        cases hxy : R x y
        · rfl
        · exact False.elim (hx (Finset.mem_filter.mpr ⟨Finset.mem_univ _, y, hxy⟩))
      dsimp only
      rw [hfalse]
      exact List.getD_eq_default _ _ (by rw [wires_length, oneHot_length])
  ·
    change gs.length + NZRow.card ≤ E.gates.length + NZCol.card
    let ActIn := Act.filter (fun a : Fin N => a.val < p)
    let ActG := Act.filter (fun a : Fin N => p ≤ a.val)
    have hAct_split : Act.card = ActIn.card + ActG.card := by
      have h := Finset.card_filter_add_card_filter_not (s := Act) (p := fun a : Fin N => a.val < p)
      have hge : Act.filter (fun a : Fin N => ¬a.val < p) = ActG := by
        ext a; simp [ActG, not_lt]
      rw [hge] at h; exact h.symm
    have hActIn_eq : ActIn.card = NZRow.card := by
      refine Finset.card_bij (fun a ha => ⟨a.val, (Finset.mem_filter.mp ha).2⟩) ?_ ?_ ?_
      · intro a ha
        have ha' := Finset.mem_filter.mp ha
        obtain ⟨y, hy, hr⟩ := (Finset.mem_filter.mp ha'.1).2.2
        have h1 := (wires_iff_dagReach p E hor ⟨a.val, ha'.2⟩ ⟨wOf y, hwOf_lt y hy⟩).mpr hr
        rw [hwOf y _] at h1
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, y, h1⟩
      · intro a1 _ a2 _ heq
        exact Fin.ext (congrArg (Fin.val (n := p)) heq)
      · intro x hx
        obtain ⟨y, hxy⟩ := (Finset.mem_filter.mp hx).2
        have hy : y ∈ NZCol := Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, hxy⟩
        have h1 : (E.wires (oneHot p x)).getD (wOf y) false = true := by rw [hwOf y x]; exact hxy
        have hr := (wires_iff_dagReach p E hor x ⟨wOf y, hwOf_lt y hy⟩).mp h1
        refine ⟨⟨x.val, by omega⟩, ?_, Fin.ext rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨x, Relation.ReflTransGen.refl⟩, ⟨y, hy, hr⟩⟩, x.isLt⟩
    have hActG_le : ActG.card ≤ E.gates.length := by
      let f : Fin N → ℕ := fun a => a.val - p
      have hinj : Set.InjOn f ↑ActG := by
        intro a1 ha1 a2 ha2 heq
        have h1 := (Finset.mem_filter.mp ha1).2
        have h2 := (Finset.mem_filter.mp ha2).2
        dsimp [f] at heq
        exact Fin.ext (by omega)
      have hsub : ActG.image f ⊆ Finset.range E.gates.length := by
        intro k hk
        rw [Finset.mem_image] at hk
        obtain ⟨a, ha, rfl⟩ := hk
        have := (Finset.mem_filter.mp ha).2
        rw [Finset.mem_range]; dsimp [f]; omega
      calc ActG.card = (ActG.image f).card := (Finset.card_image_of_injOn hinj).symm
        _ ≤ (Finset.range E.gates.length).card := Finset.card_le_card hsub
        _ = E.gates.length := Finset.card_range _

    have hsink_sum : ∑ a ∈ Act, (NZCol.filter (fun y => wOf y = a.val)).card = NZCol.card := by
      have hbi : NZCol = Act.biUnion (fun a => NZCol.filter (fun y => wOf y = a.val)) := by
        ext y
        simp only [Finset.mem_biUnion, Finset.mem_filter]
        constructor
        · intro hy
          obtain ⟨x, hxy⟩ := (Finset.mem_filter.mp hy).2
          have h1 : (E.wires (oneHot p x)).getD (wOf y) false = true := by rw [hwOf y x]; exact hxy
          have hr := (wires_iff_dagReach p E hor x ⟨wOf y, hwOf_lt y hy⟩).mp h1
          have hw_act : (⟨wOf y, hwOf_lt y hy⟩ : Fin N) ∈ Act :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨x, hr⟩, ⟨y, hy, Relation.ReflTransGen.refl⟩⟩
          exact ⟨⟨wOf y, hwOf_lt y hy⟩, hw_act, hy, rfl⟩
        · rintro ⟨_, _, hy, _⟩; exact hy
      have hdisj : Set.PairwiseDisjoint (Act : Set (Fin N)) (fun a => NZCol.filter (fun y => wOf y = a.val)) := by
        intro a1 _ a2 _ hne
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro y h1 h2
        have e1 := (Finset.mem_filter.mp h1).2
        have e2 := (Finset.mem_filter.mp h2).2
        exact hne (Fin.ext (e1.symm.trans e2))
      conv_rhs => rw [hbi]
      rw [Finset.card_biUnion hdisj]

    have hedge_sum : ∑ a ∈ Act, (Act.filter (fun b => dagEdge p E a b = true)).card ≤ 2 * ActG.card := by
      have hswap : ∑ a ∈ Act, (Act.filter (fun b => dagEdge p E a b = true)).card =
          ∑ b ∈ Act, (Act.filter (fun a => dagEdge p E a b = true)).card := by
        simp only [Finset.card_filter]
        exact Finset.sum_comm
      rw [hswap]
      calc ∑ b ∈ Act, (Act.filter (fun a => dagEdge p E a b = true)).card
          ≤ ∑ b ∈ Act, (Finset.univ.filter (fun a => dagEdge p E a b = true)).card :=
            Finset.sum_le_sum fun b _ => Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))
        _ ≤ ∑ b ∈ Act, (if p ≤ b.val then 2 else 0) :=
            Finset.sum_le_sum fun b _ => dagEdge_inDeg_le p E hor b
        _ = 2 * ActG.card := by
            rw [← Finset.sum_filter]
            simp [ActG, mul_comm]
    rw [Finset.sum_add_distrib, hsink_sum] at hgs_len
    omega

private def supp (D : Circuit) (k : ℕ) (w : ℕ) : Finset (Fin k) :=
  Finset.univ.filter (fun j : Fin k => (D.wires (oneHot k j)).getD w false = true)

private lemma supp_input (D : Circuit) (k : ℕ) (w : ℕ) (hw : w < k) :
    supp D k w = {⟨w, hw⟩} := by
  ext j
  simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  rw [wires_getD_input D (oneHot k j) w (by rw [oneHot_length]; exact hw), oneHot_getD,
    decide_eq_true_eq, Fin.ext_iff]
  exact eq_comm

private lemma supp_ge_size (D : Circuit) (k : ℕ) (w : ℕ) (hw : k + D.gates.length ≤ w) :
    supp D k w = ∅ := by
  ext j
  simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
  rw [List.getD_eq_default _ _ (by rw [wires_length, oneHot_length]; omega)]
  exact Bool.false_ne_true

private lemma supp_gate (D : Circuit) (k : ℕ) (hor : ∀ g ∈ D.gates, isOr g)
    (idx : ℕ) (hidx : idx < D.gates.length) :
    supp D k (k + idx) =
      ((D.gates[idx]).inputs.filter (· < k + idx)).toFinset.biUnion (fun u => supp D k u) := by
  ext j
  simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
    List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
  have h1 := wires_getD_gate D (oneHot k j) idx hidx
  simp only [oneHot_length] at h1
  have hop : (D.gates[idx]).op = GateOp.or := (hor _ (List.getElem_mem hidx)).1
  rw [h1, hop, GateOp.eval]
  simp only [List.any_eq_true, List.mem_map, id_eq]
  constructor
  · rintro ⟨_, ⟨u, hu, heq⟩, rfl⟩
    by_cases hult : u < k + idx
    · rw [if_pos hult] at heq
      exact ⟨u, ⟨hu, hult⟩, heq⟩
    · rw [if_neg hult] at heq
      cases heq
  · rintro ⟨u, ⟨hu, hult⟩, heq⟩
    refine ⟨true, ⟨u, hu, ?_⟩, rfl⟩
    rw [if_pos hult]
    exact heq

private lemma odd_card_cases {α : Type*} {S : Finset α} (h : Odd S.card) :
    S.card = 1 ∨ 3 ≤ S.card := by
  rcases h with ⟨m, hm⟩
  omega

private lemma nzRow_card (k n : ℕ) (F : Fin n → Finset (Fin k))
    (hOdd : ∀ i, Odd (F i).card) :
    (Finset.univ.filter (fun i : Fin n => ∃ j : Fin k, decide (j ∈ F i) = true)).card = n := by
  have heq : Finset.univ.filter (fun i : Fin n => ∃ j : Fin k, decide (j ∈ F i) = true) = Finset.univ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq, iff_true]
    have hpos : 0 < (F i).card := by
      rcases hOdd i with ⟨m, hm⟩
      omega
    exact Finset.card_pos.mp hpos
  rw [heq, Finset.card_univ, Fintype.card_fin]

private lemma nzCol_card (k n : ℕ) (F : Fin n → Finset (Fin k))
    (hSing : ∀ j : Fin k, ∃ i, F i = {j}) :
    (Finset.univ.filter (fun j : Fin k => ∃ i : Fin n, decide (j ∈ F i) = true)).card = k := by
  have heq : Finset.univ.filter (fun j : Fin k => ∃ i : Fin n, decide (j ∈ F i) = true) = Finset.univ := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq, iff_true]
    obtain ⟨i, hi⟩ := hSing j
    exact ⟨i, by rw [hi]; exact Finset.mem_singleton_self j⟩
  rw [heq, Finset.card_univ, Fintype.card_fin]

private lemma sing_card (k n : ℕ) (F : Fin n → Finset (Fin k))
    (hInj : Function.Injective F) (hSing : ∀ j : Fin k, ∃ i, F i = {j}) :
    (Finset.univ.filter (fun i : Fin n => (F i).card = 1)).card = k := by
  classical
  choose f hf using hSing
  have hf_inj : Function.Injective f := by
    intro j1 j2 heq
    have h1 : ({j1} : Finset (Fin k)) = {j2} := by
      rw [← hf j1, ← hf j2, heq]
    exact Finset.singleton_injective h1
  have himg : Finset.univ.image f = Finset.univ.filter (fun i : Fin n => (F i).card = 1) := by
    ext i
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨j, rfl⟩
      rw [hf j, Finset.card_singleton]
    · intro hc
      obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hc
      exact ⟨j, hInj ((hf j).trans hj.symm)⟩
  rw [← himg, Finset.card_image_of_injective _ hf_inj, Finset.card_univ, Fintype.card_fin]

private lemma big_card (k n : ℕ) (F : Fin n → Finset (Fin k))
    (hInj : Function.Injective F) (hOdd : ∀ i, Odd (F i).card)
    (hSing : ∀ j : Fin k, ∃ i, F i = {j}) :
    (Finset.univ.filter (fun i : Fin n => 3 ≤ (F i).card)).card + k = n := by
  have heq : Finset.univ.filter (fun i : Fin n => 3 ≤ (F i).card) =
      Finset.univ.filter (fun i : Fin n => ¬ (F i).card = 1) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases odd_card_cases (hOdd i) with h1 | h3
    · omega
    · omega
  rw [heq]
  have hsing := sing_card k n F hInj hSing
  have hsum := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (p := fun i => (F i).card = 1)
  rw [Finset.card_univ, Fintype.card_fin] at hsum
  omega

private lemma forward_dir (k n : ℕ) (F : Fin n → Finset (Fin k))
    (hInj : Function.Injective F) (hOdd : ∀ i, Odd (F i).card)
    (hSing : ∀ j : Fin k, ∃ i, F i = {j}) (s : ℕ)
    (hC : ∃ C : Circuit, C.size ≤ s ∧
      (∀ g ∈ C.gates, g.op = GateOp.or ∧ g.inputs.length ≤ 2) ∧
      ∀ j : Fin k, ∃ w : ℕ, ∀ i : Fin n,
        (C.wires (List.ofFn (fun h : Fin n => decide (h = i)))).getD w false = decide (j ∈ F i)) :
    ∃ H : Finset (Finset (Fin k)), (∀ P ∈ H, P.card = 2) ∧
      (∀ i, (F i).card = 3 → ∃ P ∈ H, P ⊆ F i) ∧ 2 * n + H.card ≤ s + 2 * k := by
  classical
  obtain ⟨C, hC_size, hC_or, hC_hits⟩ := hC
  let M : Fin n → Fin k → Bool := fun i j => decide (j ∈ F i)
  have hhits : hits n k M C := hC_hits
  have hor : ∀ g ∈ C.gates, isOr g := hC_or
  obtain ⟨D, hD_hits, hD_or, hD_size⟩ := or_transpose n k M C hhits hor
  rw [nzRow_card k n F hOdd, nzCol_card k n F hSing] at hD_size
  have hD_budget : D.gates.length + n ≤ s + k := by
    have : D.size = D.gates.length := rfl
    have : C.size = C.gates.length := rfl
    omega

  have hex_gate : ∀ i : Fin n, 3 ≤ (F i).card →
      ∃ idx : Fin D.gates.length, supp D k (k + idx.val) = F i := by
    intro i hi
    obtain ⟨w, hw⟩ := hD_hits i
    have hsupp : supp D k w = F i := by
      ext j
      simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hw j]
      simp [M]
    have hw_ge : k ≤ w := by
      by_contra hlt
      push_neg at hlt
      rw [supp_input D k w hlt] at hsupp
      have hc := congrArg Finset.card hsupp
      rw [Finset.card_singleton] at hc
      omega
    have hw_lt : w < k + D.gates.length := by
      by_contra hge
      push_neg at hge
      rw [supp_ge_size D k w hge] at hsupp
      have hc := congrArg Finset.card hsupp
      rw [Finset.card_empty] at hc
      omega
    exact ⟨⟨w - k, by omega⟩, by simpa [Nat.add_sub_of_le hw_ge] using hsupp⟩
  let G_pair : Finset (Fin D.gates.length) :=
    Finset.univ.filter (fun idx => (supp D k (k + idx.val)).card = 2)
  let bigSet : Finset (Fin n) := Finset.univ.filter (fun i => 3 ≤ (F i).card)
  let G_odd : Finset (Fin D.gates.length) :=
    Finset.univ.filter (fun idx => Odd (supp D k (k + idx.val)).card ∧ 3 ≤ (supp D k (k + idx.val)).card)

  have hbig_le_odd : bigSet.card ≤ G_odd.card := by
    have hmem : ∀ i ∈ bigSet, ∃ idx ∈ G_odd, supp D k (k + idx.val) = F i := by
      intro i hi
      simp only [bigSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      obtain ⟨idx, hidx⟩ := hex_gate i hi
      refine ⟨idx, ?_, hidx⟩
      simp only [G_odd, Finset.mem_filter, Finset.mem_univ, true_and, hidx]
      exact ⟨hOdd i, hi⟩

    have hsub : bigSet.image F ⊆ G_odd.image (fun idx => supp D k (k + idx.val)) := by
      intro S hS
      rw [Finset.mem_image] at hS ⊢
      obtain ⟨i, hi, rfl⟩ := hS
      obtain ⟨idx, hidx, heq⟩ := hmem i hi
      exact ⟨idx, hidx, heq⟩
    calc bigSet.card
        = (bigSet.image F).card := (Finset.card_image_of_injective _ hInj).symm
      _ ≤ (G_odd.image (fun idx => supp D k (k + idx.val))).card := Finset.card_le_card hsub
      _ ≤ G_odd.card := Finset.card_image_le
  have hdisj : Disjoint G_pair G_odd := by
    rw [Finset.disjoint_left]
    intro idx h1 h2
    simp only [G_pair, G_odd, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    rcases h2.1 with ⟨m, hm⟩
    omega
  let H : Finset (Finset (Fin k)) := G_pair.image (fun idx => supp D k (k + idx.val))
  refine ⟨H, ?_, ?_, ?_⟩
  · intro P hP
    rw [Finset.mem_image] at hP
    obtain ⟨idx, hidx, rfl⟩ := hP
    simp only [G_pair, Finset.mem_filter, Finset.mem_univ, true_and] at hidx
    exact hidx
  · intro i hi3
    have hne : ∃ m : ℕ, m < D.gates.length ∧ supp D k (k + m) = F i := by
      obtain ⟨idx, hidx⟩ := hex_gate i (by omega)
      exact ⟨idx.val, idx.isLt, hidx⟩
    let m := Nat.find hne
    have hm_spec : m < D.gates.length ∧ supp D k (k + m) = F i := Nat.find_spec hne
    have hm_min : ∀ m' < m, ¬ (m' < D.gates.length ∧ supp D k (k + m') = F i) :=
      fun m' hm' => Nat.find_min hne hm'
    let U : Finset ℕ := ((D.gates[m]'(hm_spec.1)).inputs.filter (· < k + m)).toFinset
    have hU_union : F i = U.biUnion (fun u => supp D k u) := by
      rw [← hm_spec.2]
      exact supp_gate D k hD_or m hm_spec.1
    have hU_card : U.card ≤ 2 := by
      calc U.card
          ≤ ((D.gates[m]'(hm_spec.1)).inputs.filter (· < k + m)).length := List.toFinset_card_le _
        _ ≤ (D.gates[m]'(hm_spec.1)).inputs.length := List.length_filter_le _ _
        _ ≤ 2 := (hD_or _ (List.getElem_mem hm_spec.1)).2
    have hU_sub : ∀ u ∈ U, supp D k u ⊆ F i := by
      intro u hu
      rw [hU_union]
      exact Finset.subset_biUnion_of_mem (fun v => supp D k v) hu
    have hU_ne : ∀ u ∈ U, supp D k u ≠ F i := by
      intro u hu heq
      have hult : u < k + m := by
        simp only [U, List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hu
        exact hu.2
      by_cases huk : u < k
      · rw [supp_input D k u huk] at heq
        have hc := congrArg Finset.card heq
        rw [Finset.card_singleton] at hc
        omega
      · push_neg at huk
        have hltm : u - k < m := by omega
        have hkm : k + (u - k) = u := by omega
        apply hm_min (u - k) hltm
        exact ⟨by omega, by rw [hkm]; exact heq⟩
    have hU_le2 : ∀ u ∈ U, (supp D k u).card ≤ 2 := by
      intro u hu
      have hss : supp D k u ⊂ F i := Finset.ssubset_iff_subset_ne.mpr ⟨hU_sub u hu, hU_ne u hu⟩
      have hlt := Finset.card_lt_card hss
      omega
    have hex_pair : ∃ u ∈ U, (supp D k u).card = 2 := by
      by_contra hno
      push_neg at hno
      have hle1 : ∀ u ∈ U, (supp D k u).card ≤ 1 := fun u hu => by
        have h2 := hU_le2 u hu
        have hne2 := hno u hu
        omega
      have hbound : (F i).card ≤ 2 := by
        calc (F i).card
            = (U.biUnion (fun u => supp D k u)).card := by rw [hU_union]
          _ ≤ ∑ u ∈ U, (supp D k u).card := Finset.card_biUnion_le
          _ ≤ ∑ _u ∈ U, 1 := Finset.sum_le_sum hle1
          _ = U.card := by simp
          _ ≤ 2 := hU_card
      omega
    obtain ⟨u, hu, hu2⟩ := hex_pair
    have hult : u < k + m := by
      simp only [U, List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hu
      exact hu.2
    have huk : k ≤ u := by
      by_contra hlt
      push_neg at hlt
      rw [supp_input D k u hlt, Finset.card_singleton] at hu2
      omega
    have hkm : k + (u - k) = u := by omega
    refine ⟨supp D k u, ?_, hU_sub u hu⟩
    rw [Finset.mem_image]
    refine ⟨⟨u - k, by omega⟩, ?_, by simp [hkm]⟩
    simp only [G_pair, Finset.mem_filter, Finset.mem_univ, true_and, hkm]
    exact hu2
  · have hH_le : H.card ≤ G_pair.card := Finset.card_image_le
    have hunion : G_pair.card + G_odd.card ≤ D.gates.length := by
      rw [← Finset.card_union_of_disjoint hdisj]
      calc (G_pair ∪ G_odd).card
          ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ _)
        _ = D.gates.length := by rw [Finset.card_univ, Fintype.card_fin]
    have hbig := big_card k n F hInj hOdd hSing
    change bigSet.card + k = n at hbig
    omega

private lemma foldl_append_or_batch (base : List Gate) (batch : List (ℕ × ℕ))
    (k : ℕ) (hbatch : ∀ p ∈ batch, p.1 < k + base.length ∧ p.2 < k + base.length) :
    let gs := base ++ batch.map (fun p => ({ op := GateOp.or, inputs := [p.1, p.2] } : Gate))
    (∀ w < k + base.length, ∀ j : Fin k,
      (gs.foldl stepW (oneHot k j)).getD w false = (base.foldl stepW (oneHot k j)).getD w false) ∧
    (∀ t (ht : t < batch.length), ∀ j : Fin k,
      (gs.foldl stepW (oneHot k j)).getD (k + base.length + t) false =
        ((base.foldl stepW (oneHot k j)).getD (batch[t]).1 false ||
         (base.foldl stepW (oneHot k j)).getD (batch[t]).2 false)) := by
  intro gs
  have hpref_len : ∀ j : Fin k, (base.foldl stepW (oneHot k j)).length = k + base.length := fun j => by
    rw [foldl_length, oneHot_length]
  have hgs_eq : ∀ j : Fin k, gs.foldl stepW (oneHot k j) =
      (batch.map (fun p => ({ op := GateOp.or, inputs := [p.1, p.2] } : Gate))).foldl stepW
        (base.foldl stepW (oneHot k j)) := fun j => by
    simp [gs, List.foldl_append]
  constructor
  · intro w hw j
    rw [hgs_eq j, foldl_getD_lt _ _ w (by rw [hpref_len j]; exact hw)]
  · intro t ht j
    let C : Circuit := ⟨gs, 0⟩
    have hidx : base.length + t < C.gates.length := by
      simp [C, gs, ht]
    have h1 := wires_getD_gate C (oneHot k j) (base.length + t) hidx
    simp only [oneHot_length] at h1
    have hadd : k + (base.length + t) = k + base.length + t := by omega
    rw [hadd] at h1
    change (C.wires (oneHot k j)).getD (k + base.length + t) false = _
    rw [h1]
    have hget : C.gates[base.length + t]'hidx =
        ({ op := GateOp.or, inputs := [(batch[t]).1, (batch[t]).2] } : Gate) := by
      simp [C, gs, List.getElem_append_right]
    rw [hget]
    have hbt := hbatch (batch[t]) (List.getElem_mem ht)
    have hlt1 : (batch[t]).1 < k + base.length + t := by omega
    have hlt2 : (batch[t]).2 < k + base.length + t := by omega
    have hw1 : (C.wires (oneHot k j)).getD (batch[t]).1 false =
        (base.foldl stepW (oneHot k j)).getD (batch[t]).1 false := by
      change (gs.foldl stepW (oneHot k j)).getD _ false = _
      rw [hgs_eq j, foldl_getD_lt _ _ _ (by rw [hpref_len j]; exact hbt.1)]
    have hw2 : (C.wires (oneHot k j)).getD (batch[t]).2 false =
        (base.foldl stepW (oneHot k j)).getD (batch[t]).2 false := by
      change (gs.foldl stepW (oneHot k j)).getD _ false = _
      rw [hgs_eq j, foldl_getD_lt _ _ _ (by rw [hpref_len j]; exact hbt.2)]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      Bool.or_false, id_eq, hlt1, hlt2, ↓reduceIte]
    rw [hw1, hw2]

private lemma card_ge5_split {k : ℕ} {S : Finset (Fin k)} (h5 : 5 ≤ S.card) :
    ∃ S1 S2 : Finset (Fin k), S1 ⊆ S ∧ S2 ⊆ S ∧
      S1.card = S.card - 2 ∧ S2.card = 3 ∧
      ∀ j : Fin k, j ∈ S ↔ j ∈ S1 ∨ j ∈ S2 := by
  have hne1 : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨x, hx⟩ := hne1
  have hne2 : (S.erase x).Nonempty := Finset.card_pos.mp (by
    rw [Finset.card_erase_of_mem hx]; omega)
  obtain ⟨y, hy⟩ := hne2
  have hyS : y ∈ S := Finset.mem_of_mem_erase hy
  have hyx : y ≠ x := Finset.ne_of_mem_erase hy
  have hne3 : ((S.erase x).erase y).Nonempty := Finset.card_pos.mp (by
    rw [Finset.card_erase_of_mem hy, Finset.card_erase_of_mem hx]; omega)
  obtain ⟨z, hz⟩ := hne3
  have hz1 : z ∈ S.erase x := Finset.mem_of_mem_erase hz
  have hzy : z ≠ y := Finset.ne_of_mem_erase hz
  have hzS : z ∈ S := Finset.mem_of_mem_erase hz1
  have hzx : z ≠ x := Finset.ne_of_mem_erase hz1
  refine ⟨(S.erase y).erase z, {x, y, z}, ?_, ?_, ?_, ?_, ?_⟩
  · exact Finset.Subset.trans (Finset.erase_subset z _) (Finset.erase_subset y S)
  · intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl <;> assumption
  · have hzy' : z ∈ S.erase y := Finset.mem_erase.mpr ⟨hzy, hzS⟩
    rw [Finset.card_erase_of_mem hzy', Finset.card_erase_of_mem hyS]
    omega
  · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp [hzy.symm]
    · simp [hyx.symm, hzx.symm]
  · intro j
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hj
      by_cases hjz : j = z
      · right; right; right; exact hjz
      · by_cases hjy : j = y
        · right; right; left; exact hjy
        · left; exact ⟨hjz, hjy, hj⟩
    · rintro (⟨_, _, hj⟩ | rfl | rfl | rfl) <;> assumption

private lemma backward_dir (k n : ℕ) (F : Fin n → Finset (Fin k))
    (hInj : Function.Injective F) (hOdd : ∀ i, Odd (F i).card)
    (hSing : ∀ j : Fin k, ∃ i, F i = {j})
    (hClosed : ∀ i, ∀ S ⊆ F i, Odd S.card → ∃ h, F h = S) (s : ℕ)
    (hH : ∃ H : Finset (Finset (Fin k)), (∀ P ∈ H, P.card = 2) ∧
      (∀ i, (F i).card = 3 → ∃ P ∈ H, P ⊆ F i) ∧ 2 * n + H.card ≤ s + 2 * k) :
    ∃ C : Circuit, C.size ≤ s ∧
      (∀ g ∈ C.gates, g.op = GateOp.or ∧ g.inputs.length ≤ 2) ∧
      ∀ j : Fin k, ∃ w : ℕ, ∀ i : Fin n,
        (C.wires (List.ofFn (fun h : Fin n => decide (h = i)))).getD w false = decide (j ∈ F i) := by
  classical
  obtain ⟨H, hH_card, hH_hit, hbudget⟩ := hH

  have hlayer : ∀ m : ℕ,
      ∃ gs : List Gate,
        (∀ g ∈ gs, isOr g) ∧
        gs.length = H.card + (Finset.univ.filter (fun i : Fin n => 3 ≤ (F i).card ∧ (F i).card ≤ m)).card ∧
        (∀ P ∈ H, ∃ w < k + gs.length, ∀ j : Fin k,
          (gs.foldl stepW (oneHot k j)).getD w false = decide (j ∈ P)) ∧
        (∀ i : Fin n, (F i).card ≤ m → ∃ w < k + gs.length, ∀ j : Fin k,
          (gs.foldl stepW (oneHot k j)).getD w false = decide (j ∈ F i)) := by
    intro m
    induction m with
    | zero =>

      let hList := H.toList
      have hpair : ∀ P ∈ hList, ∃ a b : Fin k, a ≠ b ∧ P = {a, b} := fun P hP =>
        Finset.card_eq_two.mp (hH_card P (Finset.mem_toList.mp hP))
      let pairOf : Finset (Fin k) → ℕ × ℕ := fun P =>
        if h : P ∈ H then
          let h2 := Finset.card_eq_two.mp (hH_card P h)
          ((Classical.choose h2).val, (Classical.choose (Classical.choose_spec h2)).val)
        else (0, 0)
      let batch : List (ℕ × ℕ) := hList.map pairOf
      have hbatch_lt : ∀ p ∈ batch, p.1 < k + ([] : List Gate).length ∧ p.2 < k + ([] : List Gate).length := by
        intro p hp
        rw [List.mem_map] at hp
        obtain ⟨P, hP, rfl⟩ := hp
        have hPH : P ∈ H := Finset.mem_toList.mp hP
        simp only [pairOf, dif_pos hPH, List.length_nil, Nat.add_zero]
        exact ⟨Fin.isLt _, Fin.isLt _⟩
      let gs := ([] : List Gate) ++ batch.map (fun p => ({ op := GateOp.or, inputs := [p.1, p.2] } : Gate))
      have hres := foldl_append_or_batch [] batch k hbatch_lt
      refine ⟨gs, ?_, ?_, ?_, ?_⟩
      · intro g hg
        simp only [gs, List.nil_append, List.mem_map] at hg
        obtain ⟨p, _, rfl⟩ := hg
        exact ⟨rfl, by simp⟩
      · have hemp : Finset.univ.filter (fun i : Fin n => 3 ≤ (F i).card ∧ (F i).card ≤ 0) = ∅ := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
          omega
        rw [hemp, Finset.card_empty, Nat.add_zero]
        simp [gs, batch, hList]
      · intro P hPH
        have hPmem : P ∈ hList := Finset.mem_toList.mpr hPH
        obtain ⟨t, ht, hPt⟩ := List.getElem_of_mem hPmem
        have ht_b : t < batch.length := by simp [batch, ht]
        refine ⟨k + ([] : List Gate).length + t, ?_, ?_⟩
        · simp [gs, batch]; omega
        · intro j
          have hev := hres.2 t ht_b j
          simp only [List.foldl_nil] at hev
          rw [hev]
          have hbt : batch[t]'ht_b = pairOf P := by
            simp [batch, hPt]
          rw [hbt]
          simp only [pairOf, dif_pos hPH]
          set a := Classical.choose (Finset.card_eq_two.mp (hH_card P hPH))
          set b := Classical.choose (Classical.choose_spec (Finset.card_eq_two.mp (hH_card P hPH)))
          have hab : a ≠ b ∧ P = {a, b} :=
            Classical.choose_spec (Classical.choose_spec (Finset.card_eq_two.mp (hH_card P hPH)))
          rw [oneHot_getD, oneHot_getD]
          have hPeq : P = {a, b} := hab.2
          conv_rhs => rw [hPeq]
          apply Bool.eq_iff_iff.mpr
          simp only [Bool.or_eq_true, decide_eq_true_eq, Finset.mem_insert,
            Finset.mem_singleton, Fin.ext_iff]
          exact ⟨fun h => h.imp Eq.symm Eq.symm, fun h => h.imp Eq.symm Eq.symm⟩
      · intro i hi0
        rcases hOdd i with ⟨r, hr⟩
        omega
    | succ m ih =>
      obtain ⟨gs, hgs_or, hgs_len, hgs_H, hgs_F⟩ := ih
      by_cases hm0 : m = 0
      ·
        subst hm0
        refine ⟨gs, hgs_or, ?_, hgs_H, ?_⟩
        · have heq : Finset.univ.filter (fun i : Fin n => 3 ≤ (F i).card ∧ (F i).card ≤ 1) =
              Finset.univ.filter (fun i : Fin n => 3 ≤ (F i).card ∧ (F i).card ≤ 0) := by
            ext i
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            omega
          rw [heq]; exact hgs_len
        · intro i hi1
          have hc1 : (F i).card = 1 := by
            rcases hOdd i with ⟨r, hr⟩; omega
          obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc1
          refine ⟨a.val, by omega, ?_⟩
          intro j
          rw [foldl_getD_lt gs (oneHot k j) a.val (by rw [oneHot_length]; exact a.isLt),
            oneHot_getD, ha]
          apply Bool.eq_iff_iff.mpr
          simp [Fin.ext_iff, eq_comm]
      ·
        let newSet : Finset (Fin n) :=
          Finset.univ.filter (fun i : Fin n => 3 ≤ (F i).card ∧ (F i).card = m + 1)
        have hpair_wire : ∀ i ∈ newSet,
            ∃ p : ℕ × ℕ, p.1 < k + gs.length ∧ p.2 < k + gs.length ∧
              ∀ j : Fin k,
                ((gs.foldl stepW (oneHot k j)).getD p.1 false ||
                 (gs.foldl stepW (oneHot k j)).getD p.2 false) = decide (j ∈ F i) := by
          intro i hi
          simp only [newSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi
          by_cases h3 : (F i).card = 3
          · obtain ⟨P, hPH, hPsub⟩ := hH_hit i h3
            obtain ⟨w1, hw1_lt, hw1⟩ := hgs_H P hPH
            have hdiff_card : (F i \ P).card = 1 := by
              rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hPsub, h3, hH_card P hPH]
            obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hdiff_card
            refine ⟨(w1, c.val), hw1_lt, by omega, ?_⟩
            intro j
            rw [hw1 j, foldl_getD_lt gs (oneHot k j) c.val (by rw [oneHot_length]; exact c.isLt),
              oneHot_getD]
            apply Bool.eq_iff_iff.mpr
            simp only [Bool.or_eq_true, decide_eq_true_eq]
            constructor
            · rintro (hjP | hjc)
              · exact hPsub hjP
              · have hcj : j = c := Fin.ext hjc.symm
                subst hcj
                have hmem : j ∈ F i \ P := by rw [hc]; exact Finset.mem_singleton_self j
                exact (Finset.mem_sdiff.mp hmem).1
            · intro hjF
              by_cases hjP : j ∈ P
              · left; exact hjP
              · right
                have hmem : j ∈ F i \ P := Finset.mem_sdiff.mpr ⟨hjF, hjP⟩
                rw [hc, Finset.mem_singleton] at hmem
                rw [hmem]
          · have h5 : 5 ≤ (F i).card := by
              rcases hOdd i with ⟨r, hr⟩; omega
            obtain ⟨S1, S2, hS1_sub, hS2_sub, hS1_card, hS2_card, hunion⟩ := card_ge5_split h5
            have hS1_odd : Odd S1.card := by
              rcases hOdd i with ⟨r, hr⟩
              refine ⟨r - 1, by omega⟩
            have hS2_odd : Odd S2.card := ⟨1, by omega⟩
            obtain ⟨i1, hi1⟩ := hClosed i S1 hS1_sub hS1_odd
            obtain ⟨i2, hi2⟩ := hClosed i S2 hS2_sub hS2_odd
            obtain ⟨w1, hw1_lt, hw1⟩ := hgs_F i1 (by rw [hi1]; omega)
            obtain ⟨w2, hw2_lt, hw2⟩ := hgs_F i2 (by rw [hi2]; omega)
            refine ⟨(w1, w2), hw1_lt, hw2_lt, ?_⟩
            intro j
            rw [hw1 j, hw2 j, hi1, hi2]
            apply Bool.eq_iff_iff.mpr
            simp only [Bool.or_eq_true, decide_eq_true_eq]
            exact (hunion j).symm
        let nList := newSet.toList
        let pickPair : Fin n → ℕ × ℕ := fun i =>
          if h : i ∈ newSet then Classical.choose (hpair_wire i h) else (0, 0)
        let batch : List (ℕ × ℕ) := nList.map pickPair
        have hbatch_lt : ∀ p ∈ batch, p.1 < k + gs.length ∧ p.2 < k + gs.length := by
          intro p hp
          rw [List.mem_map] at hp
          obtain ⟨i, hi, rfl⟩ := hp
          have hmem : i ∈ newSet := Finset.mem_toList.mp hi
          simp only [pickPair, dif_pos hmem]
          have hs := Classical.choose_spec (hpair_wire i hmem)
          exact ⟨hs.1, hs.2.1⟩
        let gs' := gs ++ batch.map (fun p => ({ op := GateOp.or, inputs := [p.1, p.2] } : Gate))
        have hres := foldl_append_or_batch gs batch k hbatch_lt
        refine ⟨gs', ?_, ?_, ?_, ?_⟩
        · intro g hg
          simp only [gs', List.mem_append, List.mem_map] at hg
          rcases hg with h1 | ⟨p, _, rfl⟩
          · exact hgs_or g h1
          · exact ⟨rfl, by simp⟩
        · have hdisj : Disjoint
              (Finset.univ.filter (fun i : Fin n => 3 ≤ (F i).card ∧ (F i).card ≤ m)) newSet := by
            rw [Finset.disjoint_left]
            intro i h1 h2
            simp only [newSet, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
            omega
          have hunion : Finset.univ.filter (fun i : Fin n => 3 ≤ (F i).card ∧ (F i).card ≤ m + 1) =
              Finset.univ.filter (fun i : Fin n => 3 ≤ (F i).card ∧ (F i).card ≤ m) ∪ newSet := by
            ext i
            simp only [newSet, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
            omega
          rw [hunion, Finset.card_union_of_disjoint hdisj]
          have hlen' : gs'.length = gs.length + newSet.card := by
            simp [gs', batch, nList]
          omega
        · intro P hPH
          obtain ⟨w, hw_lt, hw⟩ := hgs_H P hPH
          refine ⟨w, by simp [gs']; omega, ?_⟩
          intro j
          rw [hres.1 w hw_lt j, hw j]
        · intro i him
          by_cases hle : (F i).card ≤ m
          · obtain ⟨w, hw_lt, hw⟩ := hgs_F i hle
            refine ⟨w, by simp [gs']; omega, ?_⟩
            intro j
            rw [hres.1 w hw_lt j, hw j]
          · have h3 : 3 ≤ (F i).card := by
              rcases hOdd i with ⟨r, hr⟩; omega
            have hmem : i ∈ newSet := by
              simp only [newSet, Finset.mem_filter, Finset.mem_univ, true_and]
              omega
            have hmemL : i ∈ nList := Finset.mem_toList.mpr hmem
            obtain ⟨t, ht, hit⟩ := List.getElem_of_mem hmemL
            have ht_b : t < batch.length := by simp [batch, ht]
            refine ⟨k + gs.length + t, by simp [gs', batch]; omega, ?_⟩
            intro j
            rw [hres.2 t ht_b j]
            have hbt : batch[t]'ht_b = pickPair i := by simp [batch, hit]
            rw [hbt]
            simp only [pickPair, dif_pos hmem]
            exact (Classical.choose_spec (hpair_wire i hmem)).2.2 j
  obtain ⟨gs, hgs_or, hgs_len, _, hgs_F⟩ := hlayer k
  let D : Circuit := ⟨gs, 0⟩
  let M : Fin n → Fin k → Bool := fun i j => decide (j ∈ F i)
  have hD_hits : hits k n (fun j i => M i j) D := by
    intro i
    have hle : (F i).card ≤ k := by
      calc (F i).card ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ _)
        _ = k := by rw [Finset.card_univ, Fintype.card_fin]
    obtain ⟨w, _, hw⟩ := hgs_F i hle
    exact ⟨w, hw⟩
  obtain ⟨C, hC_hits, hC_or, hC_size⟩ := or_transpose k n (fun j i => M i j) D hD_hits hgs_or
  rw [nzCol_card k n F hSing, nzRow_card k n F hOdd] at hC_size
  have hfilter_eq : Finset.univ.filter (fun i : Fin n => 3 ≤ (F i).card ∧ (F i).card ≤ k) =
      Finset.univ.filter (fun i : Fin n => 3 ≤ (F i).card) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_left_iff_imp]
    intro _
    calc (F i).card ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ _)
      _ = k := by rw [Finset.card_univ, Fintype.card_fin]
  rw [hfilter_eq] at hgs_len
  have hbig := big_card k n F hInj hOdd hSing
  have hD_size : D.size = gs.length := rfl
  refine ⟨C, by omega, hC_or, hC_hits⟩

end PEqualNP.Outside.L_meta_27801_aux

theorem PEqualNP.Outside.L_meta_27801 :
  ∀ (k n : ℕ) (F : Fin n → Finset (Fin k)), Function.Injective F →
    (∀ i, Odd (F i).card) → (∀ j : Fin k, ∃ i, F i = {j}) →
    (∀ i, ∀ S ⊆ F i, Odd S.card → ∃ h, F h = S) →
    ∀ s : ℕ,
      (∃ C : PEqualNP.CircuitLowerBounds.Circuit, C.size ≤ s ∧
        (∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ g.inputs.length ≤ 2) ∧
        ∀ j : Fin k, ∃ w : ℕ, ∀ i : Fin n,
          (C.wires (List.ofFn (fun h : Fin n => decide (h = i)))).getD w false = decide (j ∈ F i)) ↔
      ∃ H : Finset (Finset (Fin k)), (∀ P ∈ H, P.card = 2) ∧
        (∀ i, (F i).card = 3 → ∃ P ∈ H, P ⊆ F i) ∧ 2*n + H.card ≤ s + 2*k := by
  intro k n F hInj hOdd hSing hClosed s
  exact ⟨PEqualNP.Outside.L_meta_27801_aux.forward_dir k n F hInj hOdd hSing s,
    PEqualNP.Outside.L_meta_27801_aux.backward_dir k n F hInj hOdd hSing hClosed s⟩

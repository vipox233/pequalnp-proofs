import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_825_aux

private abbrev Gate := PEqualNP.CircuitLowerBounds.Gate
private abbrev GateOp := PEqualNP.CircuitLowerBounds.GateOp
private abbrev Circ := PEqualNP.CircuitLowerBounds.Circuit

private noncomputable def isNL (g : Gate) : Bool :=
  @decide ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) (Classical.propDecidable _)

private def legalGate (g : Gate) : Prop :=
  g.inputs.length ≤ 2 ∧
    (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1))

private def wiresOf (gs : List Gate) (inp : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) inp

private lemma wiresOf_nil (inp : List Bool) : wiresOf [] inp = inp := rfl

private lemma wiresOf_append (gs1 gs2 : List Gate) (inp : List Bool) :
    wiresOf (gs1 ++ gs2) inp = wiresOf gs2 (wiresOf gs1 inp) := by
  simp [wiresOf, List.foldl_append]

private lemma wiresOf_cons (g : Gate) (gs : List Gate) (inp : List Bool) :
    wiresOf (g :: gs) inp =
      wiresOf gs (inp ++ [g.op.eval (g.inputs.map fun i => inp.getD i false)]) := rfl

private lemma wiresOf_append_singleton (gs : List Gate) (g : Gate) (inp : List Bool) :
    wiresOf (gs ++ [g]) inp =
      wiresOf gs inp ++ [g.op.eval (g.inputs.map fun i => (wiresOf gs inp).getD i false)] := by
  simp [wiresOf]

private lemma wiresOf_length (gs : List Gate) (inp : List Bool) :
    (wiresOf gs inp).length = inp.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [wiresOf]
  | append_singleton gs g ih =>
    rw [wiresOf_append_singleton, List.length_append, List.length_singleton, ih,
      List.length_append, List.length_singleton]
    omega

private lemma getD_append_left {α : Type*} (l1 l2 : List α) (i : ℕ) (d : α) (hi : i < l1.length) :
    (l1 ++ l2).getD i d = l1.getD i d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private lemma getD_append_right {α : Type*} (l1 l2 : List α) (i : ℕ) (d : α) (hi : l1.length ≤ i) :
    (l1 ++ l2).getD i d = l2.getD (i - l1.length) d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hi]

private lemma getD_append_singleton (l : List Bool) (b : Bool) (w : ℕ) :
    (l ++ [b]).getD w false =
      if w < l.length then l.getD w false else if w = l.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases hlt : w < l.length
  · simp only [hlt, ↓reduceIte, List.getElem?_append_left hlt]
  · by_cases heq : w = l.length
    · subst heq
      simp only [lt_irrefl, ↓reduceIte, List.getElem?_append_right (le_refl _), Nat.sub_self,
        List.getElem?_cons_zero, Option.getD_some]
    · have hnone : (l ++ [b])[w]? = none := List.getElem?_eq_none (by simp; omega)
      simp only [hlt, heq, ↓reduceIte, hnone, Option.getD_none]

private lemma getD_wiresOf_prefix (gs1 gs2 : List Gate) (inp : List Bool) (w : ℕ)
    (hw : w < inp.length + gs1.length) :
    (wiresOf (gs1 ++ gs2) inp).getD w false = (wiresOf gs1 inp).getD w false := by
  induction gs2 using List.reverseRecOn with
  | nil => simp
  | append_singleton gs2 g ih =>
    rw [← List.append_assoc, wiresOf_append_singleton, getD_append_left]
    · exact ih
    · rw [wiresOf_length, List.length_append]; omega

private lemma getD_wiresOf_init (gs : List Gate) (inp : List Bool) (w : ℕ) (hw : w < inp.length) :
    (wiresOf gs inp).getD w false = inp.getD w false := by
  have := getD_wiresOf_prefix [] gs inp w (by simp; exact hw)
  simpa [wiresOf_nil] using this

private lemma gateAt_eq_getElem (C : Circ) (j : ℕ) (hj : j < C.gates.length) :
    PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := by
  simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hj]

private lemma readsBack_iff (nW : ℕ) (C : Circ) :
    PEqualNP.MetaComplexity.NestedCover.ReadsBack nW C ↔
      ∀ (j : ℕ) (hj : j < C.gates.length), ∀ i ∈ (C.gates[j]).inputs, i < nW + j := by
  constructor
  · intro h j hj i hi
    have := h j hj i
    rw [gateAt_eq_getElem C j hj] at this
    exact this hi
  · intro h j hj i hi
    rw [gateAt_eq_getElem C j hj] at hi
    exact h j hj i hi

private lemma legal_const_false : legalGate ⟨.or, []⟩ := ⟨by simp, Or.inr (Or.inl rfl)⟩
private lemma legal_const_true : legalGate ⟨.and, []⟩ := ⟨by simp, Or.inl rfl⟩
private lemma legal_copy (i : ℕ) : legalGate ⟨.or, [i]⟩ := ⟨by simp, Or.inr (Or.inl rfl)⟩
private lemma legal_not (i : ℕ) : legalGate ⟨.not, [i]⟩ := ⟨by simp, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
private lemma legal_xnor (i j : ℕ) : legalGate ⟨.mod 2, [i, j]⟩ := ⟨by simp, Or.inr (Or.inr (Or.inl rfl))⟩

private lemma isNL_const_false : isNL ⟨.or, []⟩ = false := by simp [isNL]
private lemma isNL_const_true : isNL ⟨.and, []⟩ = false := by simp [isNL]
private lemma isNL_copy (i : ℕ) : isNL ⟨.or, [i]⟩ = false := by simp [isNL]
private lemma isNL_not (i : ℕ) : isNL ⟨.not, [i]⟩ = false := by simp [isNL]
private lemma isNL_xnor (i j : ℕ) : isNL ⟨.mod 2, [i, j]⟩ = false := by simp [isNL]

private lemma eval_xnor_not (a b : Bool) :
    PEqualNP.CircuitLowerBounds.GateOp.eval .not
      [PEqualNP.CircuitLowerBounds.GateOp.eval (.mod 2) [a, b]] = Bool.xor a b := by
  cases a <;> cases b <;> decide

private lemma eval_mod2_two_xor (a1 a2 b1 b2 u : Bool) :
    PEqualNP.CircuitLowerBounds.GateOp.eval (.mod 2) [Bool.xor (a1 && u) b1, Bool.xor (a2 && u) b2] =
      Bool.xor (Bool.xor a1 a2 && u) (PEqualNP.CircuitLowerBounds.GateOp.eval (.mod 2) [b1, b2]) := by
  cases a1 <;> cases a2 <;> cases b1 <;> cases b2 <;> cases u <;> decide

private lemma eval_mod2_one_xor (a1 b1 u : Bool) :
    PEqualNP.CircuitLowerBounds.GateOp.eval (.mod 2) [Bool.xor (a1 && u) b1] =
      Bool.xor (a1 && u) (PEqualNP.CircuitLowerBounds.GateOp.eval (.mod 2) [b1]) := by
  cases a1 <;> cases b1 <;> cases u <;> decide

private lemma eval_not_one_xor (a1 b1 u : Bool) :
    PEqualNP.CircuitLowerBounds.GateOp.eval .not [Bool.xor (a1 && u) b1] =
      Bool.xor (a1 && u) (PEqualNP.CircuitLowerBounds.GateOp.eval .not [b1]) := by
  cases a1 <;> cases b1 <;> cases u <;> decide

private def gateSlope (sl : ℕ → Bool) (g : Gate) : Bool :=
  match g.op, g.inputs with
  | .and, [i] => sl i
  | .or, [i] => sl i
  | .not, [i] => sl i
  | .mod 2, [i] => sl i
  | .mod 2, [i, j] => Bool.xor (sl i) (sl j)
  | _, _ => false

private def slopesList (nW : ℕ) : List Gate → (ℕ → Bool)
  | [] => fun w => decide (w = 0)
  | g :: gs =>
    let sl0 := slopesList nW gs
    fun w => if w = nW + gs.length then gateSlope sl0 g else sl0 w

private def slopesOf (nW : ℕ) (gs : List Gate) : ℕ → Bool :=
  slopesList nW gs.reverse

private lemma slopesOf_nil (nW : ℕ) : slopesOf nW [] = fun w => decide (w = 0) := rfl

private lemma slopesOf_append_singleton (nW : ℕ) (gs : List Gate) (g : Gate) :
    slopesOf nW (gs ++ [g]) =
      fun w => if w = nW + gs.length then gateSlope (slopesOf nW gs) g else slopesOf nW gs w := by
  simp [slopesOf, slopesList]

private lemma slopesOf_eq_false_ge (nW : ℕ) (gs : List Gate) (w : ℕ) (hw : nW + gs.length ≤ w)
    (hnW : 0 < nW) :
    slopesOf nW gs w = false := by
  induction gs using List.reverseRecOn with
  | nil =>
    rw [slopesOf_nil]; simp only [List.length_nil, add_zero] at hw
    simp [show w ≠ 0 by omega]
  | append_singleton gs g ih =>
    rw [slopesOf_append_singleton]
    simp only [List.length_append, List.length_singleton] at hw
    have hne : w ≠ nW + gs.length := by omega
    simp only [hne, ↓reduceIte]
    exact ih (by omega)

private lemma slopesOf_prefix (nW : ℕ) (gs1 gs2 : List Gate) (w : ℕ) (hw : w < nW + gs1.length) :
    slopesOf nW (gs1 ++ gs2) w = slopesOf nW gs1 w := by
  induction gs2 using List.reverseRecOn with
  | nil => simp
  | append_singleton gs2 g ih =>
    rw [← List.append_assoc, slopesOf_append_singleton]
    have hne : w ≠ nW + (gs1 ++ gs2).length := by rw [List.length_append]; omega
    simp only [hne, ↓reduceIte]
    exact ih

private def GoodPrefix (nW : ℕ) (gs : List Gate) : Prop :=
  ∀ (j : ℕ) (hj : j < gs.length),
    isNL gs[j] = true → ∀ i ∈ (gs[j]).inputs, slopesOf nW (gs.take j) i = false

private lemma eval_goodPrefix (t : ℕ) (gs : List Gate)
    (hleg : ∀ g ∈ gs, legalGate g)
    (hrb : ∀ (j : ℕ) (hj : j < gs.length), ∀ i ∈ (gs[j]).inputs, i < 1 + t + j)
    (hgood : GoodPrefix (1 + t) gs)
    (u : Bool) (z : Fin t → Bool) (w : ℕ) :
    (wiresOf gs (u :: List.ofFn z)).getD w false =
      Bool.xor (slopesOf (1 + t) gs w && u) ((wiresOf gs (false :: List.ofFn z)).getD w false) := by
  revert w
  induction gs using List.reverseRecOn with
  | nil =>
    intro w
    rw [wiresOf_nil, wiresOf_nil, slopesOf_nil]
    cases w with
    | zero => simp
    | succ w' => simp [List.getD_eq_getElem?_getD]
  | append_singleton gs g ih =>
    intro w
    have hleg_gs : ∀ g' ∈ gs, legalGate g' := fun g' hg' => hleg g' (List.mem_append_left _ hg')
    have hleg_g : legalGate g := hleg g (List.mem_append_right _ (List.mem_singleton_self g))
    have hrb_gs : ∀ (j : ℕ) (hj : j < gs.length), ∀ i ∈ (gs[j]).inputs, i < 1 + t + j := by
      intro j hj i hi
      have hj' : j < (gs ++ [g]).length := by simp; omega
      have hget : (gs ++ [g])[j]'hj' = gs[j]'hj := List.getElem_append_left hj
      exact hrb j hj' i (by rw [hget]; exact hi)
    have hgood_gs : GoodPrefix (1 + t) gs := by
      intro j hj hnl i hi
      have hj' : j < (gs ++ [g]).length := by simp; omega
      have hget : (gs ++ [g])[j]'hj' = gs[j]'hj := List.getElem_append_left hj
      have htake : (gs ++ [g]).take j = gs.take j := List.take_append_of_le_length (by omega)
      rw [← htake]
      exact hgood j hj' (by rw [hget]; exact hnl) i (by rw [hget]; exact hi)
    have ih' := ih hleg_gs hrb_gs hgood_gs
    have hlen_u : (wiresOf gs (u :: List.ofFn z)).length = 1 + t + gs.length := by
      rw [wiresOf_length]; simp; omega
    have hlen_f : (wiresOf gs (false :: List.ofFn z)).length = 1 + t + gs.length := by
      rw [wiresOf_length]; simp; omega
    rw [wiresOf_append_singleton, wiresOf_append_singleton, getD_append_singleton,
      getD_append_singleton, hlen_u, hlen_f, slopesOf_append_singleton]
    by_cases hlt : w < 1 + t + gs.length
    · have hne : w ≠ 1 + t + gs.length := by omega
      simp only [hlt, hne, ↓reduceIte]
      exact ih' w
    · by_cases heq : w = 1 + t + gs.length
      · subst heq
        simp only [lt_irrefl, ↓reduceIte]
        rcases hleg_g with ⟨hlen2, hop⟩
        have hj' : gs.length < (gs ++ [g]).length := by simp
        have hget : (gs ++ [g])[gs.length]'hj' = g := by simp
        have htake : (gs ++ [g]).take gs.length = gs := by simp
        rcases hop with hop | hop | hop | ⟨hop, hlen1⟩
        · cases hgi : g.inputs with
          | nil =>
            simp [hop, hgi, gateSlope, PEqualNP.CircuitLowerBounds.GateOp.eval]
          | cons i rest =>
            cases rest with
            | nil =>
              simp only [hop, hgi, gateSlope, List.map_cons, List.map_nil,
                PEqualNP.CircuitLowerBounds.GateOp.eval, List.all_cons, List.all_nil, id_eq,
                Bool.and_true]
              exact ih' i
            | cons j rest2 =>
              cases rest2 with
              | nil =>
                have hnl : isNL g = true := by simp [isNL, hop, hgi]
                have hsi : slopesOf (1 + t) gs i = false := by
                  rw [← htake]
                  exact hgood gs.length hj' (by rw [hget]; exact hnl) i (by rw [hget, hgi]; simp)
                have hsj : slopesOf (1 + t) gs j = false := by
                  rw [← htake]
                  exact hgood gs.length hj' (by rw [hget]; exact hnl) j (by rw [hget, hgi]; simp)
                simp only [hop, hgi, gateSlope, List.map_cons, List.map_nil, ih' i, ih' j, hsi, hsj,
                  Bool.false_and, Bool.false_xor]
              | cons _ _ => simp [hgi] at hlen2
        · cases hgi : g.inputs with
          | nil =>
            simp [hop, hgi, gateSlope, PEqualNP.CircuitLowerBounds.GateOp.eval]
          | cons i rest =>
            cases rest with
            | nil =>
              simp only [hop, hgi, gateSlope, List.map_cons, List.map_nil,
                PEqualNP.CircuitLowerBounds.GateOp.eval, List.any_cons, List.any_nil, id_eq,
                Bool.or_false]
              exact ih' i
            | cons j rest2 =>
              cases rest2 with
              | nil =>
                have hnl : isNL g = true := by simp [isNL, hop, hgi]
                have hsi : slopesOf (1 + t) gs i = false := by
                  rw [← htake]
                  exact hgood gs.length hj' (by rw [hget]; exact hnl) i (by rw [hget, hgi]; simp)
                have hsj : slopesOf (1 + t) gs j = false := by
                  rw [← htake]
                  exact hgood gs.length hj' (by rw [hget]; exact hnl) j (by rw [hget, hgi]; simp)
                simp only [hop, hgi, gateSlope, List.map_cons, List.map_nil, ih' i, ih' j, hsi, hsj,
                  Bool.false_and, Bool.false_xor]
              | cons _ _ => simp [hgi] at hlen2
        · cases hgi : g.inputs with
          | nil =>
            simp [hop, hgi, gateSlope, PEqualNP.CircuitLowerBounds.GateOp.eval]
          | cons i rest =>
            cases rest with
            | nil =>
              simp only [hop, hgi, gateSlope, List.map_cons, List.map_nil, ih' i]
              exact eval_mod2_one_xor _ _ u
            | cons j rest2 =>
              cases rest2 with
              | nil =>
                simp only [hop, hgi, gateSlope, List.map_cons, List.map_nil, ih' i, ih' j]
                exact eval_mod2_two_xor _ _ _ _ u
              | cons _ _ => simp [hgi] at hlen2
        · cases hgi : g.inputs with
          | nil => simp [hgi] at hlen1
          | cons i rest =>
            cases rest with
            | nil =>
              simp only [hop, hgi, gateSlope, List.map_cons, List.map_nil, ih' i]
              exact eval_not_one_xor _ _ u
            | cons _ _ => simp [hgi] at hlen1
      · simp only [hlt, heq, ↓reduceIte]
        have hsf : slopesOf (1 + t) gs w = false := slopesOf_eq_false_ge (1 + t) gs w (by omega) (by omega)
        simp [hsf]

private lemma countP_map_remap (gs : List Gate) (f : ℕ → ℕ) :
    (gs.map fun g => (⟨g.op, g.inputs.map f⟩ : Gate)).countP isNL = gs.countP isNL := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, List.countP_cons, ih]
    congr 1
    by_cases h : (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2
    · simp [isNL, h]
    · simp [isNL, h]

private lemma eval_mapped_gates (gs : List Gate) (f : ℕ → ℕ)
    (init1 init2 : List Bool) (n1 : ℕ) (hn1 : init1.length = n1)
    (hf : ∀ (j : ℕ) (hj : j < gs.length), ∀ i ∈ (gs[j]).inputs,
      i < n1 + j ∧ (i < n1 → f i < init2.length) ∧
      (∀ r < j, i = n1 + r → f i = init2.length + r))
    (hmatch : ∀ i < n1, init2.getD (f i) false = init1.getD i false)
    (hf_ge : ∀ r : ℕ, f (n1 + r) = init2.length + r) :
    ∀ (r : ℕ), r < gs.length →
      (wiresOf (gs.map fun g => ⟨g.op, g.inputs.map f⟩) init2).getD (init2.length + r) false =
        (wiresOf gs init1).getD (n1 + r) false := by
  induction gs using List.reverseRecOn with
  | nil => intro r hr; simp at hr
  | append_singleton gs g ih =>
    have hf_gs : ∀ (j : ℕ) (hj : j < gs.length), ∀ i ∈ (gs[j]).inputs,
        i < n1 + j ∧ (i < n1 → f i < init2.length) ∧
        (∀ r < j, i = n1 + r → f i = init2.length + r) := by
      intro j hj i hi
      have hj' : j < (gs ++ [g]).length := by simp; omega
      have hget : (gs ++ [g])[j]'hj' = gs[j]'hj := List.getElem_append_left hj
      exact hf j hj' i (by rw [hget]; exact hi)
    have ih' := ih hf_gs
    intro r hr
    simp only [List.map_append, List.map_singleton, wiresOf_append_singleton]
    have hlen1 : (wiresOf gs init1).length = n1 + gs.length := by rw [wiresOf_length, hn1]
    have hlen2 : (wiresOf (gs.map fun g => ⟨g.op, g.inputs.map f⟩) init2).length =
        init2.length + gs.length := by rw [wiresOf_length, List.length_map]
    rw [getD_append_singleton, getD_append_singleton, hlen1, hlen2]
    simp only [List.length_append, List.length_singleton] at hr
    by_cases hlt : r < gs.length
    · have h1 : init2.length + r < init2.length + gs.length := by omega
      have h2 : n1 + r < n1 + gs.length := by omega
      simp only [h1, h2, ↓reduceIte]
      exact ih' r hlt
    · have heq : r = gs.length := by omega
      subst heq
      simp only [lt_irrefl, ↓reduceIte]
      congr 1
      rw [List.map_map]
      refine List.map_congr_left fun i hi => ?_
      have hj' : gs.length < (gs ++ [g]).length := by simp
      have hget : (gs ++ [g])[gs.length]'hj' = g := by simp
      have hfi := (hf gs.length hj' i (by rw [hget]; exact hi)).1
      dsimp only [Function.comp_apply]
      by_cases hi1 : i < n1
      · have hfi_lt : f i < init2.length := (hf gs.length hj' i (by rw [hget]; exact hi)).2.1 hi1
        rw [getD_wiresOf_init _ init2 (f i) hfi_lt, getD_wiresOf_init _ init1 i (by omega)]
        exact hmatch i hi1
      · have hsub : i - n1 < gs.length := by omega
        have heq_i : i = n1 + (i - n1) := by omega
        rw [heq_i, hf_ge (i - n1)]
        exact ih' (i - n1) hsub

private lemma build_case1 (t : ℕ) (C : Circ)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack (1 + t) C)
    (hleg : ∀ g ∈ C.gates, legalGate g)
    (hgood : GoodPrefix (1 + t) C.gates) :
    ∃ (a : Bool) (E : Circ),
      (PEqualNP.MetaComplexity.NestedCover.ReadsBack t E ∧ ∀ g ∈ E.gates, legalGate g) ∧
      E.gates.countP isNL ≤ C.gates.countP isNL ∧
      ∀ (u : Bool) (z : Fin t → Bool),
        C.eval (u :: List.ofFn z) = Bool.xor (a && u) (E.eval (List.ofFn z)) := by
  have hrb' := (readsBack_iff (1 + t) C).mp hrb
  let remap : ℕ → ℕ := fun i =>
    if i = 0 then t else if i < 1 + t then i - 1 else i
  let gatesE : List Gate := ⟨.or, []⟩ :: C.gates.map (fun g => ⟨g.op, g.inputs.map remap⟩)
  let outE : ℕ := if C.output < 1 + t + C.gates.length then remap C.output else t
  let E : Circ := ⟨gatesE, outE⟩
  refine ⟨slopesOf (1 + t) C.gates C.output, E, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [readsBack_iff]
    intro j hj i hi
    cases j with
    | zero =>
      dsimp only [E, gatesE] at hi
      simp at hi
    | succ j' =>
      dsimp only [E, gatesE] at hj hi
      simp only [List.length_cons, List.length_map] at hj
      have hjlt : j' < C.gates.length := by omega
      simp only [List.getElem_cons_succ, List.getElem_map, List.mem_map] at hi
      obtain ⟨i0, hi0, rfl⟩ := hi
      have hlt := hrb' j' hjlt i0 hi0
      dsimp only [remap]
      split_ifs <;> omega
  · intro g hg
    dsimp only [E, gatesE] at hg
    simp only [List.mem_cons, List.mem_map] at hg
    rcases hg with rfl | ⟨g0, hg0, rfl⟩
    · exact legal_const_false
    · rcases hleg g0 hg0 with ⟨hl, hop⟩
      refine ⟨by simpa using hl, ?_⟩
      simpa using hop
  · dsimp only [E, gatesE]
    rw [List.countP_cons, isNL_const_false, countP_map_remap]
    simp
  · intro u z
    have hmain := eval_goodPrefix t C.gates hleg hrb' hgood u z C.output
    change (wiresOf C.gates (u :: List.ofFn z)).getD C.output false =
      Bool.xor (slopesOf (1 + t) C.gates C.output && u) ((wiresOf gatesE (List.ofFn z)).getD outE false)
    rw [hmain]
    congr 1
    let init1 : List Bool := false :: List.ofFn z
    let init2 : List Bool := List.ofFn z ++ [false]
    have hE_eq : wiresOf gatesE (List.ofFn z) =
        wiresOf (C.gates.map fun g => ⟨g.op, g.inputs.map remap⟩) init2 := by
      dsimp only [gatesE, init2]
      rw [wiresOf_cons]
      rfl
    rw [hE_eq]
    have hinit1_len : init1.length = 1 + t := by simp [init1]; omega
    have hinit2_len : init2.length = t + 1 := by simp [init2]
    have hmap_ok := eval_mapped_gates C.gates remap init1 init2 (1 + t) hinit1_len
      (fun j hj i hi => by
        have hlt := hrb' j hj i hi
        refine ⟨hlt, ?_, ?_⟩
        · intro hi1; dsimp only [remap]; split_ifs <;> omega
        · intro r _ heq; dsimp only [remap]; split_ifs <;> omega)
      (fun i hi => by
        dsimp only [remap, init1, init2]
        by_cases hi0 : i = 0
        · subst hi0; simp
        · have hlt : i < 1 + t := hi
          simp only [hi0, hlt, ↓reduceIte]
          rw [getD_append_left _ _ _ _ (by simp; omega)]
          cases i with
          | zero => exact absurd rfl hi0
          | succ i' => simp [List.getD_eq_getElem?_getD])
      (fun r => by dsimp only [remap]; rw [hinit2_len]; split_ifs <;> omega)
    dsimp only [outE]
    by_cases hout : C.output < 1 + t + C.gates.length
    · simp only [hout, ↓reduceIte]
      by_cases h1 : C.output < 1 + t
      · have hlt2 : remap C.output < init2.length := by
          dsimp only [remap]; rw [hinit2_len]; split_ifs <;> omega
        rw [getD_wiresOf_init _ init2 (remap C.output) hlt2,
          getD_wiresOf_init _ init1 C.output (by omega)]
        dsimp only [remap, init1, init2]
        by_cases h0 : C.output = 0
        · rw [h0]; simp
        · simp only [h0, h1, ↓reduceIte]
          rw [getD_append_left _ _ _ _ (by simp; omega)]
          cases hco : C.output with
          | zero => exact absurd hco h0
          | succ i' => simp [List.getD_eq_getElem?_getD]
      · have hr : C.output - (1 + t) < C.gates.length := by omega
        have heq_o : C.output = 1 + t + (C.output - (1 + t)) := by omega
        have hrm : remap C.output = init2.length + (C.output - (1 + t)) := by
          dsimp only [remap]; rw [hinit2_len]; split_ifs <;> omega
        rw [hrm, hmap_ok (C.output - (1 + t)) hr, ← heq_o]
    · simp only [hout, ↓reduceIte]
      have hge1 : (wiresOf C.gates init1).length ≤ C.output := by rw [wiresOf_length, hinit1_len]; omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge1, Option.getD_none]
      have ht_lt : t < init2.length := by rw [hinit2_len]; omega
      rw [getD_wiresOf_init _ init2 t ht_lt]
      dsimp only [init2]
      rw [getD_append_right _ _ _ _ (by simp)]
      simp

private def mkReconGates (n0 wU : ℕ) (sl : ℕ → Bool) (t : ℕ) (j0 : ℕ) : List Gate :=
  (List.range j0).flatMap fun j =>
    if sl (1 + t + j) then
      [⟨.mod 2, [wU, n0 + j]⟩, ⟨.not, [wU + 1 + 2 * j]⟩]
    else
      [⟨.or, [n0 + j]⟩, ⟨.or, [n0 + j]⟩]

private lemma mkReconGates_length (n0 wU : ℕ) (sl : ℕ → Bool) (t j0 : ℕ) :
    (mkReconGates n0 wU sl t j0).length = 2 * j0 := by
  induction j0 with
  | zero => simp [mkReconGates]
  | succ j ih =>
    rw [mkReconGates, List.range_succ, List.flatMap_append, List.flatMap_singleton, List.length_append]
    change (mkReconGates n0 wU sl t j).length + _ = _
    rw [ih]
    split_ifs <;> simp <;> omega

private lemma mkReconGates_countP (n0 wU : ℕ) (sl : ℕ → Bool) (t j0 : ℕ) :
    (mkReconGates n0 wU sl t j0).countP isNL = 0 := by
  induction j0 with
  | zero => simp [mkReconGates]
  | succ j ih =>
    rw [mkReconGates, List.range_succ, List.flatMap_append, List.flatMap_singleton, List.countP_append]
    change (mkReconGates n0 wU sl t j).countP isNL + _ = 0
    rw [ih, zero_add]
    split_ifs <;> simp [isNL_xnor, isNL_not, isNL_copy]

private lemma mkReconGates_legal (n0 wU : ℕ) (sl : ℕ → Bool) (t j0 : ℕ) :
    ∀ g ∈ mkReconGates n0 wU sl t j0, legalGate g := by
  intro g hg
  simp only [mkReconGates, List.mem_flatMap, List.mem_range] at hg
  obtain ⟨j, _, hg⟩ := hg
  split_ifs at hg
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact legal_xnor _ _
    · exact legal_not _
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl <;> exact legal_copy _

private lemma mkReconGates_readsBack (n0 wU : ℕ) (sl : ℕ → Bool) (t j0 : ℕ)
    (h1 : n0 + j0 ≤ wU) :
    ∀ (idx : ℕ) (hidx : idx < (mkReconGates n0 wU sl t j0).length),
      ∀ i ∈ ((mkReconGates n0 wU sl t j0)[idx]).inputs, i < wU + 1 + idx := by
  induction j0 with
  | zero => intro idx hidx; simp [mkReconGates] at hidx
  | succ j ih =>
    intro idx hidx i hi
    have hsplit : mkReconGates n0 wU sl t (j + 1) =
        mkReconGates n0 wU sl t j ++
          (if sl (1 + t + j) then [⟨.mod 2, [wU, n0 + j]⟩, ⟨.not, [wU + 1 + 2 * j]⟩]
           else [⟨.or, [n0 + j]⟩, ⟨.or, [n0 + j]⟩]) := by
      simp [mkReconGates, List.range_succ, List.flatMap_append]
    have hlenj : (mkReconGates n0 wU sl t j).length = 2 * j := mkReconGates_length n0 wU sl t j
    by_cases hlt : idx < 2 * j
    · have hidx' : idx < (mkReconGates n0 wU sl t j).length := by omega
      have hget : (mkReconGates n0 wU sl t (j + 1))[idx] = (mkReconGates n0 wU sl t j)[idx] := by
        simp only [hsplit]; exact List.getElem_append_left hidx'
      rw [hget] at hi
      exact ih (by omega) idx hidx' i hi
    · have hget : (mkReconGates n0 wU sl t (j + 1))[idx] =
          (if sl (1 + t + j) then [⟨.mod 2, [wU, n0 + j]⟩, ⟨.not, [wU + 1 + 2 * j]⟩]
           else [⟨.or, [n0 + j]⟩, ⟨.or, [n0 + j]⟩])[idx - 2 * j]'(by
            have := mkReconGates_length n0 wU sl t (j + 1); split_ifs <;> simp <;> omega) := by
        simp only [hsplit]
        rw [List.getElem_append_right (by omega)]
        congr 1; omega
      rw [hget] at hi
      have hlen1 := mkReconGates_length n0 wU sl t (j + 1)
      have hcases : idx - 2 * j = 0 ∨ idx - 2 * j = 1 := by omega
      rcases hcases with h0 | h1'
      · split_ifs at hi <;> simp only [h0, List.getElem_cons_zero, List.mem_cons,
          List.not_mem_nil, or_false] at hi <;> rcases hi with rfl | rfl <;> omega
      · split_ifs at hi <;> simp only [h1', List.getElem_cons_succ, List.getElem_cons_zero,
          List.mem_cons, List.not_mem_nil, or_false] at hi <;> subst hi <;> omega

private lemma mkReconGates_eval (n0 wU : ℕ) (sl : ℕ → Bool) (t j0 : ℕ)
    (init : List Bool) (hinit : init.length = wU + 1) (h1 : n0 + j0 ≤ wU) :
    ∀ j < j0,
      (wiresOf (mkReconGates n0 wU sl t j0) init).getD (wU + 1 + 2 * j + 1) false =
        Bool.xor (sl (1 + t + j) && init.getD wU false) (init.getD (n0 + j) false) := by
  induction j0 with
  | zero => intro j hj; omega
  | succ k ih =>
    have hsplit : mkReconGates n0 wU sl t (k + 1) =
        mkReconGates n0 wU sl t k ++
          (if sl (1 + t + k) then [⟨.mod 2, [wU, n0 + k]⟩, ⟨.not, [wU + 1 + 2 * k]⟩]
           else [⟨.or, [n0 + k]⟩, ⟨.or, [n0 + k]⟩]) := by
      simp [mkReconGates, List.range_succ, List.flatMap_append]
    intro j hj
    rw [hsplit]
    by_cases hlt : j < k
    · rw [getD_wiresOf_prefix]
      · exact ih (by omega) j hlt
      · rw [hinit, mkReconGates_length]; omega
    · have heq : j = k := by omega
      subst j
      rw [wiresOf_append]
      let base := wiresOf (mkReconGates n0 wU sl t k) init
      have hblen : base.length = wU + 1 + 2 * k := by
        dsimp only [base]; rw [wiresOf_length, hinit, mkReconGates_length]
      have hgetU : base.getD wU false = init.getD wU false :=
        getD_wiresOf_init _ init wU (by omega)
      have hgetK : base.getD (n0 + k) false = init.getD (n0 + k) false :=
        getD_wiresOf_init _ init (n0 + k) (by omega)
      cases hsl : sl (1 + t + k) with
      | true =>
        simp only [↓reduceIte, wiresOf_cons, wiresOf_nil]
        change ((base ++ [PEqualNP.CircuitLowerBounds.GateOp.eval (.mod 2) [base.getD wU false, base.getD (n0 + k) false]]) ++
          [PEqualNP.CircuitLowerBounds.GateOp.eval .not [(base ++ [PEqualNP.CircuitLowerBounds.GateOp.eval (.mod 2) [base.getD wU false, base.getD (n0 + k) false]]).getD (wU + 1 + 2 * k) false]]).getD (wU + 1 + 2 * k + 1) false = _
        have hlen1 : (base ++ [PEqualNP.CircuitLowerBounds.GateOp.eval (.mod 2) [base.getD wU false, base.getD (n0 + k) false]]).length =
            wU + 1 + 2 * k + 1 := by rw [List.length_append, List.length_singleton, hblen]
        rw [getD_append_singleton, hlen1]
        simp only [lt_irrefl, ↓reduceIte]
        rw [getD_append_singleton, hblen]
        simp only [lt_irrefl, ↓reduceIte, hgetU, hgetK, Bool.true_and]
        exact eval_xnor_not _ _
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, wiresOf_cons, wiresOf_nil]
        change ((base ++ [PEqualNP.CircuitLowerBounds.GateOp.eval .or [base.getD (n0 + k) false]]) ++
          [PEqualNP.CircuitLowerBounds.GateOp.eval .or [(base ++ [PEqualNP.CircuitLowerBounds.GateOp.eval .or [base.getD (n0 + k) false]]).getD (n0 + k) false]]).getD (wU + 1 + 2 * k + 1) false = _
        have hlen1 : (base ++ [PEqualNP.CircuitLowerBounds.GateOp.eval .or [base.getD (n0 + k) false]]).length =
            wU + 1 + 2 * k + 1 := by rw [List.length_append, List.length_singleton, hblen]
        rw [getD_append_singleton, hlen1]
        simp only [lt_irrefl, ↓reduceIte]
        rw [getD_append_left _ _ _ _ (by omega), hgetK]
        simp [PEqualNP.CircuitLowerBounds.GateOp.eval]

private lemma build_case2 (t : ℕ) (C : Circ)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack (1 + t) C)
    (hleg : ∀ g ∈ C.gates, legalGate g)
    (hnotgood : ¬GoodPrefix (1 + t) C.gates) :
    0 < C.gates.countP isNL ∧ ∃ p : (Fin t → Bool) → Bool,
      ∀ (b d : Bool), ∃ D : Circ,
        (PEqualNP.MetaComplexity.NestedCover.ReadsBack t D ∧ ∀ g ∈ D.gates, legalGate g) ∧
        D.gates.countP isNL < C.gates.countP isNL ∧
        ∀ z : Fin t → Bool, let u := Bool.xor (p z) b
          D.eval (List.ofFn z) = Bool.xor (C.eval (u :: List.ofFn z)) (d && u) := by
  classical
  have hrb' := (readsBack_iff (1 + t) C).mp hrb
  have hex_bad : ∃ j : ℕ, ∃ hj : j < C.gates.length,
      isNL (C.gates[j]'hj) = true ∧ ∃ i ∈ (C.gates[j]'hj).inputs, slopesOf (1 + t) (C.gates.take j) i = true := by
    by_contra hnot
    apply hnotgood
    intro j hj hnl i hi
    rcases Bool.eq_false_or_eq_true (slopesOf (1 + t) (C.gates.take j) i) with ht | hf
    · exact absurd ⟨j, hj, hnl, i, hi, ht⟩ hnot
    · exact hf
  let j0 : ℕ := Nat.find hex_bad
  have hj0_spec := Nat.find_spec hex_bad
  have hj0_lt : j0 < C.gates.length := hj0_spec.1
  let g0 : Gate := C.gates[j0]
  have hg0_nl : isNL g0 = true := hj0_spec.2.1
  have hg0_bad_in : ∃ i ∈ g0.inputs, slopesOf (1 + t) (C.gates.take j0) i = true := hj0_spec.2.2
  let pre : List Gate := C.gates.take j0
  let suf : List Gate := C.gates.drop (j0 + 1)
  have hpre_len : pre.length = j0 := List.length_take_of_le (by omega)
  have hsplit_C : C.gates = pre ++ [g0] ++ suf := by
    have h1 := (List.take_append_drop j0 C.gates).symm
    have h2 : C.gates.drop j0 = g0 :: suf := List.drop_eq_getElem_cons hj0_lt
    rw [h1, h2]
    simp [pre, suf]
  have hcost_C : C.gates.countP isNL = pre.countP isNL + 1 + suf.countP isNL := by
    rw [hsplit_C, List.countP_append, List.countP_append, List.countP_singleton, hg0_nl]
    simp
  have hcost_pos : 0 < C.gates.countP isNL := by omega
  have hgood_pre : GoodPrefix (1 + t) pre := by
    intro j hj hnl i hi
    have hj_lt : j < j0 := by omega
    have hj_C : j < C.gates.length := by omega
    have hget : pre[j] = C.gates[j] := List.getElem_take
    have htake : pre.take j = C.gates.take j := by
      dsimp only [pre]; rw [List.take_take, Nat.min_eq_left (by omega)]
    rw [htake]
    by_contra hne
    have ht : slopesOf (1 + t) (C.gates.take j) i = true := by
      rcases Bool.eq_false_or_eq_true (slopesOf (1 + t) (C.gates.take j) i) with ht' | hf'
      · exact ht'
      · exact absurd hf' hne
    exact Nat.find_min hex_bad hj_lt ⟨hj_C, by rw [← hget]; exact hnl, i, by rw [← hget]; exact hi, ht⟩
  have hleg_pre : ∀ g ∈ pre, legalGate g := fun g hg => hleg g (List.mem_of_mem_take hg)
  have hleg_suf : ∀ g ∈ suf, legalGate g := fun g hg => hleg g (List.mem_of_mem_drop hg)
  have hrb_pre : ∀ (j : ℕ) (hj : j < pre.length), ∀ i ∈ (pre[j]).inputs, i < 1 + t + j := by
    intro j hj i hi
    have hj_C : j < C.gates.length := by omega
    have hget : pre[j] = C.gates[j] := List.getElem_take
    exact hrb' j hj_C i (by rw [← hget]; exact hi)
  have hg0_nl' : (g0.op = .and ∨ g0.op = .or) ∧ g0.inputs.length = 2 := by simpa [isNL] using hg0_nl
  have hg0_inputs : ∃ i1 i2 : ℕ, g0.inputs = [i1, i2] := by
    cases hgi : g0.inputs with
    | nil => simp [hgi] at hg0_nl'
    | cons i1 r1 =>
      cases r1 with
      | nil => simp [hgi] at hg0_nl'
      | cons i2 r2 =>
        cases r2 with
        | nil => exact ⟨i1, i2, rfl⟩
        | cons _ _ => simp [hgi] at hg0_nl'
  obtain ⟨i1, i2, hg0_eq⟩ := hg0_inputs
  have hi1_lt : i1 < 1 + t + j0 := hrb' j0 hj0_lt i1 (by rw [hg0_eq]; simp)
  have hi2_lt : i2 < 1 + t + j0 := hrb' j0 hj0_lt i2 (by rw [hg0_eq]; simp)
  have hsel : ∃ iSel iOth : ℕ,
      ((iSel = i1 ∧ iOth = i2) ∨ (iSel = i2 ∧ iOth = i1)) ∧
      slopesOf (1 + t) pre iSel = true := by
    obtain ⟨i, hi, hsl⟩ := hg0_bad_in
    rw [hg0_eq] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi1 | hi2
    · rw [hi1] at hsl; exact ⟨i1, i2, Or.inl ⟨rfl, rfl⟩, hsl⟩
    · rw [hi2] at hsl; exact ⟨i2, i1, Or.inr ⟨rfl, rfl⟩, hsl⟩
  obtain ⟨iSel, iOth, hpair, hsel_slope⟩ := hsel
  have hiSel_lt : iSel < 1 + t + j0 := by rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  have hiOth_lt : iOth < 1 + t + j0 := by rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  let p : (Fin t → Bool) → Bool := fun z => (wiresOf pre (false :: List.ofFn z)).getD iSel false
  refine ⟨hcost_pos, p, fun b d => ?_⟩
  let remap0 : ℕ → ℕ := fun i =>
    if i = 0 then t else if i < 1 + t then i - 1 else i + 1
  let wP : ℕ := remap0 iSel
  let wU : ℕ := t + 2 + j0
  let gU : Gate := if b then ⟨.not, [wP]⟩ else ⟨.or, [wP]⟩
  let sl := slopesOf (1 + t) pre
  let recon := mkReconGates (t + 2) wU sl t j0
  let wG0 : ℕ := wU + 1 + 2 * j0
  let remapU : ℕ → ℕ := fun i =>
    if i = 0 then wU
    else if i < 1 + t then i - 1
    else if i < 1 + t + j0 then wU + 1 + 2 * (i - (1 + t)) + 1
    else if i = 1 + t + j0 then wG0
    else wG0 + (i - (1 + t + j0))
  let g0_rep : Gate :=
    match g0.op, b with
    | .and, false => ⟨.or, []⟩
    | .and, true => ⟨.or, [remapU iOth]⟩
    | .or, false => ⟨.or, [remapU iOth]⟩
    | .or, true => ⟨.and, []⟩
    | _, _ => ⟨.or, []⟩
  let pre_mapped : List Gate := pre.map (fun g => ⟨g.op, g.inputs.map remap0⟩)
  let suf_mapped : List Gate := suf.map (fun g => ⟨g.op, g.inputs.map remapU⟩)
  let baseGates : List Gate := [⟨.or, []⟩, ⟨.and, []⟩] ++ pre_mapped ++ [gU] ++ recon ++ [g0_rep] ++ suf_mapped
  have hbase_len : baseGates.length = 2 + j0 + 1 + 2 * j0 + 1 + suf.length := by
    simp only [baseGates, pre_mapped, suf_mapped, recon, List.length_append, List.length_cons,
      List.length_nil, List.length_map, hpre_len, mkReconGates_length]
  let wOut : ℕ := if C.output < 1 + t + C.gates.length then remapU C.output else t
  let corrGates : List Gate :=
    if d then [⟨.mod 2, [wOut, wU]⟩, ⟨.not, [t + baseGates.length]⟩] else []
  let gatesD : List Gate := baseGates ++ corrGates
  let outD : ℕ := if d then t + baseGates.length + 1 else wOut
  let D : Circ := ⟨gatesD, outD⟩
  have hremap0_lt : ∀ i < 1 + t + j0, remap0 i < wU := by
    intro i hi; dsimp only [remap0, wU]; split_ifs <;> omega
  have hremapU_lt_g0 : ∀ i < 1 + t + j0, remapU i < wG0 := by
    intro i hi; dsimp only [remapU, wG0, wU]; split_ifs <;> omega
  have hremapU_lt_end : ∀ i < 1 + t + C.gates.length, remapU i < t + baseGates.length := by
    intro i hi
    have hClen : C.gates.length = j0 + 1 + suf.length := by
      rw [hsplit_C]; simp [hpre_len]; omega
    dsimp only [remapU, wG0, wU]
    rw [hbase_len]
    split_ifs <;> omega
  have hwOut_lt : wOut < t + baseGates.length := by
    dsimp only [wOut]
    split_ifs with h
    · exact hremapU_lt_end C.output h
    · rw [hbase_len]; omega
  refine ⟨D, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [readsBack_iff]
    intro j hj i hi
    dsimp only [D, gatesD] at hj hi
    by_cases hjb : j < baseGates.length
    · rw [List.getElem_append_left hjb] at hi
      have h1len : ([⟨.or, []⟩, ⟨.and, []⟩] : List Gate).length = 2 := rfl
      have h2len : pre_mapped.length = j0 := by simp [pre_mapped, hpre_len]
      have h3len : ([gU] : List Gate).length = 1 := rfl
      have h4len : recon.length = 2 * j0 := mkReconGates_length (t + 2) wU sl t j0
      have h5len : ([g0_rep] : List Gate).length = 1 := rfl
      have h6len : suf_mapped.length = suf.length := by simp [suf_mapped]
      by_cases c1 : j < 2
      · have hget : baseGates[j]'(by omega) = ([⟨.or, []⟩, ⟨.and, []⟩] : List Gate)[j]'c1 := by
          dsimp only [baseGates]
          repeat rw [List.getElem_append_left (by simp [h2len, h4len, h6len]; omega)]
        rw [hget] at hi
        cases j with
        | zero => simp at hi
        | succ j' => cases j' with
          | zero => simp at hi
          | succ _ => omega
      · by_cases c2 : j < 2 + j0
        · have hj' : j - 2 < pre.length := by omega
          have hget : baseGates[j]'(by omega) = pre_mapped[j - 2]'(by omega) := by
            dsimp only [baseGates]
            rw [List.getElem_append_left (by simp [h2len, h4len, h6len]; omega)]
            rw [List.getElem_append_left (by simp [h2len, h4len]; omega)]
            rw [List.getElem_append_left (by simp [h2len, h4len]; omega)]
            rw [List.getElem_append_left (by simp [h2len]; omega)]
            rw [List.getElem_append_right (by simp; omega)]
            rfl
          rw [hget] at hi
          simp only [pre_mapped, List.getElem_map, List.mem_map] at hi
          obtain ⟨i0, hi0, rfl⟩ := hi
          have hlt0 := hrb_pre (j - 2) hj' i0 hi0
          dsimp only [remap0]
          split_ifs <;> omega
        · by_cases c3 : j = 2 + j0
          · subst c3
            have hget : baseGates[2 + j0]'(by omega) = gU := by
              dsimp only [baseGates]
              rw [List.getElem_append_left (by simp [h2len, h4len, h6len]; omega)]
              rw [List.getElem_append_left (by simp [h2len, h4len]; omega)]
              rw [List.getElem_append_left (by simp [h2len, h4len]; omega)]
              rw [List.getElem_append_right (by simp [h2len]; omega)]
              have hsub : 2 + j0 - (2 + j0) = 0 := by omega
              simp [h2len]
            rw [hget] at hi
            dsimp only [gU] at hi
            split_ifs at hi <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hi <;>
              subst hi <;> have := hremap0_lt iSel hiSel_lt <;> dsimp only [wP, wU] at * <;> omega
          · by_cases c4 : j < 2 + j0 + 1 + 2 * j0
            · have hidx : j - (2 + j0 + 1) < recon.length := by omega
              have hget : baseGates[j]'(by omega) = recon[j - (2 + j0 + 1)]'hidx := by
                dsimp only [baseGates]
                rw [List.getElem_append_left (by simp [h2len, h4len, h6len]; omega)]
                rw [List.getElem_append_left (by simp [h2len, h4len]; omega)]
                rw [List.getElem_append_right (by simp [h2len]; omega)]
                congr 1; simp [h2len]; omega
              rw [hget] at hi
              have := mkReconGates_readsBack (t + 2) wU sl t j0 (by dsimp only [wU]; omega)
                (j - (2 + j0 + 1)) hidx i hi
              dsimp only [wU] at this; omega
            · by_cases c5 : j = 2 + j0 + 1 + 2 * j0
              · subst c5
                have hget : baseGates[2 + j0 + 1 + 2 * j0]'(by omega) = g0_rep := by
                  dsimp only [baseGates]
                  rw [List.getElem_append_left (by simp [h2len, h4len, h6len]; omega)]
                  rw [List.getElem_append_right (by simp [h2len, h4len]; omega)]
                  simp [h2len, h4len]
                rw [hget] at hi
                have hlt_oth := hremapU_lt_g0 iOth hiOth_lt
                dsimp only [g0_rep] at hi
                rcases hg0_nl'.1 with hand | hor
                · rw [hand] at hi; cases b <;> simp at hi <;> subst hi <;> dsimp only [wG0, wU] at hlt_oth <;> omega
                · rw [hor] at hi; cases b <;> simp at hi <;> subst hi <;> dsimp only [wG0, wU] at hlt_oth <;> omega
              · have hsuf_idx : j - (2 + j0 + 1 + 2 * j0 + 1) < suf.length := by omega
                have hget : baseGates[j]'(by omega) = suf_mapped[j - (2 + j0 + 1 + 2 * j0 + 1)]'(by simp [suf_mapped]; exact hsuf_idx) := by
                  dsimp only [baseGates]
                  rw [List.getElem_append_right (by simp [h2len, h4len]; omega)]
                  congr 1; simp [h2len, h4len]; omega
                rw [hget] at hi
                simp only [suf_mapped, List.getElem_map, List.mem_map] at hi
                obtain ⟨i0, hi0, rfl⟩ := hi
                have hjC : j0 + 1 + (j - (2 + j0 + 1 + 2 * j0 + 1)) < C.gates.length := by
                  rw [hsplit_C]; simp [hpre_len]; omega
                have hgetC : C.gates[j0 + 1 + (j - (2 + j0 + 1 + 2 * j0 + 1))]'hjC =
                    suf[j - (2 + j0 + 1 + 2 * j0 + 1)]'hsuf_idx := by
                  simp only [suf, List.getElem_drop]
                have hlt0 := hrb' (j0 + 1 + (j - (2 + j0 + 1 + 2 * j0 + 1))) hjC i0 (hgetC ▸ hi0)
                dsimp only [remapU, wG0, wU]
                split_ifs <;> omega
    · rw [List.getElem_append_right (by omega)] at hi
      dsimp only [corrGates] at hj hi
      cases d with
      | false => simp at hj; omega
      | true =>
        simp only [↓reduceIte, List.length_append, List.length_cons, List.length_nil] at hj
        simp only [↓reduceIte] at hi
        have hcases : j - baseGates.length = 0 ∨ j - baseGates.length = 1 := by omega
        rcases hcases with h0 | h1
        · simp only [h0, List.getElem_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl
          · omega
          · dsimp only [wU]; rw [hbase_len] at hjb; omega
        · simp only [h1, List.getElem_cons_succ, List.getElem_cons_zero, List.mem_cons,
            List.not_mem_nil, or_false] at hi
          subst hi; omega
  · intro g hg
    dsimp only [D, gatesD, baseGates, corrGates] at hg
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with (((((h01 | hg) | rfl) | hg) | rfl) | hg) | hg
    · rcases h01 with rfl | rfl
      · exact legal_const_false
      · exact legal_const_true
    · simp only [pre_mapped, List.mem_map] at hg
      obtain ⟨g1, hg1, rfl⟩ := hg
      rcases hleg_pre g1 hg1 with ⟨hl, hop⟩
      exact ⟨by simpa using hl, by simpa using hop⟩
    · dsimp only [gU]; split_ifs
      · exact legal_not _
      · exact legal_copy _
    · exact mkReconGates_legal (t + 2) wU sl t j0 g hg
    · dsimp only [g0_rep]
      rcases hg0_nl'.1 with hand | hor
      · rw [hand]; cases b
        · exact legal_const_false
        · exact legal_copy _
      · rw [hor]; cases b
        · exact legal_copy _
        · exact legal_const_true
    · simp only [suf_mapped, List.mem_map] at hg
      obtain ⟨g1, hg1, rfl⟩ := hg
      rcases hleg_suf g1 hg1 with ⟨hl, hop⟩
      exact ⟨by simpa using hl, by simpa using hop⟩
    · cases d with
      | false => simp at hg
      | true =>
        simp only [↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl
        · exact legal_xnor _ _
        · exact legal_not _
  · dsimp only [D, gatesD, baseGates, corrGates]
    simp only [List.countP_append, List.countP_cons, List.countP_nil,
      isNL_const_false, isNL_const_true]
    have hpre_c : pre_mapped.countP isNL = pre.countP isNL := countP_map_remap pre remap0
    have hsuf_c : suf_mapped.countP isNL = suf.countP isNL := countP_map_remap suf remapU
    have hrecon_c : recon.countP isNL = 0 := mkReconGates_countP (t + 2) wU sl t j0
    have hgU_c : isNL gU = false := by dsimp only [gU]; split_ifs <;> simp [isNL_not, isNL_copy]
    have hg0_c : isNL g0_rep = false := by
      dsimp only [g0_rep]
      rcases hg0_nl'.1 with hand | hor
      · rw [hand]; cases b <;> simp [isNL_const_false, isNL_copy]
      · rw [hor]; cases b <;> simp [isNL_const_true, isNL_copy]
    have hcorr_c : (if d then [⟨.mod 2, [wOut, wU]⟩, ⟨.not, [t + baseGates.length]⟩] else []).countP isNL = 0 := by
      cases d <;> simp [isNL_xnor, isNL_not]
    rw [hpre_c, hsuf_c, hrecon_c, hgU_c, hg0_c, hcorr_c]
    simp only [Bool.false_eq_true, ↓reduceIte, add_zero, zero_add]
    omega
  · intro z u
    let ws1 := wiresOf [⟨.or, []⟩, ⟨.and, []⟩] (List.ofFn z)
    have hws1 : ws1 = List.ofFn z ++ [false] ++ [true] := by
      simp [ws1, wiresOf, PEqualNP.CircuitLowerBounds.GateOp.eval]
    have hws1_len : ws1.length = t + 2 := by rw [hws1]; simp
    let ws2 := wiresOf pre_mapped ws1
    have hws2_len : ws2.length = wU := by
      dsimp only [ws2, pre_mapped, wU]; rw [wiresOf_length, hws1_len, List.length_map, hpre_len]
    have hpre_eval : ∀ i < 1 + t + j0,
        ws2.getD (remap0 i) false = (wiresOf pre (false :: List.ofFn z)).getD i false := by
      let init1 : List Bool := false :: List.ofFn z
      have hinit1_len : init1.length = 1 + t := by simp [init1]; omega
      have hmap0 := eval_mapped_gates pre remap0 init1 ws1 (1 + t) hinit1_len
        (fun j hj i hi => by
          have hlt := hrb_pre j hj i hi
          refine ⟨hlt, ?_, ?_⟩
          · intro hi1; dsimp only [remap0]; rw [hws1_len]; split_ifs <;> omega
          · intro r _ heq; dsimp only [remap0]; rw [hws1_len]; split_ifs <;> omega)
        (fun i hi => by
          dsimp only [remap0, init1]
          rw [hws1]
          by_cases hi0 : i = 0
          · subst hi0; simp only [↓reduceIte]
            rw [getD_append_left _ _ _ _ (by simp), getD_append_right _ _ _ _ (by simp)]
            simp
          · simp only [hi0, hi, ↓reduceIte]
            rw [getD_append_left _ _ _ _ (by simp; omega), getD_append_left _ _ _ _ (by simp; omega)]
            cases i with
            | zero => exact absurd rfl hi0
            | succ i' => simp [List.getD_eq_getElem?_getD])
        (fun r => by dsimp only [remap0]; rw [hws1_len]; split_ifs <;> omega)
      intro i hi
      by_cases hi1 : i < 1 + t
      · have hrm_lt : remap0 i < ws1.length := by dsimp only [remap0]; rw [hws1_len]; split_ifs <;> omega
        rw [show ws2.getD (remap0 i) false = ws1.getD (remap0 i) false from
              getD_wiresOf_init pre_mapped ws1 (remap0 i) hrm_lt,
            getD_wiresOf_init pre init1 i (by omega), hws1]
        dsimp only [remap0, init1]
        by_cases hi0 : i = 0
        · subst hi0; simp only [↓reduceIte]
          rw [getD_append_left _ _ _ _ (by simp), getD_append_right _ _ _ _ (by simp)]
          simp
        · simp only [hi0, hi1, ↓reduceIte]
          rw [getD_append_left _ _ _ _ (by simp; omega), getD_append_left _ _ _ _ (by simp; omega)]
          cases i with
          | zero => exact absurd rfl hi0
          | succ i' => simp [List.getD_eq_getElem?_getD]
      · have hr : i - (1 + t) < pre.length := by omega
        have heqi : i = 1 + t + (i - (1 + t)) := by omega
        have hrm : remap0 i = ws1.length + (i - (1 + t)) := by
          dsimp only [remap0]; rw [hws1_len]; split_ifs <;> omega
        rw [hrm, hmap0 (i - (1 + t)) hr, ← heqi]
    let ws3 := wiresOf [gU] ws2
    have hws3_len : ws3.length = wU + 1 := by
      dsimp only [ws3]; rw [wiresOf_length, hws2_len]; simp
    have hws3_u : ws3.getD wU false = u := by
      dsimp only [ws3]
      rw [wiresOf_cons, wiresOf_nil, getD_append_singleton, hws2_len]
      simp only [lt_irrefl, ↓reduceIte]
      have hpz : ws2.getD wP false = p z := hpre_eval iSel hiSel_lt
      dsimp only [gU, u]
      cases b
      · simp only [Bool.false_eq_true, ↓reduceIte, List.map_cons, List.map_nil, hpz,
          PEqualNP.CircuitLowerBounds.GateOp.eval, List.any_cons, List.any_nil, id_eq,
          Bool.or_false, Bool.xor_false]
      · simp only [↓reduceIte, List.map_cons, List.map_nil, hpz,
          PEqualNP.CircuitLowerBounds.GateOp.eval, List.headD_cons, Bool.xor_true]
    let ws4 := wiresOf recon ws3
    have hws4_len : ws4.length = wG0 := by
      dsimp only [ws4, recon, wG0]; rw [wiresOf_length, hws3_len, mkReconGates_length]
    have hws4_match : ∀ i < 1 + t + j0,
        ws4.getD (remapU i) false = (wiresOf pre (u :: List.ofFn z)).getD i false := by
      intro i hi
      by_cases hi0 : i = 0
      · subst hi0
        have hrm : remapU 0 = wU := rfl
        rw [hrm]
        rw [show ws4.getD wU false = ws3.getD wU false from getD_wiresOf_init recon ws3 wU (by omega),
          hws3_u, getD_wiresOf_init pre (u :: List.ofFn z) 0 (by simp)]
        rfl
      · by_cases hi1 : i < 1 + t
        · have hrm : remapU i = i - 1 := by dsimp only [remapU]; simp only [hi0, hi1, ↓reduceIte]
          rw [hrm]
          have hlt1 : i - 1 < ws1.length := by rw [hws1_len]; omega
          have h43 : ws4.getD (i - 1) false = ws3.getD (i - 1) false :=
            getD_wiresOf_init recon ws3 (i - 1) (by omega)
          have h32 : ws3.getD (i - 1) false = ws2.getD (i - 1) false :=
            getD_wiresOf_init [gU] ws2 (i - 1) (by rw [hws2_len]; dsimp only [wU]; omega)
          have h21 : ws2.getD (i - 1) false = ws1.getD (i - 1) false :=
            getD_wiresOf_init pre_mapped ws1 (i - 1) hlt1
          rw [h43, h32, h21, getD_wiresOf_init pre (u :: List.ofFn z) i (by simp; omega), hws1]
          rw [getD_append_left _ _ _ _ (by simp; omega), getD_append_left _ _ _ _ (by simp; omega)]
          cases i with
          | zero => exact absurd rfl hi0
          | succ i' => simp [List.getD_eq_getElem?_getD]
        · have hj : i - (1 + t) < j0 := by omega
          have hrm : remapU i = wU + 1 + 2 * (i - (1 + t)) + 1 := by
            dsimp only [remapU]; simp only [hi0, hi1, hi, ↓reduceIte]
          rw [hrm]
          have hrec := mkReconGates_eval (t + 2) wU sl t j0 ws3 hws3_len (by dsimp only [wU]; omega) (i - (1 + t)) hj
          have hget3k : ws3.getD (t + 2 + (i - (1 + t))) false = ws2.getD (remap0 i) false := by
            have h32 : ws3.getD (t + 2 + (i - (1 + t))) false = ws2.getD (t + 2 + (i - (1 + t))) false :=
              getD_wiresOf_init [gU] ws2 (t + 2 + (i - (1 + t))) (by rw [hws2_len]; dsimp only [wU]; omega)
            have hrm0 : remap0 i = t + 2 + (i - (1 + t)) := by dsimp only [remap0]; split_ifs <;> omega
            rw [h32, hrm0]
          have heqi : 1 + t + (i - (1 + t)) = i := by omega
          dsimp only [ws4, recon]
          rw [hrec, hws3_u, hget3k, hpre_eval i hi, heqi]
          exact (eval_goodPrefix t pre hleg_pre hrb_pre hgood_pre u z i).symm
    let ws5 := wiresOf [g0_rep] ws4
    have hws5_len : ws5.length = wG0 + 1 := by dsimp only [ws5]; rw [wiresOf_length, hws4_len]; simp
    have hws5_g0 : ws5.getD wG0 false = (wiresOf (pre ++ [g0]) (u :: List.ofFn z)).getD (1 + t + j0) false := by
      dsimp only [ws5]
      rw [wiresOf_cons, wiresOf_nil, getD_append_singleton, hws4_len]
      simp only [lt_irrefl, ↓reduceIte]
      rw [wiresOf_append_singleton, getD_append_singleton]
      have hlen_pre : (wiresOf pre (u :: List.ofFn z)).length = 1 + t + j0 := by
        rw [wiresOf_length, hpre_len]; simp; omega
      rw [hlen_pre]
      simp only [lt_irrefl, ↓reduceIte]
      have hsel_val : (wiresOf pre (u :: List.ofFn z)).getD iSel false = b := by
        rw [eval_goodPrefix t pre hleg_pre hrb_pre hgood_pre u z iSel, hsel_slope, Bool.true_and]
        dsimp only [u, p]
        cases (wiresOf pre (false :: List.ofFn z)).getD iSel false <;> cases b <;> decide
      have hoth_val : ws4.getD (remapU iOth) false = (wiresOf pre (u :: List.ofFn z)).getD iOth false :=
        hws4_match iOth hiOth_lt
      rw [hg0_eq]
      simp only [List.map_cons, List.map_nil]
      dsimp only [g0_rep]
      rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rcases hg0_nl'.1 with hand | hor
        · rw [hand]; cases b
          · simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_nil, List.all_cons,
              List.all_nil, id_eq, hsel_val, Bool.false_and]; rfl
          · simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.map_nil,
              List.any_cons, List.any_nil, List.all_cons, List.all_nil, id_eq, hsel_val, hoth_val,
              Bool.or_false, Bool.true_and, Bool.and_true]
        · rw [hor]; cases b
          · simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.map_nil,
              List.any_cons, List.any_nil, id_eq, hsel_val, hoth_val, Bool.false_or, Bool.or_false]
          · simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_nil, List.any_cons,
              List.any_nil, id_eq, hsel_val, Bool.true_or]; rfl
      · rcases hg0_nl'.1 with hand | hor
        · rw [hand]; cases b
          · simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_nil, List.all_cons,
              List.all_nil, id_eq, hsel_val, Bool.false_and, Bool.and_false]; rfl
          · simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.map_nil,
              List.any_cons, List.any_nil, List.all_cons, List.all_nil, id_eq, hsel_val, hoth_val,
              Bool.or_false, Bool.true_and, Bool.and_true]
        · rw [hor]; cases b
          · simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.map_nil,
              List.any_cons, List.any_nil, id_eq, hsel_val, hoth_val, Bool.false_or, Bool.or_false]
          · simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_nil, List.any_cons,
              List.any_nil, id_eq, hsel_val, Bool.true_or, Bool.or_true]; rfl
    let ws6 := wiresOf suf_mapped ws5
    have hws6_eq : ws6 = wiresOf baseGates (List.ofFn z) := by
      dsimp only [ws6, ws5, ws4, ws3, ws2, ws1, baseGates]
      rw [wiresOf_append, wiresOf_append, wiresOf_append, wiresOf_append, wiresOf_append]
    have hws6_len : ws6.length = t + baseGates.length := by
      rw [hws6_eq, wiresOf_length, List.length_ofFn]
    have hws5_match : ∀ i < 1 + t + (j0 + 1),
        ws5.getD (remapU i) false = (wiresOf (pre ++ [g0]) (u :: List.ofFn z)).getD i false := by
      intro i hi
      by_cases hlt : i < 1 + t + j0
      · have hrm_lt : remapU i < ws4.length := by rw [hws4_len]; exact hremapU_lt_g0 i hlt
        have hget5 : ws5.getD (remapU i) false = ws4.getD (remapU i) false :=
          getD_wiresOf_init [g0_rep] ws4 (remapU i) hrm_lt
        have hgetC : (wiresOf (pre ++ [g0]) (u :: List.ofFn z)).getD i false =
            (wiresOf pre (u :: List.ofFn z)).getD i false := by
          exact getD_wiresOf_prefix pre [g0] (u :: List.ofFn z) i (by simp [hpre_len]; omega)
        rw [hget5, hgetC, hws4_match i hlt]
      · have heq : i = 1 + t + j0 := by omega
        subst heq
        have hrm : remapU (1 + t + j0) = wG0 := by
          dsimp only [remapU]; split_ifs <;> omega
        rw [hrm, hws5_g0]
    have hws6_suf := eval_mapped_gates suf remapU (wiresOf (pre ++ [g0]) (u :: List.ofFn z)) ws5
      (1 + t + (j0 + 1)) (by rw [wiresOf_length, List.length_append, List.length_singleton, hpre_len]; simp; omega)
      (fun j hj i hi => by
        have hjC : j0 + 1 + j < C.gates.length := by rw [hsplit_C]; simp [hpre_len]; omega
        have hgetC : C.gates[j0 + 1 + j]'hjC = suf[j]'hj := by simp [suf]
        have hlt := hrb' (j0 + 1 + j) hjC i (by rw [hgetC]; exact hi)
        refine ⟨by omega, ?_, ?_⟩
        · intro hi1; rw [hws5_len]
          by_cases hlt0 : i < 1 + t + j0
          · have := hremapU_lt_g0 i hlt0; omega
          · have heq : i = 1 + t + j0 := by omega
            subst heq; dsimp only [remapU]; split_ifs <;> omega
        · intro r _ heq; rw [hws5_len]; dsimp only [remapU]; split_ifs <;> omega)
      hws5_match
      (fun r => by rw [hws5_len]; dsimp only [remapU]; split_ifs <;> omega)
    have hws6_out : ws6.getD wOut false = C.eval (u :: List.ofFn z) := by
      change ws6.getD wOut false = (wiresOf C.gates (u :: List.ofFn z)).getD C.output false
      have hC_wires : wiresOf C.gates (u :: List.ofFn z) =
          wiresOf suf (wiresOf (pre ++ [g0]) (u :: List.ofFn z)) := by
        rw [hsplit_C, wiresOf_append]
      rw [hC_wires]
      dsimp only [wOut]
      by_cases hout : C.output < 1 + t + C.gates.length
      · simp only [hout, ↓reduceIte]
        by_cases h1 : C.output < 1 + t + (j0 + 1)
        · have hrm_lt : remapU C.output < ws5.length := by
            rw [hws5_len]
            by_cases hlt0 : C.output < 1 + t + j0
            · have := hremapU_lt_g0 C.output hlt0; omega
            · have heq : C.output = 1 + t + j0 := by omega
              rw [heq]; dsimp only [remapU]; split_ifs <;> omega
          have hget6 : ws6.getD (remapU C.output) false = ws5.getD (remapU C.output) false :=
            getD_wiresOf_init suf_mapped ws5 (remapU C.output) hrm_lt
          have hlen_pre0 : (wiresOf (pre ++ [g0]) (u :: List.ofFn z)).length = 1 + t + (j0 + 1) := by
            rw [wiresOf_length, List.length_append, List.length_singleton, hpre_len]; simp; omega
          have hgetC : (wiresOf suf (wiresOf (pre ++ [g0]) (u :: List.ofFn z))).getD C.output false =
              (wiresOf (pre ++ [g0]) (u :: List.ofFn z)).getD C.output false :=
            getD_wiresOf_init suf (wiresOf (pre ++ [g0]) (u :: List.ofFn z)) C.output (by omega)
          rw [hget6, hgetC, hws5_match C.output h1]
        · have hClen : C.gates.length = j0 + 1 + suf.length := by rw [hsplit_C]; simp [hpre_len]; omega
          have hr : C.output - (1 + t + (j0 + 1)) < suf.length := by omega
          have heq : C.output = 1 + t + (j0 + 1) + (C.output - (1 + t + (j0 + 1))) := by omega
          have hrm : remapU C.output = ws5.length + (C.output - (1 + t + (j0 + 1))) := by
            rw [hws5_len]; dsimp only [remapU]; split_ifs <;> omega
          rw [hrm, hws6_suf (C.output - (1 + t + (j0 + 1))) hr, ← heq]
      · simp only [hout, ↓reduceIte]
        have hClen : C.gates.length = j0 + 1 + suf.length := by rw [hsplit_C]; simp [hpre_len]; omega
        have hgeC : (wiresOf suf (wiresOf (pre ++ [g0]) (u :: List.ofFn z))).length ≤ C.output := by
          rw [wiresOf_length, wiresOf_length, List.length_append, List.length_singleton, hpre_len]; simp; omega
        have hnoneC : (wiresOf suf (wiresOf (pre ++ [g0]) (u :: List.ofFn z))).getD C.output false = false := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hgeC, Option.getD_none]
        rw [hnoneC]
        have ht_lt : t < ws1.length := by rw [hws1_len]; omega
        have hget6 : ws6.getD t false = ws1.getD t false := by
          have h65 := getD_wiresOf_init suf_mapped ws5 t (by rw [hws5_len]; dsimp only [wG0, wU]; omega)
          have h54 := getD_wiresOf_init [g0_rep] ws4 t (by rw [hws4_len]; dsimp only [wG0, wU]; omega)
          have h43 := getD_wiresOf_init recon ws3 t (by rw [hws3_len]; dsimp only [wU]; omega)
          have h32 := getD_wiresOf_init [gU] ws2 t (by rw [hws2_len]; dsimp only [wU]; omega)
          have h21 := getD_wiresOf_init pre_mapped ws1 t ht_lt
          exact h65.trans (h54.trans (h43.trans (h32.trans h21)))
        rw [hget6, hws1, getD_append_left _ _ _ _ (by simp), getD_append_right _ _ _ _ (by simp)]
        simp
    have hws6_u : ws6.getD wU false = u := by
      have h65 := getD_wiresOf_init suf_mapped ws5 wU (by rw [hws5_len]; dsimp only [wG0]; omega)
      have h54 := getD_wiresOf_init [g0_rep] ws4 wU (by rw [hws4_len]; dsimp only [wG0]; omega)
      have h43 := getD_wiresOf_init recon ws3 wU (by rw [hws3_len]; omega)
      exact h65.trans (h54.trans (h43.trans hws3_u))
    change (wiresOf (baseGates ++ corrGates) (List.ofFn z)).getD outD false = _
    rw [wiresOf_append, ← hws6_eq]
    cases d with
    | false =>
      dsimp only [corrGates, outD]
      simp only [Bool.false_eq_true, ↓reduceIte, wiresOf_nil, Bool.false_and, Bool.xor_false]
      exact hws6_out
    | true =>
      dsimp only [corrGates, outD]
      simp only [↓reduceIte, wiresOf_cons, wiresOf_nil, Bool.true_and]
      change ((ws6 ++ [PEqualNP.CircuitLowerBounds.GateOp.eval (.mod 2) [ws6.getD wOut false, ws6.getD wU false]]) ++
        [PEqualNP.CircuitLowerBounds.GateOp.eval .not [(ws6 ++ [PEqualNP.CircuitLowerBounds.GateOp.eval (.mod 2) [ws6.getD wOut false, ws6.getD wU false]]).getD (t + baseGates.length) false]]).getD (t + baseGates.length + 1) false = _
      have hlen1 : (ws6 ++ [PEqualNP.CircuitLowerBounds.GateOp.eval (.mod 2) [ws6.getD wOut false, ws6.getD wU false]]).length =
          t + baseGates.length + 1 := by rw [List.length_append, List.length_singleton, hws6_len]
      rw [getD_append_singleton, hlen1]
      simp only [lt_irrefl, ↓reduceIte]
      rw [getD_append_singleton, hws6_len]
      simp only [lt_irrefl, ↓reduceIte, hws6_out, hws6_u]
      exact eval_xnor_not _ _

private lemma main_825 (t : ℕ) (C : Circ)
    (hleg : PEqualNP.MetaComplexity.NestedCover.ReadsBack (1 + t) C ∧
      ∀ g ∈ C.gates, g.inputs.length ≤ 2 ∧
        (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1))) :
    let cost := fun (D : Circ) =>
      D.gates.countP (fun g => @decide
        ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) (Classical.propDecidable _))
    let legal := fun (nW : ℕ) (D : Circ) =>
      PEqualNP.MetaComplexity.NestedCover.ReadsBack nW D ∧
        (∀ g ∈ D.gates, g.inputs.length ≤ 2 ∧
          (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1)))
    (∃ (a : Bool) (E : Circ), legal t E ∧ cost E ≤ cost C ∧
      ∀ (u : Bool) (z : Fin t → Bool), C.eval (u :: List.ofFn z) =
        Bool.xor (a && u) (E.eval (List.ofFn z))) ∨
    (0 < cost C ∧ ∃ p : (Fin t → Bool) → Bool,
      ∀ (b d : Bool), ∃ D : Circ, legal t D ∧ cost D < cost C ∧
        ∀ z : Fin t → Bool, let u := Bool.xor (p z) b
          D.eval (List.ofFn z) = Bool.xor (C.eval (u :: List.ofFn z)) (d && u)) := by
  by_cases hgood : GoodPrefix (1 + t) C.gates
  · exact Or.inl (build_case1 t C hleg.1 hleg.2 hgood)
  · exact Or.inr (build_case2 t C hleg.1 hleg.2 hgood)

end PEqualNP.Outside.L_lib_825_aux

theorem PEqualNP.Outside.L_lib_825 : ∀ t : ℕ,
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let legal := fun (nW : ℕ) (C : Circ) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack nW C ∧
      (∀ g ∈ C.gates, g.inputs.length ≤ 2 ∧
        (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1)))
  let cost := fun (C : Circ) =>
    C.gates.countP (fun g => @decide
      ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) (Classical.propDecidable _))
  let Z := Fin t → Bool
  ∀ C : Circ, legal (1+t) C →
    (∃ (a : Bool) (E : Circ), legal t E ∧ cost E ≤ cost C ∧
      ∀ (u : Bool) (z : Z), C.eval (u :: List.ofFn z) =
        Bool.xor (a && u) (E.eval (List.ofFn z))) ∨
    (0 < cost C ∧ ∃ p : Z → Bool,
      ∀ (b d : Bool), ∃ D : Circ, legal t D ∧ cost D < cost C ∧
        ∀ z : Z, let u := Bool.xor (p z) b
          D.eval (List.ofFn z) = Bool.xor (C.eval (u :: List.ofFn z)) (d && u)) := by
  intro t Circ legal cost Z C hleg
  exact PEqualNP.Outside.L_lib_825_aux.main_825 t C hleg

import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1392

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)
open PEqualNP.NotBracket (notCount)

/-! ### Section 1: Circuit wire evaluation and gate utilities -/

private def gateStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem wires_eq (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl gateStep x := rfl

private theorem fold_length (gs : List Gate) (x : List Bool) :
    (gs.foldl gateStep x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, gateStep, List.length_append, List.length_cons, List.length_nil]
    omega

private theorem wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.size :=
  fold_length C.gates x

private theorem fold_getD_lt (gs : List Gate) (x : List Bool) {i : Nat} (hi : i < x.length) :
    (gs.foldl gateStep x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    have hlt : i < (gateStep x g).length := by
      simp only [gateStep, List.length_append, List.length_singleton]
      omega
    rw [List.foldl_cons, ih (gateStep x g) hlt]
    exact List.getD_append _ _ _ _ hi

private def valC (gs : List Gate) (x : List Bool) (i : Nat) : Bool :=
  (gs.foldl gateStep x).getD i false

private theorem eval_eq_valC (C : Circuit) (x : List Bool) :
    C.eval x = valC C.gates x C.output := rfl

private theorem valC_input (gs : List Gate) (x : List Bool) {i : Nat} (hi : i < x.length) :
    valC gs x i = x.getD i false :=
  fold_getD_lt gs x hi

private theorem valC_append_lt (gs1 gs2 : List Gate) (x : List Bool) {i : Nat}
    (hi : i < x.length + gs1.length) :
    valC (gs1 ++ gs2) x i = valC gs1 x i := by
  unfold valC
  rw [List.foldl_append]
  apply fold_getD_lt
  rw [fold_length]
  exact hi

private theorem valC_snoc_last (gs : List Gate) (g : Gate) (x : List Bool) :
    valC (gs ++ [g]) x (x.length + gs.length) =
      g.op.eval (g.inputs.map fun i => valC gs x i) := by
  unfold valC
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hlen : (gs.foldl gateStep x).length = x.length + gs.length := fold_length gs x
  set w := gs.foldl gateStep x
  rw [← hlen]
  simp only [gateStep]
  rw [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self]
  rfl

private theorem gateAt_eq (C : Circuit) {k : Nat} (hk : k < C.gates.length) :
    gateAt C k = C.gates[k] := by
  unfold gateAt
  simp [List.getD, hk]

private theorem valC_gate (C : Circuit) (x : List Bool) (hRB : ReadsBack x.length C)
    {k : Nat} (hk : k < C.gates.length) :
    valC C.gates x (x.length + k) =
      C.gates[k].op.eval (C.gates[k].inputs.map fun i => valC C.gates x i) := by
  have hsplit : C.gates = (C.gates.take k ++ [C.gates[k]]) ++ C.gates.drop (k + 1) := by
    rw [List.append_assoc, List.singleton_append]
    have h1 : C.gates[k] :: C.gates.drop (k + 1) = C.gates.drop k := by
      simp [List.cons_getElem_drop_succ]
    rw [h1, List.take_append_drop]
  have htk_len : (C.gates.take k).length = k := List.length_take_of_le (Nat.le_of_lt hk)
  have hlt1 : x.length + k < x.length + (C.gates.take k ++ [C.gates[k]]).length := by
    rw [List.length_append, htk_len, List.length_singleton]
    omega
  have h1 : valC C.gates x (x.length + k) =
      valC (C.gates.take k ++ [C.gates[k]]) x (x.length + k) := by
    conv_lhs => rw [hsplit]
    exact valC_append_lt _ _ x hlt1
  have h2 := valC_snoc_last (C.gates.take k) C.gates[k] x
  rw [htk_len] at h2
  rw [h1, h2]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi_lt : i < x.length + k := by
    have h := hRB k hk i
    rw [gateAt_eq C hk] at h
    exact h hi
  have hsplit2 : C.gates = C.gates.take k ++ C.gates.drop k := (List.take_append_drop k C.gates).symm
  conv_rhs => rw [hsplit2]
  rw [valC_append_lt]
  rw [htk_len]
  exact hi_lt

private def mkInput {d : Nat} (x : Fin d → Bool) : List Bool :=
  List.ofFn x ++ [false, true]

private theorem mkInput_length {d : Nat} (x : Fin d → Bool) :
    (mkInput x).length = d + 2 := by
  simp [mkInput]

private theorem mkInput_getD_var {d : Nat} (x : Fin d → Bool) (i : Fin d) :
    (mkInput x).getD i.val false = x i := by
  unfold mkInput
  have hi : i.val < (List.ofFn x).length := by simp
  rw [List.getD_append _ _ _ _ hi]
  simp [List.getD, hi]

private theorem mkInput_getD_false {d : Nat} (x : Fin d → Bool) :
    (mkInput x).getD d false = false := by
  unfold mkInput
  have hlen : (List.ofFn x).length = d := by simp
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp [hlen]

private theorem mkInput_getD_true {d : Nat} (x : Fin d → Bool) :
    (mkInput x).getD (d + 1) false = true := by
  unfold mkInput
  have hlen : (List.ofFn x).length = d := by simp
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp [hlen]

private theorem notCount_eq_zero_iff (gs : List Gate) (o : Nat) :
    notCount ⟨gs, o⟩ = 0 ↔ ∀ g ∈ gs, g.op ≠ GateOp.not := by
  unfold notCount
  simp [List.filter_eq_nil_iff]

private theorem mono_gate_props {C : Circuit} (hF : FanInTwo C) (hN : notCount C = 0) :
    ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  have h1 := hF g hg
  have h2 := (notCount_eq_zero_iff C.gates C.output).mp hN g hg
  refine ⟨?_, h1.2⟩
  rcases h1.1 with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact False.elim (h2 h)

/-! ### Section 2: Full binary monotone trees (shared by both directions) -/

private inductive BTree (α : Type) where
  | leaf (a : α)
  | and (l r : BTree α)
  | or (l r : BTree α)

private def BTree.gates {α : Type} : BTree α → Nat
  | .leaf _ => 0
  | .and l r => 1 + l.gates + r.gates
  | .or l r => 1 + l.gates + r.gates

private def BTree.leaves {α : Type} : BTree α → Nat
  | .leaf _ => 1
  | .and l r => l.leaves + r.leaves
  | .or l r => l.leaves + r.leaves

private theorem BTree.leaves_eq_gates_add_one {α : Type} (τ : BTree α) :
    τ.leaves = τ.gates + 1 := by
  induction τ with
  | leaf _ => rfl
  | and l r ihl ihr => simp [BTree.leaves, BTree.gates, ihl, ihr]; omega
  | or l r ihl ihr => simp [BTree.leaves, BTree.gates, ihl, ihr]; omega

private theorem BTree.leaves_pos {α : Type} (τ : BTree α) : 0 < τ.leaves := by
  rw [τ.leaves_eq_gates_add_one]
  omega

private def BTree.eval {α : Type} (v : α → Bool) : BTree α → Bool
  | .leaf a => v a
  | .and l r => l.eval v && r.eval v
  | .or l r => l.eval v || r.eval v

private def BTree.leafAt {α : Type} : (τ : BTree α) → Fin τ.leaves → α
  | .leaf a, _ => a
  | .and l r, i =>
    if h : i.val < l.leaves then
      l.leafAt ⟨i.val, h⟩
    else
      r.leafAt ⟨i.val - l.leaves, by have := i.isLt; simp [BTree.leaves] at this; omega⟩
  | .or l r, i =>
    if h : i.val < l.leaves then
      l.leafAt ⟨i.val, h⟩
    else
      r.leafAt ⟨i.val - l.leaves, by have := i.isLt; simp [BTree.leaves] at this; omega⟩

private def castLeft {a b : Nat} (i : Fin a) : Fin (a + b) :=
  ⟨i.val, by omega⟩

private def castRight {a b : Nat} (j : Fin b) : Fin (a + b) :=
  ⟨a + j.val, by omega⟩

private theorem BTree.leafAt_and_left {α : Type} (l r : BTree α) (i : Fin l.leaves) :
    (BTree.and l r).leafAt (castLeft i) = l.leafAt i := by
  simp [BTree.leafAt, castLeft, i.isLt]

private theorem BTree.leafAt_and_right {α : Type} (l r : BTree α) (j : Fin r.leaves) :
    (BTree.and l r).leafAt (castRight j) = r.leafAt j := by
  have h : ¬ (l.leaves + j.val < l.leaves) := by omega
  simp [BTree.leafAt, castRight, h]

private theorem BTree.leafAt_or_left {α : Type} (l r : BTree α) (i : Fin l.leaves) :
    (BTree.or l r).leafAt (castLeft i) = l.leafAt i := by
  simp [BTree.leafAt, castLeft, i.isLt]

private theorem BTree.leafAt_or_right {α : Type} (l r : BTree α) (j : Fin r.leaves) :
    (BTree.or l r).leafAt (castRight j) = r.leafAt j := by
  have h : ¬ (l.leaves + j.val < l.leaves) := by omega
  simp [BTree.leafAt, castRight, h]

private def BTree.pick {α : Type} {m : Nat} (val : α → Fin m → Bool) :
    (τ : BTree α) → Fin m → Fin m → Fin τ.leaves
  | .leaf _, _, _ => ⟨0, by simp [BTree.leaves]⟩
  | .and l r, h, l' =>
    if l.eval (fun a => val a l') = false then
      castLeft (l.pick val h l')
    else
      castRight (r.pick val h l')
  | .or l r, h, l' =>
    if l.eval (fun a => val a h) = true then
      castLeft (l.pick val h l')
    else
      castRight (r.pick val h l')

private theorem BTree.pick_and_left {α : Type} {m : Nat} (val : α → Fin m → Bool)
    (L R : BTree α) (h l : Fin m) (hL : L.eval (fun a => val a l) = false) :
    (BTree.and L R).pick val h l = castLeft (L.pick val h l) := by
  change (if L.eval (fun a => val a l) = false then castLeft (L.pick val h l)
          else castRight (R.pick val h l)) = _
  exact if_pos hL

private theorem BTree.pick_and_right {α : Type} {m : Nat} (val : α → Fin m → Bool)
    (L R : BTree α) (h l : Fin m) (hL : L.eval (fun a => val a l) ≠ false) :
    (BTree.and L R).pick val h l = castRight (R.pick val h l) := by
  change (if L.eval (fun a => val a l) = false then castLeft (L.pick val h l)
          else castRight (R.pick val h l)) = _
  exact if_neg hL

private theorem BTree.pick_or_left {α : Type} {m : Nat} (val : α → Fin m → Bool)
    (L R : BTree α) (h l : Fin m) (hL : L.eval (fun a => val a h) = true) :
    (BTree.or L R).pick val h l = castLeft (L.pick val h l) := by
  change (if L.eval (fun a => val a h) = true then castLeft (L.pick val h l)
          else castRight (R.pick val h l)) = _
  exact if_pos hL

private theorem BTree.pick_or_right {α : Type} {m : Nat} (val : α → Fin m → Bool)
    (L R : BTree α) (h l : Fin m) (hL : L.eval (fun a => val a h) ≠ true) :
    (BTree.or L R).pick val h l = castRight (R.pick val h l) := by
  change (if L.eval (fun a => val a h) = true then castLeft (L.pick val h l)
          else castRight (R.pick val h l)) = _
  exact if_neg hL

private theorem BTree.pick_sep {α : Type} {m : Nat} (val : α → Fin m → Bool)
    (τ : BTree α) (h l : Fin m)
    (hh : τ.eval (fun a => val a h) = true)
    (hl : τ.eval (fun a => val a l) = false) :
    val (τ.leafAt (τ.pick val h l)) h = true ∧
    val (τ.leafAt (τ.pick val h l)) l = false := by
  induction τ with
  | leaf a =>
    simpa [BTree.eval, BTree.leafAt, BTree.pick] using And.intro hh hl
  | and L R ihL ihR =>
    simp only [BTree.eval, Bool.and_eq_true, Bool.and_eq_false_iff] at hh hl
    by_cases hL : L.eval (fun a => val a l) = false
    · rw [BTree.pick_and_left val L R h l hL, BTree.leafAt_and_left]
      exact ihL hh.1 hL
    · rw [BTree.pick_and_right val L R h l hL, BTree.leafAt_and_right]
      have hR : R.eval (fun a => val a l) = false := by
        rcases hl with h1 | h2
        · exact False.elim (hL h1)
        · exact h2
      exact ihR hh.2 hR
  | or L R ihL ihR =>
    simp only [BTree.eval, Bool.or_eq_true, Bool.or_eq_false_iff] at hh hl
    by_cases hL : L.eval (fun a => val a h) = true
    · rw [BTree.pick_or_left val L R h l hL, BTree.leafAt_or_left]
      exact ihL hL hl.1
    · rw [BTree.pick_or_right val L R h l hL, BTree.leafAt_or_right]
      have hR : R.eval (fun a => val a h) = true := by
        rcases hh with h1 | h2
        · exact False.elim (hL h1)
        · exact h2
      exact ihR hR hl.2

private def cellOf {α : Type} {m : Nat} (val : α → Fin m → Bool) (τ : BTree α)
    (h l : Fin m) : Prop :=
  τ.eval (fun a => val a h) = true ∧ τ.eval (fun a => val a l) = false

private def rowOf {α : Type} {m : Nat} (val : α → Fin m → Bool) (τ : BTree α)
    (a b : Fin τ.leaves) : Prop :=
  ∃ h l t, cellOf val τ h l ∧ cellOf val τ h t ∧ τ.pick val h l = a ∧ τ.pick val h t = b

private def colOf {α : Type} {m : Nat} (val : α → Fin m → Bool) (τ : BTree α)
    (a b : Fin τ.leaves) : Prop :=
  ∃ h l t, cellOf val τ h l ∧ cellOf val τ t l ∧ τ.pick val h l = a ∧ τ.pick val t l = b

private def splitOf {α : Type} [DecidableEq α] (S : Finset α) (adj : α → α → Prop) : Prop :=
  ∃ U : Finset α, U.Nonempty ∧ U ⊂ S ∧ ∀ a ∈ U, ∀ b ∈ S \ U, ¬adj a b

private theorem splitOf_push {α β : Type} [DecidableEq α] [DecidableEq β]
    {f : α → β} (hf : Function.Injective f)
    {S : Finset α} {adjA : α → α → Prop} {adjB : β → β → Prop}
    (hrel : ∀ x y, adjB (f x) (f y) → adjA x y)
    (hs : splitOf S adjA) :
    splitOf (S.image f) adjB := by
  rcases hs with ⟨U, hUne, hUss, hno⟩
  refine ⟨U.image f, hUne.image f, ?_, ?_⟩
  · rw [Finset.ssubset_iff_subset_ne] at hUss ⊢
    refine ⟨Finset.image_subset_image hUss.1, ?_⟩
    intro heq
    apply hUss.2
    ext x
    constructor
    · intro hx; exact hUss.1 hx
    · intro hx
      have hfx : f x ∈ U.image f := by rw [heq]; exact Finset.mem_image_of_mem f hx
      rcases Finset.mem_image.mp hfx with ⟨y, hy, hfy⟩
      rw [← hf hfy]
      exact hy
  · intro a ha b hb hadj
    rcases Finset.mem_image.mp ha with ⟨x, hxU, rfl⟩
    rw [Finset.mem_sdiff] at hb
    rcases Finset.mem_image.mp hb.1 with ⟨y, hyS, rfl⟩
    have hyNotU : y ∉ U := by
      intro hyU
      exact hb.2 (Finset.mem_image_of_mem f hyU)
    exact hno x hxU y (Finset.mem_sdiff.mpr ⟨hyS, hyNotU⟩) (hrel x y hadj)

private theorem BTree.pick_split {α : Type} {m : Nat} (val : α → Fin m → Bool)
    (τ : BTree α) (S : Finset (Fin τ.leaves)) (hS : 2 ≤ S.card) :
    splitOf S (rowOf val τ) ∨ splitOf S (colOf val τ) := by
  classical
  induction τ with
  | leaf a =>
    have hle : S.card ≤ 1 := by
      calc S.card ≤ (Finset.univ : Finset (Fin (BTree.leaf a).leaves)).card := Finset.card_le_univ S
        _ = 1 := by change (Finset.univ : Finset (Fin 1)).card = 1; exact Finset.card_fin 1
    omega
  | and L R ihL ihR =>
    let cl : Fin L.leaves → Fin (BTree.and L R).leaves := castLeft
    let cr : Fin R.leaves → Fin (BTree.and L R).leaves := castRight
    have hInjL : Function.Injective cl := by
      intro i j hij; ext; simpa [cl, castLeft] using congrArg Fin.val hij
    have hInjR : Function.Injective cr := by
      intro i j hij; ext; have := congrArg Fin.val hij; simp [cr, castRight] at this; exact this
    let U : Finset (Fin (BTree.and L R).leaves) := S.filter (fun a => a.val < L.leaves)
    let V : Finset (Fin (BTree.and L R).leaves) := S \ U
    by_cases hU : U.Nonempty
    · by_cases hV : V.Nonempty
      · right
        refine ⟨U, hU, ?_, ?_⟩
        · rw [Finset.ssubset_iff_subset_ne]
          refine ⟨Finset.filter_subset _ S, ?_⟩
          intro heq
          rcases hV with ⟨b, hb⟩
          rw [Finset.mem_sdiff, heq] at hb
          exact hb.2 hb.1
        · intro a ha b hb hcol
          have haL : a.val < L.leaves := (Finset.mem_filter.mp ha).2
          have hbNotL : ¬ (b.val < L.leaves) := by
            intro hlt
            have hbS : b ∈ S := (Finset.mem_sdiff.mp hb).1
            exact (Finset.mem_sdiff.mp hb).2 (Finset.mem_filter.mpr ⟨hbS, hlt⟩)
          rcases hcol with ⟨h, l, t, _, _, hpick1, hpick2⟩
          by_cases hL : L.eval (fun x => val x l) = false
          · have h2 : (BTree.and L R).pick val t l = cl (L.pick val t l) := BTree.pick_and_left val L R t l hL
            rw [h2] at hpick2
            rw [← hpick2] at hbNotL
            exact hbNotL (L.pick val t l).isLt
          · have h1 : (BTree.and L R).pick val h l = cr (R.pick val h l) := BTree.pick_and_right val L R h l hL
            rw [h1] at hpick1
            rw [← hpick1] at haL
            simp [cr, castRight] at haL
      · have hVempty : V = ∅ := Finset.not_nonempty_iff_eq_empty.mp hV
        have hAllL : ∀ a ∈ S, a.val < L.leaves := by
          intro a ha
          by_contra hnot
          have : a ∈ V := Finset.mem_sdiff.mpr ⟨ha, fun hmem => hnot (Finset.mem_filter.mp hmem).2⟩
          rw [hVempty] at this
          exact Finset.notMem_empty a this
        let SL : Finset (Fin L.leaves) := Finset.univ.filter (fun i => cl i ∈ S)
        have hSimg : S = SL.image cl := by
          ext a
          constructor
          · intro ha
            have hlt := hAllL a ha
            exact Finset.mem_image.mpr ⟨⟨a.val, hlt⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩, by ext; rfl⟩
          · intro ha
            rcases Finset.mem_image.mp ha with ⟨i, hi, rfl⟩
            exact (Finset.mem_filter.mp hi).2
        have hSLcard : 2 ≤ SL.card := by
          rw [hSimg, Finset.card_image_of_injective SL hInjL] at hS
          exact hS
        have hstep := ihL SL hSLcard
        rw [hSimg]
        have hLeftPick : ∀ h l i,
            cellOf val (BTree.and L R) h l →
            (BTree.and L R).pick val h l = cl i →
            cellOf val L h l ∧ L.pick val h l = i := by
          intro h l i hcell hp
          simp only [cellOf, BTree.eval, Bool.and_eq_true] at hcell
          by_cases hL : L.eval (fun x => val x l) = false
          · have h1 : (BTree.and L R).pick val h l = cl (L.pick val h l) := BTree.pick_and_left val L R h l hL
            rw [h1] at hp
            exact ⟨⟨hcell.1.1, hL⟩, hInjL hp⟩
          · have h1 : (BTree.and L R).pick val h l = cr (R.pick val h l) := BTree.pick_and_right val L R h l hL
            rw [h1] at hp
            have hlt := i.isLt
            have heq := congrArg Fin.val hp
            simp [cl, cr, castLeft, castRight] at heq
            omega
        rcases hstep with hrow | hcol
        · left
          apply splitOf_push hInjL _ hrow
          rintro x y ⟨h, l, t, hc1, hc2, hp1, hp2⟩
          have ⟨hc1', hp1'⟩ := hLeftPick h l x hc1 hp1
          have ⟨hc2', hp2'⟩ := hLeftPick h t y hc2 hp2
          exact ⟨h, l, t, hc1', hc2', hp1', hp2'⟩
        · right
          apply splitOf_push hInjL _ hcol
          rintro x y ⟨h, l, t, hc1, hc2, hp1, hp2⟩
          have ⟨hc1', hp1'⟩ := hLeftPick h l x hc1 hp1
          have ⟨hc2', hp2'⟩ := hLeftPick t l y hc2 hp2
          exact ⟨h, l, t, hc1', hc2', hp1', hp2'⟩
    · have hUempty : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hU
      have hAllR : ∀ a ∈ S, L.leaves ≤ a.val := by
        intro a ha
        by_contra hnot
        have hlt : a.val < L.leaves := by omega
        have : a ∈ U := Finset.mem_filter.mpr ⟨ha, hlt⟩
        rw [hUempty] at this
        exact Finset.notMem_empty a this
      let SR : Finset (Fin R.leaves) := Finset.univ.filter (fun j => cr j ∈ S)
      have hSimg : S = SR.image cr := by
        ext a
        constructor
        · intro ha
          have hge := hAllR a ha
          have hlt : a.val - L.leaves < R.leaves := by
            have := a.isLt; simp [BTree.leaves] at this; omega
          have heq : cr ⟨a.val - L.leaves, hlt⟩ = a := by
            ext; simp [cr, castRight]; omega
          refine Finset.mem_image.mpr ⟨⟨a.val - L.leaves, hlt⟩, ?_, heq⟩
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          rw [heq]; exact ha
        · intro ha
          rcases Finset.mem_image.mp ha with ⟨j, hj, rfl⟩
          exact (Finset.mem_filter.mp hj).2
      have hSRcard : 2 ≤ SR.card := by
        rw [hSimg, Finset.card_image_of_injective SR hInjR] at hS
        exact hS
      have hstep := ihR SR hSRcard
      rw [hSimg]
      have hRightPick : ∀ h l j,
          cellOf val (BTree.and L R) h l →
          (BTree.and L R).pick val h l = cr j →
          cellOf val R h l ∧ R.pick val h l = j := by
        intro h l j hcell hp
        simp only [cellOf, BTree.eval, Bool.and_eq_true, Bool.and_eq_false_iff] at hcell
        by_cases hL : L.eval (fun x => val x l) = false
        · have h1 : (BTree.and L R).pick val h l = cl (L.pick val h l) := BTree.pick_and_left val L R h l hL
          rw [h1] at hp
          have hlt := (L.pick val h l).isLt
          have heq := congrArg Fin.val hp
          simp [cl, cr, castLeft, castRight] at heq
          omega
        · have h1 : (BTree.and L R).pick val h l = cr (R.pick val h l) := BTree.pick_and_right val L R h l hL
          rw [h1] at hp
          have hR : R.eval (fun a => val a l) = false := by
            rcases hcell.2 with h1' | h2'
            · exact False.elim (hL h1')
            · exact h2'
          exact ⟨⟨hcell.1.2, hR⟩, hInjR hp⟩
      rcases hstep with hrow | hcol
      · left
        apply splitOf_push hInjR _ hrow
        rintro x y ⟨h, l, t, hc1, hc2, hp1, hp2⟩
        have ⟨hc1', hp1'⟩ := hRightPick h l x hc1 hp1
        have ⟨hc2', hp2'⟩ := hRightPick h t y hc2 hp2
        exact ⟨h, l, t, hc1', hc2', hp1', hp2'⟩
      · right
        apply splitOf_push hInjR _ hcol
        rintro x y ⟨h, l, t, hc1, hc2, hp1, hp2⟩
        have ⟨hc1', hp1'⟩ := hRightPick h l x hc1 hp1
        have ⟨hc2', hp2'⟩ := hRightPick t l y hc2 hp2
        exact ⟨h, l, t, hc1', hc2', hp1', hp2'⟩
  | or L R ihL ihR =>
    let cl : Fin L.leaves → Fin (BTree.or L R).leaves := castLeft
    let cr : Fin R.leaves → Fin (BTree.or L R).leaves := castRight
    have hInjL : Function.Injective cl := by
      intro i j hij; ext; simpa [cl, castLeft] using congrArg Fin.val hij
    have hInjR : Function.Injective cr := by
      intro i j hij; ext; have := congrArg Fin.val hij; simp [cr, castRight] at this; exact this
    let U : Finset (Fin (BTree.or L R).leaves) := S.filter (fun a => a.val < L.leaves)
    let V : Finset (Fin (BTree.or L R).leaves) := S \ U
    by_cases hU : U.Nonempty
    · by_cases hV : V.Nonempty
      · left
        refine ⟨U, hU, ?_, ?_⟩
        · rw [Finset.ssubset_iff_subset_ne]
          refine ⟨Finset.filter_subset _ S, ?_⟩
          intro heq
          rcases hV with ⟨b, hb⟩
          rw [Finset.mem_sdiff, heq] at hb
          exact hb.2 hb.1
        · intro a ha b hb hrow
          have haL : a.val < L.leaves := (Finset.mem_filter.mp ha).2
          have hbNotL : ¬ (b.val < L.leaves) := by
            intro hlt
            have hbS : b ∈ S := (Finset.mem_sdiff.mp hb).1
            exact (Finset.mem_sdiff.mp hb).2 (Finset.mem_filter.mpr ⟨hbS, hlt⟩)
          rcases hrow with ⟨h, l, t, _, _, hpick1, hpick2⟩
          by_cases hL : L.eval (fun x => val x h) = true
          · have h2 : (BTree.or L R).pick val h t = cl (L.pick val h t) := BTree.pick_or_left val L R h t hL
            rw [h2] at hpick2
            rw [← hpick2] at hbNotL
            exact hbNotL (L.pick val h t).isLt
          · have h1 : (BTree.or L R).pick val h l = cr (R.pick val h l) := BTree.pick_or_right val L R h l hL
            rw [h1] at hpick1
            rw [← hpick1] at haL
            simp [cr, castRight] at haL
      · have hVempty : V = ∅ := Finset.not_nonempty_iff_eq_empty.mp hV
        have hAllL : ∀ a ∈ S, a.val < L.leaves := by
          intro a ha
          by_contra hnot
          have : a ∈ V := Finset.mem_sdiff.mpr ⟨ha, fun hmem => hnot (Finset.mem_filter.mp hmem).2⟩
          rw [hVempty] at this
          exact Finset.notMem_empty a this
        let SL : Finset (Fin L.leaves) := Finset.univ.filter (fun i => cl i ∈ S)
        have hSimg : S = SL.image cl := by
          ext a
          constructor
          · intro ha
            have hlt := hAllL a ha
            exact Finset.mem_image.mpr ⟨⟨a.val, hlt⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩, by ext; rfl⟩
          · intro ha
            rcases Finset.mem_image.mp ha with ⟨i, hi, rfl⟩
            exact (Finset.mem_filter.mp hi).2
        have hSLcard : 2 ≤ SL.card := by
          rw [hSimg, Finset.card_image_of_injective SL hInjL] at hS
          exact hS
        have hstep := ihL SL hSLcard
        rw [hSimg]
        have hLeftPick : ∀ h l i,
            cellOf val (BTree.or L R) h l →
            (BTree.or L R).pick val h l = cl i →
            cellOf val L h l ∧ L.pick val h l = i := by
          intro h l i hcell hp
          simp only [cellOf, BTree.eval, Bool.or_eq_false_iff] at hcell
          by_cases hL : L.eval (fun x => val x h) = true
          · have h1 : (BTree.or L R).pick val h l = cl (L.pick val h l) := BTree.pick_or_left val L R h l hL
            rw [h1] at hp
            exact ⟨⟨hL, hcell.2.1⟩, hInjL hp⟩
          · have h1 : (BTree.or L R).pick val h l = cr (R.pick val h l) := BTree.pick_or_right val L R h l hL
            rw [h1] at hp
            have hlt := i.isLt
            have heq := congrArg Fin.val hp
            simp [cl, cr, castLeft, castRight] at heq
            omega
        rcases hstep with hrow | hcol
        · left
          apply splitOf_push hInjL _ hrow
          rintro x y ⟨h, l, t, hc1, hc2, hp1, hp2⟩
          have ⟨hc1', hp1'⟩ := hLeftPick h l x hc1 hp1
          have ⟨hc2', hp2'⟩ := hLeftPick h t y hc2 hp2
          exact ⟨h, l, t, hc1', hc2', hp1', hp2'⟩
        · right
          apply splitOf_push hInjL _ hcol
          rintro x y ⟨h, l, t, hc1, hc2, hp1, hp2⟩
          have ⟨hc1', hp1'⟩ := hLeftPick h l x hc1 hp1
          have ⟨hc2', hp2'⟩ := hLeftPick t l y hc2 hp2
          exact ⟨h, l, t, hc1', hc2', hp1', hp2'⟩
    · have hUempty : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hU
      have hAllR : ∀ a ∈ S, L.leaves ≤ a.val := by
        intro a ha
        by_contra hnot
        have hlt : a.val < L.leaves := by omega
        have : a ∈ U := Finset.mem_filter.mpr ⟨ha, hlt⟩
        rw [hUempty] at this
        exact Finset.notMem_empty a this
      let SR : Finset (Fin R.leaves) := Finset.univ.filter (fun j => cr j ∈ S)
      have hSimg : S = SR.image cr := by
        ext a
        constructor
        · intro ha
          have hge := hAllR a ha
          have hlt : a.val - L.leaves < R.leaves := by
            have := a.isLt; simp [BTree.leaves] at this; omega
          have heq : cr ⟨a.val - L.leaves, hlt⟩ = a := by
            ext; simp [cr, castRight]; omega
          refine Finset.mem_image.mpr ⟨⟨a.val - L.leaves, hlt⟩, ?_, heq⟩
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          rw [heq]; exact ha
        · intro ha
          rcases Finset.mem_image.mp ha with ⟨j, hj, rfl⟩
          exact (Finset.mem_filter.mp hj).2
      have hSRcard : 2 ≤ SR.card := by
        rw [hSimg, Finset.card_image_of_injective SR hInjR] at hS
        exact hS
      have hstep := ihR SR hSRcard
      rw [hSimg]
      have hRightPick : ∀ h l j,
          cellOf val (BTree.or L R) h l →
          (BTree.or L R).pick val h l = cr j →
          cellOf val R h l ∧ R.pick val h l = j := by
        intro h l j hcell hp
        simp only [cellOf, BTree.eval, Bool.or_eq_true, Bool.or_eq_false_iff] at hcell
        by_cases hL : L.eval (fun x => val x h) = true
        · have h1 : (BTree.or L R).pick val h l = cl (L.pick val h l) := BTree.pick_or_left val L R h l hL
          rw [h1] at hp
          have hlt := (L.pick val h l).isLt
          have heq := congrArg Fin.val hp
          simp [cl, cr, castLeft, castRight] at heq
          omega
        · have h1 : (BTree.or L R).pick val h l = cr (R.pick val h l) := BTree.pick_or_right val L R h l hL
          rw [h1] at hp
          have hR : R.eval (fun a => val a h) = true := by
            rcases hcell.1 with h1' | h2'
            · exact False.elim (hL h1')
            · exact h2'
          exact ⟨⟨hR, hcell.2.2⟩, hInjR hp⟩
      rcases hstep with hrow | hcol
      · left
        apply splitOf_push hInjR _ hrow
        rintro x y ⟨h, l, t, hc1, hc2, hp1, hp2⟩
        have ⟨hc1', hp1'⟩ := hRightPick h l x hc1 hp1
        have ⟨hc2', hp2'⟩ := hRightPick h t y hc2 hp2
        exact ⟨h, l, t, hc1', hc2', hp1', hp2'⟩
      · right
        apply splitOf_push hInjR _ hcol
        rintro x y ⟨h, l, t, hc1, hc2, hp1, hp2⟩
        have ⟨hc1', hp1'⟩ := hRightPick h l x hc1 hp1
        have ⟨hc2', hp2'⟩ := hRightPick t l y hc2 hp2
        exact ⟨h, l, t, hc1', hc2', hp1', hp2'⟩

/-! ### Section 3: Direction (<-): Compiling row/col stage cuts into a monotone circuit -/

private theorem build_rect_tree {m R : Nat} (g : Fin m → Bool)
    (f : Fin R → Fin m → Bool) (pick : Fin m → Fin m → Fin R)
    (hsep : ∀ h l, g h = true → g l = false → f (pick h l) h = true ∧ f (pick h l) l = false)
    (hsplit : ∀ S : Finset (Fin R), 2 ≤ S.card →
      splitOf S (fun a b => ∃ h l t, (g h = true ∧ g l = false) ∧ (g h = true ∧ g t = false) ∧
        pick h l = a ∧ pick h t = b) ∨
      splitOf S (fun a b => ∃ h l t, (g h = true ∧ g l = false) ∧ (g t = true ∧ g l = false) ∧
        pick h l = a ∧ pick t l = b)) :
    ∀ (n : Nat) (S : Finset (Fin R)) (H L : Finset (Fin m)),
      S.card = n →
      H.Nonempty → L.Nonempty →
      (∀ h ∈ H, g h = true) →
      (∀ l ∈ L, g l = false) →
      (∀ h ∈ H, ∀ l ∈ L, pick h l ∈ S) →
      (∀ a ∈ S, ∃ h ∈ H, ∃ l ∈ L, pick h l = a) →
      ∃ τ : BTree (Fin R), τ.gates ≤ S.card - 1 ∧
        (∀ h ∈ H, τ.eval (fun a => f a h) = true) ∧
        (∀ l ∈ L, τ.eval (fun a => f a l) = false) := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro S H L hcard hHne hLne hHg hLg hHL hSimg
    by_cases h2 : 2 ≤ S.card
    · rcases hsplit S h2 with hrow | hcol
      · -- Row split -> OR of two subtrees
        rcases hrow with ⟨U, hUne, hUss, hno⟩
        let V : Finset (Fin R) := S \ U
        have hUsub : U ⊆ S := hUss.1
        have hVne : V.Nonempty := by
          rcases Finset.exists_of_ssubset hUss with ⟨b, hbS, hbU⟩
          exact ⟨b, Finset.mem_sdiff.mpr ⟨hbS, hbU⟩⟩
        have hUVcard : U.card + V.card = S.card := by
          have h1 : V.card + U.card = S.card := Finset.card_sdiff_add_card_eq_card hUsub
          omega
        have hUpos : 0 < U.card := Finset.Nonempty.card_pos hUne
        have hVpos : 0 < V.card := Finset.Nonempty.card_pos hVne
        have hUlt : U.card < n := by omega
        have hVlt : V.card < n := by omega
        let HU : Finset (Fin m) := H.filter (fun h => ∀ l ∈ L, pick h l ∈ U)
        let HV : Finset (Fin m) := H.filter (fun h => ∀ l ∈ L, pick h l ∈ V)
        have hUimg : ∀ a ∈ U, ∃ h ∈ HU, ∃ l ∈ L, pick h l = a := by
          intro a haU
          rcases hSimg a (hUsub haU) with ⟨h, hhH, l, hlL, hpick⟩
          refine ⟨h, Finset.mem_filter.mpr ⟨hhH, ?_⟩, l, hlL, hpick⟩
          intro l' hl'L
          by_contra hnotU
          have hmemV : pick h l' ∈ V := Finset.mem_sdiff.mpr ⟨hHL h hhH l' hl'L, hnotU⟩
          exact hno a haU (pick h l') hmemV
            ⟨h, l, l', ⟨hHg h hhH, hLg l hlL⟩, ⟨hHg h hhH, hLg l' hl'L⟩, hpick, rfl⟩
        have hVimg : ∀ b ∈ V, ∃ h ∈ HV, ∃ l ∈ L, pick h l = b := by
          intro b hbV
          rcases hSimg b (Finset.mem_sdiff.mp hbV).1 with ⟨h, hhH, l, hlL, hpick⟩
          refine ⟨h, Finset.mem_filter.mpr ⟨hhH, ?_⟩, l, hlL, hpick⟩
          intro l' hl'L
          refine Finset.mem_sdiff.mpr ⟨hHL h hhH l' hl'L, ?_⟩
          intro hmemU
          exact hno (pick h l') hmemU b hbV
            ⟨h, l', l, ⟨hHg h hhH, hLg l' hl'L⟩, ⟨hHg h hhH, hLg l hlL⟩, rfl, hpick⟩
        have hHUne : HU.Nonempty := by
          rcases hUne with ⟨a, haU⟩
          rcases hUimg a haU with ⟨h, hhHU, _, _, _⟩
          exact ⟨h, hhHU⟩
        have hHVne : HV.Nonempty := by
          rcases hVne with ⟨b, hbV⟩
          rcases hVimg b hbV with ⟨h, hhHV, _, _, _⟩
          exact ⟨h, hhHV⟩
        obtain ⟨τU, hτUg, hτUH, hτUL⟩ := ih U.card hUlt U HU L rfl hHUne hLne
          (fun h hh => hHg h (Finset.mem_filter.mp hh).1) hLg
          (fun h hh l hl => (Finset.mem_filter.mp hh).2 l hl) hUimg
        obtain ⟨τV, hτVg, hτVH, hτVL⟩ := ih V.card hVlt V HV L rfl hHVne hLne
          (fun h hh => hHg h (Finset.mem_filter.mp hh).1) hLg
          (fun h hh l hl => (Finset.mem_filter.mp hh).2 l hl) hVimg
        refine ⟨BTree.or τU τV, ?_, ?_, ?_⟩
        · simp only [BTree.gates]
          omega
        · intro h hhH
          simp only [BTree.eval, Bool.or_eq_true]
          rcases hLne with ⟨l0, hl0L⟩
          by_cases hmU : pick h l0 ∈ U
          · left
            apply hτUH
            refine Finset.mem_filter.mpr ⟨hhH, ?_⟩
            intro l' hl'L
            by_contra hnotU
            have hmemV : pick h l' ∈ V := Finset.mem_sdiff.mpr ⟨hHL h hhH l' hl'L, hnotU⟩
            exact hno (pick h l0) hmU (pick h l') hmemV
              ⟨h, l0, l', ⟨hHg h hhH, hLg l0 hl0L⟩, ⟨hHg h hhH, hLg l' hl'L⟩, rfl, rfl⟩
          · right
            apply hτVH
            refine Finset.mem_filter.mpr ⟨hhH, ?_⟩
            intro l' hl'L
            refine Finset.mem_sdiff.mpr ⟨hHL h hhH l' hl'L, ?_⟩
            intro hmemU
            have hmemV0 : pick h l0 ∈ V := Finset.mem_sdiff.mpr ⟨hHL h hhH l0 hl0L, hmU⟩
            exact hno (pick h l') hmemU (pick h l0) hmemV0
              ⟨h, l', l0, ⟨hHg h hhH, hLg l' hl'L⟩, ⟨hHg h hhH, hLg l0 hl0L⟩, rfl, rfl⟩
        · intro l hlL
          simp [BTree.eval, hτUL l hlL, hτVL l hlL]
      · -- Col split -> AND of two subtrees
        rcases hcol with ⟨U, hUne, hUss, hno⟩
        let V : Finset (Fin R) := S \ U
        have hUsub : U ⊆ S := hUss.1
        have hVne : V.Nonempty := by
          rcases Finset.exists_of_ssubset hUss with ⟨b, hbS, hbU⟩
          exact ⟨b, Finset.mem_sdiff.mpr ⟨hbS, hbU⟩⟩
        have hUVcard : U.card + V.card = S.card := by
          have h1 : V.card + U.card = S.card := Finset.card_sdiff_add_card_eq_card hUsub
          omega
        have hUpos : 0 < U.card := Finset.Nonempty.card_pos hUne
        have hVpos : 0 < V.card := Finset.Nonempty.card_pos hVne
        have hUlt : U.card < n := by omega
        have hVlt : V.card < n := by omega
        let LU : Finset (Fin m) := L.filter (fun l => ∀ h ∈ H, pick h l ∈ U)
        let LV : Finset (Fin m) := L.filter (fun l => ∀ h ∈ H, pick h l ∈ V)
        have hUimg : ∀ a ∈ U, ∃ h ∈ H, ∃ l ∈ LU, pick h l = a := by
          intro a haU
          rcases hSimg a (hUsub haU) with ⟨h, hhH, l, hlL, hpick⟩
          refine ⟨h, hhH, l, Finset.mem_filter.mpr ⟨hlL, ?_⟩, hpick⟩
          intro h' hh'H
          by_contra hnotU
          have hmemV : pick h' l ∈ V := Finset.mem_sdiff.mpr ⟨hHL h' hh'H l hlL, hnotU⟩
          exact hno a haU (pick h' l) hmemV
            ⟨h, l, h', ⟨hHg h hhH, hLg l hlL⟩, ⟨hHg h' hh'H, hLg l hlL⟩, hpick, rfl⟩
        have hVimg : ∀ b ∈ V, ∃ h ∈ H, ∃ l ∈ LV, pick h l = b := by
          intro b hbV
          rcases hSimg b (Finset.mem_sdiff.mp hbV).1 with ⟨h, hhH, l, hlL, hpick⟩
          refine ⟨h, hhH, l, Finset.mem_filter.mpr ⟨hlL, ?_⟩, hpick⟩
          intro h' hh'H
          refine Finset.mem_sdiff.mpr ⟨hHL h' hh'H l hlL, ?_⟩
          intro hmemU
          exact hno (pick h' l) hmemU b hbV
            ⟨h', l, h, ⟨hHg h' hh'H, hLg l hlL⟩, ⟨hHg h hhH, hLg l hlL⟩, rfl, hpick⟩
        have hLUne : LU.Nonempty := by
          rcases hUne with ⟨a, haU⟩
          rcases hUimg a haU with ⟨_, _, l, hlLU, _⟩
          exact ⟨l, hlLU⟩
        have hLVne : LV.Nonempty := by
          rcases hVne with ⟨b, hbV⟩
          rcases hVimg b hbV with ⟨_, _, l, hlLV, _⟩
          exact ⟨l, hlLV⟩
        obtain ⟨τU, hτUg, hτUH, hτUL⟩ := ih U.card hUlt U H LU rfl hHne hLUne
          hHg (fun l hl => hLg l (Finset.mem_filter.mp hl).1)
          (fun h hh l hl => (Finset.mem_filter.mp hl).2 h hh) hUimg
        obtain ⟨τV, hτVg, hτVH, hτVL⟩ := ih V.card hVlt V H LV rfl hHne hLVne
          hHg (fun l hl => hLg l (Finset.mem_filter.mp hl).1)
          (fun h hh l hl => (Finset.mem_filter.mp hl).2 h hh) hVimg
        refine ⟨BTree.and τU τV, ?_, ?_, ?_⟩
        · simp only [BTree.gates]
          omega
        · intro h hhH
          simp [BTree.eval, hτUH h hhH, hτVH h hhH]
        · intro l hlL
          simp only [BTree.eval, Bool.and_eq_false_iff]
          rcases hHne with ⟨h0, hh0H⟩
          by_cases hmU : pick h0 l ∈ U
          · left
            apply hτUL
            refine Finset.mem_filter.mpr ⟨hlL, ?_⟩
            intro h' hh'H
            by_contra hnotU
            have hmemV : pick h' l ∈ V := Finset.mem_sdiff.mpr ⟨hHL h' hh'H l hlL, hnotU⟩
            exact hno (pick h0 l) hmU (pick h' l) hmemV
              ⟨h0, l, h', ⟨hHg h0 hh0H, hLg l hlL⟩, ⟨hHg h' hh'H, hLg l hlL⟩, rfl, rfl⟩
          · right
            apply hτVL
            refine Finset.mem_filter.mpr ⟨hlL, ?_⟩
            intro h' hh'H
            refine Finset.mem_sdiff.mpr ⟨hHL h' hh'H l hlL, ?_⟩
            intro hmemU
            have hmemV0 : pick h0 l ∈ V := Finset.mem_sdiff.mpr ⟨hHL h0 hh0H l hlL, hmU⟩
            exact hno (pick h' l) hmemU (pick h0 l) hmemV0
              ⟨h', l, h0, ⟨hHg h' hh'H, hLg l hlL⟩, ⟨hHg h0 hh0H, hLg l hlL⟩, rfl, rfl⟩
    · -- Base case: S.card < 2 (hence S is a singleton)
      rcases hHne with ⟨h0, hh0H⟩
      rcases hLne with ⟨l0, hl0L⟩
      let a0 : Fin R := pick h0 l0
      have ha0S : a0 ∈ S := hHL h0 hh0H l0 hl0L
      have huniq : ∀ a ∈ S, a = a0 := by
        intro a haS
        by_contra hne
        have hsub : ({a, a0} : Finset (Fin R)) ⊆ S := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact haS
          · exact ha0S
        have hpair : ({a, a0} : Finset (Fin R)).card = 2 := Finset.card_pair hne
        have hle := Finset.card_le_card hsub
        omega
      refine ⟨BTree.leaf a0, by simp [BTree.gates], ?_, ?_⟩
      · intro h hhH
        have heq : pick h l0 = a0 := huniq (pick h l0) (hHL h hhH l0 hl0L)
        have hs := hsep h l0 (hHg h hhH) (hLg l0 hl0L)
        rw [heq] at hs
        exact hs.1
      · intro l hlL
        have heq : pick h0 l = a0 := huniq (pick h0 l) (hHL h0 hh0H l hlL)
        have hs := hsep h0 l (hHg h0 hh0H) (hLg l hlL)
        rw [heq] at hs
        exact hs.2

private theorem build_stage_tree {m R : Nat} (g : Fin m → Bool)
    (f : Fin R → Fin m → Bool) (pick : Fin m → Fin m → Fin R)
    (hH : ∃ h, g h = true) (hL : ∃ l, g l = false)
    (hsep : ∀ h l, g h = true → g l = false → f (pick h l) h = true ∧ f (pick h l) l = false)
    (hsplit : ∀ S : Finset (Fin R), 2 ≤ S.card →
      splitOf S (fun a b => ∃ h l t, (g h = true ∧ g l = false) ∧ (g h = true ∧ g t = false) ∧
        pick h l = a ∧ pick h t = b) ∨
      splitOf S (fun a b => ∃ h l t, (g h = true ∧ g l = false) ∧ (g t = true ∧ g l = false) ∧
        pick h l = a ∧ pick t l = b)) :
    ∃ τ : BTree (Fin R), τ.gates ≤ R - 1 ∧ ∀ t : Fin m, τ.eval (fun a => f a t) = g t := by
  classical
  let H : Finset (Fin m) := Finset.univ.filter (fun h => g h = true)
  let L : Finset (Fin m) := Finset.univ.filter (fun l => g l = false)
  let S : Finset (Fin R) := Finset.univ.filter (fun a => ∃ h ∈ H, ∃ l ∈ L, pick h l = a)
  have hHne : H.Nonempty := by
    rcases hH with ⟨h, hh⟩
    exact ⟨h, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩⟩
  have hLne : L.Nonempty := by
    rcases hL with ⟨l, hl⟩
    exact ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩⟩
  obtain ⟨τ, hτg, hτH, hτL⟩ := build_rect_tree g f pick hsep hsplit S.card S H L rfl hHne hLne
    (fun h hh => (Finset.mem_filter.mp hh).2)
    (fun l hl => (Finset.mem_filter.mp hl).2)
    (fun h hh l hl => Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨h, hh, l, hl, rfl⟩⟩)
    (fun a ha => (Finset.mem_filter.mp ha).2)
  have hScard : S.card ≤ R := by
    calc S.card ≤ (Finset.univ : Finset (Fin R)).card := Finset.card_le_univ S
      _ = R := by simp
  refine ⟨τ, by omega, ?_⟩
  intro t
  cases hgt : g t with
  | true => exact hτH t (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt⟩)
  | false => exact hτL t (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt⟩)

private def compileTree {α : Type} (wireOf : α → Nat) (N : Nat) :
    BTree α → List Gate → List Gate × Nat
  | .leaf a, gs => (gs, wireOf a)
  | .and l r, gs =>
    let p1 := compileTree wireOf N l gs
    let p2 := compileTree wireOf N r p1.1
    (p2.1 ++ [⟨GateOp.and, [p1.2, p2.2]⟩], N + p2.1.length)
  | .or l r, gs =>
    let p1 := compileTree wireOf N l gs
    let p2 := compileTree wireOf N r p1.1
    (p2.1 ++ [⟨GateOp.or, [p1.2, p2.2]⟩], N + p2.1.length)

private def GoodGates (N : Nat) (gs : List Gate) : Prop :=
  (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
  ReadsBack N ⟨gs, 0⟩

private theorem goodGates_snoc {N : Nat} {gs : List Gate} {g : Gate}
    (hG : GoodGates N gs)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : g.inputs.length ≤ 2)
    (hin : ∀ i ∈ g.inputs, i < N + gs.length) :
    GoodGates N (gs ++ [g]) := by
  refine ⟨?_, ?_⟩
  · intro g' hg'
    rw [List.mem_append, List.mem_singleton] at hg'
    rcases hg' with hg' | rfl
    · exact hG.1 g' hg'
    · exact ⟨hop, hlen⟩
  · intro k hk i hi
    rw [gateAt_eq ⟨gs ++ [g], 0⟩ hk] at hi
    rw [List.length_append, List.length_singleton] at hk
    by_cases hlt : k < gs.length
    · have hget : (gs ++ [g])[k] = gs[k] := List.getElem_append_left hlt
      rw [hget] at hi
      have hrb := hG.2 k hlt i
      rw [gateAt_eq ⟨gs, 0⟩ hlt] at hrb
      exact hrb hi
    · have hkEq : k = gs.length := by omega
      subst hkEq
      have hget : (gs ++ [g])[gs.length] = g := by simp
      rw [hget] at hi
      exact hin i hi

private theorem compileTree_spec {α : Type} (wireOf : α → Nat) (N : Nat)
    (τ : BTree α) (gs : List Gate)
    (hGood : GoodGates N gs)
    (hW : ∀ a, wireOf a < N + gs.length) :
    let res := compileTree wireOf N τ gs
    (∃ ext, res.1 = gs ++ ext) ∧
    res.1.length = gs.length + τ.gates ∧
    GoodGates N res.1 ∧
    res.2 < N + res.1.length ∧
    ∀ x : List Bool, x.length = N →
      valC res.1 x res.2 = τ.eval (fun a => valC gs x (wireOf a)) := by
  induction τ generalizing gs with
  | leaf a =>
    refine ⟨⟨[], by simp [compileTree]⟩, by simp [compileTree, BTree.gates], hGood, hW a, ?_⟩
    intro x _
    rfl
  | and L R ihL ihR =>
    simp only [compileTree, BTree.gates]
    obtain ⟨⟨ext1, hext1⟩, hlen1, hGood1, hout1, heval1⟩ := ihL gs hGood hW
    have hW1 : ∀ a, wireOf a < N + (compileTree wireOf N L gs).1.length := by
      intro a; have := hW a; omega
    obtain ⟨⟨ext2, hext2⟩, hlen2, hGood2, hout2, heval2⟩ := ihR (compileTree wireOf N L gs).1 hGood1 hW1
    set p1 := compileTree wireOf N L gs
    set p2 := compileTree wireOf N R p1.1
    set g : Gate := ⟨GateOp.and, [p1.2, p2.2]⟩
    have hout1' : p1.2 < N + p2.1.length := by omega
    refine ⟨⟨ext1 ++ ext2 ++ [g], by rw [hext2, hext1]; simp [List.append_assoc]⟩,
      by simp [hlen2, hlen1]; omega, ?_, by simp, ?_⟩
    · apply goodGates_snoc hGood2 (Or.inl rfl) (by simp [g])
      intro i hi
      simp only [g, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact hout1'
      · exact hout2
    · intro x hx
      rw [← hx, valC_snoc_last]
      simp only [g, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id,
        Bool.and_true, BTree.eval]
      have hL1 : valC p2.1 x p1.2 = valC p1.1 x p1.2 := by
        rw [hext2]
        apply valC_append_lt
        rw [hx]; exact hout1
      rw [hL1, heval1 x hx, heval2 x hx]
      congr 1
      have hRfun : (fun a => valC p1.1 x (wireOf a)) = (fun a => valC gs x (wireOf a)) := by
        funext a
        rw [hext1]
        apply valC_append_lt
        rw [hx]; exact hW a
      rw [hRfun]
  | or L R ihL ihR =>
    simp only [compileTree, BTree.gates]
    obtain ⟨⟨ext1, hext1⟩, hlen1, hGood1, hout1, heval1⟩ := ihL gs hGood hW
    have hW1 : ∀ a, wireOf a < N + (compileTree wireOf N L gs).1.length := by
      intro a; have := hW a; omega
    obtain ⟨⟨ext2, hext2⟩, hlen2, hGood2, hout2, heval2⟩ := ihR (compileTree wireOf N L gs).1 hGood1 hW1
    set p1 := compileTree wireOf N L gs
    set p2 := compileTree wireOf N R p1.1
    set g : Gate := ⟨GateOp.or, [p1.2, p2.2]⟩
    have hout1' : p1.2 < N + p2.1.length := by omega
    refine ⟨⟨ext1 ++ ext2 ++ [g], by rw [hext2, hext1]; simp [List.append_assoc]⟩,
      by simp [hlen2, hlen1]; omega, ?_, by simp, ?_⟩
    · apply goodGates_snoc hGood2 (Or.inr rfl) (by simp [g])
      intro i hi
      simp only [g, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact hout1'
      · exact hout2
    · intro x hx
      rw [← hx, valC_snoc_last]
      simp only [g, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
        Bool.or_false, BTree.eval]
      have hL1 : valC p2.1 x p1.2 = valC p1.1 x p1.2 := by
        rw [hext2]
        apply valC_append_lt
        rw [hx]; exact hout1
      rw [hL1, heval1 x hx, heval2 x hx]
      congr 1
      have hRfun : (fun a => valC p1.1 x (wireOf a)) = (fun a => valC gs x (wireOf a)) := by
        funext a
        rw [hext1]
        apply valC_append_lt
        rw [hx]; exact hW a
      rw [hRfun]

private theorem backward_dir (d m e : Nat) (X : Fin m → Fin d → Bool) (T : Fin m → Bool)
    (hd : 0 < d)
    (c : Nat) (Z : Nat → Fin m → Bool) (r : Fin (c + 1) → Nat)
    (src : (j : Fin (c + 1)) → Fin (r j) → Nat)
    (pick : (j : Fin (c + 1)) → Fin m → Fin m → Fin (r j))
    (hrsum : Finset.univ.sum r ≤ d + e + c)
    (hZbase : ∀ i : Fin d, Z i.val = fun t => X t i)
    (hZtop : Z (d + c) = T)
    (hstage : ∀ j : Fin (c + 1), 0 < r j ∧ (∀ a, src j a < d + j.val) ∧
      (∃ h, Z (d + j.val) h = true) ∧ (∃ l, Z (d + j.val) l = false) ∧
      (∀ h l, (Z (d + j.val) h = true ∧ Z (d + j.val) l = false) →
        Z (src j (pick j h l)) h = true ∧ Z (src j (pick j h l)) l = false) ∧
      ∀ S : Finset (Fin (r j)), 2 ≤ S.card →
        splitOf S (fun a b => ∃ h l t,
          (Z (d + j.val) h = true ∧ Z (d + j.val) l = false) ∧
          (Z (d + j.val) h = true ∧ Z (d + j.val) t = false) ∧
          pick j h l = a ∧ pick j h t = b) ∨
        splitOf S (fun a b => ∃ h l t,
          (Z (d + j.val) h = true ∧ Z (d + j.val) l = false) ∧
          (Z (d + j.val) t = true ∧ Z (d + j.val) l = false) ∧
          pick j h l = a ∧ pick j t l = b)) :
    ∃ C : Circuit,
      FanInTwo C ∧ ReadsBack (d + 2) C ∧
      notCount C = 0 ∧ C.output < d + 2 + C.size ∧ C.size ≤ d - 1 + e ∧
      ∀ t, C.eval (List.ofFn (X t) ++ [false, true]) = T t := by
  have hbuild : ∀ k ≤ c + 1,
      ∃ (gs : List Gate) (wireOf : Nat → Nat),
        GoodGates (d + 2) gs ∧
        gs.length ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin (c + 1) => j.val < k), (r j - 1) ∧
        ∀ u < d + k, wireOf u < d + 2 + gs.length ∧
          ∀ t, valC gs (mkInput (X t)) (wireOf u) = Z u t := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨[], id, ⟨by simp, by intro j hj; simp at hj⟩, by simp, ?_⟩
      intro u hu
      have hu' : u < d := by omega
      refine ⟨by simp; omega, ?_⟩
      intro t
      dsimp only [id]
      rw [valC_input [] (mkInput (X t)) (by rw [mkInput_length]; omega)]
      have h1 := mkInput_getD_var (X t) ⟨u, hu'⟩
      have h2 := congrFun (hZbase ⟨u, hu'⟩) t
      simpa using h1.trans h2.symm
    | succ k ih =>
      intro hk
      obtain ⟨gs, wireOf, hGood, hlen, hInv⟩ := ih (by omega)
      let j : Fin (c + 1) := ⟨k, by omega⟩
      have hsj := hstage j
      obtain ⟨τ, hτg, hτeval⟩ := build_stage_tree (Z (d + k))
        (fun a => Z (src j a)) (pick j) hsj.2.2.1 hsj.2.2.2.1
        (fun h l hh hl => hsj.2.2.2.2.1 h l ⟨hh, hl⟩) hsj.2.2.2.2.2
      have hWsrc : ∀ a : Fin (r j), wireOf (src j a) < d + 2 + gs.length :=
        fun a => (hInv (src j a) (hsj.2.1 a)).1
      have hcomp := compileTree_spec (fun a => wireOf (src j a)) (d + 2) τ gs hGood hWsrc
      set res := compileTree (fun a => wireOf (src j a)) (d + 2) τ gs
      rcases hcomp with ⟨⟨ext, hext⟩, hreslen, hresGood, hresout, hreseval⟩
      let wireOf' : Nat → Nat := fun u => if u = d + k then res.2 else wireOf u
      refine ⟨res.1, wireOf', hresGood, ?_, ?_⟩
      · have hfilt : Finset.univ.filter (fun i : Fin (c + 1) => i.val < k + 1) =
            insert j (Finset.univ.filter (fun i : Fin (c + 1) => i.val < k)) := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, j, Fin.ext_iff]
          omega
        have hjNot : j ∉ Finset.univ.filter (fun i : Fin (c + 1) => i.val < k) := by
          simp [j]
        rw [hfilt, Finset.sum_insert hjNot]
        omega
      · intro u hu
        by_cases huEq : u = d + k
        · subst huEq
          refine ⟨by simp [wireOf', hresout], ?_⟩
          intro t
          simp only [wireOf', ite_true]
          rw [hreseval (mkInput (X t)) (mkInput_length (X t))]
          have hfun : (fun a => valC gs (mkInput (X t)) (wireOf (src j a))) =
              (fun a => Z (src j a) t) := by
            funext a
            exact (hInv (src j a) (hsj.2.1 a)).2 t
          rw [hfun]
          exact hτeval t
        · have huLt : u < d + k := by omega
          have hprev := hInv u huLt
          refine ⟨by simp [wireOf', huEq]; omega, ?_⟩
          intro t
          simp only [wireOf', huEq, ite_false]
          rw [hext, valC_append_lt gs ext (mkInput (X t)) (by rw [mkInput_length]; exact hprev.1)]
          exact hprev.2 t
  obtain ⟨gs, wireOf, hGood, hlen, hInv⟩ := hbuild (c + 1) (Nat.le_refl _)
  have hfiltAll : Finset.univ.filter (fun j : Fin (c + 1) => j.val < c + 1) = Finset.univ := by
    apply Finset.filter_true_of_mem
    intro j _
    exact j.isLt
  rw [hfiltAll] at hlen
  have hsum_add : (∑ j : Fin (c + 1), (r j - 1)) + (c + 1) = ∑ j : Fin (c + 1), r j := by
    calc (∑ j : Fin (c + 1), (r j - 1)) + (c + 1)
        = (∑ j : Fin (c + 1), (r j - 1)) + ∑ _j : Fin (c + 1), 1 := by simp
      _ = ∑ j : Fin (c + 1), ((r j - 1) + 1) := by rw [← Finset.sum_add_distrib]
      _ = ∑ j : Fin (c + 1), r j := by
          apply Finset.sum_congr rfl
          intro j _
          have := (hstage j).1
          omega
  have hrsum' : ∑ j : Fin (c + 1), r j ≤ d + e + c := hrsum
  have hsz : gs.length ≤ d - 1 + e := by omega
  have hout := hInv (d + c) (by omega)
  refine ⟨⟨gs, wireOf (d + c)⟩, ?_, hGood.2, ?_, hout.1, hsz, ?_⟩
  · intro g hg
    have h1 := hGood.1 g hg
    refine ⟨?_, h1.2⟩
    rcases h1.1 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rw [notCount_eq_zero_iff]
    intro g hg hnot
    rcases (hGood.1 g hg).1 with h | h <;> rw [h] at hnot <;> cases hnot
  · intro t
    rw [eval_eq_valC]
    change valC gs (mkInput (X t)) (wireOf (d + c)) = T t
    rw [hout.2 t, hZtop]

/-! ### Section 4: Direction (->): Clean binary DAG, trimming, wire-use counting, and tree decomposition -/

private inductive BOp where
  | and
  | or

private def BOp.eval : BOp → Bool → Bool → Bool
  | .and, a, b => a && b
  | .or, a, b => a || b

private structure BGate where
  op : BOp
  lhs : Nat
  rhs : Nat

private def bGateStep (w : List Bool) (g : BGate) : List Bool :=
  w ++ [g.op.eval (w.getD g.lhs false) (w.getD g.rhs false)]

private theorem bfold_length (gs : List BGate) (x : List Bool) :
    (gs.foldl bGateStep x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, bGateStep, List.length_append, List.length_cons, List.length_nil]
    omega

private theorem bfold_getD_lt (gs : List BGate) (x : List Bool) {i : Nat} (hi : i < x.length) :
    (gs.foldl bGateStep x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    have hlt : i < (bGateStep x g).length := by
      simp only [bGateStep, List.length_append, List.length_singleton]
      omega
    rw [List.foldl_cons, ih (bGateStep x g) hlt]
    exact List.getD_append _ _ _ _ hi

private def valB {d m : Nat} (X : Fin m → Fin d → Bool) (gs : List BGate)
    (w : Nat) (t : Fin m) : Bool :=
  (gs.foldl bGateStep (List.ofFn (X t))).getD w false

private theorem valB_var {d m : Nat} (X : Fin m → Fin d → Bool) (gs : List BGate)
    (i : Fin d) (t : Fin m) :
    valB X gs i.val t = X t i := by
  unfold valB
  have hi : i.val < (List.ofFn (X t)).length := by simp
  rw [bfold_getD_lt gs (List.ofFn (X t)) hi]
  simp [List.getD, hi]

private theorem valB_append_lt {d m : Nat} (X : Fin m → Fin d → Bool) (gs1 gs2 : List BGate)
    {w : Nat} (hw : w < d + gs1.length) (t : Fin m) :
    valB X (gs1 ++ gs2) w t = valB X gs1 w t := by
  unfold valB
  rw [List.foldl_append]
  apply bfold_getD_lt
  rw [bfold_length, List.length_ofFn]
  exact hw

private theorem valB_snoc_last {d m : Nat} (X : Fin m → Fin d → Bool) (gs : List BGate)
    (g : BGate) (t : Fin m) :
    valB X (gs ++ [g]) (d + gs.length) t =
      g.op.eval (valB X gs g.lhs t) (valB X gs g.rhs t) := by
  unfold valB
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hlen : (gs.foldl bGateStep (List.ofFn (X t))).length = d + gs.length := by
    rw [bfold_length, List.length_ofFn]
  set w := gs.foldl bGateStep (List.ofFn (X t))
  rw [← hlen]
  simp only [bGateStep]
  rw [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self]
  rfl

private def BReadsBack (d : Nat) (gs : List BGate) : Prop :=
  ∀ k (hk : k < gs.length), gs[k].lhs < d + k ∧ gs[k].rhs < d + k

private theorem bReadsBack_snoc {d : Nat} {gs : List BGate} {g : BGate}
    (hRB : BReadsBack d gs) (hl : g.lhs < d + gs.length) (hr : g.rhs < d + gs.length) :
    BReadsBack d (gs ++ [g]) := by
  intro k hk
  rw [List.length_append, List.length_singleton] at hk
  by_cases hlt : k < gs.length
  · have hget : (gs ++ [g])[k] = gs[k] := List.getElem_append_left hlt
    rw [hget]
    exact hRB k hlt
  · have hkEq : k = gs.length := by omega
    subst hkEq
    have hget : (gs ++ [g])[gs.length] = g := by simp
    rw [hget]
    exact ⟨hl, hr⟩

private theorem valB_gate {d m : Nat} (X : Fin m → Fin d → Bool) (gs : List BGate)
    (hRB : BReadsBack d gs) {k : Nat} (hk : k < gs.length) (t : Fin m) :
    valB X gs (d + k) t = gs[k].op.eval (valB X gs gs[k].lhs t) (valB X gs gs[k].rhs t) := by
  have hsplit : gs = (gs.take k ++ [gs[k]]) ++ gs.drop (k + 1) := by
    rw [List.append_assoc, List.singleton_append]
    have h1 : gs[k] :: gs.drop (k + 1) = gs.drop k := by
      simp [List.cons_getElem_drop_succ]
    rw [h1, List.take_append_drop]
  have htk : (gs.take k).length = k := List.length_take_of_le (Nat.le_of_lt hk)
  have hlt1 : d + k < d + (gs.take k ++ [gs[k]]).length := by
    rw [List.length_append, htk, List.length_singleton]; omega
  have h1 : valB X gs (d + k) t = valB X (gs.take k ++ [gs[k]]) (d + k) t := by
    conv_lhs => rw [hsplit]
    exact valB_append_lt X _ _ hlt1 t
  have h2 := valB_snoc_last X (gs.take k) gs[k] t
  rw [htk] at h2
  rw [h1, h2]
  have hlhs : valB X (gs.take k) gs[k].lhs t = valB X gs gs[k].lhs t := by
    have h := valB_append_lt X (gs.take k) (gs.drop k) (w := gs[k].lhs) (by rw [htk]; exact (hRB k hk).1) t
    rw [List.take_append_drop] at h
    exact h.symm
  have hrhs : valB X (gs.take k) gs[k].rhs t = valB X gs gs[k].rhs t := by
    have h := valB_append_lt X (gs.take k) (gs.drop k) (w := gs[k].rhs) (by rw [htk]; exact (hRB k hk).2) t
    rw [List.take_append_drop] at h
    exact h.symm
  rw [hlhs, hrhs]

private def NonConst {d m : Nat} (X : Fin m → Fin d → Bool) (gs : List BGate) : Prop :=
  ∀ w < d + gs.length, (∃ h, valB X gs w h = true) ∧ (∃ l, valB X gs w l = false)

private inductive WireRep where
  | const (b : Bool)
  | wire (idx : Nat)

private theorem simplify_circuit {d m : Nat} (X : Fin m → Fin d → Bool) (T : Fin m → Bool)
    (hd : 0 < d)
    (hsep : ∀ i : Fin d, ∃ h l, T h = true ∧ T l = false ∧
      ∀ j, (X h j = true ∧ X l j = false) ↔ j = i)
    (C : Circuit) (hF : FanInTwo C) (hRB : ReadsBack (d + 2) C)
    (hN : notCount C = 0) (hout : C.output < d + 2 + C.size)
    (heval : ∀ t, C.eval (mkInput (X t)) = T t) :
    ∃ (gs : List BGate) (out : Nat),
      gs.length ≤ C.size ∧ BReadsBack d gs ∧ NonConst X gs ∧
      out < d + gs.length ∧ ∀ t, valB X gs out t = T t := by
  classical
  have hNonConstVars : ∀ i : Fin d, (∃ h, X h i = true) ∧ (∃ l, X l i = false) := by
    intro i
    rcases hsep i with ⟨h, l, _, _, hiff⟩
    have hi := (hiff i).mpr rfl
    exact ⟨⟨h, hi.1⟩, ⟨l, hi.2⟩⟩
  have hTnc : (∃ h, T h = true) ∧ (∃ l, T l = false) := by
    rcases hsep ⟨0, hd⟩ with ⟨h, l, hh, hl, _⟩
    exact ⟨⟨h, hh⟩, ⟨l, hl⟩⟩
  have hstep : ∀ k ≤ C.gates.length,
      ∃ (gs : List BGate) (rep : Nat → WireRep),
        gs.length ≤ k ∧ BReadsBack d gs ∧ NonConst X gs ∧
        ∀ w < d + 2 + k, match rep w with
          | .const b => ∀ t, valC C.gates (mkInput (X t)) w = b
          | .wire idx => idx < d + gs.length ∧ ∀ t, valC C.gates (mkInput (X t)) w = valB X gs idx t := by
    intro k
    induction k with
    | zero =>
      intro _
      let rep0 : Nat → WireRep := fun w =>
        if w < d then .wire w else if w = d then .const false else .const true
      refine ⟨[], rep0, Nat.le_refl 0, by intro j hj; simp at hj, ?_, ?_⟩
      · intro w hw
        have hw' : w < d := by simp at hw; exact hw
        rcases hNonConstVars ⟨w, hw'⟩ with ⟨⟨h, hh⟩, ⟨l, hl⟩⟩
        exact ⟨⟨h, by rw [valB_var X [] ⟨w, hw'⟩ h]; exact hh⟩,
               ⟨l, by rw [valB_var X [] ⟨w, hw'⟩ l]; exact hl⟩⟩
      · intro w hw
        by_cases h1 : w < d
        · simp only [rep0, h1, ite_true]
          refine ⟨by simp; exact h1, ?_⟩
          intro t
          rw [valC_input C.gates (mkInput (X t)) (by rw [mkInput_length]; omega)]
          rw [valB_var X [] ⟨w, h1⟩ t]
          exact mkInput_getD_var (X t) ⟨w, h1⟩
        · by_cases h2 : w = d
          · dsimp only [rep0]
            rw [if_neg h1, if_pos h2]
            dsimp only
            intro t
            rw [h2, valC_input C.gates (mkInput (X t)) (by rw [mkInput_length]; omega)]
            exact mkInput_getD_false (X t)
          · have h3 : w = d + 1 := by omega
            dsimp only [rep0]
            rw [if_neg h1, if_neg h2]
            dsimp only
            intro t
            rw [h3, valC_input C.gates (mkInput (X t)) (by rw [mkInput_length]; omega)]
            exact mkInput_getD_true (X t)
    | succ k ih =>
      intro hk
      obtain ⟨gs, rep, hlen, hBRB, hNC, hRep⟩ := ih (by omega)
      have hklt : k < C.gates.length := by omega
      let g : Gate := C.gates[k]
      let f : Fin m → Bool := fun t => valC C.gates (mkInput (X t)) (d + 2 + k)
      by_cases hcf : ∀ t, f t = false
      · let rep' : Nat → WireRep := fun w => if w = d + 2 + k then .const false else rep w
        refine ⟨gs, rep', by omega, hBRB, hNC, ?_⟩
        intro w hw
        by_cases hweq : w = d + 2 + k
        · subst hweq; simpa [rep'] using hcf
        · simp only [rep', hweq, ite_false]; exact hRep w (by omega)
      · by_cases hct : ∀ t, f t = true
        · let rep' : Nat → WireRep := fun w => if w = d + 2 + k then .const true else rep w
          refine ⟨gs, rep', by omega, hBRB, hNC, ?_⟩
          intro w hw
          by_cases hweq : w = d + 2 + k
          · subst hweq; simpa [rep'] using hct
          · simp only [rep', hweq, ite_false]; exact hRep w (by omega)
        · -- f is non-constant on Fin m!
          have hfH : ∃ h, f h = true := by
            by_contra hno
            apply hcf
            intro t
            cases hft : f t with
            | false => rfl
            | true => exact False.elim (hno ⟨t, hft⟩)
          have hfL : ∃ l, f l = false := by
            by_contra hno
            apply hct
            intro t
            cases hft : f t with
            | true => rfl
            | false => exact False.elim (hno ⟨t, hft⟩)
          have hgprop := mono_gate_props hF hN g (List.getElem_mem hklt)
          have hfeq : ∀ t, f t = g.op.eval (g.inputs.map fun i => valC C.gates (mkInput (X t)) i) := by
            intro t
            have h1 := valC_gate C (mkInput (X t)) (by rw [mkInput_length]; exact hRB) hklt
            rw [mkInput_length] at h1
            exact h1
          have hinLt : ∀ i ∈ g.inputs, i < d + 2 + k := by
            intro i hi
            have h1 := hRB k hklt i
            rw [gateAt_eq C hklt] at h1
            exact h1 hi
          -- Case split on g.inputs (length ≤ 2)
          cases hgin : g.inputs with
          | nil =>
            exfalso
            rcases hgprop.1 with hop | hop
            · apply hct; intro t; rw [hfeq t, hgin, hop]; rfl
            · apply hcf; intro t; rw [hfeq t, hgin, hop]; rfl
          | cons u rest =>
            cases rest with
            | nil =>
              have huLt : u < d + 2 + k := hinLt u (by simp [hgin])
              have hfu : ∀ t, f t = valC C.gates (mkInput (X t)) u := by
                intro t
                rw [hfeq t, hgin]
                rcases hgprop.1 with hop | hop <;> simp [hop, GateOp.eval]
              have hru := hRep u huLt
              cases hrepU : rep u with
              | const b =>
                exfalso
                rw [hrepU] at hru
                cases b
                · exact hcf (fun t => (hfu t).trans (hru t))
                · exact hct (fun t => (hfu t).trans (hru t))
              | wire iu =>
                rw [hrepU] at hru
                let rep' : Nat → WireRep := fun w => if w = d + 2 + k then .wire iu else rep w
                refine ⟨gs, rep', by omega, hBRB, hNC, ?_⟩
                intro w hw
                by_cases hweq : w = d + 2 + k
                · subst hweq
                  simp only [rep', ite_true]
                  exact ⟨hru.1, fun t => (hfu t).trans (hru.2 t)⟩
                · simp only [rep', hweq, ite_false]
                  exact hRep w (by omega)
            | cons v rest2 =>
              have hrest2 : rest2 = [] := by
                have hlen2 := hgprop.2
                rw [hgin] at hlen2
                cases rest2 with
                | nil => rfl
                | cons _ _ => simp at hlen2
              subst hrest2
              have huLt : u < d + 2 + k := hinLt u (by simp [hgin])
              have hvLt : v < d + 2 + k := hinLt v (by simp [hgin])
              have hru := hRep u huLt
              have hrv := hRep v hvLt
              obtain ⟨bop, hfuv⟩ : ∃ bop : BOp, ∀ t, f t = bop.eval (valC C.gates (mkInput (X t)) u)
                  (valC C.gates (mkInput (X t)) v) := by
                rcases hgprop.1 with hop | hop
                · exact ⟨BOp.and, fun t => by rw [hfeq t, hgin, hop]; simp [BOp.eval, GateOp.eval]⟩
                · exact ⟨BOp.or, fun t => by rw [hfeq t, hgin, hop]; simp [BOp.eval, GateOp.eval]⟩
              cases hrepU : rep u with
              | const bu =>
                rw [hrepU] at hru
                cases hrepV : rep v with
                | const bv =>
                  exfalso
                  rw [hrepV] at hrv
                  cases hres : bop.eval bu bv
                  · exact hcf (fun t => by rw [hfuv t, hru t, hrv t, hres])
                  · exact hct (fun t => by rw [hfuv t, hru t, hrv t, hres])
                | wire iv =>
                  rw [hrepV] at hrv
                  -- Either f is const (contradiction) or f = valB iv
                  have hfv : ∀ t, f t = valB X gs iv t := by
                    cases bop <;> cases bu
                    · exfalso; exact hcf (fun t => by rw [hfuv t, hru t]; simp [BOp.eval])
                    · intro t; rw [hfuv t, hru t, hrv.2 t]; simp [BOp.eval]
                    · intro t; rw [hfuv t, hru t, hrv.2 t]; simp [BOp.eval]
                    · exfalso; exact hct (fun t => by rw [hfuv t, hru t]; simp [BOp.eval])
                  let rep' : Nat → WireRep := fun w => if w = d + 2 + k then .wire iv else rep w
                  refine ⟨gs, rep', by omega, hBRB, hNC, ?_⟩
                  intro w hw
                  by_cases hweq : w = d + 2 + k
                  · subst hweq; simp only [rep', ite_true]; exact ⟨hrv.1, hfv⟩
                  · simp only [rep', hweq, ite_false]; exact hRep w (by omega)
              | wire iu =>
                rw [hrepU] at hru
                cases hrepV : rep v with
                | const bv =>
                  rw [hrepV] at hrv
                  have hfu : ∀ t, f t = valB X gs iu t := by
                    cases bop <;> cases bv
                    · exfalso; exact hcf (fun t => by rw [hfuv t, hrv t]; simp [BOp.eval])
                    · intro t; rw [hfuv t, hru.2 t, hrv t]; simp [BOp.eval]
                    · intro t; rw [hfuv t, hru.2 t, hrv t]; simp [BOp.eval]
                    · exfalso; exact hct (fun t => by rw [hfuv t, hrv t]; simp [BOp.eval])
                  let rep' : Nat → WireRep := fun w => if w = d + 2 + k then .wire iu else rep w
                  refine ⟨gs, rep', by omega, hBRB, hNC, ?_⟩
                  intro w hw
                  by_cases hweq : w = d + 2 + k
                  · subst hweq; simp only [rep', ite_true]; exact ⟨hru.1, hfu⟩
                  · simp only [rep', hweq, ite_false]; exact hRep w (by omega)
                | wire iv =>
                  rw [hrepV] at hrv
                  let bg : BGate := ⟨bop, iu, iv⟩
                  let gs' : List BGate := gs ++ [bg]
                  let rep' : Nat → WireRep :=
                    fun w => if w = d + 2 + k then .wire (d + gs.length) else rep w
                  have hgs'len : gs'.length = gs.length + 1 := by simp [gs']
                  have hBRB' : BReadsBack d gs' := bReadsBack_snoc hBRB hru.1 hrv.1
                  have hnewEval : ∀ t, valB X gs' (d + gs.length) t = f t := by
                    intro t
                    rw [valB_snoc_last, hfuv t, hru.2 t, hrv.2 t]
                  have hNC' : NonConst X gs' := by
                    intro w hw
                    rw [hgs'len] at hw
                    by_cases hlt : w < d + gs.length
                    · rcases hNC w hlt with ⟨⟨h, hh⟩, ⟨l, hl⟩⟩
                      exact ⟨⟨h, by rw [valB_append_lt X gs [bg] hlt h]; exact hh⟩,
                             ⟨l, by rw [valB_append_lt X gs [bg] hlt l]; exact hl⟩⟩
                    · have hweq : w = d + gs.length := by omega
                      subst hweq
                      rcases hfH with ⟨h, hh⟩
                      rcases hfL with ⟨l, hl⟩
                      exact ⟨⟨h, by rw [hnewEval h]; exact hh⟩,
                             ⟨l, by rw [hnewEval l]; exact hl⟩⟩
                  refine ⟨gs', rep', by omega, hBRB', hNC', ?_⟩
                  intro w hw
                  by_cases hweq : w = d + 2 + k
                  · subst hweq
                    simp only [rep', ite_true]
                    refine ⟨by rw [hgs'len]; omega, fun t => (hnewEval t).symm⟩
                  · simp only [rep', hweq, ite_false]
                    have hrw := hRep w (by omega)
                    cases hrwc : rep w with
                    | const b =>
                      rw [hrwc] at hrw
                      exact hrw
                    | wire iw =>
                      rw [hrwc] at hrw
                      refine ⟨by rw [hgs'len]; omega, ?_⟩
                      intro t
                      rw [hrw.2 t, valB_append_lt X gs [bg] hrw.1 t]
  obtain ⟨gs, rep, hlen, hBRB, hNC, hRep⟩ := hstep C.gates.length (Nat.le_refl _)
  have hrout := hRep C.output hout
  cases hrc : rep C.output with
  | const b =>
    exfalso
    rw [hrc] at hrout
    cases b
    · rcases hTnc.1 with ⟨h, hh⟩
      have := hrout h
      rw [← eval_eq_valC, heval h, hh] at this
      cases this
    · rcases hTnc.2 with ⟨l, hl⟩
      have := hrout l
      rw [← eval_eq_valC, heval l, hl] at this
      cases this
  | wire out =>
    rw [hrc] at hrout
    refine ⟨gs, out, hlen, hBRB, hNC, hrout.1, ?_⟩
    intro t
    have h1 := hrout.2 t
    rw [← eval_eq_valC, heval t] at h1
    exact h1.symm

/-! ### Section 5: Reachability, fan-out counting, and shared-wire tree cut -/

private def reachFrom (d : Nat) (gs : List BGate) (hRB : BReadsBack d gs) (w : Nat) : Finset Nat :=
  if h : d ≤ w ∧ w - d < gs.length then
    insert w (reachFrom d gs hRB (gs[w - d]'(h.2)).lhs ∪ reachFrom d gs hRB (gs[w - d]'(h.2)).rhs)
  else
    {w}
termination_by w
decreasing_by
  · exact Nat.lt_of_lt_of_eq (hRB (w - d) h.2).1 (Nat.add_sub_of_le h.1)
  · exact Nat.lt_of_lt_of_eq (hRB (w - d) h.2).2 (Nat.add_sub_of_le h.1)

private theorem reachFrom_self (d : Nat) (gs : List BGate) (hRB : BReadsBack d gs) (w : Nat) :
    w ∈ reachFrom d gs hRB w := by
  unfold reachFrom
  split_ifs
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_singleton_self _

private theorem reachFrom_le (d : Nat) (gs : List BGate) (hRB : BReadsBack d gs) :
    ∀ w u, u ∈ reachFrom d gs hRB w → u ≤ w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro u hu
    unfold reachFrom at hu
    split_ifs at hu with h
    · rw [Finset.mem_insert, Finset.mem_union] at hu
      rcases hu with rfl | h1 | h2
      · exact Nat.le_refl _
      · have hl : gs[w - d].lhs < w := by have := (hRB (w - d) h.2).1; omega
        have := ih gs[w - d].lhs hl u h1
        omega
      · have hr : gs[w - d].rhs < w := by have := (hRB (w - d) h.2).2; omega
        have := ih gs[w - d].rhs hr u h2
        omega
    · rw [Finset.mem_singleton] at hu
      omega

private theorem reachFrom_closed (d : Nat) (gs : List BGate) (hRB : BReadsBack d gs) :
    ∀ w k (hk : k < gs.length), d + k ∈ reachFrom d gs hRB w →
      gs[k].lhs ∈ reachFrom d gs hRB w ∧ gs[k].rhs ∈ reachFrom d gs hRB w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro k hk hmem
    unfold reachFrom at hmem ⊢
    split_ifs at hmem ⊢ with h
    · rw [Finset.mem_insert, Finset.mem_union] at hmem
      have hl : gs[w - d].lhs < w := by have := (hRB (w - d) h.2).1; omega
      have hr : gs[w - d].rhs < w := by have := (hRB (w - d) h.2).2; omega
      rcases hmem with heq | h1 | h2
      · have hkEq : w - d = k := by omega
        subst hkEq
        exact ⟨Finset.mem_insert_of_mem (Finset.mem_union_left _ (reachFrom_self d gs hRB _)),
               Finset.mem_insert_of_mem (Finset.mem_union_right _ (reachFrom_self d gs hRB _))⟩
      · have r := ih gs[w - d].lhs hl k hk h1
        exact ⟨Finset.mem_insert_of_mem (Finset.mem_union_left _ r.1),
               Finset.mem_insert_of_mem (Finset.mem_union_left _ r.2)⟩
      · have r := ih gs[w - d].rhs hr k hk h2
        exact ⟨Finset.mem_insert_of_mem (Finset.mem_union_right _ r.1),
               Finset.mem_insert_of_mem (Finset.mem_union_right _ r.2)⟩
    · rw [Finset.mem_singleton] at hmem
      exfalso
      apply h
      exact ⟨by omega, by omega⟩

private theorem reachFrom_has_parent (d : Nat) (gs : List BGate) (hRB : BReadsBack d gs) :
    ∀ w u, u ∈ reachFrom d gs hRB w →
      u = w ∨ ∃ (k : Nat) (hk : k < gs.length), d + k ∈ reachFrom d gs hRB w ∧
        (gs[k].lhs = u ∨ gs[k].rhs = u) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro u hu
    unfold reachFrom at hu ⊢
    split_ifs at hu ⊢ with h
    · rw [Finset.mem_insert, Finset.mem_union] at hu
      have hl : gs[w - d].lhs < w := by have := (hRB (w - d) h.2).1; omega
      have hr : gs[w - d].rhs < w := by have := (hRB (w - d) h.2).2; omega
      rcases hu with rfl | h1 | h2
      · exact Or.inl rfl
      · rcases ih gs[w - d].lhs hl u h1 with rfl | ⟨k, hk, hkm, hside⟩
        · exact Or.inr ⟨w - d, h.2, by rw [Nat.add_sub_of_le h.1]; exact Finset.mem_insert_self _ _, Or.inl rfl⟩
        · exact Or.inr ⟨k, hk, Finset.mem_insert_of_mem (Finset.mem_union_left _ hkm), hside⟩
      · rcases ih gs[w - d].rhs hr u h2 with rfl | ⟨k, hk, hkm, hside⟩
        · exact Or.inr ⟨w - d, h.2, by rw [Nat.add_sub_of_le h.1]; exact Finset.mem_insert_self _ _, Or.inr rfl⟩
        · exact Or.inr ⟨k, hk, Finset.mem_insert_of_mem (Finset.mem_union_right _ hkm), hside⟩
    · rw [Finset.mem_singleton] at hu
      exact Or.inl hu

private theorem reachFrom_mono {d m : Nat} (X : Fin m → Fin d → Bool) (gs : List BGate)
    (hRB : BReadsBack d gs) (i : Fin d) (h l : Fin m)
    (hX : ∀ j : Fin d, j ≠ i → (X h j = true → X l j = true)) :
    ∀ w < d + gs.length, i.val ∉ reachFrom d gs hRB w →
      (valB X gs w h = true → valB X gs w l = true) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hnot hv
    by_cases hwd : w < d
    · have hne : (⟨w, hwd⟩ : Fin d) ≠ i := by
        intro heq
        apply hnot
        rw [← congrArg Fin.val heq]
        exact reachFrom_self d gs hRB w
      rw [valB_var X gs ⟨w, hwd⟩ h] at hv
      rw [valB_var X gs ⟨w, hwd⟩ l]
      exact hX ⟨w, hwd⟩ hne hv
    · have hk : w - d < gs.length := by omega
      have hweq : w = d + (w - d) := by omega
      have hl : gs[w - d].lhs < w := by have := (hRB (w - d) hk).1; omega
      have hr : gs[w - d].rhs < w := by have := (hRB (w - d) hk).2; omega
      have hnotL : i.val ∉ reachFrom d gs hRB gs[w - d].lhs := by
        intro hm; apply hnot
        unfold reachFrom
        have hcond : d ≤ w ∧ w - d < gs.length := ⟨by omega, hk⟩
        simp only [hcond, and_self, dite_true]
        exact Finset.mem_insert_of_mem (Finset.mem_union_left _ hm)
      have hnotR : i.val ∉ reachFrom d gs hRB gs[w - d].rhs := by
        intro hm; apply hnot
        unfold reachFrom
        have hcond : d ≤ w ∧ w - d < gs.length := ⟨by omega, hk⟩
        simp only [hcond, and_self, dite_true]
        exact Finset.mem_insert_of_mem (Finset.mem_union_right _ hm)
      rw [hweq, valB_gate X gs hRB hk h] at hv
      rw [hweq, valB_gate X gs hRB hk l]
      have ihL := ih gs[w - d].lhs hl (by omega) hnotL
      have ihR := ih gs[w - d].rhs hr (by omega) hnotR
      cases hop : gs[w - d].op with
      | and =>
        rw [hop] at hv
        simp only [BOp.eval, Bool.and_eq_true] at hv ⊢
        exact ⟨ihL hv.1, ihR hv.2⟩
      | or =>
        rw [hop] at hv
        simp only [BOp.eval, Bool.or_eq_true] at hv ⊢
        rcases hv with h1 | h2
        · exact Or.inl (ihL h1)
        · exact Or.inr (ihR h2)

-- Sorted list of elements < N satisfying P
private def sortedFilter (P : Nat → Bool) : Nat → List Nat
  | 0 => []
  | n + 1 => sortedFilter P n ++ (if P n then [n] else [])

private theorem mem_sortedFilter (P : Nat → Bool) :
    ∀ N x, x ∈ sortedFilter P N ↔ x < N ∧ P x = true := by
  intro N
  induction N with
  | zero => intro x; simp [sortedFilter]
  | succ n ih =>
    intro x
    simp only [sortedFilter, List.mem_append, ih]
    split_ifs with hP
    · simp only [List.mem_singleton]
      constructor
      · rintro (⟨hlt, hx⟩ | rfl)
        · exact ⟨by omega, hx⟩
        · exact ⟨by omega, hP⟩
      · rintro ⟨hlt, hx⟩
        by_cases hxn : x < n
        · exact Or.inl ⟨hxn, hx⟩
        · exact Or.inr (by omega)
    · simp only [List.not_mem_nil, or_false]
      constructor
      · rintro ⟨hlt, hx⟩; exact ⟨by omega, hx⟩
      · rintro ⟨hlt, hx⟩
        have hne : x ≠ n := by intro heq; subst heq; simp [hx] at hP
        exact ⟨by omega, hx⟩

private theorem length_sortedFilter (P : Nat → Bool) :
    ∀ N, (sortedFilter P N).length = ((Finset.range N).filter (fun x => P x = true)).card := by
  intro N
  induction N with
  | zero => simp [sortedFilter]
  | succ n ih =>
    simp only [sortedFilter, List.length_append, ih, Finset.range_add_one, Finset.filter_insert]
    have hnot : n ∉ (Finset.range n).filter (fun x => P x = true) := by simp
    split_ifs with hP
    · rw [Finset.card_insert_of_notMem hnot, List.length_singleton]
    · simp

private theorem sortedFilter_strictMono (P : Nat → Bool) :
    ∀ N i j (hi : i < (sortedFilter P N).length) (hj : j < (sortedFilter P N).length),
      i < j → (sortedFilter P N)[i] < (sortedFilter P N)[j] := by
  intro N
  induction N with
  | zero => intro i j hi; simp [sortedFilter] at hi
  | succ n ih =>
    intro i j hi hj hij
    simp only [sortedFilter] at hi hj ⊢
    split_ifs at hi hj ⊢ with hP
    · rw [List.length_append, List.length_singleton] at hi hj
      by_cases hlt : j < (sortedFilter P n).length
      · have hlti : i < (sortedFilter P n).length := by omega
        rw [List.getElem_append_left hlti, List.getElem_append_left hlt]
        exact ih i j hlti hlt hij
      · have hjEq : j = (sortedFilter P n).length := by omega
        have hlti : i < (sortedFilter P n).length := by omega
        rw [List.getElem_append_left hlti]
        have hgetJ : (sortedFilter P n ++ [n])[j]'(by rw [List.length_append, List.length_singleton]; exact hj) = n := by
          subst hjEq; simp
        rw [hgetJ]
        have hmem : (sortedFilter P n)[i] ∈ sortedFilter P n := List.getElem_mem hlti
        exact ((mem_sortedFilter P n _).mp hmem).1
    · simp only [List.append_nil] at hi hj ⊢
      exact ih i j hi hj hij

private def subTree (d : Nat) (gs : List BGate) (hRB : BReadsBack d gs)
    (isShared : Nat → Bool) (u : Nat) : BTree Nat :=
  if h : d ≤ u ∧ u - d < gs.length ∧ isShared u = false then
    match (gs[u - d]'(h.2.1)).op with
    | .and => BTree.and (subTree d gs hRB isShared (gs[u - d]'(h.2.1)).lhs) (subTree d gs hRB isShared (gs[u - d]'(h.2.1)).rhs)
    | .or  => BTree.or  (subTree d gs hRB isShared (gs[u - d]'(h.2.1)).lhs) (subTree d gs hRB isShared (gs[u - d]'(h.2.1)).rhs)
  else
    BTree.leaf u
termination_by u
decreasing_by
  · exact Nat.lt_of_lt_of_eq (hRB (u - d) h.2.1).1 (Nat.add_sub_of_le h.1)
  · exact Nat.lt_of_lt_of_eq (hRB (u - d) h.2.1).2 (Nat.add_sub_of_le h.1)
  · exact Nat.lt_of_lt_of_eq (hRB (u - d) h.2.1).1 (Nat.add_sub_of_le h.1)
  · exact Nat.lt_of_lt_of_eq (hRB (u - d) h.2.1).2 (Nat.add_sub_of_le h.1)

private def stageTree (d : Nat) (gs : List BGate) (hRB : BReadsBack d gs)
    (isShared : Nat → Bool) (w : Nat) : BTree Nat :=
  if h : d ≤ w ∧ w - d < gs.length then
    match (gs[w - d]'(h.2)).op with
    | .and => BTree.and (subTree d gs hRB isShared (gs[w - d]'(h.2)).lhs) (subTree d gs hRB isShared (gs[w - d]'(h.2)).rhs)
    | .or  => BTree.or  (subTree d gs hRB isShared (gs[w - d]'(h.2)).lhs) (subTree d gs hRB isShared (gs[w - d]'(h.2)).rhs)
  else
    BTree.leaf w

private def subOcc (d : Nat) (gs : List BGate) (hRB : BReadsBack d gs)
    (isShared : Nat → Bool) (k u : Nat) : Nat :=
  if h : d ≤ u ∧ u - d < gs.length ∧ isShared u = false then
    (if u - d = k then 1 else 0) + subOcc d gs hRB isShared k (gs[u - d]'(h.2.1)).lhs + subOcc d gs hRB isShared k (gs[u - d]'(h.2.1)).rhs
  else
    0
termination_by u
decreasing_by
  · exact Nat.lt_of_lt_of_eq (hRB (u - d) h.2.1).1 (Nat.add_sub_of_le h.1)
  · exact Nat.lt_of_lt_of_eq (hRB (u - d) h.2.1).2 (Nat.add_sub_of_le h.1)

private def stageOcc (d : Nat) (gs : List BGate) (hRB : BReadsBack d gs)
    (isShared : Nat → Bool) (k w : Nat) : Nat :=
  if h : d ≤ w ∧ w - d < gs.length then
    (if w - d = k then 1 else 0) + subOcc d gs hRB isShared k (gs[w - d]'(h.2)).lhs + subOcc d gs hRB isShared k (gs[w - d]'(h.2)).rhs
  else
    0

private theorem subTree_eval {d m : Nat} (X : Fin m → Fin d → Bool) (gs : List BGate)
    (hRB : BReadsBack d gs) (isShared : Nat → Bool) (t : Fin m) :
    ∀ u, (subTree d gs hRB isShared u).eval (fun a => valB X gs a t) = valB X gs u t := by
  intro u
  induction u using Nat.strong_induction_on with
  | ind u ih =>
    unfold subTree
    split_ifs with h
    · have hl : gs[u - d].lhs < u := by have := (hRB (u - d) h.2.1).1; omega
      have hr : gs[u - d].rhs < u := by have := (hRB (u - d) h.2.1).2; omega
      have hueq : u = d + (u - d) := by omega
      have hv := valB_gate X gs hRB h.2.1 t
      rw [← hueq] at hv
      rw [hv]
      cases hop : gs[u - d].op with
      | and => simp [BTree.eval, BOp.eval, ih _ hl, ih _ hr]
      | or  => simp [BTree.eval, BOp.eval, ih _ hl, ih _ hr]
    · rfl

private theorem stageTree_eval {d m : Nat} (X : Fin m → Fin d → Bool) (gs : List BGate)
    (hRB : BReadsBack d gs) (isShared : Nat → Bool) (w : Nat) (t : Fin m) :
    (stageTree d gs hRB isShared w).eval (fun a => valB X gs a t) = valB X gs w t := by
  unfold stageTree
  split_ifs with h
  · have hweq : w = d + (w - d) := by omega
    have hv := valB_gate X gs hRB h.2 t
    rw [← hweq] at hv
    rw [hv]
    cases hop : gs[w - d].op with
    | and => simp [BTree.eval, BOp.eval, subTree_eval]
    | or  => simp [BTree.eval, BOp.eval, subTree_eval]
  · rfl

private def BTree.AllLeaves {α : Type} (P : α → Prop) : BTree α → Prop
  | .leaf a => P a
  | .and l r => l.AllLeaves P ∧ r.AllLeaves P
  | .or l r => l.AllLeaves P ∧ r.AllLeaves P

private theorem BTree.allLeaves_leafAt {α : Type} {P : α → Prop} (τ : BTree α)
    (h : τ.AllLeaves P) : ∀ a : Fin τ.leaves, P (τ.leafAt a) := by
  induction τ with
  | leaf x => intro a; exact h
  | and L R ihL ihR =>
    intro a
    unfold BTree.leafAt
    split_ifs with hlt
    · exact ihL h.1 ⟨a.val, hlt⟩
    · exact ihR h.2 ⟨a.val - L.leaves, by have := a.isLt; simp [BTree.leaves] at this; omega⟩
  | or L R ihL ihR =>
    intro a
    unfold BTree.leafAt
    split_ifs with hlt
    · exact ihL h.1 ⟨a.val, hlt⟩
    · exact ihR h.2 ⟨a.val - L.leaves, by have := a.isLt; simp [BTree.leaves] at this; omega⟩

private theorem BTree.allLeaves_mono {α : Type} {P Q : α → Prop} (τ : BTree α)
    (hpq : ∀ x, P x → Q x) (h : τ.AllLeaves P) : τ.AllLeaves Q := by
  induction τ with
  | leaf x => exact hpq x h
  | and L R ihL ihR => exact ⟨ihL h.1, ihR h.2⟩
  | or L R ihL ihR => exact ⟨ihL h.1, ihR h.2⟩

private theorem subTree_allLeaves (d : Nat) (gs : List BGate) (hRB : BReadsBack d gs)
    (isShared : Nat → Bool) :
    ∀ u, u < d + gs.length →
      (subTree d gs hRB isShared u).AllLeaves (fun v => v ≤ u ∧ (v < d ∨ isShared v = true)) := by
  intro u
  induction u using Nat.strong_induction_on with
  | ind u ih =>
    intro hu
    unfold subTree
    split_ifs with h
    · have hl : gs[u - d].lhs < u := by have := h.1; have := (hRB (u - d) h.2.1).1; omega
      have hr : gs[u - d].rhs < u := by have := h.1; have := (hRB (u - d) h.2.1).2; omega
      have hL : (subTree d gs hRB isShared gs[u - d].lhs).AllLeaves (fun v => v ≤ u ∧ (v < d ∨ isShared v = true)) :=
        BTree.allLeaves_mono _ (fun v hv => ⟨by omega, hv.2⟩) (ih gs[u - d].lhs hl (by omega))
      have hR : (subTree d gs hRB isShared gs[u - d].rhs).AllLeaves (fun v => v ≤ u ∧ (v < d ∨ isShared v = true)) :=
        BTree.allLeaves_mono _ (fun v hv => ⟨by omega, hv.2⟩) (ih gs[u - d].rhs hr (by omega))
      cases gs[u - d].op <;> exact ⟨hL, hR⟩
    · refine ⟨Nat.le_refl _, ?_⟩
      by_cases hud : u < d
      · exact Or.inl hud
      · right
        have hlt : u - d < gs.length := by omega
        cases hs : isShared u with
        | true => rfl
        | false => exact False.elim (h ⟨by omega, hlt, hs⟩)

private theorem stageTree_leaf_props (d : Nat) (gs : List BGate) (hRB : BReadsBack d gs)
    (isShared : Nat → Bool) (w : Nat) (hw : w < d + gs.length)
    (a : Fin (stageTree d gs hRB isShared w).leaves) :
    (stageTree d gs hRB isShared w).leafAt a < d ∨
    ((stageTree d gs hRB isShared w).leafAt a < w ∧ isShared ((stageTree d gs hRB isShared w).leafAt a) = true) := by
  apply BTree.allLeaves_leafAt (P := fun v => v < d ∨ (v < w ∧ isShared v = true))
  unfold stageTree
  split_ifs with h
  · have hl : gs[w - d].lhs < w := by have := h.1; have := (hRB (w - d) h.2).1; omega
    have hr : gs[w - d].rhs < w := by have := h.1; have := (hRB (w - d) h.2).2; omega
    have hL : (subTree d gs hRB isShared gs[w - d].lhs).AllLeaves (fun v => v < d ∨ (v < w ∧ isShared v = true)) :=
      BTree.allLeaves_mono _
        (fun v hv => by rcases hv.2 with h1 | h2; exact Or.inl h1; exact Or.inr ⟨by omega, h2⟩)
        (subTree_allLeaves d gs hRB isShared gs[w - d].lhs (by omega))
    have hR : (subTree d gs hRB isShared gs[w - d].rhs).AllLeaves (fun v => v < d ∨ (v < w ∧ isShared v = true)) :=
      BTree.allLeaves_mono _
        (fun v hv => by rcases hv.2 with h1 | h2; exact Or.inl h1; exact Or.inr ⟨by omega, h2⟩)
        (subTree_allLeaves d gs hRB isShared gs[w - d].rhs (by omega))
    cases gs[w - d].op <;> exact ⟨hL, hR⟩
  · left
    omega

private theorem subTree_gates_eq_sum_subOcc (d : Nat) (gs : List BGate) (hRB : BReadsBack d gs)
    (isShared : Nat → Bool) (G : Finset Nat) (out : Nat)
    (hGdef : ∀ k, k ∈ G ↔ k < gs.length ∧ d + k ∈ reachFrom d gs hRB out) :
    ∀ u, u ∈ reachFrom d gs hRB out →
      (subTree d gs hRB isShared u).gates = ∑ k ∈ G, subOcc d gs hRB isShared k u := by
  intro u
  induction u using Nat.strong_induction_on with
  | ind u ih =>
    intro hu
    unfold subTree
    split_ifs with h
    · have hl : gs[u - d].lhs < u := by have := (hRB (u - d) h.2.1).1; omega
      have hr : gs[u - d].rhs < u := by have := (hRB (u - d) h.2.1).2; omega
      have hud : d + (u - d) = u := by omega
      have hGmem : u - d ∈ G := (hGdef (u - d)).mpr ⟨h.2.1, by rw [hud]; exact hu⟩
      have hcl := reachFrom_closed d gs hRB out (u - d) h.2.1 (by rw [hud]; exact hu)
      have ihL := ih _ hl hcl.1
      have ihR := ih _ hr hcl.2
      have hsum : ∑ k ∈ G, subOcc d gs hRB isShared k u =
          1 + (∑ k ∈ G, subOcc d gs hRB isShared k gs[u - d].lhs) +
              (∑ k ∈ G, subOcc d gs hRB isShared k gs[u - d].rhs) := by
        have hstep : ∀ k ∈ G, subOcc d gs hRB isShared k u =
            (if u - d = k then 1 else 0) + subOcc d gs hRB isShared k gs[u - d].lhs +
            subOcc d gs hRB isShared k gs[u - d].rhs := by
          intro k _
          conv_lhs => unfold subOcc
          simp [h]
        rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, Finset.sum_add_distrib]
        simp [Finset.sum_ite_eq, hGmem]
      rw [hsum, ← ihL, ← ihR]
      cases gs[u - d].op <;> rfl
    · simp only [BTree.gates]
      symm
      apply Finset.sum_eq_zero
      intro k _
      unfold subOcc
      simp [h]

private theorem stageTree_gates_eq_sum_stageOcc (d : Nat) (gs : List BGate) (hRB : BReadsBack d gs)
    (isShared : Nat → Bool) (G : Finset Nat) (out : Nat)
    (hGdef : ∀ k, k ∈ G ↔ k < gs.length ∧ d + k ∈ reachFrom d gs hRB out)
    (w : Nat) (hw : w ∈ reachFrom d gs hRB out) :
    (stageTree d gs hRB isShared w).gates = ∑ k ∈ G, stageOcc d gs hRB isShared k w := by
  unfold stageTree
  split_ifs with h
  · have hwd : d + (w - d) = w := by omega
    have hGmem : w - d ∈ G := (hGdef (w - d)).mpr ⟨h.2, by rw [hwd]; exact hw⟩
    have hcl := reachFrom_closed d gs hRB out (w - d) h.2 (by rw [hwd]; exact hw)
    have hL := subTree_gates_eq_sum_subOcc d gs hRB isShared G out hGdef _ hcl.1
    have hR := subTree_gates_eq_sum_subOcc d gs hRB isShared G out hGdef _ hcl.2
    have hsum : ∑ k ∈ G, stageOcc d gs hRB isShared k w =
        1 + (∑ k ∈ G, subOcc d gs hRB isShared k gs[w - d].lhs) +
            (∑ k ∈ G, subOcc d gs hRB isShared k gs[w - d].rhs) := by
      have hstep : ∀ k ∈ G, stageOcc d gs hRB isShared k w =
          (if w - d = k then 1 else 0) + subOcc d gs hRB isShared k gs[w - d].lhs +
          subOcc d gs hRB isShared k gs[w - d].rhs := by
        intro k _
        unfold stageOcc
        simp [h]
      rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, Finset.sum_add_distrib]
      simp [Finset.sum_ite_eq, hGmem]
    rw [hsum, ← hL, ← hR]
    cases gs[w - d].op <;> rfl
  · simp only [BTree.gates]
    symm
    apply Finset.sum_eq_zero
    intro k _
    unfold stageOcc
    simp [h]

private theorem subOcc_eq_zero_of_lt (d : Nat) (gs : List BGate) (hRB : BReadsBack d gs)
    (isShared : Nat → Bool) (k : Nat) :
    ∀ u < d + k, subOcc d gs hRB isShared k u = 0 := by
  intro u
  induction u using Nat.strong_induction_on with
  | ind u ih =>
    intro hu
    unfold subOcc
    by_cases h : d ≤ u ∧ u - d < gs.length ∧ isShared u = false
    · rw [dite_eq_left_of_eq_true (eq_true h)]
      have hl : gs[u - d].lhs < u := by have := (hRB (u - d) h.2.1).1; omega
      have hr : gs[u - d].rhs < u := by have := (hRB (u - d) h.2.1).2; omega
      have hne : u - d ≠ k := by omega
      simp [hne, ih _ hl (by omega), ih _ hr (by omega)]
    · simp [h]

private theorem subOcc_eq_zero_of_shared (d : Nat) (gs : List BGate) (hRB : BReadsBack d gs)
    (isShared : Nat → Bool) (k : Nat) (hsh : isShared (d + k) = true) :
    ∀ u, subOcc d gs hRB isShared k u = 0 := by
  intro u
  induction u using Nat.strong_induction_on with
  | ind u ih =>
    unfold subOcc
    by_cases h : d ≤ u ∧ u - d < gs.length ∧ isShared u = false
    · rw [dite_eq_left_of_eq_true (eq_true h)]
      have hl : gs[u - d].lhs < u := by have := (hRB (u - d) h.2.1).1; omega
      have hr : gs[u - d].rhs < u := by have := (hRB (u - d) h.2.1).2; omega
      have hne : u - d ≠ k := by
        intro heq
        have huEq : u = d + k := by omega
        rw [huEq, hsh] at h
        cases h.2.2
      simp [hne, ih _ hl, ih _ hr]
    · simp [h]

private def hitGate (gs : List BGate) (w k' : Nat) : Nat :=
  if hk : k' < gs.length then
    (if gs[k'].lhs = w then 1 else 0) + (if gs[k'].rhs = w then 1 else 0)
  else
    0

private theorem subOcc_balance (d : Nat) (gs : List BGate) (hRB : BReadsBack d gs)
    (isShared : Nat → Bool) (G : Finset Nat) (out : Nat)
    (hGdef : ∀ k, k ∈ G ↔ k < gs.length ∧ d + k ∈ reachFrom d gs hRB out)
    (k : Nat) (hkG : k ∈ G) (hnotSh : isShared (d + k) = false) :
    ∀ u ∈ reachFrom d gs hRB out,
      subOcc d gs hRB isShared k u =
        (if u = d + k then 1 else 0) + ∑ k' ∈ G, subOcc d gs hRB isShared k' u * hitGate gs (d + k) k' := by
  intro u
  induction u using Nat.strong_induction_on with
  | ind u ih =>
    intro hu
    have hklt : k < gs.length := ((hGdef k).mp hkG).1
    by_cases h : d ≤ u ∧ u - d < gs.length ∧ isShared u = false
    · have hl : gs[u - d].lhs < u := by have := (hRB (u - d) h.2.1).1; omega
      have hr : gs[u - d].rhs < u := by have := (hRB (u - d) h.2.1).2; omega
      have hud : d + (u - d) = u := by omega
      have huG : u - d ∈ G := (hGdef (u - d)).mpr ⟨h.2.1, by rw [hud]; exact hu⟩
      have hcl := reachFrom_closed d gs hRB out (u - d) h.2.1 (by rw [hud]; exact hu)
      have ihL := ih _ hl hcl.1
      have ihR := ih _ hr hcl.2
      have hLHS : subOcc d gs hRB isShared k u =
          (if u - d = k then 1 else 0) + subOcc d gs hRB isShared k gs[u - d].lhs +
          subOcc d gs hRB isShared k gs[u - d].rhs := by
        conv_lhs => unfold subOcc
        simp [h]
      have hRHSstep : ∀ k' ∈ G, subOcc d gs hRB isShared k' u * hitGate gs (d + k) k' =
          (if u - d = k' then 1 else 0) * hitGate gs (d + k) k' +
          subOcc d gs hRB isShared k' gs[u - d].lhs * hitGate gs (d + k) k' +
          subOcc d gs hRB isShared k' gs[u - d].rhs * hitGate gs (d + k) k' := by
        intro k' _
        have hx : subOcc d gs hRB isShared k' u =
            (if u - d = k' then 1 else 0) + subOcc d gs hRB isShared k' gs[u - d].lhs +
            subOcc d gs hRB isShared k' gs[u - d].rhs := by
          conv_lhs => unfold subOcc
          simp [h]
        rw [hx]
        simp only [Nat.add_mul]
      rw [Finset.sum_congr rfl hRHSstep, Finset.sum_add_distrib, Finset.sum_add_distrib]
      have hhit : ∑ k' ∈ G, (if u - d = k' then 1 else 0) * hitGate gs (d + k) k' =
          hitGate gs (d + k) (u - d) := by
        have hstep : ∀ k' ∈ G, (if u - d = k' then 1 else 0) * hitGate gs (d + k) k' =
            if u - d = k' then hitGate gs (d + k) k' else 0 := by
          intro k' _; split_ifs <;> simp
        rw [Finset.sum_congr rfl hstep, Finset.sum_ite_eq]
        simp [huG]
      rw [hhit, hLHS, ihL, ihR]
      have hhitDef : hitGate gs (d + k) (u - d) =
          (if gs[u - d].lhs = d + k then 1 else 0) + (if gs[u - d].rhs = d + k then 1 else 0) := by
        simp [hitGate, h.2.1]
      rw [hhitDef]
      have hcondEq : (u - d = k) ↔ (u = d + k) := by omega
      simp only [hcondEq]
      omega
    · have hne : u ≠ d + k := by
        intro heq
        apply h
        subst heq
        exact ⟨by omega, by simp [hklt], hnotSh⟩
      have hL0 : subOcc d gs hRB isShared k u = 0 := by unfold subOcc; simp [h]
      have hR0 : ∑ k' ∈ G, subOcc d gs hRB isShared k' u * hitGate gs (d + k) k' = 0 := by
        apply Finset.sum_eq_zero
        intro k' _
        have : subOcc d gs hRB isShared k' u = 0 := by unfold subOcc; simp [h]
        simp [this]
      simp [hL0, hR0, hne]

private theorem stageOcc_balance (d : Nat) (gs : List BGate) (hRB : BReadsBack d gs)
    (isShared : Nat → Bool) (G : Finset Nat) (out : Nat)
    (hGdef : ∀ k, k ∈ G ↔ k < gs.length ∧ d + k ∈ reachFrom d gs hRB out)
    (k : Nat) (hkG : k ∈ G) (hnotSh : isShared (d + k) = false)
    (w : Nat) (hw : w ∈ reachFrom d gs hRB out) (hwne : w ≠ d + k) :
    stageOcc d gs hRB isShared k w =
      ∑ k' ∈ G, stageOcc d gs hRB isShared k' w * hitGate gs (d + k) k' := by
  by_cases h : d ≤ w ∧ w - d < gs.length
  · have hwd : d + (w - d) = w := by omega
    have hwG : w - d ∈ G := (hGdef (w - d)).mpr ⟨h.2, by rw [hwd]; exact hw⟩
    have hcl := reachFrom_closed d gs hRB out (w - d) h.2 (by rw [hwd]; exact hw)
    have hL := subOcc_balance d gs hRB isShared G out hGdef k hkG hnotSh _ hcl.1
    have hR := subOcc_balance d gs hRB isShared G out hGdef k hkG hnotSh _ hcl.2
    have hLHS : stageOcc d gs hRB isShared k w =
        subOcc d gs hRB isShared k gs[w - d].lhs + subOcc d gs hRB isShared k gs[w - d].rhs := by
      unfold stageOcc
      have hne' : w - d ≠ k := by omega
      simp [h, hne']
    have hRHSstep : ∀ k' ∈ G, stageOcc d gs hRB isShared k' w * hitGate gs (d + k) k' =
        (if w - d = k' then 1 else 0) * hitGate gs (d + k) k' +
        subOcc d gs hRB isShared k' gs[w - d].lhs * hitGate gs (d + k) k' +
        subOcc d gs hRB isShared k' gs[w - d].rhs * hitGate gs (d + k) k' := by
      intro k' _
      have hx : stageOcc d gs hRB isShared k' w =
          (if w - d = k' then 1 else 0) + subOcc d gs hRB isShared k' gs[w - d].lhs +
          subOcc d gs hRB isShared k' gs[w - d].rhs := by
        unfold stageOcc; simp [h]
      rw [hx]
      simp only [Nat.add_mul]
    rw [Finset.sum_congr rfl hRHSstep, Finset.sum_add_distrib, Finset.sum_add_distrib]
    have hhit : ∑ k' ∈ G, (if w - d = k' then 1 else 0) * hitGate gs (d + k) k' =
        hitGate gs (d + k) (w - d) := by
      have hstep : ∀ k' ∈ G, (if w - d = k' then 1 else 0) * hitGate gs (d + k) k' =
          if w - d = k' then hitGate gs (d + k) k' else 0 := by
        intro k' _; split_ifs <;> simp
      rw [Finset.sum_congr rfl hstep, Finset.sum_ite_eq]
      simp [hwG]
    rw [hhit, hLHS, hL, hR]
    have hhitDef : hitGate gs (d + k) (w - d) =
        (if gs[w - d].lhs = d + k then 1 else 0) + (if gs[w - d].rhs = d + k then 1 else 0) := by
      simp [hitGate, h.2]
    rw [hhitDef]
    omega
  · have hL0 : stageOcc d gs hRB isShared k w = 0 := by unfold stageOcc; simp [h]
    have hR0 : ∑ k' ∈ G, stageOcc d gs hRB isShared k' w * hitGate gs (d + k) k' = 0 := by
      apply Finset.sum_eq_zero
      intro k' _
      have : stageOcc d gs hRB isShared k' w = 0 := by unfold stageOcc; simp [h]
      simp [this]
    rw [hL0, hR0]

private theorem forward_dir (d m e : Nat) (X : Fin m → Fin d → Bool) (T : Fin m → Bool)
    (hd : 0 < d)
    (hsep : ∀ i : Fin d, ∃ h l, T h = true ∧ T l = false ∧
      ∀ j, (X h j = true ∧ X l j = false) ↔ j = i)
    (C : Circuit) (hF : FanInTwo C) (hRB : ReadsBack (d + 2) C)
    (hN : notCount C = 0) (hout : C.output < d + 2 + C.size) (hsz : C.size ≤ d - 1 + e)
    (heval : ∀ t, C.eval (mkInput (X t)) = T t) :
    ∃ (c : Nat) (Z : Nat → Fin m → Bool) (r : Fin (c + 1) → Nat)
      (src : (j : Fin (c + 1)) → Fin (r j) → Nat)
      (pick : (j : Fin (c + 1)) → Fin m → Fin m → Fin (r j)),
      c ≤ e ∧ (Finset.univ.sum r) ≤ d + e + c ∧
      (∀ i : Fin d, Z i.val = fun t => X t i) ∧ Z (d + c) = T ∧
      ∀ j : Fin (c + 1), 0 < r j ∧ (∀ a, src j a < d + j.val) ∧
        (∃ h, Z (d + j.val) h = true) ∧ (∃ l, Z (d + j.val) l = false) ∧
        (∀ h l, (Z (d + j.val) h = true ∧ Z (d + j.val) l = false) →
          Z (src j (pick j h l)) h = true ∧ Z (src j (pick j h l)) l = false) ∧
        ∀ S : Finset (Fin (r j)), 2 ≤ S.card →
          splitOf S (fun a b => ∃ h l t,
            (Z (d + j.val) h = true ∧ Z (d + j.val) l = false) ∧
            (Z (d + j.val) h = true ∧ Z (d + j.val) t = false) ∧
            pick j h l = a ∧ pick j h t = b) ∨
          splitOf S (fun a b => ∃ h l t,
            (Z (d + j.val) h = true ∧ Z (d + j.val) l = false) ∧
            (Z (d + j.val) t = true ∧ Z (d + j.val) l = false) ∧
            pick j h l = a ∧ pick j t l = b) := by
  obtain ⟨gs, out, hgsLen, hBRB, hNC, houtLt, houtEval⟩ :=
    simplify_circuit X T hd hsep C hF hRB hN hout heval
  have hgsBound : gs.length ≤ d - 1 + e := le_trans hgsLen hsz
  let R : Finset Nat := reachFrom d gs hBRB out
  let G : Finset Nat := (Finset.range gs.length).filter (fun k => d + k ∈ R)
  have hGdef : ∀ k, k ∈ G ↔ k < gs.length ∧ d + k ∈ R := by
    intro k; simp [G]
  have hRlt : ∀ w ∈ R, w < d + gs.length := by
    intro w hw
    have := reachFrom_le d gs hBRB out w hw
    omega
  -- Every raw variable 0..d-1 is in R
  have hVarsInR : ∀ i : Fin d, i.val ∈ R := by
    intro i
    by_contra hnot
    rcases hsep i with ⟨h, l, hTh, hTl, hiff⟩
    have hX : ∀ j : Fin d, j ≠ i → (X h j = true → X l j = true) := by
      intro j hj hxh
      cases hxl : X l j with
      | true => rfl
      | false =>
        have := (hiff j).mp ⟨hxh, hxl⟩
        exact False.elim (hj this)
    have hmono := reachFrom_mono X gs hBRB i h l hX out houtLt hnot
    rw [houtEval h, houtEval l, hTh, hTl] at hmono
    have := hmono rfl
    cases this
  -- R = range d ∪ G.image (d + ·), disjoint
  have hReq : R = Finset.range d ∪ G.image (fun k => d + k) := by
    ext w
    simp only [Finset.mem_union, Finset.mem_range, Finset.mem_image, hGdef]
    constructor
    · intro hw
      by_cases hwd : w < d
      · exact Or.inl hwd
      · right
        have hwlt := hRlt w hw
        exact ⟨w - d, ⟨by omega, by rw [Nat.add_sub_of_le (by omega)]; exact hw⟩, by omega⟩
    · rintro (hwd | ⟨k, ⟨_, hkR⟩, rfl⟩)
      · exact hVarsInR ⟨w, hwd⟩
      · exact hkR
  have hDisj : Disjoint (Finset.range d) (G.image (fun k => d + k)) := by
    rw [Finset.disjoint_left]
    intro w hw1 hw2
    rw [Finset.mem_range] at hw1
    rcases Finset.mem_image.mp hw2 with ⟨k, _, rfl⟩
    omega
  have hRcard : R.card = d + G.card := by
    rw [hReq, Finset.card_union_of_disjoint hDisj, Finset.card_range,
        Finset.card_image_of_injective _ (fun a b h => by omega)]
  have hGcard_le : G.card ≤ d - 1 + e := by
    calc G.card ≤ (Finset.range gs.length).card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = gs.length := Finset.card_range _
      _ ≤ d - 1 + e := hgsBound
  -- Use counts
  let uses : Nat → Nat := fun w =>
    (if w = out then 1 else 0) + ∑ k ∈ G, hitGate gs w k
  have hOutInR : out ∈ R := reachFrom_self d gs hBRB out
  have hSumUses : ∑ w ∈ R, uses w = 1 + 2 * G.card := by
    simp only [uses, Finset.sum_add_distrib]
    have h1 : ∑ w ∈ R, (if w = out then 1 else 0) = 1 := by
      simp [Finset.sum_ite_eq', hOutInR]
    have h2 : ∑ w ∈ R, ∑ k ∈ G, hitGate gs w k = 2 * G.card := by
      rw [Finset.sum_comm]
      have heach : ∀ k ∈ G, ∑ w ∈ R, hitGate gs w k = 2 := by
        intro k hkG
        have ⟨hklt, hkR⟩ := (hGdef k).mp hkG
        have hcl := reachFrom_closed d gs hBRB out k hklt hkR
        have hstep : ∀ w ∈ R, hitGate gs w k =
            (if gs[k].lhs = w then 1 else 0) + (if gs[k].rhs = w then 1 else 0) := by
          intro w _; simp [hitGate, hklt]
        rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib]
        rw [Finset.sum_ite_eq, Finset.sum_ite_eq]
        have hcl1 : gs[k].lhs ∈ R := hcl.1
        have hcl2 : gs[k].rhs ∈ R := hcl.2
        simp [hcl1, hcl2]
      rw [Finset.sum_congr rfl heach]
      simp [Nat.mul_comm]
    rw [h1, h2]
  have hUsesPos : ∀ w ∈ R, 1 ≤ uses w := by
    intro w hw
    rcases reachFrom_has_parent d gs hBRB out w hw with rfl | ⟨k, hk, hkR, hside⟩
    · simp only [uses, ite_true]; omega
    · have hkG : k ∈ G := (hGdef k).mpr ⟨hk, hkR⟩
      have hhit : 1 ≤ hitGate gs w k := by
        simp only [hitGate, hk, dite_true]
        rcases hside with h1 | h1 <;> simp [h1]
      have hle : hitGate gs w k ≤ ∑ k' ∈ G, hitGate gs w k' :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) hkG
      simp only [uses]
      omega
  have hUsesOut : uses out = 1 := by
    have hsum0 : ∑ k ∈ G, hitGate gs out k = 0 := by
      apply Finset.sum_eq_zero
      intro k hkG
      have ⟨hklt, hkR⟩ := (hGdef k).mp hkG
      have hle : d + k ≤ out := reachFrom_le d gs hBRB out (d + k) hkR
      have h1 : gs[k].lhs < d + k := (hBRB k hklt).1
      have h2 : gs[k].rhs < d + k := (hBRB k hklt).2
      simp only [hitGate, hklt, dite_true]
      have hne1 : gs[k].lhs ≠ out := by omega
      have hne2 : gs[k].rhs ≠ out := by omega
      simp [hne1, hne2]
    simp [uses, hsum0]
  -- Shared internal gates
  let isSharedGate : Nat → Bool := fun k => decide (k ∈ G ∧ 2 ≤ uses (d + k))
  let Shared : Finset Nat := (Finset.range gs.length).filter (fun k => isSharedGate k = true)
  have hSharedMem : ∀ k, k ∈ Shared ↔ k ∈ G ∧ 2 ≤ uses (d + k) := by
    intro k
    simp only [Shared, isSharedGate, Finset.mem_filter, Finset.mem_range, decide_eq_true_eq]
    constructor
    · intro h; exact h.2
    · intro h; exact ⟨((hGdef k).mp h.1).1, h⟩
  let SharedWires : Finset Nat := Shared.image (fun k => d + k)
  have hSharedSubR : SharedWires ⊆ R := by
    intro w hw
    rcases Finset.mem_image.mp hw with ⟨k, hk, rfl⟩
    exact ((hGdef k).mp ((hSharedMem k).mp hk).1).2
  let c : Nat := Shared.card
  -- Prove c ≤ e from ∑ w ∈ R, uses w = 1 + 2 * G.card
  have hSharedCard : SharedWires.card = c :=
    Finset.card_image_of_injective _ (fun a b h => by omega)
  have hSumGe : R.card + SharedWires.card ≤ ∑ w ∈ R, uses w := by
    have h1 : ∑ w ∈ R, (1 + if w ∈ SharedWires then 1 else 0) ≤ ∑ w ∈ R, uses w := by
      apply Finset.sum_le_sum
      intro w hw
      split_ifs with hsh
      · rcases Finset.mem_image.mp hsh with ⟨k, hk, rfl⟩
        exact ((hSharedMem k).mp hk).2
      · have := hUsesPos w hw; omega
    rw [Finset.sum_add_distrib] at h1
    have h2 : ∑ w ∈ R, (if w ∈ SharedWires then 1 else 0) = SharedWires.card := by
      rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hSharedSubR]
      simp
    simp only [Finset.sum_const, smul_eq_mul, Nat.mul_one, h2] at h1
    exact h1
  have hcLeE : c ≤ e := by omega
  -- Stage wires: sorted shared wires followed by out
  let sList : List Nat := sortedFilter isSharedGate gs.length
  have hsListLen : sList.length = c := by
    simp only [sList, c, Shared]
    exact length_sortedFilter isSharedGate gs.length
  have hsListMem : ∀ k, k ∈ sList ↔ k ∈ Shared := by
    intro k
    simp only [sList, Shared, mem_sortedFilter, Finset.mem_filter, Finset.mem_range]
  let stageWire : Fin (c + 1) → Nat := fun j =>
    if h : j.val < c then d + sList[j.val]'(by omega) else out
  have hStageInR : ∀ j : Fin (c + 1), stageWire j ∈ R := by
    intro j
    simp only [stageWire]
    split_ifs with h
    · have hm : sList[j.val]'(by omega) ∈ Shared := (hsListMem _).mp (List.getElem_mem _)
      exact ((hGdef _).mp ((hSharedMem _).mp hm).1).2
    · exact hOutInR
  have hStageLtOut : ∀ j : Fin (c + 1), j.val < c → stageWire j < out := by
    intro j hj
    simp only [stageWire, hj, dite_true]
    have hm : sList[j.val]'(by omega) ∈ Shared := (hsListMem _).mp (List.getElem_mem _)
    have hprops := (hSharedMem _).mp hm
    have hle : d + sList[j.val]'(by omega) ≤ out :=
      reachFrom_le d gs hBRB out _ ((hGdef _).mp hprops.1).2
    have hne : d + sList[j.val]'(by omega) ≠ out := by
      intro heq
      have h2 := hprops.2
      rw [heq, hUsesOut] at h2
      omega
    omega
  have hStageStrict : ∀ j1 j2 : Fin (c + 1), j1.val < j2.val → stageWire j1 < stageWire j2 := by
    intro j1 j2 hlt
    by_cases h2 : j2.val < c
    · have h1 : j1.val < c := by omega
      simp only [stageWire, h1, h2, dite_true]
      have hsm : sList[j1.val]'(by omega) < sList[j2.val]'(by omega) :=
        sortedFilter_strictMono isSharedGate gs.length j1.val j2.val
          (by change j1.val < sList.length; omega) (by change j2.val < sList.length; omega) hlt
      omega
    · have hj2Eq : j2.val = c := by omega
      have h1 : j1.val < c := by omega
      have hsw2 : stageWire j2 = out := by simp [stageWire, h2]
      rw [hsw2]
      exact hStageLtOut j1 h1
  have hStageInj : Function.Injective stageWire := by
    intro j1 j2 heq
    ext
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h1 | h2
    · have := hStageStrict j1 j2 h1; omega
    · have := hStageStrict j2 j1 h2; omega
  -- Shared wire indicator
  let isSharedW : Nat → Bool := fun u => decide (u ∈ SharedWires)
  have hisSharedW : ∀ u, isSharedW u = true ↔ u ∈ SharedWires := by
    intro u; simp [isSharedW]
  -- Define trees, Z, r, src, pick
  let τOf : Fin (c + 1) → BTree Nat := fun j => stageTree d gs hBRB isSharedW (stageWire j)
  let r : Fin (c + 1) → Nat := fun j => (τOf j).leaves
  -- Trace index lookup for leaves (< d or ∈ SharedWires)
  let findStage (u : Nat) : Nat :=
    (sList.findIdx (fun k => decide (d + k = u)))
  have hfindStage : ∀ u ∈ SharedWires,
      findStage u < c ∧ ∀ (h : findStage u < c + 1), stageWire ⟨findStage u, h⟩ = u := by
    intro u hu
    rcases Finset.mem_image.mp hu with ⟨k, hkSh, rfl⟩
    have hks : k ∈ sList := (hsListMem k).mpr hkSh
    have hex : ∃ x ∈ sList, decide (d + x = d + k) = true := ⟨k, hks, by simp⟩
    have hlt : sList.findIdx (fun x => decide (d + x = d + k)) < sList.length :=
      List.findIdx_lt_length.mpr hex
    have hpred : decide (d + sList[sList.findIdx (fun x => decide (d + x = d + k))]'hlt = d + k) = true :=
      List.findIdx_getElem (w := hlt)
    have heq : d + sList[sList.findIdx (fun x => decide (d + x = d + k))]'hlt = d + k :=
      of_decide_eq_true hpred
    have hltc : findStage (d + k) < c := by rw [← hsListLen]; exact hlt
    refine ⟨hltc, ?_⟩
    intro h
    simp only [stageWire, hltc, dite_true, findStage]
    exact heq
  let traceIdx : Nat → Nat := fun u => if u < d then u else d + findStage u
  let Z : Nat → Fin m → Bool := fun u =>
    if h : u < d then
      fun t => X t ⟨u, h⟩
    else if h2 : u - d < c + 1 then
      fun t => valB X gs (stageWire ⟨u - d, h2⟩) t
    else
      fun _ => false
  let src : (j : Fin (c + 1)) → Fin (r j) → Nat := fun j a => traceIdx ((τOf j).leafAt a)
  let pick : (j : Fin (c + 1)) → Fin m → Fin m → Fin (r j) :=
    fun j h l => (τOf j).pick (fun u t => valB X gs u t) h l
  -- Verify Z properties
  have hZvar : ∀ i : Fin d, Z i.val = fun t => X t i := by
    intro i; simp [Z, i.isLt]
  have hZstage : ∀ j : Fin (c + 1), Z (d + j.val) = fun t => valB X gs (stageWire j) t := by
    intro j
    have h1 : ¬ (d + j.val < d) := by omega
    have h2 : d + j.val - d < c + 1 := by simp [j.isLt]
    simp only [Z, h1, h2, dite_false, dite_true]
    have heq : (⟨d + j.val - d, h2⟩ : Fin (c + 1)) = j := by ext; simp
    rw [heq]
  have hZtop : Z (d + c) = T := by
    have h1 := hZstage ⟨c, by omega⟩
    have hsw : stageWire ⟨c, by omega⟩ = out := by simp [stageWire]
    rw [hsw] at h1
    funext t
    rw [congrFun h1 t, houtEval t]
  have hZleaf : ∀ j : Fin (c + 1), ∀ a : Fin (r j),
      src j a < d + j.val ∧ Z (src j a) = fun t => valB X gs ((τOf j).leafAt a) t := by
    intro j a
    have hwlt : stageWire j < d + gs.length := hRlt _ (hStageInR j)
    have hlp := stageTree_leaf_props d gs hBRB isSharedW (stageWire j) hwlt a
    set v := (τOf j).leafAt a
    have hsrcEq : src j a = traceIdx v := rfl
    rw [hsrcEq]
    rcases hlp with hvd | ⟨hvlt, hvsh⟩
    · refine ⟨by simp [traceIdx, hvd]; omega, ?_⟩
      simp only [traceIdx, hvd, ite_true]
      funext t
      rw [congrFun (hZvar ⟨v, hvd⟩) t, valB_var X gs ⟨v, hvd⟩ t]
    · have hvMem : v ∈ SharedWires := (hisSharedW v).mp hvsh
      have hvNotD : ¬ (v < d) := by
        rcases Finset.mem_image.mp hvMem with ⟨k, _, hkEq⟩; omega
      have ⟨hfltc, hfeqAll⟩ := hfindStage v hvMem
      have hfeq : stageWire ⟨findStage v, by omega⟩ = v := hfeqAll (by omega)
      have hfltJ : findStage v < j.val := by
        by_contra hge
        have hle : j.val ≤ findStage v := by omega
        rcases Nat.eq_or_lt_of_le hle with heq | hlt
        · have hjeq : (⟨findStage v, by omega⟩ : Fin (c + 1)) = j := Fin.ext heq.symm
          rw [hjeq] at hfeq
          omega
        · have := hStageStrict j ⟨findStage v, by omega⟩ hlt
          rw [hfeq] at this
          omega
      refine ⟨by simp [traceIdx, hvNotD]; omega, ?_⟩
      simp only [traceIdx, hvNotD, ite_false]
      rw [hZstage ⟨findStage v, by omega⟩, hfeq]
  -- Count total gates across all stages: ∑ j, (τOf j).gates = G.card
  let occ : Nat → Nat := fun k => ∑ j : Fin (c + 1), stageOcc d gs hBRB isSharedW k (stageWire j)
  have hOccEqOne : ∀ k ∈ G, occ k = 1 := by
    -- Downward induction on gs.length - k
    have hdown : ∀ n k, gs.length - k = n → k ∈ G → occ k = 1 := by
      intro n
      induction n using Nat.strong_induction_on with
      | ind n ih =>
        intro k hn hkG
        have ⟨hklt, hkR⟩ := (hGdef k).mp hkG
        by_cases hsh : k ∈ Shared
        · -- Shared gate: expanded once at its own stage root, 0 in all subTrees
          have hshW : isSharedW (d + k) = true :=
            (hisSharedW (d + k)).mpr (Finset.mem_image_of_mem _ hsh)
          have hsub0 : ∀ u, subOcc d gs hBRB isSharedW k u = 0 :=
            subOcc_eq_zero_of_shared d gs hBRB isSharedW k hshW
          have hstage_eq : ∀ j : Fin (c + 1),
              stageOcc d gs hBRB isSharedW k (stageWire j) = if stageWire j = d + k then 1 else 0 := by
            intro j
            unfold stageOcc
            by_cases h1 : d ≤ stageWire j ∧ stageWire j - d < gs.length
            · simp only [h1, and_self, dite_true, hsub0, Nat.add_zero]
              have hiff : stageWire j - d = k ↔ stageWire j = d + k := by omega
              simp [hiff]
            · simp only [h1, dite_false]
              have hne : stageWire j ≠ d + k := by
                intro heq; apply h1; rw [heq]; exact ⟨by omega, by simpa using hklt⟩
              simp [hne]
          have ⟨hfltc, hfeqAll⟩ := hfindStage (d + k) (Finset.mem_image_of_mem _ hsh)
          let j0 : Fin (c + 1) := ⟨findStage (d + k), by omega⟩
          have hfeq : stageWire j0 = d + k := hfeqAll (by omega)
          have hocc_rw : occ k = ∑ j : Fin (c + 1), if j = j0 then 1 else 0 := by
            simp only [occ]
            apply Finset.sum_congr rfl
            intro j _
            rw [hstage_eq j]
            have hiff : stageWire j = d + k ↔ j = j0 := by
              constructor
              · intro heq; exact hStageInj (heq.trans hfeq.symm)
              · intro heq; rw [heq]; exact hfeq
            simp [hiff]
          rw [hocc_rw]
          simp
        · by_cases houtEq : d + k = out
          · -- Root gate = out: expanded once at stage c, 0 at all earlier stages (< out)
            have hstage_eq : ∀ j : Fin (c + 1),
                stageOcc d gs hBRB isSharedW k (stageWire j) = if j.val = c then 1 else 0 := by
              intro j
              by_cases hjc : j.val = c
              · have hnotlt : ¬ (j.val < c) := by omega
                have hsw : stageWire j = out := by simp [stageWire, hnotlt]
                rw [hsw, ← houtEq]
                unfold stageOcc
                have hcond : d ≤ d + k ∧ d + k - d < gs.length := ⟨by omega, by simpa using hklt⟩
                rw [dif_pos hcond]
                have h1 := subOcc_eq_zero_of_lt d gs hBRB isSharedW k _ (hBRB k hklt).1
                have h2 := subOcc_eq_zero_of_lt d gs hBRB isSharedW k _ (hBRB k hklt).2
                simp [Nat.add_sub_cancel_left, hklt, h1, h2, hjc]
              · have hjlt : j.val < c := by omega
                have hswlt : stageWire j < d + k := by rw [houtEq]; exact hStageLtOut j hjlt
                simp only [hjc, ite_false]
                unfold stageOcc
                by_cases h : d ≤ stageWire j ∧ stageWire j - d < gs.length
                · simp only [h, and_self, dite_true]
                  have hne : stageWire j - d ≠ k := by omega
                  have hl : gs[stageWire j - d].lhs < d + k := by
                    have := h.1; have := (hBRB (stageWire j - d) h.2).1; omega
                  have hr : gs[stageWire j - d].rhs < d + k := by
                    have := h.1; have := (hBRB (stageWire j - d) h.2).2; omega
                  simp [hne, subOcc_eq_zero_of_lt d gs hBRB isSharedW k _ hl,
                        subOcc_eq_zero_of_lt d gs hBRB isSharedW k _ hr]
                · simp [h]
            have hocc_rw : occ k = ∑ j : Fin (c + 1), if j = ⟨c, by omega⟩ then 1 else 0 := by
              simp only [occ]
              apply Finset.sum_congr rfl
              intro j _
              rw [hstage_eq j]
              have hiff : j.val = c ↔ j = ⟨c, by omega⟩ := by
                constructor
                · intro h; ext; exact h
                · intro h; rw [h]
              simp [hiff]
            rw [hocc_rw]
            simp
          · -- Interior unshared gate: uses (d + k) = 1, apply balance + downward IH!
            have hnotShW : isSharedW (d + k) = false := by
              cases hb : isSharedW (d + k) with
              | false => rfl
              | true =>
                exfalso
                have hm := (hisSharedW (d + k)).mp hb
                rcases Finset.mem_image.mp hm with ⟨k1, hk1, heq⟩
                have : k1 = k := by omega
                subst this
                exact hsh hk1
            have hswNe : ∀ j : Fin (c + 1), stageWire j ≠ d + k := by
              intro j heq
              by_cases hj : j.val < c
              · simp only [stageWire, hj, dite_true] at heq
                have hks : sList[j.val]'(by omega) ∈ Shared := (hsListMem _).mp (List.getElem_mem _)
                have : sList[j.val]'(by omega) = k := by omega
                rw [this] at hks
                exact hsh hks
              · simp only [stageWire, hj, dite_false] at heq
                exact houtEq heq.symm
            have hbal : occ k = ∑ k' ∈ G, occ k' * hitGate gs (d + k) k' := by
              simp only [occ]
              have hstep : ∀ j : Fin (c + 1),
                  stageOcc d gs hBRB isSharedW k (stageWire j) =
                  ∑ k' ∈ G, stageOcc d gs hBRB isSharedW k' (stageWire j) * hitGate gs (d + k) k' :=
                fun j => stageOcc_balance d gs hBRB isSharedW G out hGdef k hkG hnotShW
                  (stageWire j) (hStageInR j) (hswNe j)
              rw [Finset.sum_congr rfl (fun j _ => hstep j), Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro k' _
              rw [← Finset.sum_mul]
            rw [hbal]
            have hterm : ∀ k' ∈ G, occ k' * hitGate gs (d + k) k' = hitGate gs (d + k) k' := by
              intro k' hk'G
              by_cases hhit0 : hitGate gs (d + k) k' = 0
              · simp [hhit0]
              · have hk'lt : k' < gs.length := ((hGdef k').mp hk'G).1
                have hklt' : k < k' := by
                  simp only [hitGate, hk'lt, dite_true] at hhit0
                  have h1 := (hBRB k' hk'lt).1
                  have h2 := (hBRB k' hk'lt).2
                  by_contra hge
                  have hne1 : gs[k'].lhs ≠ d + k := by omega
                  have hne2 : gs[k'].rhs ≠ d + k := by omega
                  simp [hne1, hne2] at hhit0
                have hocck' : occ k' = 1 := ih (gs.length - k') (by omega) k' rfl hk'G
                rw [hocck', Nat.one_mul]
            rw [Finset.sum_congr rfl hterm]
            have huses1 : uses (d + k) = 1 := by
              have hge1 := hUsesPos (d + k) hkR
              have hnot2 : ¬ (2 ≤ uses (d + k)) := fun h2 => hsh ((hSharedMem k).mpr ⟨hkG, h2⟩)
              omega
            simp only [uses, houtEq, ite_false, Nat.zero_add] at huses1
            exact huses1
    intro k hkG
    exact hdown (gs.length - k) k rfl hkG
  have hSumGates : ∑ j : Fin (c + 1), (τOf j).gates = G.card := by
    have h1 : ∀ j : Fin (c + 1), (τOf j).gates = ∑ k ∈ G, stageOcc d gs hBRB isSharedW k (stageWire j) :=
      fun j => stageTree_gates_eq_sum_stageOcc d gs hBRB isSharedW G out hGdef (stageWire j) (hStageInR j)
    rw [Finset.sum_congr rfl (fun j _ => h1 j), Finset.sum_comm]
    have h2 : ∀ k ∈ G, ∑ j : Fin (c + 1), stageOcc d gs hBRB isSharedW k (stageWire j) = 1 :=
      fun k hkG => hOccEqOne k hkG
    rw [Finset.sum_congr rfl h2]
    simp
  have hSumR : Finset.univ.sum r ≤ d + e + c := by
    have h1 : Finset.univ.sum r = (∑ j : Fin (c + 1), (τOf j).gates) + (c + 1) := by
      calc ∑ j : Fin (c + 1), (τOf j).leaves
          = ∑ j : Fin (c + 1), ((τOf j).gates + 1) := by
            apply Finset.sum_congr rfl; intro j _; exact (τOf j).leaves_eq_gates_add_one
        _ = (∑ j : Fin (c + 1), (τOf j).gates) + ∑ _j : Fin (c + 1), 1 := Finset.sum_add_distrib
        _ = (∑ j : Fin (c + 1), (τOf j).gates) + (c + 1) := by simp
    rw [h1, hSumGates]
    omega
  -- Assemble the final existential witness!
  refine ⟨c, Z, r, src, pick, hcLeE, hSumR, hZvar, hZtop, ?_⟩
  intro j
  have hτeval : ∀ t, (τOf j).eval (fun u => valB X gs u t) = Z (d + j.val) t := by
    intro t
    rw [congrFun (hZstage j) t]
    exact stageTree_eval X gs hBRB isSharedW (stageWire j) t
  have hNCj := hNC (stageWire j) (hRlt _ (hStageInR j))
  refine ⟨(τOf j).leaves_pos, fun a => (hZleaf j a).1, ?_, ?_, ?_, ?_⟩
  · rcases hNCj.1 with ⟨h, hh⟩
    exact ⟨h, by rw [congrFun (hZstage j) h]; exact hh⟩
  · rcases hNCj.2 with ⟨l, hl⟩
    exact ⟨l, by rw [congrFun (hZstage j) l]; exact hl⟩
  · intro h l ⟨hh, hl⟩
    rw [← hτeval h] at hh
    rw [← hτeval l] at hl
    have hps := (τOf j).pick_sep (fun u t => valB X gs u t) h l hh hl
    have hzl := (hZleaf j (pick j h l)).2
    rw [congrFun hzl h, congrFun hzl l]
    exact hps
  · intro S hScard
    have hsp := (τOf j).pick_split (fun u t => valB X gs u t) S hScard
    have hcellEq : ∀ h l, cellOf (fun u t => valB X gs u t) (τOf j) h l ↔
        (Z (d + j.val) h = true ∧ Z (d + j.val) l = false) := by
      intro h l
      simp only [cellOf, hτeval]
    rcases hsp with ⟨U, hUne, hUss, hno⟩ | ⟨U, hUne, hUss, hno⟩
    · left
      refine ⟨U, hUne, hUss, ?_⟩
      intro a ha b hb ⟨h, l, t, hc1, hc2, hp1, hp2⟩
      exact hno a ha b hb ⟨h, l, t, (hcellEq h l).mpr hc1, (hcellEq h t).mpr hc2, hp1, hp2⟩
    · right
      refine ⟨U, hUne, hUss, ?_⟩
      intro a ha b hb ⟨h, l, t, hc1, hc2, hp1, hp2⟩
      exact hno a ha b hb ⟨h, l, t, (hcellEq h l).mpr hc1, (hcellEq t l).mpr hc2, hp1, hp2⟩

end PEqualNP.Outside.L_lib_1392

theorem PEqualNP.Outside.L_lib_1392 :
    ∀ (d m e : Nat) (X : Fin m → Fin d → Bool) (T : Fin m → Bool), 0 < d →
  (∀ i, ∃ h l, T h = true ∧ T l = false ∧
    ∀ j, (X h j = true ∧ X l j = false) ↔ j = i) →
  let fits := ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (d+2) C ∧
    PEqualNP.NotBracket.notCount C = 0 ∧ C.output < d+2+C.size ∧ C.size ≤ d-1+e ∧
    ∀ t, C.eval (List.ofFn (X t) ++ [false,true]) = T t
  fits ↔ ∃ (c : Nat) (Z : Nat → Fin m → Bool) (r : Fin (c+1) → Nat)
    (src : (j : Fin (c+1)) → Fin (r j) → Nat)
    (pick : (j : Fin (c+1)) → Fin m → Fin m → Fin (r j)),
    c ≤ e ∧ (Finset.univ.sum r) ≤ d+e+c ∧
    (∀ i : Fin d, Z i.val = fun t => X t i) ∧ Z (d+c) = T ∧
    ∀ j : Fin (c+1), 0 < r j ∧ (∀ a, src j a < d+j.val) ∧
      (∃ h, Z (d+j.val) h = true) ∧ (∃ l, Z (d+j.val) l = false) ∧
      let cell := fun h l => Z (d+j.val) h = true ∧ Z (d+j.val) l = false
      (∀ h l, cell h l → Z (src j (pick j h l)) h = true ∧ Z (src j (pick j h l)) l = false) ∧
      let row := fun a b => ∃ h l t, cell h l ∧ cell h t ∧ pick j h l = a ∧ pick j h t = b
      let col := fun a b => ∃ h l t, cell h l ∧ cell t l ∧ pick j h l = a ∧ pick j t l = b
      let split := fun (S : Finset (Fin (r j))) (adj : Fin (r j) → Fin (r j) → Prop) =>
        ∃ U : Finset (Fin (r j)), U.Nonempty ∧ U ⊂ S ∧ ∀ a ∈ U, ∀ b ∈ S \ U, ¬adj a b
      ∀ S : Finset (Fin (r j)), 2 ≤ S.card → split S row ∨ split S col := by
  intro d m e X T hd hsep
  constructor
  · rintro ⟨C, hF, hRB, hN, hout, hsz, heval⟩
    exact PEqualNP.Outside.L_lib_1392.forward_dir d m e X T hd hsep C hF hRB hN hout hsz heval
  · rintro ⟨c, Z, r, src, pick, _, hrsum, hZbase, hZtop, hstage⟩
    exact PEqualNP.Outside.L_lib_1392.backward_dir d m e X T hd c Z r src pick hrsum hZbase hZtop hstage

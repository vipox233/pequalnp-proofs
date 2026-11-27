import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24159_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def combine (t a b : Bool) : Bool := if t then a && b else a || b

theorem combine_comm (t a b : Bool) : combine t a b = combine t b a := by
  cases t <;> simp [combine, Bool.and_comm, Bool.or_comm]

theorem combine_mono (t a b c d : Bool) (ha : a = true → c = true)
    (hb : b = true → d = true) (h : combine t a b = true) :
    combine t c d = true := by
  cases t <;> cases a <;> cases b <;> cases c <;> cases d <;> simp_all [combine]

inductive Formula (α : Type) where
  | var (a : α)
  | join (t : Bool) (left right : Formula α)

def leaves {α : Type} : Formula α → List α
  | .var a => [a]
  | .join _ f g => leaves f ++ leaves g

def support {α : Type} [DecidableEq α] (f : Formula α) : Finset α :=
  (leaves f).toFinset

def evalF {α : Type} (x : α → Bool) : Formula α → Bool
  | .var a => x a
  | .join t f g => combine t (evalF x f) (evalF x g)

def Linear {α : Type} [DecidableEq α] : Formula α → Prop
  | .var _ => True
  | .join _ f g => Linear f ∧ Linear g ∧ Disjoint (support f) (support g)

theorem support_join {α : Type} [DecidableEq α] (t : Bool) (f g : Formula α) :
    support (.join t f g) = support f ∪ support g := by
  ext a
  simp [support, leaves]

theorem support_nonempty {α : Type} [DecidableEq α] (f : Formula α) :
    (support f).Nonempty := by
  induction f with
  | var a => exact ⟨a, by simp [support, leaves]⟩
  | join t f g ih _ =>
    obtain ⟨a, ha⟩ := ih
    exact ⟨a, support_join t f g ▸ Finset.mem_union_left _ ha⟩

theorem leaves_nodup {α : Type} [DecidableEq α] (f : Formula α) (h : Linear f) :
    (leaves f).Nodup := by
  induction f with
  | var a => simp [leaves]
  | join t f g ihf ihg =>
    change (leaves f ++ leaves g).Nodup
    apply List.nodup_iff_count_le_one.mpr
    intro a
    have h1 := List.nodup_iff_count_le_one.mp (ihf h.1) a
    have h2 := List.nodup_iff_count_le_one.mp (ihg h.2.1) a
    rw [List.count_append]
    by_cases hf : a ∈ leaves f
    · have hg : a ∉ leaves g := by
        intro hg
        exact (Finset.disjoint_left.mp h.2.2)
          (by simpa [support] using hf) (by simpa [support] using hg)
      have he : (leaves g).count a = 0 := by
        by_contra e
        exact hg (List.count_pos_iff.mp (Nat.pos_of_ne_zero e))
      omega
    · have he : (leaves f).count a = 0 := by
        by_contra e
        exact hf (List.count_pos_iff.mp (Nat.pos_of_ne_zero e))
      omega

theorem evalF_local {α : Type} [DecidableEq α] (f : Formula α) (x y : α → Bool)
    (h : ∀ i ∈ support f, x i = y i) : evalF x f = evalF y f := by
  induction f with
  | var a => exact h a (by simp [support, leaves])
  | join t f g ihf ihg =>
    rw [support_join] at h
    simp only [evalF]
    rw [ihf (fun i hi => h i (Finset.mem_union_left _ hi)),
      ihg (fun i hi => h i (Finset.mem_union_right _ hi))]

theorem evalF_mono {α : Type} (f : Formula α) {x y : α → Bool}
    (h : ∀ a, x a = true → y a = true) (he : evalF x f = true) : evalF y f = true := by
  induction f with
  | var a => exact h a he
  | join t f g ihf ihg => exact combine_mono _ _ _ _ _ ihf ihg he

theorem evalF_empty {α : Type} (f : Formula α) : evalF (fun _ => false) f = false := by
  induction f with
  | var _ => rfl
  | join t f g ihf ihg => simp [evalF, combine, ihf, ihg]

inductive Context (α : Type) where
  | hole
  | attach (t : Bool) (core : Context α) (side : Formula α)

def ctxSupport {α : Type} [DecidableEq α] : Context α → Finset α
  | .hole => ∅
  | .attach _ c f => ctxSupport c ∪ support f

def ctxLinear {α : Type} [DecidableEq α] : Context α → Prop
  | .hole => True
  | .attach _ c f => ctxLinear c ∧ Linear f ∧ Disjoint (ctxSupport c) (support f)

def evalCtx {α : Type} (x : α → Bool) (b : Bool) : Context α → Bool
  | .hole => b
  | .attach t c f => combine t (evalCtx x b c) (evalF x f)

theorem evalCtx_local {α : Type} [DecidableEq α] (c : Context α) (x y : α → Bool)
    (b : Bool) (h : ∀ i ∈ ctxSupport c, x i = y i) : evalCtx x b c = evalCtx y b c := by
  induction c with
  | hole => rfl
  | attach t c f ih =>
    simp only [evalCtx]
    rw [ih (fun i hi => h i (Finset.mem_union_left _ hi)),
      evalF_local f x y (fun i hi => h i (Finset.mem_union_right _ hi))]

theorem evalCtx_mono {α : Type} (c : Context α) {x y : α → Bool} {a b : Bool}
    (h : ∀ i, x i = true → y i = true) (hab : a = true → b = true)
    (he : evalCtx x a c = true) : evalCtx y b c = true := by
  induction c with
  | hole => exact hab he
  | attach t c f ih => exact combine_mono _ _ _ _ _ ih (evalF_mono f h) he

theorem interp {α : Type} (c : Context α) (x : α → Bool) (b : Bool) :
    evalCtx x b c = (evalCtx x false c || (b && evalCtx x true c)) := by
  cases b
  · simp
  · have h : evalCtx x false c = true → evalCtx x true c = true :=
      evalCtx_mono c (fun _ e => e) (by simp)
    cases h0 : evalCtx x false c <;> cases h1 : evalCtx x true c <;> simp_all

abbrev Part (α : Type) := Sum Bool (Formula α)

def evalPart {α : Type} (x : α → Bool) : Part α → Bool
  | .inl a => a
  | .inr f => evalF x f

def partSupport {α : Type} [DecidableEq α] : Part α → Finset α
  | .inl _ => ∅
  | .inr f => support f

def partLinear {α : Type} [DecidableEq α] : Part α → Prop
  | .inl _ => True
  | .inr f => Linear f

def addSide {α : Type} (t : Bool) (p : Part α) (f : Formula α) : Part α :=
  match p with
  | .inr g => .inr (.join t g f)
  | .inl b => if t = b then .inr f else .inl b

def replaceHole {α : Type} (b : Bool) : Context α → Part α
  | .hole => .inl b
  | .attach t c f => addSide t (replaceHole b c) f

theorem addSide_eval {α : Type} (t : Bool) (p : Part α) (f : Formula α) (x : α → Bool) :
    evalPart x (addSide t p f) = combine t (evalPart x p) (evalF x f) := by
  cases p with
  | inl b => cases t <;> cases b <;> simp [addSide, evalPart, combine]
  | inr g => rfl

theorem replace_eval {α : Type} (b : Bool) (c : Context α) (x : α → Bool) :
    evalPart x (replaceHole b c) = evalCtx x b c := by
  induction c with
  | hole => rfl
  | attach t c f ih => simp only [replaceHole, evalCtx, addSide_eval, ih]

theorem replace_linear {α : Type} [DecidableEq α] (b : Bool) (c : Context α)
    (h : ctxLinear c) :
    partLinear (replaceHole b c) ∧ partSupport (replaceHole b c) ⊆ ctxSupport c := by
  induction c with
  | hole => simp [replaceHole, partLinear, partSupport, ctxSupport]
  | attach t c f ih =>
    obtain ⟨hl, hs⟩ := ih h.1
    cases e : replaceHole b c with
    | inl a =>
      simp only [replaceHole, e, addSide, ctxSupport]
      split_ifs
      · exact ⟨h.2.1, fun _ hi => Finset.mem_union_right _ hi⟩
      · exact ⟨trivial, Finset.empty_subset _⟩
    | inr g =>
      rw [e] at hl hs
      simp only [replaceHole, e, addSide, partLinear, partSupport, Linear, support_join, ctxSupport]
      exact ⟨⟨hl, h.2.1, Finset.disjoint_of_subset_left hs h.2.2⟩,
        Finset.union_subset_union hs (Finset.Subset.refl _)⟩

theorem foldl_snoc_keeps {α β : Type _} (F : List α → β → α) (gs : List β) (init : List α) :
    init <+: gs.foldl (fun R g => R ++ [F R g]) init := by
  induction gs generalizing init with
  | nil => exact List.prefix_refl _
  | cons g gs ih => exact (List.prefix_append init [F init g]).trans (ih _)

theorem foldl_snoc_length {α β : Type _} (F : List α → β → α) (gs : List β) (init : List α) :
    (gs.foldl (fun R g => R ++ [F R g]) init).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp
  | cons g gs ih => simp [ih]; omega

theorem getD_of_initial {α : Type _} {P L : List α} (h : P <+: L) {i : ℕ} (hi : i < P.length)
    (d : α) : L.getD i d = P.getD i d := by
  obtain ⟨t, rfl⟩ := h
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem foldl_snoc_split {α β : Type _} (F : List α → β → α) (gs : List β) (init : List α)
    (j : ℕ) (hj : j < gs.length) (d : α) :
    (gs.foldl (fun R g => R ++ [F R g]) init).getD (init.length + j) d
      = F ((gs.take j).foldl (fun R g => R ++ [F R g]) init) gs[j] ∧
    ((gs.take j).foldl (fun R g => R ++ [F R g]) init) <+:
      gs.foldl (fun R g => R ++ [F R g]) init ∧
    ((gs.take j).foldl (fun R g => R ++ [F R g]) init).length = init.length + j := by
  have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by simp
  set P := (gs.take j).foldl (fun R g => R ++ [F R g]) init with hP
  have hPl : P.length = init.length + j := by
    rw [hP, foldl_snoc_length F]; simp; omega
  have hpre : (P ++ [F P gs[j]]) <+: gs.foldl (fun R g => R ++ [F R g]) init := by
    conv_rhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
    exact foldl_snoc_keeps F _ _
  refine ⟨?_, (List.prefix_append P _).trans hpre, hPl⟩
  rw [getD_of_initial hpre (by simp; omega), ← hPl]
  simp

def readGate (w : List Bool) (g : Gate) := g.op.eval (g.inputs.map fun i => w.getD i false)

theorem wireAt (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (x.length + j) false = C.gates[j].op.eval
      (C.gates[j].inputs.map fun i => if i < x.length + j then (C.wires x).getD i false else false) := by
  obtain ⟨value,pre,len⟩ := foldl_snoc_split readGate C.gates x j hj false
  rw [show (C.wires x).getD (x.length + j) false = _ from value]
  unfold readGate
  congr 1
  apply List.map_congr_left
  intro i _
  split
  · exact (getD_of_initial pre (by omega) false).symm
  · apply List.getD_eq_default
    unfold readGate at len
    omega

def wire (N : ℕ) (C : Circuit) (i : ℕ) (x : Fin N → Bool) : Bool :=
  (C.wires (List.ofFn x)).getD i false

theorem wire_input (N : ℕ) (C : Circuit) (i : ℕ) (hi : i < N) :
    wire N C i = fun x => x ⟨i, hi⟩ := by
  funext x
  have hl : i < (List.ofFn x).length := by simpa using hi
  have hp : List.ofFn x <+: C.wires (List.ofFn x) := foldl_snoc_keeps readGate C.gates _
  rw [wire, getD_of_initial hp hl false, List.getD_eq_getElem _ _ hl]
  exact List.getElem_ofFn hl


def step (w : List Bool) (g : Gate) : List Bool := w ++ [readGate w g]

theorem wire_gate' {N : ℕ} (C : Circuit) (hback : ReadsBack N C) (j : ℕ)
    (hj : j < C.gates.length) (x : Fin N → Bool) :
    wire N C (N + j) x = (gateAt C j).op.eval
      ((gateAt C j).inputs.map fun i => wire N C i x) := by
  have he := wireAt C (List.ofFn x) j hj
  have hat : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
  rw [List.length_ofFn, ← hat] at he
  rw [wire, he]
  congr 1
  exact List.map_congr_left fun i hi => by
    simp only [ite_eq_left (hback j hj i hi), wire]

def binaryOp (t : Bool) : GateOp := if t then .and else .or

theorem binary_eval (t a b : Bool) : (binaryOp t).eval [a, b] = combine t a b := by
  cases t <;> simp [binaryOp, combine, GateOp.eval]

theorem binary_op (t : Bool) : binaryOp t = .and ∨ binaryOp t = .or := by
  cases t <;> simp [binaryOp]

def post {N : ℕ} (k : ℕ) : Formula (Fin N) → Circuit
  | .var a => ⟨[], a.val⟩
  | .join t f g =>
    let L := post k f
    let R := post (k + L.size) g
    ⟨L.gates ++ R.gates ++ [⟨binaryOp t, [L.output, R.output]⟩], k + L.size + R.size⟩

theorem post_small {N : ℕ} (f : Formula (Fin N)) {k : ℕ} (hk : N ≤ k) :
    (post k f).output < k + (post k f).size := by
  cases f with
  | var a =>
    have h := a.isLt
    change a.val < k + 0
    omega
  | join t f g =>
    simp only [post, Circuit.size, List.length_append, List.length_singleton]
    omega

theorem post_root {N : ℕ} (f : Formula (Fin N)) (k : ℕ) :
    (post k f).output + 1 = k + (post k f).size ∨
      ((post k f).size = 0 ∧ (post k f).output < N) := by
  cases f with
  | var a => exact Or.inr ⟨rfl, a.isLt⟩
  | join t f g =>
    left
    simp only [post, Circuit.size, List.length_append, List.length_singleton]
    omega

def Wired : ℕ → List Gate → Prop
  | _, [] => True
  | k, g :: gs =>
      ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∧
      (∀ a ∈ g.inputs, a < k) ∧ Wired (k + 1) gs

theorem wired_append (k : ℕ) (l r : List Gate) :
    Wired k (l ++ r) ↔ Wired k l ∧ Wired (k + l.length) r := by
  induction l generalizing k with
  | nil => simp [Wired]
  | cons a l ih =>
    simp only [List.cons_append, Wired, List.length_cons, ih, Nat.add_assoc, Nat.add_comm 1]
    tauto

theorem post_wired {N : ℕ} (f : Formula (Fin N)) {k : ℕ} (hk : N ≤ k) :
    Wired k (post k f).gates := by
  induction f generalizing k with
  | var a => trivial
  | join t f g ihf ihg =>
    let L := post k f
    let R := post (k + L.size) g
    change Wired k (L.gates ++ R.gates ++ [⟨binaryOp t, [L.output, R.output]⟩])
    rw [List.append_assoc, wired_append, wired_append]
    have hr : N ≤ k + L.size := by omega
    refine ⟨ihf hk, ihg hr, ⟨binary_op t, rfl⟩, ?_, trivial⟩
    intro i hi
    have hl := post_small f hk
    have hv := post_small g hr
    change i < k + L.size + R.size
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · change L.output < k + L.size at hl
      omega
    · exact hv

theorem wired_shape {gs : List Gate} {k : ℕ} (hw : Wired k gs) :
    ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
  induction gs generalizing k with
  | nil => simp
  | cons g gs ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hw.1
    · exact ih hw.2.2 a ha

theorem wired_reads {gs : List Gate} {k : ℕ} (hw : Wired k gs) :
    ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨.or, []⟩).inputs, i < k + j := by
  induction gs generalizing k with
  | nil => simp
  | cons g gs ih =>
    intro j hj i hi
    cases j with
    | zero => exact hw.2.1 i hi
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have he : i ∈ (gs.getD j ⟨.or, []⟩).inputs := hi
      have h := ih hw.2.2 j hj' i he
      omega

theorem post_eval {N : ℕ} (f : Formula (Fin N)) (x : Fin N → Bool)
    (k : ℕ) (hk : N ≤ k) (init : List Bool) (hi : init.length = k)
    (h : ∀ i : Fin N, init.getD i.val false = x i) :
    ((post k f).gates.foldl step init).getD (post k f).output false = evalF x f := by
  induction f generalizing k init with
  | var a => exact h a
  | join t f g ihf ihg =>
    let L := post k f
    let R := post (k + L.size) g
    let a := L.gates.foldl step init
    let b := R.gates.foldl step a
    have ha : a.length = k + L.size := by
      change (L.gates.foldl (fun l g => l ++ [readGate l g]) init).length = _
      rw [foldl_snoc_length readGate, hi]
      rfl
    have hb : b.length = k + L.size + R.size := by
      change (R.gates.foldl (fun l g => l ++ [readGate l g]) a).length = _
      rw [foldl_snoc_length readGate, ha]
      rfl
    have hp : init <+: a := foldl_snoc_keeps readGate L.gates init
    have hq : a <+: b := foldl_snoc_keeps readGate R.gates a
    have hka : N ≤ k + L.size := by omega
    have hf0 : a.getD L.output false = evalF x f := ihf k hk init hi h
    have hf : b.getD L.output false = evalF x f := by
      have hlt : L.output < a.length := ha.symm ▸ post_small f hk
      exact (getD_of_initial hq hlt false).trans hf0
    have hg : b.getD R.output false = evalF x g := by
      apply ihg (k + L.size) hka a ha
      intro i
      have hlt : i.val < init.length := by have := i.isLt; omega
      exact (getD_of_initial hp hlt false).trans (h i)
    change ((L.gates ++ R.gates ++ ([⟨binaryOp t, [L.output, R.output]⟩] : List Gate)).foldl step init).getD
      (k + L.size + R.size) false = _
    rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change (b ++ [readGate b ⟨binaryOp t, [L.output, R.output]⟩]).getD (k + L.size + R.size) false = _
    rw [← hb]
    rw [show (b ++ [readGate b ⟨binaryOp t, [L.output, R.output]⟩]).getD b.length false =
      readGate b ⟨binaryOp t, [L.output, R.output]⟩ by simp]
    change (binaryOp t).eval [b.getD L.output false, b.getD R.output false] = _
    rw [binary_eval, hf, hg]
    rfl

def readCountList (gs : List Gate) (i : ℕ) : ℕ :=
  (gs.flatMap Gate.inputs).count i

theorem readCount_append (l r : List Gate) (i : ℕ) :
    readCountList (l ++ r) i = readCountList l i + readCountList r i := by
  simp [readCountList, List.flatMap_append, List.count_append]

theorem readCount_eq (C : Circuit) (i : ℕ) :
    readsIn C (Finset.range C.size) i = readCountList C.gates i := by
  obtain ⟨gs, out⟩ := C
  induction gs using List.reverseRecOn with
  | nil => simp [readsIn, Circuit.size, readCountList]
  | append_singleton gs g ih =>
    change (∑ j ∈ Finset.range (gs ++ [g]).length,
      ((gs ++ [g]).getD j ⟨.or, []⟩).inputs.count i) = _
    rw [List.length_append, List.length_singleton, Finset.sum_range_succ, readCount_append]
    have e : ((gs ++ [g]).getD gs.length ⟨.or, []⟩) = g := by simp
    rw [e]
    rw [← ih, show readCountList [g] i = g.inputs.count i by simp [readCountList]]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    change ((gs ++ [g]).getD j ⟨.or, []⟩).inputs.count i =
      (gs.getD j ⟨.or, []⟩).inputs.count i
    rw [List.getD_append _ _ _ _ (Finset.mem_range.mp hj)]

def atRoot (o i : ℕ) : ℕ := if o = i then 1 else 0

def atGate (k len i : ℕ) : ℕ := if k ≤ i ∧ i < k + len then 1 else 0

theorem gate_ranges (k a b i : ℕ) :
    atGate k a i + atGate (k + a) b i + atRoot (k + a + b) i = atGate k (a + b + 1) i := by
  unfold atGate atRoot
  split_ifs <;> omega

theorem pair_count (a b i : ℕ) : ([a, b] : List ℕ).count i = atRoot a i + atRoot b i := by
  by_cases ha : a = i <;> by_cases hb : b = i <;>
    simp [List.count_cons, atRoot, ha, hb, eq_comm]

theorem post_count {N : ℕ} (f : Formula (Fin N)) (k i : ℕ) :
    readCountList (post k f).gates i + atRoot (post k f).output i =
      ((leaves f).map Fin.val).count i + atGate k (post k f).size i := by
  induction f generalizing k with
  | var a =>
    change 0 + atRoot a.val i = ([a.val] : List ℕ).count i + atGate k 0 i
    by_cases e : a.val = i <;> simp [atRoot, atGate, List.count_cons, e, eq_comm]
  | join t f g ihf ihg =>
    let L := post k f
    let R := post (k + L.size) g
    have hl := ihf k
    have hr := ihg (k + L.size)
    have hsz : (post k (.join t f g)).size = L.size + R.size + 1 := by
      change (L.gates ++ R.gates ++ ([⟨binaryOp t, [L.output, R.output]⟩] : List Gate)).length = _
      simp [Circuit.size, Nat.add_assoc]
    rw [hsz]
    change readCountList (L.gates ++ R.gates ++ [⟨binaryOp t, [L.output, R.output]⟩]) i +
        atRoot (k + L.size + R.size) i =
      ((leaves f ++ leaves g).map Fin.val).count i + atGate k (L.size + R.size + 1) i
    rw [readCount_append, readCount_append, List.map_append, List.count_append]
    rw [show readCountList [⟨binaryOp t, [L.output, R.output]⟩] i =
      atRoot L.output i + atRoot R.output i from pair_count ..]
    have he := gate_ranges k L.size R.size i
    change readCountList L.gates i + atRoot L.output i = _ + atGate k L.size i at hl
    change readCountList R.gates i + atRoot R.output i = _ + atGate (k + L.size) R.size i at hr
    omega

def FormulaShape (N : ℕ) (C : Circuit) : Prop :=
  ((∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
    ReadsBack N C ∧ (C.output + 1 = N + C.size ∨ (C.size = 0 ∧ C.output < N)) ∧
    (∀ i < N, readsIn C (Finset.range C.size) i ≤ 1) ∧
    (∀ j < C.size, readsIn C (Finset.range C.size) (N + j) =
      if j + 1 = C.size then 0 else 1))

theorem post_spec {N : ℕ} (f : Formula (Fin N)) (hl : Linear f) :
    ∃ C : Circuit, FormulaShape N C ∧
      (∀ i : Fin N, readsIn C (Finset.range C.size) i.val = 1 → i ∈ support f) ∧
      ∀ x : Fin N → Bool, C.eval (List.ofFn x) = evalF x f := by
  let C := post N f
  have hc := post_wired f (k := N) le_rfl
  have hm : ((leaves f).map Fin.val).Nodup := (leaves_nodup f hl).map Fin.val_injective
  have hcount (i : ℕ) :
      readsIn C (Finset.range C.size) i + atRoot C.output i =
        ((leaves f).map Fin.val).count i + atGate N C.size i := by
    rw [readCount_eq]
    exact post_count f N i
  have reads (i : ℕ) (hi : i < N) :
      readsIn C (Finset.range C.size) i ≤ ((leaves f).map Fin.val).count i := by
    have h := hcount i
    simp [atGate, show ¬ N ≤ i by omega] at h
    omega
  refine ⟨C, ⟨wired_shape hc, wired_reads hc, post_root f N, ?_, ?_⟩, ?_, ?_⟩
  · intro i hi
    exact (reads i hi).trans (List.nodup_iff_count_le_one.mp hm i)
  · intro j hj
    have hzero : ((leaves f).map Fin.val).count (N + j) = 0 := by
      by_contra h
      have hp := List.count_pos_iff.mp (Nat.pos_of_ne_zero h)
      obtain ⟨i, _, hi⟩ := List.mem_map.mp hp
      have hlt := i.isLt
      omega
    have h := hcount (N + j)
    have hroot : C.output + 1 = N + C.size ∨ (C.size = 0 ∧ C.output < N) := post_root f N
    have he : C.output + 1 = N + C.size := hroot.resolve_right (by omega)
    by_cases e : j + 1 = C.size
    · have ho : C.output = N + j := by omega
      simp [atRoot, atGate, ho, e, hzero, show N + j < N + C.size by omega] at h ⊢
      omega
    · have ho : C.output ≠ N + j := by omega
      simp [atRoot, atGate, ho, e, hzero, show N + j < N + C.size by omega] at h ⊢
      omega
  · intro i hi
    have hp : 0 < ((leaves f).map Fin.val).count i.val := by
      have h := reads i.val i.isLt
      omega
    obtain ⟨j, hj, hji⟩ := List.mem_map.mp (List.count_pos_iff.mp hp)
    have e := Fin.ext hji
    exact List.mem_toFinset.mpr (e ▸ hj)
  · intro x
    apply post_eval f x N le_rfl (List.ofFn x) (by simp)
    intro i
    simp [List.getD_eq_getElem?_getD]


inductive Label (α : Type) where
  | plain (f : Formula α)
  | marked (h : Formula α) (c : Context α)

def marked {α : Type} : Label α → Prop
  | .plain _ => False
  | .marked _ _ => True

def labelSupport {α : Type} [DecidableEq α] : Label α → Finset α
  | .plain f => support f
  | .marked h c => support h ∪ ctxSupport c

def labelLinear {α : Type} [DecidableEq α] : Label α → Prop
  | .plain f => Linear f
  | .marked h c => Linear h ∧ ctxLinear c ∧ Disjoint (support h) (ctxSupport c)

def labelValue {α : Type} (x : α → Bool) : Label α → Bool
  | .plain f => evalF x f
  | .marked h c => evalCtx x (!evalF x h) c

def joinLabel {α : Type} (t : Bool) (a b : Label α) : Label α :=
  match a, b with
  | .plain f, .plain g => .plain (.join t f g)
  | .marked h c, .plain f => .marked h (.attach t c f)
  | .plain f, .marked h c => .marked h (.attach t c f)
  | .marked h _, .marked g _ => .plain (.join t h g)

theorem attach_linear {α : Type} [DecidableEq α] (t : Bool)
    (h : Formula α) (c : Context α) (f : Formula α)
    (hl : labelLinear (.marked h c)) (hf : Linear f)
    (hd : Disjoint (labelSupport (.marked h c)) (support f)) :
    labelLinear (.marked h (.attach t c f)) := by
  obtain ⟨hh, hc, hd0⟩ := hl
  have hp := Finset.disjoint_union_left.mp hd
  exact ⟨hh, ⟨hc, hf, hp.2⟩, Finset.disjoint_union_right.mpr ⟨hd0, hp.1⟩⟩

theorem join_label {α : Type} [DecidableEq α] (t : Bool) (a b : Label α)
    (ha : labelLinear a) (hb : labelLinear b)
    (hd : Disjoint (labelSupport a) (labelSupport b)) (hnot : ¬(marked a ∧ marked b)) :
    labelLinear (joinLabel t a b) ∧
      labelSupport (joinLabel t a b) = labelSupport a ∪ labelSupport b ∧
      (∀ x, labelValue x (joinLabel t a b) = combine t (labelValue x a) (labelValue x b)) ∧
      (marked (joinLabel t a b) ↔ marked a ∨ marked b) := by
  cases a with
  | plain f =>
    cases b with
    | plain g =>
      refine ⟨⟨ha, hb, hd⟩, support_join t f g, ?_, ?_⟩
      · intro x; rfl
      · simp [joinLabel, marked]
    | marked h c =>
      refine ⟨attach_linear t h c f hb ha hd.symm, ?_, ?_, ?_⟩
      · ext i
        simp only [joinLabel, labelSupport, ctxSupport, Finset.mem_union]
        tauto
      · intro x
        exact combine_comm _ _ _
      · simp [joinLabel, marked]
  | marked h c =>
    cases b with
    | plain f =>
      refine ⟨attach_linear t h c f ha hb hd, ?_, ?_, ?_⟩
      · ext i
        simp only [joinLabel, labelSupport, ctxSupport, Finset.mem_union]
        tauto
      · intro x; rfl
      · simp [joinLabel, marked]
    | marked h' c' =>
      exact (hnot ⟨trivial, trivial⟩).elim

def negateLabel {α : Type} : Label α → Label α
  | .plain f => .marked f .hole
  | .marked h c => .marked h c

theorem negate_label {α : Type} [DecidableEq α] (a : Label α) (ha : labelLinear a)
    (hm : ¬ marked a) :
    labelLinear (negateLabel a) ∧ labelSupport (negateLabel a) = labelSupport a ∧
      (∀ x, labelValue x (negateLabel a) = !(labelValue x a)) ∧ marked (negateLabel a) := by
  cases a with
  | plain f =>
    exact ⟨⟨ha, trivial, Finset.disjoint_empty_right _⟩, by simp [negateLabel, labelSupport, ctxSupport],
      fun _ => rfl, trivial⟩
  | marked h c => exact (hm trivial).elim

theorem read_mono (C : Circuit) {p q : ℕ} (h : p ≤ q) (i : ℕ) :
    readsIn C (Finset.range p) i ≤ readsIn C (Finset.range q) i := by
  unfold readsIn
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h) (fun _ _ _ => Nat.zero_le _)

def Live (N : ℕ) (C : Circuit) (k i : ℕ) : Prop :=
  i < N + k ∧ readsIn C (Finset.range k) i = 0

def GateShape (g : Gate) : Prop :=
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
    (g.op = GateOp.not ∧ g.inputs.length = 1)

theorem build_label {α : Type} [DecidableEq α] (g : Gate) (label : ℕ → Label α)
    (hg : GateShape g)
    (hlin : ∀ i ∈ g.inputs, labelLinear (label i))
    (hdis : ∀ i ∈ g.inputs, ∀ j ∈ g.inputs, i ≠ j → Disjoint (labelSupport (label i)) (labelSupport (label j)))
    (hbin : ∀ a b, g.inputs = [a, b] → a ≠ b)
    (hone : ∀ i ∈ g.inputs, ∀ j ∈ g.inputs, marked (label i) → marked (label j) → i = j)
    (hbefore : g.op = .not → ∀ i ∈ g.inputs, ¬ marked (label i)) :
    ∃ z : Label α, labelLinear z ∧
      (∀ p, p ∈ labelSupport z ↔ ∃ i ∈ g.inputs, p ∈ labelSupport (label i)) ∧
      (∀ x, labelValue x z = g.op.eval (g.inputs.map fun i => labelValue x (label i))) ∧
      (marked z ↔ g.op = .not ∨ ∃ i ∈ g.inputs, marked (label i)) := by
  rcases hg with ⟨hop, hl⟩ | ⟨hop, hl⟩
  · obtain ⟨a, b, he⟩ := List.length_eq_two.mp hl
    have ha : a ∈ g.inputs := by simp [he]
    have hb : b ∈ g.inputs := by simp [he]
    have hab := hbin a b he
    have hh : ¬ (marked (label a) ∧ marked (label b)) :=
      fun h => hab (hone a ha b hb h.1 h.2)
    have use (t : Bool) (h : g.op = binaryOp t) :
        ∃ z : Label α, labelLinear z ∧
          (∀ p, p ∈ labelSupport z ↔ ∃ i ∈ g.inputs, p ∈ labelSupport (label i)) ∧
          (∀ x, labelValue x z = g.op.eval (g.inputs.map fun i => labelValue x (label i))) ∧
          (marked z ↔ g.op = .not ∨ ∃ i ∈ g.inputs, marked (label i)) := by
      obtain ⟨hl, hs, hv, hm⟩ := join_label t (label a) (label b) (hlin a ha)
        (hlin b hb) (hdis a ha b hb hab) hh
      refine ⟨joinLabel t (label a) (label b), hl, ?_, ?_, ?_⟩
      · intro p
        rw [hs, he, Finset.mem_union]
        simp
      · intro x
        simp only [h, he, List.map_cons, List.map_nil, binary_eval]
        exact hv x
      · have hn : g.op ≠ .not := by rw [h]; cases t <;> simp [binaryOp]
        rw [hm, he]
        simp [hn]
    rcases hop with e | e
    · exact use true e
    · exact use false e
  · obtain ⟨a, he⟩ := List.length_eq_one_iff.mp hl
    have hi : a ∈ g.inputs := by simp [he]
    obtain ⟨hl, hs, hv, hm⟩ := negate_label (label a) (hlin a hi) (hbefore hop a hi)
    refine ⟨negateLabel (label a), hl, ?_, ?_, ?_⟩
    · intro p
      simp [hs, he]
    · intro x
      simpa [hop, he, GateOp.eval] using hv x
    · simp [hop, hm]


structure LabelFacts (N : ℕ) (C : Circuit) (j0 k : ℕ) (label : ℕ → Label (Fin N)) : Prop where
  linear : ∀ i, Live N C k i → labelLinear (label i)
  eval : ∀ i, Live N C k i → ∀ x, labelValue x (label i) = wire N C i x
  disjoint : ∀ i j, Live N C k i → Live N C k j → i ≠ j →
    Disjoint (labelSupport (label i)) (labelSupport (label j))
  after : ∀ i, Live N C k i → marked (label i) → j0 < k ∧ N ≤ i
  existsMarked : j0 < k → ∃ i, Live N C k i ∧ marked (label i)
  unique : ∀ i j, Live N C k i → Live N C k j → marked (label i) → marked (label j) → i = j

theorem label_invariant (N : ℕ) (C : Circuit) (j0 : ℕ) (base : Fin N)
    (hGates : ∀ g ∈ C.gates, GateShape g)
    (hBack : ReadsBack N C)
    (hNot : ∀ j < C.size, (gateAt C j).op = .not ↔ j = j0)
    (hBound : ∀ i < N + C.gates.length, readsIn C (Finset.range C.size) i ≤ 1) :
    ∀ k ≤ C.size, ∃ label, LabelFacts N C j0 k label := by
  intro k
  induction k with
  | zero =>
    intro _
    let label (i : ℕ) : Label (Fin N) :=
      if h : i < N then .plain (.var ⟨i, h⟩) else .plain (.var base)
    have init (i : ℕ) (hi : Live N C 0 i) :
        label i = .plain (.var ⟨i, by simpa using hi.1⟩) := by
      have h : i < N := by simpa using hi.1
      simp [label, h]
    refine ⟨label, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · intro i hi
      rw [init i hi]
      trivial
    · intro i hi x
      have h : i < N := by simpa using hi.1
      rw [init i hi, wire_input N C i h]
      rfl
    · intro i j hi hj hne
      rw [init i hi, init j hj]
      apply Finset.disjoint_left.mpr
      intro a ha hb
      simp [labelSupport, support, leaves] at ha hb
      exact hne (congrArg Fin.val (ha.symm.trans hb))
    · intro i hi hm
      rw [init i hi] at hm
      exact hm.elim
    · omega
    · intro i j hi hj hm _
      rw [init i hi] at hm
      exact hm.elim
  | succ k ih =>
    intro hk
    obtain ⟨label, hf⟩ := ih (by omega)
    have hg : k < C.gates.length := by change k + 1 ≤ C.gates.length at hk; omega
    let g := gateAt C k
    have hmem : g ∈ C.gates := by
      dsimp [g, gateAt]
      rw [List.getD_eq_getElem _ _ hg]
      exact List.getElem_mem _
    have parts := hGates g hmem
    have hnot : g.op = .not ↔ k = j0 := hNot k hg
    have countStep (i : ℕ) : readsIn C (Finset.range (k + 1)) i =
        readsIn C (Finset.range k) i + g.inputs.count i := by
      unfold readsIn
      rw [Finset.sum_range_succ]
    have liveOperand (i : ℕ) (hi : i ∈ g.inputs) : Live N C k i := by
      have he := hBack k hg i hi
      have hsmall := (read_mono C hk i).trans (hBound i (by omega))
      have hpos := List.count_pos_iff.mpr hi
      rw [countStep] at hsmall
      exact ⟨he, by omega⟩
    have binDistinct (a b : ℕ) (h : g.inputs = [a, b]) : a ≠ b := by
      intro e
      subst b
      have ham : a ∈ g.inputs := by simp [h]
      have ha := hBack k hg a ham
      have hsmall := (read_mono C hk a).trans (hBound a (by omega))
      rw [countStep, h] at hsmall
      simp at hsmall
    have hbefore (he : g.op = .not) (i : ℕ) (hi : i ∈ g.inputs) : ¬ marked (label i) := by
      intro hm
      have hh := (hf.after i (liveOperand i hi) hm).1
      have h := hnot.mp he
      omega
    obtain ⟨z, hzLin, hzSupport, hzEval, hzMark⟩ :=
      build_label g label parts (fun i hi => hf.linear i (liveOperand i hi))
        (fun i hi j hj => hf.disjoint i j (liveOperand i hi) (liveOperand j hj)) binDistinct
        (fun i hi j hj => hf.unique i j (liveOperand i hi) (liveOperand j hj)) hbefore
    rw [hnot] at hzMark
    let w := N + k
    let next (i : ℕ) := if i = w then z else label i
    have nextRoot : next w = z := by simp [next]
    have nextOld (i : ℕ) (hi : i ≠ w) : next i = label i := by simp [next, hi]
    have rootLive : Live N C (k + 1) w := by
      refine ⟨by dsimp [w]; omega, ?_⟩
      unfold readsIn
      apply Finset.sum_eq_zero
      intro j hj
      have hlt : j < k + 1 := Finset.mem_range.mp hj
      have hj' : j < C.gates.length := by omega
      by_contra hh
      have hpos := List.count_pos_iff.mp (Nat.pos_of_ne_zero hh)
      have he := hBack j hj' w hpos
      dsimp [w] at he
      omega
    have older (i : ℕ) (hi : Live N C (k + 1) i) (hne : i ≠ w) : Live N C k i := by
      have he := hi.1
      have hcnt := hi.2
      rw [countStep] at hcnt
      dsimp [w] at hne
      exact ⟨by omega, by omega⟩
    have free (i : ℕ) (hi : Live N C (k + 1) i) : i ∉ g.inputs := by
      intro h
      have hpos := List.count_pos_iff.mpr h
      have e := hi.2
      rw [countStep] at e
      omega
    have remains (i : ℕ) (hi : Live N C k i) (hn : i ∉ g.inputs) : Live N C (k + 1) i := by
      have sz := hi.1
      refine ⟨by omega, ?_⟩
      rw [countStep, hi.2, Nat.zero_add]
      by_contra h
      exact hn (List.count_pos_iff.mp (Nat.pos_of_ne_zero h))
    have disjointRoot (i : ℕ) (hi : Live N C (k + 1) i) (hne : i ≠ w) :
        Disjoint (labelSupport z) (labelSupport (label i)) := by
      refine Finset.disjoint_left.mpr fun a ha hb => ?_
      obtain ⟨j, hj, hm⟩ := (hzSupport a).mp ha
      have hji : j ≠ i := fun e => free i hi (e ▸ hj)
      exact (Finset.disjoint_left.mp (hf.disjoint j i (liveOperand j hj) (older i hi hne) hji)) hm hb
    have oneRoot (i : ℕ) (hi : Live N C (k + 1) i) (hne : i ≠ w)
        (hz : marked z) (hm : marked (label i)) : False := by
      rcases hzMark.mp hz with h | ⟨a, ha, hm'⟩
      · have hp := (hf.after i (older i hi hne) hm).1
        omega
      · have e := hf.unique a i (liveOperand a ha) (older i hi hne) hm' hm
        exact free i hi (e ▸ ha)
    refine ⟨next, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · intro i hi
      by_cases e : i = w
      · rw [e, nextRoot]; exact hzLin
      · rw [nextOld i e]; exact hf.linear i (older i hi e)
    · intro i hi x
      by_cases e : i = w
      · rw [e, nextRoot, hzEval x]
        change g.op.eval (g.inputs.map fun a => labelValue x (label a)) = wire N C (N + k) x
        rw [wire_gate' C hBack k hg x]
        congr 1
        exact List.map_congr_left fun a ha => hf.eval a (liveOperand a ha) x
      · rw [nextOld i e]
        exact hf.eval i (older i hi e) x
    · intro i j hi hj hne
      by_cases e : i = w
      · subst i
        rw [nextRoot, nextOld j hne.symm]
        exact disjointRoot j hj hne.symm
      · by_cases f : j = w
        · subst j
          rw [nextOld i e, nextRoot]
          exact (disjointRoot i hi e).symm
        · rw [nextOld i e, nextOld j f]
          exact hf.disjoint i j (older i hi e) (older j hj f) hne
    · intro i hi hm
      by_cases e : i = w
      · subst i
        rw [nextRoot] at hm
        have hb : N ≤ w := by dsimp [w]; omega
        refine ⟨?_, hb⟩
        rcases hzMark.mp hm with he | ⟨a, ha, hm'⟩
        · omega
        · have hp := (hf.after a (liveOperand a ha) hm').1
          omega
      · rw [nextOld i e] at hm
        have he := hf.after i (older i hi e) hm
        exact ⟨by omega, he.2⟩
    · intro hAfter
      by_cases e : k = j0
      · exact ⟨w, rootLive, nextRoot.symm ▸ hzMark.mpr (Or.inl e)⟩
      · obtain ⟨i, hi, hm⟩ := hf.existsMarked (by omega)
        by_cases hused : i ∈ g.inputs
        · exact ⟨w, rootLive, nextRoot.symm ▸ hzMark.mpr (Or.inr ⟨i, hused, hm⟩)⟩
        · have hne : i ≠ w := by
            have hs := hi.1
            dsimp [w]
            omega
          exact ⟨i, remains i hi hused, (nextOld i hne).symm ▸ hm⟩
    · intro i j hi hj hmi hmj
      by_cases e : i = w
      · subst i
        by_cases f : j = w
        · exact f.symm
        · rw [nextRoot] at hmi
          rw [nextOld j f] at hmj
          exact (oneRoot j hj f hmi hmj).elim
      · by_cases f : j = w
        · subst j
          rw [nextRoot] at hmj
          rw [nextOld i e] at hmi
          exact (oneRoot i hi e hmj hmi).elim
        · rw [nextOld i e] at hmi
          rw [nextOld j f] at hmj
          exact hf.unique i j (older i hi e) (older j hj f) hmi hmj


def bits {N : ℕ} (S : Finset (Fin N)) (i : Fin N) : Bool := decide (i ∈ S)

def on {N : ℕ} (x : Fin N → Bool) : Finset (Fin N) := Finset.univ.filter (fun i => x i = true)

theorem bits_mono {N : ℕ} {S T : Finset (Fin N)} (h : S ⊆ T) :
    ∀ i, bits S i = true → bits T i = true := by
  intro i hi
  exact decide_eq_true (h (of_decide_eq_true hi))

theorem inside_bits {N : ℕ} (x : Fin N → Bool) {S : Finset (Fin N)} {i : Fin N} (hi : i ∈ S) :
    bits (on x ∩ S) i = x i := by
  cases e : x i <;> simp [bits, on, hi, e]

theorem outside_bits {N : ℕ} (x : Fin N → Bool) {S : Finset (Fin N)} {i : Fin N} (hi : i ∉ S) :
    bits (on x \ S) i = x i := by
  cases e : x i <;> simp [bits, on, hi, e]

theorem enough_inputs {N : ℕ} (D : Circuit) (hp : 0 < D.size)
    (hshape : ∀ g ∈ D.gates, GateShape g) (hback : ReadsBack N D) : 0 < N := by
  have hmem : gateAt D 0 ∈ D.gates := by
    rw [gateAt, List.getD_eq_getElem _ _ hp]
    exact List.getElem_mem hp
  have h := hshape _ hmem
  cases e : (gateAt D 0).inputs with
  | nil =>
    rcases h with ⟨_, hh⟩ | ⟨_, hh⟩ <;> simp [e] at hh
  | cons i is =>
    have hi := hback 0 hp i (by simp [e])
    omega

end PEqualNP.Outside.L_meta_24159_aux

open PEqualNP.Outside.L_meta_24159_aux PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover in


theorem PEqualNP.Outside.L_meta_24159 : ∀ (N : ℕ) (D : PEqualNP.CircuitLowerBounds.Circuit), (∀ g ∈ D.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) → PEqualNP.MetaComplexity.NestedCover.ReadsBack N D → 0 < D.size → D.output + 1 = N + D.size → (∃ j0 < D.size, ∀ j < D.size, (D.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩).op = PEqualNP.CircuitLowerBounds.GateOp.not ↔ j = j0) → (∀ i < N, PEqualNP.MetaComplexity.NestedCover.readsIn D (Finset.range D.size) i ≤ 1) → (∀ j < D.size, PEqualNP.MetaComplexity.NestedCover.readsIn D (Finset.range D.size) (N + j) = if j + 1 = D.size then 0 else 1) → ∃ (Nset : Finset (Fin N)) (H α β : Finset (Fin N) → Bool), Nset.Nonempty ∧ H ∅ = false ∧ (∀ S T : Finset (Fin N), S ⊆ T → H S = true → H T = true) ∧ (∀ S T : Finset (Fin N), S ⊆ T → α S = true → α T = true) ∧ (∀ S T : Finset (Fin N), S ⊆ T → β S = true → β T = true) ∧ (∀ S : Finset (Fin N), β S = true → α S = true) ∧ (∀ x : Fin N → Bool, D.eval (List.ofFn x) = (β ((Finset.univ.filter (fun i : Fin N => x i = true)) \ Nset) || (!H ((Finset.univ.filter (fun i : Fin N => x i = true)) ∩ Nset) && α ((Finset.univ.filter (fun i : Fin N => x i = true)) \ Nset)))) ∧ (∃ FH : PEqualNP.CircuitLowerBounds.Circuit, ((∀ g ∈ FH.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack N FH ∧ (FH.output + 1 = N + FH.size ∨ (FH.size = 0 ∧ FH.output < N)) ∧ (∀ i < N, PEqualNP.MetaComplexity.NestedCover.readsIn FH (Finset.range FH.size) i ≤ 1) ∧ (∀ j < FH.size, PEqualNP.MetaComplexity.NestedCover.readsIn FH (Finset.range FH.size) (N + j) = if j + 1 = FH.size then 0 else 1)) ∧ (∀ i : Fin N, PEqualNP.MetaComplexity.NestedCover.readsIn FH (Finset.range FH.size) i.val = 1 → i ∈ Nset) ∧ ∀ S : Finset (Fin N), H S = FH.eval (List.ofFn fun k : Fin N => decide (k ∈ S))) ∧ ((∃ c : Bool, ∀ S : Finset (Fin N), α S = c) ∨ ∃ Fα : PEqualNP.CircuitLowerBounds.Circuit, ((∀ g ∈ Fα.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack N Fα ∧ (Fα.output + 1 = N + Fα.size ∨ (Fα.size = 0 ∧ Fα.output < N)) ∧ (∀ i < N, PEqualNP.MetaComplexity.NestedCover.readsIn Fα (Finset.range Fα.size) i ≤ 1) ∧ (∀ j < Fα.size, PEqualNP.MetaComplexity.NestedCover.readsIn Fα (Finset.range Fα.size) (N + j) = if j + 1 = Fα.size then 0 else 1)) ∧ (∀ i : Fin N, PEqualNP.MetaComplexity.NestedCover.readsIn Fα (Finset.range Fα.size) i.val = 1 → i ∉ Nset) ∧ ∀ S : Finset (Fin N), α S = Fα.eval (List.ofFn fun k : Fin N => decide (k ∈ S))) := by
  intro N D hshape hback hp hlast hnot hinput hgate
  obtain ⟨j0, hj0, hNot⟩ := hnot
  have hnot' (k : ℕ) (hk : k < D.size) : (gateAt D k).op = .not ↔ k = j0 := by
    have e := hNot k hk
    rw [List.getD_eq_getElem _ _ hk] at e
    rw [gateAt, List.getD_eq_getElem _ _ hk]
    exact e
  have hb (i : ℕ) (hi : i < N + D.gates.length) :
      readsIn D (Finset.range D.size) i ≤ 1 := by
    by_cases he : i < N
    · exact hinput i he
    · let j := i - N
      have hj : j < D.size := by change j < D.gates.length; dsimp [j]; omega
      have eq : N + j = i := by dsimp [j]; omega
      rw [← eq, hgate j hj]
      split_ifs <;> omega
  obtain ⟨label, L⟩ :=
    label_invariant N D j0 ⟨0, enough_inputs D hp hshape hback⟩ hshape hback hnot' hb D.size le_rfl
  obtain ⟨i, hi, mark⟩ := L.existsMarked hj0
  have hge := (L.after i hi mark).2
  let j := i - N
  have hlt : j < D.size := by have h := hi.1; dsimp [j]; omega
  have hw : N + j = i := by dsimp [j]; omega
  have hz := hi.2
  rw [← hw, hgate j hlt] at hz
  have hLastJ : j + 1 = D.size := by
    by_contra e
    simp [e] at hz
  have hout : D.output = i := by omega
  have heval := L.eval i hi
  have hlin := L.linear i hi
  cases hl : label i with
  | plain f =>
    rw [hl] at mark
    exact mark.elim
  | marked F c =>
    rw [hl] at heval hlin
    obtain ⟨hF, hC, hd⟩ := hlin
    let Nset := support F
    let H := fun S => evalF (bits S) F
    let α := fun S => evalCtx (bits S) true c
    let β := fun S => evalCtx (bits S) false c
    refine ⟨Nset, H, α, β, support_nonempty F, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have e : bits (∅ : Finset (Fin N)) = fun _ => false := by
        funext i
        simp [bits]
      change evalF (bits ∅) F = false
      rw [e, evalF_empty]
    · intro S T hs h
      exact evalF_mono F (bits_mono hs) h
    · intro S T hs h
      exact evalCtx_mono c (bits_mono hs) (fun e => e) h
    · intro S T hs h
      exact evalCtx_mono c (bits_mono hs) (fun e => e) h
    · intro S h
      exact evalCtx_mono c (fun _ e => e) (by simp) h
    · intro x
      have hx := heval x
      rw [← hout] at hx
      change evalCtx x (!evalF x F) c = D.eval (List.ofFn x) at hx
      have h1 : evalF x F = H (on x ∩ Nset) :=
        evalF_local F x _ (fun i hi => (inside_bits x hi).symm)
      have h2 (b : Bool) : evalCtx x b c = evalCtx (bits (on x \ Nset)) b c :=
        evalCtx_local c x _ b (fun i hi => (outside_bits x (fun hm =>
          (Finset.disjoint_left.mp hd) hm hi)).symm)
      calc
        D.eval (List.ofFn x) = evalCtx x (!evalF x F) c := hx.symm
        _ = evalCtx (bits (on x \ Nset)) (!H (on x ∩ Nset)) c := by rw [h1, h2]
        _ = (β (on x \ Nset) || (!H (on x ∩ Nset) && α (on x \ Nset))) := interp c _ _
    · obtain ⟨FH, hh, hus, hval⟩ := post_spec F hF
      refine ⟨FH, hh, hus, ?_⟩
      intro S
      exact (hval (bits S)).symm
    · have hpart := replace_linear true c hC
      cases e : replaceHole true c with
      | inl b =>
        left
        refine ⟨b, ?_⟩
        intro S
        change evalCtx (bits S) true c = b
        rw [← replace_eval true c, e]
        rfl
      | inr g =>
        right
        rw [e] at hpart
        obtain ⟨FA, ha, hus, heq⟩ := post_spec g hpart.1
        refine ⟨FA, ha, ?_, ?_⟩
        · intro i hi hn
          exact (Finset.disjoint_left.mp hd) hn (hpart.2 (hus i hi))
        · intro S
          change evalCtx (bits S) true c = FA.eval (List.ofFn (bits S))
          rw [← replace_eval true c, e]
          exact (heq (bits S)).symm


import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23964_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

variable {α : Type} [DecidableEq α]

def bits (s : Finset α) (i : α) : Bool := decide (i ∈ s)

def Local (s : Finset α) (f : (α → Bool) → Bool) : Prop :=
  ∀ x y, (∀ i ∈ s, x i = y i) → f x = f y

def hits (f : (α → Bool) → Bool) (a : α) : Prop := f (bits {a}) = true

def edge (f : (α → Bool) → Bool) (a b : α) : Prop := f (bits {a, b}) = true

def Rectangles (f : (α → Bool) → Bool) : Prop :=
  (∀ a, f (bits {a}) = false) →
    ∀ a b c d, edge f a b → edge f c b → edge f c d → edge f a d

def Spec (s : Finset α) (f : (α → Bool) → Bool) : Prop :=
  s.Nonempty ∧ Local s f ∧ f (bits ∅) = false ∧ f (fun _ => true) = true ∧ Rectangles f

def Two (s : Finset α) (f : (α → Bool) → Bool) : Prop :=
  ∀ a b, a ≠ b → s = {a, b} →
    (∀ x, f x = (x a && x b)) ∨ (∀ x, f x = (x a || x b))

theorem pair_without {s : Finset α} {f : (α → Bool) → Bool} (hf : Local s f) {a b : α}
    (ha : a ∉ s) : f (bits {a, b}) = f (bits {b}) := by
  apply hf
  intro i hi
  have hia : i ≠ a := fun h => ha (h ▸ hi)
  simp [bits, hia]

theorem single_without {s : Finset α} {f : (α → Bool) → Bool} (hf : Local s f) {a : α}
    (ha : a ∉ s) : f (bits {a}) = f (bits ∅) := by
  apply hf
  intro i hi
  have hia : i ≠ a := fun h => ha (h ▸ hi)
  simp [bits, hia]

theorem hit_in {s : Finset α} {f : (α → Bool) → Bool} (hf : Local s f)
    (hzero : f (bits ∅) = false) {a : α} (ha : hits f a) : a ∈ s := by
  by_contra h
  change f (bits {a}) = true at ha
  rw [single_without hf h, hzero] at ha
  contradiction

theorem edge_comm {f : (α → Bool) → Bool} {a b : α} : edge f a b ↔ edge f b a := by
  simp only [edge, Finset.pair_comm a b]

theorem edge_inside {s : Finset α} {f : (α → Bool) → Bool} (hf : Local s f)
    (hs : ∀ a, f (bits {a}) = false) {a b : α} (hab : edge f a b) : a ∈ s ∧ b ∈ s := by
  have left {i j : α} (h : edge f i j) : i ∈ s := by
    by_contra hi
    change f (bits {i, j}) = true at h
    rw [pair_without hf hi, hs] at h
    contradiction
  exact ⟨left hab, left (edge_comm.mp hab)⟩

theorem or_rectangles {s t : Finset α} {f g : (α → Bool) → Bool}
    (hdis : Disjoint s t) (hf : Local s f) (hg : Local t g)
    (rf : Rectangles f) (rg : Rectangles g) : Rectangles (fun x => f x || g x) := by
  intro hs a b c d hab hcb hcd
  have sf (i : α) : f (bits {i}) = false := (Bool.or_eq_false_iff.mp (hs i)).1
  have sg (i : α) : g (bits {i}) = false := (Bool.or_eq_false_iff.mp (hs i)).2
  have hnot {i : α} (hi : i ∈ s) (hj : i ∈ t) : False := Finset.disjoint_left.mp hdis hi hj
  change (f (bits {a, b}) || g (bits {a, b})) = true at hab
  change (f (bits {c, b}) || g (bits {c, b})) = true at hcb
  change (f (bits {c, d}) || g (bits {c, d})) = true at hcd
  have hresult : edge f a d ∨ edge g a d := by
    rcases Bool.or_eq_true_iff.mp hab with hab | hab
    · have hb := (edge_inside hf sf hab).2
      have hcb' : edge f c b := (Bool.or_eq_true_iff.mp hcb).resolve_right
        (fun hc => hnot hb (edge_inside hg sg hc).2)
      have hc := (edge_inside hf sf hcb').1
      have hcd' : edge f c d := (Bool.or_eq_true_iff.mp hcd).resolve_right
        (fun hd => hnot hc (edge_inside hg sg hd).1)
      exact Or.inl (rf sf a b c d hab hcb' hcd')
    · have hb := (edge_inside hg sg hab).2
      have hcb' : edge g c b := (Bool.or_eq_true_iff.mp hcb).resolve_left
        (fun hc => hnot (edge_inside hf sf hc).2 hb)
      have hc := (edge_inside hg sg hcb').1
      have hcd' : edge g c d := (Bool.or_eq_true_iff.mp hcd).resolve_left
        (fun hd => hnot (edge_inside hf sf hd).1 hc)
      exact Or.inr (rg sg a b c d hab hcb' hcd')
  exact Bool.or_eq_true_iff.mpr hresult

theorem and_edge {s t : Finset α} {f g : (α → Bool) → Bool}
    (hdis : Disjoint s t) (hf : Local s f) (hg : Local t g)
    (zf : f (bits ∅) = false) (zg : g (bits ∅) = false) (a b : α) :
    edge (fun x => f x && g x) a b ↔
      (hits f a ∧ hits g b) ∨ (hits f b ∧ hits g a) := by
  have dis {i : α} (hs : i ∈ s) (ht : i ∈ t) : False := Finset.disjoint_left.mp hdis hs ht
  have lands {r : Finset α} {h : (α → Bool) → Bool} (hl : Local r h)
      (hz : h (bits ∅) = false) {i j : α} (hij : edge h i j) : i ∈ r ∨ j ∈ r := by
    by_contra hn
    change h (bits {i, j}) = true at hij
    rw [pair_without hl (fun hi => hn (Or.inl hi)),
      single_without hl (fun hj => hn (Or.inr hj)), hz] at hij
    contradiction
  have align {i j : α} (hi : i ∈ s) (hj : j ∈ t) :
      (edge f i j ∧ edge g i j) ↔ hits f i ∧ hits g j := by
    have e₁ : f (bits {i, j}) = f (bits {i}) := by
      rw [Finset.pair_comm i j, pair_without hf (fun hs => dis hs hj)]
    have e₂ : g (bits {i, j}) = g (bits {j}) := pair_without hg (fun ht => dis hi ht)
    unfold edge hits
    rw [e₁, e₂]
  change (f (bits {a, b}) && g (bits {a, b})) = true ↔ _
  rw [Bool.and_eq_true]
  constructor
  · intro h
    rcases lands hf zf h.1 with ha | hb
    · have hb' := (lands hg zg h.2).resolve_left (fun ha' => dis ha ha')
      exact Or.inl ((align ha hb').mp h)
    · have ha' := (lands hg zg h.2).resolve_right (fun hb' => dis hb hb')
      exact Or.inr ((align hb ha').mp ⟨edge_comm.mp h.1, edge_comm.mp h.2⟩)
  · rintro (h | h)
    · exact (align (hit_in hf zf h.1) (hit_in hg zg h.2)).mpr h
    · have hh := (align (hit_in hf zf h.1) (hit_in hg zg h.2)).mpr h
      exact ⟨edge_comm.mp hh.1, edge_comm.mp hh.2⟩

theorem and_rectangles {s t : Finset α} {f g : (α → Bool) → Bool}
    (hdis : Disjoint s t) (hf : Local s f) (hg : Local t g)
    (zf : f (bits ∅) = false) (zg : g (bits ∅) = false) :
    Rectangles (fun x => f x && g x) := by
  intro _ a b c d hab hcb hcd
  have ha (i j : α) := and_edge hdis hf hg zf zg i j
  have hn {i : α} (h₁ : hits f i) (h₂ : hits g i) : False :=
    Finset.disjoint_left.mp hdis (hit_in hf zf h₁) (hit_in hg zg h₂)
  apply (ha a d).mpr
  rcases (ha a b).mp hab with hab | hab
  · have hcb := ((ha c b).mp hcb).resolve_right (fun h => hn h.1 hab.2)
    have hcd := ((ha c d).mp hcd).resolve_right (fun h => hn hcb.1 h.2)
    exact Or.inl ⟨hab.1, hcd.2⟩
  · have hcb := ((ha c b).mp hcb).resolve_left (fun h => hn hab.1 h.2)
    have hcd := ((ha c d).mp hcd).resolve_left (fun h => hn h.1 hcb.2)
    exact Or.inr ⟨hcd.1, hab.2⟩

def connect (isAnd : Bool) (f g : (α → Bool) → Bool) (x : α → Bool) : Bool :=
  if isAnd then f x && g x else f x || g x

theorem combined_spec {s t : Finset α} {f g : (α → Bool) → Bool}
    (isAnd : Bool) (hdis : Disjoint s t) (hf : Spec s f) (hg : Spec t g) :
    Spec (s ∪ t) (connect isAnd f g) := by
  rcases hf with ⟨⟨a, ha⟩, lf, zf, onesF, rf⟩
  rcases hg with ⟨_, lg, zg, onesG, rg⟩
  refine ⟨⟨a, Finset.mem_union_left _ ha⟩, ?_, ?_, ?_, ?_⟩
  · intro x y h
    simp only [connect, lf x y (fun i hi => h i (Finset.mem_union_left _ hi)),
      lg x y (fun i hi => h i (Finset.mem_union_right _ hi))]
  · cases isAnd <;> simp [connect, zf, zg]
  · cases isAnd <;> simp [connect, onesF, onesG]
  · cases isAnd with
    | false => exact or_rectangles hdis lf lg rf rg
    | true => exact and_rectangles hdis lf lg zf zg

theorem singleton_eval (a : α) {f : (α → Bool) → Bool} (hf : Spec {a} f) (x : α → Bool) :
    f x = x a := by
  cases hx : x a with
  | false =>
    rw [← hf.2.2.1]
    apply hf.2.1
    intro i hi
    obtain rfl := Finset.mem_singleton.mp hi
    simp [bits, hx]
  | true =>
    rw [← hf.2.2.2.1]
    apply hf.2.1
    intro i hi
    obtain rfl := Finset.mem_singleton.mp hi
    exact hx

theorem split_pair {s t : Finset α} {a b : α} (hs : s.Nonempty) (ht : t.Nonempty)
    (hd : Disjoint s t) (he : s ∪ t = {a, b}) :
    (s = {a} ∧ t = {b}) ∨ (s = {b} ∧ t = {a}) := by
  have dis {i : α} (hi : i ∈ s) (hj : i ∈ t) : False := Finset.disjoint_left.mp hd hi hj
  have orient {c d : α} (hc : c ∈ s) (he : s ∪ t = {c, d}) : s = {c} ∧ t = {d} := by
    have ls {i : α} (hi : i ∈ s) : i = c ∨ i = d := by
      have hmem : i ∈ ({c, d} : Finset α) := he ▸ Finset.mem_union_left t hi
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem
    have lt {i : α} (hi : i ∈ t) : i = c ∨ i = d := by
      have hmem : i ∈ ({c, d} : Finset α) := he ▸ Finset.mem_union_right s hi
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem
    obtain ⟨j, hj⟩ := ht
    have ej := (lt hj).resolve_left (fun h => dis hc (h ▸ hj))
    have hdt : d ∈ t := ej ▸ hj
    constructor
    · ext i
      simp only [Finset.mem_singleton]
      exact ⟨fun hi => (ls hi).resolve_right (fun h => dis (h ▸ hi) hdt), fun h => h.symm ▸ hc⟩
    · ext i
      simp only [Finset.mem_singleton]
      exact ⟨fun hi => (lt hi).resolve_left (fun h => dis hc (h ▸ hi)), fun h => h.symm ▸ hdt⟩
  obtain ⟨i, hi⟩ := hs
  have hmem : i ∈ ({a, b} : Finset α) := he ▸ Finset.mem_union_left t hi
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with ha | hb
  · exact Or.inl (orient (ha ▸ hi) he)
  · exact Or.inr (orient (hb ▸ hi) (he.trans (Finset.pair_comm a b)))

theorem combined_two {s t : Finset α} {f g : (α → Bool) → Bool}
    (isAnd : Bool) (hd : Disjoint s t) (hf : Spec s f) (hg : Spec t g) :
    Two (s ∪ t) (connect isAnd f g) := by
  intro a b _ he
  rcases split_pair hf.1 hg.1 hd he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · cases isAnd with
    | false => exact Or.inr fun x => by simp [connect, singleton_eval a hf, singleton_eval b hg]
    | true => exact Or.inl fun x => by simp [connect, singleton_eval a hf, singleton_eval b hg]
  · cases isAnd with
    | false =>
      refine Or.inr fun x => ?_
      simp [connect, singleton_eval b hf, singleton_eval a hg, Bool.or_comm]
    | true =>
      refine Or.inl fun x => ?_
      simp [connect, singleton_eval b hf, singleton_eval a hg, Bool.and_comm]

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

theorem wire_gate {N : ℕ} (C : Circuit) (hback : ReadsBack N C) (j a b : ℕ)
    (hj : j < C.gates.length) (hins : (gateAt C j).inputs = [a, b])
    (hop : (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) :
    ∃ isAnd, wire N C (N + j) = connect isAnd (wire N C a) (wire N C b) := by
  have ha := hback j hj a (by simp [hins])
  have hb := hback j hj b (by simp [hins])
  have hat : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
  have ev (x : Fin N → Bool) :
      wire N C (N + j) x =
        (gateAt C j).op.eval [wire N C a x, wire N C b x] := by
    have he := wireAt C (List.ofFn x) j hj
    rw [List.length_ofFn, ← hat, hins] at he
    simpa only [wire, List.map_cons, List.map_nil, ite_eq_left ha, ite_eq_left hb] using he
  rcases hop with h | h
  · refine ⟨true, funext fun x => ?_⟩
    rw [ev, h]
    simp [GateOp.eval, connect]
  · refine ⟨false, funext fun x => ?_⟩
    rw [ev, h]
    simp [GateOp.eval, connect]

theorem variable_spec (a : α) : Spec {a} (fun x => x a) := by
  refine ⟨⟨a, by simp⟩, fun x y h => h a (by simp), by simp [bits], rfl, ?_⟩
  intro h
  have hh := h a
  simp [bits] at hh

theorem read_mono (C : Circuit) {p q : ℕ} (hpq : p ≤ q) (i : ℕ) :
    readsIn C (Finset.range p) i ≤ readsIn C (Finset.range q) i := by
  unfold readsIn
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hpq) (fun _ _ _ => Nat.zero_le _)

theorem read_positive (C : Circuit) {i j : ℕ} (hj : j < C.gates.length)
    (hi : i ∈ (gateAt C j).inputs) : 0 < readsIn C (Finset.range C.gates.length) i := by
  have hle : (gateAt C j).inputs.count i ≤ readsIn C (Finset.range C.gates.length) i :=
    Finset.single_le_sum (f := fun k => (gateAt C k).inputs.count i)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hj)
  exact (List.count_pos_iff.mpr hi).trans_le hle

def Live (N : ℕ) (C : Circuit) (k i : ℕ) : Prop :=
  i < N + k ∧ readsIn C (Finset.range k) i = 0

def WireSpec (N : ℕ) (C : Circuit) (i : ℕ) (s : Finset (Fin N)) : Prop :=
  Spec s (wire N C i) ∧ Two s (wire N C i) ∧
    (∀ a ∈ s, a.val = i ∨ 0 < readsIn C (Finset.range C.gates.length) a.val) ∧
    (N ≤ i → 2 ≤ s.card)

theorem label_invariant (N : ℕ) (C : Circuit)
    (hgate : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hback : ReadsBack N C)
    (hbound : ∀ i < N + C.gates.length, readsIn C (Finset.range C.gates.length) i ≤ 1) :
    ∀ k ≤ C.gates.length, ∃ label : ℕ → Finset (Fin N),
      (∀ i, Live N C k i → WireSpec N C i (label i)) ∧
      (∀ i j, Live N C k i → Live N C k j → i ≠ j → Disjoint (label i) (label j)) := by
  intro k
  induction k with
  | zero =>
    intro _
    let label (i : ℕ) : Finset (Fin N) := if h : i < N then {⟨i, h⟩} else ∅
    have singleton (i : ℕ) (hi : Live N C 0 i) :
        label i = {⟨i, by simpa using hi.1⟩} := by
      have h : i < N := by simpa using hi.1
      simp [label, h]
    refine ⟨label, ?_, ?_⟩
    · intro i hi
      have hi' : i < N := by simpa using hi.1
      rw [singleton i hi]
      unfold WireSpec
      rw [wire_input N C i hi']
      refine ⟨variable_spec _, ?_, ?_, by omega⟩
      · intro a b hab h
        have e := congrArg Finset.card h
        rw [Finset.card_singleton, Finset.card_pair_eq_two_iff.mpr hab] at e
        omega
      · intro a ha
        exact Or.inl (congrArg Fin.val (Finset.mem_singleton.mp ha))
    · intro i j hi hj hij
      rw [singleton i hi, singleton j hj]
      apply Finset.disjoint_left.mpr
      intro a ha hb
      exact hij (congrArg Fin.val ((Finset.mem_singleton.mp ha).symm.trans (Finset.mem_singleton.mp hb)))
  | succ k ih =>
    intro hk
    obtain ⟨label, hlabel, hd⟩ := ih (by omega)
    have hg : k < C.gates.length := by omega
    have hat : gateAt C k = C.gates[k] := List.getD_eq_getElem _ _ hg
    have good := hgate (gateAt C k) (by rw [hat]; exact List.getElem_mem _)
    obtain ⟨a, b, hin⟩ := List.length_eq_two.mp good.2
    have count_step (i : ℕ) : readsIn C (Finset.range (k + 1)) i =
        readsIn C (Finset.range k) i + ([a, b] : List ℕ).count i := by
      rw [readsIn, Finset.sum_range_succ]
      change readsIn C (Finset.range k) i + (gateAt C k).inputs.count i = _
      rw [hin]
    have aEarlier := hback k hg a (by simp [hin])
    have bEarlier := hback k hg b (by simp [hin])
    have readBound (i : ℕ) (hi : i < N + k) :
        readsIn C (Finset.range (k + 1)) i ≤ 1 :=
      (read_mono C hk i).trans (hbound i (by omega))
    have ac := readBound a aEarlier
    have bc := readBound b bEarlier
    rw [count_step] at ac bc
    have ap : 0 < ([a, b] : List ℕ).count a := List.count_pos_iff.mpr (by simp)
    have bp : 0 < ([a, b] : List ℕ).count b := List.count_pos_iff.mpr (by simp)
    have ha : Live N C k a := ⟨aEarlier, by omega⟩
    have hb : Live N C k b := ⟨bEarlier, by omega⟩
    have hab : a ≠ b := by
      intro h
      subst b
      simp at ac
    have hdis := hd a b ha hb hab
    obtain ⟨isAnd, hwire⟩ := wire_gate C hback k a b hg hin good.1
    have vertex (i : ℕ) (hi : Live N C (k + 1) i) :
        i ≠ a ∧ i ≠ b := by
      have hcount := hi.2
      rw [count_step] at hcount
      constructor
      · intro h; subst i; omega
      · intro h; subst i; omega
    have earlier (i : ℕ) (hi : Live N C (k + 1) i) (he : i ≠ N + k) :
        Live N C k i := by
      obtain ⟨hl, hr⟩ := hi
      rw [count_step] at hr
      exact ⟨by omega, by omega⟩
    let next (i : ℕ) := if i = N + k then label a ∪ label b else label i
    have root : WireSpec N C (N + k) (label a ∪ label b) := by
      unfold WireSpec
      rw [hwire]
      have sa := (hlabel a ha).1
      have sb := (hlabel b hb).1
      refine ⟨combined_spec isAnd hdis sa sb, combined_two isAnd hdis sa sb, ?_, ?_⟩
      · intro i hi
        apply Or.inr
        rcases Finset.mem_union.mp hi with hi | hi
        · rcases (hlabel a ha).2.2.1 i hi with h | h
          · exact read_positive C hg (by simp [hin, h])
          · exact h
        · rcases (hlabel b hb).2.2.1 i hi with h | h
          · exact read_positive C hg (by simp [hin, h])
          · exact h
      · intro _
        rw [Finset.card_union_of_disjoint hdis]
        have hs := Finset.card_pos.mpr sa.1
        have ht := Finset.card_pos.mpr sb.1
        omega
    refine ⟨next, ?_, ?_⟩
    · intro i hi
      by_cases he : i = N + k
      · subst i
        simpa [next] using root
      · simpa [next, he] using hlabel i (earlier i hi he)
    · intro i j hi hj hij
      have join_disjoint (p : ℕ) (hp : Live N C (k + 1) p) (he : p ≠ N + k) :
          Disjoint (label a ∪ label b) (label p) :=
        Finset.disjoint_union_left.mpr
          ⟨hd a p ha (earlier p hp he) (vertex p hp).1.symm,
            hd b p hb (earlier p hp he) (vertex p hp).2.symm⟩
      by_cases hi' : i = N + k
      · subst i
        simpa [next, hij.symm] using join_disjoint j hj hij.symm
      · by_cases hj' : j = N + k
        · subst j
          simpa [next, hi'] using (join_disjoint i hi hi').symm
        · simpa [next, hi', hj'] using hd i j (earlier i hi hi') (earlier j hj hj') hij

end PEqualNP.Outside.L_meta_23964_aux

open PEqualNP.Outside.L_meta_23964_aux PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover in
theorem PEqualNP.Outside.L_meta_23964 : ∀ (N : ℕ) (F : PEqualNP.CircuitLowerBounds.Circuit), ((∀ g ∈ F.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack N F ∧ (F.output + 1 = N + F.size ∨ (F.size = 0 ∧ F.output < N)) ∧ (∀ i < N, PEqualNP.MetaComplexity.NestedCover.readsIn F (Finset.range F.size) i ≤ 1) ∧ (∀ j < F.size, PEqualNP.MetaComplexity.NestedCover.readsIn F (Finset.range F.size) (N + j) = if j + 1 = F.size then 0 else 1)) → ((F.eval (List.ofFn fun k : Fin N => decide (k ∈ (∅ : Finset (Fin N)))) = false → (∀ a : Fin N, F.eval (List.ofFn fun k : Fin N => decide (k ∈ ({a} : Finset (Fin N)))) = false) → ∀ a b c d : Fin N, F.eval (List.ofFn fun k : Fin N => decide (k ∈ ({a, b} : Finset (Fin N)))) = true → F.eval (List.ofFn fun k : Fin N => decide (k ∈ ({c, b} : Finset (Fin N)))) = true → F.eval (List.ofFn fun k : Fin N => decide (k ∈ ({c, d} : Finset (Fin N)))) = true → F.eval (List.ofFn fun k : Fin N => decide (k ∈ ({a, d} : Finset (Fin N)))) = true) ∧ (∀ a b : Fin N, a ≠ b → (∀ i : Fin N, PEqualNP.MetaComplexity.NestedCover.readsIn F (Finset.range F.size) i.val = 1 ↔ (i = a ∨ i = b)) → (∀ x : Fin N → Bool, F.eval (List.ofFn x) = (x a && x b)) ∨ (∀ x : Fin N → Bool, F.eval (List.ofFn x) = (x a || x b)))) := by
  rintro N C ⟨hshape, hback, hout, hinput, hgate⟩
  change C.output + 1 = N + C.gates.length ∨ (C.gates.length = 0 ∧ C.output < N) at hout
  change ∀ i < N, readsIn C (Finset.range C.gates.length) i ≤ 1 at hinput
  change ∀ j < C.gates.length, readsIn C (Finset.range C.gates.length) (N + j) =
    if j + 1 = C.gates.length then 0 else 1 at hgate
  have hbound (i : ℕ) (hi : i < N + C.gates.length) :
      readsIn C (Finset.range C.gates.length) i ≤ 1 := by
    by_cases h : i < N
    · exact hinput i h
    · let j := i - N
      have hj : j < C.gates.length := by dsimp [j]; omega
      have he : N + j = i := by dsimp [j]; omega
      rw [← he, hgate j hj]
      split_ifs <;> omega
  have hlive : Live N C C.gates.length C.output := by
    rcases hout with h | ⟨hnil, h⟩
    · refine ⟨by omega, ?_⟩
      by_cases hnil : C.gates.length = 0
      · simp [readsIn, hnil]
      · let j := C.gates.length - 1
        have hj : j < C.gates.length := by dsimp [j]; omega
        have he : N + j = C.output := by dsimp [j]; omega
        have hlast : j + 1 = C.gates.length := by dsimp [j]; omega
        rw [← he, hgate j hj, ite_eq_left hlast]
    · exact ⟨by omega, by simp [readsIn, hnil]⟩
  obtain ⟨label, hlabel, _⟩ := label_invariant N C hshape hback hbound C.gates.length le_rfl
  obtain ⟨hspec, htwo, hused, hcard⟩ := hlabel C.output hlive
  constructor
  · intro _ hs a b c d hab hcb hcd
    exact hspec.2.2.2.2 hs a b c d hab hcb hcd
  · intro a b hab hreads
    have hnonempty : C.gates.length ≠ 0 := by
      intro h
      have hh := (hreads a).2 (Or.inl rfl)
      simp [Circuit.size, readsIn, h] at hh
    have hroot : N ≤ C.output := by rcases hout with h | ⟨h, _⟩ <;> omega
    have hsub : label C.output ⊆ {a, b} := by
      intro i hi
      rcases hused i hi with h | h
      · have := i.isLt
        omega
      · have hle := hinput i.val i.isLt
        have he : readsIn C (Finset.range C.size) i.val = 1 := by
          change readsIn C (Finset.range C.gates.length) i.val = 1
          omega
        simpa only [Finset.mem_insert, Finset.mem_singleton] using (hreads i).1 he
    have hlabel' : label C.output = {a, b} := Finset.eq_of_subset_of_card_le hsub (by
      rw [Finset.card_pair_eq_two_iff.mpr hab]
      exact hcard hroot)
    exact htwo a b hab hlabel'

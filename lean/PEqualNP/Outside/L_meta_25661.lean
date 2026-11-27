import PEqualNP.Defs
import PEqualNP.Outside.L_meta_6339

namespace PEqualNP.Outside.L_meta_25661_aux.Transfer.Restriction

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_start (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_start gs w
  rw [ht]; simp [hl]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

abbrev Stat : Type := Bool ⊕ ℕ

def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | _ => (none, Sum.inl false)

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or) (hlen : ins.length ≤ 2)
    (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_start r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Sum.inl false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Sum.inl false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

theorem elim_count (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, Ok g) → k < acc.1.length → (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
    (elim n gs acc).2.length + gs.countP (fun g => decide (k ∈ g.inputs))
      ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _; simp [elim]
  | cons g gs ih =>
    intro acc hok hk hc
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (by simp [elimStep]; omega)
      (by
        obtain ⟨c, hc⟩ := hc
        refine ⟨c, ?_⟩
        simp only [elimStep]
        rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
    rw [h3, List.length_cons, List.countP_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hnok.1
        · simpa using hnok.2
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
        rw [hnone]; simp
      simp only [hkg, decide_true, ite_true]
      omega
    · have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      simp only [hkg, decide_false, Bool.false_eq_true, ite_false]
      omega

theorem getD_ofFn' {α : Type} (m : ℕ) (f : Fin m → α) (d : α) (j : Fin m) :
    (List.ofFn f).getD j.val d = f j := by
  simp [List.getD_eq_getElem?_getD]

end PEqualNP.Outside.L_meta_25661_aux.Transfer.Restriction

namespace PEqualNP.Outside.L_meta_25661_aux.Transfer.WireEval

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt2 (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt2 gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt2 gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt2 _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

def OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

lemma opMono_eq : OpMono Eq := by
  intro op _ l f g h
  rw [List.map_congr_left h]

lemma opMono_imp : OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

lemma mono_ops {C : Circuit} (hM : Monotone2 C) :
    ∀ k < C.gates.length, (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or := by
  intro k hk
  exact (hM _ (gateAt_mem hk)).1

end PEqualNP.Outside.L_meta_25661_aux.Transfer.WireEval

namespace PEqualNP.Outside.L_meta_25661_aux.Transfer.DeleteInput

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

open PEqualNP.Outside.L_meta_25661_aux.Transfer.Restriction PEqualNP.Outside.L_meta_25661_aux.Transfer.WireEval

def pull {n m : ℕ} (source : Fin n → Option (Fin m)) (y : Fin m → Bool) (i : Fin n) : Bool :=
  ((source i).map y).getD false

def code {n m : ℕ} (source : Fin n → Option (Fin m)) (i : Fin n) : Stat :=
  match source i with
  | none => Sum.inl false
  | some j => Sum.inr j.val

theorem deleteInput {n m : ℕ} (C : Circuit) (mono : Monotone2 C) (source : Fin n → Option (Fin m))
    (p : Fin n) (removed : source p = none) (reader : ∃ g ∈ C.gates, p.val ∈ g.inputs)
    (rejects : ∃ y, circuitFun n C (pull source y) = false) :
    ∃ D : Circuit, Monotone2 D ∧ circuitFun m D = (fun y => circuitFun n C (pull source y)) ∧
      D.size < C.size := by
  let start : List Stat × List Gate := (List.ofFn (code source),[])
  let finish := elim m C.gates start
  have seed (y : Fin m → Bool) : Inv m (List.ofFn y) (List.ofFn (pull source y)) start := by
    refine ⟨by simp [start],?_⟩
    intro i
    by_cases inside : i < n
    · let t : Fin n := ⟨i,inside⟩
      change ((List.ofFn (code source)).getD t.val _).Valid (m+0) ∧
        ((List.ofFn (code source)).getD t.val _).val (List.ofFn y) = (List.ofFn (pull source y)).getD t.val _
      rw [getD_ofFn',getD_ofFn']
      cases h : source t with
      | none => simp [code,h,pull,Stat.Valid,Stat.val]
      | some u => simp [code,h,pull,Stat.Valid,Stat.val,u.isLt]
    · have a : start.1.getD i (Sum.inl false) = Sum.inl false :=
        List.getD_eq_default _ _ (by simp [start]; omega)
      have b : (List.ofFn (pull source y)).getD i false = false :=
        List.getD_eq_default _ _ (by simp; omega)
      rw [a,b]; exact ⟨trivial,rfl⟩
  have known : start.1.getD p.val (Sum.inl false) = Sum.inl false := by
    change (List.ofFn (code source)).getD p.val _ = _
    rw [getD_ofFn']; simp [code,removed]
  have limit := elim_count m p.val C.gates start mono (by simp [start]) ⟨false,known⟩
  have cost : finish.2.length + C.gates.countP (fun g => decide (p.val ∈ g.inputs)) ≤ C.size := by
    simpa [start,finish,Circuit.size] using limit
  obtain ⟨g,hg,read⟩ := reader
  have charge : 0 < C.gates.countP (fun h => decide (p.val ∈ h.inputs)) := by
    by_contra! zero
    exact (List.countP_eq_zero.mp (Nat.le_zero.mp zero) g hg) (decide_eq_true read)
  have short : finish.2.length < C.size := by omega
  let out := finish.1.getD C.output (Sum.inl false)
  have eval (y : Fin m → Bool) :
      out.val (wiresFrom finish.2 (List.ofFn y)) = circuitFun n C (pull source y) :=
    ((inv_elim m (List.ofFn y) (by simp) C.gates _ start mono (seed y)).2 C.output).2
  have legal : ∀ h ∈ finish.2, Ok h := elim_ok m C.gates start (by simp [start])
  cases result : out with
  | inr i =>
    refine ⟨⟨finish.2,i⟩,legal,?_,short⟩
    funext y
    have h := eval y
    rw [result] at h
    exact h
  | inl b =>
    have const (y : Fin m → Bool) : b = circuitFun n C (pull source y) := by
      have h := eval y
      rw [result] at h
      exact h
    obtain ⟨y,hy⟩ := rejects
    have off : b = false := (const y).trans hy
    refine ⟨⟨[],m⟩,by intro h mem; simp at mem,?_,by change 0 < C.size; omega⟩
    funext z
    change (List.ofFn z).getD m false = _
    rw [List.getD_eq_default _ _ (by simp)]
    exact off.symm.trans (const z)

theorem read_of_separation {n : ℕ} (C : Circuit) (mono : Monotone2 C) (p : Fin n)
    (out : C.output ≠ p.val) (x y : Fin n → Bool)
    (ordered : ∀ t, t ≠ p → x t = true → y t = true)
    (on : circuitFun n C x = true) (off : circuitFun n C y = false) :
    ∃ g ∈ C.gates, p.val ∈ g.inputs := by
  by_contra! unread
  have wires (w : ℕ) : w ≠ p.val → val C (List.ofFn x) w = true → val C (List.ofFn y) w = true := by
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro ne
      by_cases raw : w < n
      · let t : Fin n := ⟨w,raw⟩
        rw [val_input List.length_ofFn raw,val_input List.length_ofFn raw]
        simpa [t,raw] using ordered t (fun eq => ne (congrArg Fin.val eq))
      by_cases past : n+C.gates.length ≤ w
      · rw [val_ge List.length_ofFn past]; simp
      obtain ⟨k,rfl⟩ : ∃ k, w=n+k := ⟨w-n,by omega⟩
      have valid : k < C.gates.length := by omega
      rw [val_gate List.length_ofFn valid,val_gate List.length_ofFn valid]
      apply opMono_imp _ (mono_ops mono k valid)
      intro i hi
      by_cases earlier : i < n+k
      · simp only [earlier,ite_true]
        exact ih i earlier (fun eq => unread _ (gateAt_mem valid) (eq ▸ hi))
      · simp [earlier]
  have contradiction := wires C.output out on
  change circuitFun n C y = true at contradiction
  simp [off] at contradiction
end PEqualNP.Outside.L_meta_25661_aux.Transfer.DeleteInput

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

namespace PEqualNP.Outside.L_meta_25661_aux.Transfer

def mask {n m : ℕ} (t : ℕ) (u : Fin n) (v : Fin m) : Bool :=
  t.testBit (m * u.val + v.val)

def cell {n m : ℕ} (u : Fin n) (v : Fin m) (w : Fin (n + m)) : Bool :=
  (oneEach u v).getD w.val false

theorem cell_toList {n m : ℕ} (u : Fin n) (v : Fin m) :
    List.ofFn (cell u v) = oneEach u v := by
  apply List.ext_getElem
  · simp [oneEach]
  · intro i hi hj
    simp [cell, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

def dropWire {n m : ℕ} (p : ℕ) (i : Fin n) : Option (Fin m) :=
  let j := if i.val < p then i.val else i.val - 1
  if i.val = p then none else if h : j < m then some ⟨j, h⟩ else none

theorem smaller {n m n' m' : ℕ} (t t' : ℕ)
    (row : Fin n' → Fin n) (col : Fin m' → Fin m) (p : Fin (n + m))
    (a b c : Fin n × Fin m)
    (cert : mask t a.1 a.2 = true ∧ mask t b.1 b.2 = false ∧
      mask t c.1 c.2 = true ∧ cell c.1 c.2 p = false ∧
      (∀ i, i ≠ p → cell a.1 a.2 i = true → cell b.1 b.2 i = true) ∧
      (∀ u v, List.ofFn (DeleteInput.pull (dropWire (n := n+m) (m := n'+m') p.val) (cell u v)) =
        oneEach (row u) (col v)) ∧
      (∀ u v, mask t (row u) (col v) = mask t' u v) ∧
      (∃ (u : Fin n') (v : Fin m'), mask t' u v = false)) {k : ℕ} :
    RepSizeAtMost (@mask n m t) (k + 1) → RepSizeAtMost (@mask n' m' t') k := by
  rintro ⟨C, hm, hs, hr⟩
  obtain ⟨ha, hb, hc, cp, ordered, embed, table, u0, v0, off⟩ := cert
  have evalCell (u : Fin n) (v : Fin m) : circuitFun (n+m) C (cell u v) = mask t u v := by
    change C.eval (List.ofFn _) = _
    rw [cell_toList]
    exact hr u v
  have out : C.output ≠ p.val := by
    intro eq
    have h := (hr c.1 c.2).trans hc
    change WireEval.val C (oneEach c.1 c.2) C.output = true at h
    rw [eq, WireEval.val_input (n := n+m) (by simp [oneEach]) p.isLt] at h
    exact Bool.noConfusion (cp.symm.trans h)
  have reads := DeleteInput.read_of_separation C hm p out (cell a.1 a.2) (cell b.1 b.2)
    ordered ((evalCell _ _).trans ha) ((evalCell _ _).trans hb)
  let src := dropWire (n := n+m) (m := n'+m') p.val
  have compute (u : Fin n') (v : Fin m') :
      circuitFun (n+m) C (DeleteInput.pull src (cell u v)) = mask t' u v := by
    change C.eval (List.ofFn (DeleteInput.pull _ _)) = _
    rw [embed u v]
    exact (hr _ _).trans (table u v)
  obtain ⟨D, legal, eqv, size⟩ := DeleteInput.deleteInput C hm src p
    (by simp [src, dropWire]) reads ⟨cell u0 v0, (compute u0 v0).trans off⟩
  refine ⟨D, legal, by omega, ?_⟩
  intro u v
  rw [← cell_toList u v]
  change circuitFun (n'+m') D (cell u v) = _
  rw [eqv]
  exact compute u v

def skipFourth (i : Fin 4) : Fin 5 := if i.val < 3 then i.castSucc else 4

theorem dropLast :
    PEqualNP.Represents.RepSizeAtMost (@mask 4 6 271347) 11 →
    PEqualNP.Represents.RepSizeAtMost (@mask 4 5 35315) 10 := by
  exact smaller 271347 35315 (id : Fin 4 → Fin 4) (Fin.castSucc : Fin 5 → Fin 6)
    9 (0,5) (0,2) (0,0) (by decide +kernel)

theorem dropFourth :
    PEqualNP.Represents.RepSizeAtMost (@mask 4 5 35315) 10 →
    PEqualNP.Represents.RepSizeAtMost (@mask 4 4 4731) 9 := by
  exact smaller 35315 4731 (id : Fin 4 → Fin 4) skipFourth
    7 (1,3) (1,4) (1,0) (by decide +kernel)

end PEqualNP.Outside.L_meta_25661_aux.Transfer

theorem PEqualNP.Outside.L_meta_25661 : ¬ (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (271347 : ℕ).testBit (6 * u.val + v.val)) 11) := by
  intro h
  exact PEqualNP.Outside.L_meta_6339.2
    (PEqualNP.Outside.L_meta_25661_aux.Transfer.dropFourth
      (PEqualNP.Outside.L_meta_25661_aux.Transfer.dropLast h))

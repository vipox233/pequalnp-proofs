import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25799_aux.Normal.Normalize
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x
theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]
theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega
theorem getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
theorem getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]
theorem run_init (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]
theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_init [] gs x i (by simpa using hi)
  simpa [run] using this
theorem run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_init gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_init gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)
theorem gv (N : ℕ) (C : Circuit) (hb : ReadsBack N C) (x : List Bool) (hx : x.length = N) (j : ℕ)
    (hj : j < C.gates.length) :
    (run C.gates x).getD (N + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => (run C.gates x).getD i false) := by
  have hw := run_gate C.gates x j hj
  have he : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
  rw [hx, ← he] at hw
  rw [hw]
  congr 1
  exact List.map_congr_left fun i hi => if_pos (hb j hj i hi)
def reads (g : Gate) (w : ℕ) : Prop :=
  (g.op = .not ∧ g.inputs.head? = some w) ∨ (g.op ≠ .not ∧ w ∈ g.inputs)
end PEqualNP.Outside.L_meta_25799_aux.Normal.Normalize
namespace PEqualNP.Outside.L_meta_25799_aux.Normal.Normalize
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
def collapses {X : Type} (W : X → ℕ → Bool) (top : ℕ) (out : X → Bool) : Prop :=
  (∃ b, ∀ x, out x = b) ∨ ∃ w < top, ∀ x, out x = W x w
theorem read_pair (l : List ℕ) (w : ℕ) (hlen : l.length ≤ 2) (hw : w ∈ l) :
    l = [w] ∨ ∃ v, l = [w,v] ∨ l = [v,w] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨d,tail⟩⟩⟩
  · simp at hw
  · have e : w=a := by simpa using hw
    exact Or.inl (by rw [e])
  · rcases List.mem_cons.mp hw with e | h
    · exact Or.inr ⟨b,Or.inl (by rw [e])⟩
    · have e : w=b := by simpa using h
      exact Or.inr ⟨a,Or.inr (by rw [e])⟩
  · simp at hlen
theorem not_value {X : Type} (W : X → ℕ → Bool) (g : Gate) {w : ℕ} {b : Bool}
    (op : g.op = .not) (r : reads g w) (fixed : ∀ x, W x w = b) (x : X) :
    g.op.eval (g.inputs.map (W x)) = !b := by
  have he : g.inputs.head? = some w := by simpa [reads,op] using r
  cases h : g.inputs with
  | nil => simp [h] at he
  | cons a tail =>
    have e : a=w := by simpa [h] using he
    simp [op,h,GateOp.eval,e,fixed]
theorem dominant {X : Type} (W : X → ℕ → Bool) (g : Gate) (w : ℕ)
    (hlen : g.inputs.length ≤ 2) (r : reads g w) (op : g.op = .and ∨ g.op = .not)
    (fixed : ∀ x, W x w = false) :
    ∃ b, ∀ x, g.op.eval (g.inputs.map (W x)) = b := by
  rcases op with h|h
  · have mem : w ∈ g.inputs := by simpa [reads,h] using r
    refine ⟨false,fun x => ?_⟩
    rcases read_pair _ w hlen mem with e | ⟨v,e|e⟩ <;> simp [h,e,GateOp.eval,fixed]
  · exact ⟨true,not_value W g h r fixed⟩
theorem when_read {X : Type} (W : X → ℕ → Bool) (g : Gate) (top w : ℕ) (b : Bool)
    (ok : g.op = .and ∨ g.op = .or ∨ g.op = .not) (hlen : g.inputs.length ≤ 2)
    (before : ∀ t ∈ g.inputs, t < top) (r : reads g w) (fixed : ∀ x, W x w = b) :
    collapses W top (fun x => g.op.eval (g.inputs.map (W x))) := by
  by_cases hn : g.op = .not
  · exact Or.inl ⟨!b,not_value W g hn r fixed⟩
  have hop : g.op = .and ∨ g.op = .or := by tauto
  have mem : w ∈ g.inputs := by simpa [reads,hn] using r
  rcases read_pair _ w hlen mem with e | ⟨v,e⟩
  · refine Or.inl ⟨b,fun x => ?_⟩
    rcases hop with ho|ho <;> simp [ho,e,GateOp.eval,fixed]
  · have hv : v < top := before v (by rcases e with h|h <;> simp [h])
    rcases hop with h|h
    · cases b
      · refine Or.inl ⟨false,fun x => ?_⟩
        rcases e with h'|h' <;> simp [h,h',GateOp.eval,fixed]
      · refine Or.inr ⟨v,hv,fun x => ?_⟩
        rcases e with h'|h' <;> simp [h,h',GateOp.eval,fixed]
    · cases b
      · refine Or.inr ⟨v,hv,fun x => ?_⟩
        rcases e with h'|h' <;> simp [h,h',GateOp.eval,fixed]
      · refine Or.inl ⟨true,fun x => ?_⟩
        rcases e with h'|h' <;> simp [h,h',GateOp.eval,fixed]
def toNat {s : ℕ} (K : Finset (Fin s)) : Finset ℕ := K.map ⟨Fin.val,Fin.val_injective⟩
theorem marked {X : Type} (N : ℕ) (C : Circuit) (src : X → List Bool)
    (hs : ∀ x, (src x).length=N) (u : ℕ) (hu : u<N) (hu0 : ∀ x, (src x).getD u false=false)
    (fan : FanInTwo C) (back : ReadsBack N C) (K : Finset (Fin C.gates.length))
    (mark : ∀ j ∈ K, reads (C.gates.get j) u ∨ ∃ i : Fin C.gates.length, i<j ∧
      reads (C.gates.get i) u ∧ ((C.gates.get i).op=.and ∨ (C.gates.get i).op=.not) ∧
      reads (C.gates.get j) (N+i.val)) :
    ∀ k ∈ toNat K, k < C.gates.length ∧
      collapses (fun x w => (run C.gates (src x)).getD w false) (N+k)
        (fun x => (run C.gates (src x)).getD (N+k) false) := by
  let W := fun (x : X) (w : ℕ) => (run C.gates (src x)).getD w false
  have raw (x : X) : W x u = false :=
    (run_input _ _ _ (by rw [hs]; exact hu)).trans (hu0 x)
  have atGate (j : Fin C.gates.length) : gateAt C j.val=C.gates.get j :=
    List.getD_eq_getElem _ _ j.isLt
  have ev (j : Fin C.gates.length) (x : X) :
      W x (N+j.val) = (C.gates.get j).op.eval ((C.gates.get j).inputs.map (W x)) := by
    simpa only [W,atGate j] using gv N C back (src x) (hs x) j.val j.isLt
  intro k hk
  obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hk
  refine ⟨j.isLt,?_⟩
  change collapses W (N+j.val) (fun x => W x (N+j.val))
  have same := funext (ev j)
  rw [same]
  have ok := fan (C.gates.get j) (List.get_mem _ _)
  have before (t : ℕ) (ht : t∈(C.gates.get j).inputs) : t<N+j.val :=
    back j.val j.isLt t (by rwa [atGate])
  have folded (w : ℕ) (b : Bool) (r : reads (C.gates.get j) w) (h : ∀ x, W x w=b) :=
    when_read W _ (N+j.val) w b (by simpa using ok.1) ok.2 before r h
  rcases mark j hj with direct | ⟨i,_,ri,oi,rj⟩
  · exact folded u false direct raw
  · have fi := fan (C.gates.get i) (List.get_mem _ _)
    obtain ⟨b,hb⟩ := dominant W _ u fi.2 ri oi raw
    exact folded (N+i.val) b rj (fun x => (ev i x).trans (hb x))
end PEqualNP.Outside.L_meta_25799_aux.Normal.Normalize
namespace PEqualNP.Outside.L_meta_25799_aux.Normal
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
open scoped Classical
abbrev Active (C : Circuit) := readsIn C (Finset.range C.size)
theorem wire_positive {C : Circuit} {w j : ℕ} (hj : j<C.size) (hw : w∈(gateAt C j).inputs) :
    0<Active C w := lt_of_lt_of_le (List.count_pos_iff.mpr hw) (Finset.single_le_sum
      (f:=fun k => (gateAt C k).inputs.count w) (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hj))
end PEqualNP.Outside.L_meta_25799_aux.Normal
namespace PEqualNP.Outside.L_meta_25799_aux.Cone.Profile.Wire
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
def W (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w
theorem W_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    W (g :: gs) w = W gs (step w g) := rfl
theorem step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]
theorem W_length (gs : List Gate) :
    ∀ w : List Bool, (W gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [W]
  | cons g gs ih =>
    intro w
    rw [W_cons, ih, step_len, List.length_cons]
    omega
theorem getD_app_lt (l l2 : List Bool) (i : ℕ) (h : i < l.length) :
    (l ++ l2).getD i false = l.getD i false := by
  simp [List.getD, List.getElem?_append_left h]
theorem getD_app_len (l : List Bool) (v : Bool) : (l ++ [v]).getD l.length false = v := by
  simp [List.getD]
theorem getD_ge (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
theorem step_lt (w : List Bool) (g : Gate) (i : ℕ) (h : i < w.length) :
    (step w g).getD i false = w.getD i false := getD_app_lt w _ i h
theorem step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk; exact getD_app_len w _
theorem W_prefix (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length → (W gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [W_cons, ih (step w g) i (by rw [step_len]; omega)]
    exact getD_app_lt w _ i hi
theorem W_ge (gs : List Gate) (w : List Bool) (i : ℕ) (h : w.length + gs.length ≤ i) :
    (W gs w).getD i false = false := getD_ge _ _ (by rw [W_length]; exact h)
theorem W_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (W gs w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (W gs w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [W_cons]
    cases j with
    | zero =>
      have h1 : w.length < (step w g).length := by simp [step]
      rw [Nat.add_zero, W_prefix gs (step w g) w.length h1]
      simp only [List.getElem_cons_zero]
      rw [step_last w g w.length rfl]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, W_prefix gs (step w g) i (by simp [step]; omega)]
        exact (step_lt w g i hi).symm
      · rw [if_neg hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (step w g) j hj'
      have hl : (step w g).length = w.length + 1 := step_len w g
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key
theorem gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]
theorem getElem?_gateAt {C : Circuit} {j : ℕ} {g : Gate} (h : C.gates[j]? = some g) :
    gateAt C j = g ∧ j < C.gates.length := by
  have hj : j < C.gates.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at h; cases h
  refine ⟨?_, hj⟩
  rw [gateAt_eq hj]
  rw [List.getElem?_eq_getElem hj] at h
  exact Option.some.inj h
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false
theorem eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl
theorem val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := W_prefix _ _ _ (by omega)
theorem val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := W_ge _ _ _ (by omega)
theorem val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact W_gate C.gates x j hj
theorem val_gate_rb {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) (hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => val C x i) := by
  rw [val_gate hx hj]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [if_pos (hrb i hi)]
theorem val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]
theorem val_ofFn_lt {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    val C (List.ofFn x) u = x ⟨u, hu⟩ := val_ofFn C x ⟨u, hu⟩
def pt (n m a b : ℕ) : Fin (n + m) → Bool := fun k => decide (k.val = a) || decide (k.val = b)
theorem oneEach_pt (n m : ℕ) (u : Fin n) (v : Fin m) :
    PEqualNP.Represents.oneEach u v = List.ofFn (pt n m u.val (n + v.val)) := by
  rw [List.ofFn_add]
  unfold PEqualNP.Represents.oneEach
  have hu := u.isLt
  have hv := v.isLt
  congr 1
  · congr 1
    funext k
    have hk := k.isLt
    rw [Bool.eq_iff_iff]
    simp only [pt, decide_eq_true_eq, Bool.or_eq_true, Fin.ext_iff, Fin.val_castAdd, Fin.coe_castLE]
    omega
  · congr 1
    funext k
    have hk := k.isLt
    rw [Bool.eq_iff_iff]
    simp only [pt, decide_eq_true_eq, Bool.or_eq_true, Fin.ext_iff, Fin.coe_natAdd]
    omega
end PEqualNP.Outside.L_meta_25799_aux.Cone.Profile.Wire
namespace PEqualNP.Outside.L_meta_25799_aux.Cone.Profile
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
def inner51 (N : Nat) (D : Finset Nat) (w : Nat) : Prop :=
  N≤w ∧ w-N∈D
structure Region51 (N : Nat) (C : Circuit) (S D E : Finset Nat) (top : Nat) : Prop where
  back : ReadsBack N C
  small : ∀ w∈S, w<N
  kept : D ⊆ Finset.range C.size
  topMem : top∈D
  one : E.card≤1
  entries : ∀ w∈E,w<N+top ∧ w∉S ∧ ¬inner51 N D w
  gates : ∀ j∈D, ((gateAt C j).op=.and ∨ (gateAt C j).op=.or) ∧
    ∀ w∈(gateAt C j).inputs,w∈S ∨ inner51 N D w ∨ w∈E
  sealedInputs : ∀ j<C.size,j∉D → ∀ w∈(gateAt C j).inputs,w∉S ∧ (inner51 N D w → w=N+top)
  outS : C.output∉S
  outD : inner51 N D C.output → C.output=N+top
def cutVal51 (C : Circuit) (N : Nat) (E : Finset Nat) (lit : Nat) (e : Bool) (w : Nat) : Bool :=
  if w∈E then e else if w<N then decide (w=lit) else
    (gateAt C (w-N)).op.eval ((gateAt C (w-N)).inputs.map fun v =>
      if hv : v<w then cutVal51 C N E lit e v else false)
termination_by w
private lemma gateMono51 {l : List Nat} {f g : Nat → Bool} {op : GateOp}
    (h : op=.and ∨ op=.or) (le : ∀ v∈l,f v=true → g v=true)
    (x : op.eval (l.map f)=true) : op.eval (l.map g)=true := by
  rcases h with rfl|rfl
  · simp only [GateOp.eval,List.all_map,List.all_eq_true,Function.comp_apply,id_eq] at x ⊢
    exact fun v hv => le v hv (x v hv)
  · simp only [GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq] at x ⊢
    obtain ⟨v,hv,hf⟩ := x
    exact ⟨v,hv,le v hv hf⟩
theorem cutMono51 {C : Circuit} {N lit top : Nat} {S D E : Finset Nat}
    (H : Region51 N C S D E top) {a b : Bool} (le : ∀ v∈E,a=true → b=true) :
    ∀ w, w∈S ∨ inner51 N D w ∨ w∈E →
      cutVal51 C N E lit a w=true → cutVal51 C N E lit b w=true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro h
    rw [cutVal51,cutVal51]
    by_cases he : w∈E
    · simpa only [if_pos he] using le w he
    simp only [if_neg he]
    by_cases raw : w<N
    · simp only [if_pos raw,imp_self]
    simp only [if_neg raw]
    have ins : inner51 N D w := (h.resolve_left (fun z => raw (H.small w z))).resolve_right he
    have jmem := ins.2
    refine gateMono51 (H.gates _ jmem).1 ?_
    intro v hv
    have lt := H.back (w-N) (Finset.mem_range.mp (H.kept jmem)) v hv
    have bound : v<w := by have := ins.1;omega
    simpa only [dif_pos bound] using ih v bound ((H.gates _ jmem).2 v hv)
theorem cutMatches51 {C : Circuit} {N lit top : Nat} {S D E : Finset Nat}
    (H : Region51 N C S D E top) (values : Nat → Bool) (e : Bool)
    (base : ∀ w∈S,values w=decide (w=lit)) (boundary : ∀ w∈E,values w=e)
    (step : ∀ j<C.size,values (N+j)=(gateAt C j).op.eval ((gateAt C j).inputs.map values)) :
    ∀ w, w∈S ∨ inner51 N D w ∨ w∈E → values w=cutVal51 C N E lit e w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro h
    rw [cutVal51]
    by_cases he : w∈E
    · simpa only [if_pos he] using boundary w he
    simp only [if_neg he]
    by_cases raw : w<N
    · rw [if_pos raw]
      exact base w (h.resolve_right (fun z => z.elim (fun si => (Nat.not_le_of_gt raw) si.1) he))
    rw [if_neg raw]
    have ins : inner51 N D w := (h.resolve_left (fun z => raw (H.small w z))).resolve_right he
    have jmem := ins.2
    have jlt := Finset.mem_range.mp (H.kept jmem)
    have eq := step (w-N) jlt
    rw [show N+(w-N)=w by omega] at eq
    rw [eq]
    congr 1
    apply List.map_congr_left
    intro v hv
    have lt := H.back (w-N) jlt v hv
    have bound : v<w := by have := ins.1;omega
    rw [dif_pos bound]
    exact ih v bound ((H.gates _ jmem).2 v hv)
theorem outside51 {C : Circuit} {N top : Nat} {S D E : Finset Nat}
    (H : Region51 N C S D E top) (x y : Nat → Bool)
    (raw : ∀ w<N,w∉S → x w=y w)
    (gate : ∀ j<C.size,(∀ v∈(gateAt C j).inputs,x v=y v) → x (N+j)=y (N+j))
    (large : ∀ w,N+C.size≤w → x w=y w) :
    ∀ w,w∉S → (inner51 N D w → w=N+top) → (N+top≤w → x (N+top)=y (N+top)) → x w=y w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro ns ex term
    by_cases inp : w<N
    · exact raw w inp ns
    by_cases high : N+C.size≤w
    · exact large w high
    by_cases localWire : inner51 N D w
    · have eq := ex localWire
      exact eq ▸ term (by omega)
    have jlt : w-N<C.size := by omega
    have nreg : w-N∉D := fun hit => localWire ⟨by omega,hit⟩
    have add : N+(w-N)=w := by omega
    have agree (v : Nat) (hv : v∈(gateAt C (w-N)).inputs) : x v=y v := by
      have b := H.back (w-N) jlt v hv
      have bv : v<w := by omega
      have e := H.sealedInputs _ jlt nreg v hv
      exact ih v bv e.1 e.2 (fun z => term (by omega))
    exact add ▸ gate _ jlt agree
end PEqualNP.Outside.L_meta_25799_aux.Cone.Profile
namespace PEqualNP.Outside.L_meta_25799_aux.Cone.Profile
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
theorem sideCap51 {n m d N top : Nat} {C : Circuit} {S D E : Finset Nat}
    (H : Region51 N C S D E top) (A : Finset (Fin n)) (B : Finset (Fin m))
    (G : Fin n → Fin m → Bool) (pin : Fin n → Nat) (other : Fin m → Nat)
    (V : Fin n → Fin m → Nat → Bool)
    (distance : ∀ a b : Fin n,a≠b → d≤(Finset.univ.filter (fun v=>G a v≠G b v)).card)
    (privatePin : ∀ a∈A,pin a∈S) (unmarked : ∀ v∉B,other v∉S)
    (inputs : ∀ a v w,w<N → V a v w=(decide (w=pin a) || decide (w=other v)))
    (step : ∀ a v j,j<C.size → V a v (N+j)=(gateAt C j).op.eval ((gateAt C j).inputs.map (V a v)))
    (large : ∀ a v w,N+C.size≤w → V a v w=false)
    (result : ∀ a v,V a v C.output=G a v) (short : B.card<d) :
    A.card≤2+E.card := by
  classical
  let sig (a : Fin n) (e : Bool) := cutVal51 C N E (pin a) e (N+top)
  have itop : inner51 N D (N+top) := ⟨by omega,by simpa using H.topMem⟩
  have mon (a : Fin n) : sig a false=true → sig a true=true :=
    cutMono51 H (fun _ _ _ => rfl) _ (Or.inr (Or.inl itop))
  let code (a : Fin n) : Nat := if sig a false then 0 else if sig a true then 2 else 1
  have cap (a : Fin n) : code a<2+E.card := by
    by_cases nonempty : E.Nonempty
    · have h := Finset.card_pos.mpr nonempty
      dsimp [code]; split <;> (try split) <;> omega
    · have rev : sig a true=true → sig a false=true :=
        cutMono51 H (fun w hw => (nonempty ⟨w,hw⟩).elim) _ (Or.inr (Or.inl itop))
      dsimp [code]; split <;> (try split) <;> first | omega | solve_by_elim
  have same {a b : Fin n} (h : code a=code b) (t : Bool) : sig a t=sig b t := by
    have ma := mon a
    have mb := mon b
    dsimp only [code] at h
    cases t <;> cases fa : sig a false <;> cases fb : sig b false <;>
      cases ta : sig a true <;> cases tb : sig b true <;> simp_all
  have inj : Set.InjOn code (↑A : Set (Fin n)) := by
    intro a ha b hb eqcode
    by_contra ne
    have subset : Finset.univ.filter (fun v=>G a v≠G b v) ⊆ B := by
      intro v hv
      by_contra nv
      have agreeRaw : ∀ w<N,w∉S → V a v w=V b v w := by
        intro w hw ns
        have na : w≠pin a := fun z=>ns (z ▸ privatePin a ha)
        have nb : w≠pin b := fun z=>ns (z ▸ privatePin b hb)
        simp [inputs a v w hw,inputs b v w hw,na,nb]
      have outside := outside51 H (V a v) (V b v) agreeRaw (fun j hj h => by
        rw [step a v j hj,step b v j hj,List.map_congr_left h])
        (fun w hw => (large a v w hw).trans (large b v w hw).symm)
      have entrySame {w : Nat} (hw : w∈E) : V a v w=V b v w := by
        obtain ⟨less,ns,nd⟩ := H.entries w hw
        exact outside w ns (fun i=> (nd i).elim) (fun le=> (Nat.not_le_of_gt less le).elim)
      obtain ⟨state,ab,bb⟩ : ∃ t : Bool,(∀ w∈E,V a v w=t) ∧ ∀ w∈E,V b v w=t := by
        by_cases ex : E.Nonempty
        · obtain ⟨w,hw⟩ := ex
          refine ⟨V a v w,?_,?_⟩
          · intro t ht
            rw [Finset.card_le_one.mp H.one t ht w hw]
          · intro t ht
            rw [Finset.card_le_one.mp H.one t ht w hw,entrySame hw]
        · exact ⟨false,fun w hw=>(ex ⟨w,hw⟩).elim,fun w hw=>(ex ⟨w,hw⟩).elim⟩
      have base (q : Fin n) (w : Nat) (hw : w∈S) : V q v w=decide (w=pin q) := by
        have otherNe : w≠other v := fun en => unmarked v nv (en ▸ hw)
        simp [inputs q v w (H.small w hw),otherNe]
      have topA := cutMatches51 H (V a v) state (base a) ab (step a v) (N+top) (Or.inr (Or.inl itop))
      have topB := cutMatches51 H (V b v) state (base b) bb (step b v) (N+top) (Or.inr (Or.inl itop))
      have topAgree := topA.trans ((same eqcode state).trans topB.symm)
      apply (Finset.mem_filter.mp hv).2
      exact (result a v).symm.trans ((outside _ H.outS H.outD (fun _=>topAgree)).trans (result b v))
    have low := distance a b ne
    have up := Finset.card_le_card subset
    omega
  have small : A.image code ⊆ Finset.range (2+E.card) := by
    intro j hj
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_range.mpr (cap a)
  have cnt := Finset.card_le_card small
  simpa [Finset.card_image_of_injOn inj] using cnt
end PEqualNP.Outside.L_meta_25799_aux.Cone.Profile
namespace PEqualNP.Outside.L_meta_25799_aux.Cone
open PEqualNP.Outside.L_meta_25799_aux.Cone.Profile in
theorem cap51 :
∀ (n m d : ℕ) (G : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit)
    (R : Finset (Fin n)) (B : Finset (Fin m)) (region entry : Finset ℕ) (top : ℕ),
  let raw := n + m
  let sources := R.image (fun sourceRow => sourceRow.val) ∪ B.image (fun sourceCol => n + sourceCol.val)
  let inside := fun (w : ℕ) => raw ≤ w ∧ w - raw ∈ region
  let gate := PEqualNP.MetaComplexity.NestedCover.gateAt C
  (∀ firstRow secondRow : Fin n, firstRow ≠ secondRow → d ≤ (Finset.univ.filter (fun col => G firstRow col ≠ G secondRow col)).card) →
  (∀ firstCol secondCol : Fin m, firstCol ≠ secondCol → d ≤ (Finset.univ.filter (fun row => G row firstCol ≠ G row secondCol)).card) →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack raw C →
  PEqualNP.Represents.Represents G C → region ⊆ Finset.range C.size → top ∈ region →
  entry.card ≤ 1 → (∀ w ∈ entry, w < raw + top ∧ w ∉ sources ∧ ¬ inside w) →
  (∀ k ∈ region,
    ((gate k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
     (gate k).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
    ∀ w ∈ (gate k).inputs, w ∈ sources ∨ inside w ∨ w ∈ entry) →
  (∀ k < C.size, k ∉ region → ∀ w ∈ (gate k).inputs,
    w ∉ sources ∧ (inside w → w = raw + top)) →
  C.output ∉ sources → (inside C.output → C.output = raw + top) →
  (B.card < d → R.card ≤ 2 + entry.card) ∧ (R.card < d → B.card ≤ 2 + entry.card) := by
  intro n m d G C R B region entry top raw sources inside gate farR farB back rep kept topMem one ext gates privateReads outputRaw outputGate
  classical
  let row := fun u : Fin n => u.val
  let col := fun v : Fin m => n+v.val
  have containsRow (u : Fin n) : row u∈sources ↔ u∈R := by
    constructor
    · intro hu
      rcases Finset.mem_union.mp hu with h|h
      · obtain ⟨q,hq,eqn⟩ := Finset.mem_image.mp h
        exact (Fin.ext eqn : q=u) ▸ hq
      · obtain ⟨q,_,eqn⟩ := Finset.mem_image.mp h
        change n+q.val=u.val at eqn
        omega
    · exact fun hu=>Finset.mem_union_left _ (Finset.mem_image.mpr ⟨u,hu,rfl⟩)
  have containsCol (v : Fin m) : col v∈sources ↔ v∈B := by
    constructor
    · intro hv
      rcases Finset.mem_union.mp hv with h|h
      · obtain ⟨q,_,eqn⟩ := Finset.mem_image.mp h
        change q.val=n+v.val at eqn
        omega
      · obtain ⟨q,hq,eqn⟩ := Finset.mem_image.mp h
        change n+q.val=n+v.val at eqn
        exact (Fin.ext (Nat.add_left_cancel eqn) : q=v) ▸ hq
    · exact fun hv=>Finset.mem_union_right _ (Finset.mem_image.mpr ⟨v,hv,rfl⟩)
  have small : ∀ w∈sources,w<raw := by
    intro w h
    rcases Finset.mem_union.mp h with h|h
    · obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp h
      change q.val<n+m; omega
    · obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp h
      change n+q.val<n+m; omega
  have H : Region51 raw C sources region entry top :=
    ⟨back,small,kept,topMem,one,ext,gates,privateReads,outputRaw,outputGate⟩
  let V := fun (u : Fin n) (v : Fin m) => Wire.val C (List.ofFn (Wire.pt n m (row u) (col v)))
  have inp (a : Fin n) (v : Fin m) (w : Nat) (hw : w<raw) :
      V a v w=(decide (w=row a) || decide (w=col v)) :=
    Wire.val_ofFn_lt C (Wire.pt n m (row a) (col v)) w hw
  have next (a : Fin n) (v : Fin m) (j : Nat) (hj : j<C.size) :
      V a v (raw+j)=(gate j).op.eval ((gate j).inputs.map (V a v)) :=
    Wire.val_gate_rb (by simp [raw]) hj (back j hj)
  have high (a : Fin n) (v : Fin m) (w : Nat) (hw : raw+C.size≤w) : V a v w=false :=
    Wire.val_ge (by simp [raw]) hw
  have out (a : Fin n) (v : Fin m) : V a v C.output=G a v := by
    have h := rep a v
    rw [Wire.oneEach_pt] at h
    exact h
  refine ⟨sideCap51 H R B G row col V farR (fun a=> (containsRow a).2)
      (fun v hv h=>hv ((containsCol v).1 h)) inp next high out,?_⟩
  apply sideCap51 H B R (fun v a=>G a v) col row (fun v a=>V a v) farB
      (fun v=>(containsCol v).2) (fun a ha h=>ha ((containsRow a).1 h))
  · intro v a w l
    rw [inp a v w l,Bool.or_comm]
  · exact fun v a => next a v
  · exact fun v a => high a v
  · exact fun v a => out a v
end PEqualNP.Outside.L_meta_25799_aux.Cone
namespace PEqualNP.Outside.L_meta_25799_aux.Cone
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
def nodes (N:Nat) (region S:Finset Nat) := S ∪ region.image (fun j=>N+j)
def edge (N:Nat) (C:Circuit) (region:Finset Nat) (w z:Nat) : Prop :=
  ∃ j∈region,z=N+j ∧ w∈(gateAt C j).inputs
abbrev reach (N:Nat) (C:Circuit) (region:Finset Nat) := Relation.ReflTransGen (edge N C region)
noncomputable def subsetAt (N:Nat) (C:Circuit) (region S:Finset Nat) (top:Nat) : Finset Nat := by
  classical exact S.filter (fun w=>reach N C region w top)
structure Frame (N:Nat) (C:Circuit) (region S entries:Finset Nat) (root:Nat) : Prop where
  low : ∀w∈S,w<N
  back : ReadsBack N C
  reg : region ⊆ Finset.range C.size
  rootIn : root∈nodes N region S
  entryOut : ∀e∈entries,e∉nodes N region S
  entryRead : ∀e∈entries,readsIn C region e=1
  shape : ∀j∈region, ((gateAt C j).op=.and ∨ (gateAt C j).op=.or) ∧
    (gateAt C j).inputs.length=2 ∧
    ∀ w∈(gateAt C j).inputs,w∈nodes N region S ∨ w∈entries
  rootZero : readsIn C region root=0
  priv : ∀w∈nodes N region S,w≠root →
    readsIn C region w=1 ∧ readsIn C (Finset.range C.size) w=1 ∧ C.output≠w
end PEqualNP.Outside.L_meta_25799_aux.Cone
namespace PEqualNP.Outside.L_meta_25799_aux.Cone
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
variable {N : Nat} {C : Circuit} {reg S X : Finset Nat} {root : Nat}
variable (F : Frame N C reg S X root)
include F
lemma edge_lt {u v:Nat} (e:edge N C reg u v) : u<v := by
  obtain ⟨j,hj,rfl,hit⟩:=e
  exact F.back j (Finset.mem_range.mp (F.reg hj)) u hit
lemma reach_le {u v:Nat} (h:reach N C reg u v) : u≤v := by
  induction h with
  | refl => rfl
  | tail _ e ih => exact ih.trans (Nat.le_of_lt (edge_lt F e))
lemma reader_le_one {j w:Nat} (hj:j∈reg) (hw:w∈(gateAt C j).inputs) : readsIn C reg w≤1 := by
  rcases (F.shape j hj).2.2 w hw with inside|ent
  · by_cases eq:w=root
    · simp [eq,F.rootZero]
    · exact Nat.le_of_eq (F.priv w inside eq).1
  · exact Nat.le_of_eq (F.entryRead w ent)
lemma succUnique {u v w:Nat} (h:edge N C reg u v) (h':edge N C reg u w) : v=w := by
  obtain ⟨i,hi,rfl,iu⟩:=h;obtain ⟨j,hj,rfl,ju⟩:=h'
  by_contra neq
  have ij : i≠j:=by omega
  have le:=Finset.add_le_sum (f:=fun k=>(gateAt C k).inputs.count u) (fun _ _=>Nat.zero_le _) hi hj ij
  have h1:=List.count_pos_iff.mpr iu
  have h2:=List.count_pos_iff.mpr ju
  have h3:=reader_le_one F hi iu
  change _≤readsIn C reg u at le
  omega
lemma enters {u v : Nat} (e:edge N C reg u v) : ∃ j∈reg,v=N+j := by
  obtain ⟨j,h,rfl,_⟩:=e;exact ⟨j,h,rfl⟩
lemma reachesRoot {w:Nat} (hw:w∈nodes N reg S) : reach N C reg w root := by
  let M:=N+C.size
  have bl {i:Nat} (h:i∈nodes N reg S) : i<M := by
    rcases Finset.mem_union.mp h with hs|hi
    · have:=F.low _ hs;dsimp [M];omega
    · obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp hi
      have:=Finset.mem_range.mp (F.reg hj);dsimp [M];omega
  suffices work : ∀ d,∀ i∈nodes N reg S, M-i=d → reach N C reg i root by exact work _ w hw rfl
  intro d;induction d using Nat.strong_induction_on with
  | ind d ih =>
    intro i hi eq
    by_cases ir:i=root
    · subst i;exact .refl
    have one:readsIn C reg i=1 := (F.priv _ hi ir).1
    have hit:∃j∈reg,i∈(gateAt C j).inputs := by
      by_contra! nh
      have z:readsIn C reg i=0:=Finset.sum_eq_zero (fun j hj=>List.count_eq_zero.mpr (nh j hj))
      omega
    obtain ⟨j,hj,m⟩:=hit
    have ed : edge N C reg i (N+j) := ⟨j,hj,rfl,m⟩
    have next:N+j∈nodes N reg S := Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j,hj,rfl⟩)
    exact (ih (M-(N+j)) (by have:=edge_lt F ed;have:=bl next;omega) (N+j) next rfl).head ed
lemma siblingsApart {x y top u:Nat} (ex:edge N C reg x top) (ey:edge N C reg y top)
    (ne:x≠y) (px:reach N C reg u x) (py:reach N C reg u y) : False := by
  have impossible {a b:Nat} (aa:edge N C reg a top) (bb:edge N C reg b top)
      (nn:a≠b) (path:reach N C reg a b) : False := by
    rcases path.cases_head with eq|⟨c,ac,cb⟩
    · exact nn eq
    · have same:=succUnique F aa ac
      have :=reach_le F cb;have:=edge_lt F bb;omega
  have unique : Relator.RightUnique (edge N C reg) := by
    intro a b c x y;exact succUnique F x y
  rcases Relation.ReflTransGen.total_of_right_unique unique px py with xy|yx
  · exact impossible ex ey ne xy
  · exact impossible ey ex ne.symm yx
lemma rootLeaves : subsetAt N C reg S root=S := by
  classical
  ext w;constructor
  · exact fun h=>(Finset.mem_filter.mp h).1
  · intro h;exact Finset.mem_filter.mpr ⟨h,reachesRoot F (Finset.mem_union_left _ h)⟩
end PEqualNP.Outside.L_meta_25799_aux.Cone
namespace PEqualNP.Outside.L_meta_25799_aux.Cone
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
variable {N : Nat} {C : Circuit} {reg S X : Finset Nat} {root : Nat}
variable (F : Frame N C reg S X root)
include F
private lemma splitNode (top:Nat) :
    (subsetAt N C reg S top).card≤1 ∨
    ∃ x y : Nat, x≠y ∧ top∈nodes N reg S ∧ edge N C reg x top ∧ edge N C reg y top ∧
      (subsetAt N C reg S top).card≤(subsetAt N C reg S x).card+(subsetAt N C reg S y).card := by
  classical
  by_cases gate : ∃ j∈reg,top=N+j
  · right
    obtain ⟨j,hj,rfl⟩:=gate
    obtain ⟨x,y,eq⟩:=List.length_eq_two.mp (F.shape j hj).2.1
    have hitx : x∈(gateAt C j).inputs := by simp [eq]
    have hity : y∈(gateAt C j).inputs := by simp [eq]
    have ne:x≠y := by
      intro e;subst y
      have le:=Finset.single_le_sum (f:=fun k=>(gateAt C k).inputs.count x) (fun _ _=>Nat.zero_le _) hj
      change (gateAt C j).inputs.count x≤readsIn C reg x at le
      have lim:=reader_le_one F hj hitx
      simp [eq] at le;omega
    refine ⟨x,y,ne,Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j,hj,rfl⟩),⟨j,hj,rfl,hitx⟩,⟨j,hj,rfl,hity⟩,?_⟩
    apply le_trans (b:=((subsetAt N C reg S x) ∪ (subsetAt N C reg S y)).card) _ (Finset.card_union_le _ _)
    apply Finset.card_le_card
    intro w hw
    obtain ⟨hs,p⟩:=Finset.mem_filter.mp hw
    rcases p.cases_tail with same|⟨v,pv,i,hi,ii,m⟩
    · have:=F.low w hs;omega
    · have ij:i=j:=by omega
      subst i
      rw [eq] at m
      rcases (by simpa using m : v=x ∨ v=y) with rfl|rfl
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hs,pv⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hs,pv⟩)
  · left;apply Finset.card_le_one.mpr
    intro a ha b hb
    have eqtop (w:Nat) (h:w∈subsetAt N C reg S top) : w=top := by
      have p:reach N C reg w top := (Finset.mem_filter.mp h).2
      rcases p.cases_tail with eq|⟨v,_,e⟩
      · exact eq.symm
      · exact (gate (enters F e)).elim
    exact (eqtop _ ha).trans (eqtop _ hb).symm
omit F in
private lemma below {a b : Nat} {T:Finset Nat} (e:edge N C reg a b) :
    subsetAt N C reg T a ⊆ subsetAt N C reg T b := by
  classical
  intro w hw;obtain ⟨h,p⟩:=Finset.mem_filter.mp hw
  exact Finset.mem_filter.mpr ⟨h,p.tail e⟩
lemma pureBounds (cap:∀top∈nodes N reg S,(subsetAt N C reg X top)=∅ →
    5≤(subsetAt N C reg S top).card → (subsetAt N C reg S top).card≤8 → False) :
    ∀top,(subsetAt N C reg X top)=∅ → (subsetAt N C reg S top).card≤4 := by
  intro t;induction t using Nat.strong_induction_on with
  | ind t ih =>
    intro empty
    rcases splitNode F t with leaf|⟨x,y,ne,ht,ex,ey,le⟩
    · omega
    · have bx:=ih x (edge_lt F ex) (Finset.subset_empty.mp (empty ▸ below (T:=X) ex))
      have by':=ih y (edge_lt F ey) (Finset.subset_empty.mp (empty ▸ below (T:=X) ey))
      by_contra! hlarge
      exact cap t ht empty (by omega) (by omega)
lemma boundPure (cap:∀top∈nodes N reg S,(subsetAt N C reg X top)=∅ →
    5≤(subsetAt N C reg S top).card → (subsetAt N C reg S top).card≤8 → False)
    (empty:X=∅) : S.card≤4 := by
  have hx : subsetAt N C reg X root=∅ := by simp [subsetAt,empty]
  simpa [rootLeaves F] using pureBounds F cap root hx
lemma boundMixed (cardX:X.card≤1)
    (pureCap:∀top∈nodes N reg S,(subsetAt N C reg X top)=∅ →
      5≤(subsetAt N C reg S top).card → (subsetAt N C reg S top).card≤8 → False)
    (mixCap:∀top∈nodes N reg S,7≤(subsetAt N C reg S top).card →
      (subsetAt N C reg S top).card≤10 → False) : S.card≤6 := by
  classical
  suffices all : ∀t,(subsetAt N C reg S t).card≤6 by simpa [rootLeaves F] using all root
  intro t;induction t using Nat.strong_induction_on with
  | ind t ih =>
    rcases splitNode F t with leaf|⟨x,y,ne,ht,ex,ey,le⟩
    · omega
    · have bx:=ih x (edge_lt F ex);have by':=ih y (edge_lt F ey)
      have either : subsetAt N C reg X x=∅ ∨ subsetAt N C reg X y=∅ := by
        by_contra! h
        obtain ⟨a,ha⟩:=h.1
        obtain ⟨b,hb⟩:=h.2
        obtain ⟨ax,ap⟩:=Finset.mem_filter.mp ha
        obtain ⟨bx,bp⟩:=Finset.mem_filter.mp hb
        have ab:=Finset.card_le_one.mp cardX a ax b bx;subst b
        exact siblingsApart F ex ey ne ap bp
      by_contra! large
      apply mixCap t ht (by omega)
      rcases either with h|h
      · have:=pureBounds F pureCap x h;omega
      · have:=pureBounds F pureCap y h;omega
end PEqualNP.Outside.L_meta_25799_aux.Cone
namespace PEqualNP.Outside.L_meta_25799_aux.Cone
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
abbrev srcSet {n m:Nat} (R:Finset (Fin n)) (B:Finset (Fin m)) :=
  R.image (fun u=>u.val) ∪ B.image (fun v=>n+v.val)
lemma srcCard {n m:Nat} (R:Finset (Fin n)) (B:Finset (Fin m)) :
    (srcSet R B).card=R.card+B.card := by
  classical
  unfold srcSet
  rw [Finset.card_union_of_disjoint,Finset.card_image_of_injective _ Fin.val_injective,
      Finset.card_image_of_injective _ (show Function.Injective (fun v:Fin m=>n+v.val) from fun _ _ e=>Fin.ext (Nat.add_left_cancel e))]
  apply Finset.disjoint_left.mpr
  intro w hu hv
  obtain ⟨u,_,rfl⟩:=Finset.mem_image.mp hu
  obtain ⟨v,_,e⟩:=Finset.mem_image.mp hv
  have:=u.isLt;omega
lemma srcLow {n m:Nat} (R:Finset (Fin n)) (B:Finset (Fin m)) (w:Nat) (hw:w∈srcSet R B) : w<n+m := by
  rcases Finset.mem_union.mp hw with a|b
  · obtain ⟨u,_,rfl⟩:=Finset.mem_image.mp a;have:=u.isLt;omega
  · obtain ⟨v,_,rfl⟩:=Finset.mem_image.mp b;have:=v.isLt;omega
def WindowCap {N:Nat} (C:Circuit) (reg S X:Finset Nat) (d:Nat) : Prop :=
  ∀top∈nodes N reg S,
    let l:=(subsetAt N C reg S top).card
    let e:=(subsetAt N C reg X top).card
    e≤1 → 2+e<d → l<2*d → l≤2*(2+e)
lemma pure59 {N root : Nat} {C:Circuit} {reg S:Finset Nat} (F:Frame N C reg S ∅ root)
    (cap:WindowCap (N:=N) C reg S ∅ 5) : S.card≤4 := by
  apply boundPure F _ rfl
  intro t ht empty low hi
  have val:=cap t ht
  dsimp only at val;rw [empty,Finset.card_empty] at val;omega
lemma mixed62 {N root e : Nat} {C:Circuit} {reg S:Finset Nat} (F:Frame N C reg S {e} root)
    (cap:WindowCap (N:=N) C reg S {e} 6) : S.card≤6 := by
  apply boundMixed F (by simp)
  · intro t ht empty low hi
    have val:=cap t ht
    dsimp only at val;rw [empty,Finset.card_empty] at val;omega
  · intro t ht low hi
    classical
    have le : (subsetAt N C reg {e} t).card≤1 := by
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (Finset.card_singleton e).le
    have val:=cap t ht
    dsimp only at val;omega
end PEqualNP.Outside.L_meta_25799_aux.Cone
namespace PEqualNP.Outside.L_meta_25799_aux.Cone
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
noncomputable def gateSubset (N : Nat) (C : Circuit) (region : Finset Nat) (top : Nat) : Finset Nat := by
  classical exact region.filter (fun j => reach N C region (N+j) top)
private theorem walk_le {N root : Nat} {C : Circuit} {P S E : Finset Nat}
    (F : Frame N C P S E root) {x y : Nat} (h : reach N C P x y) : x≤y := by
  induction h with
  | refl => exact le_rfl
  | tail _ e ih =>
    obtain ⟨j,hj,rfl,inp⟩:=e
    exact ih.trans (Nat.le_of_lt (F.back j (Finset.mem_range.mp (F.reg hj)) _ inp))
private theorem first_observer {N root : Nat} {C : Circuit} {P S E : Finset Nat}
    (F : Frame N C P S E root) {w top : Nat} (inW : w∈nodes N P S)
    (path : reach N C P w top) (notTop : w≠top) :
    C.output≠w ∧ ∀j<C.size,w∈(gateAt C j).inputs → j∈gateSubset N C P top := by
  classical
  obtain ⟨v,edge,rest⟩ := path.cases_head.resolve_left notTop
  obtain ⟨i,hi,rfl,hit⟩ := edge
  have count := List.count_pos_iff.mpr hit
  have sub : (gateAt C i).inputs.count w ≤ readsIn C P w :=
    Finset.single_le_sum (fun l _ => Nat.zero_le ((gateAt C l).inputs.count w)) hi
  have nr : w≠root := by
    intro eq
    subst w
    rw [F.rootZero] at sub
    omega
  obtain ⟨_,one,out⟩ := F.priv w inW nr
  refine ⟨out,?_⟩
  intro j hj readJ
  have ji : j=i := by
    by_contra ne
    have cnt2 := List.count_pos_iff.mpr readJ
    have both := Finset.add_le_sum (f:=fun l => (gateAt C l).inputs.count w) (fun _ _=>Nat.zero_le _)
      (Finset.mem_range.mpr hj) (F.reg hi) ne
    change _ ≤ readsIn C (Finset.range C.size) w at both
    omega
  subst j
  exact Finset.mem_filter.mpr ⟨hi,rest⟩
theorem subtree_boundary {N root : Nat} {C : Circuit} {P S E : Finset Nat}
    (F : Frame N C P S E root) {top : Nat} (member : top∈nodes N P S) (large : N≤top) :
    let P' := gateSubset N C P top
    let S' := subsetAt N C P S top
    let E' := subsetAt N C P E top
    let inside := fun w => N≤w ∧ w-N∈P'
    P' ⊆ Finset.range C.size ∧ top-N∈P' ∧
    (∀ e∈E', e<top ∧ e∉S' ∧ ¬inside e) ∧
    (∀ k∈P', ((gateAt C k).op=.and ∨ (gateAt C k).op=.or) ∧
      ∀w∈(gateAt C k).inputs,w∈S' ∨ inside w ∨ w∈E') ∧
    (∀ k<C.size, k∉P' → ∀w∈(gateAt C k).inputs, w∉S' ∧ (inside w → w=top)) ∧
    C.output∉S' ∧ (inside C.output → C.output=top) := by
  classical
  dsimp only
  have in_orig {w : Nat} (h : N≤w ∧ w-N∈gateSubset N C P top) :
      w∈nodes N P S ∧ reach N C P w top := by
    obtain ⟨lo,hw⟩:=h
    obtain ⟨hp,way⟩:=Finset.mem_filter.mp hw
    have eq : N+(w-N)=w:=by omega
    exact ⟨Finset.mem_union_right _ (Finset.mem_image.mpr ⟨w-N,hp,eq⟩),eq ▸ way⟩
  have raw_prop {w : Nat} (h : w∈subsetAt N C P S top) :
      w∈nodes N P S ∧ reach N C P w top ∧ w≠top := by
    obtain ⟨hs,path⟩:=Finset.mem_filter.mp h
    exact ⟨Finset.mem_union_left _ hs,path,ne_of_lt ((F.low _ hs).trans_le large)⟩
  have idx : top-N∈P := by
    rcases Finset.mem_union.mp member with hs | hg
    · have := F.low top hs;omega
    · obtain ⟨j,hj,eq⟩:=Finset.mem_image.mp hg
      exact (show top-N=j by omega) ▸ hj
  refine ⟨fun _ h=>F.reg (Finset.mem_filter.mp h).1,
    Finset.mem_filter.mpr ⟨idx,by rw [Nat.add_sub_of_le large]⟩,?_,?_,?_,?_,?_⟩
  · intro e he
    obtain ⟨inE,path⟩:=Finset.mem_filter.mp he
    have no := F.entryOut e inE
    exact ⟨lt_of_le_of_ne (walk_le F path) (fun eq=>no (eq ▸ member)),
      fun hs=>no (raw_prop hs).1,fun hi=>no (in_orig hi).1⟩
  · intro j hj
    obtain ⟨occurs,path⟩:=Finset.mem_filter.mp hj
    obtain ⟨op,_,inputs⟩:=F.shape j occurs
    refine ⟨op,?_⟩
    intro w hit
    have way : reach N C P w top := path.head ⟨j,occurs,rfl,hit⟩
    rcases inputs w hit with orig | ent
    · rcases Finset.mem_union.mp orig with src | g
      · exact Or.inl (Finset.mem_filter.mpr ⟨src,way⟩)
      · obtain ⟨k,hk,rfl⟩:=Finset.mem_image.mp g
        refine Or.inr (Or.inl ⟨by omega,?_⟩)
        rw [Nat.add_sub_cancel_left]
        exact Finset.mem_filter.mpr ⟨hk,way⟩
    · exact Or.inr (Or.inr (Finset.mem_filter.mpr ⟨ent,way⟩))
  · intro j hj outside w read
    constructor
    · intro hs
      obtain ⟨inW,way,ne⟩:=raw_prop hs
      exact outside ((first_observer F inW way ne).2 j hj read)
    · intro hi
      by_contra ne
      obtain ⟨inW,way⟩:=in_orig hi
      exact outside ((first_observer F inW way ne).2 j hj read)
  · intro hs
    obtain ⟨inW,way,ne⟩:=raw_prop hs
    exact (first_observer F inW way ne).1 rfl
  · intro hi
    by_contra ne
    obtain ⟨inW,way⟩:=in_orig hi
    exact (first_observer F inW way ne).1 rfl
theorem leaves_one_of_low {N root : Nat} {C : Circuit} {P S E : Finset Nat}
    (F : Frame N C P S E root) {top : Nat} (small : top<N) : (subsetAt N C P S top).card≤1 := by
  classical
  have sub : subsetAt N C P S top ⊆ {top} := by
    intro w hw;obtain ⟨_,path⟩:=Finset.mem_filter.mp hw
    rcases path.cases_tail with eq | ⟨v,_,j,hj,eq,_⟩
    · simpa using eq.symm
    · omega
  exact (Finset.card_le_card sub).trans (by simp)
end PEqualNP.Outside.L_meta_25799_aux.Cone
namespace PEqualNP.Outside.L_meta_25799_aux.Cone
def Gap51 : Prop :=
∀ (n m d : ℕ) (G : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit)
    (R : Finset (Fin n)) (B : Finset (Fin m)) (region entry : Finset ℕ) (top : ℕ),
  let raw := n + m
  let sources := R.image (fun sourceRow => sourceRow.val) ∪ B.image (fun sourceCol => n + sourceCol.val)
  let inside := fun (w : ℕ) => raw ≤ w ∧ w - raw ∈ region
  let gate := PEqualNP.MetaComplexity.NestedCover.gateAt C
  (∀ firstRow secondRow : Fin n, firstRow ≠ secondRow → d ≤ (Finset.univ.filter (fun col => G firstRow col ≠ G secondRow col)).card) →
  (∀ firstCol secondCol : Fin m, firstCol ≠ secondCol → d ≤ (Finset.univ.filter (fun row => G row firstCol ≠ G row secondCol)).card) →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack raw C →
  PEqualNP.Represents.Represents G C → region ⊆ Finset.range C.size → top ∈ region →
  entry.card ≤ 1 → (∀ w ∈ entry, w < raw + top ∧ w ∉ sources ∧ ¬ inside w) →
  (∀ k ∈ region,
    ((gate k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
     (gate k).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
    ∀ w ∈ (gate k).inputs, w ∈ sources ∨ inside w ∨ w ∈ entry) →
  (∀ k < C.size, k ∉ region → ∀ w ∈ (gate k).inputs,
    w ∉ sources ∧ (inside w → w = raw + top)) →
  C.output ∉ sources → (inside C.output → C.output = raw + top) →
  (B.card < d → R.card ≤ 2 + entry.card) ∧ (R.card < d → B.card ≤ 2 + entry.card)
end PEqualNP.Outside.L_meta_25799_aux.Cone
namespace PEqualNP.Outside.L_meta_25799_aux.Cone
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
def sourceIds {n m : Nat} (R : Finset (Fin n)) (B : Finset (Fin m)) : Finset Nat :=
  R.image Fin.val ∪ B.image (fun v=>n+v.val)
theorem sourceCard {n m : Nat} (R : Finset (Fin n)) (B : Finset (Fin m)) :
    (sourceIds R B).card = R.card+B.card := by
  classical
  have dis : Disjoint (R.image Fin.val) (B.image (fun v=>n+v.val)) := by
    apply Finset.disjoint_left.mpr
    intro w hw hb
    obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hw
    obtain ⟨v,hv,e⟩:=Finset.mem_image.mp hb
    have:=u.isLt;omega
  unfold sourceIds
  rw [Finset.card_union_of_disjoint dis,Finset.card_image_of_injective _ Fin.val_injective,
    Finset.card_image_of_injective _ (fun _ _ e=>Fin.ext (Nat.add_left_cancel e))]
theorem forbiddenWindow {n m d root : Nat} {G : Fin n → Fin m → Bool} {C : Circuit}
    {R : Finset (Fin n)} {B : Finset (Fin m)} {region entries : Finset Nat}
    (cap : Gap51)
    (dr : ∀ a b : Fin n, a≠b → d≤(Finset.univ.filter (fun col=>G a col≠G b col)).card)
    (dc : ∀ a b : Fin m, a≠b → d≤(Finset.univ.filter (fun row=>G row a≠G row b)).card)
    (rep : Represents G C) (F : Frame (n+m) C region (sourceIds R B) entries root)
    {top : Nat} (ht : top∈nodes (n+m) region (sourceIds R B))
    (one : (subsetAt (n+m) C region entries top).card≤1)
    (narrow : 2+(subsetAt (n+m) C region entries top).card<d)
    (window : (subsetAt (n+m) C region (sourceIds R B) top).card<2*d) :
    (subsetAt (n+m) C region (sourceIds R B) top).card ≤
      2*(2+(subsetAt (n+m) C region entries top).card) := by
  classical
  let N:=n+m
  let S:=sourceIds R B
  let P' := gateSubset N C region top
  let E' := subsetAt N C region entries top
  let A := R.filter (fun u => reach N C region u.val top)
  let H := B.filter (fun v => reach N C region (n+v.val) top)
  have ids : sourceIds A H = subsetAt N C region S top := by
    ext w
    simp only [sourceIds, A, H, S,subsetAt,Finset.mem_filter,Finset.mem_union,Finset.mem_image]
    constructor
    · rintro (⟨u,⟨hu,way⟩,rfl⟩ | ⟨v,⟨hv,way⟩,rfl⟩)
      · exact ⟨Or.inl ⟨u,hu,rfl⟩,way⟩
      · exact ⟨Or.inr ⟨v,hv,rfl⟩,way⟩
    · rintro ⟨(⟨u,hu,rfl⟩ | ⟨v,hv,rfl⟩),way⟩
      · exact Or.inl ⟨u,⟨hu,way⟩,rfl⟩
      · exact Or.inr ⟨v,⟨hv,way⟩,rfl⟩
  have card : (subsetAt N C region S top).card = A.card+H.card := by rw [←ids,sourceCard]
  by_cases inside : N≤top
  · obtain ⟨sub,topIn,ent,op,out,privateR,privateG⟩:=subtree_boundary F ht inside
    have eq : N+(top-N)=top := Nat.add_sub_of_le inside
    have rule := cap n m d G C A H P' E' (top-N) dr dc F.back rep sub topIn one
    change (∀w∈E', w<N+(top-N) ∧ w∉sourceIds A H ∧ ¬(N≤w ∧ w-N∈P')) → _ at rule
    have answer := rule (by simpa only [eq,ids] using ent)
      (by
        change ∀k∈P', _ ∧ ∀w∈(gateAt C k).inputs,w∈sourceIds A H ∨ (N≤w ∧ w-N∈P') ∨ w∈E'
        rw [ids];exact op)
      (by
        change ∀k<C.size,k∉P' → ∀w∈(gateAt C k).inputs,w∉sourceIds A H ∧ ((N≤w ∧ w-N∈P') → w=N+(top-N))
        rw [ids,eq];exact out)
      (by change C.output∉sourceIds A H;rw [ids];exact privateR)
      (by change (N≤C.output ∧ C.output-N∈P') → C.output=N+(top-N);rw [eq];exact privateG)
    obtain ⟨bsmall,asmall⟩ := answer
    change H.card<d → A.card≤2+E'.card at bsmall
    change A.card<d → H.card≤2+E'.card at asmall
    change 2+E'.card<d at narrow
    change (subsetAt N C region S top).card<2*d at window
    change (subsetAt N C region S top).card≤2*(2+E'.card)
    omega
  · have small:=leaves_one_of_low F (top:=top) (by omega)
    omega
end PEqualNP.Outside.L_meta_25799_aux.Cone
namespace PEqualNP.Outside.L_meta_25799_aux.Local
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open Cone Cone.Profile Cone.Profile.Wire
def world (N : Nat) (C : Circuit) (X : Finset Nat) (w : Nat) :=
  val C (List.ofFn (fun i : Fin N => decide (i.val ∈ X))) w
lemma world_raw {N C X w} (hw : w < N) : world N C X w = decide (w∈X) :=
  val_ofFn_lt C _ w hw
lemma world_step {N C X} (back : ReadsBack N C) (j : Nat) (hj : j<C.size) :
    world N C X (N+j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (world N C X)) :=
  val_gate_rb (by simp) hj (back j hj)
lemma world_past {N C X w} (far : N+C.size≤w) : world N C X w=false :=
  val_ge (by simp) far
def localVal (N : Nat) (C : Circuit) (E I : Finset Nat) (t : Bool) (w : Nat) : Bool :=
  if w∈E then t else if w<N then decide (w∈I) else
    (gateAt C (w-N)).op.eval ((gateAt C (w-N)).inputs.map (fun v =>
      if h : v<w then localVal N C E I t v else false))
termination_by w
variable {N : Nat} {C : Circuit} {S D E : Finset Nat} {j : Nat}
lemma local_mono (H : Region51 N C S D E j) {I J : Finset Nat} {a b : Bool}
    (growth : ∀w∈S, w∈I → w∈J) (bound : ∀w∈E, a=true → b=true) :
    ∀ w, w∈S ∨ inner51 N D w ∨ w∈E → localVal N C E I a w=true → localVal N C E J b w=true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    rw [localVal,localVal]
    by_cases he : w∈E
    · simpa only [if_pos he] using bound w he
    simp only [if_neg he]
    by_cases low : w<N
    · have hs : w∈S := (hw.resolve_right (fun h => h.elim (fun h => (Nat.not_le_of_gt low) h.1) he))
      simpa only [if_pos low,decide_eq_true_eq] using growth w hs
    simp only [if_neg low]
    have hd : inner51 N D w := (hw.resolve_left (fun h => low (H.small w h))).resolve_right he
    have mono {l : List Nat} {f g : Nat → Bool} {op : GateOp} (hop : op=.and ∨ op=.or)
        (h : ∀v∈l, f v=true → g v=true) : op.eval (l.map f)=true → op.eval (l.map g)=true := by
      rcases hop with rfl|rfl
      · simp only [GateOp.eval,List.all_map,List.all_eq_true,Function.comp_apply,id_eq]
        exact fun yes v hv => h v hv (yes v hv)
      · simp only [GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
        rintro ⟨v,hv,one⟩; exact ⟨v,hv,h v hv one⟩
    apply mono (H.gates _ hd.2).1
    intro v hv
    have lt := H.back (w-N) (Finset.mem_range.mp (H.kept hd.2)) v hv
    have less : v<w := by have := hd.1; omega
    simpa only [dif_pos less] using ih v less ((H.gates _ hd.2).2 v hv)
lemma agrees_inside (H : Region51 N C S D E j) (X I : Finset Nat) (a : Bool)
    (inside : ∀w∈S,w∈X ↔ w∈I) (boundary : ∀w∈E,world N C X w=a) :
    ∀ w, w∈S ∨ inner51 N D w ∨ w∈E → world N C X w=localVal N C E I a w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    rw [localVal]
    by_cases he : w∈E
    · simpa only [if_pos he] using boundary w he
    simp only [if_neg he]
    by_cases low : w<N
    · have hs : w∈S := hw.resolve_right (fun h => h.elim (fun h => (Nat.not_le_of_gt low) h.1) he)
      simp only [if_pos low,world_raw low,inside w hs]
    simp only [if_neg low]
    have hd : inner51 N D w := (hw.resolve_left (fun h => low (H.small w h))).resolve_right he
    have eq := world_step (X:=X) H.back (w-N) (Finset.mem_range.mp (H.kept hd.2))
    rw [Nat.add_sub_of_le hd.1] at eq
    rw [eq]
    congr 1
    apply List.map_congr_left
    intro v hv
    have lt:=H.back (w-N) (Finset.mem_range.mp (H.kept hd.2)) v hv
    have less : v<w := by have := hd.1; omega
    rw [dif_pos less]
    exact ih v less ((H.gates _ hd.2).2 v hv)
lemma compare_worlds (H : Region51 N C S D E j) {X Y I J : Finset Nat}
    (hx : ∀w∈S,w∈X ↔ w∈I) (hy : ∀w∈S,w∈Y ↔ w∈J)
    (agree : ∀w<N,w∉S → (w∈X ↔ w∈Y))
    (sec : ∀t,localVal N C E I t (N+j)=localVal N C E J t (N+j)) :
    world N C X C.output=world N C Y C.output := by
  have ext := outside51 H (world N C X) (world N C Y)
    (fun w low ns => by simp only [world_raw low, agree w low ns])
    (fun k hk h => by rw [world_step H.back k hk,world_step H.back k hk,List.map_congr_left h])
    (fun w hi => (world_past hi).trans (world_past hi).symm)
  have entry {w} (hw : w∈E) : world N C X w = world N C Y w := by
    obtain ⟨low,ns,outer⟩ := H.entries w hw
    exact ext w ns (fun z => (outer z).elim) (fun z => (Nat.not_le_of_gt low z).elim)
  obtain ⟨t, tx, ty⟩ : ∃ t : Bool, (∀w∈E,world N C X w=t) ∧ ∀w∈E,world N C Y w=t := by
    by_cases non : E.Nonempty
    · obtain ⟨b,hb⟩ := non
      refine ⟨world N C X b,?_,?_⟩
      · intro w hw; rw [Finset.card_le_one.mp H.one w hw b hb]
      · intro w hw; rw [Finset.card_le_one.mp H.one w hw b hb,←entry hb]
    · exact ⟨false,fun w h=>(non ⟨w,h⟩).elim,fun w h=>(non ⟨w,h⟩).elim⟩
  have top : inner51 N D (N+j) := ⟨by omega,by simpa using H.topMem⟩
  have left := agrees_inside H X I t hx tx (N+j) (Or.inr (Or.inl top))
  have right := agrees_inside H Y J t hy ty (N+j) (Or.inr (Or.inl top))
  exact ext _ H.outS H.outD (fun _ => left.trans ((sec t).trans right.symm))
def code (N : Nat) (C : Circuit) (E I : Finset Nat) (root : Nat) : Nat :=
  if localVal N C E I false root then 2 else if localVal N C E I true root then 1 else 0
lemma ordered (H : Region51 N C S D E j) (I : Finset Nat) :
    localVal N C E I false (N+j)=true → localVal N C E I true (N+j)=true :=
  local_mono H (fun _ _ h=>h) (fun _ _ _=>rfl) _
    (Or.inr (Or.inl ⟨by omega,by simpa using H.topMem⟩))
lemma same_code (H : Region51 N C S D E j) {I J : Finset Nat}
    (eq : code N C E I (N+j)=code N C E J (N+j)) (t : Bool) :
    localVal N C E I t (N+j)=localVal N C E J t (N+j) := by
  have u:=ordered H I; have v:=ordered H J
  dsimp only [code] at eq
  cases t <;> cases a:localVal N C E I false (N+j) <;> cases b:localVal N C E I true (N+j) <;>
    cases c:localVal N C E J false (N+j) <;> cases d:localVal N C E J true (N+j) <;> simp_all
lemma key_mem (H : Region51 N C S D E j) (I : Finset Nat) :
    code N C E I (N+j) ∈ (if E=∅ then {0,2} else {0,1,2} : Finset Nat) := by
  by_cases em : E=∅
  · have reverse : localVal N C E I true (N+j)=true → localVal N C E I false (N+j)=true :=
      local_mono H (fun _ _ h=>h) (fun w hw => (Finset.notMem_empty w (em ▸ hw)).elim) _
        (Or.inr (Or.inl ⟨by omega,by simpa using H.topMem⟩))
    rw [if_pos em]
    dsimp only [code]
    cases a:localVal N C E I false (N+j) <;> cases b:localVal N C E I true (N+j) <;> simp_all
  · rw [if_neg em]
    dsimp only [code]
    split <;> (try split) <;> decide
lemma masks (H : Region51 N C S D E j) {b : Nat} (top : code N C E {b} (N+j) = 2)
    {I : Finset Nat} (hb : b∈I) (t : Bool) :
    localVal N C E I t (N+j)=localVal N C E {b} t (N+j) := by
  have on : localVal N C E {b} false (N+j)=true := by
    dsimp only [code] at top
    split at top
    · assumption
    · split at top <;> contradiction
  have pulse : localVal N C E {b} t (N+j)=true := by cases t; exact on; exact ordered H _ on
  have both := local_mono H (I:={b}) (J:=I) (a:=t) (b:=t)
    (fun w _ hw => (Finset.mem_singleton.mp hw).symm ▸ hb) (fun _ _ h=>h) (N+j)
    (Or.inr (Or.inl ⟨by omega,by simpa using H.topMem⟩)) pulse
  exact both.trans pulse.symm
end PEqualNP.Outside.L_meta_25799_aux.Local
namespace PEqualNP.Outside.L_meta_25799_aux.Local
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open Cone Cone.Profile
abbrev dist {m : Nat} (f g : Fin m → Bool) := (Finset.univ.filter (fun i => f i ≠ g i)).card
def near {n m} (G : Fin n → Fin m → Bool) (base : Fin m → Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun a => dist (G a) base ≤ 2)
lemma near_small {n m} (G : Fin n → Fin m → Bool) (base : Fin m → Bool)
    (far : ∀a b, a≠b → 6 ≤ dist (G a) (G b)) : (near G base).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  by_contra ne
  have incl : Finset.univ.filter (fun i=>G a i≠G b i) ⊆
      Finset.univ.filter (fun i=>G a i≠base i) ∪ Finset.univ.filter (fun i=>G b i≠base i) := by
    intro i hi
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union] at hi ⊢
    by_cases eq : G a i=base i
    · exact Or.inr (fun eqb=>hi (eq.trans eqb.symm))
    · exact Or.inl eq
  have count := (Finset.card_le_card incl).trans (Finset.card_union_le _ _)
  have da := (Finset.mem_filter.mp ha).2
  have db := (Finset.mem_filter.mp hb).2
  have dl := far a b ne
  unfold dist at da db dl
  omega
variable {N : Nat} {C : Circuit} {S D E : Finset Nat} {j : Nat}
lemma exterior (H : Region51 N C S D E j) {I J : Finset Nat} (hI : I ⊆ S) (hJ : J ⊆ S)
    (z : Nat) (outside : z∉S) (eq : code N C E I (N+j) = code N C E J (N+j)) :
    world N C (insert z I) C.output = world N C (insert z J) C.output := by
  apply compare_worlds H (I:=I) (J:=J)
  · intro w hw
    simp [show w≠z from fun h=>outside (h ▸ hw)]
  · intro w hw
    simp [show w≠z from fun h=>outside (h ▸ hw)]
  · intro w _ hw
    simp [show w∉I from fun i=>hw (hI i),show w∉J from fun i=>hw (hJ i)]
  · exact same_code H eq
def palette (E : Finset Nat) : Finset Nat := if E=∅ then {0,2} else {0,1,2}
lemma palette_card (le : E.card ≤ 1) : (palette E).card = 2+E.card := by
  by_cases e : E=∅
  · simp [palette,e]
  · have pos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr e)
    have one : E.card=1 := by omega
    simp [palette,e,one]
lemma key_injective {n m : Nat} (H : Region51 N C S D E j) (p : Fin n → Nat) (q : Fin m → Nat)
    (R : Finset (Fin n)) (B : Finset (Fin m)) (rpin : ∀a∈R,p a∈S)
    (bpin : ∀v∉B,q v∉S) (G : Fin n → Fin m → Bool)
    (rep : ∀a v, G a v = world N C {q v,p a} C.output)
    (far : ∀a b,a≠b → 6≤dist (G a) (G b)) (size : R.card+B.card≤6) :
    Set.InjOn (fun a => code N C E {p a} (N+j)) (↑R : Set (Fin n)) := by
  intro a ha b hb eq
  by_contra ne
  have incl : Finset.univ.filter (fun v => G a v≠G b v) ⊆ B := by
    intro v hv
    by_contra out
    apply (Finset.mem_filter.mp hv).2
    rw [rep,rep]
    exact exterior H (Finset.singleton_subset_iff.mpr (rpin a ha))
      (Finset.singleton_subset_iff.mpr (rpin b hb)) (q v) (bpin v out) eq
  have hi := Finset.card_le_card incl
  have lo := far a b ne
  have non := Finset.card_pos.mpr (show R.Nonempty from ⟨a,ha⟩)
  unfold dist at lo
  omega
lemma bank_cap {n m : Nat} (H : Region51 N C S D E j) (p : Fin n → Nat) (q : Fin m → Nat)
    (R : Finset (Fin n)) (B : Finset (Fin m)) (rpin : ∀a∈R,p a∈S)
    (bpin : ∀v∉B,q v∉S) (G : Fin n → Fin m → Bool)
    (rep : ∀a v, G a v = world N C {q v,p a} C.output)
    (ri : Set.InjOn (fun a => code N C E {p a} (N+j)) (↑R : Set (Fin n)))
    (bi : Set.InjOn (fun v => code N C E {q v} (N+j)) (↑B : Set (Fin m))) :
    (R \ near G (fun v => world N C {q v} C.output)).card ≤ 1+E.card := by
  classical
  let kr := fun a => code N C E {p a} (N+j)
  let kc := fun v => code N C E {q v} (N+j)
  let zero := code N C E ∅ (N+j)
  let base := fun v => world N C {q v} C.output
  have rc (a) : kr a∈palette E := key_mem H _
  have cc (v) : kc v∈palette E := key_mem H _
  have baseMem : zero∈palette E := key_mem H _
  have colorSub : B.image kc ⊆ palette E := by
    intro z hz; obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hz; exact cc v
  have bcount := Finset.card_le_card colorSub
  rw [Finset.card_image_of_injOn bi, palette_card H.one] at bcount
  have matched (a) (ha : a∈R) (k0 : kr a=zero) : a∈near G base := by
    let diff := Finset.univ.filter (fun v=>G a v≠base v)
    have sub : diff⊆B := by
      intro v hv
      by_contra out
      apply (Finset.mem_filter.mp hv).2
      rw [rep]
      exact exterior H (Finset.singleton_subset_iff.mpr (rpin a ha)) (Finset.empty_subset _) _ (bpin v out) k0
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change diff.card≤2
    by_cases small : B.card≤2
    · exact (Finset.card_le_card sub).trans small
    · have cap := H.one
      have full : B.image kc=palette E := Finset.eq_of_subset_of_card_le colorSub (by
        rw [Finset.card_image_of_injOn bi,palette_card cap]; omega)
      have two : 2∈B.image kc := by rw [full]; unfold palette; split <;> decide
      obtain ⟨v,hv,top⟩:=Finset.mem_image.mp two
      have same : G a v=base v := by
        rw [rep]
        apply compare_worlds H (I:={q v,p a}) (J:={q v}) (fun _ _=>Iff.rfl) (fun _ _=>Iff.rfl)
        · intro w _ out
          simp [show w≠p a from fun e=>out (e.symm ▸ rpin a ha)]
        · exact masks H top (by simp)
      have without : diff⊆B.erase v := fun w h => Finset.mem_erase.mpr
        ⟨fun e => (Finset.mem_filter.mp h).2 (e.symm ▸ same), sub h⟩
      have bound := Finset.card_le_card without
      rw [Finset.card_erase_of_mem hv] at bound
      omega
  have sub : (R \ near G base).image kr ⊆ (palette E).erase zero := by
    intro k hk
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨inR,out⟩ := Finset.mem_sdiff.mp ha
    exact Finset.mem_erase.mpr ⟨fun z=>out (matched a inR z),rc a⟩
  have count := Finset.card_le_card sub
  rw [Finset.card_image_of_injOn (ri.mono (by intro a ha; exact (Finset.mem_sdiff.mp ha).1)),
    Finset.card_erase_of_mem baseMem,palette_card H.one] at count
  change (R \ near G base).card ≤ 1+E.card
  omega
end PEqualNP.Outside.L_meta_25799_aux.Local
namespace PEqualNP.Outside.L_meta_25799_aux.Local
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
open Cone Cone.Profile Cone.Profile.Wire
def rowBase (n m : Nat) (C : Circuit) (v : Fin m) := world (n+m) C {n+v.val} C.output
def colBase (n m : Nat) (C : Circuit) (a : Fin n) := world (n+m) C {a.val} C.output
def marked {n m} (G : Fin n → Fin m → Bool) (C : Circuit) : Finset Nat :=
  srcSet (near G (rowBase n m C)) (near (fun v a=>G a v) (colBase n m C))
lemma on_pair {n m G C} (rep : Represents (n:=n) (m:=m) G C) (a : Fin n) (v : Fin m) :
    G a v = world (n+m) C {n+v.val,a.val} C.output := by
  rw [←rep a v,eval_eq_val,oneEach_pt]
  unfold world
  congr 2
  funext i
  apply Bool.eq_iff_iff.mpr
  simp only [pt,Bool.or_eq_true,decide_eq_true_eq,Finset.mem_insert,Finset.mem_singleton]
  exact or_comm
lemma namedRow {n m} (R : Finset (Fin n)) (B : Finset (Fin m)) (a : Fin n) :
    a.val∈srcSet R B ↔ a∈R := by
  constructor
  · intro h
    rcases Finset.mem_union.mp h with l|r
    · obtain ⟨a',ha,e⟩:=Finset.mem_image.mp l
      exact (Fin.ext e : a'=a) ▸ ha
    · obtain ⟨v,_,e⟩:=Finset.mem_image.mp r
      change n+v.val=a.val at e
      have:=a.isLt; omega
  · exact fun h=>Finset.mem_union_left _ (Finset.mem_image_of_mem _ h)
lemma namedCol {n m} (R : Finset (Fin n)) (B : Finset (Fin m)) (v : Fin m) :
    n+v.val∈srcSet R B ↔ v∈B := by
  constructor
  · intro h
    rcases Finset.mem_union.mp h with l|r
    · obtain ⟨a,_,e⟩:=Finset.mem_image.mp l
      change a.val=n+v.val at e
      have:=a.isLt; omega
    · obtain ⟨v',hv,e⟩:=Finset.mem_image.mp r
      exact (Fin.ext (Nat.add_left_cancel e) : v'=v) ▸ hv
  · exact fun h=>Finset.mem_union_right _ (Finset.mem_image_of_mem _ h)
lemma small_regions {n m : Nat} {G : Fin n → Fin m → Bool} {C P E root} (R : Finset (Fin n)) (B : Finset (Fin m))
    (dr : ∀a b,a≠b → 6≤dist (G a) (G b))
    (dc : ∀v w,v≠w → 6≤dist (fun a=>G a v) (fun a=>G a w))
    (rep : Represents G C) (F : Frame (n+m) C P (srcSet R B) E root) (one : E.card≤1) :
    R.card+B.card≤6 := by
  rw [←srcCard]
  have cap {k : Nat} (low : k≤6) : WindowCap C P (srcSet R B) E k :=
    fun _ ht => forbiddenWindow (R:=R) (B:=B) cap51
      (fun a b h=>low.trans (dr a b h)) (fun v w h=>low.trans (dc v w h)) rep F ht
  by_cases em : E=∅
  · subst E
    exact (pure59 F (cap (k:=5) (by decide))).trans (by decide)
  · have pos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr em)
    obtain ⟨e,he⟩ := Finset.card_eq_one.mp (show E.card=1 by omega)
    subst E
    exact mixed62 F (cap (le_refl 6))
lemma local_cap {n m : Nat} {G : Fin n → Fin m → Bool} {C D E t} (R : Finset (Fin n)) (B : Finset (Fin m))
    (dr : ∀a b,a≠b → 6≤dist (G a) (G b))
    (dc : ∀v w,v≠w → 6≤dist (fun a=>G a v) (fun a=>G a w)) (rep : Represents G C)
    (H : Region51 (n+m) C (srcSet R B) D E t) (size : R.card+B.card≤6) :
    (srcSet R B \ marked G C).card ≤ 2+2*E.card := by
  let p := fun a : Fin n=>a.val
  let q := fun v : Fin m=>n+v.val
  let T := fun v a=>G a v
  have inR a : a∈R → p a∈srcSet R B := (namedRow R B a).mpr
  have inC v : v∈B → q v∈srcSet R B := (namedCol R B v).mpr
  have outR a : a∉R → p a∉srcSet R B := mt (namedRow R B a).mp
  have outC v : v∉B → q v∉srcSet R B := mt (namedCol R B v).mp
  have pval (a v) : G a v=world (n+m) C {q v,p a} C.output := on_pair rep a v
  have qval (v a) : T v a=world (n+m) C {p a,q v} C.output := by
    rw [Finset.pair_comm]; exact pval a v
  have kr := key_injective H p q R B inR outC G pval dr size
  have kc := key_injective H q p B R inC outR T qval dc (by omega)
  have first := bank_cap H p q R B inR outC G pval kr kc
  have last := bank_cap H q p B R inC outR T qval kc kr
  let X := near G (rowBase n m C)
  let Y := near T (colBase n m C)
  change (R \ X).card≤1+E.card at first
  change (B \ Y).card≤1+E.card at last
  have sub : srcSet R B \ marked G C ⊆ srcSet (R \ X) (B \ Y) := by
    intro w hw
    obtain ⟨inside,out⟩:=Finset.mem_sdiff.mp hw
    rcases Finset.mem_union.mp inside with left|right
    · obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp left
      exact (namedRow _ _ a).mpr (Finset.mem_sdiff.mpr ⟨ha,fun h=>out ((namedRow X Y a).mpr h)⟩)
    · obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp right
      exact (namedCol _ _ v).mpr (Finset.mem_sdiff.mpr ⟨hv,fun h=>out ((namedCol X Y v).mpr h)⟩)
  have bound:=Finset.card_le_card sub
  rw [srcCard] at bound
  omega
lemma split_sources {n m : Nat} {S : Finset Nat} (small : ∀w∈S,w<n+m) :
    ∃(R : Finset (Fin n)) (B : Finset (Fin m)), S=srcSet R B := by
  let R:=Finset.univ.filter (fun a : Fin n=>a.val∈S)
  let B:=Finset.univ.filter (fun v : Fin m=>n+v.val∈S)
  refine ⟨R,B,?_⟩
  ext w
  by_cases lo : w<n
  · change (⟨w,lo⟩ : Fin n).val∈S ↔ (⟨w,lo⟩ : Fin n).val∈srcSet R B
    exact (show w∈S ↔ (⟨w,lo⟩ : Fin n) ∈ R by simp [R]).trans (namedRow R B ⟨w,lo⟩).symm
  · by_cases hi : w<n+m
    · let v : Fin m:=⟨w-n,by omega⟩
      have eq : n+v.val=w := by dsimp [v]; omega
      rw [←eq, namedCol]
      simp [B]
    · exact iff_of_false (fun h=>hi (small w h)) (fun h=>hi (srcLow R B w h))
lemma frame_cap {n m : Nat} {G : Fin n → Fin m → Bool} {C P S E root} (dr : ∀a b,a≠b → 6≤dist (G a) (G b))
    (dc : ∀v w,v≠w → 6≤dist (fun a=>G a v) (fun a=>G a w)) (rep : Represents G C)
    (F : Frame (n+m) C P S E root) (one : E.card≤1) : (S \ marked G C).card ≤ 2+2*E.card := by
  classical
  by_cases high : n+m≤root
  · obtain ⟨R,B,shape⟩ := split_sources F.low
    subst S
    let N := n+m
    let S := srcSet R B
    let E' := subsetAt N C P E root
    let P' := gateSubset N C P root
    have ecount : E'.card≤E.card := Finset.card_le_card (Finset.filter_subset _ _)
    have back := subtree_boundary F F.rootIn high
    dsimp only at back
    rw [rootLeaves F] at back
    obtain ⟨sub,mem,entries,gates,out,raw,inner⟩ := back
    have eq : N+(root-N)=root := Nat.add_sub_of_le high
    have H : Region51 N C S P' E' (root-N) := by
      refine ⟨F.back,F.low,sub,mem,ecount.trans one,?_,gates,?_,raw,?_⟩
      · simpa only [eq,E',S,P',inner51,N] using entries
      · simpa only [eq,E',S,P',inner51,N] using out
      · simpa only [eq,E',S,P',inner51,N] using inner
    have lim := local_cap R B dr dc rep H (small_regions R B dr dc rep F one)
    omega
  · have sz := leaves_one_of_low F (top:=root) (by omega)
    rw [rootLeaves F] at sz
    have le := Finset.card_le_card (show S \ marked G C ⊆ S from Finset.sdiff_subset)
    omega
end PEqualNP.Outside.L_meta_25799_aux.Local
namespace PEqualNP.Outside.L_meta_25799_aux.Local
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
open Cone Cone.Profile Cone.Profile.Wire
lemma unread_world {N : Nat} {C : Circuit} (back : ReadsBack N C) {p : Nat}
    (off : Normal.Active C p=0) {X Y : Finset Nat} (same : ∀w, w≠p → (w∈X ↔ w∈Y)) :
    ∀w, w≠p → world N C X w=world N C Y w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro ne
    by_cases low : w<N
    · simp only [world_raw low,same w ne]
    by_cases high : N+C.size≤w
    · rw [world_past high,world_past high]
    have k : w-N<C.size := by omega
    have eq : N+(w-N)=w := by omega
    have h (v) (hv : v∈(gateAt C (w-N)).inputs) : world N C X v=world N C Y v := by
      have active := Normal.wire_positive k hv
      have earlier := back (w-N) k v hv
      apply ih v (by omega)
      rintro rfl; omega
    have left := world_step (X:=X) back (w-N) k
    have right := world_step (X:=Y) back (w-N) k
    rw [eq] at left right
    rw [left,right,List.map_congr_left h]
end PEqualNP.Outside.L_meta_25799_aux.Local
namespace PEqualNP.Outside.L_meta_25799_aux.Local
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
open Cone Cone.Profile Cone.Profile.Wire
lemma unread_at {n m : Nat} {G : Fin n→Fin m→Bool} {C : Circuit}
    (back : ReadsBack (n+m) C) (rep : Represents G C)
    {w : Nat} (hw : w<n+m) (off : Normal.Active C w=0) (different : C.output≠w) : w∈marked G C := by
  by_cases row : w<n
  · let a : Fin n := ⟨w,row⟩
    apply (namedRow _ _ a).mpr
    have eq (v : Fin m) : G a v=rowBase n m C v := by
      rw [on_pair rep]
      apply unread_world back off _ _ different
      intro z ne
      simp [a,ne]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simp [dist,eq]⟩
  · let v : Fin m := ⟨w-n,by omega⟩
    have p : n+v.val=w := by dsimp [v]; omega
    rw [←p]
    apply (namedCol _ _ v).mpr
    have eq (a : Fin n) : G a v=colBase n m C a := by
      rw [on_pair rep]
      apply unread_world back off _ _ different
      intro z ne
      simp [p,ne]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simp [dist,eq]⟩
lemma row_only (n m : Nat) (C : Circuit) (v : Fin m) :
    rowBase n m C v = C.eval (List.replicate n false ++ List.ofFn (fun x : Fin m=>decide (x=v))) := by
  change C.eval (List.ofFn (fun k : Fin (n+m)=>decide (k.val∈({n+v.val} : Finset Nat)))) = _
  congr 1
  rw [List.ofFn_add]
  have l : (fun k : Fin n=>decide ((k.castAdd m).val∈({n+v.val} : Finset Nat)))=(fun _=>false) := by
    funext k
    simp only [Fin.val_castAdd,Fin.coe_castLE,Finset.mem_singleton,decide_eq_false_iff_not]
    have := k.isLt; omega
  have r : (fun k : Fin m=>decide ((Fin.natAdd n k).val∈({n+v.val} : Finset Nat)))=(fun k=>decide (k=v)) := by
    funext k; simp [Fin.ext_iff]
  simp only [Fin.val_castAdd, Fin.coe_castLE] at l ⊢
  rw [l,r]; simp
lemma col_only (n m : Nat) (C : Circuit) (a : Fin n) :
    colBase n m C a = C.eval (List.ofFn (fun x : Fin n=>decide (x=a)) ++ List.replicate m false) := by
  change C.eval (List.ofFn (fun k : Fin (n+m)=>decide (k.val∈({a.val} : Finset Nat)))) = _
  congr 1
  rw [List.ofFn_add]
  have l : (fun k : Fin n=>decide ((k.castAdd m).val∈({a.val} : Finset Nat)))=(fun k=>decide (k=a)) := by
    funext k; simp [Fin.ext_iff]
  have r : (fun k : Fin m=>decide ((Fin.natAdd n k).val∈({a.val} : Finset Nat)))=(fun _=>false) := by
    funext k
    simp only [Fin.coe_natAdd,Finset.mem_singleton,decide_eq_false_iff_not]
    have := a.isLt; omega
  simp only [Fin.val_castAdd, Fin.coe_castLE] at l ⊢
  rw [l,r]; simp
end PEqualNP.Outside.L_meta_25799_aux.Local
theorem PEqualNP.Outside.L_meta_25799 : (∀ (n m : ℕ) (G : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit),
  let raw := n+m
  let gate := PEqualNP.MetaComplexity.NestedCover.gateAt C
  let reads := PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size)
  let rowBase := fun j : Fin m => C.eval (List.replicate n false ++
    List.ofFn (fun l : Fin m => decide (l = j)))
  let colBase := fun i : Fin n => C.eval (List.ofFn (fun l : Fin n => decide (l = i)) ++
    List.replicate m false)
  let nearR := Finset.univ.filter (fun i : Fin n =>
    (Finset.univ.filter (fun j : Fin m => G i j ≠ rowBase j)).card ≤ 2)
  let nearC := Finset.univ.filter (fun j : Fin m =>
    (Finset.univ.filter (fun i : Fin n => G i j ≠ colBase i)).card ≤ 2)
  let H := nearR.image (fun i => i.val) ∪ nearC.image (fun j => n+j.val)
  (∀ firstRow secondRow : Fin n, firstRow ≠ secondRow → 6 ≤ (Finset.univ.filter (fun col => G firstRow col ≠ G secondRow col)).card) →
  (∀ firstCol secondCol : Fin m, firstCol ≠ secondCol → 6 ≤ (Finset.univ.filter (fun row => G row firstCol ≠ G row secondCol)).card) →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack raw C →
  PEqualNP.Represents.Represents G C →
    nearR.card ≤ 1 ∧ nearC.card ≤ 1 ∧
    (∀ w < raw, w ≠ C.output → reads w = 0 → w ∈ H) ∧
    ∀ (S E region : Finset ℕ) (root : ℕ),
      let wires := S ∪ region.image (fun k => raw+k)
      let localReads := PEqualNP.MetaComplexity.NestedCover.readsIn C region
      S ⊆ Finset.range raw → E.card ≤ 1 → region ⊆ Finset.range C.size →
      root ∈ wires → localReads root = 0 →
      (∀ b ∈ E, b ∉ wires ∧ b < root ∧ localReads b = 1) →
      (∀ j ∈ region,
        ((gate j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
         (gate j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
        (gate j).inputs.length = 2 ∧ ∀ w ∈ (gate j).inputs, w ∈ wires ∨ w ∈ E) →
      (∀ w ∈ wires, w ≠ root → localReads w = 1 ∧ reads w = 1 ∧ C.output ≠ w) →
      (S \ H).card ≤ 2+2*E.card) := by
  intro n m G C raw gate reads rb cb nr nc H dr dc back rep
  have rb_eq : PEqualNP.Outside.L_meta_25799_aux.Local.rowBase n m C=rb := funext (PEqualNP.Outside.L_meta_25799_aux.Local.row_only n m C)
  have cb_eq : PEqualNP.Outside.L_meta_25799_aux.Local.colBase n m C=cb := funext (PEqualNP.Outside.L_meta_25799_aux.Local.col_only n m C)
  have nr_eq : PEqualNP.Outside.L_meta_25799_aux.Local.near G (PEqualNP.Outside.L_meta_25799_aux.Local.rowBase n m C)=nr := by rw [rb_eq]; rfl
  have nc_eq : PEqualNP.Outside.L_meta_25799_aux.Local.near (fun v a=>G a v) (PEqualNP.Outside.L_meta_25799_aux.Local.colBase n m C)=nc := by rw [cb_eq]; rfl
  have same : PEqualNP.Outside.L_meta_25799_aux.Local.marked G C=H := by
    unfold PEqualNP.Outside.L_meta_25799_aux.Local.marked; rw [nr_eq,nc_eq]
  refine ⟨nr_eq ▸ PEqualNP.Outside.L_meta_25799_aux.Local.near_small G _ dr,nc_eq ▸ PEqualNP.Outside.L_meta_25799_aux.Local.near_small (fun v a=>G a v) _ dc,?_,?_⟩
  · intro w hw no unread
    rw [←same]
    exact PEqualNP.Outside.L_meta_25799_aux.Local.unread_at back rep hw unread no.symm
  · intro S E P root wires localReads low one sub loc zero entries shape once
    rw [←same]
    apply PEqualNP.Outside.L_meta_25799_aux.Local.frame_cap dr dc rep (P:=P) (root:=root) _ one
    exact ⟨fun _ h=>Finset.mem_range.mp (low h),back,sub,loc,fun e h=>(entries e h).1,
      fun e h=>(entries e h).2.2,shape,zero,once⟩

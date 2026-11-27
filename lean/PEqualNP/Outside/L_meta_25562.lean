import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25562_aux.Profile.Wire


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

theorem wires_W (C : Circuit) (x : List Bool) : C.wires x = W C.gates x := rfl

theorem eval_W (C : Circuit) (x : List Bool) : C.eval x = (W C.gates x).getD C.output false := rfl

theorem circuitFun_W (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    circuitFun n C x = (W C.gates (List.ofFn x)).getD C.output false := rfl

theorem W_nil (w : List Bool) : W [] w = w := rfl

theorem W_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    W (g :: gs) w = W gs (step w g) := rfl

theorem W_single (g : Gate) (w : List Bool) : W [g] w = step w g := rfl

theorem W_append (a b : List Gate) (w : List Bool) : W (a ++ b) w = W b (W a w) := by
  simp [W, List.foldl_append]

theorem W_snoc (gs : List Gate) (g : Gate) (w : List Bool) : W (gs ++ [g]) w = step (W gs w) g := by
  rw [W_append]; rfl

theorem W_split (gs : List Gate) (w : List Bool) (j : ℕ) :
    W gs w = W (gs.drop j) (W (gs.take j) w) := by
  rw [← W_append, List.take_append_drop]

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

theorem W_snoc_getD (gs : List Gate) (g : Gate) (w : List Bool) (t : ℕ) :
    (W (gs ++ [g]) w).getD t false =
      if t = w.length + gs.length then g.op.eval (g.inputs.map fun i => (W gs w).getD i false)
      else (W gs w).getD t false := by
  rw [W_snoc]
  by_cases ht : t = w.length + gs.length
  · rw [if_pos ht, step_last _ _ _ (by rw [W_length]; exact ht)]
  · rw [if_neg ht]
    by_cases hlt : t < w.length + gs.length
    · exact step_lt _ _ _ (by rw [W_length]; exact hlt)
    · rw [getD_ge _ _ (by rw [step_len, W_length]; omega), getD_ge _ _ (by rw [W_length]; omega)]

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

theorem W_gate_pre (gs pre post : List Gate) (g : Gate) (w : List Bool)
    (h : gs = pre ++ g :: post) :
    (W gs w).getD (w.length + pre.length) false =
      g.op.eval (g.inputs.map fun i => (W pre w).getD i false) := by
  subst h
  rw [W_append, W_cons, W_prefix _ _ _ (by rw [step_len, W_length]; omega)]
  exact step_last _ _ _ (by rw [W_length])

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    (List.ofFn x).getD u false = x ⟨u, hu⟩ := by
  simp [List.getD_eq_getElem?_getD, hu]

theorem ofFn_getD_ge {n : ℕ} (x : Fin n → Bool) (u : ℕ) (hu : n ≤ u) :
    (List.ofFn x).getD u false = false := getD_ge _ _ (by simpa using hu)

theorem split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate), gs = pre ++ gs[j] :: post ∧ pre.length = j := by
  refine ⟨gs.take j, gs.drop (j + 1), ?_, by simp; omega⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

theorem split2 (gs : List Gate) : ∀ (j : ℕ) (g : Gate), gs[j]? = some g →
    ∃ pre post, pre.length = j ∧ gs = pre ++ g :: post ∧ ∀ g2, gs.set j g2 = pre ++ g2 :: post := by
  induction gs with
  | nil => intro j g h; simp at h
  | cons a gs ih =>
    intro j g h
    cases j with
    | zero =>
      have ha : a = g := by simpa using h
      subst ha
      exact ⟨[], gs, rfl, rfl, fun g2 => rfl⟩
    | succ j =>
      have h2 : gs[j]? = some g := by simpa using h
      obtain ⟨pre, post, hl, e1, e2⟩ := ih j g h2
      refine ⟨a :: pre, post, by rw [List.length_cons, hl], ?_, fun g2 => ?_⟩
      · exact congrArg (List.cons a) e1
      · exact congrArg (List.cons a) (e2 g2)

theorem step_congr (P : List Bool) (g1 g2 : Gate)
    (h : g1.op.eval (g1.inputs.map fun i => P.getD i false)
      = g2.op.eval (g2.inputs.map fun i => P.getD i false)) :
    step P g1 = step P g2 := by
  show P ++ [_] = P ++ [_]
  rw [h]

theorem gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

theorem gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

theorem gateAt_ge {C : Circuit} {j : ℕ} (hj : C.gates.length ≤ j) :
    gateAt C j = ⟨GateOp.or, []⟩ := by
  simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_none hj]

theorem getElem?_gateAt {C : Circuit} {j : ℕ} {g : Gate} (h : C.gates[j]? = some g) :
    gateAt C j = g ∧ j < C.gates.length := by
  have hj : j < C.gates.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at h; cases h
  refine ⟨?_, hj⟩
  rw [gateAt_eq hj]
  rw [List.getElem?_eq_getElem hj] at h
  exact Option.some.inj h

theorem eval_and_iff (l : List ℕ) (f : ℕ → Bool) :
    GateOp.and.eval (l.map f) = true ↔ ∀ i ∈ l, f i = true := by
  simp [GateOp.eval]

theorem eval_or_iff (l : List ℕ) (f : ℕ → Bool) :
    GateOp.or.eval (l.map f) = true ↔ ∃ i ∈ l, f i = true := by
  simp [GateOp.eval]

theorem eval_and2 (a b : Bool) : GateOp.and.eval [a, b] = (a && b) := by
  cases a <;> cases b <;> rfl

theorem eval_or2 (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by
  cases a <;> cases b <;> rfl

theorem eval_and1 (a : Bool) : GateOp.and.eval [a] = a := by cases a <;> rfl

theorem eval_or1 (a : Bool) : GateOp.or.eval [a] = a := by cases a <;> rfl

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

theorem eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

theorem circuitFun_val (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    circuitFun n C x = val C (List.ofFn x) C.output := rfl

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

end PEqualNP.Outside.L_meta_25562_aux.Profile.Wire

namespace PEqualNP.Outside.L_meta_25562_aux.Profile
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

end PEqualNP.Outside.L_meta_25562_aux.Profile

namespace PEqualNP.Outside.L_meta_25562_aux.Profile
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

end PEqualNP.Outside.L_meta_25562_aux.Profile

namespace PEqualNP.Outside.L_meta_25562_aux
open PEqualNP.Outside.L_meta_25562_aux.Profile in
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

end PEqualNP.Outside.L_meta_25562_aux

namespace PEqualNP.Outside.L_meta_25562_aux
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

end PEqualNP.Outside.L_meta_25562_aux

namespace PEqualNP.Outside.L_meta_25562_aux
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
end PEqualNP.Outside.L_meta_25562_aux

namespace PEqualNP.Outside.L_meta_25562_aux
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
end PEqualNP.Outside.L_meta_25562_aux

namespace PEqualNP.Outside.L_meta_25562_aux
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

end PEqualNP.Outside.L_meta_25562_aux


namespace PEqualNP.Outside.L_meta_25562_aux
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

end PEqualNP.Outside.L_meta_25562_aux

namespace PEqualNP.Outside.L_meta_25562_aux
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
end PEqualNP.Outside.L_meta_25562_aux

namespace PEqualNP.Outside.L_meta_25562_aux
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
end PEqualNP.Outside.L_meta_25562_aux

namespace PEqualNP.Outside.L_meta_25562_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
def ProfileWindows : Prop := ∀ {n m d : Nat} {G:Fin n→Fin m→Bool} (C:Circuit)
    (R:Finset (Fin n)) (B:Finset (Fin m)) (reg X:Finset Nat) (root:Nat),
    (∀a b:Fin n, a≠b → d≤(Finset.univ.filter (fun j=>G a j≠G b j)).card) →
    (∀i j:Fin m, i≠j → d≤(Finset.univ.filter (fun a=>G a i≠G a j)).card) →
    Represents G C → Frame (n+m) C reg (srcSet R B) X root →
    WindowCap (N:=n+m) C reg (srcSet R B) X d

theorem official62 (caps : ProfileWindows) : ∀ (n m : ℕ) (G : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit)
    (R : Finset (Fin n)) (B : Finset (Fin m)) (region : Finset ℕ) (root entry : ℕ),
  let raw := n + m
  let sources := R.image (fun sourceRow => sourceRow.val) ∪ B.image (fun sourceCol => n + sourceCol.val)
  let wires := sources ∪ region.image (fun gateIndex => raw + gateIndex)
  let gate := PEqualNP.MetaComplexity.NestedCover.gateAt C
  let localReads := PEqualNP.MetaComplexity.NestedCover.readsIn C region
  let allReads := PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size)
  (∀ a b : Fin n, a ≠ b → 6 ≤ (Finset.univ.filter (fun col => G a col ≠ G b col)).card) →
  (∀ i j : Fin m, i ≠ j → 6 ≤ (Finset.univ.filter (fun row => G row i ≠ G row j)).card) →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack raw C →
  PEqualNP.Represents.Represents G C → region ⊆ Finset.range C.size → root ∈ wires →
  entry ∉ wires → entry < root → localReads entry = 1 →
  (∀ k ∈ region,
    ((gate k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
     (gate k).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
    (gate k).inputs.length = 2 ∧ ∀ w ∈ (gate k).inputs, w ∈ wires ∨ w = entry) →
  localReads root = 0 →
  (∀ w ∈ wires, w ≠ root → localReads w = 1 ∧ allReads w = 1 ∧ C.output ≠ w) →
  R.card + B.card ≤ 6 := by
  intro n m G C R B reg root entry N S W gate localUse totalUse dr dc back rep rg rt outside before read binary zero once
  have F:Frame N C reg S {entry} root := by
    refine ⟨srcLow R B,back,rg,rt,?_,?_,?_,zero,once⟩
    · intro w hw;rw [Finset.mem_singleton.mp hw];exact outside
    · intro w hw;rw [Finset.mem_singleton.mp hw];exact read
    · intro j hj
      obtain ⟨op,len,mem⟩:=binary j hj
      refine ⟨op,len,?_⟩
      intro w hw;exact (mem w hw).imp_right (fun he=>Finset.mem_singleton.mpr he)
  have ans:=mixed62 F (caps C R B reg {entry} root dr dc rep F)
  simpa only [srcCard] using (show (srcSet R B).card≤6 from ans)
end PEqualNP.Outside.L_meta_25562_aux

open PEqualNP.Outside.L_meta_25562_aux in
theorem PEqualNP.Outside.L_meta_25562 : ∀ (n m : ℕ) (G : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit)
    (R : Finset (Fin n)) (B : Finset (Fin m)) (region : Finset ℕ) (root entry : ℕ),
  let raw := n + m
  let sources := R.image (fun sourceRow => sourceRow.val) ∪ B.image (fun sourceCol => n + sourceCol.val)
  let wires := sources ∪ region.image (fun gateIndex => raw + gateIndex)
  let gate := PEqualNP.MetaComplexity.NestedCover.gateAt C
  let localReads := PEqualNP.MetaComplexity.NestedCover.readsIn C region
  let allReads := PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size)
  (∀ a b : Fin n, a ≠ b → 6 ≤ (Finset.univ.filter (fun col => G a col ≠ G b col)).card) →
  (∀ i j : Fin m, i ≠ j → 6 ≤ (Finset.univ.filter (fun row => G row i ≠ G row j)).card) →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack raw C →
  PEqualNP.Represents.Represents G C → region ⊆ Finset.range C.size → root ∈ wires →
  entry ∉ wires → entry < root → localReads entry = 1 →
  (∀ k ∈ region,
    ((gate k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
     (gate k).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
    (gate k).inputs.length = 2 ∧ ∀ w ∈ (gate k).inputs, w ∈ wires ∨ w = entry) →
  localReads root = 0 →
  (∀ w ∈ wires, w ≠ root → localReads w = 1 ∧ allReads w = 1 ∧ C.output ≠ w) →
  R.card + B.card ≤ 6 := by
  apply official62
  intro n m d G C R B reg X root dr dc rep F t ht
  exact forbiddenWindow cap51 dr dc rep F ht

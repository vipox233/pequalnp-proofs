import Mathlib.Data.List.Perm.Subperm
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FinCases
import Mathlib.Data.List.GetD
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27697

open PEqualNP.CircuitLowerBounds

def pmValue (x : Fin 9 → Bool) : Bool :=
  ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) ||
   (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) ||
   (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))

def pmPush (ws : List Bool) (g : Gate) : List Bool :=
  ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]

def pmRun (gs : List Gate) (ws : List Bool) : List Bool := gs.foldl pmPush ws

theorem pmRun_len (gs : List Gate) (ws : List Bool) : (pmRun gs ws).length = ws.length+gs.length := by
  induction gs generalizing ws with
  | nil => simp [pmRun]
  | cons g gs ih =>
    change (pmRun gs (pmPush ws g)).length = _
    rw [ih]
    simp [pmPush]
    omega

theorem pmRun_skips (gs : List Gate) (k : Nat) (w v : List Bool)
    (hk : k ∉ gs.flatMap (fun g => g.inputs)) (hl : w.length = v.length)
    (he : ∀ i, i ≠ k → w.getD i false = v.getD i false) :
    ∀ i, i ≠ k → (pmRun gs w).getD i false = (pmRun gs v).getD i false := by
  induction gs generalizing w v with
  | nil => exact he
  | cons g gs ih =>
    have hg : k ∉ g.inputs := fun h => hk (by simp [h])
    have ht : k ∉ gs.flatMap (fun g => g.inputs) := fun h => hk (by simp [h])
    have hmap : (g.inputs.map fun j => w.getD j false) = (g.inputs.map fun j => v.getD j false) := by
      apply List.map_congr_left
      intro j hj
      exact he j (fun h => hg (h ▸ hj))
    apply ih (pmPush w g) (pmPush v g) ht (by simp [pmPush, hl])
    intro j hj
    by_cases hleft : j < w.length
    · have hright : j < v.length := by omega
      simpa [pmPush, List.getD_eq_getElem?_getD, List.getElem?_append_left hleft,
        List.getElem?_append_left hright] using he j hj
    · have hw : w.length ≤ j := by omega
      have hv : v.length ≤ j := by omega
      unfold pmPush
      rw [hmap]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hw,
        List.getElem?_append_right hv, hl]

def pmFirst : Gate := ⟨.or,[0,1]⟩
def pmSecond : Gate := ⟨.or,[3,9]⟩

def pmOff (k i : Fin 9) : Bool :=
  ([162,97,80,133,68,66,20,12,10] : List Nat).getD k.val 0 |>.testBit i.val

def pmOn (k i : Fin 9) : Bool :=
  ([163,99,84,141,84,98,84,140,266] : List Nat).getD k.val 0 |>.testBit i.val

theorem pmExamples : ∀ k : Fin 9,
    (∀ j : Fin 11, j.val ≠ k.val →
      (pmRun [pmFirst,pmSecond] (List.ofFn (pmOff k))).getD j.val false =
      (pmRun [pmFirst,pmSecond] (List.ofFn (pmOn k))).getD j.val false) ∧
    pmValue (pmOff k) ≠ pmValue (pmOn k) := by decide +kernel

theorem pmInputUses (C : Circuit) (hf : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = pmValue x)
    (hout : C.output + 1 = 9 + C.size)
    (hhd : C.gates.head? = some ⟨.or,[0,1]⟩)
    (hnext : C.gates.tail.head? = some ⟨.or,[3,9]⟩) :
    (∀ k, k < 9 → 1 ≤ (C.gates.flatMap (fun g => g.inputs)).count k) ∧
    (∀ k ∈ ([0,1,3] : List Nat), 2 ≤ (C.gates.flatMap (fun g => g.inputs)).count k) := by
  obtain ⟨gs,out⟩ := C
  cases gs with
  | nil => simp at hhd
  | cons a tl =>
    have ea : a = pmFirst := Option.some.inj hhd
    subst a
    cases tl with
    | nil => simp at hnext
    | cons b tl =>
      have eb : b = pmSecond := Option.some.inj hnext
      subst b
      have outBound : 11 ≤ out + 1 := by
        simp [Circuit.size] at hout
        omega
      have allUsed : ∀ k, k < 9 → 1 ≤ (tl.flatMap (fun g => g.inputs)).count k := by
        intro k hk
        let t : Fin 9 := ⟨k,hk⟩
        have ⟨agree,diff⟩ := pmExamples t
        have mem : k ∈ tl.flatMap (fun g => g.inputs) := by
          by_contra hn
          let u := pmRun [pmFirst,pmSecond] (List.ofFn (pmOff t))
          let v := pmRun [pmFirst,pmSecond] (List.ofFn (pmOn t))
          have lu : u.length=11 := by simp [u,pmRun_len]
          have lv : v.length=11 := by simp [v,pmRun_len]
          have same : ∀ j, j ≠ k → u.getD j false = v.getD j false := by
            intro j hj
            by_cases h : j < 11
            · exact agree ⟨j,h⟩ hj
            · have ha : u.length ≤ j := by omega
              have hb : v.length ≤ j := by omega
              simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none ha, List.getElem?_eq_none hb]
          have outEq := pmRun_skips tl k u v hn (lu.trans lv.symm) same out (by omega)
          exact diff ((hf (pmOff t)).symm.trans (outEq.trans (hf (pmOn t))))
        exact List.count_pos_iff.mpr mem
      constructor
      · intro k hk
        have h := allUsed k hk
        simp only [List.flatMap_cons, List.count_append]
        omega
      · intro k hk
        simp at hk
        rcases hk with rfl | rfl | rfl <;>
          first | (have h := allUsed 0 (by decide); simp [pmFirst,pmSecond] at *; omega)
                | (have h := allUsed 1 (by decide); simp [pmFirst,pmSecond] at *; omega)
                | (have h := allUsed 3 (by decide); simp [pmFirst,pmSecond] at *; omega)

end PEqualNP.Outside.L_meta_27697

namespace PEqualNP.Outside.L_meta_27697.Counts

open PEqualNP.CircuitLowerBounds

def slots (gs : List Gate) : List Nat := gs.flatMap (fun g => g.inputs)

theorem slotLength {gs : List Gate} (hfan : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (slots gs).length ≤ 2 * gs.length := by
  induction gs with
  | nil => simp [slots]
  | cons g gs ih =>
    have ht := ih (fun t ht => hfan t (List.mem_cons_of_mem _ ht))
    have hg := hfan g List.mem_cons_self
    change (g.inputs ++ slots gs).length ≤ _
    rw [List.length_append, List.length_cons]
    omega

theorem saturated {gs : List Gate} (hfan : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (hsize : (slots gs).length = 2 * gs.length) :
    ∀ g ∈ gs, g.inputs.length = 2 := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have ht : ∀ t ∈ gs, t.inputs.length ≤ 2 := fun t ht => hfan t (List.mem_cons_of_mem _ ht)
    have htl := slotLength ht
    have hg := hfan g List.mem_cons_self
    change (g.inputs ++ slots gs).length = _ at hsize
    rw [List.length_append, List.length_cons] at hsize
    have htail := ih ht (by omega)
    intro t h
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · exact htail t h

theorem slot_counts (gs : List Gate) (hpos : 0 < gs.length) (hsize : gs.length ≤ 11)
    (hfan : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (hraw : ∀ w, w < 9 → 1 ≤ (slots gs).count w)
    (hdbl : ∀ w ∈ ([0, 1, 3] : List Nat), 2 ≤ (slots gs).count w)
    (hlive : ∀ j : Fin gs.length, j.val + 1 < gs.length →
      ∃ k : Fin gs.length, j.val < k.val ∧ 9 + j.val ∈ (gs.get k).inputs) :
    gs.length = 11 ∧ (∀ w, w ≠ 0 → w ≠ 1 → w ≠ 3 → (slots gs).count w ≤ 1) ∧
      ∀ g ∈ gs, g.inputs.length = 2 := by
  let required := ([0, 1, 3] : List Nat) ++ List.range (8 + gs.length)
  have hbase : ∀ w < 8 + gs.length, 1 ≤ (slots gs).count w := by
    intro w hw
    by_cases hsmall : w < 9
    · exact hraw w hsmall
    · let j : Fin gs.length := ⟨w-9, by omega⟩
      obtain ⟨k, _, hk⟩ := hlive j (by dsimp [j]; omega)
      have hj : 9 + j.val = w := by dsimp [j]; omega
      rw [hj] at hk
      have hm : w ∈ slots gs := List.mem_flatMap.mpr ⟨gs.get k, List.get_mem _ _, hk⟩
      exact List.count_pos_iff.mpr hm
  have hsub : List.Subperm required (slots gs) := by
    apply List.subperm_iff_count.mpr
    intro w
    by_cases hw : w ∈ ([0, 1, 3] : List Nat)
    · have hd := hdbl w hw
      have hnod : ([0, 1, 3] : List Nat).Nodup := by decide
      simp only [required, List.count_append, hnod.count_of_mem hw, List.count_range]
      split <;> omega
    · simp only [required, List.count_append, List.count_eq_zero_of_not_mem hw, Nat.zero_add,
        List.count_range]
      split
      · exact hbase w (by assumption)
      · omega
  have l1 := hsub.length_le
  have l2 := slotLength hfan
  have rl : required.length = 11 + gs.length := by simp [required]; omega
  rw [rl] at l1
  have eqn : gs.length = 11 := by omega
  have p := hsub.perm_of_length_le (by omega)
  refine ⟨eqn, ?_, saturated hfan (by omega)⟩
  intro w h0 h1 h3
  rw [← List.perm_iff_count.mp p w]
  have hmem : w ∉ ([0, 1, 3] : List Nat) := by simp [h0, h1, h3]
  simp only [required, List.count_append, List.count_eq_zero_of_not_mem hmem, Nat.zero_add,
    List.count_range]
  split <;> omega

end PEqualNP.Outside.L_meta_27697.Counts

namespace PEqualNP.Outside.L_meta_27697.Unroll

inductive Expr where
  | var (i : Nat)
  | both (a b : Expr)
  | either (a b : Expr)

def ev (e : Expr) (f : Nat → Bool) : Bool :=
  match e with
  | .var i => f i
  | .both a b => ev a f && ev b f
  | .either a b => ev a f || ev b f

def occ (e : Expr) (w : Nat) : Nat :=
  match e with
  | .var i => if i = w then 1 else 0
  | .both a b => occ a w + occ b w
  | .either a b => occ a w + occ b w

end PEqualNP.Outside.L_meta_27697.Unroll

namespace PEqualNP.Outside.L_meta_27697

abbrev Point := Fin 4 → Bool

inductive RO : Finset (Fin 4) → (Point → Bool) → Prop where
  | const (b : Bool) : RO ∅ (fun _ => b)
  | var (i : Fin 4) : RO {i} (fun x => x i)
  | neg {s f} : RO s f → RO s (fun x => !(f x))
  | and {s t f g} : Disjoint s t → RO s f → RO t g → RO (s ∪ t) (fun x => f x && g x)
  | or {s t f g} : Disjoint s t → RO s f → RO t g → RO (s ∪ t) (fun x => f x || g x)

def depends (s : Finset (Fin 4)) (f : Point → Bool) : Prop :=
  ∀ x y, (∀ i ∈ s, x i = y i) → f x = f y

theorem RO.dep {s f} (hf : RO s f) : depends s f := by
  induction hf with
  | const => intro x y h; rfl
  | var i => intro x y h; exact h i (by simp)
  | neg _ ih => intro x y h; simp only [ih x y h]
  | and _ _ _ ih jh =>
    intro x y h
    dsimp only
    rw [ih x y (fun i hi => h i (Finset.mem_union_left _ hi)),
      jh x y (fun i hi => h i (Finset.mem_union_right _ hi))]
  | or _ _ _ ih jh =>
    intro x y h
    dsimp only
    rw [ih x y (fun i hi => h i (Finset.mem_union_left _ hi)),
      jh x y (fun i hi => h i (Finset.mem_union_right _ hi))]

def path4 (x : Point) : Bool :=
  (x 1 && x 3) || (x 1 && x 2) || (x 0 && x 3)

def polarity (p : Bool) (x : Point) : Bool := if p then !(path4 x) else path4 x

def crossPoint (s : Finset (Fin 4)) (x y : Point) : Point :=
  fun i => if i ∈ s then x i else y i

theorem path_rectangles : ∀ (s : Finset (Fin 4)) (p k : Bool), s ≠ ∅ → s ≠ Finset.univ →
    ∃ x y : Point, polarity p x = k ∧ polarity p y = k ∧ polarity p (crossPoint s x y) ≠ k := by
  decide +kernel

theorem path_not_const : ∀ c p : Bool, (fun _ : Point => c) ≠ polarity p := by decide +kernel

theorem path_not_var : ∀ (i : Fin 4) (p : Bool), (fun x : Point => x i) ≠ polarity p := by decide +kernel

def combine (k a b : Bool) : Bool := if k then a && b else a || b

theorem comb_extreme (k a b : Bool) : combine k a b = k ↔ a=k ∧ b=k := by
  cases k <;> cases a <;> cases b <;> decide

theorem comb_neutral (k a : Bool) : combine k k a = a := by cases k <;> cases a <;> decide

theorem comb_absorb (k a : Bool) : combine k (!k) a = !k := by cases k <;> cases a <;> decide

theorem comb_comm (k a b : Bool) : combine k a b = combine k b a := by
  cases k <;> cases a <;> cases b <;> decide

theorem no_const_split {f g : Point → Bool} (hf : depends ∅ f)
    (other : ∀ p, g ≠ polarity p) (k p : Bool) :
    (fun x => combine k (f x) (g x)) ≠ polarity p := by
  intro he
  let c := f (fun _ => false)
  have hc (x) : f x = c := hf _ _ (by simp)
  by_cases hk : c = k
  · apply other p
    funext x
    simpa only [hc, hk, comb_neutral] using congrFun he x
  · have switch (a d : Bool) : a ≠ d → a = !d := by cases a <;> cases d <;> decide
    have hneg : c = !k := switch c k hk
    apply path_not_const (!k) p
    funext x
    simpa only [hc, hneg, comb_absorb] using congrFun he x

theorem no_split {s t f g} (dis : Disjoint s t) (hf : depends s f) (hg : depends t g)
    (exf : ∀ p, f ≠ polarity p) (exg : ∀ p, g ≠ polarity p) (k p : Bool) :
    (fun x => combine k (f x) (g x)) ≠ polarity p := by
  by_cases hs : s=∅
  · subst s
    exact no_const_split hf exg k p
  by_cases hs' : s=Finset.univ
  · subst s
    have ht : t = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      exact Finset.disjoint_left.mp dis (Finset.mem_univ i) hi
    subst t
    intro he
    apply no_const_split hg exf k p
    exact (funext fun x => comb_comm k (g x) (f x)).trans he
  intro he
  obtain ⟨x,y,hx,hy,hcross⟩ := path_rectangles s p k hs hs'
  have ha := (comb_extreme k (f x) (g x)).mp ((congrFun he x).trans hx)
  have hb := (comb_extreme k (f y) (g y)).mp ((congrFun he y).trans hy)
  apply hcross
  rw [← congrFun he (crossPoint s x y)]
  apply (comb_extreme _ _ _).mpr
  constructor
  · exact (hf _ x (fun i hi => by simp [crossPoint, hi])).trans ha.1
  · apply Eq.trans (hg _ y ?_) hb.2
    intro i hi
    have hn : i ∉ s := fun h => Finset.disjoint_left.mp dis h hi
    simp [crossPoint, hn]

theorem RO.not_polarity {s f} (hf : RO s f) : ∀ p, f ≠ polarity p := by
  induction hf with
  | const c => exact path_not_const c
  | var i => exact path_not_var i
  | @neg s f _ ih =>
    intro p h
    apply ih (!p)
    funext x
    have eq := congrFun h x
    cases p <;> cases hx : f x <;> cases hy : path4 x <;> simp_all [polarity]
  | and dis a b iha ihb => exact no_split dis a.dep b.dep iha ihb true
  | or dis a b iha ihb => exact no_split dis a.dep b.dep iha ihb false

theorem no_readonce_path (s : Finset (Fin 4)) : ¬ RO s path4 :=
  fun h => h.not_polarity false rfl

end PEqualNP.Outside.L_meta_27697

namespace PEqualNP.Outside.L_meta_27697.Restriction

open Unroll

def src (i : Fin 4) : Nat :=
  if i = 0 then 2 else if i = 1 then 5 else if i = 2 then 6 else 7

def activeRead (w : Nat) (u : Point) : Bool :=
  if w = 2 then u 0 else if w = 5 then u 1 else if w = 6 then u 2 else if w = 7 then u 3
  else decide (w = 0 ∨ w = 1 ∨ w = 3)

def support : Expr → Finset (Fin 4)
  | .var w => Finset.univ.filter (fun i => src i = w)
  | .both a b => support a ∪ support b
  | .either a b => support a ∪ support b

theorem mem_support (e : Expr) (i : Fin 4) : i ∈ support e ↔ 0 < occ e (src i) := by
  induction e with
  | var w =>
    by_cases h : w = src i
    · simp [support, occ, h]
    · simp [support, occ, h, Ne.symm h]
  | both a b ha hb => simp only [support, Finset.mem_union, ha, hb, occ]; omega
  | either a b ha hb => simp only [support, Finset.mem_union, ha, hb, occ]; omega

theorem leaf_ro (w : Nat) : RO (support (.var w)) (fun u => activeRead w u) := by
  by_cases h2 : w = 2
  · subst w
    have hs : support (.var 2) = {0} := by decide +kernel
    rw [hs]
    exact RO.var 0
  by_cases h5 : w = 5
  · subst w
    have hs : support (.var 5) = {1} := by decide +kernel
    rw [hs]
    exact RO.var 1
  by_cases h6 : w = 6
  · subst w
    have hs : support (.var 6) = {2} := by decide +kernel
    rw [hs]
    exact RO.var 2
  by_cases h7 : w = 7
  · subst w
    have hs : support (.var 7) = {3} := by decide +kernel
    rw [hs]
    exact RO.var 3
  have hs : support (.var w) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    have hx : src i = w := (Finset.mem_filter.mp hi).2
    have possible : src i = 2 ∨ src i = 5 ∨ src i = 6 ∨ src i = 7 := by
      fin_cases i <;> decide
    omega
  rw [hs]
  simpa only [activeRead, ite_eq_right h2, ite_eq_right h5, ite_eq_right h6, ite_eq_right h7] using
    RO.const (decide (w = 0 ∨ w = 1 ∨ w = 3))

theorem supports_disjoint {a b : Expr} (h : ∀ i : Fin 4, occ a (src i) + occ b (src i) ≤ 1) :
    Disjoint (support a) (support b) := by
  apply Finset.disjoint_left.mpr
  intro i ha hb
  have := h i
  have := (mem_support a i).mp ha
  have := (mem_support b i).mp hb
  omega

theorem restrict_ro (e : Expr) (h : ∀ i : Fin 4, occ e (src i) ≤ 1) :
    RO (support e) (fun u => ev e (fun w => activeRead w u)) := by
  induction e with
  | var w => exact leaf_ro w
  | both a b ha hb =>
    change ∀ i : Fin 4, occ a (src i) + occ b (src i) ≤ 1 at h
    apply RO.and (supports_disjoint h)
    · exact ha (fun i => by have := h i; omega)
    · exact hb (fun i => by have := h i; omega)
  | either a b ha hb =>
    change ∀ i : Fin 4, occ a (src i) + occ b (src i) ≤ 1 at h
    apply RO.or (supports_disjoint h)
    · exact ha (fun i => by have := h i; omega)
    · exact hb (fun i => by have := h i; omega)

theorem lookup (u : Point) (w : Nat) (hw : w < 9) :
    (List.ofFn (fun i : Fin 9 => activeRead i.val u)).getD w false = activeRead w u := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hw)]
  simp only [Option.getD_some, List.getElem_ofFn]

theorem path_restrict (u : Point) :
    let x := fun i : Fin 9 => activeRead i.val u
    ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
      (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)) = path4 u := by
  simp [activeRead, path4]

end PEqualNP.Outside.L_meta_27697.Restriction

namespace PEqualNP.Outside.L_meta_27697.Unroll

open PEqualNP.CircuitLowerBounds

def sub (e : Expr) (n : Nat) (r : Expr) : Expr :=
  match e with
  | .var i => if i = n then r else .var i
  | .both a b => .both (sub a n r) (sub b n r)
  | .either a b => .either (sub a n r) (sub b n r)

def Binary (g : Gate) : Prop :=
  ∃ a b : Nat, g = ⟨.and, [a, b]⟩ ∨ g = ⟨.or, [a, b]⟩

def gexpr (g : Gate) : Expr :=
  match g.op, g.inputs with
  | .and, [a, b] => .both (.var a) (.var b)
  | .or, [a, b] => .either (.var a) (.var b)
  | _, _ => .var 0

def unroll (n : Nat) (gs : List Gate) (out : Nat) : Expr :=
  match gs with
  | [] => .var out
  | g :: tail => sub (unroll (n + 1) tail out) n (gexpr g)

end PEqualNP.Outside.L_meta_27697.Unroll

namespace PEqualNP.Outside.L_meta_27697.Unroll

open PEqualNP.CircuitLowerBounds

theorem occ_sub (e : Expr) (n : Nat) (r : Expr) (w : Nat) (hw : w ≠ n) :
    occ (sub e n r) w = occ e w + occ e n * occ r w := by
  induction e with
  | var i =>
    by_cases hi : i = n
    · subst i
      simp [sub, occ, Ne.symm hw]
    · simp [sub, occ, hi]
  | both a b ha hb =>
    simp only [sub, occ, ha, hb, Nat.add_mul]
    omega
  | either a b ha hb =>
    simp only [sub, occ, ha, hb, Nat.add_mul]
    omega

theorem occ_gexpr (g : Gate) (hb : Binary g) (w : Nat) :
    occ (gexpr g) w = g.inputs.count w := by
  obtain ⟨a, b, rfl | rfl⟩ := hb <;>
    by_cases ha : a = w <;> by_cases hb : b = w <;> simp [occ, gexpr, ha, hb]

theorem occ_unroll (n : Nat) (gs : List Gate) (out : Nat) (hb : ∀ g ∈ gs, Binary g)
    (hcap : ∀ i, n ≤ i → (gs.flatMap Gate.inputs).count i + (if i = out then 1 else 0) ≤ 1)
    (w : Nat) (hw : w < n) :
    occ (unroll n gs out) w ≤ (gs.flatMap Gate.inputs).count w + (if w = out then 1 else 0) := by
  induction gs generalizing n w with
  | nil =>
    by_cases h : w = out
    · subst w
      simp [unroll, occ]
    · simp [unroll, occ, h, Ne.symm h]
  | cons g gs ih =>
    have hg : Binary g := hb g (by simp)
    have hgs : ∀ x ∈ gs, Binary x := fun x hx => hb x (by simp [hx])
    have ht : ∀ i, n ≤ i → (gs.flatMap Gate.inputs).count i + (if i = out then 1 else 0) ≤ 1 := by
      intro i hi
      have h := hcap i hi
      simp only [List.flatMap_cons, List.count_append] at h
      omega
    have hc : ∀ i, n + 1 ≤ i → (gs.flatMap Gate.inputs).count i + (if i = out then 1 else 0) ≤ 1 :=
      fun i hi => ht i (by omega)
    have hn := ih (n + 1) hgs hc n (by omega)
    have hsingle : occ (unroll (n + 1) gs out) n ≤ 1 := le_trans hn (ht n (by omega))
    have hraw := ih (n + 1) hgs hc w (by omega)
    simp only [unroll, occ_sub _ _ _ _ (Nat.ne_of_lt hw), occ_gexpr _ hg, List.flatMap_cons,
      List.count_append]
    rcases (show occ (unroll (n + 1) gs out) n = 0 ∨ occ (unroll (n + 1) gs out) n = 1 by omega) with hz | ho
    · rw [hz, Nat.zero_mul]
      omega
    · rw [ho, Nat.one_mul]
      omega

end PEqualNP.Outside.L_meta_27697.Unroll

namespace PEqualNP.Outside.L_meta_27697.Unroll

open PEqualNP.CircuitLowerBounds

theorem ev_sub (e : Expr) (n : Nat) (r : Expr) (f : Nat → Bool) :
    ev (sub e n r) f = ev e (fun i => if i = n then ev r f else f i) := by
  induction e with
  | var i => by_cases h : i = n <;> simp [sub, ev, h]
  | both a b ia ib => simp only [sub, ev, ia, ib]
  | either a b ia ib => simp only [sub, ev, ia, ib]

theorem ev_gexpr (g : Gate) (f : Nat → Bool) (hg : Binary g) :
    ev (gexpr g) f = g.op.eval (g.inputs.map f) := by
  obtain ⟨a, b, rfl | rfl⟩ := hg <;> simp [gexpr, ev, GateOp.eval]

theorem getD_snoc_wire (x : List Bool) (v : Bool) (i : Nat) :
    (x ++ [v]).getD i false = if i = x.length then v else x.getD i false := by
  by_cases he : i = x.length
  · subst i
    simp [List.getD_eq_getElem?_getD]
  · rw [ite_eq_right he]
    rcases lt_or_gt_of_ne he with h | h
    · exact List.getD_append _ _ _ _ h
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ h.le]

theorem ev_list (gs : List Gate) (x : List Bool) (out : Nat) (hb : ∀ g ∈ gs, Binary g) :
    ev (unroll x.length gs out) (fun i => x.getD i false) = (Circuit.mk gs out).eval x := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    let b := g.op.eval (g.inputs.map fun i => x.getD i false)
    let next := x ++ [b]
    have he : (fun i => if i=x.length then b else x.getD i false) = (fun i => next.getD i false) :=
      funext fun i => (getD_snoc_wire x b i).symm
    have hlen : next.length = x.length + 1 := by simp [next]
    rw [unroll, ev_sub, ev_gexpr g _ (hb g List.mem_cons_self)]
    change ev (unroll (x.length+1) gs out) (fun i => if i=x.length then b else x.getD i false) = _
    rw [he, ← hlen]
    exact ih next (fun g' hg' => hb g' (List.mem_cons_of_mem _ hg'))

theorem ev_unroll (C : Circuit) (x : List Bool) (hb : ∀ g ∈ C.gates, Binary g) :
    ev (unroll x.length C.gates C.output) (fun i => x.getD i false) = C.eval x :=
  ev_list C.gates x C.output hb

end PEqualNP.Outside.L_meta_27697.Unroll

namespace PEqualNP.Outside.L_meta_27697

open PEqualNP.CircuitLowerBounds

def pmNormal (C : Circuit) : Prop :=
  ∀ j : Fin C.gates.length,
    ((C.gates.get j).op = .not ∧
      ∃ a, a < 9+j.val ∧ (C.gates.get j).inputs = [a]) ∨
    (((C.gates.get j).op = .and ∨ (C.gates.get j).op = .or) ∧
      ∃ a b, a < b ∧ b < 9+j.val ∧ (C.gates.get j).inputs = [a,b])

theorem pmGateEq {g : Gate} {op : GateOp} {ins : List Nat}
    (ho : g.op=op) (hi : g.inputs=ins) : g=⟨op,ins⟩ := by cases g; simp_all

theorem pmNoOutputRead (C : Circuit) (hn : pmNormal C) (hout : C.output+1=9+C.size) :
    C.output ∉ Counts.slots C.gates := by
  intro hm
  obtain ⟨g,hg,hmem⟩ := List.mem_flatMap.mp hm
  obtain ⟨j,rfl⟩ := List.mem_iff_get.mp hg
  have hj := j.isLt
  change C.output+1=9+C.gates.length at hout
  rcases hn j with ⟨_,a,ha,hi⟩ | ⟨_,a,b,hab,hb,hi⟩
  · rw [hi] at hmem
    simp only [List.mem_singleton] at hmem
    omega
  · rw [hi] at hmem
    simp at hmem
    omega

theorem pmBridge (C : Circuit) (hfan : PEqualNP.MetaComplexity.FanInTwo C)
    (hsize : C.size ≤ 11)
    (hf : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = pmValue x)
    (hout : C.output + 1 = 9 + C.size)
    (hn : pmNormal C)
    (hlive : ∀ j : Fin C.gates.length, j.val+1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9+j.val ∈ (C.gates.get k).inputs)
    (hhd : C.gates.head? = some ⟨.or,[0,1]⟩)
    (hnext : C.gates.tail.head? = some ⟨.or,[3,9]⟩) :
    (∀ g ∈ C.gates, ∃ a b : Nat, g=⟨.and,[a,b]⟩ ∨ g=⟨.or,[a,b]⟩) ∧
      (∀ i, 9 ≤ i → (C.gates.flatMap Gate.inputs).count i + (if i=C.output then 1 else 0) ≤ 1) ∧
      (∀ i, i < 9 → i ≠ 0 → i ≠ 1 → i ≠ 3 →
        (C.gates.flatMap Gate.inputs).count i + (if i=C.output then 1 else 0) ≤ 1) := by
  have hp : 0 < C.gates.length := by
    cases hs : C.gates with
    | nil => simp [hs] at hhd
    | cons => simp
  obtain ⟨raw,dbl⟩ := pmInputUses C hf hout hhd hnext
  obtain ⟨hlen,hcap,hpair⟩ := Counts.slot_counts C.gates hp hsize
    (fun g hg => (hfan g hg).2) raw dbl hlive
  have eout := pmNoOutputRead C hn hout
  change C.output+1=9+C.gates.length at hout
  refine ⟨?_,?_,?_⟩
  · intro g hg
    have hl := hpair g hg
    obtain ⟨j,rfl⟩ := List.mem_iff_get.mp hg
    rcases hn j with ⟨_,a,ha,hi⟩ | ⟨ho,a,b,hab,hb,hi⟩
    · change (C.gates.get j).inputs.length = 2 at hl
      rw [hi] at hl
      simp at hl
    · refine ⟨a,b,?_⟩
      rcases ho with ho | ho
      · exact Or.inl (pmGateEq ho hi)
      · exact Or.inr (pmGateEq ho hi)
  · intro i hi
    by_cases he : i=C.output
    · subst i
      change (Counts.slots C.gates).count C.output + _ ≤ 1
      simp [List.count_eq_zero_of_not_mem eout]
    · simpa [he,Counts.slots] using hcap i (by omega) (by omega) (by omega)
  · intro i hi h0 h1 h3
    have ne : i ≠ C.output := by omega
    simpa [ne,Counts.slots] using hcap i h0 h1 h3

end PEqualNP.Outside.L_meta_27697

open PEqualNP.Outside.L_meta_27697

theorem PEqualNP.Outside.L_meta_27697 : (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))) ∧
    C.output + 1 = 9 + C.size ∧
    (∀ j : Fin C.gates.length,
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
    (∀ j : Fin C.gates.length,
      (∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
      ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
    (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 9]⟩)) := by
  rintro ⟨C,hfan,hsize,hf,hout,hn,_,hlive,hhd,hnext⟩
  obtain ⟨binary,capacity,raw⟩ := pmBridge C hfan hsize hf hout hn hlive hhd hnext
  have hb : ∀ g ∈ C.gates, Unroll.Binary g := binary
  let e := Unroll.unroll 9 C.gates C.output

  have sourceBounds : ∀ i : Fin 4, Restriction.src i < 9 ∧ Restriction.src i ≠ 0 ∧
      Restriction.src i ≠ 1 ∧ Restriction.src i ≠ 3 := by decide +kernel
  have hro := Restriction.restrict_ro e (fun i => by
    obtain ⟨hi,h0,h1,h3⟩ := sourceBounds i
    exact le_trans (Unroll.occ_unroll 9 C.gates C.output hb capacity _ hi)
      (raw _ hi h0 h1 h3))
  have equations : (fun u => Unroll.ev e (fun w => Restriction.activeRead w u)) = path4 := by
    funext u
    let x : Fin 9 → Bool := fun i => Restriction.activeRead i.val u
    have look : (fun w => (List.ofFn x).getD w false) = (fun w => Restriction.activeRead w u) := by
      funext w
      by_cases hw : w < 9
      · exact Restriction.lookup u w hw
      · have hl : (List.ofFn x).length ≤ w := by simpa using Nat.le_of_not_gt hw
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hl]
        simp [Restriction.activeRead,
          show w ≠ 0 by omega, show w ≠ 1 by omega, show w ≠ 2 by omega,
          show w ≠ 3 by omega, show w ≠ 5 by omega, show w ≠ 6 by omega, show w ≠ 7 by omega]
    calc
      Unroll.ev e (fun w => Restriction.activeRead w u) =
          Unroll.ev e (fun w => (List.ofFn x).getD w false) := congrArg (Unroll.ev e) look.symm
      _ = C.eval (List.ofFn x) := by simpa only [e,List.length_ofFn] using Unroll.ev_unroll C (List.ofFn x) hb
      _ = pmValue x := hf x
      _ = path4 u := Restriction.path_restrict u
  rw [equations] at hro
  exact no_readonce_path _ hro

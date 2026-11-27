import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25615_aux.CircuitPart.Cut
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
open scoped Classical
def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

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
  exact List.map_congr_left fun i hi => ite_eq_left (hb j hj i hi)

theorem past (gs : List Gate) (x : List Bool) (i : ℕ) (hi : x.length + gs.length ≤ i) :
    (run gs x).getD i false = false :=
  List.getD_eq_default _ _ (by rw [run_length]; exact hi)

theorem oneEach_length {n m : ℕ} (u : Fin n) (v : Fin m) :
    (PEqualNP.Represents.oneEach u v).length = n + m := by
  simp [PEqualNP.Represents.oneEach]

theorem oneEach_getD {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) :
    (PEqualNP.Represents.oneEach u v).getD i false = decide (i = u.val ∨ i = n + v.val) := by
  unfold PEqualNP.Represents.oneEach
  rw [List.getD_eq_getElem?_getD]
  by_cases h : i < n
  · rw [List.getElem?_append_left (by simpa using h)]
    simp only [List.getElem?_ofFn]
    simp [h, Fin.ext_iff]
    omega
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_ofFn, List.getElem?_ofFn]
    by_cases h2 : i - n < m
    · simp [h2, Fin.ext_iff]
      have hu : ¬ i = u.val := by omega
      by_cases hv : i = n + v.val
      · simp [hv]
      · have hv' : ¬ i - n = v.val := by omega
        simp [hu, hv, hv']
    · simp [h2]
      omega

def inside (N : ℕ) (region : Finset ℕ) (w : ℕ) : Prop := N≤w ∧ w-N∈region
def V (C : Circuit) (x : List Bool) (i : ℕ) := (run C.gates x).getD i false

structure Layout (N : ℕ) (C : Circuit) (src reg ent : Finset ℕ) (top : ℕ) : Prop where
  back : ReadsBack N C
  valid : reg ⊆ Finset.range C.size
  member : top∈reg
  one : ent.card≤1
  ports : ∀ w∈ent, w<N+top ∧ w∉src ∧ ¬inside N reg w
  interior : ∀ j∈reg, ((gateAt C j).op=.and ∨ (gateAt C j).op=.or) ∧
    ∀ w∈(gateAt C j).inputs, w∈src ∨ inside N reg w ∨ w∈ent
  exterior : ∀ j<C.size, j∉reg → ∀ w∈(gateAt C j).inputs, w∉src ∧ (inside N reg w → w=N+top)
  output : C.output∉src
  visible : inside N reg C.output → C.output=N+top

variable {N top : ℕ} {C : Circuit} {src reg ent : Finset ℕ}

theorem gate_mono (g : Gate) (op : g.op=.and ∨ g.op=.or) {x y : ℕ → Bool}
    (le : ∀ i∈g.inputs, x i=true → y i=true) :
    g.op.eval (g.inputs.map x)=true → g.op.eval (g.inputs.map y)=true := by
  rcases op with op|op <;> rw [op]
  · simp only [GateOp.eval,List.all_map,List.all_eq_true,Function.comp_apply,id]
    exact fun h i hi => le i hi (h i hi)
  · simp only [GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id]
    rintro ⟨i,hi,h⟩; exact ⟨i,hi,le i hi h⟩

theorem inside_mono (L : Layout N C src reg ent top) (x y : List Bool) (hx : x.length=N) (hy : y.length=N)
    (hs : ∀ i∈src, V C x i=true → V C y i=true) (he : ∀ i∈ent, V C x i=true → V C y i=true) :
    ∀ i, inside N reg i → V C x i=true → V C y i=true := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    rintro ⟨ge,mem⟩
    let j := i-N
    have jmem : j∈reg := mem
    have jlen : j<C.gates.length := Finset.mem_range.mp (L.valid jmem)
    have idx : N+j=i := Nat.add_sub_of_le ge
    have vx : V C x i = (gateAt C j).op.eval ((gateAt C j).inputs.map (V C x)) := idx ▸ gv N C L.back x hx j jlen
    have vy : V C y i = (gateAt C j).op.eval ((gateAt C j).inputs.map (V C y)) := idx ▸ gv N C L.back y hy j jlen
    rw [vx,vy]
    apply gate_mono _ (L.interior j jmem).1
    intro w hw
    rcases (L.interior j jmem).2 w hw with h|h|h
    · exact hs w h
    · exact ih w (idx ▸ L.back j jlen w hw) h
    · exact he w h

theorem outside_agree (L : Layout N C src reg ent top) (x y : List Bool) (hx : x.length=N) (hy : y.length=N)
    (raw : ∀ i<N, i∉src → V C x i=V C y i) (cap : ℕ)
    (ht : N+top<cap → V C x (N+top)=V C y (N+top)) :
    ∀ i<cap, i∉src → ¬inside N reg i → V C x i=V C y i := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro bound hs hi
    by_cases low : i<N
    · exact raw i low hs
    by_cases far : N+C.gates.length ≤ i
    · have a := past C.gates x i (by rwa [hx])
      have b := past C.gates y i (by rwa [hy])
      exact a.trans b.symm
    let j := i-N
    have jlen : j<C.gates.length := by dsimp [j]; omega
    have idx : N+j=i := by dsimp [j]; omega
    have jr : j∉reg := fun h => hi ⟨by omega,h⟩
    have vx : V C x i = (gateAt C j).op.eval ((gateAt C j).inputs.map (V C x)) := idx ▸ gv N C L.back x hx j jlen
    have vy : V C y i = (gateAt C j).op.eval ((gateAt C j).inputs.map (V C y)) := idx ▸ gv N C L.back y hy j jlen
    rw [vx,vy]; congr 1
    apply List.map_congr_left
    intro w hw
    have smaller : w < i := idx ▸ L.back j jlen w hw
    have cut := L.exterior j jlen jr w hw
    by_cases h : inside N reg w
    · have eq := cut.2 h
      rw [eq]; exact ht (by omega)
    · exact ih w smaller (by omega) cut.1 h

noncomputable def port (ent : Finset ℕ) (v : ℕ → Bool) : Bool := decide (∃ i∈ent, v i=true)

theorem port_le (one : ent.card≤1) (x y : ℕ → Bool) (h : port ent x=true → port ent y=true) :
    ∀ i∈ent, x i=true → y i=true := by
  classical
  intro i hi xi
  have a : port ent x=true := by simpa only [port,decide_eq_true_eq] using (show ∃ j∈ent, x j=true from ⟨i,hi,xi⟩)
  have b := h a
  obtain ⟨j,hj,yj⟩ := of_decide_eq_true b
  exact (Finset.card_le_one.mp one j hj i hi) ▸ yj

noncomputable def low {β : Type} (bad : Finset β) (bit out : β → Bool) :=
  decide (∃ c, c∉bad ∧ bit c=false ∧ out c=true)
noncomputable def high {β : Type} (bad : Finset β) (out : β → Bool) :=
  decide (∃ c, c∉bad ∧ out c=true)

theorem low_high {β : Type} (bad : Finset β) (bit out : β → Bool) :
    low bad bit out=true → high bad out=true := by
  simp only [low,high,decide_eq_true_eq]
  rintro ⟨c,h,_,v⟩; exact ⟨c,h,v⟩

theorem reproduce {β : Type} (bad : Finset β) (bit out : β → Bool)
    (mono : ∀ c∉bad, ∀ c'∉bad, (bit c=true → bit c'=true) → out c=true → out c'=true)
    (c : β) (hc : c∉bad) : out c = if bit c then high bad out else low bad bit out := by
  apply Bool.eq_iff_iff.mpr
  cases h : bit c with
  | false =>
    simp only [Bool.false_eq_true,ite_false,low,decide_eq_true_eq]
    constructor
    · exact fun yes => ⟨c,hc,h,yes⟩
    · rintro ⟨w,hw,h0,yes⟩; exact mono w hw c hc (by simp [h0]) yes
  | true =>
    simp only [ite_true,high,decide_eq_true_eq]
    constructor
    · exact fun yes => ⟨c,hc,yes⟩
    · rintro ⟨w,hw,yes⟩; exact mono w hw c hc (fun _ => h) yes

theorem pairs : ∀ a b c d : Bool, (a=true → b=true) → (c=true → d=true) →
    a.toNat+b.toNat=c.toNat+d.toNat → a=c ∧ b=d := by decide

theorem side_bound {α β : Type} [Fintype β] [DecidableEq α] [DecidableEq β]
    (L : Layout N C src reg ent top) (S : Finset α) (bad : Finset β)
    (A : α → β → Bool) (xs : α → β → List Bool) (len : ∀ a c, (xs a c).length=N)
    (sem : ∀ a c, C.eval (xs a c)=A a c)
    (outside : ∀ a∈S, ∀ b∈S, ∀ c∉bad, ∀ i<N, i∉src → V C (xs a c) i=V C (xs b c) i)
    (privatePins : ∀ a∈S, ∀ c∉bad, ∀ c'∉bad, ∀ i∈src, V C (xs a c) i=V C (xs a c') i)
    : (S.image (fun a => (Finset.univ \ bad).filter (fun c => A a c=true))).card ≤ 2+ent.card := by
  classical
  let bit := fun a c => port ent (V C (xs a c))
  let out := fun a c => V C (xs a c) (N+top)
  have imem : inside N reg (N+top) := ⟨by omega,by simpa using L.member⟩
  have localEval (a) (ha : a∈S) (c) (hc : c∉bad) :
      out a c = if bit a c then high bad (out a) else low bad (bit a) (out a) := by
    apply reproduce
    · intro q hq w hw le
      exact inside_mono L _ _ (len a q) (len a w)
        (fun i hi v => (privatePins a ha q hq w hw i hi) ▸ v) (port_le L.one _ _ le) _ imem
    · exact hc
  have sameBit (a) (ha : a∈S) (b) (hb : b∈S) (c) (hc : c∉bad) : bit a c=bit b c := by
    apply Bool.eq_iff_iff.mpr
    simp only [bit,port,decide_eq_true_eq]
    have atEntry (i) (hi : i∈ent) : V C (xs a c) i=V C (xs b c) i :=
      outside_agree L _ _ (len a c) (len b c) (outside a ha b hb c hc) (N+top) (by omega)
        i (L.ports i hi).1 (L.ports i hi).2.1 (L.ports i hi).2.2
    constructor <;> rintro ⟨i,hi,yes⟩
    · exact ⟨i,hi,(atEntry i hi) ▸ yes⟩
    · exact ⟨i,hi,(atEntry i hi).symm ▸ yes⟩
  let lo := fun a => low bad (bit a) (out a)
  let hi := fun a => high bad (out a)
  let code := fun a => if ent=∅ then (lo a).toNat else (lo a).toNat+(hi a).toNat
  have maxBit (b : Bool) : b.toNat≤1 := by cases b <;> decide
  have bound (a : α) : code a<2+ent.card := by
    have l := maxBit (lo a); have h := maxBit (hi a)
    dsimp only [code]
    split_ifs with empty
    · omega
    · have := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr empty); omega
  let profile := fun a : α => (⟨code a,bound a⟩ : Fin (2+ent.card))
  let face := fun a => (Finset.univ \ bad).filter (fun c => A a c=true)
  have same (a) (ha : a∈S) (b) (hb : b∈S) (eq : profile a=profile b) : face a=face b := by
    have keys : code a=code b := congrArg Fin.val eq
    have outsideCol (c : β) (hc : c∉bad) : A a c=A b c := by
      have agreePort := sameBit a ha b hb c hc
      have agreeTop : out a c=out b c := by
        rw [localEval a ha c hc,localEval b hb c hc,agreePort]
        by_cases empty : ent=∅
        · have zero : bit b c=false := by simp [bit,port,empty]
          simp only [zero,Bool.false_eq_true,ite_false]
          have k : (lo a).toNat=(lo b).toNat := by simpa only [code,empty,ite_true] using keys
          exact (by cases h : lo a <;> cases j : lo b <;> simp_all : lo a=lo b)
        · have k : (lo a).toNat+(hi a).toNat=(lo b).toNat+(hi b).toNat := by simpa only [code,empty,ite_false] using keys
          obtain ⟨lowEq,highEq⟩ := pairs _ _ _ _ (low_high bad (bit a) (out a)) (low_high bad (bit b) (out b)) k
          split <;> assumption
      rw [←sem,←sem]
      change V C (xs a c) C.output = V C (xs b c) C.output
      by_cases interior : inside N reg C.output
      · rw [L.visible interior]; exact agreeTop
      · exact outside_agree L _ _ (len a c) (len b c) (outside a ha b hb c hc) (C.output+1)
          (fun _ => agreeTop) _ (by omega) L.output interior
    ext c
    by_cases mem : c∈bad
    · simp [face,mem]
    · simp [face,mem,outsideCol c mem]
  let decode (z : Fin (2+ent.card)) := if h : ∃ a∈S, profile a=z then face h.choose else ∅
  have sub : S.image face ⊆ Finset.univ.image decode := by
    intro v hv
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hv
    refine Finset.mem_image.mpr ⟨profile a,Finset.mem_univ _,?_⟩
    have h : ∃ b∈S, profile b=profile a := ⟨a,ha,rfl⟩
    simpa only [decode,dif_pos h] using same h.choose h.choose_spec.1 a ha h.choose_spec.2
  exact (Finset.card_le_card sub).trans ((Finset.card_image_le).trans (by simp))

theorem axis {α β : Type} [Fintype β] [DecidableEq α] [DecidableEq β]
    (L : Layout N C src reg ent top) (S : Finset α) (bad : Finset β)
    (A : α → β → Bool) (xs : α → β → List Bool) (len : ∀ a c, (xs a c).length=N)
    (sem : ∀ a c, C.eval (xs a c)=A a c)
    (left : α → ℕ) (right : β → ℕ) (ltL : ∀ a, left a<N) (ltR : ∀ b, right b<N)
    (injR : Function.Injective right) (disjoint : ∀ a b, left a≠right b)
    (hs : src=S.image left ∪ bad.image right)
    (atRaw : ∀ a c i, i<N → V C (xs a c) i = decide (i=left a ∨ i=right c))
    : (S.image (fun a => (Finset.univ \ bad).filter (fun c => A a c=true))).card ≤ 2+ent.card := by
  apply side_bound L S bad A xs len sem
  · intro a ha b hb c _ i hi off
    have na : i≠left a := fun eq => off (hs ▸ eq ▸ Finset.mem_union_left _ (Finset.mem_image_of_mem left ha))
    have nb : i≠left b := fun eq => off (hs ▸ eq ▸ Finset.mem_union_left _ (Finset.mem_image_of_mem left hb))
    simp [atRaw a c i hi,atRaw b c i hi,na,nb]
  · intro a _ c hc c' hc' i hi
    rw [hs] at hi
    rcases Finset.mem_union.mp hi with l|r
    · obtain ⟨a',_,rfl⟩ := Finset.mem_image.mp l
      simp [atRaw,ltL,disjoint]
    · obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp r
      have p : right b≠right c := fun eq => hc (injR eq ▸ hb)
      have q : right b≠right c' := fun eq => hc' (injR eq ▸ hb)
      simp [atRaw,ltR,p,q]

theorem both_axes {n m : ℕ} (G : Fin n → Fin m → Bool) (C : Circuit)
    (R : Finset (Fin n)) (B : Finset (Fin m)) (reg ent : Finset ℕ) (top : ℕ)
    (L : Layout (n+m) C (R.image Fin.val ∪ B.image (fun j => n+j.val)) reg ent top)
    (rep : Represents G C) :
    (R.image (fun a => (Finset.univ \ B).filter (fun c => G a c=true))).card≤2+ent.card ∧
    (B.image (fun c => (Finset.univ \ R).filter (fun a => G a c=true))).card≤2+ent.card := by
  classical
  let N := n+m
  have lowVal (u : Fin n) (v : Fin m) (i : ℕ) (hi : i<N) :
      V C (oneEach u v) i=decide (i=u.val ∨ i=n+v.val) := by
    change (run C.gates (oneEach u v)).getD i false=_
    rw [run_input _ _ _ (by rwa [oneEach_length]),oneEach_getD]
  have hr (i : Fin n) : i.val<N := by dsimp [N]; have := i.isLt; omega
  have hc (j : Fin m) : n+j.val<N := by dsimp [N]; have := j.isLt; omega
  have dis (i : Fin n) (j : Fin m) : i.val≠n+j.val := by have := i.isLt; omega
  constructor
  · exact axis L R B G oneEach oneEach_length rep (fun i => i.val) (fun j => n+j.val)
      hr hc (fun _ _ eq => Fin.ext (Nat.add_left_cancel eq)) dis rfl lowVal
  · exact axis L B R (fun j i => G i j) (fun j i => oneEach i j) (fun j i => oneEach_length i j)
      (fun j i => rep i j) (fun j => n+j.val) (fun i => i.val) hc hr Fin.val_injective
      (fun j i => (dis i j).symm) (Finset.union_comm _ _)
      (fun j i k hk => by simpa only [or_comm] using lowVal i j k hk)

end PEqualNP.Outside.L_meta_25615_aux.CircuitPart.Cut

namespace PEqualNP.Outside.L_meta_25615_aux.CircuitPart
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
open scoped Classical

theorem only_reader (C : Circuit) (i j k : ℕ) (hj : j < C.size) (hk : k < C.size)
    (hc : readsIn C (Finset.range C.size) i = 1)
    (hij : i ∈ (gateAt C j).inputs) (hik : i ∈ (gateAt C k).inputs) : j = k := by
  by_contra h
  have hs : ({j, k} : Finset ℕ) ⊆ Finset.range C.size := by
    intro l hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl <;> exact Finset.mem_range.mpr (by assumption)
  have hsum : (∑ g ∈ ({j, k} : Finset ℕ), (gateAt C g).inputs.count i) ≤
      readsIn C (Finset.range C.size) i :=
    Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => Nat.zero_le _)
  rw [Finset.sum_pair h, hc] at hsum
  have ha := List.count_pos_iff.mpr hij
  have hb := List.count_pos_iff.mpr hik
  omega

def wireSet (N : ℕ) (S reg : Finset ℕ) := S ∪ reg.image (fun j => N+j)
def edge (N : ℕ) (C : Circuit) (reg : Finset ℕ) (w z : ℕ) : Prop :=
  ∃ j∈reg, z=N+j ∧ w∈(gateAt C j).inputs
abbrev reach (N : ℕ) (C : Circuit) (reg : Finset ℕ) := Relation.ReflTransGen (edge N C reg)
noncomputable def leaves {α : Type} (N : ℕ) (C : Circuit) (reg : Finset ℕ) (f : α → ℕ)
    (S : Finset α) (z : ℕ) := S.filter fun a => reach N C reg (f a) z
noncomputable def stages (N : ℕ) (C : Circuit) (reg : Finset ℕ) (z : ℕ) :=
  reg.filter fun j => reach N C reg (N+j) z

structure Tree (N : ℕ) (C : Circuit) (sources reg : Finset ℕ) (root : ℕ) (ext : Finset ℕ) : Prop where
  rawLt : ∀ i∈sources, i<N
  back : ReadsBack N C
  valid : reg ⊆ Finset.range C.size
  rootMem : root∈wireSet N sources reg
  gates : ∀ j∈reg, ((gateAt C j).op=.and ∨ (gateAt C j).op=.or) ∧
    (gateAt C j).inputs.length=2 ∧ ∀ i∈(gateAt C j).inputs, i∈wireSet N sources reg ∨ i∈ext
  portData : ∀ w∈ext, w∉wireSet N sources reg ∧ w<root ∧ readsIn C reg w=1
  endReads : readsIn C reg root=0
  uniq : ∀ w∈wireSet N sources reg, w≠root →
    readsIn C reg w=1 ∧ readsIn C (Finset.range C.size) w=1 ∧ C.output≠w

variable {N root : ℕ} {C : Circuit} {s r ext : Finset ℕ}

theorem tail_step {a b : ℕ} (h : reach N C r a b) (ne : a≠b) :
    ∃ w, reach N C r a w ∧ edge N C r w b := by
  cases h with
  | refl => contradiction
  | tail h last => exact ⟨_,h,last⟩

theorem head_step {a b : ℕ} (h : reach N C r a b) (ne : a≠b) :
    ∃ w, edge N C r a w ∧ reach N C r w b := by
  induction h with
  | refl => contradiction
  | @tail b c h last ih =>
    by_cases zero : a=b
    · subst b; exact ⟨c,last,.refl⟩
    · obtain ⟨w,e,p⟩ := ih zero
      exact ⟨w,e,p.tail last⟩

theorem edge_lt (T : Tree N C s r root ext) {a b : ℕ} (h : edge N C r a b) : a<b := by
  obtain ⟨j,hj,rfl,hr⟩ := h
  exact T.back j (Finset.mem_range.mp (T.valid hj)) a hr

theorem wire_bound (T : Tree N C s r root ext) {w : ℕ} (h : w∈wireSet N s r) : w<N+C.size := by
  rcases Finset.mem_union.mp h with h|h
  · have := T.rawLt w h; omega
  · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp h
    have := Finset.mem_range.mp (T.valid hj); omega

theorem exists_reader {reg : Finset ℕ} {w : ℕ} (pos : 0<readsIn C reg w) :
    ∃ j∈reg,w∈(gateAt C j).inputs := by
  classical
  by_contra no
  have z : readsIn C reg w=0 := Finset.sum_eq_zero fun j hj =>
    List.count_eq_zero.mpr (fun h => no ⟨j,hj,h⟩)
  omega

theorem root_ends (T : Tree N C s r root ext) {j : ℕ} (hj : j∈r) : root∉(gateAt C j).inputs := by
  intro h
  have le : (gateAt C j).inputs.count root≤readsIn C r root :=
    Finset.single_le_sum (f:=fun j => (gateAt C j).inputs.count root) (fun _ _ => Nat.zero_le _) hj
  have pos := List.count_pos_iff.mpr h
  have z := T.endReads; omega

theorem to_root (T : Tree N C s r root ext) (w : ℕ) (hw : w∈wireSet N s r) : reach N C r w root := by
  by_cases terminal : w=root
  · subst w; exact .refl
  · obtain ⟨once,_,_⟩ := T.uniq w hw terminal
    obtain ⟨j,hj,reads⟩ := exists_reader (show 0<readsIn C r w by omega)
    have e : edge N C r w (N+j) := ⟨j,hj,rfl,reads⟩
    have member : N+j∈wireSet N s r := Finset.mem_union_right _ (Finset.mem_image_of_mem _ hj)
    exact (Relation.ReflTransGen.single e).trans (to_root T _ member)
termination_by N+C.size-w
decreasing_by
  have := edge_lt T e
  have := wire_bound T member
  omega

theorem no_escape (T : Tree N C s r root ext) {w z j : ℕ} (hw : w∈wireSet N s r)
    (path : reach N C r w z) (neq : w≠z) (hj : j<C.size) (hr : w∈(gateAt C j).inputs) :
    j∈stages N C r z := by
  obtain ⟨next,⟨k,hk,rfl,read⟩,p⟩ := head_step path neq
  have nonroot : w≠root := fun e => root_ends T hk (e ▸ read)
  have eq := only_reader C w j k hj (Finset.mem_range.mp (T.valid hk)) (T.uniq w hw nonroot).2.1 hr read
  subst j; exact Finset.mem_filter.mpr ⟨hk,p⟩

theorem hidden (T : Tree N C s r root ext) {w z : ℕ} (hw : w∈wireSet N s r)
    (path : reach N C r w z) (neq : w≠z) : C.output≠w := by
  obtain ⟨next,⟨j,hj,_,read⟩,_⟩ := head_step path neq
  exact (T.uniq w hw (fun e => root_ends T hj (e ▸ read))).2.2

theorem path_le (T : Tree N C s r root ext) {a b : ℕ} (p : reach N C r a b) : a≤b := by
  induction p with
  | refl => rfl
  | tail h last ih => exact ih.trans (edge_lt T last).le

theorem at_most_one (T : Tree N C s r root ext) {v j : ℕ} (hj : j∈r)
    (h : v∈(gateAt C j).inputs) : readsIn C r v≤1 := by
  rcases (T.gates j hj).2.2 v h with w|e
  · by_cases terminal : v=root
    · subst v; rw [T.endReads]; decide
    · exact (T.uniq v w terminal).1.le
  · exact (T.portData v e).2.2.le

theorem deterministic (T : Tree N C s r root ext) {a b c : ℕ} (ab : edge N C r a b)
    (ac : edge N C r a c) : b=c := by
  obtain ⟨j,jr,rfl,aj⟩ := ab
  obtain ⟨k,kr,rfl,ak⟩ := ac
  congr 1
  by_contra ne
  have sub : ({j,k} : Finset ℕ) ⊆ r := by
    intro i hi; simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    exact hi.elim (fun h => h ▸ jr) (fun h => h ▸ kr)
  have sum : (∑ g∈({j,k} : Finset ℕ), (gateAt C g).inputs.count a) ≤ readsIn C r a :=
    Finset.sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => Nat.zero_le _)
  rw [Finset.sum_pair ne] at sum
  have p := List.count_pos_iff.mpr aj; have q := List.count_pos_iff.mpr ak
  have bound := at_most_one T jr aj; omega

theorem comparable (T : Tree N C s r root ext) {u a b : ℕ} (pa : reach N C r u a)
    (pb : reach N C r u b) : reach N C r a b ∨ reach N C r b a := by
  by_cases ua : u=a
  · subst a; exact Or.inl pb
  by_cases ub : u=b
  · subst b; exact Or.inr pa
  obtain ⟨w,uw,wa⟩ := head_step pa ua
  obtain ⟨v,uv,vb⟩ := head_step pb ub
  have eq := deterministic T uw uv
  subst v
  exact comparable T wa vb
termination_by N+C.size-u
decreasing_by
  have lt := edge_lt T uw
  obtain ⟨j,hj,eq,_⟩ := uw
  have := Finset.mem_range.mp (T.valid hj)
  omega

theorem distinct_operands (T : Tree N C s r root ext) {k a b : ℕ} (hk : k∈r)
    (ops : (gateAt C k).inputs=[a,b]) : a≠b := by
  intro eq; subst b
  have h : a∈(gateAt C k).inputs := by simp [ops]
  have two : (gateAt C k).inputs.count a=2 := by simp [ops]
  have le : (gateAt C k).inputs.count a ≤ readsIn C r a :=
    Finset.single_le_sum (f:=fun j => (gateAt C j).inputs.count a) (fun _ _ => Nat.zero_le _) hk
  have cap := at_most_one T hk h; omega

theorem branch (T : Tree N C s r root ext) {a b z : ℕ} (az : edge N C r a z)
    (bz : edge N C r b z) (diff : a≠b) (u : ℕ) : ¬reach N C r u a ∨ ¬reach N C r u b := by
  by_contra two
  push_neg at two
  have no {x y : ℕ} (xz : edge N C r x z) (yz : edge N C r y z) (xy : x≠y) (p : reach N C r x y) : False := by
    obtain ⟨w,xw,wy⟩ := head_step p xy
    have eq := deterministic T xz xw
    have le := path_le T wy; have lt := edge_lt T yz; omega
  rcases comparable T two.1 two.2 with h|h
  · exact no az bz diff h
  · exact no bz az diff.symm h

theorem binary_list {α : Type} (l : List α) (h : l.length=2) : ∃ a b, l=[a,b] := by
  obtain _|⟨a,l⟩ := l <;> simp_all
  obtain _|⟨b,l⟩ := l <;> simp_all

end PEqualNP.Outside.L_meta_25615_aux.CircuitPart

namespace PEqualNP.Outside.L_meta_25615_aux.CircuitPart.Shape

abbrev Signal := Finset ℕ → Bool
def pair (f : Signal) (a c : ℕ) : Prop :=
  f {a}=false ∧ f {c}=false ∧ f {a,c}=true
def Closed (P : ℕ → ℕ → Prop) := ∀ a b x y, P a x → P b x → P b y → P a y
theorem yes_or (a b : Bool) : (a || b)=true ↔ a=true ∨ b=true := by cases a <;> cases b <;> decide
theorem yes_and (a b : Bool) : (a && b)=true ↔ a=true ∧ b=true := by cases a <;> cases b <;> decide
structure Model (f : Signal) (A : Set ℕ) : Prop where
  mono : ∀ U V : Finset ℕ, U ⊆ V → f U=true → f V=true
  agree : ∀ U V : Finset ℕ, (∀ i∈A, i∈U ↔ i∈V) → f U=f V
  rect : Closed (pair f)

theorem widen {f : Signal} {A B : Set ℕ} (F : Model f A) (h : A⊆B) : Model f B :=
  ⟨F.mono,fun U V e => F.agree U V (fun i hi => e i (h hi)),F.rect⟩

theorem fixed (v : Bool) : Model (fun _ => v) ∅ := by
  refine ⟨fun _ _ _ h => h,fun _ _ _ => rfl,?_⟩
  intro a b x y first _ _
  exact False.elim (Bool.false_ne_true (first.1.symm.trans first.2.2))

theorem input (i : ℕ) : Model (fun U => decide (i∈U)) {i} := by
  classical
  constructor
  · intro U V sub yes; exact decide_eq_true (sub (of_decide_eq_true yes))
  · intro U V h; apply Bool.eq_iff_iff.mpr; simpa only [decide_eq_true_eq] using h i (Set.mem_singleton i)
  · intro a b x y p _ _
    obtain ⟨l,r,z⟩ := p
    simp only [decide_eq_false_iff_not,Finset.mem_singleton,decide_eq_true_eq,
      Finset.mem_insert] at l r z
    exact False.elim (z.elim l r)

theorem singleton_agree {f : Signal} {A : Set ℕ} (F : Model f A) {a x : ℕ} (h : x∉A) :
    f {a,x}=f {a} := by
  apply F.agree
  intro i hi
  have ne : i≠x := fun eq => h (eq ▸ hi)
  simp [ne]

theorem absent {f : Signal} {A : Set ℕ} (F : Model f A) {a : ℕ} (h : a∉A) : f {a}=f ∅ := by
  apply F.agree
  intro i hi
  have ne : i≠a := fun eq => h (eq ▸ hi)
  simp [ne]

theorem endpoints {f : Signal} {A : Set ℕ} (F : Model f A) {a x : ℕ} (p : pair f a x) : a∈A ∧ x∈A := by
  constructor
  · by_contra h
    have e : f {a,x}=f {x} := by rw [Finset.pair_comm]; exact singleton_agree F h
    exact Bool.false_ne_true (p.2.1.symm.trans (e.symm.trans p.2.2))
  · by_contra h
    exact Bool.false_ne_true (p.1.symm.trans ((singleton_agree F h).symm.trans p.2.2))

theorem combine {P Q : ℕ → ℕ → Prop} (p : Closed P) (q : Closed Q)
    (row : ∀ i x y, P i x → Q i y → False) (col : ∀ a b x, P a x → Q b x → False) :
    Closed (fun i j => P i j ∨ Q i j) := by
  intro a b x y ax bx byy
  rcases ax with h|h
  · rcases bx with h2|h2
    · rcases byy with h3|h3
      · exact Or.inl (p _ _ _ _ h h2 h3)
      · exact False.elim (row _ _ _ h2 h3)
    · exact False.elim (col _ _ _ h h2)
  · rcases bx with h2|h2
    · exact False.elim (col _ _ _ h2 h)
    · rcases byy with h3|h3
      · exact False.elim (row _ _ _ h3 h2)
      · exact Or.inr (q _ _ _ _ h h2 h3)

theorem or_model {f g : Signal} {A B : Set ℕ} (F : Model f A) (H : Model g B)
    (dis : ∀ i∈A, i∉B) : Model (fun U => f U || g U) (A∪B) := by
  refine ⟨?_,?_,?_⟩
  · intro U V sub h
    simp only [Bool.or_eq_true] at h ⊢
    exact h.imp (F.mono U V sub) (H.mono U V sub)
  · intro U V h
    rw [F.agree U V (fun i hi => h i (Or.inl hi)),H.agree U V (fun i hi => h i (Or.inr hi))]
  · have liftPair {a x} (p : pair (fun U => f U || g U) a x) : pair f a x ∨ pair g a x := by
      obtain ⟨pa,px,pax⟩ := p
      simp only [Bool.or_eq_false_iff] at pa px
      simp only [Bool.or_eq_true] at pax
      exact pax.imp (fun z => ⟨pa.1,px.1,z⟩) (fun z => ⟨pa.2,px.2,z⟩)
    have closed := combine F.rect H.rect
      (fun i x y l r => dis i (endpoints F l).1 (endpoints H r).1)
      (fun a b x l r => dis x (endpoints F l).2 (endpoints H r).2)
    intro a b x y ax bx byy
    refine ⟨ax.1,byy.2.1,?_⟩
    apply (yes_or _ _).mpr
    exact (closed a b x y (liftPair ax) (liftPair bx) (liftPair byy)).imp (fun h => h.2.2) (fun h => h.2.2)

theorem hits {f : Signal} {A : Set ℕ} (F : Model f A) (base : f ∅=false)
    {a x} (h : f {a,x}=true) : a∈A ∨ x∈A := by
  by_contra! miss
  have z := (singleton_agree F miss.2).trans ((absent F miss.1).trans base)
  exact Bool.false_ne_true (z.symm.trans h)

theorem and_model {f g : Signal} {A B : Set ℕ} (F : Model f A) (H : Model g B)
    (dis : ∀ i∈A, i∉B) : Model (fun U => f U && g U) (A∪B) := by
  have constant {v : Signal} {S : Set ℕ} (M : Model v S) (h : v ∅=true) (U) : v U=true :=
    M.mono ∅ U (Finset.empty_subset _) h
  cases bf : f ∅ with
  | true =>
    have eq : (fun U => f U && g U)=g := by funext U; simp [constant F bf U]
    rw [eq]; exact widen H (fun _ h => Or.inr h)
  | false =>
    cases bg : g ∅ with
    | true =>
      have eq : (fun U => f U && g U)=f := by funext U; simp [constant H bg U]
      rw [eq]; exact widen F (fun _ h => Or.inl h)
    | false =>
      have unique (i) (p : f {i}=true) (q : g {i}=true) : False := by
        have mem {v : Signal} {S : Set ℕ} (M : Model v S) (z : v ∅=false) (t : v {i}=true) : i∈S := by
          by_contra no; exact Bool.false_ne_true (z.symm.trans ((absent M no).symm.trans t))
        exact dis i (mem F bf p) (mem H bg q)
      let P := fun i j : ℕ => f {i}=true ∧ g {j}=true
      let Q := fun i j : ℕ => g {i}=true ∧ f {j}=true
      have pc : Closed P := fun _ _ _ _ ax _ byy => ⟨ax.1,byy.2⟩
      have qc : Closed Q := fun _ _ _ _ ax _ byy => ⟨ax.1,byy.2⟩
      have closed := combine pc qc (fun i _ _ p q => unique i p.1 q.1) (fun _ _ j p q => unique j q.2 p.2)
      have classify {a x} (h : pair (fun U => f U && g U) a x) : P a x ∨ Q a x := by
        obtain ⟨_,_,hit⟩ := h
        obtain ⟨l,r⟩ := (yes_and _ _).mp hit
        have slice {v : Signal} {S : Set ℕ} (M : Model v S) {i j : ℕ} (ni : i∉S) (vij : v {i,j}=true) :
            v {j}=true := by
          rw [Finset.pair_comm,singleton_agree M ni] at vij
          exact vij
        rcases hits F bf l with aA|xA
        · rcases hits H bg r with aB|xB
          · exact False.elim (dis a aA aB)
          · exact Or.inl ⟨(singleton_agree F (fun h => dis x h xB)).symm.trans l,slice H (dis a aA) r⟩
        · rcases hits H bg r with aB|xB
          · exact Or.inr ⟨(singleton_agree H (dis x xA)).symm.trans r,slice F (fun h => dis a h aB) l⟩
          · exact False.elim (dis x xA xB)
      refine ⟨?_,?_,?_⟩
      · intro U V sub h
        obtain ⟨l,r⟩ := (yes_and _ _).mp h
        exact (yes_and _ _).mpr ⟨F.mono U V sub l,H.mono U V sub r⟩
      · intro U V h
        rw [F.agree U V (fun i hi => h i (Or.inl hi)),H.agree U V (fun i hi => h i (Or.inr hi))]
      · intro a b x y ax bx byy
        refine ⟨ax.1,byy.2.1,(yes_and _ _).mpr ?_⟩
        have subL : ({a} : Finset ℕ)⊆{a,y} := by simp
        have subR : ({y} : Finset ℕ)⊆{a,y} := by simp
        rcases closed a b x y (classify ax) (classify bx) (classify byy) with h|h
        · exact ⟨F.mono _ _ subL h.1,H.mono _ _ subR h.2⟩
        · exact ⟨F.mono _ _ subR h.2,H.mono _ _ subL h.1⟩

end PEqualNP.Outside.L_meta_25615_aux.CircuitPart.Shape

namespace PEqualNP.Outside.L_meta_25615_aux.CircuitPart
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
open scoped Classical
variable {N root : ℕ} {C : Circuit} {s r e : Finset ℕ}

theorem whole_layout (T : Tree N C s r root e) (one : e.card≤1) {k : ℕ}
    (hk : k∈r) (eq : root=N+k) : Cut.Layout N C s r e k := by
  have insideWire {w} (h : Cut.inside N r w) : w∈wireSet N s r := by
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨w-N,h.2,Nat.add_sub_of_le h.1⟩)
  have privateRead {w j} (h : w∈wireSet N s r) (ne : w≠root) (hj : j<C.size)
      (read : w∈(gateAt C j).inputs) : j∈r :=
    (Finset.mem_filter.mp (no_escape T h (to_root T w h) ne hj read)).1
  refine ⟨T.back,T.valid,hk,one,?_,?_,?_,?_,?_⟩
  · intro w hw
    obtain ⟨away,low,_⟩ := T.portData w hw
    exact ⟨eq ▸ low,fun hs => away (Finset.mem_union_left _ hs),fun h => away (insideWire h)⟩
  · intro j hj
    refine ⟨(T.gates j hj).1,?_⟩
    intro w hw
    rcases (T.gates j hj).2.2 w hw with a|b
    · rcases Finset.mem_union.mp a with hs|hr
      · exact Or.inl hs
      · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hr
        exact Or.inr (Or.inl ⟨by omega,by simpa using hi⟩)
    · exact Or.inr (Or.inr b)
  · intro j hj out w hw
    constructor
    · intro hs
      have low := T.rawLt w hs
      exact out (privateRead (Finset.mem_union_left _ hs) (by omega) hj hw)
    · intro within
      by_contra ne
      exact out (privateRead (insideWire within) (fun h => ne (h.trans eq)) hj hw)
  · intro hs
    have low := T.rawLt _ hs
    exact (T.uniq _ (Finset.mem_union_left _ hs) (by omega)).2.2 rfl
  · intro inside
    by_contra ne
    exact (T.uniq _ (insideWire inside) (fun h => ne (h.trans eq))).2.2 rfl

def sample (N : ℕ) (S U : Finset ℕ) : List Bool :=
  List.ofFn fun i : Fin N => decide (i.val∈S ∧ i.val∈U)
theorem sample_length (N : ℕ) (S U : Finset ℕ) : (sample N S U).length=N := by simp [sample]
theorem sample_read (N : ℕ) (S U : Finset ℕ) (i : ℕ) (h : i<N) :
    (sample N S U).getD i false=decide (i∈S ∧ i∈U) := by
  simp [sample,List.getD_eq_getElem?_getD,List.getElem?_ofFn,h]
def sig (N : ℕ) (C : Circuit) (s : Finset ℕ) (w : ℕ) (U : Finset ℕ) :=
  Cut.V C (sample N s U) w
theorem sig_raw {i : ℕ} (low : i<N) (U : Finset ℕ) :
    sig N C s i U=decide (i∈s ∧ i∈U) := by
  change (Cut.run C.gates (sample N s U)).getD i false=_
  rw [Cut.run_input _ _ _ (by rwa [sample_length]),sample_read _ _ _ _ low]

theorem raw_same (U V : Finset ℕ) (i : ℕ) (low : i<N) (away : i∉s) :
    Cut.V C (sample N s U) i=Cut.V C (sample N s V) i := by
  change sig _ _ _ _ _=sig _ _ _ _ _
  rw [sig_raw low,sig_raw low]; simp [away]

theorem port_value {k : ℕ} (L : Cut.Layout N C s r e k) {w : ℕ} (hw : w∈e) (U : Finset ℕ) :
    sig N C s w U=sig N C s w ∅ := by
  exact Cut.outside_agree L _ _ (sample_length _ _ _) (sample_length _ _ _) (raw_same U ∅)
    (N+k) (by omega) w (L.ports w hw).1 (L.ports w hw).2.1 (L.ports w hw).2.2

theorem readout {k : ℕ} (L : Cut.Layout N C s r e k) :
    ∃ out : Bool → Bool, ∀ U, sig N C s C.output U=out (sig N C s (N+k) U) := by
  classical
  let head := sig N C s (N+k)
  let endVal := sig N C s C.output
  have single (U V) (h : head U=head V) : endVal U=endVal V := by
    by_cases inner : Cut.inside N r C.output
    · simpa only [endVal,L.visible inner] using h
    · exact Cut.outside_agree L _ _ (sample_length _ _ _) (sample_length _ _ _) (raw_same U V)
        (C.output+1) (fun _ => h) _ (by omega) L.output inner
  let out (b) := if h : ∃ U, head U=b then endVal h.choose else false
  refine ⟨out,?_⟩
  intro U
  have h : ∃ V, head V=head U := ⟨U,rfl⟩
  change endVal U=out (head U)
  simpa only [out,dif_pos h] using single U h.choose h.choose_spec.symm

def support (N : ℕ) (C : Circuit) (s r : Finset ℕ) (w : ℕ) : Set ℕ :=
  {i | i∈s ∧ reach N C r i w}

theorem structural (T : Tree N C s r root e) {k : ℕ} (L : Cut.Layout N C s r e k)
    (w : ℕ) : w∈wireSet N s r ∨ w∈e → Shape.Model (sig N C s w) (support N C s r w) := by
  classical
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rintro (hw|port)
    · rcases Finset.mem_union.mp hw with raw|gateMem
      · have eq : sig N C s w=(fun U => decide (w∈U)) := by
          funext U; simp [sig_raw (T.rawLt w raw),raw]
        rw [eq]
        apply Shape.widen (Shape.input w)
        intro u hu
        obtain rfl : u=w := Set.mem_singleton_iff.mp hu
        exact ⟨raw,.refl⟩
      · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp gateMem
        obtain ⟨a,b,ops⟩ := binary_list _ (T.gates j hj).2.1
        have ha : a∈(gateAt C j).inputs := by simp [ops]
        have hb : b∈(gateAt C j).inputs := by simp [ops]
        have len := Finset.mem_range.mp (T.valid hj)
        have A := ih a (T.back j len a ha) ((T.gates j hj).2.2 a ha)
        have B := ih b (T.back j len b hb) ((T.gates j hj).2.2 b hb)
        have ea : edge N C r a (N+j) := ⟨j,hj,rfl,ha⟩
        have eb : edge N C r b (N+j) := ⟨j,hj,rfl,hb⟩
        have dis (i) (la : i∈support N C s r a) (lb : i∈support N C s r b) : False :=
          (branch T ea eb (distinct_operands T hj ops) i).elim (fun no => no la.2) (fun no => no lb.2)
        have sub : support N C s r a ∪ support N C s r b ⊆ support N C s r (N+j) := by
          intro i hi
          rcases hi with l|h
          · exact ⟨l.1,l.2.tail ea⟩
          · exact ⟨h.1,h.2.tail eb⟩
        have val U : sig N C s (N+j) U=(gateAt C j).op.eval [sig N C s a U,sig N C s b U] := by
          have v := Cut.gv N C T.back (sample N s U) (sample_length _ _ _) j len
          simpa only [sig,Cut.V,ops,List.map_cons,List.map_nil] using v
        rcases (T.gates j hj).1 with op|op
        · have eq : sig N C s (N+j)=(fun U => sig N C s a U && sig N C s b U) := by
            funext U; simp [val,op,GateOp.eval]
          rw [eq]; exact Shape.widen (Shape.and_model A B dis) sub
        · have eq : sig N C s (N+j)=(fun U => sig N C s a U || sig N C s b U) := by
            funext U; simp [val,op,GateOp.eval]
          rw [eq]; exact Shape.widen (Shape.or_model A B dis) sub
    · have eq : sig N C s w=(fun _ => sig N C s w ∅) := funext (port_value L port)
      rw [eq]
      exact Shape.widen (Shape.fixed _) (Set.empty_subset _)

end PEqualNP.Outside.L_meta_25615_aux.CircuitPart

namespace PEqualNP.Outside.L_meta_25615_aux.CircuitPart
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
open scoped Classical

theorem one_pair {n m : ℕ} (u : Fin n) (c : Fin m) (S : Finset ℕ) (hu : u.val∈S) (hc : n+c.val∈S) :
    sample (n+m) S {u.val,n+c.val}=oneEach u c := by
  apply List.ext_getElem (by rw [sample_length,Cut.oneEach_length])
  intro i hi hj
  have low : i<n+m := by simpa only [sample_length] using hi
  rw [←List.getD_eq_getElem _ false hi,←List.getD_eq_getElem _ false hj,
    sample_read _ _ _ _ low,Cut.oneEach_getD]
  congr 1
  apply propext
  simp only [Finset.mem_insert,Finset.mem_singleton]
  exact ⟨And.right,fun h => ⟨h.elim (fun eq => eq ▸ hu) (fun eq => eq ▸ hc),h⟩⟩

end PEqualNP.Outside.L_meta_25615_aux.CircuitPart

namespace PEqualNP.Outside.L_meta_25615_aux.CircuitPart
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
open scoped Classical

def bits (N : ℕ) (U : Finset ℕ) := sample N (Finset.range N) U
def value (N : ℕ) (C : Circuit) (w : ℕ) (U : Finset ℕ) := Cut.V C (bits N U) w

theorem pair_in {s : Finset ℕ} {a b : ℕ} (ha : a∈s) (hb : b∈s) : ({a,b} : Finset ℕ)⊆s := by
  intro i hi
  rcases Finset.mem_insert.mp hi with h|h
  · exact h ▸ ha
  · exact (Finset.mem_singleton.mp h) ▸ hb

theorem raw_value {N : ℕ} (C : Circuit) {i : ℕ} (low : i<N) (U : Finset ℕ) :
    value N C i U=decide (i∈U) := by
  change sig N C (Finset.range N) i U=_
  simpa only [Finset.mem_range,low,true_and] using (sig_raw (C:=C) (s:=Finset.range N) low U)

theorem values_order {N : ℕ} (C : Circuit) (mono : Monotone2 C) (back : ReadsBack N C)
    {U W : Finset ℕ} (incl : U⊆W) : ∀ i, value N C i U=true → value N C i W=true := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    by_cases low : i<N
    · rw [raw_value C low,raw_value C low,decide_eq_true_eq,decide_eq_true_eq]; exact fun h => incl h
    by_cases far : N+C.size ≤ i
    · intro hx
      have h := Cut.past C.gates (bits N U) i (by rw [show (bits N U).length=N from sample_length ..]; exact far)
      exact False.elim (Bool.false_ne_true (h.symm.trans hx))
    let j := i-N
    have eq : N+j=i := Nat.add_sub_of_le (by omega)
    have len : j<C.size := by dsimp [j]; omega
    have gm : gateAt C j∈C.gates := by
      have l : j<C.gates.length := len
      rw [gateAt,List.getD_eq_getElem _ _ l]; exact List.getElem_mem l
    change (Cut.run C.gates (bits N U)).getD i false=true → (Cut.run C.gates (bits N W)).getD i false=true
    rw [←eq,Cut.gv N C back (bits N U) (sample_length ..) j len,Cut.gv N C back (bits N W) (sample_length ..) j len]
    apply Cut.gate_mono _ (mono _ gm).1
    intro v hv; exact ih v (eq ▸ back j len v hv)

theorem outside_order {N : ℕ} {C : Circuit} {s reg e : Finset ℕ} {k : ℕ}
    (L : Cut.Layout N C s reg e k) (mono : Monotone2 C) (U W : Finset ℕ)
    (raw : ∀ i<N, i∉s → value N C i U=true → value N C i W=true)
    (top : value N C (N+k) U=true → value N C (N+k) W=true) :
    value N C C.output U=true → value N C C.output W=true := by
  by_cases bound : Cut.inside N reg C.output
  · simpa only [L.visible bound] using top
  have aux (i : ℕ) : i∉s → ¬Cut.inside N reg i → value N C i U=true → value N C i W=true := by
    induction i using Nat.strong_induction_on with
    | ind i ih =>
      intro off outside
      by_cases low : i<N
      · exact raw i low off
      by_cases far : N+C.size ≤ i
      · intro hx
        have h := Cut.past C.gates (bits N U) i (by rw [show (bits N U).length=N from sample_length ..]; exact far)
        exact False.elim (Bool.false_ne_true (h.symm.trans hx))
      let j := i-N
      have eq : N+j=i := Nat.add_sub_of_le (by omega)
      have len : j<C.size := by dsimp [j]; omega
      have gm : gateAt C j∈C.gates := by
        have l : j<C.gates.length := len
        rw [gateAt,List.getD_eq_getElem _ _ l]; exact List.getElem_mem l
      have jr : j∉reg := fun h => outside ⟨by omega,h⟩
      change (Cut.run C.gates (bits N U)).getD i false=true → (Cut.run C.gates (bits N W)).getD i false=true
      rw [←eq,Cut.gv N C L.back (bits N U) (sample_length ..) j len,Cut.gv N C L.back (bits N W) (sample_length ..) j len]
      apply Cut.gate_mono _ (mono _ gm).1
      intro v hv
      have cut := L.exterior j len jr v hv
      by_cases inner : Cut.inside N reg v
      · rw [cut.2 inner]; exact top
      · exact ih v (eq ▸ L.back j len v hv) cut.1 inner
  exact aux _ L.output bound

theorem matrix_read {n m : ℕ} (G : Fin n → Fin m → Bool) {C : Circuit} (rep : Represents G C)
    (a : Fin n) (c : Fin m) : value (n+m) C C.output {a.val,n+c.val}=G a c := by
  have hi : a.val∈Finset.range (n+m) := Finset.mem_range.mpr (by have := a.isLt; omega)
  have hj : n+c.val∈Finset.range (n+m) := Finset.mem_range.mpr (by have := c.isLt; omega)
  change Cut.V C (sample (n+m) (Finset.range (n+m)) _) C.output=_
  rw [one_pair a c _ hi hj]; exact rep a c

end PEqualNP.Outside.L_meta_25615_aux.CircuitPart

namespace PEqualNP.Outside.L_meta_25615_aux.CircuitPart
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
open scoped Classical

def onLeaves (N : ℕ) (C : Circuit) (s : Finset ℕ) (U : Finset ℕ) :=
  s.filter (fun w => value N C w U=true)

theorem expose {N root : ℕ} {C : Circuit} {s r e : Finset ℕ} (T : Tree N C s r root e)
    (w : ℕ) (hw : w∈wireSet N s r ∨ w∈e) : ∃ f : Shape.Signal,
    Shape.Model f (support N C (s∪e) r w) ∧ ∀ U, value N C w U=f (onLeaves N C (s∪e) U) := by
  classical
  have terminal (w) (h : w∈s∪e) : ∃ f : Shape.Signal,
      Shape.Model f (support N C (s∪e) r w) ∧ ∀ U, value N C w U=f (onLeaves N C (s∪e) U) := by
    refine ⟨_,Shape.widen (Shape.input w) ?_,?_⟩
    · intro i hi
      obtain rfl : i=w := Set.mem_singleton_iff.mp hi
      exact ⟨h,.refl⟩
    · intro U
      simp only [onLeaves,Finset.mem_filter,h,true_and]
      cases value N C w U <;> decide
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rcases hw with marked|portWire
    · rcases Finset.mem_union.mp marked with raw|gateMem
      · exact terminal _ (Finset.mem_union_left _ raw)
      · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp gateMem
        obtain ⟨a,b,ops⟩ := binary_list _ (T.gates j hj).2.1
        have ha : a∈(gateAt C j).inputs := by simp [ops]
        have hb : b∈(gateAt C j).inputs := by simp [ops]
        have len := Finset.mem_range.mp (T.valid hj)
        obtain ⟨f,F,fv⟩ := ih a (T.back j len a ha) ((T.gates j hj).2.2 a ha)
        obtain ⟨g,H,gv⟩ := ih b (T.back j len b hb) ((T.gates j hj).2.2 b hb)
        have ea : edge N C r a (N+j) := ⟨j,hj,rfl,ha⟩
        have eb : edge N C r b (N+j) := ⟨j,hj,rfl,hb⟩
        have dis (i) (la : i∈support N C (s∪e) r a) (lb : i∈support N C (s∪e) r b) : False :=
          (branch T ea eb (distinct_operands T hj ops) i).elim (fun no => no la.2) (fun no => no lb.2)
        have sub : support N C (s∪e) r a ∪ support N C (s∪e) r b ⊆ support N C (s∪e) r (N+j) := by
          intro i hi
          rcases hi with l|h
          · exact ⟨l.1,l.2.tail ea⟩
          · exact ⟨h.1,h.2.tail eb⟩
        have calcVal U : value N C (N+j) U=(gateAt C j).op.eval
            [f (onLeaves N C (s∪e) U),g (onLeaves N C (s∪e) U)] := by
          rw [←fv,←gv]
          have h := Cut.gv N C T.back (bits N U) (sample_length ..) j len
          simpa only [value,Cut.V,ops,List.map_cons,List.map_nil] using h
        rcases (T.gates j hj).1 with op|op
        · exact ⟨_,Shape.widen (Shape.and_model F H dis) sub,fun U => by simp [calcVal,op,GateOp.eval]⟩
        · exact ⟨_,Shape.widen (Shape.or_model F H dis) sub,fun U => by simp [calcVal,op,GateOp.eval]⟩
    · exact terminal _ (Finset.mem_union_right _ portWire)

end PEqualNP.Outside.L_meta_25615_aux.CircuitPart

namespace PEqualNP.Outside.L_meta_25615_aux.CircuitPart
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
open scoped Classical

structure Face (s e : Finset ℕ) (O : Shape.Signal) where
  f : Shape.Signal
  A : Set ℕ
  model : Shape.Model f A
  flags : Finset ℕ → Finset ℕ
  flagSub : ∀ W, flags W⊆e
  compare : ∀ W, Disjoint W s → ∀ U V, U⊆s → V⊆s →
    (f (U∪flags W)=true → f (V∪flags W)=true) → O (W∪U)=true → O (W∪V)=true

theorem exterior_value {N root : ℕ} {C : Circuit} {s r e : Finset ℕ} (T : Tree N C s r root e)
    {k : ℕ} (L : Cut.Layout N C s r e k) (mono : Monotone2 C) :
    Nonempty (Face s e (value N C C.output)) := by
  classical
  have inRoot : N+k∈wireSet N s r := Finset.mem_union_right _ (Finset.mem_image_of_mem _ L.member)
  obtain ⟨f,M,eval⟩ := expose T (N+k) (Or.inl inRoot)
  let flags := onLeaves N C e
  have mask W (dis : Disjoint W s) U (hu : U⊆s) :
      onLeaves N C (s∪e) (W∪U)=U∪flags W := by
    have portEq (i) (hi : i∈e) : value N C i (W∪U)=value N C i W := by
      apply Cut.outside_agree L _ _ (sample_length ..) (sample_length ..) _ (N+k) (by omega)
        i (L.ports i hi).1 (L.ports i hi).2.1 (L.ports i hi).2.2
      intro j low off
      change value N C j (W∪U)=value N C j W
      rw [raw_value C low,raw_value C low]
      simp [show j∉U from fun h => off (hu h)]
    ext i
    by_cases si : i∈s
    · have notW : i∉W := fun h => Finset.disjoint_left.mp dis h si
      have notE : i∉e := fun h => (L.ports i h).2.1 si
      simp [onLeaves,flags,si,notW,notE,raw_value C (T.rawLt i si)]
    · have notU : i∉U := fun h => si (hu h)
      by_cases ei : i∈e
      · simp [onLeaves,flags,si,notU,ei,portEq i ei]
      · simp [onLeaves,flags,si,notU,ei]
  refine ⟨⟨f,_,M,flags,fun _ => Finset.filter_subset _ _,?_⟩⟩
  intro W dis U V hu hv top
  apply outside_order L mono
  · intro i low off
    rw [raw_value C low,raw_value C low,decide_eq_true_eq,decide_eq_true_eq]
    simp only [Finset.mem_union]
    intro h; exact Or.inl (h.resolve_right fun h => off (hu h))
  · simpa only [eval,mask W dis U hu,mask W dis V hv] using top

theorem force (p q u v : Bool) (pass : (p=true → q=true) → u=true → v=true)
    (yes : u=true) (no : v=false) : p=true ∧ q=false := by
  cases p <;> cases q <;> simp_all

theorem linear : ∀ a b c d : Bool, (a=true → b=true) → (c=true → d=true) →
    ((a=true → c=true) ∧ (b=true → d=true)) ∨ ((c=true → a=true) ∧ (d=true → b=true)) := by decide

variable {s e : Finset ℕ} {O : Shape.Signal}

theorem flag_cases (F : Face s e O) (one : e.card≤1) (W) : F.flags W=∅ ∨ F.flags W=e := by
  by_cases empty : F.flags W=∅
  · exact Or.inl empty
  · right
    apply Finset.eq_of_subset_of_card_le (F.flagSub W)
    have pos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr empty)
    omega

theorem face_chain (F : Face s e O) (one : e.card≤1) (a b : ℕ) (ha : a∈s) (hb : b∈s) :
    (∀ z∉s, O {a,z}=true → O {b,z}=true) ∨ (∀ z∉s, O {b,z}=true → O {a,z}=true) := by
  have increase (v : ℕ) : F.f {v}=true → F.f ({v}∪e)=true := F.model.mono _ _ Finset.subset_union_left
  have transport (v w) (hv : v∈s) (hw : w∈s) (lo : F.f {v}=true → F.f {w}=true)
      (hi : F.f ({v}∪e)=true → F.f ({w}∪e)=true) :
      ∀ z∉s, O {v,z}=true → O {w,z}=true := by
    intro z hz
    have step := F.compare {z} (by simpa using hz) {v} {w}
      (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_subset_iff.mpr hw) (by
        rcases flag_cases F one {z} with h|h
        · simpa only [h,Finset.union_empty] using lo
        · simpa only [h] using hi)
    simpa only [Finset.singleton_union,Finset.pair_comm z] using step
  rcases linear _ _ _ _ (increase a) (increase b) with forward|reverse
  · exact Or.inl (transport a b ha hb forward.1 forward.2)
  · exact Or.inr (transport b a hb ha reverse.1 reverse.2)

theorem face_no_triangle (F : Face s e O) (one : e.card≤1)
    (a x i j : ℕ) (ha : a∈s) (hx : x∈s) (hi : i∉s) (hj : j∉s)
    (a0 : O {a}=false) (x0 : O {x}=false) (i0 : O {i}=false) (j0 : O {j}=false)
    (ax : O {a,x}=true) (aj : O {a,j}=true) (ix : O {i,x}=true) : False := by
  classical
  let t := F.flags ∅
  let r := F.flags {i}
  let c := F.flags {j}
  have constraints (W) (dis : Disjoint W s) (U V) (su : U⊆s) (sv : V⊆s)
      (yes : O (W∪U)=true) (no : O (W∪V)=false) :
      F.f (U∪F.flags W)=true ∧ F.f (V∪F.flags W)=false :=
    force _ _ _ _ (F.compare W dis U V su sv) yes no
  have haX : ({a,x} : Finset ℕ)⊆s := pair_in ha hx
  have hA : ({a} : Finset ℕ)⊆s := Finset.singleton_subset_iff.mpr ha
  have hX : ({x} : Finset ℕ)⊆s := Finset.singleton_subset_iff.mpr hx
  have H := constraints ∅ (by simp) {a,x} {a} haX hA (by simpa using ax) (by simpa using a0)
  have X := constraints ∅ (by simp) {a,x} {x} haX hX (by simpa using ax) (by simpa using x0)
  have J := constraints {j} (by simpa using hj) {a} ∅ hA (by simp)
    (by simpa only [Finset.singleton_union,Finset.pair_comm j] using aj) (by simpa using j0)
  have I := constraints {i} (by simpa using hi) {x} ∅ hX (by simp)
    (by simpa using ix) (by simpa using i0)
  change F.f ({a,x}∪t)=true ∧ F.f ({a}∪t)=false at H
  change F.f ({a,x}∪t)=true ∧ F.f ({x}∪t)=false at X
  change F.f ({a}∪c)=true ∧ F.f (∅∪c)=false at J
  change F.f ({x}∪r)=true ∧ F.f (∅∪r)=false at I
  have empty : t=∅ := by
    rcases flag_cases F one ∅ with off|on
    · exact off
    · change t=e at on
      have more : {a}∪c⊆{a}∪t := by
        rw [on]
        exact Finset.union_subset_union (Finset.Subset.refl _) (F.flagSub {j})
      have pos := F.model.mono _ _ more J.1
      exact False.elim (Bool.false_ne_true (H.2.symm.trans pos))
  rw [empty,Finset.union_empty,Finset.union_empty] at H X
  have allC : c=e := by
    rcases flag_cases F one {j} with off|on
    · change c=∅ at off
      simp only [off,Finset.union_empty,H.2,Bool.false_eq_true,false_and] at J
    · exact on
  have allR : r=e := by
    rcases flag_cases F one {i} with off|on
    · change r=∅ at off
      simp only [off,Finset.union_empty,X.2,Bool.false_eq_true,false_and] at I
    · exact on
  have nonemptyE : e.Nonempty := by
    by_contra no
    have zero := Finset.not_nonempty_iff_eq_empty.mp no
    simp only [allC,zero,Finset.union_empty,H.2,Bool.false_eq_true,false_and] at J
  have card : e.card=1 := by have p := Finset.card_pos.mpr nonemptyE; omega
  obtain ⟨z,ez⟩ := Finset.card_eq_one.mp card
  simp only [allC,ez,Finset.singleton_union,Finset.empty_union] at J
  simp only [allR,ez,Finset.singleton_union,Finset.empty_union] at I
  have xa : Shape.pair F.f a x := ⟨H.2,X.2,H.1⟩
  have zx : Shape.pair F.f z x := ⟨I.2,X.2,by simpa only [Finset.pair_comm z x] using I.1⟩
  have za : Shape.pair F.f z a := ⟨J.2,H.2,by simpa only [Finset.pair_comm z a] using J.1⟩
  have aa := (F.model.rect a z x a xa zx za).2.2
  have aYes : F.f {a}=true := by simpa using aa
  exact Bool.false_ne_true (H.2.symm.trans aYes)

end PEqualNP.Outside.L_meta_25615_aux.CircuitPart

namespace PEqualNP.Outside.L_meta_25615_aux.CircuitPart
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
open scoped Classical

theorem bits_eq_sample {N : ℕ} (s U : Finset ℕ) (sub : U⊆s) : bits N U=sample N s U := by
  unfold bits sample
  congr 1
  funext i
  by_cases hit : i.val∈U
  · simp [hit,sub hit,i.isLt]
  · simp [hit]

theorem inside_closed {N root : ℕ} {C : Circuit} {s r e : Finset ℕ} (T : Tree N C s r root e)
    {k : ℕ} (L : Cut.Layout N C s r e k) (mono : Monotone2 C) :
    ∀ a∈s, ∀ b∈s, ∀ x∈s, ∀ y∈s,
      value N C C.output {a}=false → value N C C.output {b}=false →
      value N C C.output {x}=false → value N C C.output {y}=false →
      value N C C.output {a,x}=true → value N C C.output {b,x}=true → value N C C.output {b,y}=true →
      value N C C.output {a,y}=true := by
  classical
  let O := value N C C.output
  let f := sig N C s (N+k)
  have model := structural T L (N+k) (Or.inl (Finset.mem_union_right _ (Finset.mem_image_of_mem _ L.member)))
  have cmp (U V) (hu : U⊆s) (hv : V⊆s) (le : f U=true → f V=true) : O U=true → O V=true := by
    apply outside_order L mono
    · intro w low off
      rw [raw_value C low,raw_value C low,decide_eq_true_eq,decide_eq_true_eq]
      exact fun h => False.elim (off (hu h))
    · change Cut.V C (bits N U) (N+k)=true → Cut.V C (bits N V) (N+k)=true
      rw [bits_eq_sample s U hu,bits_eq_sample s V hv]
      exact le
  intro a ha b hb x hx y hy a0 b0 x0 y0 ax bx byy
  have make (u v) (hu : u∈s) (hv : v∈s) (offU : O {u}=false) (offV : O {v}=false)
      (hit : O {u,v}=true) : Shape.pair f u v := by
    have both : ({u,v} : Finset ℕ)⊆s := pair_in hu hv
    have A := force _ _ _ _ (cmp _ _ both (Finset.singleton_subset_iff.mpr hu)) hit offU
    have B := force _ _ _ _ (cmp _ _ both (Finset.singleton_subset_iff.mpr hv)) hit offV
    exact ⟨A.2,B.2,A.1⟩
  have diag := model.rect a b x y (make a x ha hx a0 x0 ax) (make b x hb hx b0 x0 bx) (make b y hb hy b0 y0 byy)
  exact cmp {a,x} {a,y} (pair_in ha hx) (pair_in ha hy) (fun _ => diag.2.2) ax

theorem single_zeros {n m : ℕ} {C : Circuit} (G : Fin n → Fin m → Bool)
    (rz : ∀ a, ∃ c, G a c=false) (cz : ∀ c, ∃ a, G a c=false)
    (mono : Monotone2 C) (back : ReadsBack (n+m) C) (rep : Represents G C) :
    (∀ a : Fin n, value (n+m) C C.output {a.val}=false) ∧
    (∀ c : Fin m, value (n+m) C C.output {n+c.val}=false) := by
  have zero (w : ℕ) (U : Finset ℕ) (hw : w∈U) (z : value (n+m) C C.output U=false) :
      value (n+m) C C.output {w}=false := by
    cases v : value (n+m) C C.output {w} with
    | false => rfl
    | true =>
      have yes := values_order C mono back (Finset.singleton_subset_iff.mpr hw) C.output v
      exact False.elim (Bool.false_ne_true (z.symm.trans yes))
  constructor
  · intro a; obtain ⟨c,h⟩ := rz a
    exact zero _ {a.val,n+c.val} (by simp) ((matrix_read G rep a c).trans h)
  · intro c; obtain ⟨a,h⟩ := cz c
    exact zero _ {a.val,n+c.val} (by simp) ((matrix_read G rep a c).trans h)

theorem neg_sets {α β : Type} [DecidableEq α] [Fintype β] [DecidableEq β]
    (G : α → β → Bool) (B : Finset β) (a b : α)
    (order : (∀ c∉B, G a c=true → G b c=true) ∨ (∀ c∉B, G b c=true → G a c=true)) :
    (Finset.univ \ B).filter (fun c => G a c=false) ⊆ (Finset.univ \ B).filter (fun c => G b c=false) ∨
    (Finset.univ \ B).filter (fun c => G b c=false) ⊆ (Finset.univ \ B).filter (fun c => G a c=false) := by
  have reverse (i j : α) (forward : ∀ c∉B, G i c=true → G j c=true) :
      (Finset.univ \ B).filter (fun c => G j c=false) ⊆ (Finset.univ \ B).filter (fun c => G i c=false) := by
    intro c hc
    obtain ⟨outside,off⟩ := Finset.mem_filter.mp hc
    refine Finset.mem_filter.mpr ⟨outside,?_⟩
    cases h : G i c with
    | false => rfl
    | true => exact False.elim (Bool.false_ne_true (off.symm.trans (forward c (Finset.mem_sdiff.mp outside).2 h)))
  exact order.elim (fun h => Or.inr (reverse a b h)) (fun h => Or.inl (reverse b a h))

end PEqualNP.Outside.L_meta_25615_aux.CircuitPart

namespace PEqualNP.Outside.L_meta_25615_aux
open PEqualNP.Outside.L_meta_25615_aux.CircuitPart PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents in
theorem privateTree : ∀ (n m : ℕ) (G : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit)
    (R : Finset (Fin n)) (B : Finset (Fin m)) (region entry : Finset ℕ) (root : ℕ),
  let raw := n + m
  let sources := R.image (fun src => src.val) ∪ B.image (fun dest => n + dest.val)
  let wires := sources ∪ region.image (fun idx => raw + idx)
  let gate := PEqualNP.MetaComplexity.NestedCover.gateAt C
  let localReads := PEqualNP.MetaComplexity.NestedCover.readsIn C region
  let allReads := PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size)
  let extR := fun (i : Fin n) => (Finset.univ \ B).filter (fun outColumn : Fin m => G i outColumn = false)
  let extC := fun (j : Fin m) => (Finset.univ \ R).filter (fun outRow : Fin n => G outRow j = false)
  (∀ a, ∃ c, G a c = false) → (∀ c, ∃ a, G a c = false) →
  PEqualNP.MetaComplexity.Monotone2 C →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack raw C →
  PEqualNP.Represents.Represents G C → region ⊆ Finset.range C.size → root ∈ wires →
  entry.card ≤ 1 → (∀ w ∈ entry, w ∉ wires ∧ w < root ∧ localReads w = 1) →
  (∀ k ∈ region,
    ((gate k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
     (gate k).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
    (gate k).inputs.length = 2 ∧ ∀ w ∈ (gate k).inputs, w ∈ wires ∨ w ∈ entry) →
  localReads root = 0 →
  (∀ w ∈ wires, w ≠ root → localReads w = 1 ∧ allReads w = 1 ∧ C.output ≠ w) →
  (∀ a ∈ R, ∀ b ∈ R, extR a ⊆ extR b ∨ extR b ⊆ extR a) ∧
  (∀ x ∈ B, ∀ y ∈ B, extC x ⊆ extC y ∨ extC y ⊆ extC x) ∧
  (∀ a ∈ R, ∀ b ∈ R, ∀ x ∈ B, ∀ y ∈ B,
    G a x = true → G b x = true → G b y = true → G a y = true) ∧
  (∀ a ∈ R, ∀ x ∈ B, G a x = true →
    (∀ j ∉ B, G a j = false) ∨ (∀ i ∉ R, G i x = false)) := by
  classical
  intro n m G C R B r e root
  dsimp only
  intro rz cz mono back rep valid rootIn one ports gates last uses
  let N := n+m
  let l := fun a : Fin n => a.val
  let q := fun x : Fin m => n+x.val
  let S := R.image l ∪ B.image q
  let O := value N C C.output
  have cross (a : Fin n) (x : Fin m) : l a≠q x := by have := a.isLt; dsimp [l,q]; omega
  have left (a : Fin n) : l a∈S ↔ a∈R := by
    constructor
    · intro h
      rcases Finset.mem_union.mp h with h|h
      · obtain ⟨b,hb,eq⟩ := Finset.mem_image.mp h
        exact Fin.val_injective eq ▸ hb
      · obtain ⟨x,_,eq⟩ := Finset.mem_image.mp h
        exact False.elim (cross a x eq.symm)
    · exact fun h => Finset.mem_union_left _ (Finset.mem_image_of_mem _ h)
  have right (x : Fin m) : q x∈S ↔ x∈B := by
    constructor
    · intro h
      rcases Finset.mem_union.mp h with h|h
      · obtain ⟨a,_,eq⟩ := Finset.mem_image.mp h
        exact False.elim (cross a x eq)
      · obtain ⟨y,hy,eq⟩ := Finset.mem_image.mp h
        change n+y.val=n+x.val at eq
        exact Fin.ext (Nat.add_left_cancel eq) ▸ hy
    · exact fun h => Finset.mem_union_right _ (Finset.mem_image_of_mem _ h)
  have low (i) (h : i∈S) : i<N := by
    rcases Finset.mem_union.mp h with h|h
    · obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp h; dsimp [l,N]; have := a.isLt; omega
    · obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp h; dsimp [q,N]; have := x.isLt; omega
  have T : Tree N C S r root e := ⟨low,back,valid,rootIn,gates,ports,last,uses⟩
  have val (a x) : value N C C.output {l a,q x}=G a x := matrix_read G rep a x
  obtain ⟨zR,zC⟩ := single_zeros G rz cz mono back rep
  rcases Finset.mem_union.mp T.rootMem with raw|gate
  · have same (i) (hi : i∈S) : i=root := by
      by_contra neq
      have small := low _ raw
      obtain ⟨_,_,j,_,eq,_⟩ := tail_step (to_root T i (Finset.mem_union_left _ hi)) neq
      omega
    have lr (a b : Fin n) (ha : a∈R) (hb : b∈R) : a=b :=
      Fin.ext ((same _ ((left _).mpr ha)).trans (same _ ((left _).mpr hb)).symm)
    have cr (x y : Fin m) (hx : x∈B) (hy : y∈B) : x=y :=
      Fin.ext (Nat.add_left_cancel ((same _ ((right _).mpr hx)).trans (same _ ((right _).mpr hy)).symm))
    have never (a x) (ha : a∈R) (hx : x∈B) : False :=
      cross a x ((same _ ((left _).mpr ha)).trans (same _ ((right _).mpr hx)).symm)
    refine ⟨?_,?_,?_,?_⟩
    · intro a ha b hb; rw [lr a b ha hb]; exact Or.inl (Finset.Subset.refl _)
    · intro x hx y hy; rw [cr x y hx hy]; exact Or.inl (Finset.Subset.refl _)
    · intro a ha b hb x hx; exact False.elim (never a x ha hx)
    · intro a ha x hx; exact False.elim (never a x ha hx)
  · obtain ⟨k,hk,eq⟩ := Finset.mem_image.mp gate
    have L := whole_layout T one hk eq.symm
    obtain ⟨F⟩ := exterior_value T L mono
    refine ⟨?_,?_,?_,?_⟩
    · intro a ha b hb
      apply neg_sets G B a b
      rcases face_chain F one (l a) (l b) ((left _).mpr ha) ((left _).mpr hb) with p|p
      · left; intro y hy; simpa only [val] using p (q y) (fun h => hy ((right y).mp h))
      · right; intro y hy; simpa only [val] using p (q y) (fun h => hy ((right y).mp h))
    · intro x hx y hy
      apply neg_sets (fun c a => G a c) R x y
      rcases face_chain F one (q x) (q y) ((right _).mpr hx) ((right _).mpr hy) with p|p
      · left; intro a ha
        simpa only [Finset.pair_comm (q x) (l a),Finset.pair_comm (q y) (l a),val] using
          p (l a) (fun h => ha ((left a).mp h))
      · right; intro a ha
        simpa only [Finset.pair_comm (q x) (l a),Finset.pair_comm (q y) (l a),val] using
          p (l a) (fun h => ha ((left a).mp h))
    · intro a ha b hb x hx y hy ax bx byy
      rw [←val] at ax bx byy ⊢
      exact inside_closed T L mono (l a) ((left _).mpr ha) (l b) ((left _).mpr hb) (q x) ((right _).mpr hx)
        (q y) ((right _).mpr hy) (zR a) (zR b) (zC x) (zC y) ax bx byy
    · intro a ha x hx ax
      by_contra! bad
      obtain ⟨⟨j,hj,aj⟩,⟨i,hi,ix⟩⟩ := bad
      have yesR : G a j=true := by cases h : G a j <;> simp_all
      have yesC : G i x=true := by cases h : G i x <;> simp_all
      exact face_no_triangle F one (l a) (q x) (l i) (q j)
        ((left _).mpr ha) ((right _).mpr hx) (fun h => hi ((left _).mp h)) (fun h => hj ((right _).mp h))
        (zR a) (zC x) (zR i) (zC j) ((val a x).trans ax) ((val a j).trans yesR) ((val i x).trans yesC)

end PEqualNP.Outside.L_meta_25615_aux
namespace PEqualNP.Outside.L_meta_25615_aux
open scoped Classical

variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

def neg (G : α → β → Bool) (a : α) := Finset.univ.filter (fun x => G a x=false)
def ext (G : α → β → Bool) (B : Finset β) (a : α) := (Finset.univ \ B).filter (fun x => G a x=false)
def pos (G : α → β → Bool) (B : Finset β) (a : α) := B.filter (fun x => G a x=true)
def flip (G : α → β → Bool) := fun (x : β) (a : α) => G a x
def GoodRows (G : α → β → Bool) := ∀ a, 2≤(neg G a).card
def NoFour (G : α → β → Bool) := ∀ a b, a≠b → ((neg G a)∩(neg G b)).card≤1
def Chain (G : α → β → Bool) (R : Finset α) (B : Finset β) :=
  ∀ a∈R, ∀ b∈R, ext G B a⊆ext G B b ∨ ext G B b⊆ext G B a
def Rect (G : α → β → Bool) (R : Finset α) (B : Finset β) :=
  ∀ a∈R, ∀ b∈R, ∀ x∈B, ∀ y∈B, G a x=true → G b x=true → G b y=true → G a y=true
def Cross (G : α → β → Bool) (R : Finset α) (B : Finset β) :=
  ∀ a∈R, ∀ x∈B, G a x=true → (∀ j∉B, G a j=false) ∨ (∀ i∉R, G i x=false)
def Unique (G : α → β → Bool) (R : Finset α) (B : Finset β) :=
  ∀ a∈R, ∀ b∈R, ∀ x∈B, G a x=true → G b x=true → a=b
def Hex (G : α → β → Bool) := ∃ (rows : Fin 3 → α) (cols : Fin 3 → β),
  Function.Injective rows ∧ Function.Injective cols ∧ ∀ i j, i≠j → G (rows i) (cols j)=false
def few (G : α → β → Bool) (R : Finset α) := R.filter (fun a => (pos G Finset.univ a).card≤3)

theorem flip_four {G : α → β → Bool} (h : NoFour G) : NoFour (flip G) := by
  intro x y xy
  apply Finset.card_le_one.mpr
  intro a ha b hb
  by_contra ab
  have va := Finset.mem_inter.mp ha
  have vb := Finset.mem_inter.mp hb
  have ax : G a x=false := (Finset.mem_filter.mp va.1).2
  have ay : G a y=false := (Finset.mem_filter.mp va.2).2
  have bx : G b x=false := (Finset.mem_filter.mp vb.1).2
  have byy : G b y=false := (Finset.mem_filter.mp vb.2).2
  have incl : ({x,y} : Finset β)⊆(neg G a)∩(neg G b) := by
    intro z hz
    rcases Finset.mem_insert.mp hz with eq|eq
    · subst z; simp [neg,ax,bx]
    · obtain rfl := Finset.mem_singleton.mp eq; simp [neg,ay,byy]
  have cap := Finset.card_le_card incl
  rw [Finset.card_pair xy] at cap
  have one := h a b ab; omega

theorem flip_rect {G : α → β → Bool} {R : Finset α} {B : Finset β} (h : Rect G R B) : Rect (flip G) B R := by
  intro x hx y hy a ha b hb xa ya yb
  exact h b hb a ha y hy x hx yb ya xa

theorem flip_cross {G : α → β → Bool} {R : Finset α} {B : Finset β} (h : Cross G R B) : Cross (flip G) B R :=
  fun x hx a ha yes => (h a ha x hx yes).symm

theorem flip_hex {G : α → β → Bool} (h : Hex (flip G)) : Hex G := by
  obtain ⟨c,r,hc,hr,h⟩ := h
  exact ⟨r,c,hr,hc,fun i j ne => h j i ne.symm⟩

theorem inside_unique {G : α → β → Bool} {R : Finset α} {B : Finset β}
    (deg : GoodRows G) (noFour : NoFour G) (chain : Chain G R B) (rect : Rect G R B) : Unique G R B := by
  have orient (a) (ha : a∈R) (b) (hb : b∈R) (x) (hx : x∈B) (ax : G a x=true) (bx : G b x=true)
      (sub : ext G B a⊆ext G B b) : a=b := by
    by_contra ne
    have incl : neg G a⊆neg G b := by
      intro y hy
      have off := (Finset.mem_filter.mp hy).2
      apply Finset.mem_filter.mpr; refine ⟨Finset.mem_univ _,?_⟩
      by_cases inside : y∈B
      · cases on : G b y with
        | false => rfl
        | true => exact False.elim (Bool.false_ne_true (off.symm.trans (rect a ha b hb x hx y inside ax bx on)))
      · have member : y∈ext G B a := Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,inside⟩,off⟩
        exact (Finset.mem_filter.mp (sub member)).2
    have h := noFour a b ne
    rw [Finset.inter_eq_left.mpr incl] at h
    have lower := deg a; omega
  intro a ha b hb x hx ax bx
  rcases chain a ha b hb with h|h
  · exact orient a ha b hb x hx ax bx h
  · exact (orient b hb a ha x hx bx ax h).symm

structure Side (G : α → β → Bool) (R : Finset α) (B : Finset β) : Prop where
  deg : GoodRows G
  noFour : NoFour G
  chain : Chain G R B
  byCol : Unique G R B
  byRow : Unique (flip G) B R
  cross : Cross G R B

theorem pos_small {G : α → β → Bool} {R : Finset α} {B : Finset β} (H : Side G R B)
    {a} (ha : a∈R) : (pos G B a).card≤1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  obtain ⟨bx,px⟩ := Finset.mem_filter.mp hx
  obtain ⟨byy,py⟩ := Finset.mem_filter.mp hy
  exact H.byRow x bx y byy a ha px py

theorem nested {G : α → β → Bool} {R : Finset α} {B : Finset β} (H : Side G R B)
    {a b} (ha : a∈R) (hb : b∈R) (order : (ext G B a).card≤(ext G B b).card) : ext G B a⊆ext G B b := by
  rcases H.chain a ha b hb with h|h
  · exact h
  · exact (Finset.eq_of_subset_of_card_le h order).ge

theorem pair_facts {G : α → β → Bool} {R : Finset α} {B : Finset β} (H : Side G R B)
    {a b : α} (ha : a∈R) (hb : b∈R) (ne : a≠b) (sub : ext G B a⊆ext G B b) :
    (neg G a).card=2 ∧ (∃ x∈B, G a x=false ∧ G b x=true) ∧ (∃ y, G a y=false ∧ G b y=false) := by
  classical
  let both := neg G a ∩ neg G b
  let positive := pos G B b
  have cover : neg G a⊆both∪positive := by
    intro x hx
    have ax := (Finset.mem_filter.mp hx).2
    cases bx : G b x with
    | false => exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hx,Finset.mem_filter.mpr ⟨Finset.mem_univ _,bx⟩⟩)
    | true =>
      apply Finset.mem_union_right _
      refine Finset.mem_filter.mpr ⟨?_,bx⟩
      by_contra outside
      have mem : x∈ext G B a := Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,outside⟩,ax⟩
      exact Bool.false_ne_true ((Finset.mem_filter.mp (sub mem)).2.symm.trans bx)
  have u := (Finset.card_le_card cover).trans (Finset.card_union_le _ _)
  have atMost : both.card≤1 := H.noFour a b ne
  have singleton : positive.card≤1 := pos_small H hb
  have two := H.deg a
  refine ⟨by omega,?_,?_⟩
  · by_contra! missing
    have incl : neg G a⊆both := by
      intro x hx
      rcases Finset.mem_union.mp (cover hx) with h|h
      · exact h
      · obtain ⟨inside,bx⟩ := Finset.mem_filter.mp h
        exact False.elim (by have no := missing x inside (Finset.mem_filter.mp hx).2; simp_all)
    have h := Finset.card_le_card incl
    omega
  · have one : 0<both.card := by omega
    obtain ⟨y,hy⟩ := Finset.card_pos.mp one
    obtain ⟨first,second⟩ := Finset.mem_inter.mp hy
    exact ⟨y,(Finset.mem_filter.mp first).2,(Finset.mem_filter.mp second).2⟩

theorem choice_count (K : Finset α) (Q : Finset β) (P : α → β → Prop)
    (existsP : ∀ a∈K, ∃ b∈Q, P a b)
    (unique : ∀ a∈K, ∀ b∈K, ∀ x∈Q, P a x → P b x → a=b) : K.card≤Q.card := by
  classical
  let pick (a : {v // v∈K}) := (existsP a.val a.property).choose
  have sp (a) : pick a∈Q ∧ P a.val (pick a) := (existsP a.val a.property).choose_spec
  have inj : Function.Injective pick := by
    intro a b eq
    exact Subtype.ext (unique _ a.property _ b.property _ (sp a).1 (sp a).2 (eq ▸ (sp b).2))
  have cover : K.attach.image pick ⊆ Q := by
    intro z hz
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hz
    exact (sp a).1
  have le := Finset.card_le_card cover
  simpa only [Finset.card_image_of_injective _ inj,Finset.card_attach] using le

end PEqualNP.Outside.L_meta_25615_aux

namespace PEqualNP.Outside.L_meta_25615_aux
open scoped Classical
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
variable {G : α → β → Bool} {R : Finset α} {B : Finset β}

theorem rest_info (H : Side G R B) (hr : R.Nonempty) : ∃ a∈R,
    (∀ b∈R.erase a, (ext G B a).card≤(ext G B b).card) ∧
    (∀ b∈R.erase a, (neg G a).card=2 ∧ (∃ x∈B, G a x=false ∧ G b x=true) ∧ (∃ y, G a y=false ∧ G b y=false)) := by
  obtain ⟨a,ha,least⟩ := Finset.exists_min_image R (fun z => (ext G B z).card) hr
  refine ⟨a,ha,fun b hb => least b (Finset.mem_erase.mp hb).2,?_⟩
  intro b hb
  obtain ⟨neq,mem⟩ := Finset.mem_erase.mp hb
  exact pair_facts H ha mem neq.symm (nested H ha mem (least b mem))

theorem three_limit (H : Side G R B) : R.card≤3 := by
  classical
  by_cases many : 1<R.card
  · obtain ⟨a,ha,_,facts⟩ := rest_info H (Finset.card_pos.mp (by omega))
    have er := Finset.card_erase_add_one ha
    have existsB : 0<(R.erase a).card := by omega
    obtain ⟨b,hb⟩ := Finset.card_pos.mp existsB
    have bound := (facts b hb).1
    let P (z : α) (x : β) := x∈B ∧ G z x=true
    have count := choice_count (R.erase a) (neg G a) P (by
      intro z hz
      obtain ⟨x,inB,off,on⟩ := (facts z hz).2.1
      exact ⟨x,Finset.mem_filter.mpr ⟨Finset.mem_univ _,off⟩,inB,on⟩) (by
      intro z hz w hw x _ px py
      exact H.byCol z (Finset.mem_erase.mp hz).2 w (Finset.mem_erase.mp hw).2 x px.1 px.2 py.2)
    omega
  · omega

theorem at_degree_three (H : Side G R B) (deg : ∀ a,3≤(neg G a).card) : R.card≤1 := by
  by_contra! many
  obtain ⟨a,ha,_,facts⟩ := rest_info H (Finset.card_pos.mp (by omega))
  have er := Finset.card_erase_add_one ha
  obtain ⟨b,hb⟩ := Finset.card_pos.mp (show 0<(R.erase a).card by omega)
  have two := (facts b hb).1
  have three := deg a; omega

theorem three_inj {γ : Type} (x y z : γ) (xy : x≠y) (xz : x≠z) (yz : y≠z) :
    Function.Injective (![x,y,z] : Fin 3 → γ) := by
  intro i j eq
  fin_cases i <;> fin_cases j <;> simp_all

theorem three_hex (H : Side G R B) (three : 2<R.card) : Hex G := by
  classical
  obtain ⟨a,ha,_,facts⟩ := rest_info H (Finset.card_pos.mp (by omega))
  let K := R.erase a
  have cK : K.card+1=R.card := Finset.card_erase_add_one ha
  have nonemp : K.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨b,hb,least⟩ := Finset.exists_min_image K (fun k => (ext G B k).card) nonemp
  have cS := Finset.card_erase_add_one hb
  obtain ⟨c,mem⟩ := Finset.card_pos.mp (show 0<(K.erase b).card by omega)
  obtain ⟨cb,hc⟩ := Finset.mem_erase.mp mem
  have ab := (Finset.mem_erase.mp hb).1.symm
  have ac := (Finset.mem_erase.mp hc).1.symm
  have br := (Finset.mem_erase.mp hb).2
  have cr := (Finset.mem_erase.mp hc).2
  obtain ⟨x,hx,ax,bx⟩ := (facts b hb).2.1
  obtain ⟨y,hy,ay,cy⟩ := (facts c hc).2.1
  obtain ⟨z,bz,cz⟩ := (pair_facts H br cr cb.symm (nested H br cr (least c hc))).2.2
  have xy : x≠y := fun eq => cb.symm (H.byCol b br c cr x hx bx (eq ▸ cy))
  have zx : z≠x := by intro eq; subst z; rw [bx] at bz; contradiction
  have zy : z≠y := by intro eq; subst z; rw [cy] at cz; contradiction
  have byy : G b y=false := by
    cases value : G b y with
    | false => rfl
    | true => exact False.elim (cb.symm (H.byCol b br c cr y hy value cy))
  have cx : G c x=false := by
    cases value : G c x with
    | false => rfl
    | true => exact False.elim (cb (H.byCol c cr b br x hx value bx))
  refine ⟨![a,b,c],![z,x,y],three_inj a b c ab ac cb.symm,three_inj z x y zx zy xy,?_⟩
  intro i j ne
  fin_cases i <;> fin_cases j <;> simp_all

theorem closed_few (H : Side G R B) {a} (ha : a∈R) (closed : ∀ j∉B, G a j=false) :
    a∈few G R := by
  refine Finset.mem_filter.mpr ⟨ha,?_⟩
  have incl : pos G Finset.univ a⊆pos G B a := by
    intro x hx
    have yes := (Finset.mem_filter.mp hx).2
    refine Finset.mem_filter.mpr ⟨?_,yes⟩
    by_contra off
    exact Bool.false_ne_true ((closed x off).symm.trans yes)
  exact (Finset.card_le_card incl).trans ((pos_small H ha).trans (by decide))

theorem charge (H : Side G R B) (V : Side (flip G) B R) :
    R.card≤1+(few G R).card+(few (flip G) B).card := by
  classical
  by_cases empty : R=∅
  · simp [empty]
  obtain ⟨a,ha,_,facts⟩ := rest_info H (Finset.nonempty_iff_ne_empty.mpr empty)
  let K := R.erase a
  let F := few G R
  let Q := few (flip G) B
  have er : K.card+1=R.card := Finset.card_erase_add_one ha
  have bound : (K \ F).card≤Q.card := by
    apply choice_count _ _ (fun b x => G b x=true)
    · intro b hb
      obtain ⟨bk,notFew⟩ := Finset.mem_sdiff.mp hb
      have br := (Finset.mem_erase.mp bk).2
      obtain ⟨x,inside,_,yes⟩ := (facts b bk).2.1
      rcases H.cross b br x inside yes with row|col
      · exact False.elim (notFew (closed_few H br row))
      · exact ⟨x,closed_few V inside col,yes⟩
    · intro b hb c hc x hx byy cy
      have br := (Finset.mem_erase.mp (Finset.mem_sdiff.mp hb).1).2
      have cr := (Finset.mem_erase.mp (Finset.mem_sdiff.mp hc).1).2
      exact H.byCol b br c cr x (Finset.mem_filter.mp hx).1 byy cy
  have cover : K⊆F∪(K\F) := by
    intro x hx
    by_cases hf : x∈F
    · exact Finset.mem_union_left _ hf
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hx,hf⟩)
  have cap := (Finset.card_le_card cover).trans (Finset.card_union_le _ _)
  change R.card≤1+F.card+Q.card
  omega

end PEqualNP.Outside.L_meta_25615_aux

open PEqualNP.Outside.L_meta_25615_aux in
theorem PEqualNP.Outside.L_meta_25615 : ∀ (n m : ℕ) (G : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit)
    (R : Finset (Fin n)) (B : Finset (Fin m)) (region entry : Finset ℕ) (root : ℕ),
  let raw := n + m
  let sources := R.image (fun src => src.val) ∪ B.image (fun dest => n + dest.val)
  let wires := sources ∪ region.image (fun idx => raw + idx)
  let gate := PEqualNP.MetaComplexity.NestedCover.gateAt C
  let localReads := PEqualNP.MetaComplexity.NestedCover.readsIn C region
  let allReads := PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size)
  let nbrR := fun (sourceRow : Fin n) => Finset.univ.filter (fun destCol : Fin m => G sourceRow destCol = false)
  let nbrC := fun (sourceCol : Fin m) => Finset.univ.filter (fun destRow : Fin n => G destRow sourceCol = false)
  let hexagon := ∃ (rows : Fin 3 → Fin n) (cols : Fin 3 → Fin m),
    Function.Injective rows ∧ Function.Injective cols ∧
    ∀ i j : Fin 3, i ≠ j → G (rows i) (cols j) = false
  (∀ a, 2 ≤ (nbrR a).card) → (∀ c, 2 ≤ (nbrC c).card) →
  (∀ a b, a ≠ b → ((nbrR a) ∩ (nbrR b)).card ≤ 1) →
  PEqualNP.MetaComplexity.Monotone2 C →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack raw C →
  PEqualNP.Represents.Represents G C → region ⊆ Finset.range C.size → root ∈ wires →
  entry.card ≤ 1 → (∀ w ∈ entry, w ∉ wires ∧ w < root ∧ localReads w = 1) →
  (∀ k ∈ region,
    ((gate k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
     (gate k).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
    (gate k).inputs.length = 2 ∧ ∀ w ∈ (gate k).inputs, w ∈ wires ∨ w ∈ entry) →
  localReads root = 0 →
  (∀ w ∈ wires, w ≠ root → localReads w = 1 ∧ allReads w = 1 ∧ C.output ≠ w) →
  let fewR := R.filter (fun r => (Finset.univ.filter (fun positiveCol : Fin m => G r positiveCol = true)).card ≤ 3)
  let fewC := B.filter (fun c => (Finset.univ.filter (fun positiveRow : Fin n => G positiveRow c = true)).card ≤ 3)
  R.card + B.card ≤ 2 + 2 * (fewR.card + fewC.card) ∧
  (R.card ≤ 3 ∧ B.card ≤ 3) ∧
  (¬hexagon → R.card ≤ 2 ∧ B.card ≤ 2) ∧
  ((∀ a, 3 ≤ (nbrR a).card) → (∀ c, 3 ≤ (nbrC c).card) → R.card ≤ 1 ∧ B.card ≤ 1) := by
  classical
  intro n m G C R B region entry root
  dsimp only
  intro dR dC noFour mono back rep valid member one ports gates last uses
  have nr : GoodRows G := dR
  have nc : GoodRows (PEqualNP.Outside.L_meta_25615_aux.flip G) := dC
  have nf : NoFour G := noFour
  have anyZero {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
      (G : α → β → Bool) (d : GoodRows G) : ∀ a, ∃ c, G a c=false := by
    intro a
    have deg := d a
    obtain ⟨c,hit⟩ := Finset.card_pos.mp (show 0<(neg G a).card by omega)
    exact ⟨c,(Finset.mem_filter.mp hit).2⟩
  obtain ⟨r,c,rect,cross⟩ := privateTree n m G C R B region entry root
    (anyZero G nr) (anyZero (PEqualNP.Outside.L_meta_25615_aux.flip G) nc) mono back rep valid member one ports gates last uses
  have fr : Rect G R B := rect
  have cr : Cross G R B := cross
  have chainR : Chain G R B := r
  have chainC : Chain (PEqualNP.Outside.L_meta_25615_aux.flip G) B R := c
  have oneR := inside_unique nr nf chainR fr
  have oneC := inside_unique nc (flip_four nf) chainC (flip_rect fr)
  let H : Side G R B := ⟨nr,nf,chainR,oneR,oneC,cr⟩
  let V : Side (PEqualNP.Outside.L_meta_25615_aux.flip G) B R := ⟨nc,flip_four nf,chainC,oneC,oneR,flip_cross cr⟩
  refine ⟨?_,⟨three_limit H,three_limit V⟩,?_,?_⟩
  · have rows := charge H V
    have cols := charge V H
    change B.card≤1+(few (PEqualNP.Outside.L_meta_25615_aux.flip G) B).card+(few G R).card at cols
    change R.card+B.card≤2+2*((few G R).card+(few (PEqualNP.Outside.L_meta_25615_aux.flip G) B).card)
    omega
  · intro noHex
    change ¬Hex G at noHex
    constructor
    · by_contra! big; exact noHex (three_hex H big)
    · by_contra! big; exact noHex (flip_hex (three_hex V big))
  · intro highR highC
    exact ⟨at_degree_three H highR,at_degree_three V highC⟩

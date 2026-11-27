import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25551_aux
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
    (L : Layout N C src reg ent top) (S : Finset α) (bad : Finset β) (d : ℕ)
    (A : α → β → Bool) (xs : α → β → List Bool) (len : ∀ a c, (xs a c).length=N)
    (sem : ∀ a c, C.eval (xs a c)=A a c)
    (outside : ∀ a∈S, ∀ b∈S, ∀ c∉bad, ∀ i<N, i∉src → V C (xs a c) i=V C (xs b c) i)
    (privatePins : ∀ a∈S, ∀ c∉bad, ∀ c'∉bad, ∀ i∈src, V C (xs a c) i=V C (xs a c') i)
    (distant : ∀ a b, a≠b → d≤(Finset.univ.filter (fun c => A a c ≠ A b c)).card)
    (narrow : bad.card<d) : S.card≤2+ent.card := by
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
  have inj : Set.InjOn profile S := by
    intro a ha b hb eq
    by_contra diff
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
    have sub : Finset.univ.filter (fun c => A a c≠A b c) ⊆ bad := by
      intro c hc; by_contra h; exact (Finset.mem_filter.mp hc).2 (outsideCol c h)
    have nc := Finset.card_le_card sub; have ds := distant a b diff; omega
  have card := Finset.card_image_iff.mpr inj
  have max := Finset.card_le_univ (S.image profile)
  rw [card,Fintype.card_fin] at max
  exact max

theorem axis {α β : Type} [Fintype β] [DecidableEq α] [DecidableEq β]
    (L : Layout N C src reg ent top) (S : Finset α) (bad : Finset β) (d : ℕ)
    (A : α → β → Bool) (xs : α → β → List Bool) (len : ∀ a c, (xs a c).length=N)
    (sem : ∀ a c, C.eval (xs a c)=A a c)
    (left : α → ℕ) (right : β → ℕ) (ltL : ∀ a, left a<N) (ltR : ∀ b, right b<N)
    (injR : Function.Injective right) (disjoint : ∀ a b, left a≠right b)
    (hs : src=S.image left ∪ bad.image right)
    (atRaw : ∀ a c i, i<N → V C (xs a c) i = decide (i=left a ∨ i=right c))
    (dist : ∀ a b, a≠b → d≤(Finset.univ.filter (fun c => A a c≠A b c)).card)
    (narrow : bad.card<d) : S.card≤2+ent.card := by
  apply side_bound L S bad d A xs len sem _ _ dist narrow
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

end PEqualNP.Outside.L_meta_25551_aux

open PEqualNP.Outside.L_meta_25551_aux PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents in
theorem PEqualNP.Outside.L_meta_25551 : ∀ (n m d : ℕ) (G : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit)
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
  classical
  intro n m d G C R B region entry top
  dsimp only
  intro rowSep colSep back rep valid member one ports inner outer output visible
  let N := n+m
  let src := R.image (fun i : Fin n => i.val) ∪ B.image (fun j : Fin m => n+j.val)
  have L : Layout N C src region entry top :=
    ⟨back,valid,member,one,ports,inner,outer,output,visible⟩
  have lowVal (u : Fin n) (v : Fin m) (i : ℕ) (hi : i<N) :
      V C (oneEach u v) i=decide (i=u.val ∨ i=n+v.val) := by
    change (run C.gates (oneEach u v)).getD i false=_
    rw [run_input _ _ _ (by rwa [oneEach_length]),oneEach_getD]
  have hr (i : Fin n) : i.val<N := by dsimp [N]; have := i.isLt; omega
  have hc (j : Fin m) : n+j.val<N := by dsimp [N]; have := j.isLt; omega
  have dis (i : Fin n) (j : Fin m) : i.val≠n+j.val := by have := i.isLt; omega
  constructor
  · exact axis L R B d G oneEach oneEach_length rep (fun i => i.val) (fun j => n+j.val)
      hr hc (fun _ _ eq => Fin.ext (Nat.add_left_cancel eq)) dis rfl lowVal rowSep
  · exact axis L B R d (fun j i => G i j) (fun j i => oneEach i j) (fun j i => oneEach_length i j)
      (fun j i => rep i j) (fun j => n+j.val) (fun i => i.val) hc hr Fin.val_injective
      (fun j i => (dis i j).symm) (Finset.union_comm _ _)
      (fun j i k hk => by simpa only [or_comm] using lowVal i j k hk) colSep

import PEqualNP.Defs
import PEqualNP.Library.Helpers.FiniteGateBank
import PEqualNP.MetaComplexity.Helpers.LowMergeWires

namespace PEqualNP.GraphInversionSeeds

abbrev I (n : Nat) := Fin n
abbrev Edge (n : Nat) := I n × I n
abbrev F (n : Nat) := (I n → Bool) → Bool

abbrev pos (i : I n) : F n := fun x => x i
abbrev neg (i : I n) : F n := fun x => !(x i)
abbrev eqBit (e : Edge n) : F n := fun x => x e.1 == x e.2
abbrev xorBit (e : Edge n) : F n := fun x => xor (x e.1) (x e.2)
abbrev zz (e : Edge n) : F n := fun x => !(x e.1) && !(x e.2)
abbrev oz (e : Edge n) : F n := fun x => x e.1 && !(x e.2)
abbrev zo (e : Edge n) : F n := fun x => !(x e.1) && x e.2

noncomputable def raw (E : Finset (Edge n)) : Finset (F n) := by
  classical
  exact {fun _ => false,fun _ => true} ∪ Finset.univ.image pos ∪ E.image eqBit ∪ E.image xorBit
noncomputable def target (E : Finset (Edge n)) : Finset (F n) := by
  classical
  exact Finset.univ.image neg ∪ E.image zz ∪ E.image oz ∪ E.image zo

private abbrev bAnd {X : Type} (x y : X → Bool) : X → Bool := fun a => x a && y a
private abbrev bOr {X : Type} (x y : X → Bool) : X → Bool := fun a => x a || y a

def hits (E : Finset (Edge n)) (S : Finset (I n)) : Prop :=
  ∀ C : Finset (I n), C.Nonempty → (∀ e∈E, e.1∈C ↔ e.2∈C) →
    ∃ i∈C, i∈S

def sampleStep {X : Type} (U : Finset (X → Bool)) (z : X → Bool) : Prop :=
  ∃ x∈U, ∃ y∈U, z=bAnd x y ∨ z=bOr x y

abbrev Step (U : Finset (F n)) (z : F n) := sampleStep U z

theorem grow (E : Finset (Edge n)) (S : Finset (I n))
    (D U : Finset (F n)) (cover : hits E S) (rawIn : raw E ⊆ U)
    (targetIn : target E ⊆ D) (seeds : ∀ i∈S, neg i∈U)
    (stable : ∀ z∈D, Step U z → z∈U) : target E ⊆ U := by
  classical
  have input (i : I n) : pos i∈U := rawIn (by simp [raw])
  have same (e) (he : e∈E) : eqBit e∈U := rawIn (by simp only [raw,Finset.mem_union]; exact Or.inl (Or.inr (Finset.mem_image_of_mem _ he)))
  have diff (e) (he : e∈E) : xorBit e∈U := rawIn (by simp only [raw,Finset.mem_union]; exact Or.inr (Finset.mem_image_of_mem _ he))
  have mkAnd {x y z : F n} (hx : x∈U) (hy : y∈U) (hz : z∈target E)
      (eq : z=bAnd x y) : z∈U := stable z (targetIn hz) ⟨x,hx,y,hy,Or.inl eq⟩
  have mkOr {x y z : F n} (hx : x∈U) (hy : y∈U) (hz : z∈target E)
      (eq : z=bOr x y) : z∈U := stable z (targetIn hz) ⟨x,hx,y,hy,Or.inr eq⟩
  have first (e) (he : e∈E) : oz e∈U :=
    mkAnd (input e.1) (diff e he) (by simp only [target,Finset.mem_union]; exact Or.inl (Or.inr (Finset.mem_image_of_mem _ he))) (by
      funext x; cases h : x e.1 <;> cases k : x e.2 <;> simp [oz,pos,bAnd,xorBit,h,k])
  have second (e) (he : e∈E) : zo e∈U :=
    mkAnd (input e.2) (diff e he) (by simp only [target,Finset.mem_union]; exact Or.inr (Finset.mem_image_of_mem _ he)) (by
      funext x; cases h : x e.1 <;> cases k : x e.2 <;> simp [zo,pos,bAnd,xorBit,h,k])
  have zeroLeft (e) (he : e∈E) (hi : neg e.1∈U) : zz e∈U :=
    mkAnd hi (same e he) (by simp only [target,Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (Finset.mem_image_of_mem _ he)))) (by
      funext x; cases h : x e.1 <;> cases k : x e.2 <;> simp [zz,neg,bAnd,eqBit,h,k])
  have zeroRight (e) (he : e∈E) (hi : neg e.2∈U) : zz e∈U :=
    mkAnd hi (same e he) (by simp only [target,Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (Finset.mem_image_of_mem _ he)))) (by
      funext x; cases h : x e.1 <;> cases k : x e.2 <;> simp [zz,neg,bAnd,eqBit,h,k])
  have spread (e) (he : e∈E) : neg e.1∈U ↔ neg e.2∈U := by
    constructor
    · intro h
      exact mkOr (zeroLeft e he h) (first e he) (by simp [target]) (by
        funext x; cases h : x e.1 <;> cases k : x e.2 <;> simp [neg,bOr,zz,oz,h,k])
    · intro h
      exact mkOr (zeroRight e he h) (second e he) (by simp [target]) (by
        funext x; cases h : x e.1 <;> cases k : x e.2 <;> simp [neg,bOr,zz,zo,h,k])
  have all (i : I n) : neg i∈U := by
    by_contra absent
    let C := Finset.univ.filter (fun j : I n => neg j∉U)
    have mem (j) : j∈C ↔ neg j∉U := by simp [C]
    obtain ⟨j,hj,hs⟩ := cover C ⟨i,(mem i).mpr absent⟩
      (fun e he => (mem _).trans ((not_congr (spread e he)).trans (mem _).symm))
    exact (mem j).mp hj (seeds j hs)
  intro z hz
  simp only [target,Finset.mem_union,Finset.mem_image,Finset.mem_univ,true_and] at hz
  rcases hz with (((⟨i,rfl⟩|⟨e,he,rfl⟩)|⟨e,he,rfl⟩)|⟨e,he,rfl⟩)
  · exact all _
  · exact zeroLeft e he (all _)
  · exact first _ he
  · exact second _ he

private theorem obstruction (E : Finset (Edge n)) (S C : Finset (I n))
    (closed : ∀ e∈E, e.1∈C ↔ e.2∈C) (miss : ∀ i∈C, i∉S) :
    ∃ a b : I n → Bool,
      (∀ z∈raw E, z a = true → z b = true) ∧
      (∀ i∈S, neg i a = true → neg i b = true) ∧
      ∀ i∈C, neg i a = true ∧ neg i b = false := by
  classical
  let b := fun i => decide (i∈C)
  have agree (e) (he : e∈E) : b e.1=b e.2 := by simp [b,closed e he]
  refine ⟨fun _ => false,b,?_,?_,?_⟩
  · intro z hz
    simp only [raw,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
      Finset.mem_image,Finset.mem_univ,true_and] at hz
    rcases hz with ((((rfl|rfl)|⟨i,rfl⟩)|⟨e,he,rfl⟩)|⟨e,he,rfl⟩)
    · simp
    · simp
    · simp [pos]
    · simp [eqBit,agree e he]
    · simp [xorBit]
  · intro i hi
    have out : i∉C := fun h => miss i h hi
    simp [neg,b,out]
  · intro i hi
    simp [neg,b,hi]

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.FiniteGateBank
open Classical

abbrev sampleRow {X : Type} (L : List (X → Bool)) (x : X) := L.map (fun f => f x)
def sampleFits {X : Type} (L : List (X → Bool)) (T : Finset (X → Bool)) (p : Nat) : Prop :=
  ∃ C : Circuit, Monotone2 C ∧ NestedCover.ReadsBack L.length C ∧
    C.output < L.length+C.size ∧ C.size≤p ∧
    ∀ f∈T, ∃ i<L.length+C.size, ∀ x, (C.wires (sampleRow L x)).getD i false=f x

private theorem emitAll {X : Type} [DecidableEq (X → Bool)] (L : List (X → Bool)) (T : Finset (X → Bool))
    (closed : ∀ U, L.toFinset⊆U → (∀ z∈T, sampleStep U z → z∈U) → T⊆U)
    (U : Finset (X → Bool)) (base : L.toFinset⊆U) (net : Net L.length)
    (live : ∀ f∈U, net.has (sampleRow L) f) :
    ∃ net' : Net L.length, net'.cost=net.cost ∧ net'.gates.length≤net.gates.length+(T\U).card ∧
      ∀ f∈T, net'.has (sampleRow L) f := by
  by_cases doneT : T⊆U
  · exact ⟨net,rfl,by omega,fun f hf => live f (doneT hf)⟩
  have advance : ∃ z∈T, z∉U ∧ sampleStep U z := by
    by_contra! none
    exact doneT (closed U base (fun z hz step => by by_contra h; exact none z hz h step))
  obtain ⟨z,hz,fresh,x,hx,y,hy,op⟩ := advance
  have build : ∃ q, Grow (sampleRow L) net q 1 0 ∧ q.has (sampleRow L) z := by
    rcases op with rfl|rfl
    · simpa only [if_true] using binary (raw := sampleRow L) (fun _ => by simp [sampleRow]) net x y (live x hx) (live y hy) true
    · simpa only [Bool.false_eq_true,if_false] using binary (raw := sampleRow L) (fun _ => by simp [sampleRow]) net x y (live x hx) (live y hy) false
  obtain ⟨q,progress,hzq⟩ := build
  have diff : T \ insert z U=(T\U).erase z := by ext i; simp; tauto
  have one : (T\insert z U).card+1=(T\U).card := by
    rw [diff]; exact Finset.card_erase_add_one (Finset.mem_sdiff.mpr ⟨hz,fresh⟩)
  obtain ⟨r,hr,size,done⟩ := emitAll L T closed (insert z U) (base.trans (Finset.subset_insert _ _)) q
    (fun v hv => (Finset.mem_insert.mp hv).elim (fun eq => eq ▸ hzq) (fun h => progress.1 _ (live v h)))
  exact ⟨r,by simpa [progress.2.2] using hr,by have inc := progress.2.1; omega,done⟩
termination_by (T\U).card

theorem tightBuild {X : Type} [DecidableEq (X → Bool)] (L : List (X → Bool)) (T : Finset (X → Bool)) (nonempty : 0<L.length)
    (closed : ∀ U, L.toFinset⊆U → (∀ z∈T, sampleStep U z → z∈U) → T⊆U) :
    sampleFits L T (T\L.toFinset).card := by
  have base (f) (hf : f∈L.toFinset) : (empty L.length).has (sampleRow L) f := by
    obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp hf)
    refine ⟨i,by simpa [empty] using hi,?_⟩
    intro x
    change (sampleRow L x).getD i false = f x
    rw [List.getD_eq_getElem _ _ (by simpa using hi)]
    simpa [sampleRow] using congrFun he x
  obtain ⟨q,cost,size,all⟩ := emitAll L T closed L.toFinset (by rfl) (empty L.length) base
  let C : Circuit := ⟨q.gates,0⟩
  have no : (C.gates.filter (fun g => decide (g.op=GateOp.not)))=[] := by
    apply List.length_eq_zero_iff.mp
    simpa [C,Net.cost,NotBracket.notCount,empty] using cost
  have positive : Monotone2 C := by
    intro g hg
    have types := q.fan g hg
    have hn : g.op ≠ GateOp.not := by
      intro bad
      have h : g∈C.gates.filter (fun t => decide (t.op=GateOp.not)) := by simp [hg,bad]
      rw [no] at h
      simp at h
    simpa [Set.mem_insert_iff,Set.mem_singleton_iff,hn] using types
  exact ⟨C,positive,q.readsBack,by change 0<L.length+_; omega,by simpa [C,Circuit.size,empty] using size,all⟩

theorem countMissing {X : Type} [DecidableEq (X → Bool)] (L : List (X → Bool)) (T : Finset (X → Bool)) {p} (h : sampleFits L T p) :
    (T\L.toFinset).card≤p := by
  obtain ⟨C,_,_,_,size,all⟩ := h
  let added (j : Fin C.size) : X → Bool := fun x => (C.wires (sampleRow L x)).getD (L.length+j.val) false
  have sub : T\L.toFinset ⊆ Finset.univ.image added := by
    intro f hf
    obtain ⟨present,missing⟩ := Finset.mem_sdiff.mp hf
    obtain ⟨i,hi,he⟩ := all f present
    by_cases input : i<L.length
    · have eq : L[i]=f := by
        funext x
        obtain ⟨tail,old,_⟩ := CoverCircuit.run_prefix C.gates (sampleRow L x)
        have q := he x
        rw [CoverCircuit.wires_eq,old,List.getD_append _ _ _ _ (by simpa using input),
          List.getD_eq_getElem _ _ (by simpa using input)] at q
        simpa [sampleRow] using q
      exact False.elim (missing (List.mem_toFinset.mpr (eq ▸ List.getElem_mem input)))
    · refine Finset.mem_image.mpr ⟨⟨i-L.length,by omega⟩,Finset.mem_univ _,?_⟩
      funext x
      simpa [added,show L.length+(i-L.length)=i by omega] using he x
  exact (Finset.card_le_card sub).trans ((Finset.card_image_le.trans (by simp)).trans size)

abbrev row (L : List (F n)) (x : I n → Bool) := sampleRow L x
abbrev fits (L : List (F n)) (T : Finset (F n)) (p : Nat) := sampleFits L T p

private theorem lower (E : Finset (Edge n)) (S : Finset (I n)) (L : List (F n))
    (inputs : L.toFinset=raw E ∪ S.image neg) {p} (fit : fits L (target E) p) : hits E S := by
  intro C nonempty closed
  by_contra! miss
  obtain ⟨a,b,base,seed,drops⟩ := obstruction E S C closed miss
  obtain ⟨D,mono,_,_,_,reads⟩ := fit
  have ordered : LowMergeProof.LeL (row L a) (row L b) := by
    intro i
    by_cases h : i<L.length
    · simp only [row,List.getD_eq_getElem _ _ (by simpa using h : i<(row L a).length),
        List.getD_eq_getElem _ _ (by simpa using h : i<(row L b).length), List.getElem_map]
      have mem : L[i]∈raw E ∪ S.image neg := inputs ▸ List.mem_toFinset.mpr (List.getElem_mem h)
      rcases Finset.mem_union.mp mem with hr|hs
      · exact base _ hr
      · obtain ⟨j,hj,eq⟩ := Finset.mem_image.mp hs
        rw [←eq]
        exact seed j hj
    · simp [row,List.getD_eq_getElem?_getD,List.getElem?_eq_none (Nat.le_of_not_gt h)]
  obtain ⟨i,hi⟩ := nonempty
  obtain ⟨j,_,read⟩ := reads (neg i) (by simp [target])
  have m := LowMergeProof.wires_mono D (fun g hg => (mono g hg).1) (row L a) (row L b) (by simp) ordered j
  rw [read a,read b,(drops i hi).1,(drops i hi).2] at m
  simp at m

theorem exactBudget (E : Finset (Edge n)) (S : Finset (I n)) (L : List (F n))
    (inputs : L.toFinset=raw E ∪ S.image neg) (p : Nat) :
    fits L (target E) p ↔ hits E S ∧ ((target E)\L.toFinset).card≤p := by
  refine ⟨fun h => ⟨lower E S L inputs h,countMissing (X:=I n → Bool) L (target E) h⟩,?_⟩
  rintro ⟨cover,budget⟩
  have nonempty : 0<L.length := by
    obtain ⟨f,hf⟩ : L.toFinset.Nonempty := ⟨fun _ => false,by rw [inputs]; simp [raw]⟩
    exact List.length_pos_of_mem (List.mem_toFinset.mp hf)
  obtain ⟨D,hm,hr,ho,sz,all⟩ := tightBuild L (target E) nonempty (by
    intro U hU stable
    rw [inputs] at hU
    exact grow E S (target E) U cover (Finset.union_subset_iff.mp hU).1 (by rfl)
      (fun i hi => (Finset.union_subset_iff.mp hU).2 (Finset.mem_image_of_mem _ hi)) stable)
  exact ⟨D,hm,hr,ho,sz.trans budget,all⟩

private noncomputable def signature (f : F n) : Bool × Bool × Finset (I n) × Finset (I n) :=
  (f (fun _ => false), f (fun _ => true),
   Finset.univ.filter (fun j => f (fun i => decide (i=j)) ≠ f (fun _ => false)),
   Finset.univ.filter (fun j => f (fun i => decide (i≠j)) ≠ f (fun _ => true)))

private theorem sigConst (b : Bool) : signature (n:=n) (fun _ => b) = (b,b,∅,∅) := by
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · rfl
  · rfl
  · ext j
    simp [signature]
  · ext j
    simp [signature]

private theorem sigPos (i : I n) : signature (n:=n) (pos i) = (false,true,{i},{i}) := by
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · rfl
  · rfl
  · ext j
    by_cases h : i=j <;> simp_all [signature,pos] <;> grind
  · ext j
    by_cases h : i=j <;> simp_all [signature,pos] <;> grind

private theorem sigNeg (i : I n) : signature (n:=n) (neg i) = (true,false,{i},{i}) := by
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · rfl
  · rfl
  · ext j
    by_cases h : i=j <;> simp_all [signature,neg] <;> grind
  · ext j
    by_cases h : i=j <;> simp_all [signature,neg] <;> grind

private theorem sigSame (e : Edge n) (h : e.1≠e.2) : signature (n:=n) (eqBit e) = (true,true,{e.1,e.2},{e.1,e.2}) := by
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · rfl
  · rfl
  · ext j
    by_cases a : e.1=j <;> by_cases b : e.2=j <;> simp_all [signature,eqBit] <;> grind
  · ext j
    by_cases a : e.1=j <;> by_cases b : e.2=j <;> simp_all [signature,eqBit] <;> grind

private theorem sigDiff (e : Edge n) (h : e.1≠e.2) : signature (n:=n) (xorBit e) = (false,false,{e.1,e.2},{e.1,e.2}) := by
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · rfl
  · rfl
  · ext j
    by_cases a : e.1=j <;> by_cases b : e.2=j <;> simp_all [signature,xorBit] <;> grind
  · ext j
    by_cases a : e.1=j <;> by_cases b : e.2=j <;> simp_all [signature,xorBit] <;> grind

private theorem sigZero (e : Edge n) (h : e.1≠e.2) : signature (n:=n) (zz e) = (true,false,{e.1,e.2},∅) := by
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · rfl
  · rfl
  · ext j
    by_cases a : e.1=j <;> by_cases b : e.2=j <;> simp_all [signature,zz] <;> grind
  · ext j
    by_cases a : e.1=j <;> by_cases b : e.2=j <;> simp_all [signature,zz] <;> grind

private theorem sigLeft (e : Edge n) (h : e.1≠e.2) : signature (n:=n) (oz e) = (false,false,{e.1},{e.2}) := by
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · rfl
  · rfl
  · ext j
    by_cases a : e.1=j <;> by_cases b : e.2=j <;> simp_all [signature,oz] <;> grind
  · ext j
    by_cases a : e.1=j <;> by_cases b : e.2=j <;> simp_all [signature,oz] <;> grind

private theorem sigRight (e : Edge n) (h : e.1≠e.2) : signature (n:=n) (zo e) = (false,false,{e.2},{e.1}) := by
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · rfl
  · rfl
  · ext j
    by_cases a : e.1=j <;> by_cases b : e.2=j <;> simp_all [signature,zo] <;> grind
  · ext j
    by_cases a : e.1=j <;> by_cases b : e.2=j <;> simp_all [signature,zo] <;> grind

private noncomputable def tag (f : F n) : Nat :=
  let z := signature f
  if z.1 then (if z.2.1 then 0 else if z.2.2.2.Nonempty then 1 else 2)
  else if z.2.1 then 0 else if z.2.2.1.card=1 then 3 else 0

private theorem negInj : Function.Injective (neg (n:=n)) := by
  intro i j same
  have h := congrArg signature same
  simpa [sigNeg] using h

theorem countTargets (E : Finset (Edge n)) (sorted : ∀ e∈E, e.1<e.2) (S : Finset (I n)) :
    ((target E) \ (raw E ∪ S.image neg)).card = n + 3*E.card - S.card := by
  classical
  have ne (e) (he : e∈E) := ne_of_lt (sorted e he)
  have zeroTag (e) (he : e∈E) : tag (zz e)=2 := by simp [tag,sigZero e (ne e he)]
  have leftTag (e) (he : e∈E) : tag (oz e)=3 := by simp [tag,sigLeft e (ne e he)]
  have rightTag (e) (he : e∈E) : tag (zo e)=3 := by simp [tag,sigRight e (ne e he)]
  have negTag (i : I n) : tag (neg i)=1 := by simp [tag,sigNeg]
  have rawTag (f) (hf : f∈raw E) : tag f=0 := by
    simp only [raw,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.mem_image,
      Finset.mem_univ,true_and] at hf
    rcases hf with ((((rfl|rfl)|⟨i,rfl⟩)|⟨e,he,rfl⟩)|⟨e,he,rfl⟩)
    · simp [tag,sigConst]
    · simp [tag,sigConst]
    · simp [tag,sigPos]
    · simp [tag,sigSame e (ne e he)]
    · simp [tag,sigDiff e (ne e he),ne e he]
  have zeroInj : Set.InjOn zz (E : Set (Edge n)) := by
    intro e he d hd eq
    have hs := congrArg (fun z => (signature z).2.2.1) eq
    simp only [sigZero e (ne e he),sigZero d (ne d hd)] at hs
    have ha : e.1∈({d.1,d.2}:Finset (I n)) := hs ▸ Finset.mem_insert_self _ _
    have hb : e.2∈({d.1,d.2}:Finset (I n)) := hs ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
    have ea := sorted e he
    have eb := sorted d hd
    apply Prod.ext <;> apply Fin.ext <;> simp only [Fin.ext_iff] at ha hb <;> change e.1.val < e.2.val at ea <;> change d.1.val < d.2.val at eb <;> omega
  have leftInj : Set.InjOn oz (E : Set (Edge n)) := by
    intro e he d hd eq
    have h := congrArg signature eq
    simp [sigLeft e (ne e he),sigLeft d (ne d hd)] at h
    exact Prod.ext h.1 h.2
  have rightInj : Set.InjOn zo (E : Set (Edge n)) := by
    intro e he d hd eq
    have h := congrArg signature eq
    simp [sigRight e (ne e he),sigRight d (ne d hd)] at h
    exact Prod.ext h.2 h.1
  let V := Finset.univ.image (neg (n:=n))
  let Z := E.image zz
  let A := E.image oz
  let B := E.image zo
  have vTag f (hf : f∈V) : tag f=1 := by obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hf; exact negTag i
  have zTag f (hf : f∈Z) : tag f=2 := by obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hf; exact zeroTag e he
  have aTag f (hf : f∈A) : tag f=3 := by obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hf; exact leftTag e he
  have bTag f (hf : f∈B) : tag f=3 := by obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hf; exact rightTag e he
  have diffAB : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro f ha hb
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨d,hd,eq⟩ := Finset.mem_image.mp hb
    have h := congrArg signature eq
    simp [sigLeft e (ne e he),sigRight d (ne d hd)] at h
    have ea := sorted e he
    have da := sorted d hd
    obtain ⟨ha,hb⟩ := h
    rw [←ha,←hb] at ea
    exact (lt_asymm ea da)
  have dvz : Disjoint V Z := Finset.disjoint_left.mpr (fun {f} h k => by have := vTag f h; have := zTag f k; omega)
  have dva : Disjoint (V∪Z) A := by
    apply Finset.disjoint_left.mpr
    intro f hx hy
    have := aTag _ hy
    rcases Finset.mem_union.mp hx with h|h
    · have := vTag _ h; omega
    · have := zTag _ h; omega
  have dvb : Disjoint (V∪Z∪A) B := by
    apply Finset.disjoint_left.mpr
    intro f hx hy
    have := bTag _ hy
    rcases Finset.mem_union.mp hx with h|h
    · rcases Finset.mem_union.mp h with h|h
      · have := vTag _ h; omega
      · have := zTag _ h; omega
    · exact Finset.disjoint_left.mp diffAB h hy
  have ct : (target E).card=n+3*E.card := by
    change (V∪Z∪A∪B).card=_
    rw [Finset.card_union_of_disjoint dvb,Finset.card_union_of_disjoint dva,Finset.card_union_of_disjoint dvz]
    simp only [V,Z,A,B,Finset.card_image_of_injective _ negInj,Finset.card_image_of_injOn zeroInj,
      Finset.card_image_of_injOn leftInj,Finset.card_image_of_injOn rightInj,Finset.card_univ,Fintype.card_fin]
    omega
  have disj : Disjoint (target E) (raw E) := by
    apply Finset.disjoint_left.mpr
    intro f ht hr
    have h0 := rawTag _ hr
    change f∈V∪Z∪A∪B at ht
    simp only [Finset.mem_union] at ht
    rcases ht with (((h|h)|h)|h)
    · have := vTag _ h; omega
    · have := zTag _ h; omega
    · have := aTag _ h; omega
    · have := bTag _ h; omega
  have sub : S.image neg ⊆ target E := by
    rintro f hf
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hf
    simp [target]
  have drop : target E \ (raw E ∪ S.image neg) = target E \ S.image neg := by
    ext f
    simp only [Finset.mem_sdiff,Finset.mem_union]
    exact ⟨fun h => ⟨h.1,fun v => h.2 (Or.inr v)⟩,fun h => ⟨h.1,fun v => v.elim
      (Finset.disjoint_left.mp disj h.1) h.2⟩⟩
  rw [drop,Finset.card_sdiff_of_subset sub,ct,Finset.card_image_of_injective _ negInj]

set_option maxHeartbeats 1000000 in
theorem criterion :
∀ (n : Nat) (E : Finset (Fin n × Fin n)), (∀ e ∈ E, e.1 < e.2) →
  ∀ (S : Finset (Fin n)),
  letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
  let F := (Fin n → Bool) → Bool
  let bit := fun (i : Fin n) (x : Fin n → Bool) => x i
  let inv := fun (i : Fin n) (x : Fin n → Bool) => !(x i)
  let eqBit := fun (e : Fin n × Fin n) (x : Fin n → Bool) => x e.1 == x e.2
  let diff := fun (e : Fin n × Fin n) (x : Fin n → Bool) => xor (x e.1) (x e.2)
  let raw : Finset F := {fun _ => false, fun _ => true} ∪ Finset.univ.image bit ∪ E.image eqBit ∪ E.image diff
  let starts := raw ∪ S.image inv
  let demand : Finset F := Finset.univ.image inv ∪
    E.image (fun e x => !(x e.1) && !(x e.2)) ∪ E.image (fun e x => x e.1 && !(x e.2)) ∪
    E.image (fun e x => !(x e.1) && x e.2)
  let hit := ∀ C : Finset (Fin n), C.Nonempty → (∀ e∈E, e.1∈C ↔ e.2∈C) → ∃ i∈C, i∈S
  (demand \ starts).card = n+3*E.card-S.card ∧
  ∀ (L : List F), L.toFinset = starts → ∀ p : Nat,
    (∃ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack L.length D ∧
      D.output < L.length+D.size ∧ D.size ≤ p ∧
      ∀ f∈demand, ∃ i<L.length+D.size, ∀ x, (D.wires (L.map (fun z => z x))).getD i false = f x) ↔
    hit ∧ n+3*E.card-S.card ≤ p
:= by
  intro n E sorted S
  dsimp only
  have count := countTargets E sorted S
  dsimp only [target,raw,pos,neg,eqBit,xorBit,zz,oz,zo] at count
  constructor
  · convert! count using 0 <;> congr! <;> apply Subsingleton.elim
  intro L h p
  have inputs : L.toFinset = raw E ∪ S.image neg := by
    dsimp only [raw,pos,neg,eqBit,xorBit]
    convert! h using 0 <;> congr! <;> apply Subsingleton.elim
  have bound := exactBudget E S L inputs p
  rw [inputs,countTargets E sorted S] at bound
  dsimp only [fits,sampleFits,target,neg,zz,oz,zo,row,sampleRow,hits] at bound
  convert! bound using 0 <;> congr! <;> apply Subsingleton.elim

end PEqualNP.GraphInversionSeeds

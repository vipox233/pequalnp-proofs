import PEqualNP.Defs
import PEqualNP.Library.Helpers.FiniteGateBank
import PEqualNP.MetaComplexity.Helpers.LowMergeWires

namespace PEqualNP.GraphSeedSamples

open Classical CircuitLowerBounds MetaComplexity FiniteGateBank

abbrev Word (n : Nat) := Finset (Fin n)
abbrev Test (n : Nat) := Word n → Bool

def row (L : List (Test n)) (x : Word n) := L.map (fun f => f x)
def ordered (L : List (Test n)) (x y : Word n) := ∀ f∈L, f x=true → f y=true

def fits (A : Finset (Word n)) (L : List (Test n)) (T : Finset (Test n)) :=
  ∃ C : Circuit, Monotone2 C ∧ NestedCover.ReadsBack L.length C ∧ C.output<L.length+C.size ∧
    ∀ f∈T, ∃ j<L.length+C.size, ∀ x∈A, (C.wires (row L x)).getD j false=f x

private theorem everyList {X J : Type} {w : Nat} {r : X → List Bool}
    (width : ∀ x,(r x).length=w) (p : Net w) (one : p.has r (fun _ => true))
    (l : List J) (f : J → X → Bool) (live : ∀ i∈l,p.has r (f i)) :
    ∃ q, Grow r p q l.length 0 ∧ q.has r (fun x => l.all (fun j => f j x)) := by
  induction l with
  | nil => exact ⟨p,start _ _,one⟩
  | cons i l ih =>
    obtain ⟨q,g,old⟩ := ih (fun j hj => live j (by simp [hj]))
    obtain ⟨s,k,out⟩ := binary width q _ _ (g.1 _ (live i (by simp))) old true
    exact ⟨s,chain g k,by simpa [List.all_cons] using out⟩

private theorem interpolation (A : Finset (Word n)) (L : List (Test n)) (T : Finset (Test n))
    (zero : (fun _ => false)∈L) (one : (fun _ => true)∈L) :
    fits A L T ↔ ∀ x∈A, ∀ y∈A, ordered L x y → ∀ f∈T, f x=true → f y=true := by
  constructor
  · rintro ⟨C,mono,_,_,get⟩ x hx y hy ord f hf fv
    obtain ⟨j,_,val⟩ := get f hf
    have le : LowMergeProof.LeL (row L x) (row L y) := by
      intro i
      by_cases h : i<L.length
      · rw [List.getD_eq_getElem _ _ (by simpa [row] using h : i<(row L x).length),
          List.getD_eq_getElem _ _ (by simpa [row] using h : i<(row L y).length)]
        simpa [row] using ord L[i] (List.getElem_mem h)
      · simp [row,List.getD_eq_getElem?_getD,List.getElem?_eq_none (Nat.le_of_not_gt h)]
    have imp := LowMergeProof.wires_mono C (fun g hg => (mono g hg).1) _ _ (by simp [row]) le j
    rw [val x hx,val y hy] at imp
    exact imp fv
  · intro mono
    let r := fun x : A => row L x.val
    have width (x : A) : (r x).length=L.length := by simp [r,row]
    let p := empty L.length
    have inp (f : Test n) (hf : f∈L) : p.has r (fun x => f x.val) := by
      obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hf
      refine ⟨i,by simpa [p,empty] using hi,?_⟩
      intro x
      change (row L x.val).getD i false = f x.val
      rw [List.getD_eq_getElem _ _ (by simpa [row] using hi)]
      simpa [row] using congrFun he x.val
    let U := A.toList
    let term := fun (x : Word n) (y : A) => (L.filter (fun f => f x)).all (fun f => f y.val)
    have termIff (x : Word n) (y : A) : term x y=true ↔ ordered L x y := by
      simp only [term,ordered,List.all_eq_true,List.mem_filter,and_imp]
    obtain ⟨q,cq,allTerms⟩ := batch (raw:=r) p U term L.length 0 (by
      intro x _ net keep
      obtain ⟨s,gs,out⟩ := everyList width net (keep _ (inp _ one)) (L.filter (fun f => f x))
        (fun f y => f y.val) (fun f hf => keep _ (inp f (List.mem_filter.mp hf).1))
      exact ⟨s,allowance gs (List.length_filter_le ..),out⟩)
    obtain ⟨s,cs,allOut⟩ := batch (raw:=r) q T.toList (fun f (x : A) => f x.val) U.length 0 (by
      intro f hf net keep
      obtain ⟨v,gv,out⟩ := anyList width net (keep _ (cq.1 _ (inp _ zero))) (U.filter f) term
        (fun x hx => keep _ (allTerms x (List.mem_filter.mp hx).1))
      refine ⟨v,allowance gv (List.length_filter_le ..),?_⟩
      have eq : (fun y : A => (U.filter f).any (fun x => term x y)) = fun y => f y.val := by
        funext y
        apply Bool.eq_iff_iff.mpr
        rw [List.any_eq_true]
        constructor
        · rintro ⟨x,hx,holds⟩
          obtain ⟨a,b⟩ := List.mem_filter.mp hx
          exact mono x (by simpa [U] using a) y.val y.property ((termIff x y).mp holds) f
            (by simpa using hf) b
        · intro b
          exact ⟨y.val,List.mem_filter.mpr ⟨by simpa [U] using y.property,b⟩,
            (termIff _ _).mpr (fun _ _ => id)⟩
      exact eq ▸ out)
    let C : Circuit := ⟨s.gates,0⟩
    have cost : s.cost=0 := by rw [cs.2.2,cq.2.2]; simp [p,empty,Net.cost,NotBracket.notCount]
    have no : (C.gates.filter (fun g => decide (g.op=GateOp.not)))=[] := by
      apply List.length_eq_zero_iff.mp
      simpa [C,Net.cost,NotBracket.notCount] using cost
    refine ⟨C,?_,s.readsBack,by have := List.length_pos_of_mem zero; change 0<L.length+_; omega,?_⟩
    · intro g hg
      have ops := s.fan g hg
      have notGate : g.op≠GateOp.not := by
        intro h
        have m : g∈C.gates.filter (fun t => decide (t.op=GateOp.not)) := by simp [hg,h]
        rw [no] at m
        simp at m
      simpa [Set.mem_insert_iff,Set.mem_singleton_iff,notGate] using ops
    · intro f hf
      obtain ⟨j,hj,h⟩ := allOut f (by simpa using hf)
      exact ⟨j,hj,fun x hx => h ⟨x,hx⟩⟩

abbrev Edge (n : Nat) := Fin n × Fin n
def bit (i : Fin n) (x : Word n) := decide (i∈x)
def inv (i : Fin n) (x : Word n) := decide (i∉x)
def same (e : Edge n) (x : Word n) := decide (e.1∈x ↔ e.2∈x)
def cross (e : Edge n) (x : Word n) := !(same e x)

noncomputable def bank (E : Finset (Edge n)) (S : Word n) : Finset (Test n) :=
  {fun _ => false,fun _ => true} ∪ Finset.univ.image bit ∪ E.image same ∪ E.image cross ∪ S.image inv

def closed (E : Finset (Edge n)) (V : Word n) := ∀ e∈E, e.1∈V ↔ e.2∈V

private theorem orderIff (E : Finset (Edge n)) (S x y : Word n) :
    ordered (bank E S).toList x y ↔ x⊆y ∧ closed E (y\x) ∧ Disjoint (y\x) S := by
  classical
  constructor
  · intro ord
    have raw (f) (hf : f∈bank E S) := ord f (by simpa using hf)
    have sub : x⊆y := by
      intro i hi
      exact of_decide_eq_true (raw (bit i) (by simp [bank]) (by simpa [bit] using hi))
    refine ⟨sub,?_,?_⟩
    · intro e he
      have a := raw (same e) (by simp only [bank,Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (Finset.mem_image_of_mem _ he))))
      have b := raw (cross e) (by simp only [bank,Finset.mem_union]; exact Or.inl (Or.inr (Finset.mem_image_of_mem _ he)))
      have s := @sub e.1
      have t := @sub e.2
      simp [same,cross] at a b
      simp only [Finset.mem_sdiff]
      tauto
    · apply Finset.disjoint_left.mpr
      intro i hi hs
      have a := raw (inv i) (by simp only [bank,Finset.mem_union]; exact Or.inr (Finset.mem_image_of_mem _ hs))
      have p := Finset.mem_sdiff.mp hi
      simpa [inv,p.1,p.2] using a
  · rintro ⟨sub,c,d⟩ f hf
    have h : f∈bank E S := by simpa using hf
    simp only [bank,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.mem_image,
      Finset.mem_univ,true_and] at h
    rcases h with (((((rfl|rfl)|⟨i,rfl⟩)|⟨e,he,rfl⟩)|⟨e,he,rfl⟩)|⟨i,hi,rfl⟩)
    · exact id
    · exact id
    · simpa [bit] using @sub i
    · have a := c e he
      have s := @sub e.1
      have t := @sub e.2
      simp only [Finset.mem_sdiff] at a
      simp [same]
      tauto
    · have a := c e he
      have s := @sub e.1
      have t := @sub e.2
      simp only [Finset.mem_sdiff] at a
      simp [cross,same]
      tauto
    · simp [inv]
      intro hx hy
      exact Finset.disjoint_left.mp d (Finset.mem_sdiff.mpr ⟨hy,hx⟩) hi

def detects (A : Finset (Word n)) (E : Finset (Edge n)) (S : Word n) :=
  ∀ x∈A, ∀ y∈A, x⊆y → closed E (y\x) → Disjoint (y\x) S → y=x

private theorem fitIff (A : Finset (Word n)) (E : Finset (Edge n)) (S : Word n)
    (T : Finset (Test n)) (required : ∀ i, inv i∈T) :
    fits A (bank E S).toList T ↔ detects A E S := by
  rw [interpolation A _ T (by simp [bank]) (by simp [bank])]
  constructor
  · intro can x hx y hy sub c d
    have ord := (orderIff E S x y).mpr ⟨sub,c,d⟩
    apply Finset.Subset.antisymm _ sub
    intro i hi
    by_contra h
    have v := can x hx y hy ord (inv i) (required i) (by simp [inv,h])
    simpa [inv,hi] using v
  · intro det x hx y hy ord f _ fx
    obtain ⟨sub,c,d⟩ := (orderIff E S x y).mp ord
    rw [det x hx y hy sub c d]
    exact fx

private theorem edgesBound {I : Type} [DecidableEq I] (D : Finset I) (A : Finset (Finset I))
    (nonempty : A.Nonempty)
    (edges : ∀ j∈D, ∃ x∈A, j∉x ∧ insert j x∈A) : D.card+1≤A.card := by
  classical
  induction D using Finset.induction_on generalizing A with
  | empty => simpa using Finset.card_pos.mpr nonempty
  | @insert j D hj ih =>
    let erase := fun u : Finset I => u.erase j
    obtain ⟨w,hw,miss,hw'⟩ := edges j (Finset.mem_insert_self ..)
    have collide : erase w=erase (insert j w) := by simp [erase,miss]
    have smaller : (A.image erase).card < A.card := by
      apply lt_of_le_of_ne Finset.card_image_le
      intro eq
      have k := (Finset.card_image_iff.mp eq) hw hw' collide
      exact miss (k.symm ▸ Finset.mem_insert_self ..)
    have bound := ih (A.image erase) (nonempty.image _) (by
      intro i hi
      have neq : i≠j := fun h => hj (h ▸ hi)
      obtain ⟨x,hx,absent,mem⟩ := edges i (Finset.mem_insert_of_mem hi)
      refine ⟨erase x,Finset.mem_image_of_mem _ hx,by simp [erase,absent],?_⟩
      have eq : erase (insert i x)=insert i (erase x) := by ext z; simp [erase]; grind
      exact eq ▸ Finset.mem_image_of_mem _ mem)
    rw [Finset.card_insert_of_notMem hj]
    omega

noncomputable def block (color : Fin n → Fin c) (j : Fin c) : Word n :=
  Finset.univ.filter (fun i => color i=j)
def cover (color : Fin n → Fin c) (S : Word n) := ∀ j, ∃ i∈S, color i=j
def tested (A : Finset (Word n)) (color : Fin n → Fin c) :=
  ∀ j, ∃ x∈A, Disjoint x (block color j) ∧ x∪block color j∈A

def preserves (A : Finset (Word n)) (E : Finset (Edge n)) (color : Fin n → Fin c)
    (T : Finset (Test n)) :=
  ∀ S, fits A (bank E S).toList T ↔ cover color S

private theorem sampleIff (color : Fin n → Fin c) (onto : Function.Surjective color)
    (E : Finset (Edge n))
    (classes : ∀ V, closed E V ↔ ∀ i k, color i=color k → (i∈V ↔ k∈V))
    (T : Finset (Test n)) (required : ∀ i, inv i∈T) (A : Finset (Word n)) :
    preserves A E color T ↔ tested A color := by
  constructor
  · intro keeps j
    let B := block color j
    let S := Finset.univ\B
    have missed : ¬cover color S := by
      intro cov
      obtain ⟨i,hi,e⟩ := cov j
      simpa [S,B,block,e] using hi
    have fail := fun h => missed ((keeps S).mp ((fitIff A E S T required).mpr h))
    change ¬detects A E S at fail
    unfold detects at fail
    push_neg at fail
    obtain ⟨x,hx,y,hy,sub,cl,d,ne⟩ := fail
    obtain ⟨i,hi⟩ : (y\x).Nonempty := by
      by_contra! h
      exact ne (Finset.Subset.antisymm (fun k hk => by
        by_contra missing
        have m := Finset.mem_sdiff.mpr ⟨hk,missing⟩
        rw [h] at m
        exact Finset.notMem_empty _ m) sub)
    have inside (k) (hk : k∈y\x) : color k=j := by
      by_contra neq
      exact Finset.disjoint_left.mp d hk (by simp [S,B,block,neq])
    have diff : y\x=B := by
      ext k
      constructor
      · intro hk
        simpa [B,block] using inside k hk
      · intro hk
        have eq : color k=j := by simpa [B,block] using hk
        exact ((classes _).mp cl i k ((inside i hi).trans eq.symm)).mp hi
    refine ⟨x,hx,?_,?_⟩
    · change Disjoint x B
      rw [←diff]
      exact Finset.disjoint_sdiff
    · have together : x∪B=y := by rw [←diff]; ext k; simp; grind
      change x∪B∈A
      rwa [together]
  · intro supports S
    rw [fitIff A E S T required]
    constructor
    · intro det j
      by_contra! absent
      obtain ⟨x,hx,d,hi⟩ := supports j
      let B := block color j
      have diff : (x∪B)\x=B := by
        ext v
        have guard : v∈x → v∈B → False := fun h k => Finset.disjoint_left.mp d h k
        simp only [Finset.mem_sdiff,Finset.mem_union]
        change (v∈x ∨ v∈B) ∧ v∉x ↔ v∈B
        grind
      have cl : closed E B := (classes _).mpr (by intro i k eq; simp [B,block,eq])
      have miss : Disjoint B S := Finset.disjoint_left.mpr (by
        intro i he hs
        exact absent i hs (by simpa [B,block] using he))
      have eq := det x hx (x∪B) hi Finset.subset_union_left (by rwa [diff]) (by rwa [diff])
      obtain ⟨i,eqi⟩ := onto j
      have bi : i∈B := by simp [B,block,eqi]
      have inside : i∈x∪B := Finset.mem_union_right _ bi
      exact Finset.disjoint_left.mp d (eq ▸ inside) bi
    · intro hit x _ y _ sub cl dis
      apply Finset.Subset.antisymm _ sub
      intro i hi
      by_contra missing
      have mem : i∈y\x := Finset.mem_sdiff.mpr ⟨hi,missing⟩
      obtain ⟨k,hk,eq⟩ := hit (color i)
      exact Finset.disjoint_left.mp dis (((classes _).mp cl i k eq.symm).mp mem) hk

private theorem leastSample (color : Fin n → Fin c) (onto : Function.Surjective color)
    (A : Finset (Word n)) (full : tested A color) (pos : 0<c) : c+1≤A.card := by
  classical
  choose representative rep using onto
  let project := fun x : Word n => Finset.univ.filter (fun j : Fin c => representative j∈x)
  let P := A.image project
  obtain ⟨w,hw,_,_⟩ := full (⟨0,pos⟩ : Fin c)
  have bound := edgesBound (Finset.univ : Finset (Fin c)) P ⟨_,Finset.mem_image_of_mem _ hw⟩ (by
    intro j _
    obtain ⟨x,hx,d,both⟩ := full j
    have reprB : representative j∈block color j := by simp [block,rep]
    have out : representative j∉x := fun h => Finset.disjoint_left.mp d h reprB
    refine ⟨project x,Finset.mem_image_of_mem _ hx,by simp [project,out],?_⟩
    have eq : project (x∪block color j)=insert j (project x) := by
      ext k
      simp [project,block,rep,or_comm]
    exact eq ▸ Finset.mem_image_of_mem _ both)
  exact (by simpa using bound : c+1≤P.card).trans Finset.card_image_le

private theorem star (color : Fin n → Fin c) :
    ∃ A : Finset (Word n), A.card≤c+1 ∧ tested A color := by
  classical
  let A := insert ∅ (Finset.univ.image (block color))
  refine ⟨A,?_,?_⟩
  · have h := Finset.card_insert_le (∅ : Word n) (Finset.univ.image (block color))
    have b : (Finset.univ.image (block color)).card≤c := Finset.card_image_le.trans (by simp)
    exact h.trans (by omega)
  · intro j
    exact ⟨∅,by simp [A],by simp,by simp [A]⟩

theorem criterion :
∀ (n c : Nat) (E : Finset (Fin n × Fin n)) (color : Fin n → Fin c),
  Function.Surjective color →
  (∀ V : Finset (Fin n), (∀ e∈E, e.1∈V ↔ e.2∈V) ↔
    ∀ i j, color i=color j → (i∈V ↔ j∈V)) →
  let W := Finset (Fin n)
  let bit := fun (i : Fin n) (x : W) => decide (i∈x)
  let inv := fun (i : Fin n) (x : W) => decide (i∉x)
  let same := fun (e : Fin n × Fin n) (x : W) => decide (e.1∈x ↔ e.2∈x)
  let bank := fun S : W => (({fun _ : W => false,fun _ : W => true} : Finset (W → Bool)) ∪
    Finset.univ.image bit ∪ E.image same ∪ E.image (fun e x => !(same e x)) ∪ S.image inv).toList
  let B := fun j : Fin c => Finset.univ.filter (fun i => color i=j)
  ∀ T : Finset (W → Bool), (∀ i, inv i∈T) →
    let keeps := fun A : Finset W => ∀ S : W,
      (∃ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (bank S).length D ∧
        D.output < (bank S).length+D.size ∧ ∀ f∈T, ∃ j<(bank S).length+D.size,
          ∀ x∈A, (D.wires ((bank S).map (fun g => g x))).getD j false=f x) ↔
      ∀ j, ∃ i∈S, color i=j
    (∀ A, keeps A ↔ ∀ j, ∃ x∈A, Disjoint x (B j) ∧ x∪B j∈A) ∧
    (∃ A, keeps A ∧ A.card=(if c=0 then 0 else c+1) ∧ ∀ A', keeps A' → A.card≤A'.card)
:= by
  classical
  intro n c E color onto classes
  dsimp only
  intro T req
  change (∀ A, preserves A E color T ↔ tested A color) ∧
    ∃ A, preserves A E color T ∧ A.card=(if c=0 then 0 else c+1) ∧
      ∀ A', preserves A' E color T → A.card≤A'.card
  have iff := sampleIff color onto E classes T req
  refine ⟨iff,?_⟩
  by_cases h : c=0
  · subst c
    exact ⟨∅,(iff _).mpr (fun j => Fin.elim0 j),by simp,by simp⟩
  · have pos : 0<c := Nat.pos_of_ne_zero h
    obtain ⟨A,sz,ok⟩ := star color
    have lo := leastSample color onto A ok pos
    exact ⟨A,(iff _).mpr ok,by simp [h]; omega,
      fun A' hA => sz.trans (leastSample color onto _ ((iff _).mp hA) pos)⟩

end PEqualNP.GraphSeedSamples

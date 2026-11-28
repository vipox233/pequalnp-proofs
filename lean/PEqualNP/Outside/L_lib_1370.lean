import Mathlib.Tactic
import PEqualNP.Defs

-- The circuit realization part (namespace P1297 below) is copied from L_lib_1297.lean
-- by Zamua Nasrawt (merged, Apache-2.0), renamed into this file's helper namespace.

namespace PEqualNP.Outside.L_lib_1370_aux.P1297
section WireFacts
open scoped Classical
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
variable {n m : ℕ}
abbrev Col (m : ℕ) := Fin m → Bool
noncomputable def raw (x : Fin m → Finset (Fin n)) (i : Fin m) :=
  List.ofFn (fun a : Fin n => decide (a ∈ x i)) ++ [false,true]
noncomputable def val (x : Fin m → Finset (Fin n)) (gs : List Gate) (p : ℕ) : Col m :=
  fun i => ((Circuit.mk gs 0).wires (raw x i)).getD p false
noncomputable def ix (gs : List Gate) := (List.range gs.length).filter fun j =>
  decide ((gs.getD j ⟨.or,[]⟩).op = GateOp.not)
noncomputable def trace (x : Fin m → Finset (Fin n)) (gs : List Gate) :=
  (ix gs).map fun j => val x gs (n+2+j)
noncomputable def sing (x : Fin m → Finset (Fin n)) (a : Fin n) : Col m := fun i => decide (a∈x i)
noncomputable def base (x : Fin m → Finset (Fin n)) : Set (Col m) :=
  {f | f=(fun _ => false) ∨ f=(fun _ => true) ∨ ∃ a, f=sing x a}
noncomputable def inv (f : Col m) : Col m := fun i => !(f i)
noncomputable def conj (f g : Col m) : Col m := fun i => f i && g i
noncomputable def disj (f g : Col m) : Col m := fun i => f i || g i

theorem wirelen (gs : List Gate) (u : List Bool) : ((Circuit.mk gs 0).wires u).length=u.length+gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton gs g ih => simpa [Circuit.wires,List.foldl_append,Nat.add_assoc] using congrArg Nat.succ ih

theorem old (x : Fin m → Finset (Fin n)) (gs : List Gate) (g : Gate) {p} (hp : p<n+2+gs.length) :
    val x (gs++[g]) p=val x gs p := by
  funext i
  have len := wirelen gs (raw x i)
  rw [show (raw x i).length=n+2 by simp [raw]] at len
  simp only [val,Circuit.wires,List.foldl_append,List.foldl_cons,List.foldl_nil]
  change (((Circuit.mk gs 0).wires (raw x i)) ++ [_]).getD p false = _
  exact List.getD_append _ _ _ _ (by omega)

theorem fresh (x : Fin m → Finset (Fin n)) (gs : List Gate) (g : Gate) (i : Fin m) :
    val x (gs++[g]) (n+2+gs.length) i=g.op.eval (g.inputs.map fun p => val x gs p i) := by
  have len := wirelen gs (raw x i)
  rw [show (raw x i).length=n+2 by simp [raw]] at len
  simp only [val,Circuit.wires,List.foldl_append,List.foldl_cons,List.foldl_nil]
  change ( ((Circuit.mk gs 0).wires (raw x i)) ++ [_]).getD _ false = _
  rw [←len,List.getD_append_right _ _ _ _ (by omega)]
  simp

theorem ixAdd (gs : List Gate) (g : Gate) :
    ix (gs++[g])=ix gs ++ (if g.op=.not then [gs.length] else []) := by
  unfold ix
  simp only [List.length_append,List.length_singleton,List.range_succ,List.filter_append]
  congr 1
  · apply List.filter_congr
    intro i hi
    rw [List.getD_append _ _ _ _ (List.mem_range.mp hi)]
  · by_cases h : g.op=.not <;> simp [h]

theorem ixRange {gs : List Gate} {j} (h : j∈ix gs) : j<gs.length :=
  List.mem_range.mp (List.mem_filter.mp h).1

theorem traceAdd (x : Fin m → Finset (Fin n)) (gs : List Gate) (g : Gate) :
    trace x (gs++[g])=trace x gs ++ (if g.op=.not then [val x (gs++[g]) (n+2+gs.length)] else []) := by
  unfold trace
  rw [ixAdd,List.map_append]
  congr 1
  · apply List.map_congr_left
    intro j hj
    exact old _ _ _ (by have := ixRange hj; omega)
  · split <;> rfl

theorem countIx (gs : List Gate) : PEqualNP.NotBracket.notCount ⟨gs,0⟩=(ix gs).length := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    rw [ixAdd]
    unfold PEqualNP.NotBracket.notCount at *
    by_cases h : g.op=.not <;> simp [List.filter_append,h,ih]

theorem extendBack (gs : List Gate) (g : Gate) (h : ReadsBack (n+2) ⟨gs,0⟩)
    (ok : ∀ p∈g.inputs,p<n+2+gs.length) : ReadsBack (n+2) ⟨gs++[g],0⟩ := by
  intro j hj p hp
  simp only [List.length_append,List.length_singleton] at hj
  by_cases hj' : j<gs.length
  · apply h j hj' p
    simpa only [gateAt,List.getD_append _ _ _ _ hj'] using hp
  · obtain rfl : j=gs.length := by omega
    apply ok
    simpa [gateAt,List.getD_append_right _ _ _ _ (le_refl _)] using hp

-- A column gives one wire value per sample. Only a physical NOT extends the trace.
noncomputable def Built (x : Fin m → Finset (Fin n)) (tr : List (Col m)) (k : ℕ) (S : Set (Col m)) :=
  ∃ gs : List Gate, FanInTwo ⟨gs,0⟩ ∧ ReadsBack (n+2) ⟨gs,0⟩ ∧ gs.length≤k ∧ trace x gs=tr ∧
    ∀ f∈S, ∃ p<n+2+gs.length, val x gs p=f
end WireFacts

section Compiler
open scoped Classical
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
variable {n m : ℕ} {x : Fin m → Finset (Fin n)} {tr : List (Col m)} {k : ℕ} {S : Set (Col m)}

theorem Built.start : Built x [] 0 (base x) := by
  refine ⟨[],by simp [FanInTwo],by simp [ReadsBack],by simp,rfl,?_⟩
  intro f hf
  rcases hf with rfl|rfl|⟨a,rfl⟩
  · refine ⟨n,by simp,?_⟩
    funext i
    simp [val,Circuit.wires,raw]
  · refine ⟨n+1,by simp,?_⟩
    funext i
    simp [val,Circuit.wires,raw]
  · refine ⟨a.val,by have := a.isLt; simp; omega,?_⟩
    funext i
    change ((List.ofFn fun u : Fin n => decide (u∈x i)) ++ _).getD a.val false=_
    rw [List.getD_append _ _ _ _ (by simp)]
    simp [sing]

theorem Built.relax {K : ℕ} {T : Set (Col m)} (ih : Built x tr k S) (sz : k≤K) (sub : T⊆S) : Built x tr K T := by
  obtain ⟨gs,fan,back,le,trace,signal⟩ := ih
  exact ⟨gs,fan,back,le.trans sz,trace,fun f hf => signal f (sub hf)⟩

theorem Built.andGate {f z : Col m} (ih : Built x tr k S) (hf : f∈S) (hg : z∈S) : Built x tr (k+1) (insert (conj f z) S) := by
  obtain ⟨gs,fan,back,sz,ht,sig⟩ := ih
  obtain ⟨a,ha,ea⟩ := sig _ hf
  obtain ⟨b,hb,eb⟩ := sig _ hg
  let g : Gate := ⟨.and,[a,b]⟩
  refine ⟨gs++[g],?_,?_,by simpa using sz,?_,?_⟩
  · intro j hj
    rcases List.mem_append.mp hj with oj|nj
    · exact fan j oj
    · obtain rfl : j=g := List.mem_singleton.mp nj
      simp [g]
  · apply extendBack _ _ back
    simp_all [g]
  · rw [traceAdd]; simpa [g] using ht
  · intro f mem
    rcases mem with rfl|mem
    · refine ⟨n+2+gs.length,by simp,?_⟩
      funext i; rw [fresh]; simp [g,GateOp.eval,ea,eb,conj]
    · obtain ⟨p,hp,eq⟩ := sig _ mem
      exact ⟨p,by simp; omega,(old _ _ _ hp).trans eq⟩

theorem Built.orGate {f z : Col m} (ih : Built x tr k S) (hf : f∈S) (hg : z∈S) : Built x tr (k+1) (insert (disj f z) S) := by
  obtain ⟨gs,fan,back,sz,ht,sig⟩ := ih
  obtain ⟨a,ha,ea⟩ := sig _ hf
  obtain ⟨b,hb,eb⟩ := sig _ hg
  let g : Gate := ⟨.or,[a,b]⟩
  refine ⟨gs++[g],?_,?_,by simpa using sz,?_,?_⟩
  · intro j hj
    rcases List.mem_append.mp hj with oj|nj
    · exact fan j oj
    · obtain rfl : j=g := List.mem_singleton.mp nj
      simp [g]
  · apply extendBack _ _ back
    simp_all [g]
  · rw [traceAdd]; simpa [g] using ht
  · intro f mem
    rcases mem with rfl|mem
    · refine ⟨n+2+gs.length,by simp,?_⟩
      funext i; rw [fresh]; simp [g,GateOp.eval,ea,eb,disj]
    · obtain ⟨p,hp,eq⟩ := sig _ mem
      exact ⟨p,by simp; omega,(old _ _ _ hp).trans eq⟩

theorem Built.notGate {f : Col m} (ih : Built x tr k S) (hf : f∈S) : Built x (tr++[inv f]) (k+1) (insert (inv f) S) := by
  obtain ⟨gs,fan,back,sz,ht,sig⟩ := ih
  obtain ⟨a,ha,ea⟩ := sig _ hf
  let g : Gate := ⟨.not,[a]⟩
  have ev : val x (gs++[g]) (n+2+gs.length)=inv f := by
    funext i; rw [fresh]; simp [g,GateOp.eval,ea,inv]
  refine ⟨gs++[g],?_,?_,by simpa using sz,by simp [traceAdd,g,ht,ev],?_⟩
  · intro j hj
    rcases List.mem_append.mp hj with old|new
    · exact fan j old
    · obtain rfl : j=g := List.mem_singleton.mp new
      simp [g]
  · apply extendBack _ _ back; simpa [g] using ha
  · intro f mem
    rcases mem with rfl|mem
    · exact ⟨_,by simp,ev⟩
    · obtain ⟨p,hp,eq⟩ := sig _ mem
      exact ⟨p,by simp; omega,(old _ _ _ hp).trans eq⟩

end Compiler

section Construction
open scoped Classical
variable {n m : ℕ} {x : Fin m → Finset (Fin n)} {tr : List (Col m)} {k : ℕ} {S : Set (Col m)}

noncomputable def Grow (x : Fin m → Finset (Fin n)) (tr : List (Col m)) (k : ℕ) (S : Set (Col m))
    (b : ℕ) (f : Col m) := ∃ T, Built x tr (k+b) T ∧ S⊆T ∧ f∈T

theorem batch {ι : Type} (s : Finset ι) (F : ι → Col m) (b : ℕ) (H : Built x tr k S)
    (make : ∀ {K T}, Built x tr K T → S⊆T → ∀ a∈s, Grow x tr K T b (F a)) :
    ∃ T, Built x tr (k+s.card*b) T ∧ S⊆T ∧ ∀ a∈s, F a∈T := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨S,by simpa using H,Set.Subset.rfl,by simp⟩
  | @insert a s fresh ih =>
    obtain ⟨U,hU,sub,allU⟩ := ih (fun h st i hi => make h st i (Finset.mem_insert_of_mem hi))
    obtain ⟨T,hT,ut,hit⟩ := make hU sub a (Finset.mem_insert_self _ _)
    refine ⟨T,by simpa [Finset.card_insert_of_notMem fresh,Nat.add_mul,Nat.add_assoc] using hT,sub.trans ut,?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl|hh
    · exact hit
    · exact ut (allU _ hh)

theorem allFold {ι : Type} (s : Finset ι) (F : ι → Col m) (H : Built x tr k S)
    (unit : (fun _ => true)∈S) (get : ∀ a∈s, F a∈S) :
    Grow x tr k S s.card (fun j => decide (∀ a∈s, F a j=true)) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨S,by simpa using H,Set.Subset.rfl,by simpa using unit⟩
  | @insert a s fr ih =>
    obtain ⟨T,h,st,ft⟩ := ih (fun a ha => get a (Finset.mem_insert_of_mem ha))
    have g := Built.andGate h (st (get a (Finset.mem_insert_self _ _))) ft
    refine ⟨_,by simpa [Finset.card_insert_of_notMem fr,Nat.add_assoc] using g,st.trans (Set.subset_insert _ _),?_⟩
    apply Set.mem_insert_iff.mpr; left
    funext j
    simp [conj, Bool.decide_and]

theorem anyFold {ι : Type} (s : Finset ι) (F : ι → Col m) (H : Built x tr k S)
    (unit : (fun _ => false)∈S) (get : ∀ a∈s, F a∈S) :
    Grow x tr k S s.card (fun j => decide (∃ a∈s, F a j=true)) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨S,by simpa using H,Set.Subset.rfl,by simpa using unit⟩
  | @insert a s fr ih =>
    obtain ⟨T,h,st,ft⟩ := ih (fun a ha => get a (Finset.mem_insert_of_mem ha))
    have g := Built.orGate h (st (get a (Finset.mem_insert_self _ _))) ft
    refine ⟨_,by simpa [Finset.card_insert_of_notMem fr,Nat.add_assoc] using g,st.trans (Set.subset_insert _ _),?_⟩
    apply Set.mem_insert_iff.mpr; left
    funext j
    simp [disj, Bool.decide_or]

-- A surviving sample must be contained in the current mask and agree on the processed bits.
noncomputable def indicator (x : Fin m → Finset (Fin n)) (v : Fin m → ℕ) (i : Fin m) : Col m :=
  fun j => decide (x i⊆x j ∧ v i=v j)
noncomputable def hist (r : ℕ) (v : Fin m → ℕ) : List (Col m) :=
  List.ofFn fun b : Fin r => fun i => !(v i).testBit (r-1-b.val)

theorem hist_succ (r : ℕ) (v : Fin m → ℕ) :
    hist (r+1) v=hist r (fun i => v i/2) ++ [fun i => !(v i).testBit 0] := by
  rw [hist,List.ofFn_succ',List.concat_eq_append]
  congr 1
  · unfold hist
    congr 1
    funext b i
    simp [Nat.testBit_div_two,show r-1-(b:ℕ)+1 = r+1-1-b by have := b.isLt; omega]
  · simp

theorem stages (x : Fin m → Finset (Fin n)) (r : ℕ) (v : Fin m → ℕ)
    (cap : ∀ i, v i<2^r) (mono : ∀ i j, x i⊆x j → v i≤v j) :
    ∃ S, Built x (hist r v) (m*(n+2*r)+r) S ∧ base x ⊆ S ∧ ∀ i, indicator x v i∈S := by
  induction r generalizing v with
  | zero =>
    have z : ∀ i,v i=0 := fun i => by have := cap i; simp at this; omega
    obtain ⟨T,bt,st,allT⟩ := batch (Finset.univ : Finset (Fin m)) (indicator x v) n (Built.start (x:=x)) (by
      intro K U h bu i _
      obtain ⟨V,hh,sub,fi⟩ := allFold (x i) (sing x) h (bu (Or.inr (Or.inl rfl)))
        (fun a _ => bu (Or.inr (Or.inr ⟨a,rfl⟩)))
      have lim := Finset.card_le_univ (x i)
      refine ⟨V,hh.relax (by simpa using Nat.add_le_add_left lim K) Set.Subset.rfl,sub,?_⟩
      have eq : indicator x v i = (fun j => decide (∀ a ∈ x i,sing x a j=true)) := by
        funext j; simp [indicator,sing,z,Finset.subset_iff]
      rw [eq]; convert fi using 1; funext j; apply Bool.eq_iff_iff.mpr; simp)
    exact ⟨T,by simpa [hist] using bt,st,fun i => allT i (Finset.mem_univ _)⟩
  | succ r ih =>
    let u := fun i => v i/2
    have ucap : ∀ i,u i<2^r := fun i => by have := cap i; simp [pow_succ] at this; dsimp [u]; omega
    obtain ⟨S,h,bs,hInd⟩ := ih u ucap (fun i j h => Nat.div_le_div_right (mono i j h))
    let bit : Col m := fun i => (v i).testBit 0
    let sel := Finset.univ.filter fun i => bit i=true
    obtain ⟨T,hT,st,hit⟩ := anyFold sel (indicator x u) h (bs (Or.inl rfl)) (fun i _ => hInd i)
    have eqn : (fun j => decide (∃ a∈sel, indicator x u a j=true))=bit := by
      funext j
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq,indicator,sel,Finset.mem_filter,Finset.mem_univ,true_and]
      constructor
      · rintro ⟨a,ba,sub,eq⟩
        have ord := mono a j sub
        simp [u] at eq
        simp [bit] at ba ⊢
        omega
      · intro b; exact ⟨j,b,Finset.Subset.rfl,rfl⟩
    have hit2 : bit ∈ T := by
      rw [←eqn]; convert hit using 1; funext j; apply Bool.eq_iff_iff.mpr; simp
    have hn := Built.notGate hT hit2
    let U := insert (inv bit) T
    have su : S⊆U := st.trans (Set.subset_insert _ _)
    obtain ⟨V,hV,uv,allV⟩ := batch (Finset.univ : Finset (Fin m)) (indicator x v) 1 hn (by
      intro K W hw uw i _
      have iw := uw (su (hInd i))
      by_cases bi : bit i=true
      · have same : indicator x v i=indicator x u i := by
          funext j; simp only [indicator,decide_eq_decide]
          constructor
          · rintro ⟨a,b⟩; exact ⟨a,congrArg (·/2) b⟩
          · rintro ⟨a,b⟩; have ord := mono i j a
            simp [bit] at bi; dsimp [u] at b; exact ⟨a,by omega⟩
        exact ⟨W,hw.relax (by omega) Set.Subset.rfl,Set.Subset.rfl,same ▸ iw⟩
      · have bw : inv bit ∈ W := uw (Set.mem_insert _ _)
        have made := Built.andGate hw iw bw
        refine ⟨_,made,Set.subset_insert _ _,Set.mem_insert_iff.mpr (Or.inl ?_)⟩
        funext j
        apply Bool.eq_iff_iff.mpr
        simp only [indicator,conj,inv,decide_eq_true_eq,Bool.and_eq_true,Bool.not_eq_true']
        simp [bit] at bi
        simp [bit,u]
        grind)
    have lim : sel.card≤m := by simpa using Finset.card_le_univ sel
    rw [hist_succ]
    refine ⟨V,hV.relax ?_ Set.Subset.rfl,(bs.trans su).trans uv,fun i => allV i (Finset.mem_univ _)⟩
    simp only [Finset.card_univ,Fintype.card_fin,mul_one]
    simp only [Nat.mul_add,Nat.mul_succ] at *
    omega
end Construction

section TraceOrder
open scoped Classical
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
variable {n m : ℕ} {x : Fin m → Finset (Fin n)}
noncomputable def decode (i : Fin m) : List (Col m) → ℕ
  | [] => 0
  | a::as => 2*decode i as + if a i then 0 else 1
noncomputable def score (i : Fin m) (word : List (Col m)) := decode i word.reverse
theorem snocScore (i : Fin m) (l : List (Col m)) (f : Col m) :
    score i (l++[f])=2*score i l + if f i then 0 else 1 := by simp [score,decode]

theorem other (x : Fin m → Finset (Fin n)) (gs : List Gate) (g : Gate) {p}
    (hp : p≠n+2+gs.length) : val x (gs++[g]) p=val x gs p := by
  by_cases low : p<n+2+gs.length
  · exact old x gs g low
  funext i
  have oz := wirelen gs (raw x i)
  have nz := wirelen (gs++[g]) (raw x i)
  rw [show (raw x i).length=n+2 by simp [raw]] at oz nz
  simp only [List.length_append,List.length_singleton] at nz
  unfold val
  rw [List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by omega)]

theorem rawMono {i j : Fin m} (sub : x i ⊆ x j) (p : ℕ) :
    val x [] p i=true → val x [] p j=true := by
  by_cases hp : p<n
  · simp only [val,Circuit.wires,List.foldl_nil,raw]
    rw [List.getD_append _ _ _ _ (by simpa using hp),List.getD_append _ _ _ _ (by simpa using hp)]
    simpa [List.getD_eq_getElem?_getD,hp] using @sub ⟨p,hp⟩
  · simp only [val,Circuit.wires,List.foldl_nil,raw]
    rw [List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt hp),
      List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt hp)]
    simp

theorem ordinary {i j : Fin m} {gs : List Gate} (prior : ∀ p,val x gs p i=true → val x gs p j=true)
    (g : Gate) (op : g.op=.and ∨ g.op=.or) :
    val x (gs++[g]) (n+2+gs.length) i=true → val x (gs++[g]) (n+2+gs.length) j=true := by
  rw [fresh,fresh]
  rcases op with op|op
  · simp only [op,GateOp.eval,List.all_map,List.all_eq_true,Function.comp_apply,id_eq]
    exact fun h p hp => prior _ (h p hp)
  · simp only [op,GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
    rintro ⟨p,hp,v⟩; exact ⟨p,hp,prior _ v⟩

theorem inverseGate {i j : Fin m} {gs : List Gate} (prior : ∀ p,val x gs p i=true → val x gs p j=true)
    (g : Gate) (op : g.op=.not) :
    val x (gs++[g]) (n+2+gs.length) j=true → val x (gs++[g]) (n+2+gs.length) i=true := by
  rw [fresh,fresh]
  cases args : g.inputs with
  | nil => simp [op,GateOp.eval]
  | cons a l =>
    have h := prior a
    simp [op,GateOp.eval]
    cases e : val x gs a i <;> cases d : val x gs a j <;> simp_all

theorem stepOrder (x : Fin m → Finset (Fin n)) (gs : List Gate) (fan : FanInTwo ⟨gs,0⟩)
    (i j : Fin m) (sub : x i⊆x j) :
    score i (trace x gs) ≤ score j (trace x gs) ∧
    (score i (trace x gs)=score j (trace x gs) → ∀ p,val x gs p i=true → val x gs p j=true) := by
  induction gs using List.reverseRecOn with
  | nil => exact ⟨le_refl _,fun _ => rawMono sub⟩
  | append_singleton gs g ih =>
    obtain ⟨le,transfer⟩ := ih (fun u hu => fan u (List.mem_append_left _ hu))
    have ops := (fan g (List.mem_append_right _ (List.mem_singleton_self _))).1
    change g.op=.and ∨ g.op=.or ∨ g.op=.not at ops
    by_cases nt : g.op=.not
    · simp only [traceAdd,ite_eq_left nt,snocScore]
      let p := n+2+gs.length
      by_cases eq : score i (trace x gs)=score j (trace x gs)
      · have ant := inverseGate (transfer eq) g nt
        constructor
        · rw [eq]
          change _ + (if val x (gs++[g]) p i then 0 else 1) ≤ _ + (if val x (gs++[g]) p j then 0 else 1)
          cases ai : val x (gs++[g]) p i <;> cases aj : val x (gs++[g]) p j <;> simp_all [p]
        · intro same a
          by_cases aeq : a=p
          · subst a
            dsimp [p] at *
            split at same <;> split at same <;> simp_all
          · rw [other x gs g aeq]; exact transfer eq _
      · have strict := lt_of_le_of_ne le eq
        split <;> split <;> constructor <;> omega
    · have ao : g.op=.and ∨ g.op=.or := ops.elim Or.inl (fun h => Or.inr (h.resolve_right nt))
      simp only [traceAdd,ite_eq_right nt,List.append_nil]
      refine ⟨le,fun eq a => ?_⟩
      by_cases he : a=n+2+gs.length
      · subst a; exact ordinary (transfer eq) g ao
      · rw [other x gs g he]; exact transfer eq _
end TraceOrder

section Characterization
open scoped Classical
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
variable {n m t r : ℕ} (x : Fin m → Finset (Fin n)) (v : Fin m → ℕ) (w : Fin m → Fin t → Bool)

noncomputable def OK := ∀ i j, x i ⊆ x j → v i ≤ v j ∧ (v i=v j → ∀ a,w i a=true → w j a=true)
noncomputable def Fits (r : ℕ) (C : Circuit) (tap : Fin t → ℕ) := FanInTwo C ∧ ReadsBack (n+2) C ∧
  C.output<n+2+C.size ∧ PEqualNP.NotBracket.notCount C=r ∧ (ix C.gates).length=r ∧
  (∀ a,tap a<n+2+C.size) ∧ (∀ i a,val x C.gates (tap a) i=w i a) ∧
  ∀ i (b : Fin r),val x C.gates (n+2+(ix C.gates).getD b.val C.size) i= !(v i).testBit (r-1-b.val)

theorem decodeHist (i : Fin m) (r : ℕ) (v : Fin m → ℕ) (cap : ∀ i,v i<2^r) :
    score i (hist r v)=v i := by
  induction r generalizing v with
  | zero => have hi := cap i; simpa [hist,score,decode] using (show 0=v i by simpa using (Nat.eq_zero_of_le_zero (by simpa using hi)).symm)
  | succ r ih =>
    rw [hist_succ,snocScore,ih _ (fun j => by have := cap j; rw [pow_succ] at this; omega)]
    simp [Nat.testBit_zero]
    split <;> omega

theorem traceEq {C : Circuit} {tap : Fin t → ℕ} (fit : Fits x v w r C tap) :
    trace x C.gates=hist r v := by
  obtain ⟨_,_,_,_,len,_,_,allBits⟩ := fit
  apply List.ext_getElem
  · simp [trace,hist,len]
  · intro j hj hj'
    have h : j<r := by simpa [hist] using hj'
    have ht : j<(ix C.gates).length := by omega
    simp only [trace,hist,List.getElem_map,List.getElem_ofFn]
    funext i
    have e := allBits i ⟨j,h⟩
    change val x C.gates (n+2+(ix C.gates).getD j C.size) i=_ at e
    rw [List.getD_eq_getElem _ _ ht] at e
    simpa only [trace,hist,List.getElem_map,List.getElem_ofFn] using e

theorem necessary (cap : ∀ i,v i<2^r) {C tap} (fit : Fits x v w r C tap) : OK x v w := by
  have e := traceEq x v w fit
  intro i j sub
  have h := stepOrder x C.gates fit.1 i j sub
  rw [e,decodeHist i r v cap,decodeHist j r v cap] at h
  refine ⟨h.1,?_⟩
  intro eq a ha
  have taps := fit.2.2.2.2.2.2.1
  rw [←taps i a] at ha
  rw [←taps j a]
  exact h.2 eq _ ha

theorem sufficient (cap : ∀ i,v i<2^r) (ok : OK x v w) :
    ∃ C tap,Fits x v w r C tap ∧ C.size≤m*(n+2*r+t)+r := by
  obtain ⟨S,b,baseSub,ind⟩ := stages x r v cap (fun i j h => (ok i j h).1)
  let f := fun a : Fin t => fun i => w i a
  obtain ⟨T,hT,_,haveTap⟩ := batch (Finset.univ : Finset (Fin t)) f m b (by
    intro K U hu su a _
    let sel := Finset.univ.filter fun i => w i a=true
    obtain ⟨V,hV,uv,got⟩ := anyFold sel (indicator x v) hu (su (baseSub (Or.inl rfl))) (fun i _ => su (ind i))
    have lim : sel.card≤m := by simpa using Finset.card_le_univ sel
    refine ⟨V,hV.relax (by omega) Set.Subset.rfl,uv,?_⟩
    convert got using 1
    funext j
    apply Bool.eq_iff_iff.mpr
    simp only [sel,Finset.mem_filter,Finset.mem_univ,true_and,indicator,decide_eq_true_eq,f]
    constructor
    · intro h; exact ⟨j,h,Finset.Subset.rfl,rfl⟩
    · rintro ⟨i,hit,sub,same⟩; exact (ok i j sub).2 same a hit)
  obtain ⟨gs,fan,back,sz,ht,wire⟩ := hT
  choose tap valid data using fun a => wire _ (haveTap a (Finset.mem_univ _))
  have len := congrArg List.length ht
  simp [trace,hist] at len
  refine ⟨⟨gs,0⟩,tap,⟨fan,back,by simp [Circuit.size],(countIx gs).trans len,len,valid,
    fun i a => congrFun (data a) i,?_⟩,?_⟩
  · intro i b
    have hb : b.val<(ix gs).length := by rw [len]; exact b.isLt
    have e := List.getElem_of_eq ht (i:=b.val) (by simpa [trace] using hb)
    change val x gs (n+2+(ix gs).getD b.val gs.length) i=_
    rw [List.getD_eq_getElem _ _ hb]
    simp only [trace,hist,List.getElem_map,List.getElem_ofFn] at e
    exact congrFun e i
  · change gs.length≤_
    simpa [Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,Nat.mul_comm] using sz
end Characterization


theorem t1297 : letI : ∀ P : Prop, Decidable P := Classical.propDecidable
∀ (n m t r : Nat) (x : Fin m → Finset (Fin n)) (level : Fin m → Fin (2^r))
  (w : Fin m → Fin t → Bool),
  let orderOK := ∀ i j, x i ⊆ x j → (level i).val ≤ (level j).val ∧
    (level i = level j → ∀ a, w i a = true → w j a = true)
  let fit := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin t → Nat) =>
    let ns := (List.range C.size).filter (fun g =>
      decide ((C.gates.getD g ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).op =
        PEqualNP.CircuitLowerBounds.GateOp.not))
    let atWire := fun (i : Fin m) (p : Nat) =>
      (C.wires (List.ofFn (fun a : Fin n => decide (a ∈ x i)) ++ [false,true])).getD p false
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
    C.output < n+2+C.size ∧ PEqualNP.NotBracket.notCount C = r ∧ ns.length = r ∧
    (∀ a, tap a < n+2+C.size) ∧ (∀ i a, atWire i (tap a) = w i a) ∧
    ∀ i (b : Fin r), atWire i (n+2+ns.getD b.val C.size) =
      !((level i).val.testBit (r-1-b.val))
  ((∃ C tap, fit C tap) ↔ orderOK) ∧
    (orderOK → ∃ C tap, fit C tap ∧ C.size ≤ m*(n+2*r+t)+r) := by
  classical
  intro n m t r x level w
  let v := fun i => (level i).val
  have cap : ∀ i,v i<2^r := fun i => (level i).isLt
  dsimp only
  have compat : (∀ i j, x i⊆x j → v i≤v j ∧ (level i=level j → ∀ a,w i a=true → w j a=true)) ↔ OK x v w := by
    simp only [OK,v,Fin.ext_iff]
  have maskEq (i : Fin m) : (List.ofFn (fun a : Fin n => @decide (a∈x i) (Classical.propDecidable _)) ++ [false,true]) = raw x i := by
    unfold raw
    congr 1
    congr 1
    funext a
    apply Bool.eq_iff_iff.mpr; simp
  simp_rw [maskEq]
  let fitting := Fits x v w r
  change ((∃ C tap, fitting C tap) ↔ _) ∧ (_ → ∃ C tap, fitting C tap ∧ _)
  rw [compat]
  refine ⟨⟨?_,?_⟩,sufficient x v w cap⟩
  · rintro ⟨C,tap,fit⟩; exact necessary x v w cap fit
  · intro ok
    obtain ⟨C,tap,fit,_⟩ := sufficient x v w cap ok
    exact ⟨C,tap,fit⟩

end PEqualNP.Outside.L_lib_1370_aux.P1297

namespace PEqualNP.Outside.L_lib_1370_aux
open scoped Classical

section Sorting
variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def lvl (n : α → ℕ) (j : ℕ) : Finset α := Finset.univ.filter (fun p => j < n p)
noncomputable def car (n : α → ℕ) (x : Finset α) (j : ℕ) : Finset α := x.filter (fun p => j ≤ n p)
noncomputable def ind (x : Finset α) (p : α) : ℕ := if p ∈ x then 1 else 0
noncomputable def cnt {D : ℕ} (S : Fin D → Finset α) (p : α) : ℕ :=
  (Finset.univ.filter (fun j => p ∈ S j)).card

theorem car_zero (n : α → ℕ) (x : Finset α) : car n x 0 = x := by
  ext p; simp [car]

theorem car_succ (n : α → ℕ) (x : Finset α) (j : ℕ) : car n x (j+1) = lvl n j ∩ car n x j := by
  ext p; simp only [car, lvl, Finset.mem_filter, Finset.mem_inter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h1, by omega⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h2, by omega⟩

theorem lvl_add (n : α → ℕ) (x : Finset α) (j : ℕ) :
    lvl (fun p => n p + ind x p) j = lvl n j ∪ car n x j := by
  ext p; simp only [car, lvl, Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]
  unfold ind
  by_cases hp : p ∈ x
  · rw [if_pos hp]; simp only [hp, true_and]; omega
  · rw [if_neg hp]; simp only [hp, false_and, or_false]; omega

theorem ins (L : Finset α → Prop) (hI : ∀ A B, L A → L B → L (A ∩ B))
    (c : Finset α → ℕ) (hc : ∀ A B, L A → L B → c (A ∩ B) + c (A ∪ B) ≤ c A + c B)
    (n : α → ℕ) (hL : ∀ j, L (lvl n j)) (x : Finset α) (hx : L x) :
    ∀ k, L (car n x k) ∧ (∑ j ∈ Finset.range k, c (lvl (fun p => n p + ind x p) j)) + c (car n x k)
      ≤ (∑ j ∈ Finset.range k, c (lvl n j)) + c x := by
  intro k
  induction k with
  | zero => simp [car_zero, hx]
  | succ k ih =>
    obtain ⟨hk, ih⟩ := ih
    have h1 := hc (lvl n k) (car n x k) (hL k) hk
    rw [← car_succ, ← lvl_add] at h1
    refine ⟨?_, ?_⟩
    · rw [car_succ]; exact hI _ _ (hL k) hk
    · rw [Finset.sum_range_succ, Finset.sum_range_succ]; omega

theorem cnt_le {D : ℕ} (S : Fin D → Finset α) (p : α) : cnt S p ≤ D := by
  unfold cnt
  calc _ ≤ (Finset.univ : Finset (Fin D)).card := Finset.card_filter_le _ _
    _ = D := by simp

theorem cnt_succ {D : ℕ} (S : Fin (D+1) → Finset α) (p : α) :
    cnt S p = cnt (fun j : Fin D => S j.castSucc) p + ind (S (Fin.last D)) p := by
  simp only [cnt, ind, Finset.card_filter, Fin.sum_univ_castSucc]

theorem sort (L : Finset α → Prop) (hI : ∀ A B, L A → L B → L (A ∩ B))
    (hU : ∀ A B, L A → L B → L (A ∪ B)) (hE : L ∅)
    (c : Finset α → ℕ) (hc : ∀ A B, L A → L B → c (A ∩ B) + c (A ∪ B) ≤ c A + c B) :
    ∀ (D : ℕ) (S : Fin D → Finset α), (∀ j, L (S j)) →
      (∀ j, L (lvl (cnt S) j)) ∧ ∑ j ∈ Finset.range D, c (lvl (cnt S) j) ≤ ∑ j, c (S j) := by
  intro D
  induction D with
  | zero =>
    intro S _
    refine ⟨fun j => ?_, by simp⟩
    have : lvl (cnt S) j = ∅ := by
      ext p; simp [lvl, cnt]
    rw [this]; exact hE
  | succ D ih =>
    intro S hS
    obtain ⟨hL', hs'⟩ := ih (fun j => S j.castSucc) (fun j => hS _)
    have hx := hS (Fin.last D)
    have hcs : cnt S = fun p => cnt (fun j : Fin D => S j.castSucc) p + ind (S (Fin.last D)) p := by
      funext p; exact cnt_succ S p
    have hins := ins L hI c hc _ hL' (S (Fin.last D)) hx
    rw [hcs]
    refine ⟨fun j => ?_, ?_⟩
    · rw [lvl_add]; exact hU _ _ (hL' j) (hins j).1
    · have hD := (hins D).2
      have heq : lvl (fun p => cnt (fun j : Fin D => S j.castSucc) p + ind (S (Fin.last D)) p) D
          = car (cnt (fun j : Fin D => S j.castSucc)) (S (Fin.last D)) D := by
        rw [lvl_add]
        have : lvl (cnt (fun j : Fin D => S j.castSucc)) D = ∅ := by
          ext p
          have := cnt_le (fun j : Fin D => S j.castSucc) p
          simp only [lvl, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
            iff_false]
          omega
        rw [this, Finset.empty_union]
      rw [Finset.sum_range_succ, heq, Fin.sum_univ_castSucc]
      omega

end Sorting

section Flags

noncomputable def F {q a : ℕ} (r : Fin q) (w : Finset (Fin a)) : Finset (Fin q × Option (Fin a)) :=
  Finset.univ.filter (fun p => p.1.val < r.val ∨ (p.1 = r ∧ ∃ v, p.2 = some v ∧ v ∈ w))

def isF {q a : ℕ} (S : Finset (Fin q × Option (Fin a))) : Prop := ∃ r w, S = F r w

noncomputable def dec {q a : ℕ} (S : Finset (Fin q × Option (Fin a))) : Finset (Fin a) :=
  Finset.univ.filter (fun v => ∃ s : Fin q, (s, some v) ∈ S ∧ (s, none) ∉ S)

theorem mem_F {q a : ℕ} (r : Fin q) (w : Finset (Fin a)) (s : Fin q) (i : Option (Fin a)) :
    (s, i) ∈ F r w ↔ (s.val < r.val ∨ (s = r ∧ ∃ v, i = some v ∧ v ∈ w)) := by
  simp [F]

theorem dec_F {q a : ℕ} (r : Fin q) (w : Finset (Fin a)) : dec (F r w) = w := by
  ext v
  simp only [dec, Finset.mem_filter, Finset.mem_univ, true_and, mem_F]
  constructor
  · rintro ⟨s, h1, h2⟩
    rcases h1 with h1 | ⟨rfl, v', hv', hw⟩
    · exact absurd (Or.inl h1) h2
    · cases hv'; exact hw
  · intro hv
    refine ⟨r, Or.inr ⟨rfl, v, rfl, hv⟩, ?_⟩
    rintro (h | ⟨_, v', hv', _⟩)
    · exact lt_irrefl _ h
    · cases hv'

theorem F_sub {q a : ℕ} (r1 r2 : Fin q) (w1 w2 : Finset (Fin a)) (h : F r1 w1 ⊆ F r2 w2) :
    r1.val ≤ r2.val ∧ (r1 = r2 → w1 ⊆ w2) := by
  constructor
  · by_contra hlt
    push_neg at hlt
    have := h ((mem_F r1 w1 r2 none).2 (Or.inl hlt))
    rw [mem_F] at this
    rcases this with h1 | ⟨_, v, hv, _⟩
    · exact lt_irrefl _ h1
    · cases hv
  · rintro rfl v hv
    have := h ((mem_F r1 w1 r1 (some v)).2 (Or.inr ⟨rfl, v, rfl, hv⟩))
    rw [mem_F] at this
    rcases this with h1 | ⟨_, v', hv', hw⟩
    · exact absurd h1 (lt_irrefl _)
    · cases hv'; exact hw

theorem F_le {q a : ℕ} (r1 r2 : Fin q) (w1 w2 : Finset (Fin a)) (h : r1.val < r2.val) :
    F r1 w1 ⊆ F r2 w2 := by
  rintro ⟨s, i⟩ hp
  rw [mem_F] at hp ⊢
  rcases hp with h1 | ⟨rfl, _⟩
  · exact Or.inl (lt_trans h1 h)
  · exact Or.inl h

theorem F_inter {q a : ℕ} (r : Fin q) (w1 w2 : Finset (Fin a)) :
    F r w1 ∩ F r w2 = F r (w1 ∩ w2) := by
  ext ⟨s, i⟩
  rw [Finset.mem_inter, mem_F, mem_F, mem_F]
  rcases i with _ | v
  · simp
  · simp only [Option.some.injEq, exists_eq_left', Finset.mem_inter]
    tauto

theorem F_union {q a : ℕ} (r : Fin q) (w1 w2 : Finset (Fin a)) :
    F r w1 ∪ F r w2 = F r (w1 ∪ w2) := by
  ext ⟨s, i⟩
  rw [Finset.mem_union, mem_F, mem_F, mem_F]
  rcases i with _ | v
  · simp
  · simp only [Option.some.injEq, exists_eq_left', Finset.mem_union]
    tauto

theorem isF_inter {q a : ℕ} (A B : Finset (Fin q × Option (Fin a))) (hA : isF A) (hB : isF B) :
    isF (A ∩ B) := by
  obtain ⟨r1, w1, rfl⟩ := hA
  obtain ⟨r2, w2, rfl⟩ := hB
  rcases lt_trichotomy r1.val r2.val with h | h | h
  · rw [Finset.inter_eq_left.mpr (F_le r1 r2 w1 w2 h)]; exact ⟨r1, w1, rfl⟩
  · have : r1 = r2 := Fin.ext h
    subst this; rw [F_inter]; exact ⟨r1, _, rfl⟩
  · rw [Finset.inter_eq_right.mpr (F_le r2 r1 w2 w1 h)]; exact ⟨r2, w2, rfl⟩

theorem isF_union {q a : ℕ} (A B : Finset (Fin q × Option (Fin a))) (hA : isF A) (hB : isF B) :
    isF (A ∪ B) := by
  obtain ⟨r1, w1, rfl⟩ := hA
  obtain ⟨r2, w2, rfl⟩ := hB
  rcases lt_trichotomy r1.val r2.val with h | h | h
  · rw [Finset.union_eq_right.mpr (F_le r1 r2 w1 w2 h)]; exact ⟨r2, w2, rfl⟩
  · have : r1 = r2 := Fin.ext h
    subst this; rw [F_union]; exact ⟨r1, _, rfl⟩
  · rw [Finset.union_eq_left.mpr (F_le r2 r1 w2 w1 h)]; exact ⟨r1, w1, rfl⟩

theorem isF_empty {q a : ℕ} (hq : 0 < q) : isF (∅ : Finset (Fin q × Option (Fin a))) := by
  refine ⟨⟨0, hq⟩, ∅, ?_⟩
  ext ⟨s, i⟩
  rw [mem_F]
  simp only [Finset.notMem_empty, false_iff, not_or, not_and]
  refine ⟨Nat.not_lt_zero _, ?_⟩
  rintro _ ⟨v, _, hv⟩
  exact hv

theorem dec_sub {q a : ℕ} (cost : Finset (Fin a) → ℕ)
    (hsub : ∀ U V, cost (U ∩ V) + cost (U ∪ V) ≤ cost U + cost V)
    (A B : Finset (Fin q × Option (Fin a))) (hA : isF A) (hB : isF B) :
    cost (dec (A ∩ B)) + cost (dec (A ∪ B)) ≤ cost (dec A) + cost (dec B) := by
  obtain ⟨r1, w1, rfl⟩ := hA
  obtain ⟨r2, w2, rfl⟩ := hB
  rcases lt_trichotomy r1.val r2.val with h | h | h
  · rw [Finset.inter_eq_left.mpr (F_le r1 r2 w1 w2 h),
      Finset.union_eq_right.mpr (F_le r1 r2 w1 w2 h)]
  · have : r1 = r2 := Fin.ext h
    subst this; rw [F_inter, F_union, dec_F, dec_F, dec_F, dec_F]; exact hsub _ _
  · rw [Finset.inter_eq_right.mpr (F_le r2 r1 w2 w1 h),
      Finset.union_eq_left.mpr (F_le r2 r1 w2 w1 h)]; omega

end Flags

end PEqualNP.Outside.L_lib_1370_aux

open PEqualNP.Outside.L_lib_1370_aux

theorem PEqualNP.Outside.L_lib_1370 : letI : ∀ P : Prop, Decidable P := Classical.propDecidable
∀ (m a : Nat) (cost : Fin m → Finset (Fin a) → Nat),
  (∀ t U V, cost t (U ∩ V) + cost t (U ∪ V) ≤ cost t U + cost t V) ↔
  ∀ (n b D : Nat) (mask : Fin m → Finset (Fin n)),
  let q := 2^b
  let flag := fun (r : Fin q) (w : Finset (Fin a)) (s : Fin q) (i : Option (Fin a)) =>
    decide (s.val < r.val ∨ (s = r ∧ ∃ v, i = some v ∧ v ∈ w))
  ∀ (lev : Fin m → Fin D → Fin q) (word : Fin m → Fin D → Finset (Fin a)),
    let count := fun t s i => (Finset.univ.filter (fun j => flag (lev t j) (word t j) s i)).card
    (∀ t u, mask t ⊆ mask u → ∀ s i, count t s i ≤ count u s i) →
    ∃ (rank : Fin D → Fin m → Fin q) (out : Fin D → Fin m → Finset (Fin a)),
      (∀ j t s i, flag (rank j t) (out j t) s i = decide (j.val < count t s i)) ∧
      (∀ t, Finset.univ.sum (fun j => cost t (out j t)) ≤
        Finset.univ.sum (fun j => cost t (word t j))) ∧
      ∀ j, ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin a → Nat),
        let ns := (List.range C.size).filter (fun g =>
          decide ((C.gates.getD g ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).op =
            PEqualNP.CircuitLowerBounds.GateOp.not))
        let atWire := fun (t : Fin m) (w : Nat) =>
          (C.wires (List.ofFn (fun v : Fin n => decide (v ∈ mask t)) ++ [false,true])).getD w false
        PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
        C.output < n+2+C.size ∧ PEqualNP.NotBracket.notCount C = b ∧ ns.length = b ∧
        C.size ≤ m*(n+2*b+a)+b ∧ (∀ i, tap i < n+2+C.size) ∧
        (∀ t i, atWire t (tap i) = decide (i ∈ out j t)) ∧
        ∀ t (h : Fin b), atWire t (n+2+ns.getD h.val C.size) =
          !((rank j t).val.testBit (b-1-h.val)) := by
  intro m a cost
  constructor
  · intro hsub n b D mask q flag lev word count hmono
    have hq : 0 < q := by show 0 < 2^b; positivity
    let S : Fin m → Fin D → Finset (Fin q × Option (Fin a)) := fun t j => F (lev t j) (word t j)
    have hflag : ∀ r w s i, flag r w s i = decide ((s, i) ∈ F r w) := by
      intro r w s i
      exact decide_eq_decide.mpr (mem_F r w s i).symm
    have hcount : ∀ t s i, count t s i = cnt (S t) (s, i) := by
      intro t s i
      simp only [count, cnt, S]
      congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hflag, decide_eq_true_eq]
    have hsub' : ∀ t (U V : Finset (Fin a)), cost t (U ∩ V) + cost t (U ∪ V) ≤ cost t U + cost t V := by
      intro t U V; convert hsub t U V
    have hsort := fun t => sort (α := Fin q × Option (Fin a)) isF isF_inter isF_union (isF_empty hq)
      (fun A => cost t (dec A)) (fun A B hA hB => dec_sub (cost t) (hsub' t) A B hA hB) D (S t)
      (fun j => ⟨lev t j, word t j, rfl⟩)
    have hT : ∀ t (j : Fin D), ∃ r w, lvl (cnt (S t)) j.val = F r w := fun t j => (hsort t).1 j
    choose R W hRW using hT
    have hmemT : ∀ t (j : Fin D) s i, (s, i) ∈ F (R t j) (W t j) ↔ j.val < count t s i := by
      intro t j s i
      rw [← hRW, hcount]
      simp [lvl]
    refine ⟨fun j t => R t j, fun j t => W t j, ?_, ?_, ?_⟩
    · intro j t s i
      rw [hflag]
      exact decide_eq_decide.mpr (hmemT t j s i)
    · intro t
      have h2 := (hsort t).2
      calc (Finset.univ.sum fun j => cost t (W t j))
          = Finset.univ.sum (fun j : Fin D => cost t (dec (lvl (cnt (S t)) j.val))) := by
            refine Finset.sum_congr rfl (fun j _ => ?_)
            rw [hRW, dec_F]
        _ = ∑ j ∈ Finset.range D, cost t (dec (lvl (cnt (S t)) j)) :=
            Fin.sum_univ_eq_sum_range (fun j => cost t (dec (lvl (cnt (S t)) j))) D
        _ ≤ _ := h2
        _ = _ := by
            refine Finset.sum_congr rfl (fun j _ => ?_)
            simp only [S, dec_F]
    · intro j
      have hok : ∀ t u, mask t ⊆ mask u → (R t j).val ≤ (R u j).val ∧
          (R t j = R u j → ∀ i, decide (i ∈ W t j) = true → decide (i ∈ W u j) = true) := by
        intro t u htu
        have hsubF : F (R t j) (W t j) ⊆ F (R u j) (W u j) := by
          rintro ⟨s, i⟩ hp
          rw [hmemT] at hp ⊢
          exact lt_of_lt_of_le hp (hmono t u htu s i)
        obtain ⟨h1, h2⟩ := F_sub _ _ _ _ hsubF
        refine ⟨h1, fun he i hi => ?_⟩
        simp only [decide_eq_true_eq] at hi ⊢
        exact h2 he hi
      obtain ⟨C, tap, ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩, hsize⟩ :=
        (P1297.t1297 n m a b mask (fun t => R t j) (fun t i => decide (i ∈ W t j))).2 hok
      exact ⟨C, tap, f1, f2, f3, f4, f5, hsize, f6,
        fun t i => (f7 t i).trans (decide_eq_decide.mpr Iff.rfl), f8⟩
  · intro h t U V
    have h' := h 0 0 2 (fun _ => ∅) (fun _ _ => 0) (fun _ j => ![U, V] j) (fun _ _ _ _ _ => le_rfl)
    obtain ⟨rank, out, hfl, hcost, -⟩ := h'
    have hc := hcost t
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hc
    have key : ∀ (j : Fin 2) v, v ∈ out j t ↔
        j.val < (if v ∈ U then 1 else 0) + (if v ∈ V then 1 else 0) := by
      intro j v
      have := hfl j t ⟨0, by norm_num⟩ (some v)
      have hr : rank j t = ⟨0, by norm_num⟩ := Fin.ext (by have := (rank j t).isLt; simp only [Nat.pow_zero] at this; simp only; omega)
      rw [hr] at this
      simp only [Nat.pow_zero, lt_self_iff_false, true_and, Option.some.injEq,
        exists_eq_left', false_or, decide_eq_decide] at this
      rw [this, Finset.card_filter, Fin.sum_univ_two]
      simp
    have e0 : out 0 t = U ∪ V := by
      ext v; rw [key, Finset.mem_union]
      by_cases hu : v ∈ U <;> by_cases hv : v ∈ V <;> simp [hu, hv]
    have e1 : out 1 t = U ∩ V := by
      ext v; rw [key, Finset.mem_inter]
      by_cases hu : v ∈ U <;> by_cases hv : v ∈ V <;> simp [hu, hv]
    rw [e0, e1, Nat.add_comm] at hc
    convert hc

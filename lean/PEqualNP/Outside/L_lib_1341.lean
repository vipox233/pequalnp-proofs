import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1341_aux
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

noncomputable def Built (x : Fin m → Finset (Fin n)) (tr : List (Col m)) (k : ℕ) (S : Set (Col m)) :=
  ∃ gs : List Gate, FanInTwo ⟨gs,0⟩ ∧ ReadsBack (n+2) ⟨gs,0⟩ ∧ gs.length≤ k ∧ trace x gs=tr ∧
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

theorem Built.relax {K : ℕ} {T : Set (Col m)} (ih : Built x tr k S) (sz : k≤ K) (sub : T⊆S) : Built x tr K T := by
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
    (cap : ∀ i, v i<2^r) (mono : ∀ i j, x i⊆x j → v i≤ v j) :
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
    have lim : sel.card≤ m := by simpa using Finset.card_le_univ sel
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
    ∃ C tap,Fits x v w r C tap ∧ C.size≤ m*(n+2*r+t)+r := by
  obtain ⟨S,b,baseSub,ind⟩ := stages x r v cap (fun i j h => (ok i j h).1)
  let f := fun a : Fin t => fun i => w i a
  obtain ⟨T,hT,_,haveTap⟩ := batch (Finset.univ : Finset (Fin t)) f m b (by
    intro K U hu su a _
    let sel := Finset.univ.filter fun i => w i a=true
    obtain ⟨V,hV,uv,got⟩ := anyFold sel (indicator x v) hu (su (baseSub (Or.inl rfl))) (fun i _ => su (ind i))
    have lim : sel.card≤ m := by simpa using Finset.card_le_univ sel
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

section Bridge
open scoped Classical
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
variable {n m : ℕ}

theorem decode_lt (i : Fin m) : ∀ l : List (Col m), decode i l < 2 ^ l.length
  | [] => by simp [decode]
  | a :: as => by
    have := decode_lt i as
    simp only [decode, List.length_cons, pow_succ]
    split <;> omega

theorem score_lt (i : Fin m) (l : List (Col m)) : score i l < 2 ^ l.length := by
  have := decode_lt i l.reverse
  simpa [score] using this

theorem trace_length (x : Fin m → Finset (Fin n)) (gs : List Gate) :
    (trace x gs).length = PEqualNP.NotBracket.notCount ⟨gs, 0⟩ := by
  rw [countIx]; simp [trace]

theorem rawEq (x : Fin m → Finset (Fin n)) (i : Fin m) {d : ∀ a : Fin n, Decidable (a ∈ x i)} :
    (List.ofFn (fun a : Fin n => @decide (a ∈ x i) (d a)) ++ [false,true]) = raw x i := by
  unfold raw
  congr 1
  congr 1
  funext a
  apply Bool.eq_iff_iff.mpr; simp

end Bridge

section Enc
open scoped Classical
open PEqualNP.CircuitLowerBounds

def listLe (l l' : List Bool) : Prop := ∀ p, l.getD p false = true → l'.getD p false = true

theorem listLe_append {A B A' B' : List Bool} (h : A.length = A'.length) :
    listLe (A ++ B) (A' ++ B') ↔ listLe A A' ∧ listLe B B' := by
  constructor
  · intro H
    refine ⟨fun p hp => ?_, fun p hp => ?_⟩
    · have hpl : p < A.length := by
        by_contra hc
        rw [List.getD_eq_default _ _ (by omega)] at hp
        exact Bool.false_ne_true hp
      have h1 := H p (by rw [List.getD_append _ _ _ _ hpl]; exact hp)
      rwa [List.getD_append _ _ _ _ (by omega)] at h1
    · have h1 := H (A.length + p) (by rw [List.getD_append_right _ _ _ _ (by omega)]; simpa using hp)
      rw [List.getD_append_right _ _ _ _ (by omega)] at h1
      simpa [h] using h1
  · rintro ⟨H1, H2⟩ p hp
    by_cases hpl : p < A.length
    · rw [List.getD_append _ _ _ _ hpl] at hp
      rw [List.getD_append _ _ _ _ (by omega)]
      exact H1 p hp
    · rw [List.getD_append_right _ _ _ _ (by omega)] at hp
      rw [List.getD_append_right _ _ _ _ (by omega), ← h]
      exact H2 _ hp

theorem getD_ofFn {n : ℕ} (g : Fin n → Bool) (p : ℕ) :
    (List.ofFn g).getD p false = if h : p < n then g ⟨p, h⟩ else false := by
  split_ifs with h
  · rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_ofFn]
  · exact List.getD_eq_default _ _ (by simp; omega)

theorem listLe_ofFn {n : ℕ} (g g' : Fin n → Bool) :
    listLe (List.ofFn g) (List.ofFn g') ↔ ∀ v, g v = true → g' v = true := by
  constructor
  · intro H v hv
    have := H v.val (by rw [getD_ofFn, dif_pos v.isLt]; exact hv)
    rwa [getD_ofFn, dif_pos v.isLt] at this
  · intro H p hp
    rw [getD_ofFn] at hp ⊢
    split_ifs at hp ⊢ with h
    exact H _ hp

theorem length_flat {k d : ℕ} (F : Fin k → List Bool) (hF : ∀ j, (F j).length = d) :
    (List.ofFn F).flatten.length = k * d := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.ofFn_succ, List.flatten_cons, List.length_append, ih (fun j => F j.succ) (fun j => hF _), hF]
    ring

theorem listLe_flat {k d : ℕ} (F F' : Fin k → List Bool) (hF : ∀ j, (F j).length = d)
    (hF' : ∀ j, (F' j).length = d) :
    listLe (List.ofFn F).flatten (List.ofFn F').flatten ↔ ∀ j, listLe (F j) (F' j) := by
  induction k with
  | zero =>
    constructor
    · intro _ j; exact j.elim0
    · intro _ p hp; simp at hp
  | succ k ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.flatten_cons, List.flatten_cons,
      listLe_append (by rw [hF, hF']),
      ih (fun j => F j.succ) (fun j => F' j.succ) (fun j => hF _) (fun j => hF' _)]
    constructor
    · rintro ⟨h0, hs⟩ j
      exact Fin.cases h0 (fun j => hs j) j
    · intro H; exact ⟨H 0, fun j => H j.succ⟩

variable (u d k : ℕ) (tag : Fin k → Finset (Fin u))

def preL (i : Fin k) (X : Fin k → Finset (Fin d)) : List Bool :=
  List.ofFn (fun v : Fin u => decide (v ∈ tag i)) ++
    (List.ofFn (fun j : Fin k => List.ofFn (fun v : Fin d => decide (v ∈ X j)))).flatten

theorem preL_length (i : Fin k) (X : Fin k → Finset (Fin d)) : (preL u d k tag i X).length = u + k * d := by
  unfold preL
  rw [List.length_append, List.length_ofFn, length_flat (d := d) _ (fun j => by simp)]

def enc (i : Fin k) (X : Fin k → Finset (Fin d)) : Finset (Fin (u + k * d)) :=
  Finset.univ.filter (fun a => (preL u d k tag i X).getD a.val false = true)

theorem mem_enc {i : Fin k} {X : Fin k → Finset (Fin d)} {a : Fin (u + k * d)} :
    a ∈ enc u d k tag i X ↔ (preL u d k tag i X).getD a.val false = true := by
  simp [enc]

theorem enc_sub_iff (i i' : Fin k) (X X' : Fin k → Finset (Fin d)) :
    enc u d k tag i X ⊆ enc u d k tag i' X' ↔ tag i ⊆ tag i' ∧ ∀ j, X j ⊆ X' j := by
  have key : enc u d k tag i X ⊆ enc u d k tag i' X' ↔
      listLe (preL u d k tag i X) (preL u d k tag i' X') := by
    constructor
    · intro H p hp
      have hpl : p < u + k * d := by
        by_contra hc
        rw [List.getD_eq_default _ _ (by rw [preL_length]; omega)] at hp
        exact Bool.false_ne_true hp
      have := H ((mem_enc u d k tag (a := ⟨p, hpl⟩)).2 hp)
      exact (mem_enc u d k tag).1 this
    · intro H a ha
      exact (mem_enc u d k tag).2 (H _ ((mem_enc u d k tag).1 ha))
  rw [key]
  unfold preL
  rw [listLe_append (by simp), listLe_ofFn, listLe_flat (d := d) _ _ (fun j => by simp) (fun j => by simp)]
  simp only [listLe_ofFn, decide_eq_true_eq, Finset.subset_iff]

def raw1 {N : ℕ} (S : Finset (Fin N)) : List Bool := List.ofFn (fun a : Fin N => decide (a ∈ S)) ++ [false,true]

theorem ofFn_enc (i : Fin k) (X : Fin k → Finset (Fin d)) :
    List.ofFn (fun a : Fin (u + k * d) => decide (a ∈ enc u d k tag i X)) = preL u d k tag i X := by
  apply List.ext_getElem (by rw [List.length_ofFn, preL_length])
  intro p h1 h2
  rw [List.getElem_ofFn, ← List.getD_eq_getElem _ false h2]
  cases hb : (preL u d k tag i X).getD p false
  · simp only [mem_enc, Fin.val_mk]; rw [hb]; rfl
  · simp only [mem_enc, Fin.val_mk]; rw [hb]; rfl

theorem raw_eq_enc (i : Fin k) (X : Fin k → Finset (Fin d)) {d1 : ∀ v, Decidable (v ∈ tag i)}
    {d2 : ∀ j v, Decidable (v ∈ X j)} :
    List.ofFn (fun v : Fin u => @decide (v ∈ tag i) (d1 v)) ++
      (List.ofFn (fun j : Fin k => List.ofFn (fun v : Fin d => @decide (v ∈ X j) (d2 j v)))).flatten ++
        [false,true] = raw1 (enc u d k tag i X) := by
  unfold raw1
  rw [ofFn_enc]
  unfold preL
  congr!

end Enc

section Levels
open scoped Classical
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem val_eq {n m : ℕ} (x : Fin m → Finset (Fin n)) (gs : List Gate) (p : ℕ) (s : Fin m) (S : Finset (Fin n))
    (h : x s = S) : val x gs p s = ((Circuit.mk gs 0).wires (raw1 S)).getD p false := by
  subst h; rfl

theorem levels (N B : ℕ) (C : Circuit) (fan : FanInTwo C) (hnc : PEqualNP.NotBracket.notCount C ≤ B) :
    ∃ lev : Finset (Fin N) → ℕ, (∀ S, lev S < 2 ^ B) ∧
      ∀ S S', S ⊆ S' → lev S ≤ lev S' ∧ (lev S = lev S' → ∀ p,
        (C.wires (raw1 S)).getD p false = true → (C.wires (raw1 S')).getD p false = true) := by
  let e := Fintype.equivFin (Finset (Fin N))
  let x : Fin (Fintype.card (Finset (Fin N))) → Finset (Fin N) := e.symm
  refine ⟨fun S => score (e S) (trace x C.gates), fun S => ?_, fun S S' sub => ?_⟩
  · have h1 := score_lt (e S) (trace x C.gates)
    rw [trace_length] at h1
    have h2 : PEqualNP.NotBracket.notCount ⟨C.gates, 0⟩ = PEqualNP.NotBracket.notCount C := rfl
    rw [h2] at h1
    exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) hnc)
  · have sub' : x (e S) ⊆ x (e S') := by simpa [x] using sub
    have so := stepOrder x C.gates fan (e S) (e S') sub'
    refine ⟨so.1, fun eq p hp => ?_⟩
    have h3 := so.2 eq p
    rw [val_eq x C.gates p (e S) S (by simp [x]), val_eq x C.gates p (e S') S' (by simp [x])] at h3
    exact h3 hp

end Levels

section Chains
open scoped Classical

theorem chain_count (L : ℕ → ℕ) (Fall : ℕ → Prop) [DecidablePred Fall] (d : ℕ)
    (h : ∀ j < d, L j ≤ L (j+1) ∧ (Fall j → L j < L (j+1))) :
    L 0 + ((Finset.range d).filter Fall).card ≤ L d := by
  induction d with
  | zero => simp
  | succ d ih =>
    have ih' := ih (fun j hj => h j (by omega))
    have hd := h d (by omega)
    rw [Finset.card_filter] at ih'
    rw [Finset.card_filter, Finset.sum_range_succ]
    split_ifs with hf
    · have := hd.2 hf; omega
    · have := hd.1; omega

theorem path_tele (l : ℕ) (S E loc : Fin (l+1) → ℕ) (J : Fin l → ℕ)
    (h1 : ∀ a, S a + loc a ≤ E a) (h2 : ∀ j : Fin l, E j.castSucc + J j ≤ S j.succ) :
    S 0 + (∑ a, loc a) + (∑ j, J j) ≤ E (Fin.last l) := by
  induction l with
  | zero => simpa using h1 0
  | succ l ih =>
    have ih' := ih (fun a => S a.castSucc) (fun a => E a.castSucc) (fun a => loc a.castSucc)
      (fun j => J j.castSucc) (fun a => h1 _)
      (fun j => by have := h2 j.castSucc; rw [Fin.succ_castSucc] at this; exact this)
    rw [Fin.sum_univ_castSucc (f := loc), Fin.sum_univ_castSucc (f := J)]
    have h2l := h2 (Fin.last l)
    have h1l := h1 (Fin.last (l+1))
    simp only [Fin.succ_last, Nat.succ_eq_add_one] at h2l
    simp only [Fin.castSucc_zero] at ih'
    beta_reduce at ih'
    omega

theorem prefix_fn (k : ℕ) (hk : 0 < k) (rel : Fin k → Fin k → Prop) (hirr : ∀ i, ¬ rel i i)
    (htr : ∀ a b c, rel a b → rel b c → rel a c) (loc : Fin k → ℕ) (jmp : Fin k → Fin k → ℕ) (K : ℕ)
    (hpath : ∀ (l : ℕ) (q : Fin (l+1) → Fin k), (∀ a b, a < b → rel (q a) (q b)) →
      (∑ a, loc (q a)) + (∑ j : Fin l, jmp (q j.castSucc) (q j.succ)) < K) :
    ∃ P : Fin k → ℕ, (∀ i, P i + loc i < K) ∧ (∀ i i', rel i i' → P i + loc i + jmp i i' ≤ P i') := by
  let V' : ∀ l, (Fin (l+1) → Fin k) → ℕ := fun l q =>
    (∑ a : Fin l, loc (q a.castSucc)) + ∑ j : Fin l, jmp (q j.castSucc) (q j.succ)
  let good : ∀ l, (Fin (l+1) → Fin k) → Fin k → Prop := fun l q i =>
    (∀ a b, a < b → rel (q a) (q b)) ∧ q (Fin.last l) = i
  let P : Fin k → ℕ := fun i => (Finset.range k).sup (fun l =>
    (Finset.univ.filter (fun q : Fin (l+1) → Fin k => good l q i)).sup (V' l))
  have hV : ∀ l (q : Fin (l+1) → Fin k), (∑ a, loc (q a)) + (∑ j : Fin l, jmp (q j.castSucc) (q j.succ)) =
      V' l q + loc (q (Fin.last l)) := by
    intro l q
    simp only [V']
    rw [Fin.sum_univ_castSucc (f := fun a => loc (q a))]
    ring
  have hlen : ∀ l (q : Fin (l+1) → Fin k), (∀ a b, a < b → rel (q a) (q b)) → l < k := by
    intro l q hq
    have inj : Function.Injective q := by
      intro a b hab
      rcases lt_trichotomy a b with h | h | h
      · exact absurd (hab ▸ hq a b h) (hirr _)
      · exact h
      · exact absurd (hab ▸ hq b a h) (hirr _)
    have := Fintype.card_le_of_injective q inj
    simp only [Fintype.card_fin] at this
    omega
  refine ⟨P, fun i => ?_, fun i i' hii' => ?_⟩
  · have hloc : loc i < K := by
      have := hpath 0 (fun _ => i) (fun a b h => absurd h (by rw [Fin.lt_def]; have := a.isLt; have := b.isLt; omega))
      simpa using this
    have : P i ≤ K - 1 - loc i := by
      apply Finset.sup_le
      intro l _
      apply Finset.sup_le
      intro q hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, good] at hq
      have h1 := hpath l q hq.1
      rw [hV, hq.2] at h1
      omega
    omega
  · have ext : ∀ l, l ∈ Finset.range k → ∀ q ∈ Finset.univ.filter (fun q : Fin (l+1) → Fin k => good l q i),
        V' l q + (loc i + jmp i i') ≤ P i' := by
      intro l _ q hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, good] at hq
      let q' : Fin (l+2) → Fin k := fun a => if h : a.val < l+1 then q ⟨a.val, h⟩ else i'
      have hq'1 : ∀ a : Fin (l+1), q' a.castSucc = q a := by
        intro a
        show (if h : (Fin.castSucc a).val < l+1 then q ⟨(Fin.castSucc a).val, h⟩ else i') = q a
        rw [dif_pos (show (Fin.castSucc a).val < l+1 from a.isLt)]
        rfl
      have hq'2 : q' (Fin.last (l+1)) = i' := by simp [q']
      have strict' : ∀ a b, a < b → rel (q' a) (q' b) := by
        intro a b hab
        rw [Fin.lt_def] at hab
        by_cases hb : b.val < l+1
        · have ha : a.val < l+1 := by omega
          simp only [q', dif_pos ha, dif_pos hb]
          exact hq.1 _ _ (by rw [Fin.lt_def]; exact hab)
        · have ha : a.val < l+1 := by have := b.isLt; omega
          simp only [q', dif_pos ha, dif_neg hb]
          by_cases hal : a.val = l
          · have e : (⟨a.val, ha⟩ : Fin (l+1)) = Fin.last l := Fin.ext hal
            rw [e, hq.2]; exact hii'
          · exact htr _ _ _ (hq.1 ⟨a.val, ha⟩ (Fin.last l) (by rw [Fin.lt_def]; simp; omega)) (hq.2 ▸ hii')
      have hl1 : l + 1 ∈ Finset.range k := Finset.mem_range.2 (hlen (l+1) q' strict')
      have hmem : q' ∈ Finset.univ.filter (fun q : Fin (l+1+1) → Fin k => good (l+1) q i') := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, good]; exact ⟨strict', hq'2⟩
      have hval : V' (l+1) q' = V' l q + (loc i + jmp i i') := by
        simp only [V']
        rw [Fin.sum_univ_castSucc (f := fun a => loc (q' a.castSucc)),
          Fin.sum_univ_castSucc (f := fun j => jmp (q' j.castSucc) (q' j.succ))]
        simp only [hq'1, Fin.succ_castSucc, Fin.succ_last, hq'2, hq.2]
        ring
      calc V' l q + (loc i + jmp i i') = V' (l+1) q' := hval.symm
        _ ≤ (Finset.univ.filter (fun q : Fin (l+1+1) → Fin k => good (l+1) q i')).sup (V' (l+1)) :=
            Finset.le_sup hmem
        _ ≤ P i' := Finset.le_sup (f := fun l => (Finset.univ.filter
              (fun q : Fin (l+1) → Fin k => good l q i')).sup (V' l)) hl1
    have h0 : (0 : ℕ) ∈ Finset.range k := Finset.mem_range.2 hk
    have q0mem : (fun _ : Fin (0+1) => i) ∈ Finset.univ.filter (fun q : Fin (0+1) → Fin k => good 0 q i) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, good]
      refine ⟨fun a b h => absurd h (by rw [Fin.lt_def]; have := a.isLt; have := b.isLt; omega), by simp⟩
    have hc : loc i + jmp i i' ≤ P i' := by
      have := ext 0 h0 _ q0mem; simp [V'] at this; omega
    have : P i ≤ P i' - (loc i + jmp i i') := by
      apply Finset.sup_le
      intro l hl
      apply Finset.sup_le
      intro q hq
      have := ext l hl q hq
      omega
    omega

end Chains

section Height
open scoped Classical
variable {d t : ℕ}

def fl (w z : Fin t → Bool) : Prop := ∃ a, w a = true ∧ z a = false

theorem fl_split (w y z : Fin t → Bool) (h : fl w z) : fl w y ∨ fl y z := by
  obtain ⟨a, ha, hz⟩ := h
  cases hy : y a
  · exact Or.inl ⟨a, ha, hy⟩
  · exact Or.inr ⟨a, hy, hz⟩

theorem fl_self (w : Fin t → Bool) : ¬ fl w w := by
  rintro ⟨a, h1, h2⟩; rw [h1] at h2; exact Bool.noConfusion h2

noncomputable def hg (g : Finset (Fin d) → Fin t → Bool) (x : Finset (Fin d)) : ℕ :=
  x.attach.sup (fun a => hg g (x.erase a.1) + if fl (g (x.erase a.1)) (g x) then 1 else 0)
termination_by x.card
decreasing_by exact Finset.card_erase_lt_of_mem a.2

theorem hg_eq (g : Finset (Fin d) → Fin t → Bool) (x : Finset (Fin d)) :
    hg g x = x.attach.sup (fun a => hg g (x.erase a.1) + if fl (g (x.erase a.1)) (g x) then 1 else 0) := by
  rw [hg]

theorem hg_empty (g : Finset (Fin d) → Fin t → Bool) : hg g (∅ : Finset (Fin d)) = 0 := by
  rw [hg_eq]; simp

theorem hg_step (g : Finset (Fin d) → Fin t → Bool) (x : Finset (Fin d)) (a : Fin d) (ha : a ∈ x) :
    hg g (x.erase a) + (if fl (g (x.erase a)) (g x) then 1 else 0) ≤ hg g x := by
  rw [hg_eq g x]
  exact Finset.le_sup (f := fun a : x => hg g (x.erase a.1) + if fl (g (x.erase a.1)) (g x) then 1 else 0)
    (Finset.mem_attach x ⟨a, ha⟩)

theorem hg_mono (g : Finset (Fin d) → Fin t → Bool) : ∀ (n : ℕ) (x x' : Finset (Fin d)), x ⊆ x' →
    (x' \ x).card = n → hg g x + (if fl (g x) (g x') then 1 else 0) ≤ hg g x' := by
  intro n
  induction n with
  | zero =>
    intro x x' hs hc
    have : x' = x := by
      apply Finset.Subset.antisymm _ hs
      intro b hb
      by_contra hn
      have hm : b ∈ x' \ x := Finset.mem_sdiff.2 ⟨hb, hn⟩
      rw [Finset.card_eq_zero] at hc
      rw [hc] at hm
      simp at hm
    subst this
    rw [if_neg (fl_self _)]
    omega
  | succ n ih =>
    intro x x' hs hc
    obtain ⟨a, ha⟩ : (x' \ x).Nonempty := by rw [← Finset.card_pos]; omega
    have ha' := Finset.mem_sdiff.1 ha
    have hs2 : x ⊆ x'.erase a := fun b hb => Finset.mem_erase.2 ⟨fun h => ha'.2 (h ▸ hb), hs hb⟩
    have hc2 : (x'.erase a \ x).card = n := by
      have : x'.erase a \ x = (x' \ x).erase a := by
        ext b; simp only [Finset.mem_sdiff, Finset.mem_erase]; tauto
      rw [this, Finset.card_erase_of_mem ha, hc]
      rfl
    have h1 := ih x (x'.erase a) hs2 hc2
    have h2 := hg_step g x' a ha'.1
    by_cases hf : fl (g x) (g x')
    · rw [if_pos hf]
      rcases fl_split _ (g (x'.erase a)) _ hf with h | h
      · rw [if_pos h] at h1
        split_ifs at h2 <;> omega
      · rw [if_pos h] at h2
        split_ifs at h1 <;> omega
    · rw [if_neg hf]
      split_ifs at h1 h2 <;> omega

def cut (π : Equiv.Perm (Fin d)) (j : ℕ) : Finset (Fin d) := Finset.univ.filter (fun a => (π a).val < j)

noncomputable def cnt (g : Finset (Fin d) → Fin t → Bool) (π : Equiv.Perm (Fin d)) (J : ℕ) : ℕ :=
  ((Finset.range J).filter (fun j => fl (g (cut π j)) (g (cut π (j+1))))).card

theorem cnt_succ (g : Finset (Fin d) → Fin t → Bool) (π : Equiv.Perm (Fin d)) (J : ℕ) :
    cnt g π (J+1) = cnt g π J + if fl (g (cut π J)) (g (cut π (J+1))) then 1 else 0 := by
  unfold cnt
  rw [Finset.card_filter, Finset.sum_range_succ, ← Finset.card_filter]

theorem hg_perm (g : Finset (Fin d) → Fin t → Bool) : ∀ (n : ℕ) (x : Finset (Fin d)), x.card = n →
    ∃ π : Equiv.Perm (Fin d), cut π n = x ∧ hg g x ≤ cnt g π n := by
  intro n
  induction n with
  | zero =>
    intro x hx
    rw [Finset.card_eq_zero] at hx
    subst hx
    refine ⟨1, ?_, by rw [hg_empty]; exact Nat.zero_le _⟩
    ext a; simp [cut]
  | succ n ih =>
    intro x hx
    have hne : x.attach.Nonempty := by
      rw [Finset.attach_nonempty_iff, ← Finset.card_pos]; omega
    obtain ⟨⟨a, ha⟩, _, hmax⟩ := Finset.exists_mem_eq_sup x.attach hne
      (fun a => hg g (x.erase a.1) + if fl (g (x.erase a.1)) (g x) then 1 else 0)
    rw [← hg_eq] at hmax
    dsimp only at hmax
    have hcard : (x.erase a).card = n := by rw [Finset.card_erase_of_mem ha, hx]; rfl
    obtain ⟨π0, hcut0, hle0⟩ := ih (x.erase a) hcard
    have hnd : n < d := by
      have := Finset.card_le_univ x
      simp only [Fintype.card_fin] at this
      omega
    let p : Fin d := ⟨n, hnd⟩
    let π : Equiv.Perm (Fin d) := π0.trans (Equiv.swap (π0 a) p)
    have hπ : ∀ b, π b = Equiv.swap (π0 a) p (π0 b) := fun b => rfl
    have ha0 : n ≤ (π0 a).val := by
      by_contra hc
      have hm : a ∈ cut π0 n := by simp only [cut, Finset.mem_filter, Finset.mem_univ, true_and]; omega
      rw [hcut0] at hm
      simp at hm
    have agree : ∀ j ≤ n, cut π j = cut π0 j := by
      intro j hj
      ext b
      simp only [cut, Finset.mem_filter, Finset.mem_univ, true_and, hπ, Equiv.swap_apply_def]
      split_ifs with h1 h2
      · have : b = a := π0.injective h1
        subst this
        simp only [p]
        omega
      · rw [h2]
        simp only [p]
        omega
      · exact Iff.rfl
    have top : cut π (n+1) = x := by
      ext b
      simp only [cut, Finset.mem_filter, Finset.mem_univ, true_and, hπ, Equiv.swap_apply_def]
      split_ifs with h1 h2
      · have : b = a := π0.injective h1
        subst this
        simp only [p]
        exact ⟨fun _ => ha, fun _ => by omega⟩
      · have hba : b ≠ a := fun h => h1 (by rw [h])
        have hne' : π0 a ≠ p := fun h => h1 (h2.trans h.symm)
        have hval : n < (π0 a).val := by
          have : (π0 a).val ≠ n := fun h => hne' (Fin.ext h)
          omega
        have hbx : b ∉ x := by
          intro hb
          have hm : b ∈ x.erase a := Finset.mem_erase.2 ⟨hba, hb⟩
          rw [← hcut0] at hm
          simp only [cut, Finset.mem_filter, Finset.mem_univ, true_and, h2] at hm
          simp only [p] at hm
          omega
        constructor
        · intro h; omega
        · intro h; exact absurd h hbx
      · have hba : b ≠ a := fun h => h1 (by rw [h])
        have hvn : (π0 b).val ≠ n := fun h => h2 (Fin.ext h)
        have e1 : b ∈ x ↔ b ∈ x.erase a := by simp [Finset.mem_erase, hba]
        rw [e1, ← hcut0]
        simp only [cut, Finset.mem_filter, Finset.mem_univ, true_and]
        omega
    refine ⟨π, top, ?_⟩
    have cnt_eq : cnt g π n = cnt g π0 n := by
      unfold cnt
      congr 1
      apply Finset.filter_congr
      intro j hj
      rw [Finset.mem_range] at hj
      rw [agree j (by omega), agree (j+1) (by omega)]
    have hfin : cnt g π (n+1) = cnt g π0 n + (if fl (g (x.erase a)) (g x) then 1 else 0) := by
      rw [cnt_succ, cnt_eq, agree n le_rfl, top, hcut0]
    rw [hfin, hmax]
    exact Nat.add_le_add_right hle0 _

theorem hg_le_cnt (g : Finset (Fin d) → Fin t → Bool) : ∃ π : Equiv.Perm (Fin d), hg g Finset.univ ≤ cnt g π d := by
  obtain ⟨π, _, h⟩ := hg_perm g d Finset.univ (by simp)
  exact ⟨π, h⟩

end Height

end PEqualNP.Outside.L_lib_1341_aux

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_lib_1341 : (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
let valid := fun (d : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
  PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (d+2) C ∧
  C.output < d+2+C.size
∀ (u d k t B : Nat) (tag : Fin k → Finset (Fin u)),
  0 < k → Function.Injective tag →
  let N := u+k*d
  let raw := fun (i : Fin k) (X : Fin k → Finset (Fin d)) =>
    List.ofFn (fun v : Fin u => decide (v ∈ tag i)) ++
    (List.ofFn (fun j : Fin k => List.ofFn (fun v : Fin d => decide (v ∈ X j)))).flatten ++ [false,true]
  let falls := fun (w z : Fin t → Bool) => ∃ a, w a = true ∧ z a = false
  ∀ ok : Fin k → Finset (Fin d) → (Fin t → Bool) → Prop,
    (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin t → Nat), valid N C ∧
      (∀ a, tap a < N+2+C.size) ∧ PEqualNP.NotBracket.notCount C ≤ B ∧
      ∀ i X, ok i (X i) (fun a => ((C.wires (raw i X)).getD (tap a) false))) ↔
    ∃ f : Fin k → Finset (Fin d) → Fin t → Bool, (∀ i x, ok i x (f i x)) ∧
      let cut := fun (π : Equiv.Perm (Fin d)) (j : Nat) => Finset.univ.filter (fun a => (π a).val < j)
      let localHeight := fun i => Finset.univ.sup (fun π : Equiv.Perm (Fin d) =>
        ((Finset.range d).filter (fun j => falls (f i (cut π j)) (f i (cut π (j+1))))).card)
      ∀ (l : Nat) (path : Fin (l+1) → Fin k),
        (∀ a b, a < b → tag (path a) ⊂ tag (path b)) →
        (∑ a, localHeight (path a)) +
          (Finset.univ.filter (fun j : Fin l =>
            falls (f (path j.castSucc) Finset.univ) (f (path j.succ) ∅))).card < 2^B) := by
  intro valid u d k t B tag hk htag N raw falls ok
  have hraw : ∀ i X, raw i X = PEqualNP.Outside.L_lib_1341_aux.raw1 (PEqualNP.Outside.L_lib_1341_aux.enc u d k tag i X) :=
    fun i X => PEqualNP.Outside.L_lib_1341_aux.raw_eq_enc u d k tag i X
  let slice : Fin k → Finset (Fin d) → Fin k → Finset (Fin d) := fun i x j =>
    if j = i then x else if tag j ⊂ tag i then Finset.univ else ∅
  have slice_mono : ∀ i x x', x ⊆ x' → ∀ j, slice i x j ⊆ slice i x' j := by
    intro i x x' h j
    simp only [slice]
    split_ifs
    · exact h
    · exact subset_refl _
    · exact subset_refl _
  have enc_mono : ∀ i x x', x ⊆ x' →
      PEqualNP.Outside.L_lib_1341_aux.enc u d k tag i (slice i x) ⊆ PEqualNP.Outside.L_lib_1341_aux.enc u d k tag i (slice i x') := fun i x x' h =>
    (PEqualNP.Outside.L_lib_1341_aux.enc_sub_iff u d k tag i i _ _).2 ⟨subset_refl _, slice_mono i x x' h⟩
  have jump_sub : ∀ i i', tag i ⊂ tag i' →
      PEqualNP.Outside.L_lib_1341_aux.enc u d k tag i (slice i Finset.univ) ⊆ PEqualNP.Outside.L_lib_1341_aux.enc u d k tag i' (slice i' ∅) := by
    intro i i' hii
    refine (PEqualNP.Outside.L_lib_1341_aux.enc_sub_iff u d k tag i i' _ _).2 ⟨hii.subset, fun j => ?_⟩
    have hne : i ≠ i' := fun h => by subst h; exact ssubset_irrefl _ hii
    simp only [slice]
    by_cases h1 : j = i
    · subst h1
      rw [if_pos rfl, if_neg hne, if_pos hii]
    · by_cases h2 : tag j ⊂ tag i
      · have h3 : j ≠ i' := fun h => by subst h; exact ssubset_asymm h2 hii
        rw [if_neg h1, if_pos h2, if_neg h3, if_pos (h2.trans hii)]
      · rw [if_neg h1, if_neg h2]
        exact Finset.empty_subset _
  constructor
  · rintro ⟨C, tap, ⟨fan, _, _⟩, _, hnc, hC⟩
    obtain ⟨lev, hlev, hmono⟩ := PEqualNP.Outside.L_lib_1341_aux.levels N B C fan hnc
    let out : Finset (Fin N) → Fin t → Bool := fun S a => (C.wires (PEqualNP.Outside.L_lib_1341_aux.raw1 S)).getD (tap a) false
    have step : ∀ S S', S ⊆ S' → lev S ≤ lev S' ∧ (falls (out S) (out S') → lev S < lev S') := by
      intro S S' sub
      obtain ⟨h1, h2⟩ := hmono S S' sub
      refine ⟨h1, fun hfall => ?_⟩
      obtain ⟨a, ha, hb⟩ := hfall
      rcases lt_or_eq_of_le h1 with h | h
      · exact h
      · have h3 := h2 h (tap a) ha
        simp only [out] at hb
        rw [h3] at hb
        exact absurd hb (by simp)
    let f : Fin k → Finset (Fin d) → Fin t → Bool := fun i x => out (PEqualNP.Outside.L_lib_1341_aux.enc u d k tag i (slice i x))
    refine ⟨f, fun i x => ?_, ?_⟩
    · have h0 := hC i (slice i x)
      have e1 : slice i x i = x := if_pos rfl
      rw [e1, hraw] at h0
      exact h0
    · intro cut localHeight l path hpath
      have cut0 : ∀ π, cut π 0 = ∅ := by intro π; ext a; simp [cut]
      have cutd : ∀ π, cut π d = Finset.univ := by intro π; ext a; simp [cut, (π a).isLt]
      have cutm : ∀ π j, cut π j ⊆ cut π (j+1) := by
        intro π j a ha; simp only [cut, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢; omega
      have locBound : ∀ i, lev (PEqualNP.Outside.L_lib_1341_aux.enc u d k tag i (slice i ∅)) + localHeight i ≤
          lev (PEqualNP.Outside.L_lib_1341_aux.enc u d k tag i (slice i Finset.univ)) := by
        intro i
        have hSE := (step _ _ (enc_mono i _ _ (Finset.empty_subset Finset.univ))).1
        have hle : localHeight i ≤ lev (PEqualNP.Outside.L_lib_1341_aux.enc u d k tag i (slice i Finset.univ)) -
            lev (PEqualNP.Outside.L_lib_1341_aux.enc u d k tag i (slice i ∅)) := by
          dsimp only [localHeight]
          apply Finset.sup_le
          intro π _
          have hc := @PEqualNP.Outside.L_lib_1341_aux.chain_count (fun j => lev (PEqualNP.Outside.L_lib_1341_aux.enc u d k tag i (slice i (cut π j))))
            (fun j => falls (f i (cut π j)) (f i (cut π (j+1)))) (fun j => Classical.propDecidable _) d
            (fun j _ => step _ _ (enc_mono i _ _ (cutm π j)))
          beta_reduce at hc
          rw [cut0, cutd] at hc
          omega
        omega
      have jumpBound : ∀ j : Fin l, lev (PEqualNP.Outside.L_lib_1341_aux.enc u d k tag (path j.castSucc) (slice (path j.castSucc) Finset.univ)) +
          @ite ℕ (falls (f (path j.castSucc) Finset.univ) (f (path j.succ) ∅)) (Classical.propDecidable _) 1 0 ≤
          lev (PEqualNP.Outside.L_lib_1341_aux.enc u d k tag (path j.succ) (slice (path j.succ) ∅)) := by
        intro j
        have hss : tag (path j.castSucc) ⊂ tag (path j.succ) := hpath _ _ Fin.castSucc_lt_succ
        have hst := step _ _ (jump_sub _ _ hss)
        split_ifs with hf
        · have := hst.2 hf; omega
        · have := hst.1; omega
      have tele := PEqualNP.Outside.L_lib_1341_aux.path_tele l (fun a => lev (PEqualNP.Outside.L_lib_1341_aux.enc u d k tag (path a) (slice (path a) ∅)))
        (fun a => lev (PEqualNP.Outside.L_lib_1341_aux.enc u d k tag (path a) (slice (path a) Finset.univ))) (fun a => localHeight (path a))
        (fun j => @ite ℕ (falls (f (path j.castSucc) Finset.univ) (f (path j.succ) ∅)) (Classical.propDecidable _) 1 0)
        (fun a => locBound (path a)) jumpBound
      have hE := hlev (PEqualNP.Outside.L_lib_1341_aux.enc u d k tag (path (Fin.last l)) (slice (path (Fin.last l)) Finset.univ))
      rw [Finset.card_filter]
      beta_reduce at tele
      omega
  · rintro ⟨f, hf, hcond⟩
    let loc : Fin k → ℕ := fun i => (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
      Finset.univ.sup (fun π : Equiv.Perm (Fin d) =>
        ((Finset.range d).filter (fun j => falls (f i (Finset.univ.filter (fun a => (π a).val < j)))
          (f i (Finset.univ.filter (fun a => (π a).val < j+1))))).card))
    let jmp : Fin k → Fin k → ℕ := fun i i' => (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
      if falls (f i Finset.univ) (f i' ∅) then 1 else 0)
    have hp : ∀ l (q : Fin (l+1) → Fin k), (∀ a b, a < b → tag (q a) ⊂ tag (q b)) →
        (∑ a, loc (q a)) + (∑ j : Fin l, jmp (q j.castSucc) (q j.succ)) < 2^B := by
      intro l q hq
      have h0 := hcond l q hq
      rw [Finset.card_filter] at h0
      exact h0
    obtain ⟨P, hP1, hP2⟩ := PEqualNP.Outside.L_lib_1341_aux.prefix_fn k hk (fun i i' => tag i ⊂ tag i') (fun i => ssubset_irrefl _)
      (fun a b c h1 h2 => h1.trans h2) loc jmp (2^B) hp
    let H : Fin k → Finset (Fin d) → ℕ := fun i x => PEqualNP.Outside.L_lib_1341_aux.hg (f i) x
    have hH1 : ∀ i x, H i x ≤ loc i := by
      intro i x
      have m := PEqualNP.Outside.L_lib_1341_aux.hg_mono (f i) _ x Finset.univ (Finset.subset_univ x) rfl
      obtain ⟨π, hπ⟩ := PEqualNP.Outside.L_lib_1341_aux.hg_le_cnt (f i)
      have hc : PEqualNP.Outside.L_lib_1341_aux.cnt (f i) π d ≤ loc i := by
        refine le_trans (le_of_eq ?_) (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
          Finset.le_sup (f := fun π : Equiv.Perm (Fin d) =>
            ((Finset.range d).filter (fun j => falls (f i (Finset.univ.filter (fun a => (π a).val < j)))
              (f i (Finset.univ.filter (fun a => (π a).val < j+1))))).card) (Finset.mem_univ π))
        have ec : ∀ j, PEqualNP.Outside.L_lib_1341_aux.cut π j = (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
            Finset.univ.filter (fun a : Fin d => (π a).val < j)) := by
          intro j; ext a; simp [PEqualNP.Outside.L_lib_1341_aux.cut]
        unfold PEqualNP.Outside.L_lib_1341_aux.cnt
        beta_reduce
        refine congrArg Finset.card ?_
        ext j
        simp only [Finset.mem_filter]
        rw [ec, ec]
        rfl
      exact le_trans (le_trans (Nat.le_add_right _ _) m) (le_trans hπ hc)
    let e : (Fin k × (Fin k → Finset (Fin d))) ≃ Fin (Fintype.card (Fin k × (Fin k → Finset (Fin d)))) := Fintype.equivFin _
    let x : Fin (Fintype.card (Fin k × (Fin k → Finset (Fin d)))) → Finset (Fin N) := fun s => PEqualNP.Outside.L_lib_1341_aux.enc u d k tag (e.symm s).1 (e.symm s).2
    let v : Fin (Fintype.card (Fin k × (Fin k → Finset (Fin d)))) → ℕ := fun s => P (e.symm s).1 + H (e.symm s).1 ((e.symm s).2 (e.symm s).1)
    let w : Fin (Fintype.card (Fin k × (Fin k → Finset (Fin d)))) → Fin t → Bool := fun s => f (e.symm s).1 ((e.symm s).2 (e.symm s).1)
    have key : ∀ i i' X X', PEqualNP.Outside.L_lib_1341_aux.enc u d k tag i X ⊆ PEqualNP.Outside.L_lib_1341_aux.enc u d k tag i' X' →
        P i + H i (X i) + @ite ℕ (PEqualNP.Outside.L_lib_1341_aux.fl (f i (X i)) (f i' (X' i'))) (Classical.propDecidable _) 1 0 ≤
          P i' + H i' (X' i') := by
      intro i i' X X' sub
      obtain ⟨ht, hX⟩ := (PEqualNP.Outside.L_lib_1341_aux.enc_sub_iff u d k tag i i' X X').1 sub
      by_cases hti : tag i = tag i'
      · have hii := htag hti
        subst hii
        have m := PEqualNP.Outside.L_lib_1341_aux.hg_mono (f i) _ (X i) (X' i) (hX i) rfl
        simp only [H]
        split_ifs at m ⊢ <;> omega
      · have hss : tag i ⊂ tag i' := Finset.ssubset_iff_subset_ne.2 ⟨ht, hti⟩
        have A1 := PEqualNP.Outside.L_lib_1341_aux.hg_mono (f i) _ (X i) Finset.univ (Finset.subset_univ _) rfl
        have A2 := hH1 i Finset.univ
        have Bq := hP2 i i' hss
        have Cq := PEqualNP.Outside.L_lib_1341_aux.hg_mono (f i') _ ∅ (X' i') (Finset.empty_subset _) rfl
        rw [PEqualNP.Outside.L_lib_1341_aux.hg_empty] at Cq
        simp only [H, jmp] at A1 A2 Bq Cq ⊢
        have split3 : PEqualNP.Outside.L_lib_1341_aux.fl (f i (X i)) (f i' (X' i')) → PEqualNP.Outside.L_lib_1341_aux.fl (f i (X i)) (f i Finset.univ) ∨
            falls (f i Finset.univ) (f i' ∅) ∨ PEqualNP.Outside.L_lib_1341_aux.fl (f i' ∅) (f i' (X' i')) := by
          intro h0
          rcases PEqualNP.Outside.L_lib_1341_aux.fl_split _ (f i Finset.univ) _ h0 with h | h
          · exact Or.inl h
          · rcases PEqualNP.Outside.L_lib_1341_aux.fl_split _ (f i' ∅) _ h with h' | h'
            · exact Or.inr (Or.inl h')
            · exact Or.inr (Or.inr h')
        split_ifs at A1 Bq Cq ⊢ <;> first | omega |
          (exfalso; rcases split3 (by assumption) with h | h | h <;> contradiction)
    have cap : ∀ s, v s < 2^B := by
      intro s
      have h1 := hP1 (e.symm s).1
      have h2 := hH1 (e.symm s).1 ((e.symm s).2 (e.symm s).1)
      simp only [v]
      omega
    have okv : PEqualNP.Outside.L_lib_1341_aux.OK x v w := by
      intro s s' sub
      have hk2 := key _ _ _ _ sub
      simp only [v, w]
      refine ⟨by split_ifs at hk2 <;> omega, fun heq a ha => ?_⟩
      by_contra hna
      have hf1 : PEqualNP.Outside.L_lib_1341_aux.fl (f (e.symm s).1 ((e.symm s).2 (e.symm s).1)) (f (e.symm s').1 ((e.symm s').2 (e.symm s').1)) :=
        ⟨a, ha, by simpa using hna⟩
      rw [if_pos hf1] at hk2
      omega
    obtain ⟨C, tap, fit, _⟩ := PEqualNP.Outside.L_lib_1341_aux.sufficient x v w cap okv
    obtain ⟨fan, back, outlt, hnc, _, taps, vals, _⟩ := fit
    refine ⟨C, tap, ⟨fan, back, outlt⟩, taps, le_of_eq hnc, fun i X => ?_⟩
    have hx : x (e (i, X)) = PEqualNP.Outside.L_lib_1341_aux.enc u d k tag i X := by simp [x]
    have hval : (fun a => (C.wires (raw i X)).getD (tap a) false) = f i (X i) := by
      funext a
      rw [hraw i X]
      have h1 := vals (e (i, X)) a
      rw [PEqualNP.Outside.L_lib_1341_aux.val_eq x C.gates (tap a) (e (i, X)) _ hx] at h1
      simp only [w, Equiv.symm_apply_apply] at h1
      exact h1
    rw [hval]
    exact hf i (X i)

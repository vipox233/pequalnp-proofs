import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1316_aux
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

def Valid (x : Fin m → Finset (Fin n)) (A : Fin m → Finset (Finset (Fin 2))) (r : ℕ) (S : Finset (Fin m))
    (lev : Fin m → ℕ) (wd : Fin m → Finset (Fin 2)) : Prop :=
  (∀ i ∈ S, wd i ∈ A i ∧ lev i < 2 ^ r) ∧
  ∀ i ∈ S, ∀ j ∈ S, x i ⊆ x j → lev i ≤ lev j ∧ (lev i = lev j → wd i ⊆ wd j)

def Feas (x : Fin m → Finset (Fin n)) (A : Fin m → Finset (Finset (Fin 2))) (r : ℕ) (S : Finset (Fin m)) : Prop :=
  ∃ lev wd, Valid x A r S lev wd

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

theorem feas_mono {x : Fin m → Finset (Fin n)} {A : Fin m → Finset (Finset (Fin 2))} {r : ℕ} {S T : Finset (Fin m)}
    (h : T ⊆ S) (hf : Feas x A r S) : Feas x A r T := by
  obtain ⟨lev, wd, h1, h2⟩ := hf
  exact ⟨lev, wd, fun i hi => h1 i (h hi), fun i hi j hj => h2 i (h hi) j (h hj)⟩

theorem rawEq (x : Fin m → Finset (Fin n)) (i : Fin m) {d : ∀ a : Fin n, Decidable (a ∈ x i)} :
    (List.ofFn (fun a : Fin n => @decide (a ∈ x i) (d a)) ++ [false,true]) = raw x i := by
  unfold raw
  congr 1
  congr 1
  funext a
  apply Bool.eq_iff_iff.mpr; simp

end Bridge

theorem fits_to_feas : letI : ∀ P : Prop, Decidable P := Classical.propDecidable
    ∀ (n m : ℕ) (x : Fin m → Finset (Fin n)) (A : Fin m → Finset (Finset (Fin 2))) (r : ℕ) (S : Finset (Fin m)),
    (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin 2 → Nat),
          PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
          C.output < n+2+C.size ∧ (∀ a, tap a < n+2+C.size) ∧ PEqualNP.NotBracket.notCount C ≤ r ∧
          ∀ i ∈ S, (Finset.univ.filter (fun a =>
            (C.wires (List.ofFn (fun j : Fin n => decide (j ∈ x i)) ++ [false,true])).getD (tap a) false = true)) ∈ A i) →
    Feas x A r S := by
  intro n m x A r S h
  obtain ⟨C, tap, fan, _, _, _, hnc, hS⟩ := h
  refine ⟨fun i => score i (trace x C.gates), fun i => Finset.univ.filter (fun a => val x C.gates (tap a) i = true), ?_, ?_⟩
  · intro i hi
    refine ⟨?_, ?_⟩
    · convert hS i hi using 1
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      first
        | (rw [rawEq x i]; rfl)
        | (simp only [rawEq]; rfl)
        | (erw [rawEq x i]; rfl)
        | (unfold val; rw [rawEq x i])
    · have h1 := score_lt i (trace x C.gates)
      rw [trace_length] at h1
      have h2 : PEqualNP.NotBracket.notCount ⟨C.gates, 0⟩ = PEqualNP.NotBracket.notCount C := rfl
      rw [h2] at h1
      exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) hnc)
  · intro i _ j _ sub
    have so := stepOrder x C.gates fan i j sub
    refine ⟨so.1, fun eq => ?_⟩
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact so.2 eq _ ha

theorem feas_to_fits : letI : ∀ P : Prop, Decidable P := Classical.propDecidable
    ∀ (n m : ℕ) (x : Fin m → Finset (Fin n)) (A : Fin m → Finset (Finset (Fin 2))) (r : ℕ) (S : Finset (Fin m)),
    Feas x A r S →
    (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin 2 → Nat),
          PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
          C.output < n+2+C.size ∧ (∀ a, tap a < n+2+C.size) ∧ PEqualNP.NotBracket.notCount C ≤ r ∧
          ∀ i ∈ S, (Finset.univ.filter (fun a =>
            (C.wires (List.ofFn (fun j : Fin n => decide (j ∈ x i)) ++ [false,true])).getD (tap a) false = true)) ∈ A i) := by
  intro n m x A r S h
  obtain ⟨lev, wd, hv, ho⟩ := h
  let e := S.orderEmbOfFin rfl
  let x' : Fin S.card → Finset (Fin n) := fun k => x (e k)
  let v : Fin S.card → ℕ := fun k => lev (e k)
  let w : Fin S.card → Fin 2 → Bool := fun k a => decide (a ∈ wd (e k))
  have he : ∀ k, e k ∈ S := fun k => Finset.orderEmbOfFin_mem S rfl k
  have cap : ∀ k, v k < 2 ^ r := fun k => (hv _ (he k)).2
  have ok : OK x' v w := by
    intro k k' sub
    have := ho _ (he k) _ (he k') sub
    refine ⟨this.1, fun eq a ha => ?_⟩
    simp only [w, decide_eq_true_eq] at ha ⊢
    exact this.2 eq ha
  obtain ⟨C, tap, fit, _⟩ := sufficient x' v w cap ok
  obtain ⟨fan, back, out, hnc, _, taps, vals, _⟩ := fit
  refine ⟨C, tap, fan, back, out, taps, le_of_eq hnc, ?_⟩
  intro i hi
  have hr : i ∈ Set.range e := by rw [Finset.range_orderEmbOfFin]; exact hi
  obtain ⟨k, rfl⟩ := hr
  convert (hv _ (he k)).1 using 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  first
    | rw [rawEq x (e k)]
    | simp only [rawEq]
    | erw [rawEq x (e k)]
  have := vals k a
  change val x' C.gates (tap a) k = true ↔ _
  rw [this]
  simp [w]

end PEqualNP.Outside.L_lib_1316_aux

namespace PEqualNP.Outside.L_lib_1316_aux
section Labels
open scoped Classical
variable {n m : ℕ} (x : Fin m → Finset (Fin n)) (A : Fin m → Finset (Finset (Fin 2)))

def MC (B : Finset (Finset (Fin 2))) : Prop := ∀ u ∈ B, ∀ v ∈ B, u ∩ v ∈ B

def MonoFeas (D : Finset (Fin m)) : Prop :=
  ∃ wd : Fin m → Finset (Fin 2), (∀ i ∈ D, wd i ∈ A i) ∧ ∀ i ∈ D, ∀ j ∈ D, x i ⊆ x j → wd i ⊆ wd j

theorem monoFeas_mono {D E : Finset (Fin m)} (h : E ⊆ D) (hf : MonoFeas x A D) : MonoFeas x A E := by
  obtain ⟨wd, h1, h2⟩ := hf
  exact ⟨wd, fun i hi => h1 i (h hi), fun i hi j hj => h2 i (h hi) j (h hj)⟩

noncomputable def Up (P : Finset (Fin m)) : ℕ → Finset (Fin m)
  | 0 => P
  | ℓ + 1 => (Up P ℓ).filter (fun i => ¬ MonoFeas x A ((Up P ℓ).filter (fun j => x j ⊆ x i)))

theorem up_succ_sub (P : Finset (Fin m)) (ℓ : ℕ) : Up x A P (ℓ + 1) ⊆ Up x A P ℓ := by
  intro i hi
  simp only [Up, Finset.mem_filter] at hi
  exact hi.1

theorem up_anti (P : Finset (Fin m)) {ℓ ℓ' : ℕ} (h : ℓ ≤ ℓ') : Up x A P ℓ' ⊆ Up x A P ℓ := by
  induction ℓ' with
  | zero =>
    obtain rfl : ℓ = 0 := by omega
    exact Finset.Subset.refl _
  | succ k ih =>
    rcases Nat.lt_or_ge ℓ (k + 1) with h' | h'
    · exact (up_succ_sub x A P k).trans (ih (by omega))
    · obtain rfl : ℓ = k + 1 := by omega
      exact Finset.Subset.refl _

theorem up_sub (P : Finset (Fin m)) (ℓ : ℕ) : Up x A P ℓ ⊆ P := up_anti x A P (Nat.zero_le ℓ)

theorem mem_up_succ {P : Finset (Fin m)} {ℓ : ℕ} {i : Fin m} :
    i ∈ Up x A P (ℓ + 1) ↔ i ∈ Up x A P ℓ ∧ ¬ MonoFeas x A ((Up x A P ℓ).filter (fun j => x j ⊆ x i)) := by
  simp only [Up, Finset.mem_filter]

theorem up_upward (P : Finset (Fin m)) : ∀ ℓ, ∀ i ∈ Up x A P ℓ, ∀ j ∈ P, x i ⊆ x j → j ∈ Up x A P ℓ := by
  intro ℓ
  induction ℓ with
  | zero => intro i _ j hj _; exact hj
  | succ k ih =>
    intro i hi j hj sub
    rw [mem_up_succ] at hi ⊢
    refine ⟨ih i hi.1 j hj sub, fun hf => hi.2 (monoFeas_mono x A ?_ hf)⟩
    intro q hq
    simp only [Finset.mem_filter] at hq ⊢
    exact ⟨hq.1, hq.2.trans sub⟩

theorem up_monoP {P Q : Finset (Fin m)} (h : P ⊆ Q) : ∀ ℓ, Up x A P ℓ ⊆ Up x A Q ℓ := by
  intro ℓ
  induction ℓ with
  | zero => exact h
  | succ k ih =>
    intro i hi
    rw [mem_up_succ] at hi ⊢
    refine ⟨ih hi.1, fun hf => hi.2 (monoFeas_mono x A ?_ hf)⟩
    intro q hq
    simp only [Finset.mem_filter] at hq ⊢
    exact ⟨ih hq.1, hq.2⟩

theorem up_lev (r : ℕ) (P : Finset (Fin m)) (lev : Fin m → ℕ) (wd : Fin m → Finset (Fin 2))
    (hv : Valid x A r P lev wd) : ∀ ℓ, ∀ i ∈ Up x A P ℓ, ℓ ≤ lev i := by
  intro ℓ
  induction ℓ with
  | zero => intro i _; exact Nat.zero_le _
  | succ k ih =>
    intro i hi
    rw [mem_up_succ] at hi
    have hk := ih i hi.1
    by_contra hlt
    have heq : lev i = k := by omega
    apply hi.2
    refine ⟨wd, ?_, ?_⟩
    · intro j hj
      simp only [Finset.mem_filter] at hj
      exact (hv.1 j (up_sub x A P k hj.1)).1
    · intro j hj q hq sub
      simp only [Finset.mem_filter] at hj hq
      have hjP := up_sub x A P k hj.1
      have hqP := up_sub x A P k hq.1
      have hiP := up_sub x A P k hi.1
      have e1 := (hv.2 j hjP i hiP hj.2).1
      have e2 := (hv.2 q hqP i hiP hq.2).1
      have e3 := ih j hj.1
      have e4 := ih q hq.1
      exact (hv.2 j hjP q hqP sub).2 (by omega)

theorem not_feas_of_up (r : ℕ) (P : Finset (Fin m)) (h : (Up x A P (2 ^ r)).Nonempty) : ¬ Feas x A r P := by
  rintro ⟨lev, wd, hv⟩
  obtain ⟨i, hi⟩ := h
  have h1 := up_lev x A r P lev wd hv _ i hi
  have h2 := (hv.1 i (up_sub x A P _ hi)).2
  omega

def ot (b : Fin 2) : Fin 2 := if b = 0 then 1 else 0

theorem ot_ne (b : Fin 2) : ot b ≠ b := by fin_cases b <;> decide
theorem ot_ot (b : Fin 2) : ot (ot b) = b := by fin_cases b <;> decide
theorem eq_ot_of_ne {b c : Fin 2} (h : b ≠ c) : b = ot c := by fin_cases b <;> fin_cases c <;> simp_all [ot]

def Intr (B : Finset (Finset (Fin 2))) (b : Fin 2) : Prop := ∀ w ∈ B, b ∈ w
def Coup (B : Finset (Finset (Fin 2))) (c b : Fin 2) : Prop := ∀ w ∈ B, c ∈ w → b ∈ w

def One (D : Finset (Fin m)) (i : Fin m) (b : Fin 2) : Prop := ∃ j ∈ D, x j ⊆ x i ∧ Intr (A j) b
def Two (D : Finset (Fin m)) (i : Fin m) (b : Fin 2) : Prop :=
  ∃ k ∈ D, ∃ j ∈ D, x k ⊆ x j ∧ x j ⊆ x i ∧ Intr (A k) (ot b) ∧ Coup (A j) (ot b) b

noncomputable def Phi (D : Finset (Fin m)) (i : Fin m) : Finset (Fin 2) :=
  Finset.univ.filter (fun b => One x A D i b ∨ Two x A D i b)

theorem mem_phi {D : Finset (Fin m)} {i : Fin m} {b : Fin 2} :
    b ∈ Phi x A D i ↔ One x A D i b ∨ Two x A D i b := by
  simp [Phi]

theorem phi_mono {D : Finset (Fin m)} {i i' : Fin m} (h : x i ⊆ x i') : Phi x A D i ⊆ Phi x A D i' := by
  intro b hb
  rw [mem_phi] at hb ⊢
  rcases hb with ⟨j, hj, s, t⟩ | ⟨k, hk, j, hj, s1, s2, t1, t2⟩
  · exact Or.inl ⟨j, hj, s.trans h, t⟩
  · exact Or.inr ⟨k, hk, j, hj, s1, s2.trans h, t1, t2⟩

theorem phi_sub {D E : Finset (Fin m)} {i : Fin m} (wd : Fin m → Finset (Fin 2))
    (hl : ∀ j ∈ E, wd j ∈ A j) (hm : ∀ j ∈ E, ∀ q ∈ E, x j ⊆ x q → wd j ⊆ wd q)
    (hi : i ∈ E) (hcl : ∀ j ∈ D, x j ⊆ x i → j ∈ E) : Phi x A D i ⊆ wd i := by
  intro b hb
  rw [mem_phi] at hb
  rcases hb with ⟨j, hj, s, t⟩ | ⟨k, hk, j, hj, s1, s2, t1, t2⟩
  · have hjE := hcl j hj s
    exact hm j hjE i hi s (t _ (hl j hjE))
  · have hjE := hcl j hj s2
    have hkE := hcl k hk (s1.trans s2)
    have h1 : ot b ∈ wd k := t1 _ (hl k hkE)
    have h2 : ot b ∈ wd j := hm k hkE j hjE s1 h1
    have h3 : b ∈ wd j := t2 _ (hl j hjE) h2
    exact hm j hjE i hi s2 h3

theorem mc_inf_mem {B : Finset (Finset (Fin 2))} (hB : MC B) (W : Finset (Finset (Fin 2))) (hW : W ⊆ B)
    (hne : W.Nonempty) : W.inf' hne id ∈ B := by
  apply Finset.inf'_mem (B : Set (Finset (Fin 2)))
  · intro u hu v hv
    exact hB u hu v hv
  · intro w hw; exact hW hw

theorem phi_closed {D : Finset (Fin m)} {i : Fin m} (hiD : i ∈ D) (hB : MC (A i))
    (hw : ∃ w ∈ A i, Phi x A D i ⊆ w) : Phi x A D i ∈ A i := by
  set U := Phi x A D i with hU
  let W := (A i).filter (fun w => U ⊆ w)
  have hne : W.Nonempty := by
    obtain ⟨w, hw1, hw2⟩ := hw
    exact ⟨w, Finset.mem_filter.2 ⟨hw1, hw2⟩⟩
  have hmem := mc_inf_mem hB W (Finset.filter_subset _ _) hne
  have hUle : U ⊆ W.inf' hne id := by
    apply Finset.le_inf'
    intro w hw
    exact (Finset.mem_filter.1 hw).2
  have hle : W.inf' hne id ⊆ U := by
    intro c hc
    by_contra hcU
    have hall : ∀ w ∈ A i, U ⊆ w → c ∈ w := by
      intro w hw hUw
      have : W.inf' hne id ≤ id w := Finset.inf'_le _ (Finset.mem_filter.2 ⟨hw, hUw⟩)
      exact this hc
    apply hcU
    rw [hU, mem_phi]
    by_cases hemp : U = ∅
    · left
      refine ⟨i, hiD, Finset.Subset.refl _, fun w hw => hall w hw (by rw [hemp]; exact Finset.empty_subset _)⟩
    · obtain ⟨b, hb⟩ := Finset.nonempty_iff_ne_empty.2 hemp
      have hbc : b ≠ c := fun e => hcU (e ▸ hb)
      have hbo : b = ot c := eq_ot_of_ne hbc
      have hcoup : Coup (A i) b c := by
        intro w hw hbw
        apply hall w hw
        intro d hd
        by_cases hdb : d = b
        · exact hdb ▸ hbw
        · have hdc : d ≠ c := fun e => hcU (e ▸ hd)
          exfalso
          have h1 : d.val ≠ b.val := fun e => hdb (Fin.ext e)
          have h2 : d.val ≠ c.val := fun e => hdc (Fin.ext e)
          have h3 : b.val ≠ c.val := fun e => hbc (Fin.ext e)
          have := b.isLt
          have := c.isLt
          have := d.isLt
          omega
      have hb' := hb
      rw [hU, mem_phi] at hb'
      rcases hb' with ⟨j, hj, s, t⟩ | ⟨k, hk, j, hj, s1, s2, t1, t2⟩
      · right
        refine ⟨j, hj, i, hiD, s, Finset.Subset.refl _, ?_, ?_⟩
        · rw [← hbo]; exact t
        · rw [← hbo]; exact hcoup
      · left
        refine ⟨k, hk, s1.trans s2, ?_⟩
        rw [hbo, ot_ot] at t1
        exact t1
  have : W.inf' hne id = U := Finset.Subset.antisymm hle hUle
  rw [← this]; exact hmem

theorem locality {D : Finset (Fin m)} (hB : ∀ i ∈ D, MC (A i))
    (h : ∀ i ∈ D, MonoFeas x A (D.filter (fun j => x j ⊆ x i))) : MonoFeas x A D := by
  refine ⟨Phi x A D, ?_, ?_⟩
  · intro i hi
    obtain ⟨wd, hl, hm⟩ := h i hi
    apply phi_closed x A hi (hB i hi)
    refine ⟨wd i, hl i (Finset.mem_filter.2 ⟨hi, Finset.Subset.refl _⟩), ?_⟩
    apply phi_sub x A wd hl hm (Finset.mem_filter.2 ⟨hi, Finset.Subset.refl _⟩)
    intro j hj s
    exact Finset.mem_filter.2 ⟨hj, s⟩
  · intro i _ j _ s
    exact phi_mono x A s

end Labels
end PEqualNP.Outside.L_lib_1316_aux

namespace PEqualNP.Outside.L_lib_1316_aux
section Witness
open scoped Classical
variable {n m : ℕ} (x : Fin m → Finset (Fin n)) (A : Fin m → Finset (Finset (Fin 2)))

theorem univ_of_mem_ne : ∀ (w : Finset (Fin 2)) (c : Fin 2), c ∈ w → w ≠ {c} → w = Finset.univ := by decide

theorem fin2_cover (b d : Fin 2) : d = b ∨ d = ot b := by fin_cases b <;> fin_cases d <;> simp [ot]

theorem card_fin2 (U : Finset (Fin 2)) : U.card ≤ 2 := by
  have := Finset.card_le_univ U
  simpa using this

theorem witness3 (ρ : ℕ) (D : Finset (Fin m)) (hB : ∀ i ∈ D, MC (A i))
    (hρ : 2 ≤ ρ ∨ (1 ≤ ρ ∧ ∃ c : Fin 2, ∀ i ∈ D, ({c} : Finset (Fin 2)) ∉ A i))
    (hnf : ¬ MonoFeas x A D) :
    ∃ G ⊆ D, G.card ≤ 3 ∧ ¬ MonoFeas x A G ∧ (∃ t ∈ G, ∀ q ∈ G, x q ⊆ x t) ∧
      ∃ R ⊆ G, R.card ≤ ρ ∧ ∀ q ∈ G, ∃ p ∈ R, x p ⊆ x q := by
  have hρ1 : 1 ≤ ρ := by rcases hρ with h | h; omega; exact h.1
  have hex : ∃ i ∈ D, Phi x A D i ∉ A i := by
    by_contra hall
    push_neg at hall
    exact hnf ⟨Phi x A D, hall, fun i _ j _ s => phi_mono x A s⟩
  obtain ⟨i, hiD, hPi⟩ := hex
  have hno : ¬ ∃ w ∈ A i, Phi x A D i ⊆ w := fun h => hPi (phi_closed x A hiD (hB i hiD) h)
  by_cases hα : ∃ b, Two x A D i b
  · obtain ⟨b, k, hk, j, hj, s1, s2, t1, t2⟩ := hα
    refine ⟨(insert k (insert j {i}) : Finset (Fin m)), ?_, ?_, ?_, ⟨i, by simp, ?_⟩, ({k} : Finset (Fin m)), by simp, by simp; omega, ?_⟩
    · intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl <;> assumption
    · exact (Finset.card_insert_le _ _).trans (by
        have := Finset.card_insert_le j ({i} : Finset (Fin m))
        simp at this ⊢
        omega)
    · rintro ⟨wd, hl, hm⟩
      have mk : k ∈ (insert k (insert j {i}) : Finset (Fin m)) := by simp
      have mj : j ∈ (insert k (insert j {i}) : Finset (Fin m)) := by simp
      have mi : i ∈ (insert k (insert j {i}) : Finset (Fin m)) := by simp
      have h1 : ot b ∈ wd k := t1 _ (hl k mk)
      have h2 : ot b ∈ wd j := hm k mk j mj s1 h1
      have h3 : b ∈ wd j := t2 _ (hl j mj) h2
      have h4 : b ∈ wd i := hm j mj i mi s2 h3
      have h5 : ot b ∈ wd i := hm j mj i mi s2 h2
      apply hno
      refine ⟨wd i, hl i mi, ?_⟩
      intro d _
      rcases fin2_cover b d with rfl | rfl
      · exact h4
      · exact h5
    · intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl
      · exact s1.trans s2
      · exact s2
      · exact Finset.Subset.refl _
    · intro q hq
      refine ⟨k, by simp, ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl
      · exact Finset.Subset.refl _
      · exact s1
      · exact s1.trans s2
  · have hOne : ∀ b ∈ Phi x A D i, ∃ j ∈ D, x j ⊆ x i ∧ Intr (A j) b := by
      intro b hb
      rw [mem_phi] at hb
      rcases hb with h | h
      · exact h
      · exact absurd ⟨b, h⟩ hα
    have single : ∀ j ∈ D, x j ⊆ x i → (∀ wd : Fin m → Finset (Fin 2), wd j ∈ A j → Phi x A D i ⊆ wd j) →
        ∃ G ⊆ D, G.card ≤ 3 ∧ ¬ MonoFeas x A G ∧ (∃ t ∈ G, ∀ q ∈ G, x q ⊆ x t) ∧
          ∃ R ⊆ G, R.card ≤ ρ ∧ ∀ q ∈ G, ∃ p ∈ R, x p ⊆ x q := by
      intro j hj sj hforce
      refine ⟨(insert j {i} : Finset (Fin m)), ?_, ?_, ?_, ⟨i, by simp, ?_⟩, ({j} : Finset (Fin m)), by simp, by simp; omega, ?_⟩
      · intro q hq
        simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl <;> assumption
      · exact (Finset.card_insert_le _ _).trans (by simp)
      · rintro ⟨wd, hl, hm⟩
        have mj : j ∈ (insert j {i} : Finset (Fin m)) := by simp
        have mi : i ∈ (insert j {i} : Finset (Fin m)) := by simp
        apply hno
        exact ⟨wd i, hl i mi, (hforce wd (hl j mj)).trans (hm j mj i mi sj)⟩
      · intro q hq
        simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl
        · exact sj
        · exact Finset.Subset.refl _
      · intro q hq
        refine ⟨j, by simp, ?_⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl
        · exact Finset.Subset.refl _
        · exact sj
    by_cases hP : Phi x A D i = ∅
    · apply single i hiD (Finset.Subset.refl _)
      intro wd _
      rw [hP]; exact Finset.empty_subset _
    rcases hρ with hρ2 | ⟨_, c, hc⟩
    · have : Nonempty (Fin m) := ⟨i⟩
      choose! jf hjfD hjfs hjfI using hOne
      let R := (Phi x A D i).image jf
      have hRD : R ⊆ D := by
        intro p hp
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hp
        exact hjfD b hb
      refine ⟨insert i R, ?_, ?_, ?_, ⟨i, by simp, ?_⟩, R, Finset.subset_insert _ _, ?_, ?_⟩
      · intro q hq
        rcases Finset.mem_insert.1 hq with rfl | hq
        · exact hiD
        · exact hRD hq
      · have h1 := Finset.card_insert_le i R
        have h2 : R.card ≤ (Phi x A D i).card := Finset.card_image_le
        have h3 := card_fin2 (Phi x A D i)
        omega
      · rintro ⟨wd, hl, hm⟩
        have mi : i ∈ insert i R := by simp
        apply hno
        refine ⟨wd i, hl i mi, ?_⟩
        intro b hb
        have mjb : jf b ∈ insert i R := Finset.mem_insert_of_mem (Finset.mem_image_of_mem jf hb)
        exact hm _ mjb i mi (hjfs b hb) (hjfI b hb _ (hl _ mjb))
      · intro q hq
        rcases Finset.mem_insert.1 hq with rfl | hq
        · exact Finset.Subset.refl _
        · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hq
          exact hjfs b hb
      · have h2 : R.card ≤ (Phi x A D i).card := Finset.card_image_le
        have h3 := card_fin2 (Phi x A D i)
        omega
      · intro q hq
        rcases Finset.mem_insert.1 hq with rfl | hq
        · obtain ⟨b, hb⟩ := Finset.nonempty_iff_ne_empty.2 hP
          exact ⟨jf b, Finset.mem_image_of_mem jf hb, hjfs b hb⟩
        · exact ⟨q, hq, Finset.Subset.refl _⟩
    · by_cases hcP : c ∈ Phi x A D i
      · obtain ⟨j, hj, sj, hI⟩ := hOne c hcP
        apply single j hj sj
        intro wd hwd
        have hcw : c ∈ wd j := hI _ hwd
        have hne : wd j ≠ {c} := fun e => hc j hj (e ▸ hwd)
        rw [univ_of_mem_ne _ c hcw hne]
        exact Finset.subset_univ _
      · obtain ⟨b, hb⟩ := Finset.nonempty_iff_ne_empty.2 hP
        obtain ⟨j, hj, sj, hI⟩ := hOne b hb
        apply single j hj sj
        intro wd hwd d hd
        have hdc : d ≠ c := fun e => hcP (e ▸ hd)
        have hbc : b ≠ c := fun e => hcP (e ▸ hb)
        have hdb : d = b := by
          have h1 : d.val ≠ c.val := fun e => hdc (Fin.ext e)
          have h2 : b.val ≠ c.val := fun e => hbc (Fin.ext e)
          have := b.isLt
          have := c.isLt
          have := d.isLt
          exact Fin.ext (by omega)
        rw [hdb]
        exact hI _ hwd

theorem feas_of_up_empty (r : ℕ) (P : Finset (Fin m)) (hB : ∀ i ∈ P, MC (A i))
    (h : Up x A P (2 ^ r) = ∅) : Feas x A r P := by
  have hpos : 1 ≤ 2 ^ r := Nat.one_le_two_pow
  have hex : ∀ i, ∃ ℓ, i ∉ Up x A P (ℓ + 1) := by
    intro i
    refine ⟨2 ^ r - 1, ?_⟩
    rw [show 2 ^ r - 1 + 1 = 2 ^ r by omega, h]
    exact Finset.notMem_empty i
  let lev : Fin m → ℕ := fun i => Nat.find (hex i)
  have hlt : ∀ i, lev i < 2 ^ r := by
    intro i
    have : lev i ≤ 2 ^ r - 1 := Nat.find_min' (hex i) (by
      rw [show 2 ^ r - 1 + 1 = 2 ^ r by omega, h]
      exact Finset.notMem_empty i)
    omega
  have hout : ∀ i, i ∉ Up x A P (lev i + 1) := fun i => Nat.find_spec (hex i)
  have hin : ∀ i ∈ P, i ∈ Up x A P (lev i) := by
    intro i hi
    cases hl : lev i with
    | zero => exact hi
    | succ k =>
      have hk : k < Nat.find (hex i) := by
        change k < lev i
        omega
      have := Nat.find_min (hex i) hk
      simpa using this
  have hchar : ∀ i ℓ, i ∈ Up x A P ℓ → ℓ ≤ lev i := by
    intro i ℓ hiu
    by_contra hc
    exact hout i (up_anti x A P (by omega) hiu)
  let Sl : ℕ → Finset (Fin m) := fun ℓ => (Up x A P ℓ).filter (fun i => i ∉ Up x A P (ℓ + 1))
  have hsl : ∀ ℓ, MonoFeas x A (Sl ℓ) := by
    intro ℓ
    apply locality x A
    · intro i hi
      exact hB i (up_sub x A P ℓ (Finset.mem_filter.1 hi).1)
    · intro i hi
      have hi' := Finset.mem_filter.1 hi
      have hmf : MonoFeas x A ((Up x A P ℓ).filter (fun j => x j ⊆ x i)) := by
        by_contra hc
        exact hi'.2 (mem_up_succ x A |>.2 ⟨hi'.1, hc⟩)
      apply monoFeas_mono x A _ hmf
      intro q hq
      simp only [Sl, Finset.mem_filter] at hq ⊢
      exact ⟨hq.1.1, hq.2⟩
  choose wdf hwdl hwdm using hsl
  have hsli : ∀ i ∈ P, i ∈ Sl (lev i) := fun i hi => Finset.mem_filter.2 ⟨hin i hi, hout i⟩
  refine ⟨lev, fun i => wdf (lev i) i, ?_, ?_⟩
  · intro i hi
    exact ⟨hwdl _ i (hsli i hi), hlt i⟩
  · intro i hi j hj sub
    have hj' : j ∈ Up x A P (lev i) := up_upward x A P _ i (hin i hi) j hj sub
    have hle := hchar j _ hj'
    refine ⟨hle, fun eq => ?_⟩
    have hjs : j ∈ Sl (lev i) := by rw [eq]; exact hsli j hj
    have := hwdm (lev i) i (hsli i hi) j hjs sub
    simp only
    rw [← eq]
    exact this

def T (ρ : ℕ) : ℕ → ℕ
  | 0 => 0
  | ℓ + 1 => 3 + ρ * T ρ ℓ

theorem T_two (L : ℕ) : T 2 L = 3 * (2 ^ L - 1) := by
  induction L with
  | zero => simp [T]
  | succ L ih =>
    simp only [T, ih, pow_succ]
    have := Nat.one_le_two_pow (n := L)
    have h : 2 ^ L * 2 = 2 * 2 ^ L := by ring
    omega

theorem T_one (L : ℕ) : T 1 L = 3 * L := by
  induction L with
  | zero => simp [T]
  | succ L ih => simp only [T, ih]; ring

theorem step_build (ρ : ℕ) (P : Finset (Fin m)) (hB : ∀ i ∈ P, MC (A i))
    (hρ : 2 ≤ ρ ∨ (1 ≤ ρ ∧ ∃ c : Fin 2, ∀ i ∈ P, ({c} : Finset (Fin 2)) ∉ A i))
    (ℓ : ℕ) (IH : ∀ p ∈ Up x A P ℓ, ∃ W ⊆ P, p ∈ Up x A (insert p W) ℓ ∧ W.card ≤ T ρ ℓ)
    (i : Fin m) (hi : i ∈ Up x A P (ℓ + 1)) :
    ∃ W ⊆ P, W.card ≤ T ρ (ℓ + 1) ∧ ∃ G ⊆ W, ¬ MonoFeas x A G ∧ (∀ q ∈ G, x q ⊆ x i) ∧
      (∃ t ∈ G, ∀ q ∈ G, x q ⊆ x t) ∧ ∀ Q, W ⊆ Q → ∀ q ∈ G, q ∈ Up x A Q ℓ := by
  rw [mem_up_succ] at hi
  obtain ⟨_, hnf⟩ := hi
  set D := (Up x A P ℓ).filter (fun j => x j ⊆ x i) with hD
  have hDP : D ⊆ P := fun q hq => up_sub x A P ℓ (Finset.mem_filter.1 hq).1
  have hρD : 2 ≤ ρ ∨ (1 ≤ ρ ∧ ∃ c : Fin 2, ∀ i ∈ D, ({c} : Finset (Fin 2)) ∉ A i) := by
    rcases hρ with h | ⟨h1, c, hc⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, c, fun i hi => hc i (hDP hi)⟩
  obtain ⟨G, hGD, hGc, hGnf, ⟨t, ht, htop⟩, R, hRG, hRc, hcov⟩ :=
    witness3 x A ρ D (fun q hq => hB q (hDP hq)) hρD hnf
  have hRup : ∀ p ∈ R, p ∈ Up x A P ℓ := fun p hp => (Finset.mem_filter.1 (hGD (hRG hp))).1
  have IH' : ∀ p, ∃ W, p ∈ R → W ⊆ P ∧ p ∈ Up x A (insert p W) ℓ ∧ W.card ≤ T ρ ℓ := by
    intro p
    by_cases hp : p ∈ R
    · obtain ⟨W, hW, h1, h2⟩ := IH p (hRup p hp)
      exact ⟨W, fun _ => ⟨hW, h1, h2⟩⟩
    · exact ⟨∅, fun h => absurd h hp⟩
  choose Wf hWf using IH'
  let W := G ∪ R.biUnion Wf
  refine ⟨W, ?_, ?_, G, Finset.subset_union_left, hGnf, ?_, ⟨t, ht, htop⟩, ?_⟩
  · intro q hq
    rcases Finset.mem_union.1 hq with hq | hq
    · exact hDP (hGD hq)
    · obtain ⟨p, hp, hqp⟩ := Finset.mem_biUnion.1 hq
      exact (hWf p hp).1 hqp
  · have h1 := Finset.card_union_le G (R.biUnion Wf)
    have h2 : (R.biUnion Wf).card ≤ ∑ p ∈ R, (Wf p).card := Finset.card_biUnion_le
    have h3 : ∑ p ∈ R, (Wf p).card ≤ R.card * T ρ ℓ := by
      have := Finset.sum_le_card_nsmul R (fun p => (Wf p).card) (T ρ ℓ) (fun p hp => (hWf p hp).2.2)
      simpa using this
    have h4 : R.card * T ρ ℓ ≤ ρ * T ρ ℓ := Nat.mul_le_mul_right _ hRc
    have h5 : T ρ (ℓ + 1) = 3 + ρ * T ρ ℓ := rfl
    rw [h5]
    show (G ∪ R.biUnion Wf).card ≤ 3 + ρ * T ρ ℓ
    omega
  · intro q hq
    exact (Finset.mem_filter.1 (hGD hq)).2
  · intro Q hWQ q hq
    obtain ⟨p, hpR, hpq⟩ := hcov q hq
    have hsub : insert p (Wf p) ⊆ Q := by
      intro z hz
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact hWQ (Finset.mem_union_left _ (hRG hpR))
      · exact hWQ (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨p, hpR, hz⟩))
    have hpQ := up_monoP x A hsub ℓ (hWf p hpR).2.1
    exact up_upward x A Q ℓ p hpQ q (hWQ (Finset.mem_union_left _ hq)) hpq

theorem monoFeas_empty : MonoFeas x A ∅ := ⟨fun _ => ∅, by simp, by simp⟩

theorem up_witness (ρ : ℕ) (P : Finset (Fin m)) (hB : ∀ i ∈ P, MC (A i))
    (hρ : 2 ≤ ρ ∨ (1 ≤ ρ ∧ ∃ c : Fin 2, ∀ i ∈ P, ({c} : Finset (Fin 2)) ∉ A i)) :
    ∀ ℓ, ∀ p ∈ Up x A P ℓ, ∃ W ⊆ P, p ∈ Up x A (insert p W) ℓ ∧ W.card ≤ T ρ ℓ := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro p _
    exact ⟨∅, Finset.empty_subset _, by simp [Up], by simp [T]⟩
  | succ k ih =>
    intro p hp
    obtain ⟨W, hWP, hWc, G, hGW, hGnf, hGp, _, hGup⟩ := step_build x A ρ P hB hρ k ih p hp
    refine ⟨W, hWP, ?_, hWc⟩
    have hGne : G.Nonempty := by
      by_contra hc
      rw [Finset.not_nonempty_iff_eq_empty] at hc
      exact hGnf (hc ▸ monoFeas_empty x A)
    obtain ⟨q, hq⟩ := hGne
    have hQ : W ⊆ insert p W := Finset.subset_insert _ _
    rw [mem_up_succ]
    refine ⟨up_upward x A _ k q (hGup _ hQ q hq) p (Finset.mem_insert_self _ _) (hGp q hq), ?_⟩
    intro hmf
    apply hGnf
    apply monoFeas_mono x A _ hmf
    intro z hz
    exact Finset.mem_filter.2 ⟨hGup _ hQ z hz, hGp z hz⟩

theorem bound (ρ r : ℕ) (hB : ∀ i, MC (A i))
    (hρ : 2 ≤ ρ ∨ (1 ≤ ρ ∧ ∃ c : Fin 2, ∀ i, ({c} : Finset (Fin 2)) ∉ A i))
    (h : ∀ S : Finset (Fin m), S.card ≤ T ρ (2 ^ r) → Feas x A r S) : Feas x A r Finset.univ := by
  by_contra hnf
  have hne : (Up x A Finset.univ (2 ^ r)).Nonempty := by
    by_contra hc
    rw [Finset.not_nonempty_iff_eq_empty] at hc
    exact hnf (feas_of_up_empty x A r _ (fun i _ => hB i) hc)
  have hpos : 1 ≤ 2 ^ r := Nat.one_le_two_pow
  have hρ' : 2 ≤ ρ ∨ (1 ≤ ρ ∧ ∃ c : Fin 2, ∀ i ∈ (Finset.univ : Finset (Fin m)), ({c} : Finset (Fin 2)) ∉ A i) := by
    rcases hρ with h | ⟨h1, c, hc⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, c, fun i _ => hc i⟩
  obtain ⟨i, hi⟩ := hne
  rw [show 2 ^ r = (2 ^ r - 1) + 1 by omega] at hi
  obtain ⟨W, _, hWc, G, hGW, hGnf, _, ⟨t, ht, htop⟩, hGup⟩ :=
    step_build x A ρ _ (fun i _ => hB i) hρ' _ (up_witness x A ρ _ (fun i _ => hB i) hρ' _) i hi
  apply not_feas_of_up x A r W _ (h W (by rw [show 2 ^ r = (2 ^ r - 1) + 1 by omega]; exact hWc))
  refine ⟨t, ?_⟩
  rw [show 2 ^ r = (2 ^ r - 1) + 1 by omega, mem_up_succ]
  refine ⟨hGup W (Finset.Subset.refl _) t ht, ?_⟩
  intro hmf
  apply hGnf
  apply monoFeas_mono x A _ hmf
  intro z hz
  exact Finset.mem_filter.2 ⟨hGup W (Finset.Subset.refl _) z hz, htop z hz⟩

end Witness
end PEqualNP.Outside.L_lib_1316_aux

namespace PEqualNP.Outside.L_lib_1316_aux
section Dual
open scoped Classical
variable {n m : ℕ}

theorem feas_dual (x : Fin m → Finset (Fin n)) (A : Fin m → Finset (Finset (Fin 2))) (r : ℕ) (S : Finset (Fin m))
    (h : Feas x A r S) : Feas (fun i => (x i)ᶜ) (fun i => (A i).image (fun w => wᶜ)) r S := by
  obtain ⟨lev, wd, hv, ho⟩ := h
  have hpos : 1 ≤ 2 ^ r := Nat.one_le_two_pow
  refine ⟨fun i => 2 ^ r - 1 - lev i, fun i => (wd i)ᶜ, ?_, ?_⟩
  · intro i hi
    have := (hv i hi).2
    exact ⟨Finset.mem_image_of_mem _ (hv i hi).1, by show 2 ^ r - 1 - lev i < 2 ^ r; omega⟩
  · intro i hi j hj sub
    have sub' : x j ⊆ x i := Finset.compl_subset_compl.1 sub
    have hji := ho j hj i hi sub'
    have h1 := (hv i hi).2
    have h2 := (hv j hj).2
    refine ⟨by simp only; omega, fun eq => ?_⟩
    have e : lev j = lev i := by simp only at eq; omega
    exact Finset.compl_subset_compl.2 (hji.2 e)

theorem feas_dual2 (x : Fin m → Finset (Fin n)) (A : Fin m → Finset (Finset (Fin 2))) (r : ℕ) (S : Finset (Fin m))
    (h : Feas (fun i => (x i)ᶜ) (fun i => (A i).image (fun w => wᶜ)) r S) : Feas x A r S := by
  have := feas_dual _ _ r S h
  have e1 : (fun i => ((fun i => (x i)ᶜ) i)ᶜ) = x := by funext i; simp
  have e2 : (fun i => ((fun i => (A i).image (fun w : Finset (Fin 2) => wᶜ)) i).image (fun w : Finset (Fin 2) => wᶜ)) = A := by
    funext i
    simp only [Finset.image_image]
    have : ((fun w : Finset (Fin 2) => wᶜ) ∘ fun w => wᶜ) = id := by funext w; simp
    rw [this, Finset.image_id]
  rw [e1, e2] at this
  exact this

def phiC (c : Fin 2) (w : Finset (Fin 2)) : Finset (Fin 2) := if w = {c} then {ot c} else w

theorem phiC_mono : ∀ (c : Fin 2) (u v : Finset (Fin 2)), u ⊆ v → phiC c u ⊆ phiC c v := by
  unfold phiC ot; decide

theorem chain_inter : ∀ (c : Fin 2) (u v : Finset (Fin 2)), u ≠ {c} → v ≠ {c} → u ∩ v = u ∨ u ∩ v = v := by decide

theorem feas_fold (c : Fin 2) (x : Fin m → Finset (Fin n)) (A : Fin m → Finset (Finset (Fin 2))) (r : ℕ)
    (S : Finset (Fin m)) (hA : ∀ i, {c} ∈ A i → {ot c} ∈ A i) (h : Feas x A r S) :
    Feas x (fun i => (A i).erase {c}) r S := by
  obtain ⟨lev, wd, hv, ho⟩ := h
  refine ⟨lev, fun i => phiC c (wd i), ?_, ?_⟩
  · intro i hi
    refine ⟨?_, (hv i hi).2⟩
    have hw := (hv i hi).1
    simp only [phiC]
    split_ifs with he
    · rw [he] at hw
      refine Finset.mem_erase.2 ⟨?_, hA i hw⟩
      intro e
      have := congrArg (fun s : Finset (Fin 2) => c ∈ s) e
      simp at this
      exact ot_ne c (this.symm)
    · exact Finset.mem_erase.2 ⟨he, hw⟩
  · intro i hi j hj sub
    have := ho i hi j hj sub
    exact ⟨this.1, fun e => phiC_mono c _ _ (this.2 e)⟩

theorem feas_unfold (c : Fin 2) (x : Fin m → Finset (Fin n)) (A : Fin m → Finset (Finset (Fin 2))) (r : ℕ)
    (S : Finset (Fin m)) (h : Feas x (fun i => (A i).erase {c}) r S) : Feas x A r S := by
  obtain ⟨lev, wd, hv, ho⟩ := h
  exact ⟨lev, wd, fun i hi => ⟨Finset.mem_of_mem_erase (hv i hi).1, (hv i hi).2⟩, ho⟩

theorem erase_mc (c : Fin 2) (B : Finset (Finset (Fin 2))) : MC (B.erase {c}) := by
  intro u hu v hv
  have hu' := Finset.mem_erase.1 hu
  have hv' := Finset.mem_erase.1 hv
  rcases chain_inter c u v hu'.1 hv'.1 with e | e
  · rw [e]; exact hu
  · rw [e]; exact hv

theorem dual_mc (B : Finset (Finset (Fin 2))) (hB : ∀ u ∈ B, ∀ v ∈ B, u ∪ v ∈ B) :
    MC (B.image (fun w => wᶜ)) := by
  intro u hu v hv
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hu
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hv
  have : aᶜ ∩ bᶜ = (a ∪ b)ᶜ := by rw [Finset.compl_union]
  rw [this]
  exact Finset.mem_image_of_mem _ (hB a ha b hb)

end Dual

section Obstruction
open scoped Classical

def locP (N k z : ℕ) : Prop :=
  (k < N ∧ z = 2 * k) ∨
  (N ≤ k ∧ k + 1 < 2 * N ∧ (z = 2 * (k - N) ∨ z = 2 * (k - N) + 1 ∨ z = 2 * (k - N) + 2)) ∨
  (k = 2 * N - 1 ∧ (z = 0 ∨ z = 1)) ∨
  (k = 2 * N ∧ (z = 2 * N - 3 ∨ z = 2 * N - 2))

def RightP (N j k : ℕ) : Prop := (k < N ∧ j < k) ∨ (N ≤ k ∧ k + 1 < 2 * N ∧ j ≤ k - N) ∨ k = 2 * N

theorem locP_last (N k : ℕ) (hN : 3 ≤ N) : ¬ locP N k (2 * N - 1) := by unfold locP; omega

theorem side_eq (N j k k' : ℕ) (hN : 3 ≤ N) (hj1 : 1 ≤ j) (hj2 : j + 2 ≤ N) (hk : k ≤ 2 * N) (hk' : k' ≤ 2 * N)
    (hkj : k ≠ j) (hk'j : k' ≠ j) (h : ∀ z, locP N k z → locP N k' z) : (RightP N j k ↔ RightP N j k') := by
  unfold RightP
  rcases (show k < N ∨ (N ≤ k ∧ k + 1 < 2 * N) ∨ k = 2 * N - 1 ∨ k = 2 * N by omega) with hk1 | hk1 | hk1 | hk1
  · have h0 := h (2 * k) (by unfold locP; omega)
    unfold locP at h0
    constructor <;> intro _ <;> omega
  · have h1 := h (2 * (k - N) + 1) (by unfold locP; omega)
    have h2 := h (2 * (k - N) + 2) (by unfold locP; omega)
    have h3 := h (2 * (k - N)) (by unfold locP; omega)
    unfold locP at h1 h2 h3
    constructor <;> intro _ <;> omega
  · have h1 := h 1 (by unfold locP; omega)
    have h0 := h 0 (by unfold locP; omega)
    unfold locP at h1 h0
    constructor <;> intro _ <;> omega
  · have h1 := h (2 * N - 3) (by unfold locP; omega)
    have h2 := h (2 * N - 2) (by unfold locP; omega)
    unfold locP at h1 h2
    constructor <;> intro _ <;> omega

theorem loc_inj (N k k' : ℕ) (hN : 3 ≤ N) (hk : k ≤ 2 * N) (hk' : k' ≤ 2 * N)
    (h : ∀ z, locP N k z → locP N k' z) (h' : ∀ z, locP N k' z → locP N k z) : k = k' := by
  rcases (show k < N ∨ (N ≤ k ∧ k + 1 < 2 * N) ∨ k = 2 * N - 1 ∨ k = 2 * N by omega) with hk1 | hk1 | hk1 | hk1
  · have h0 := h (2 * k) (by unfold locP; omega)
    rcases (show k' < N ∨ (N ≤ k' ∧ k' + 1 < 2 * N) ∨ k' = 2 * N - 1 ∨ k' = 2 * N by omega) with hk2 | hk2 | hk2 | hk2
    · unfold locP at h0; omega
    · have h1 := h' (2 * (k' - N) + 1) (by unfold locP; omega)
      unfold locP at h1; omega
    · have h1 := h' 1 (by unfold locP; omega)
      unfold locP at h1; omega
    · have h1 := h' (2 * N - 3) (by unfold locP; omega)
      unfold locP at h1; omega
  · have h1 := h (2 * (k - N) + 1) (by unfold locP; omega)
    have h2 := h (2 * (k - N) + 2) (by unfold locP; omega)
    have h3 := h (2 * (k - N)) (by unfold locP; omega)
    unfold locP at h1 h2 h3
    omega
  · have h1 := h 1 (by unfold locP; omega)
    have h0 := h 0 (by unfold locP; omega)
    rcases (show k' < N ∨ (N ≤ k' ∧ k' + 1 < 2 * N) ∨ k' = 2 * N - 1 ∨ k' = 2 * N by omega) with hk2 | hk2 | hk2 | hk2
    · unfold locP at h1 h0; omega
    · have g1 := h' (2 * (k' - N) + 1) (by unfold locP; omega)
      have g2 := h' (2 * (k' - N) + 2) (by unfold locP; omega)
      unfold locP at g1 g2; omega
    · omega
    · unfold locP at h1; omega
  · have h1 := h (2 * N - 3) (by unfold locP; omega)
    have h2 := h (2 * N - 2) (by unfold locP; omega)
    rcases (show k' < N ∨ (N ≤ k' ∧ k' + 1 < 2 * N) ∨ k' = 2 * N - 1 ∨ k' = 2 * N by omega) with hk2 | hk2 | hk2 | hk2
    · unfold locP at h1; omega
    · have g1 := h' (2 * (k' - N)) (by unfold locP; omega)
      have g2 := h' (2 * (k' - N) + 1) (by unfold locP; omega)
      unfold locP at g1 g2; omega
    · unfold locP at h1; omega
    · omega

end Obstruction
end PEqualNP.Outside.L_lib_1316_aux

namespace PEqualNP.Outside.L_lib_1316_aux
section Obs2
open scoped Classical
variable (N T : ℕ)

noncomputable def oxP (a : Fin T × Fin (2 * N + 1)) : Finset (Fin T × Fin (2 * N)) :=
  Finset.univ.filter (fun c => c.1 < a.1 ∨ (c.1 = a.1 ∧ locP N a.2.val c.2.val))

theorem oxP_sub (hN : 3 ≤ N) (a b : Fin T × Fin (2 * N + 1)) :
    oxP N T a ⊆ oxP N T b ↔ a.1 < b.1 ∨ (a.1 = b.1 ∧ ∀ z, locP N a.2.val z → locP N b.2.val z) := by
  constructor
  · intro hs
    rcases lt_trichotomy a.1 b.1 with h | h | h
    · exact Or.inl h
    · right
      refine ⟨h, fun z hz => ?_⟩
      have hzB : z < 2 * N := by unfold locP at hz; have := a.2.isLt; omega
      have hc : ((a.1, ⟨z, hzB⟩) : Fin T × Fin (2 * N)) ∈ oxP N T a :=
        Finset.mem_filter.2 ⟨Finset.mem_univ _, Or.inr ⟨rfl, hz⟩⟩
      have := (Finset.mem_filter.1 (hs hc)).2
      rcases this with h1 | ⟨_, h2⟩
      · exact absurd (lt_of_lt_of_eq h1 h.symm) (lt_irrefl _)
      · exact h2
    · exfalso
      have hz : 2 * N - 1 < 2 * N := by omega
      have hc : ((b.1, ⟨2 * N - 1, hz⟩) : Fin T × Fin (2 * N)) ∈ oxP N T a :=
        Finset.mem_filter.2 ⟨Finset.mem_univ _, Or.inl h⟩
      have := (Finset.mem_filter.1 (hs hc)).2
      rcases this with h1 | ⟨_, h2⟩
      · exact lt_irrefl _ h1
      · exact locP_last N _ hN h2
  · rintro (h | ⟨h, hl⟩) c hc
    · have hc' := (Finset.mem_filter.1 hc).2
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      rcases hc' with h1 | ⟨h1, _⟩
      · exact Or.inl (h1.trans h)
      · exact Or.inl (lt_of_eq_of_lt h1 h)
    · have hc' := (Finset.mem_filter.1 hc).2
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      rcases hc' with h1 | ⟨h1, h2⟩
      · exact Or.inl (lt_of_lt_of_eq h1 h)
      · exact Or.inr ⟨h1.trans h, hl _ h2⟩

noncomputable def ox (p : Fin (T * (2 * N + 1))) : Finset (Fin (T * (2 * N))) :=
  (oxP N T (finProdFinEquiv.symm p)).map finProdFinEquiv.toEmbedding

theorem ox_sub (hN : 3 ≤ N) (p q : Fin (T * (2 * N + 1))) :
    ox N T p ⊆ ox N T q ↔ oxP N T (finProdFinEquiv.symm p) ⊆ oxP N T (finProdFinEquiv.symm q) := by
  unfold ox
  exact Finset.map_subset_map

def listOf (Aa Ab A1 A2 : Finset (Finset (Fin 2))) (k : ℕ) : Finset (Finset (Fin 2)) :=
  if k < N then Aa else if k + 1 < 2 * N then Ab else if k = 2 * N - 1 then A1 else A2

noncomputable def oA (Aa Ab A1 A2 : Finset (Finset (Fin 2))) (p : Fin (T * (2 * N + 1))) : Finset (Finset (Fin 2)) :=
  listOf N Aa Ab A1 A2 (finProdFinEquiv.symm p).2.val

theorem fin_eq_two : ∀ u v : Finset (Fin 2), u ≠ ∅ → v ≠ Finset.univ → u ⊆ v → u = v := by decide
theorem fin_mixed : ∀ u : Finset (Fin 2), u ≠ ∅ → u ≠ Finset.univ → u = {0} ∨ u = {1} := by decide

theorem ox_inj (hN : 3 ≤ N) : Function.Injective (ox N T) := by
  intro p q hpq
  have h1 := (ox_sub N T hN p q).1 (hpq ▸ Finset.Subset.refl _)
  have h2 := (ox_sub N T hN q p).1 (hpq ▸ Finset.Subset.refl _)
  rw [oxP_sub N T hN] at h1 h2
  have key : finProdFinEquiv.symm p = finProdFinEquiv.symm q := by
    rcases h1 with h1 | ⟨e1, l1⟩
    · rcases h2 with h2 | ⟨e2, _⟩
      · exact absurd (h1.trans h2) (lt_irrefl _)
      · exact absurd (e2 ▸ h1) (lt_irrefl _)
    · rcases h2 with h2 | ⟨_, l2⟩
      · exact absurd (e1 ▸ h2) (lt_irrefl _)
      · have hk := loc_inj N _ _ hN (by have := (finProdFinEquiv.symm p).2.isLt; omega)
          (by have := (finProdFinEquiv.symm q).2.isLt; omega) l1 l2
        exact Prod.ext e1 (Fin.ext hk)
  exact finProdFinEquiv.symm.injective key

theorem obs_infeas (hN : 3 ≤ N) (r : ℕ) (hT : T = 2 ^ r) (Aa Ab A1 A2 : Finset (Finset (Fin 2)))
    (hAae : ∅ ∉ Aa) (hAbu : Finset.univ ∉ Ab) (hA11 : {1} ∉ A1) (hA20 : {0} ∉ A2) :
    ¬ Feas (ox N T) (oA N T Aa Ab A1 A2) r Finset.univ := by
  rintro ⟨lev, wd, hv, ho⟩
  let e : Fin T × Fin (2 * N + 1) ≃ Fin (T * (2 * N + 1)) := finProdFinEquiv
  have hord : ∀ a b : Fin T × Fin (2 * N + 1), oxP N T a ⊆ oxP N T b →
      lev (e a) ≤ lev (e b) ∧ (lev (e a) = lev (e b) → wd (e a) ⊆ wd (e b)) := by
    intro a b hab
    apply ho _ (Finset.mem_univ _) _ (Finset.mem_univ _)
    rw [ox_sub N T hN]
    simpa [e] using hab
  have hlist : ∀ a : Fin T × Fin (2 * N + 1), wd (e a) ∈ listOf N Aa Ab A1 A2 a.2.val := by
    intro a
    have := (hv (e a) (Finset.mem_univ _)).1
    simpa [oA, e] using this
  have hlt : ∀ a : Fin T × Fin (2 * N + 1), lev (e a) < T := by
    intro a
    exact lt_of_lt_of_eq (hv (e a) (Finset.mem_univ _)).2 hT.symm
  have hT1 : 1 ≤ T := by rw [hT]; exact Nat.one_le_two_pow
  have color : ∀ t (ht : t < T), (∀ k : Fin (2 * N + 1), lev (e (⟨t, ht⟩, k)) = t) → False := by
    intro t ht hall
    let pt : ℕ → Fin T × Fin (2 * N + 1) := fun k => (⟨t, ht⟩, ⟨k % (2 * N + 1), Nat.mod_lt _ (by omega)⟩)
    have hpt : ∀ k, k < 2 * N + 1 → (pt k).2.val = k := fun k hk => Nat.mod_eq_of_lt hk
    have wsub : ∀ k k', k < 2 * N + 1 → k' < 2 * N + 1 → (∀ z, locP N k z → locP N k' z) →
        wd (e (pt k)) ⊆ wd (e (pt k')) := by
      intro k k' hk hk' hl
      apply (hord (pt k) (pt k') ((oxP_sub N T hN _ _).2 (Or.inr ⟨rfl, ?_⟩))).2
      · rw [hall, hall]
      · rw [hpt k hk, hpt k' hk']; exact hl
    have wl : ∀ k, k < 2 * N + 1 → wd (e (pt k)) ∈ listOf N Aa Ab A1 A2 k := by
      intro k hk; have := hlist (pt k); rwa [hpt k hk] at this
    have lowL : ∀ i, i < N → wd (e (pt i)) ∈ Aa := by
      intro i hi
      have := wl i (by omega)
      simpa [listOf, hi] using this
    have highL : ∀ i, i + 2 ≤ N → wd (e (pt (N + i))) ∈ Ab := by
      intro i hi
      have := wl (N + i) (by omega)
      simpa [listOf, show ¬ (N + i < N) by omega, show N + i + 1 < 2 * N by omega] using this
    have cLL : wd (e (pt (2 * N - 1))) ∈ A1 := by
      have := wl (2 * N - 1) (by omega)
      simpa [listOf, show ¬ (2 * N - 1 < N) by omega, show ¬ (2 * N - 1 + 1 < 2 * N) by omega] using this
    have cRL : wd (e (pt (2 * N))) ∈ A2 := by
      have := wl (2 * N) (by omega)
      simpa [listOf, show ¬ (2 * N < N) by omega, show ¬ (2 * N + 1 < 2 * N) by omega,
        show ¬ (2 * N = 2 * N - 1) by omega] using this
    have WV : ∀ i, i + 2 ≤ N → wd (e (pt i)) = wd (e (pt (N + i))) ∧ wd (e (pt (i + 1))) = wd (e (pt (N + i))) := by
      intro i hi
      have hne1 : wd (e (pt i)) ≠ ∅ := fun h => hAae (h ▸ lowL i (by omega))
      have hne2 : wd (e (pt (i + 1))) ≠ ∅ := fun h => hAae (h ▸ lowL (i + 1) (by omega))
      have hnu : wd (e (pt (N + i))) ≠ Finset.univ := fun h => hAbu (h ▸ highL i hi)
      refine ⟨fin_eq_two _ _ hne1 hnu (wsub _ _ (by omega) (by omega) ?_),
        fin_eq_two _ _ hne2 hnu (wsub _ _ (by omega) (by omega) ?_)⟩
      · intro z hz; unfold locP at hz ⊢; omega
      · intro z hz; unfold locP at hz ⊢; omega
    have W0 : ∀ i, i < N → wd (e (pt i)) = wd (e (pt 0)) := by
      intro i
      induction i with
      | zero => intro _; rfl
      | succ i ih =>
        intro hi
        have := WV i (by omega)
        rw [this.2, ← this.1]
        exact ih (by omega)
    have hcL : wd (e (pt (2 * N - 1))) = wd (e (pt 0)) := by
      apply Finset.Subset.antisymm
      · have h1 : wd (e (pt (2 * N - 1))) ⊆ wd (e (pt (N + 0))) :=
          wsub _ _ (by omega) (by omega) (by intro z hz; unfold locP at hz ⊢; omega)
        rw [← (WV 0 (by omega)).1] at h1
        exact h1
      · exact wsub _ _ (by omega) (by omega) (by intro z hz; unfold locP at hz ⊢; omega)
    have hcR : wd (e (pt (2 * N))) = wd (e (pt 0)) := by
      apply Finset.Subset.antisymm
      · have h1 : wd (e (pt (2 * N))) ⊆ wd (e (pt (N + (N - 2)))) :=
          wsub _ _ (by omega) (by omega) (by intro z hz; unfold locP at hz ⊢; omega)
        rw [← (WV (N - 2) (by omega)).1, W0 (N - 2) (by omega)] at h1
        exact h1
      · have h1 : wd (e (pt (N - 1))) ⊆ wd (e (pt (2 * N))) :=
          wsub _ _ (by omega) (by omega) (by intro z hz; unfold locP at hz ⊢; omega)
        rw [W0 (N - 1) (by omega)] at h1
        exact h1
    have hne : wd (e (pt 0)) ≠ ∅ := fun h => hAae (h ▸ lowL 0 (by omega))
    have hnu : wd (e (pt 0)) ≠ Finset.univ := by
      rw [(WV 0 (by omega)).1]
      exact fun h => hAbu (h ▸ highL 0 (by omega))
    rcases fin_mixed _ hne hnu with h0 | h1
    · apply hA20
      have := cRL
      rw [hcR, h0] at this
      exact this
    · apply hA11
      have := cLL
      rw [hcL, h1] at this
      exact this
  have claim : ∀ t (ht : t < T), ∃ k : Fin (2 * N + 1), t + 1 ≤ lev (e (⟨t, ht⟩, k)) := by
    intro t
    induction t with
    | zero =>
      intro ht
      by_contra hall
      push Not at hall
      exact color 0 ht (fun k => by have := hall k; omega)
    | succ s ih =>
      intro ht
      have hs' : s < T := by omega
      obtain ⟨k0, hk0⟩ := ih hs'
      by_contra hall
      push Not at hall
      apply color (s + 1) ht
      intro k
      have hle := (hord (⟨s, hs'⟩, k0) (⟨s + 1, ht⟩, k) ((oxP_sub N T hN _ _).2
        (Or.inl (Fin.mk_lt_mk.2 (Nat.lt_succ_self s))))).1
      have := hall k
      omega
  obtain ⟨k, hk⟩ := claim (T - 1) (by omega)
  have := hlt (⟨T - 1, by omega⟩, k)
  omega

theorem obs_small (hN : 3 ≤ N) (r : ℕ) (hT : T = 2 ^ r) (Aa Ab A1 A2 : Finset (Finset (Fin 2)))
    (hAa0 : {0} ∈ Aa) (hAa1 : {1} ∈ Aa) (hAb0 : {0} ∈ Ab) (hAb1 : {1} ∈ Ab)
    (hA10 : {0} ∈ A1) (hA21 : {1} ∈ A2) (S : Finset (Fin (T * (2 * N + 1)))) (hS : S.card + 3 ≤ N) :
    Feas (ox N T) (oA N T Aa Ab A1 A2) r S := by
  let e : Fin T × Fin (2 * N + 1) ≃ Fin (T * (2 * N + 1)) := finProdFinEquiv
  have hgap : ∀ t : Fin T, ∃ j, 1 ≤ j ∧ j + 2 ≤ N ∧ ∀ hj : j < 2 * N + 1, e (t, ⟨j, hj⟩) ∉ S := by
    intro t
    by_contra hall
    push Not at hall
    let f : ℕ → Fin (T * (2 * N + 1)) := fun j => e (t, ⟨j % (2 * N + 1), Nat.mod_lt _ (by omega)⟩)
    have hsub : (Finset.Icc 1 (N - 2)).image f ⊆ S := by
      intro p hp
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hp
      rw [Finset.mem_Icc] at hj
      obtain ⟨hj', hm⟩ := hall j hj.1 (by omega)
      have hmod : j % (2 * N + 1) = j := Nat.mod_eq_of_lt hj'
      have : f j = e (t, ⟨j, hj'⟩) := by
        simp only [f]
        congr 2
        exact Fin.ext hmod
      rw [this]; exact hm
    have hinj : Set.InjOn f (Finset.Icc 1 (N - 2) : Set ℕ) := by
      intro a ha b hb hab
      simp only [Finset.coe_Icc, Set.mem_Icc] at ha hb
      have := congrArg (fun p => (e.symm p).2.val) hab
      simp only [f, Equiv.symm_apply_apply] at this
      rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    have hc := Finset.card_le_card hsub
    rw [Finset.card_image_of_injOn hinj] at hc
    simp at hc
    omega
  choose gap hg1 hg2 hg3 using hgap
  have hnot : ∀ s ∈ S, (e.symm s).2.val ≠ gap (e.symm s).1 := by
    intro s hs hk
    have hlt' : gap (e.symm s).1 < 2 * N + 1 := hk ▸ (e.symm s).2.isLt
    apply hg3 (e.symm s).1 hlt'
    have : ((e.symm s).1, (⟨gap (e.symm s).1, hlt'⟩ : Fin (2 * N + 1))) = e.symm s :=
      Prod.ext rfl (Fin.ext hk.symm)
    rw [this, Equiv.apply_symm_apply]; exact hs
  refine ⟨fun p => (e.symm p).1.val,
    fun p => if RightP N (gap (e.symm p).1) (e.symm p).2.val then {1} else {0}, ?_, ?_⟩
  · intro p _
    refine ⟨?_, lt_of_lt_of_eq (e.symm p).1.isLt hT⟩
    have hk := (e.symm p).2.isLt
    have hj1 := hg1 (e.symm p).1
    have hj2 := hg2 (e.symm p).1
    simp only [oA]
    change _ ∈ listOf N Aa Ab A1 A2 (e.symm p).2.val
    unfold listOf
    split_ifs with h1 h2 h3 h4 h5 h6 h7 h8
    all_goals first
      | assumption
      | (exfalso; unfold RightP at *; omega)
  · intro p hp q hq sub
    rw [ox_sub N T hN, oxP_sub N T hN] at sub
    rcases sub with h | ⟨h, hl⟩
    · have h' : (e.symm p).1.val < (e.symm q).1.val := h
      exact ⟨le_of_lt h', fun eq => absurd eq (ne_of_lt h')⟩
    · refine ⟨le_of_eq (congrArg Fin.val h), fun _ => ?_⟩
      have hkp := hnot p hp
      have hkq := hnot q hq
      rw [← h] at hkq
      have hiff := side_eq N (gap (e.symm p).1) _ _ hN (hg1 _) (hg2 _)
        (by have := (e.symm p).2.isLt; omega) (by have := (e.symm q).2.isLt; omega) hkp hkq hl
      simp only
      rw [← h]
      by_cases hr : RightP N (gap (e.symm p).1) (e.symm p).2.val
      · rw [if_pos hr, if_pos (hiff.1 hr)]
      · rw [if_neg hr, if_neg (fun h' => hr (hiff.2 h'))]

end Obs2
end PEqualNP.Outside.L_lib_1316_aux

namespace PEqualNP.Outside.L_lib_1316_aux
section Finite
theorem inter_cases : ∀ u v : Finset (Fin 2), u ∩ v ≠ u → u ∩ v ≠ v →
    ((u = {0} ∧ v = {1}) ∨ (u = {1} ∧ v = {0})) ∧ u ∩ v = ∅ := by decide
theorem union_cases : ∀ u v : Finset (Fin 2), u ∪ v ≠ u → u ∪ v ≠ v →
    ((u = {0} ∧ v = {1}) ∨ (u = {1} ∧ v = {0})) ∧ u ∪ v = Finset.univ := by decide
theorem ot_zero : ot 0 = 1 := by decide
theorem ot_one : ot 1 = 0 := by decide
end Finite
end PEqualNP.Outside.L_lib_1316_aux

theorem PEqualNP.Outside.L_lib_1316 : (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
∀ (L : Finset (Finset (Finset (Fin 2)))) (r : Nat),
  let meet := ∀ A ∈ L, ∀ u ∈ A, ∀ v ∈ A, u ∩ v ∈ A
  let join := ∀ A ∈ L, ∀ u ∈ A, ∀ v ∈ A, u ∪ v ∈ A
  let fold := (∀ A ∈ L, ({0} : Finset (Fin 2)) ∈ A → ({1} : Finset (Fin 2)) ∈ A) ∨
    (∀ A ∈ L, ({1} : Finset (Fin 2)) ∈ A → ({0} : Finset (Fin 2)) ∈ A)
  let test := fun K : Nat =>
    ∀ (n m : Nat) (x : Fin m → Finset (Fin n)) (A : Fin m → Finset (Finset (Fin 2))),
      Function.Injective x → (∀ i, A i ∈ L) →
      let fits := fun (S : Finset (Fin m)) =>
        ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin 2 → Nat),
          PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
          C.output < n+2+C.size ∧ (∀ a, tap a < n+2+C.size) ∧ PEqualNP.NotBracket.notCount C ≤ r ∧
          ∀ i ∈ S, (Finset.univ.filter (fun a =>
            (C.wires (List.ofFn (fun j : Fin n => decide (j ∈ x i)) ++ [false,true])).getD (tap a) false = true)) ∈ A i
      fits Finset.univ ↔ ∀ S, S.card ≤ K → fits S
  ((∃ K, test K) ↔ meet ∨ join ∨ fold) ∧
    ((meet ∨ join) → test (3*(2^(2^r)-1))) ∧ (fold → test (3*2^r))) := by
  intro L r meet join fold test
  have hT : ∀ K, test K ↔ ∀ (n m : ℕ) (x : Fin m → Finset (Fin n)) (A : Fin m → Finset (Finset (Fin 2))),
      Function.Injective x → (∀ i, A i ∈ L) →
      ((∀ S : Finset (Fin m), S.card ≤ K → PEqualNP.Outside.L_lib_1316_aux.Feas x A r S) →
        PEqualNP.Outside.L_lib_1316_aux.Feas x A r Finset.univ) := by
    intro K
    constructor
    · intro h n m x A hx hL hsmall
      have := (h n m x A hx hL).2 (fun S hS => PEqualNP.Outside.L_lib_1316_aux.feas_to_fits n m x A r S (hsmall S hS))
      exact PEqualNP.Outside.L_lib_1316_aux.fits_to_feas n m x A r _ this
    · intro h n m x A hx hL
      constructor
      · intro hf S _
        obtain ⟨C, tap, h1, h2, h3, h4, h5, h6⟩ := hf
        exact ⟨C, tap, h1, h2, h3, h4, h5, fun i _ => h6 i (Finset.mem_univ i)⟩
      · intro hs
        exact PEqualNP.Outside.L_lib_1316_aux.feas_to_fits n m x A r _
          (h n m x A hx hL (fun S hS => PEqualNP.Outside.L_lib_1316_aux.fits_to_feas n m x A r S (hs S hS)))
  have hMeet : meet → test (3*(2^(2^r)-1)) := by
    intro hm
    rw [hT]
    intro n m x A _ hL hsmall
    apply PEqualNP.Outside.L_lib_1316_aux.bound x A 2 r (fun i => ?_) (Or.inl le_rfl)
    · intro S hS
      rw [PEqualNP.Outside.L_lib_1316_aux.T_two] at hS
      exact hsmall S hS
    · intro u hu v hv
      have := hm (A i) (hL i) u hu v hv
      convert this using 1
      ext a; simp only [Finset.mem_inter]
  have hJoin : join → test (3*(2^(2^r)-1)) := by
    intro hj
    rw [hT]
    intro n m x A _ hL hsmall
    apply PEqualNP.Outside.L_lib_1316_aux.feas_dual2 x A r
    apply PEqualNP.Outside.L_lib_1316_aux.bound (fun i => (x i)ᶜ) (fun i => (A i).image (fun w => wᶜ)) 2 r
      (fun i => PEqualNP.Outside.L_lib_1316_aux.dual_mc _ ?_) (Or.inl le_rfl)
    · intro S hS
      apply PEqualNP.Outside.L_lib_1316_aux.feas_dual
      rw [PEqualNP.Outside.L_lib_1316_aux.T_two] at hS
      exact hsmall S hS
    · intro u hu v hv
      have := hj (A i) (hL i) u hu v hv
      convert this using 1
      ext a; simp only [Finset.mem_union]
  have hFold : fold → test (3*2^r) := by
    intro hf
    rw [hT]
    intro n m x A _ hL hsmall
    rcases hf with hf | hf
    · apply PEqualNP.Outside.L_lib_1316_aux.feas_unfold 0 x A r
      apply PEqualNP.Outside.L_lib_1316_aux.bound x (fun i => (A i).erase {0}) 1 r
        (fun i => PEqualNP.Outside.L_lib_1316_aux.erase_mc 0 (A i)) (Or.inr ⟨le_rfl, 0, fun i => by simp⟩)
      intro S hS
      apply PEqualNP.Outside.L_lib_1316_aux.feas_fold 0 x A r S (fun i h => by
        rw [PEqualNP.Outside.L_lib_1316_aux.ot_zero]; exact hf (A i) (hL i) h)
      rw [PEqualNP.Outside.L_lib_1316_aux.T_one] at hS
      exact hsmall S hS
    · apply PEqualNP.Outside.L_lib_1316_aux.feas_unfold 1 x A r
      apply PEqualNP.Outside.L_lib_1316_aux.bound x (fun i => (A i).erase {1}) 1 r
        (fun i => PEqualNP.Outside.L_lib_1316_aux.erase_mc 1 (A i)) (Or.inr ⟨le_rfl, 1, fun i => by simp⟩)
      intro S hS
      apply PEqualNP.Outside.L_lib_1316_aux.feas_fold 1 x A r S (fun i h => by
        rw [PEqualNP.Outside.L_lib_1316_aux.ot_one]; exact hf (A i) (hL i) h)
      rw [PEqualNP.Outside.L_lib_1316_aux.T_one] at hS
      exact hsmall S hS
  have hObs : (∃ K, test K) → meet ∨ join ∨ fold := by
    rintro ⟨K, hK⟩
    by_contra hno
    have hnm : ¬ meet := fun h => hno (Or.inl h)
    have hnj : ¬ join := fun h => hno (Or.inr (Or.inl h))
    have hnf : ¬ fold := fun h => hno (Or.inr (Or.inr h))
    have eAa : ∃ Aa ∈ L, ({0} : Finset (Fin 2)) ∈ Aa ∧ ({1} : Finset (Fin 2)) ∈ Aa ∧ ∅ ∉ Aa := by
      by_contra hc
      apply hnm
      intro A hA u hu v hv
      by_contra huv
      have huv' : u ∩ v ∉ A := by
        intro h; apply huv; convert h using 1; ext a; simp only [Finset.mem_inter]
      have h1 : u ∩ v ≠ u := fun e => huv' (by rw [e]; exact hu)
      have h2 : u ∩ v ≠ v := fun e => huv' (by rw [e]; exact hv)
      obtain ⟨hc1, hc2⟩ := PEqualNP.Outside.L_lib_1316_aux.inter_cases u v h1 h2
      apply hc
      refine ⟨A, hA, ?_, ?_, ?_⟩
      · rcases hc1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
      · rcases hc1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
      · rw [← hc2]; exact huv'
    have eAb : ∃ Ab ∈ L, ({0} : Finset (Fin 2)) ∈ Ab ∧ ({1} : Finset (Fin 2)) ∈ Ab ∧ Finset.univ ∉ Ab := by
      by_contra hc
      apply hnj
      intro A hA u hu v hv
      by_contra huv
      have huv' : u ∪ v ∉ A := by
        intro h; apply huv; convert h using 1; ext a; simp only [Finset.mem_union]
      have h1 : u ∪ v ≠ u := fun e => huv' (by rw [e]; exact hu)
      have h2 : u ∪ v ≠ v := fun e => huv' (by rw [e]; exact hv)
      obtain ⟨hc1, hc2⟩ := PEqualNP.Outside.L_lib_1316_aux.union_cases u v h1 h2
      apply hc
      refine ⟨A, hA, ?_, ?_, ?_⟩
      · rcases hc1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
      · rcases hc1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
      · rw [← hc2]; exact huv'
    have eA1 : ∃ A1 ∈ L, ({0} : Finset (Fin 2)) ∈ A1 ∧ ({1} : Finset (Fin 2)) ∉ A1 := by
      by_contra hc
      apply hnf
      left
      intro A hA h0
      by_contra h1
      exact hc ⟨A, hA, h0, h1⟩
    have eA2 : ∃ A2 ∈ L, ({1} : Finset (Fin 2)) ∈ A2 ∧ ({0} : Finset (Fin 2)) ∉ A2 := by
      by_contra hc
      apply hnf
      right
      intro A hA h0
      by_contra h1
      exact hc ⟨A, hA, h0, h1⟩
    obtain ⟨Aa, hAaL, hAa0, hAa1, hAae⟩ := eAa
    obtain ⟨Ab, hAbL, hAb0, hAb1, hAbu⟩ := eAb
    obtain ⟨A1, hA1L, hA10, hA11⟩ := eA1
    obtain ⟨A2, hA2L, hA21, hA20⟩ := eA2
    have hN : 3 ≤ K + 3 := by omega
    have hLists : ∀ p, PEqualNP.Outside.L_lib_1316_aux.oA (K + 3) (2 ^ r) Aa Ab A1 A2 p ∈ L := by
      intro p
      unfold PEqualNP.Outside.L_lib_1316_aux.oA PEqualNP.Outside.L_lib_1316_aux.listOf
      split_ifs <;> assumption
    have key := (hT K).1 hK _ _ _ _ (PEqualNP.Outside.L_lib_1316_aux.ox_inj (K + 3) (2 ^ r) hN) hLists
      (fun S hS => PEqualNP.Outside.L_lib_1316_aux.obs_small (K + 3) (2 ^ r) hN r rfl Aa Ab A1 A2
        hAa0 hAa1 hAb0 hAb1 hA10 hA21 S (by omega))
    exact PEqualNP.Outside.L_lib_1316_aux.obs_infeas (K + 3) (2 ^ r) hN r rfl Aa Ab A1 A2 hAae hAbu hA11 hA20 key
  refine ⟨⟨hObs, ?_⟩, fun h => h.elim hMeet hJoin, hFold⟩
  rintro (h | h | h)
  · exact ⟨_, hMeet h⟩
  · exact ⟨_, hJoin h⟩
  · exact ⟨_, hFold h⟩

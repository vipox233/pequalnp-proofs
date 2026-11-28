import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1369_aux
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

theorem decode_lt (i : Fin m) (l : List (Col m)) : decode i l < 2 ^ l.length := by
  induction l with
  | nil => simp [decode]
  | cons a as ih =>
    simp only [decode, List.length_cons, pow_succ]
    split <;> omega

theorem score_lt (i : Fin m) (l : List (Col m)) : score i l < 2 ^ l.length := by
  simpa [score, List.length_reverse] using decode_lt i l.reverse

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

section VertexCoverEncoding
open scoped Classical
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

noncomputable def leftSet (t b : ℕ) (i : Fin t) : Finset (Fin (2 * t + 2 * (2 ^ b - 1))) :=
  Finset.univ.filter fun j => j.val = i.val

noncomputable def rightSet (t b : ℕ) (i : Fin t) : Finset (Fin (2 * t + 2 * (2 ^ b - 1))) :=
  Finset.univ.filter fun j => j.val = t + i.val

noncomputable def cellSet (t b : ℕ) (i j : Fin t) : Finset (Fin (2 * t + 2 * (2 ^ b - 1))) :=
  Finset.univ.filter fun h => h.val = i.val ∨ h.val = t + j.val

noncomputable def tailSet (t b : ℕ) (s : ℕ) : Finset (Fin (2 * t + 2 * (2 ^ b - 1))) :=
  Finset.univ.filter fun j => j.val < 2 * t + s + 1

noncomputable def idxL (t b : ℕ) (E : Finset (Fin t × Fin t)) (i : Fin t) :
    Fin (3 * t + E.card + 2 * (2 ^ b - 1)) :=
  ⟨i.val, by have := i.isLt; omega⟩

noncomputable def idxR (t b : ℕ) (E : Finset (Fin t × Fin t)) (i : Fin t) :
    Fin (3 * t + E.card + 2 * (2 ^ b - 1)) :=
  ⟨t + i.val, by have := i.isLt; omega⟩

noncomputable def idxD (t b : ℕ) (E : Finset (Fin t × Fin t)) (i : Fin t) :
    Fin (3 * t + E.card + 2 * (2 ^ b - 1)) :=
  ⟨2 * t + i.val, by have := i.isLt; omega⟩

noncomputable def idxE (t b : ℕ) (E : Finset (Fin t × Fin t)) (k : Fin E.card) :
    Fin (3 * t + E.card + 2 * (2 ^ b - 1)) :=
  ⟨3 * t + k.val, by have := k.isLt; omega⟩

noncomputable def idxT (t b : ℕ) (E : Finset (Fin t × Fin t)) (s : Fin (2 * (2 ^ b - 1))) :
    Fin (3 * t + E.card + 2 * (2 ^ b - 1)) :=
  ⟨3 * t + E.card + s.val, by have := s.isLt; omega⟩

noncomputable def sampleX (t b : ℕ) (E : Finset (Fin t × Fin t))
    (q : Fin (3 * t + E.card + 2 * (2 ^ b - 1))) : Finset (Fin (2 * t + 2 * (2 ^ b - 1))) :=
  if h1 : q.val < t then leftSet t b ⟨q.val, h1⟩
  else if h2 : q.val < 2 * t then rightSet t b ⟨q.val - t, by omega⟩
  else if h3 : q.val < 3 * t then cellSet t b ⟨q.val - 2 * t, by omega⟩ ⟨q.val - 2 * t, by omega⟩
  else if h4 : q.val < 3 * t + E.card then
    let e := (E.equivFin.symm ⟨q.val - 3 * t, by omega⟩).val
    cellSet t b e.1 e.2
  else
    tailSet t b (q.val - (3 * t + E.card))

theorem sampleX_idxL (t b : ℕ) (E : Finset (Fin t × Fin t)) (i : Fin t) :
    sampleX t b E (idxL t b E i) = leftSet t b i := by
  simp [sampleX, idxL, i.isLt]

theorem sampleX_idxR (t b : ℕ) (E : Finset (Fin t × Fin t)) (i : Fin t) :
    sampleX t b E (idxR t b E i) = rightSet t b i := by
  have hi := i.isLt
  have h1 : ¬ (t + i.val < t) := by omega
  have h2 : t + i.val < 2 * t := by omega
  simp [sampleX, idxR, h1, h2]

theorem sampleX_idxD (t b : ℕ) (E : Finset (Fin t × Fin t)) (i : Fin t) :
    sampleX t b E (idxD t b E i) = cellSet t b i i := by
  have hi := i.isLt
  have h1 : ¬ (2 * t + i.val < t) := by omega
  have h2 : ¬ (2 * t + i.val < 2 * t) := by omega
  have h3 : 2 * t + i.val < 3 * t := by omega
  simp [sampleX, idxD, h1, h2, h3]

theorem sampleX_idxE (t b : ℕ) (E : Finset (Fin t × Fin t)) (e : Fin t × Fin t) (he : e ∈ E) :
    sampleX t b E (idxE t b E (E.equivFin ⟨e, he⟩)) = cellSet t b e.1 e.2 := by
  let k := E.equivFin ⟨e, he⟩
  have hk := k.isLt
  have h1 : ¬ (3 * t + k.val < t) := by omega
  have h2 : ¬ (3 * t + k.val < 2 * t) := by omega
  have h3 : ¬ (3 * t + k.val < 3 * t) := by omega
  have h4 : 3 * t + k.val < 3 * t + E.card := by omega
  have heq : (⟨3 * t + k.val - 3 * t, by omega⟩ : Fin E.card) = k := by
    ext; simp
  change sampleX t b E (idxE t b E k) = _
  unfold sampleX idxE
  simp only [h1, h2, h3, h4, dite_false, dite_true]
  rw [heq]
  simp [k]

theorem sampleX_idxT (t b : ℕ) (E : Finset (Fin t × Fin t)) (s : Fin (2 * (2 ^ b - 1))) :
    sampleX t b E (idxT t b E s) = tailSet t b s.val := by
  have h1 : ¬ (3 * t + E.card + s.val < t) := by omega
  have h2 : ¬ (3 * t + E.card + s.val < 2 * t) := by omega
  have h3 : ¬ (3 * t + E.card + s.val < 3 * t) := by omega
  have h4 : ¬ (3 * t + E.card + s.val < 3 * t + E.card) := by omega
  simp [sampleX, idxT, h1, h2, h3, h4]

theorem graph_lt_2t (t b : ℕ) (E : Finset (Fin t × Fin t))
    (q : Fin (3 * t + E.card + 2 * (2 ^ b - 1))) (hq : q.val < 3 * t + E.card)
    (a : Fin (2 * t + 2 * (2 ^ b - 1))) (ha : a ∈ sampleX t b E q) : a.val < 2 * t := by
  unfold sampleX at ha
  split_ifs at ha with h1 h2 h3
  · simp [leftSet] at ha; omega
  · simp [rightSet] at ha; omega
  · simp [cellSet] at ha; omega
  · simp [cellSet] at ha
    have hlt1 := (E.equivFin.symm ⟨q.val - 3 * t, by omega⟩).val.1.isLt
    have hlt2 := (E.equivFin.symm ⟨q.val - 3 * t, by omega⟩).val.2.isLt
    omega

theorem not_tail_sub_graph (t b : ℕ) (E : Finset (Fin t × Fin t))
    (q1 q2 : Fin (3 * t + E.card + 2 * (2 ^ b - 1)))
    (h1 : ¬ q1.val < 3 * t + E.card) (h2 : q2.val < 3 * t + E.card)
    (hsub : sampleX t b E q1 ⊆ sampleX t b E q2) : False := by
  have hlen : 0 < 2 * (2 ^ b - 1) := by have := q1.isLt; omega
  let a : Fin (2 * t + 2 * (2 ^ b - 1)) := ⟨2 * t, by omega⟩
  have ha1 : a ∈ sampleX t b E q1 := by
    unfold sampleX
    have g1 : ¬ q1.val < t := by omega
    have g2 : ¬ q1.val < 2 * t := by omega
    have g3 : ¬ q1.val < 3 * t := by omega
    simp only [g1, g2, g3, h1, dite_false]
    simp [tailSet, a]
  have ha2 := graph_lt_2t t b E q2 h2 a (hsub ha1)
  simp [a] at ha2

theorem graph_sub_tail (t b : ℕ) (E : Finset (Fin t × Fin t))
    (q : Fin (3 * t + E.card + 2 * (2 ^ b - 1))) (hq : q.val < 3 * t + E.card)
    (s : Fin (2 * (2 ^ b - 1))) :
    sampleX t b E q ⊆ sampleX t b E (idxT t b E s) := by
  intro a ha
  rw [sampleX_idxT]
  have hlt := graph_lt_2t t b E q hq a ha
  simp [tailSet]
  omega

theorem tailSet_sub_iff (t b s1 s2 : ℕ) (hs1 : s1 < 2 * (2 ^ b - 1)) (_hs2 : s2 < 2 * (2 ^ b - 1)) :
    tailSet t b s1 ⊆ tailSet t b s2 ↔ s1 ≤ s2 := by
  constructor
  · intro hsub
    by_contra hlt
    have hs : s2 + 1 ≤ s1 := by omega
    let a : Fin (2 * t + 2 * (2 ^ b - 1)) := ⟨2 * t + s2 + 1, by omega⟩
    have ha1 : a ∈ tailSet t b s1 := by simp [tailSet, a]; omega
    have ha2 : a ∈ tailSet t b s2 := hsub ha1
    simp [tailSet, a] at ha2
  · intro hle a ha
    simp only [tailSet, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    omega

theorem leftSet_sub_cellSet (t b : ℕ) (i j : Fin t) : leftSet t b i ⊆ cellSet t b i j := by
  intro a ha
  simp only [leftSet, cellSet, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
  exact Or.inl ha

theorem rightSet_sub_cellSet (t b : ℕ) (i j : Fin t) : rightSet t b j ⊆ cellSet t b i j := by
  intro a ha
  simp only [rightSet, cellSet, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
  exact Or.inr ha

noncomputable def sampleV (t b : ℕ) (E : Finset (Fin t × Fin t))
    (q : Fin (3 * t + E.card + 2 * (2 ^ b - 1))) : ℕ :=
  if q.val < 3 * t + E.card then 0
  else (q.val - (3 * t + E.card) + 1) / 2

noncomputable def sampleW (t b : ℕ) (E : Finset (Fin t × Fin t)) (S : Finset (Fin t))
    (q : Fin (3 * t + E.card + 2 * (2 ^ b - 1))) (a : Fin 2) : Bool :=
  if q.val < 3 * t + E.card then
    if a.val = 0 then
      decide (∃ i : Fin t, i ∉ S ∧ ⟨i.val, by have := i.isLt; omega⟩ ∈ sampleX t b E q)
    else
      decide (∃ j : Fin t, j ∉ S ∧ ⟨t + j.val, by have := j.isLt; omega⟩ ∈ sampleX t b E q)
  else
    if a.val = 0 then
      decide ((q.val - (3 * t + E.card)) % 2 = 0)
    else
      true

theorem sampleV_lt (t b : ℕ) (E : Finset (Fin t × Fin t))
    (q : Fin (3 * t + E.card + 2 * (2 ^ b - 1))) : sampleV t b E q < 2 ^ b := by
  have hpos : 0 < 2 ^ b := Nat.two_pow_pos b
  unfold sampleV
  split_ifs with h
  · exact hpos
  · have hq := q.isLt
    omega

theorem sampleOK (t b : ℕ) (E : Finset (Fin t × Fin t)) (S : Finset (Fin t)) :
    OK (sampleX t b E) (sampleV t b E) (sampleW t b E S) := by
  intro q1 q2 hsub
  by_cases h1 : q1.val < 3 * t + E.card <;> by_cases h2 : q2.val < 3 * t + E.card
  · refine ⟨by simp [sampleV, h1, h2], ?_⟩
    intro _ a ha
    unfold sampleW at ha ⊢
    simp only [h1, h2, ite_true] at ha ⊢
    split_ifs at ha ⊢ with ha0
    · simp only [decide_eq_true_eq] at ha ⊢
      rcases ha with ⟨i, hi, hmem⟩
      exact ⟨i, hi, hsub hmem⟩
    · simp only [decide_eq_true_eq] at ha ⊢
      rcases ha with ⟨j, hj, hmem⟩
      exact ⟨j, hj, hsub hmem⟩
  · refine ⟨by simp [sampleV, h1, h2], ?_⟩
    intro heq a _
    simp only [sampleV, h1, h2, ite_true, ite_false] at heq
    have hz : q2.val - (3 * t + E.card) = 0 := by omega
    unfold sampleW
    simp only [h2, ite_false, hz]
    split_ifs <;> rfl
  · exact False.elim (not_tail_sub_graph t b E q1 q2 h1 h2 hsub)
  · have ht1 : sampleX t b E q1 = tailSet t b (q1.val - (3 * t + E.card)) := by
      unfold sampleX
      have g1 : ¬ q1.val < t := by omega
      have g2 : ¬ q1.val < 2 * t := by omega
      have g3 : ¬ q1.val < 3 * t := by omega
      simp [g1, g2, g3, h1]
    have ht2 : sampleX t b E q2 = tailSet t b (q2.val - (3 * t + E.card)) := by
      unfold sampleX
      have g1 : ¬ q2.val < t := by omega
      have g2 : ¬ q2.val < 2 * t := by omega
      have g3 : ¬ q2.val < 3 * t := by omega
      simp [g1, g2, g3, h2]
    rw [ht1, ht2] at hsub
    have hle : q1.val - (3 * t + E.card) ≤ q2.val - (3 * t + E.card) :=
      (tailSet_sub_iff t b _ _ (by have := q1.isLt; omega) (by have := q2.isLt; omega)).mp hsub
    refine ⟨by simp only [sampleV, h1, h2, ite_false]; omega, ?_⟩
    intro heq a ha
    simp only [sampleV, h1, h2, ite_false] at heq
    unfold sampleW at ha ⊢
    simp only [h1, h2, ite_false] at ha ⊢
    split_ifs at ha ⊢ with ha0
    · simp only [decide_eq_true_eq] at ha ⊢
      omega
    · rfl

theorem sampleW_idxL (t b : ℕ) (E : Finset (Fin t × Fin t)) (S : Finset (Fin t)) (i : Fin t) :
    sampleW t b E S (idxL t b E i) 0 = decide (i ∉ S) := by
  have hi := i.isLt
  have hlt : (idxL t b E i).val < 3 * t + E.card := by simp [idxL]; omega
  unfold sampleW
  simp only [hlt, ite_true, Fin.val_zero, sampleX_idxL]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, leftSet, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨k, hk, heq⟩
    have : k = i := Fin.ext heq
    subst this
    exact hk
  · intro hiS
    exact ⟨i, hiS, rfl⟩

theorem sampleW_idxR (t b : ℕ) (E : Finset (Fin t × Fin t)) (S : Finset (Fin t)) (i : Fin t) :
    sampleW t b E S (idxR t b E i) 1 = decide (i ∉ S) := by
  have hi := i.isLt
  have hlt : (idxR t b E i).val < 3 * t + E.card := by simp [idxR]; omega
  unfold sampleW
  simp only [hlt, ite_true, Fin.val_one, one_ne_zero, ite_false, sampleX_idxR]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, rightSet, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨k, hk, heq⟩
    have : k = i := Fin.ext (by omega)
    subst this
    exact hk
  · intro hiS
    exact ⟨i, hiS, rfl⟩

theorem sampleW_cell_zero (t b : ℕ) (E : Finset (Fin t × Fin t)) (S : Finset (Fin t))
    (q : Fin (3 * t + E.card + 2 * (2 ^ b - 1))) (hq : q.val < 3 * t + E.card)
    (i j : Fin t) (hx : sampleX t b E q = cellSet t b i j) :
    sampleW t b E S q 0 = decide (i ∉ S) := by
  unfold sampleW
  simp only [hq, ite_true, Fin.val_zero, hx]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, cellSet, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨k, hk, heq | heq⟩
    · have : k = i := Fin.ext heq
      subst this
      exact hk
    · have := k.isLt
      omega
  · intro hiS
    exact ⟨i, hiS, Or.inl rfl⟩

theorem sampleW_cell_one (t b : ℕ) (E : Finset (Fin t × Fin t)) (S : Finset (Fin t))
    (q : Fin (3 * t + E.card + 2 * (2 ^ b - 1))) (hq : q.val < 3 * t + E.card)
    (i j : Fin t) (hx : sampleX t b E q = cellSet t b i j) :
    sampleW t b E S q 1 = decide (j ∉ S) := by
  unfold sampleW
  simp only [hq, ite_true, Fin.val_one, one_ne_zero, ite_false, hx]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, cellSet, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨k, hk, heq | heq⟩
    · have := i.isLt
      omega
    · have : k = j := Fin.ext (by omega)
      subst this
      exact hk
  · intro hjS
    exact ⟨j, hjS, Or.inr rfl⟩

theorem sampleW_idxT (t b : ℕ) (E : Finset (Fin t × Fin t)) (S : Finset (Fin t))
    (s : Fin (2 * (2 ^ b - 1))) :
    sampleW t b E S (idxT t b E s) 0 = decide (s.val % 2 = 0) := by
  unfold sampleW
  simp [idxT]

theorem raw_eq_mask {n : ℕ} (A : Finset (Fin n)) (P : Fin n → Prop)
    [∀ a, Decidable (a ∈ A)] [∀ a, Decidable (P a)] (h : ∀ a, a ∈ A ↔ P a) :
    List.ofFn (fun a : Fin n => decide (a ∈ A)) ++ [false, true] =
    List.ofFn (fun a : Fin n => decide (P a)) ++ [false, true] := by
  congr 1; congr 1; funext a; apply Bool.eq_iff_iff.mpr; simp [h]

theorem loss_sum_exact (t M : ℕ) (w : Fin t → ℕ) (pL rZ dZ dP : Fin t → Bool)
    (hmono : ∀ i, rZ i = true → dZ i = true) :
    (Finset.univ : Finset (Fin t)).sum (fun i =>
      (if pL i = false then w i else 0) +
      (if rZ i = false then M else 0) +
      (if dZ i = true then M else 0) +
      (if dP i = true ∧ dZ i = false then M else 0)) =
    t * M + (Finset.univ.filter (fun i => pL i = false)).sum w +
      (Finset.univ : Finset (Fin t)).sum (fun i =>
        (if rZ i = false ∧ dZ i = true then M else 0) +
        (if dP i = true ∧ dZ i = false then M else 0)) := by
  have hterm : ∀ i : Fin t,
      (if pL i = false then w i else 0) +
      (if rZ i = false then M else 0) +
      (if dZ i = true then M else 0) +
      (if dP i = true ∧ dZ i = false then M else 0) =
      M + (if pL i = false then w i else 0) +
        ((if rZ i = false ∧ dZ i = true then M else 0) +
         (if dP i = true ∧ dZ i = false then M else 0)) := by
    intro i
    have hm := hmono i
    cases hr : rZ i <;> cases hd : dZ i <;> simp_all <;> omega
  simp_rw [hterm, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [← Finset.sum_filter]

theorem score_zero_on_graph (t b : ℕ) (E : Finset (Fin t × Fin t))
    (C : Circuit) (p : ℕ) (hFan : FanInTwo C) (hNot : PEqualNP.NotBracket.notCount C ≤ b)
    (hTail : ∀ s : Fin (2 * (2 ^ b - 1)), val (sampleX t b E) C.gates p (idxT t b E s) = decide (s.val % 2 = 0)) :
    ∀ q : Fin (3 * t + E.card + 2 * (2 ^ b - 1)), q.val < 3 * t + E.card →
      score q (trace (sampleX t b E) C.gates) = 0 := by
  have htrLen : (trace (sampleX t b E) C.gates).length ≤ b := by
    have h1 : (trace (sampleX t b E) C.gates).length = (ix C.gates).length := by simp [trace]
    have h2 : PEqualNP.NotBracket.notCount C = (ix C.gates).length := countIx C.gates
    omega
  have hscLt : ∀ q, score q (trace (sampleX t b E) C.gates) < 2 ^ b := by
    intro q
    calc score q (trace (sampleX t b E) C.gates) < 2 ^ (trace (sampleX t b E) C.gates).length := score_lt q _
      _ ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) htrLen
  by_cases hb : b = 0
  · subst hb
    intro q _
    have := hscLt q
    simp at this
    exact this
  · have hpow : 2 ≤ 2 ^ b := by
      have : 1 ≤ b := by omega
      calc 2 = 2 ^ 1 := by simp
        _ ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) this
    have hlenPos : 0 < 2 * (2 ^ b - 1) := by omega
    let t0 : Fin (2 * (2 ^ b - 1)) := ⟨0, hlenPos⟩
    have hstep : ∀ k (hk : 2 * k + 1 < 2 * (2 ^ b - 1)),
        score (idxT t b E ⟨2 * k, by omega⟩) (trace (sampleX t b E) C.gates) <
        score (idxT t b E ⟨2 * k + 1, hk⟩) (trace (sampleX t b E) C.gates) := by
      intro k hk
      have hsub : sampleX t b E (idxT t b E ⟨2 * k, by omega⟩) ⊆
          sampleX t b E (idxT t b E ⟨2 * k + 1, hk⟩) := by
        simp only [sampleX_idxT]
        exact (tailSet_sub_iff t b (2 * k) (2 * k + 1) (by omega) hk).mpr (by omega)
      have hord := stepOrder (sampleX t b E) C.gates hFan _ _ hsub
      rcases lt_or_eq_of_le hord.1 with hlt | heq
      · exact hlt
      · have he := hTail ⟨2 * k, by omega⟩
        have ho := hTail ⟨2 * k + 1, hk⟩
        have he1 : val (sampleX t b E) C.gates p (idxT t b E ⟨2 * k, by omega⟩) = true := by
          simpa using he
        have ho1 : val (sampleX t b E) C.gates p (idxT t b E ⟨2 * k + 1, hk⟩) = false := by
          simpa [Nat.add_mod] using ho
        have := hord.2 heq p he1
        rw [ho1] at this
        cases this
    have hclimb : ∀ k (hk : 2 * k + 1 < 2 * (2 ^ b - 1)),
        score (idxT t b E t0) (trace (sampleX t b E) C.gates) + k + 1 ≤
        score (idxT t b E ⟨2 * k + 1, hk⟩) (trace (sampleX t b E) C.gates) := by
      intro k
      induction k with
      | zero =>
        intro hk
        have := hstep 0 hk
        simpa [t0] using this
      | succ k ih =>
        intro hk
        have hk' : 2 * k + 1 < 2 * (2 ^ b - 1) := by omega
        have h1 := ih hk'
        have hsub : sampleX t b E (idxT t b E ⟨2 * k + 1, hk'⟩) ⊆
            sampleX t b E (idxT t b E ⟨2 * (k + 1), by omega⟩) := by
          simp only [sampleX_idxT]
          exact (tailSet_sub_iff t b (2 * k + 1) (2 * (k + 1)) hk' (by omega)).mpr (by omega)
        have h2 := (stepOrder (sampleX t b E) C.gates hFan _ _ hsub).1
        have h3 := hstep (k + 1) hk
        omega
    have htop : 2 * (2 ^ b - 2) + 1 < 2 * (2 ^ b - 1) := by omega
    have hbound := hclimb (2 ^ b - 2) htop
    have hlt := hscLt (idxT t b E ⟨2 * (2 ^ b - 2) + 1, htop⟩)
    have hzero0 : score (idxT t b E t0) (trace (sampleX t b E) C.gates) = 0 := by omega
    intro q hq
    have hsub : sampleX t b E q ⊆ sampleX t b E (idxT t b E t0) := graph_sub_tail t b E q hq t0
    have hle := (stepOrder (sampleX t b E) C.gates hFan _ _ hsub).1
    omega

end VertexCoverEncoding

end PEqualNP.Outside.L_lib_1369_aux

open PEqualNP.Outside.L_lib_1369_aux

theorem PEqualNP.Outside.L_lib_1369 : (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
∀ (t b : Nat) (E : Finset (Fin t × Fin t)) (w : Fin t → Nat),
  let vertices : Finset (Fin t) := Finset.univ
  let M := 1 + vertices.sum w
  let length := 2*(2^b-1)
  let n := 2*t+length
  let H := (t+1)*M
  let mask := fun (f : Fin n → Bool) => List.ofFn f ++ [false,true]
  let left := fun (i : Fin t) => mask (fun j => decide (j.val = i.val))
  let right := fun (i : Fin t) => mask (fun j => decide (j.val = t+i.val))
  let cell := fun (i j : Fin t) => mask (fun h => decide (h.val = i.val ∨ h.val = t+j.val))
  let tail := fun (s : Nat) => mask (fun j => decide (j.val < 2*t+s+1))
  let fit := fun (L : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit) (p z : Nat) =>
    let read := fun (x : List Bool) (wire : Nat) => (C.wires x).getD wire false
    let loss := vertices.sum (fun i =>
      (if read (left i) p = false then w i else 0) +
      (if read (right i) z = false then M else 0) +
      (if read (cell i i) z = true then M else 0) +
      (if read (cell i i) p = true ∧ read (cell i i) z = false then M else 0)) +
      E.sum (fun e => if read (cell e.1 e.2) p = true ∧ read (cell e.1 e.2) z = true then M else 0) +
      (Finset.range length).sum (fun s => if read (tail s) p = decide (s % 2 = 0) then 0 else H)
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
    C.output < n+2+C.size ∧ p < n+2+C.size ∧ z < n+2+C.size ∧
    PEqualNP.NotBracket.notCount C ≤ b ∧ loss ≤ L
  ∀ L : Nat,
    ((∃ S ⊆ vertices, (∀ e ∈ E, e.1 ∈ S ∨ e.2 ∈ S) ∧ t*M + S.sum w ≤ L) ↔
      ∃ C p z, fit L C p z) ∧
    ((∃ C p z, fit L C p z) →
      ∃ C p z, fit L C p z ∧ C.size ≤ (3*t+E.card+length)*(n+2*b+2)+b)) := by
  intro t b E w vertices M length n H mask left right cell tail fit L
  let x := sampleX t b E
  have hrawL : ∀ i : Fin t, raw x (idxL t b E i) = left i := by
    intro i
    unfold raw
    rw [show x (idxL t b E i) = leftSet t b i from sampleX_idxL t b E i]
    change List.ofFn _ ++ [false, true] = List.ofFn _ ++ [false, true]
    congr 1; congr 1; funext a; apply Bool.eq_iff_iff.mpr; simp [leftSet]
  have hrawR : ∀ i : Fin t, raw x (idxR t b E i) = right i := by
    intro i
    unfold raw
    rw [show x (idxR t b E i) = rightSet t b i from sampleX_idxR t b E i]
    change List.ofFn _ ++ [false, true] = List.ofFn _ ++ [false, true]
    congr 1; congr 1; funext a; apply Bool.eq_iff_iff.mpr; simp [rightSet]
  have hrawD : ∀ i : Fin t, raw x (idxD t b E i) = cell i i := by
    intro i
    unfold raw
    rw [show x (idxD t b E i) = cellSet t b i i from sampleX_idxD t b E i]
    change List.ofFn _ ++ [false, true] = List.ofFn _ ++ [false, true]
    congr 1; congr 1; funext a; apply Bool.eq_iff_iff.mpr; simp [cellSet]
  have hrawE : ∀ e : Fin t × Fin t, ∀ he : e ∈ E,
      raw x (idxE t b E (E.equivFin ⟨e, he⟩)) = cell e.1 e.2 := by
    intro e he
    unfold raw
    rw [show x (idxE t b E (E.equivFin ⟨e, he⟩)) = cellSet t b e.1 e.2 from sampleX_idxE t b E e he]
    change List.ofFn _ ++ [false, true] = List.ofFn _ ++ [false, true]
    congr 1; congr 1; funext a; apply Bool.eq_iff_iff.mpr; simp [cellSet]
  have hrawT : ∀ s : Fin length, raw x (idxT t b E s) = tail s.val := by
    intro s
    unfold raw
    rw [show x (idxT t b E s) = tailSet t b s.val from sampleX_idxT t b E s]
    change List.ofFn _ ++ [false, true] = List.ofFn _ ++ [false, true]
    congr 1; congr 1; funext a; apply Bool.eq_iff_iff.mpr; simp [tailSet]
  have hForward :
      (∃ S ⊆ vertices, (∀ e ∈ E, e.1 ∈ S ∨ e.2 ∈ S) ∧ t * M + S.sum w ≤ L) →
      ∃ C p z, fit L C p z ∧ C.size ≤ (3 * t + E.card + length) * (n + 2 * b + 2) + b := by
    rintro ⟨S, _, hCov, hCost⟩
    obtain ⟨C, tap, hFit, hSize⟩ :=
      sufficient x (sampleV t b E) (sampleW t b E S) (sampleV_lt t b E) (sampleOK t b E S)
    refine ⟨C, tap 0, tap 1, ⟨hFit.1, hFit.2.1, hFit.2.2.1, hFit.2.2.2.2.2.1 0, hFit.2.2.2.2.2.1 1,
      le_of_eq hFit.2.2.2.1, ?_⟩, hSize⟩
    have htap := hFit.2.2.2.2.2.2.1
    dsimp only
    have hVsum : vertices.sum (fun i =>
        (if (C.wires (left i)).getD (tap 0) false = false then w i else 0) +
        (if (C.wires (right i)).getD (tap 1) false = false then M else 0) +
        (if (C.wires (cell i i)).getD (tap 1) false = true then M else 0) +
        (if (C.wires (cell i i)).getD (tap 0) false = true ∧
            (C.wires (cell i i)).getD (tap 1) false = false then M else 0)) =
        t * M + S.sum w := by
      have hterm : ∀ i : Fin t,
          (if (C.wires (left i)).getD (tap 0) false = false then w i else 0) +
          (if (C.wires (right i)).getD (tap 1) false = false then M else 0) +
          (if (C.wires (cell i i)).getD (tap 1) false = true then M else 0) +
          (if (C.wires (cell i i)).getD (tap 0) false = true ∧
              (C.wires (cell i i)).getD (tap 1) false = false then M else 0) =
          M + (if i ∈ S then w i else 0) := by
        intro i
        rw [← hrawL i, ← hrawR i, ← hrawD i]
        change (if val x C.gates (tap 0) (idxL t b E i) = false then w i else 0) +
          (if val x C.gates (tap 1) (idxR t b E i) = false then M else 0) +
          (if val x C.gates (tap 1) (idxD t b E i) = true then M else 0) +
          (if val x C.gates (tap 0) (idxD t b E i) = true ∧
              val x C.gates (tap 1) (idxD t b E i) = false then M else 0) = _
        rw [htap (idxL t b E i) 0, htap (idxR t b E i) 1, htap (idxD t b E i) 0, htap (idxD t b E i) 1]
        rw [sampleW_idxL, sampleW_idxR,
          sampleW_cell_zero t b E S (idxD t b E i) (by have := i.isLt; simp [idxD]; omega) i i (sampleX_idxD t b E i),
          sampleW_cell_one t b E S (idxD t b E i) (by have := i.isLt; simp [idxD]; omega) i i (sampleX_idxD t b E i)]
        by_cases hi : i ∈ S <;> simp [hi] <;> omega
      simp_rw [hterm, Finset.sum_add_distrib]
      simp only [vertices, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      congr 1
      rw [← Finset.sum_filter]
      congr 1
      ext i
      simp
    have hEsum : E.sum (fun e =>
        if (C.wires (cell e.1 e.2)).getD (tap 0) false = true ∧
           (C.wires (cell e.1 e.2)).getD (tap 1) false = true then M else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro e he
      rw [← hrawE e he]
      change (if val x C.gates (tap 0) (idxE t b E (E.equivFin ⟨e, he⟩)) = true ∧
                 val x C.gates (tap 1) (idxE t b E (E.equivFin ⟨e, he⟩)) = true then M else 0) = 0
      rw [htap _ 0, htap _ 1,
        sampleW_cell_zero t b E S _ (by simp [idxE]) e.1 e.2 (sampleX_idxE t b E e he),
        sampleW_cell_one t b E S _ (by simp [idxE]) e.1 e.2 (sampleX_idxE t b E e he)]
      rcases hCov e he with h1 | h2
      · simp [h1]
      · simp [h2]
    have hTsum : (Finset.range length).sum (fun s =>
        if (C.wires (tail s)).getD (tap 0) false = decide (s % 2 = 0) then 0 else H) = 0 := by
      apply Finset.sum_eq_zero
      intro s hs
      have hs' : s < length := Finset.mem_range.mp hs
      rw [← hrawT ⟨s, hs'⟩]
      change (if val x C.gates (tap 0) (idxT t b E ⟨s, hs'⟩) = decide (s % 2 = 0) then 0 else H) = 0
      rw [htap _ 0, sampleW_idxT]
      simp
    have hgoal :
        vertices.sum (fun i =>
          (if (C.wires (left i)).getD (tap 0) false = false then w i else 0) +
          (if (C.wires (right i)).getD (tap 1) false = false then M else 0) +
          (if (C.wires (cell i i)).getD (tap 1) false = true then M else 0) +
          (if (C.wires (cell i i)).getD (tap 0) false = true ∧
              (C.wires (cell i i)).getD (tap 1) false = false then M else 0)) +
        E.sum (fun e =>
          if (C.wires (cell e.1 e.2)).getD (tap 0) false = true ∧
             (C.wires (cell e.1 e.2)).getD (tap 1) false = true then M else 0) +
        (Finset.range length).sum (fun s =>
          if (C.wires (tail s)).getD (tap 0) false = decide (s % 2 = 0) then 0 else H) ≤ L := by
      rw [hVsum, hEsum, hTsum]
      omega
    convert hgoal
  have hBackward :
      (∃ C p z, fit L C p z) →
      ∃ S ⊆ vertices, (∀ e ∈ E, e.1 ∈ S ∨ e.2 ∈ S) ∧ t * M + S.sum w ≤ L := by
    rintro ⟨C, p, z, hFan, _, _, _, _, hNot, hLoss0⟩
    dsimp only at hLoss0
    have hLoss :
        vertices.sum (fun i =>
          (if (C.wires (left i)).getD p false = false then w i else 0) +
          (if (C.wires (right i)).getD z false = false then M else 0) +
          (if (C.wires (cell i i)).getD z false = true then M else 0) +
          (if (C.wires (cell i i)).getD p false = true ∧
              (C.wires (cell i i)).getD z false = false then M else 0)) +
        E.sum (fun e =>
          if (C.wires (cell e.1 e.2)).getD p false = true ∧
             (C.wires (cell e.1 e.2)).getD z false = true then M else 0) +
        (Finset.range length).sum (fun s =>
          if (C.wires (tail s)).getD p false = decide (s % 2 = 0) then 0 else H) ≤ L := by
      convert hLoss0
    clear hLoss0
    by_cases hHL : H ≤ L
    · refine ⟨vertices, Finset.Subset.rfl, fun e _ => Or.inl (Finset.mem_univ _), ?_⟩
      dsimp only [H, M] at hHL ⊢
      have : (t + 1) * (1 + vertices.sum w) = t * (1 + vertices.sum w) + (1 + vertices.sum w) := by ring
      omega
    · have hLtH : L < H := by omega
      have hTailEq : ∀ s : Fin length, val x C.gates p (idxT t b E s) = decide (s.val % 2 = 0) := by
        intro s
        by_contra hne
        have hmem : s.val ∈ Finset.range length := Finset.mem_range.mpr s.isLt
        have hle := Finset.single_le_sum
          (f := fun u => if (C.wires (tail u)).getD p false = decide (u % 2 = 0) then 0 else H)
          (fun _ _ => Nat.zero_le _) hmem
        rw [← hrawT s] at hle
        change (if val x C.gates p (idxT t b E s) = decide (s.val % 2 = 0) then 0 else H) ≤ _ at hle
        rw [ite_eq_right hne] at hle
        omega
      have hZero := score_zero_on_graph t b E C p hFan hNot hTailEq
      have hMono : ∀ q1 q2 : Fin (3 * t + E.card + length),
          q1.val < 3 * t + E.card → q2.val < 3 * t + E.card → x q1 ⊆ x q2 →
          ∀ wire, val x C.gates wire q1 = true → val x C.gates wire q2 = true := by
        intro q1 q2 h1 h2 hsub wire hw
        have hord := stepOrder x C.gates hFan q1 q2 hsub
        exact hord.2 (by rw [hZero q1 h1, hZero q2 h2]) wire hw
      have hMonoR : ∀ i : Fin t,
          val x C.gates z (idxR t b E i) = true → val x C.gates z (idxD t b E i) = true := by
        intro i hi
        apply hMono (idxR t b E i) (idxD t b E i)
          (by have := i.isLt; simp [idxR]; omega)
          (by have := i.isLt; simp [idxD]; omega)
        · simp only [x, sampleX_idxR, sampleX_idxD]
          exact rightSet_sub_cellSet t b i i
        · exact hi
      have hMonoL : ∀ i : Fin t,
          val x C.gates p (idxL t b E i) = true → val x C.gates p (idxD t b E i) = true := by
        intro i hi
        apply hMono (idxL t b E i) (idxD t b E i)
          (by have := i.isLt; simp [idxL]; omega)
          (by have := i.isLt; simp [idxD]; omega)
        · simp only [x, sampleX_idxL, sampleX_idxD]
          exact leftSet_sub_cellSet t b i i
        · exact hi
      have hMonoEL : ∀ e : Fin t × Fin t, ∀ he : e ∈ E,
          val x C.gates p (idxL t b E e.1) = true →
          val x C.gates p (idxE t b E (E.equivFin ⟨e, he⟩)) = true := by
        intro e he hi
        apply hMono (idxL t b E e.1) (idxE t b E (E.equivFin ⟨e, he⟩))
          (by have := e.1.isLt; simp [idxL]; omega)
          (by simp [idxE])
        · simp only [x, sampleX_idxL, sampleX_idxE]
          exact leftSet_sub_cellSet t b e.1 e.2
        · exact hi
      have hMonoER : ∀ e : Fin t × Fin t, ∀ he : e ∈ E,
          val x C.gates z (idxR t b E e.2) = true →
          val x C.gates z (idxE t b E (E.equivFin ⟨e, he⟩)) = true := by
        intro e he hi
        apply hMono (idxR t b E e.2) (idxE t b E (E.equivFin ⟨e, he⟩))
          (by have := e.2.isLt; simp [idxR]; omega)
          (by simp [idxE])
        · simp only [x, sampleX_idxR, sampleX_idxE]
          exact rightSet_sub_cellSet t b e.1 e.2
        · exact hi
      have hRewriteV :
          vertices.sum (fun i =>
            (if (C.wires (left i)).getD p false = false then w i else 0) +
            (if (C.wires (right i)).getD z false = false then M else 0) +
            (if (C.wires (cell i i)).getD z false = true then M else 0) +
            (if (C.wires (cell i i)).getD p false = true ∧
                (C.wires (cell i i)).getD z false = false then M else 0)) =
          t * M + (Finset.univ.filter (fun i => val x C.gates p (idxL t b E i) = false)).sum w +
            (Finset.univ : Finset (Fin t)).sum (fun i =>
              (if val x C.gates z (idxR t b E i) = false ∧ val x C.gates z (idxD t b E i) = true then M else 0) +
              (if val x C.gates p (idxD t b E i) = true ∧ val x C.gates z (idxD t b E i) = false then M else 0)) := by
        have heq1 : vertices.sum (fun i =>
            (if (C.wires (left i)).getD p false = false then w i else 0) +
            (if (C.wires (right i)).getD z false = false then M else 0) +
            (if (C.wires (cell i i)).getD z false = true then M else 0) +
            (if (C.wires (cell i i)).getD p false = true ∧
                (C.wires (cell i i)).getD z false = false then M else 0)) =
            (Finset.univ : Finset (Fin t)).sum (fun i =>
              (if val x C.gates p (idxL t b E i) = false then w i else 0) +
              (if val x C.gates z (idxR t b E i) = false then M else 0) +
              (if val x C.gates z (idxD t b E i) = true then M else 0) +
              (if val x C.gates p (idxD t b E i) = true ∧ val x C.gates z (idxD t b E i) = false then M else 0)) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [← hrawL i, ← hrawR i, ← hrawD i]
          rfl
        rw [heq1]
        exact loss_sum_exact t M w
          (fun i => val x C.gates p (idxL t b E i))
          (fun i => val x C.gates z (idxR t b E i))
          (fun i => val x C.gates z (idxD t b E i))
          (fun i => val x C.gates p (idxD t b E i))
          hMonoR
      rw [hRewriteV] at hLoss
      clear hRewriteV
      let S := Finset.univ.filter (fun i : Fin t => val x C.gates p (idxL t b E i) = false)
      have hCostS : t * M + S.sum w ≤ L := by
        dsimp only [S]
        omega
      refine ⟨S, Finset.subset_univ _, ?_, hCostS⟩
      have hHsplit : H = t * M + M := by dsimp only [H]; ring
      intro e he
      by_contra hnc
      have hnc1 : e.1 ∉ S := fun h => hnc (Or.inl h)
      have hnc2 : e.2 ∉ S := fun h => hnc (Or.inr h)
      have h1 : val x C.gates p (idxL t b E e.1) = true := by
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hnc1
        cases h : val x C.gates p (idxL t b E e.1)
        · exact False.elim (hnc1 h)
        · rfl
      have h2 : val x C.gates p (idxL t b E e.2) = true := by
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hnc2
        cases h : val x C.gates p (idxL t b E e.2)
        · exact False.elim (hnc2 h)
        · rfl
      have hdp2 : val x C.gates p (idxD t b E e.2) = true := hMonoL e.2 h2
      have hdz2 : val x C.gates z (idxD t b E e.2) = true := by
        cases hfalse : val x C.gates z (idxD t b E e.2)
        · have hle := Finset.single_le_sum
            (f := fun i =>
              (if val x C.gates z (idxR t b E i) = false ∧ val x C.gates z (idxD t b E i) = true then M else 0) +
              (if val x C.gates p (idxD t b E i) = true ∧ val x C.gates z (idxD t b E i) = false then M else 0))
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ e.2)
          simp only [hdp2, hfalse, and_true, and_false, Bool.false_eq_true, ite_true, ite_false, zero_add] at hle
          omega
        · rfl
      have hrz2 : val x C.gates z (idxR t b E e.2) = true := by
        cases hfalse : val x C.gates z (idxR t b E e.2)
        · have hle := Finset.single_le_sum
            (f := fun i =>
              (if val x C.gates z (idxR t b E i) = false ∧ val x C.gates z (idxD t b E i) = true then M else 0) +
              (if val x C.gates p (idxD t b E i) = true ∧ val x C.gates z (idxD t b E i) = false then M else 0))
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ e.2)
          simp only [hdz2, hfalse, and_true, and_false, Bool.true_eq_false, ite_true, ite_false, add_zero] at hle
          omega
        · rfl
      have hep : val x C.gates p (idxE t b E (E.equivFin ⟨e, he⟩)) = true := hMonoEL e he h1
      have hez : val x C.gates z (idxE t b E (E.equivFin ⟨e, he⟩)) = true := hMonoER e he hrz2
      have hle := Finset.single_le_sum
        (f := fun e' =>
          if (C.wires (cell e'.1 e'.2)).getD p false = true ∧
             (C.wires (cell e'.1 e'.2)).getD z false = true then M else 0)
        (fun _ _ => Nat.zero_le _) he
      rw [← hrawE e he] at hle
      change (if val x C.gates p (idxE t b E (E.equivFin ⟨e, he⟩)) = true ∧
                 val x C.gates z (idxE t b E (E.equivFin ⟨e, he⟩)) = true then M else 0) ≤ _ at hle
      simp only [hep, hez, and_self, ite_true] at hle
      omega
  refine ⟨⟨?_, hBackward⟩, ?_⟩
  · intro hS
    obtain ⟨C, p, z, hfit, _⟩ := hForward hS
    exact ⟨C, p, z, hfit⟩
  · intro hC
    exact hForward (hBackward hC)

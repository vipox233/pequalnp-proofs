import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1425
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open scoped Classical

def Valid (n : Nat) (D : Circuit) := FanInTwo D ∧ ReadsBack (n+2) D ∧ D.output<n+2+D.size
noncomputable def Bits {n : Nat} (X : Finset (Fin n)) := List.ofFn (fun j : Fin n => decide (j∈X))
def Possible {r m : Nat} (b : Nat) (lab : Finset (Fin r) → Fin m → Prop) : Prop :=
  ∃ (D : Circuit) (out : Fin m → Nat), Valid r D ∧ (∀ j, out j<r+2+D.size) ∧
    PEqualNP.NotBracket.notCount D ≤ b ∧ ∀ X i, lab X i → ∀ j,
      (D.wires (Bits X ++ [false,true])).getD (out j) false = decide (i=j)

def block {r d : Nat} (g : Fin r → Fin d) (j : Fin d) : Finset (Fin r) :=
  Finset.univ.filter (fun i => g i=j)

abbrev Box {r d : Nat} (g : Fin r → Fin d) := (j : Fin d) → Fin ((block g j).card+1)

def query {r d : Nat} (g : Fin r → Fin d) (X : Finset (Fin r)) : Box g :=
  fun j => ⟨(X∩block g j).card, Nat.lt_succ_of_le (Finset.card_le_card Finset.inter_subset_right)⟩

def Reach {Q : Type} [LE Q] {m : Nat} (T : Q → Fin m → Bool) : Nat → Q → Fin m → Prop
  | 0, _, _ => False
  | 1, v, i => ∃ u, u≤v ∧ T u i=true
  | l+2, v, i => ∃ u, u≤v ∧ T u i=true ∧ ∃ j, j≠i ∧ Reach T (l+1) u j

end PEqualNP.Outside.L_lib_1425

namespace PEqualNP.Outside.L_lib_1425
namespace StageNet
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
    have lim : sel.card≤ m := by simpa using Finset.card_le_univ sel
    rw [hist_succ]
    refine ⟨V,hV.relax ?_ Set.Subset.rfl,(bs.trans su).trans uv,fun i => allV i (Finset.mem_univ _)⟩
    simp only [Finset.card_univ,Fintype.card_fin,mul_one]
    simp only [Nat.mul_add,Nat.mul_succ] at *
    omega
end Construction

end StageNet
end PEqualNP.Outside.L_lib_1425

namespace PEqualNP.Outside.L_lib_1425
namespace DP
open StageNet
open scoped Classical

variable {n p m : Nat} {x : Fin p → Finset (Fin n)} {tr : List (Col p)}
variable {k : Nat} {S : Set (Col p)}

theorem multiBatch {ι κ : Type} (s : Finset ι) (F : ι → κ → Col p) (cost : Nat)
    (H : Built x tr k S)
    (make : ∀ {K U}, Built x tr K U → S⊆U → ∀ a∈s, ∃ V, Built x tr (K+cost) V ∧ U⊆V ∧ ∀ b,F a b∈V) :
    ∃ V, Built x tr (k+s.card*cost) V ∧ S⊆V ∧ ∀ a∈s, ∀ b,F a b∈V := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨S,by simpa using H,Set.Subset.rfl,by simp⟩
  | @insert a s fresh ih =>
    obtain ⟨U,hU,su,old⟩ := ih (fun h st i hi => make h st i (Finset.mem_insert_of_mem hi))
    obtain ⟨V,hV,uv,haveV⟩ := make hU su a (Finset.mem_insert_self _ _)
    refine ⟨V,by simpa [Finset.card_insert_of_notMem fresh,Nat.add_mul,Nat.add_assoc] using hV,su.trans uv,?_⟩
    intro i hi b
    rcases Finset.mem_insert.mp hi with rfl|hi
    · exact haveV _
    · exact uv (old i hi b)

noncomputable def pref (f : Fin m → Col p) (t : Nat) : Col p := fun z => decide (∃ i : Fin m, i.val<t ∧ f i z=true)

lemma prefBuild (f : Fin m → Col p) (H : Built x tr k S) (no : (fun _ => false)∈S) (src : ∀ i,f i∈S)
    (t : Nat) (ht : t ≤ m) :
    ∃ V, Built x tr (k+t) V ∧ S⊆V ∧ ∀ a≤t, pref f a∈V := by
  induction t with
  | zero =>
    refine ⟨S,by simpa using H,Set.Subset.rfl,?_⟩
    intro a ha
    have eq : pref f a = fun _ => false := by funext z; simp [pref,show a=0 by omega]
    exact eq ▸ no
  | succ t ih =>
    obtain ⟨U,hu,su,previous⟩ := ih (by omega)
    let i : Fin m := ⟨t,by omega⟩
    have made := Built.orGate hu (previous t (le_refl _)) (su (src i))
    refine ⟨_,by simpa [Nat.add_assoc] using made,su.trans (Set.subset_insert _ _),?_⟩
    intro a ha
    by_cases eq : a=t+1
    · subst a
      apply Set.mem_insert_iff.mpr
      left
      funext z
      apply Bool.eq_iff_iff.mpr
      simp only [pref,disj,decide_eq_true_eq,Bool.or_eq_true]
      constructor
      · rintro ⟨j,hj,hf⟩
        by_cases v : j.val=t
        · exact Or.inr ((Fin.ext (show j.val=i.val from v) : j=i) ▸ hf)
        · exact Or.inl ⟨j,by omega,hf⟩
      · rintro (⟨j,lt,hf⟩|hf)
        · exact ⟨j,by omega,hf⟩
        · exact ⟨i,by simp [i],hf⟩
    · exact Set.mem_insert_of_mem _ (previous _ (by omega))

noncomputable def excluded (f : Fin m → Col p) (i : Fin m) : Col p :=
  fun z => decide (∃ j, j≠i ∧ f j z=true)

lemma excludeBuild (f : Fin m → Col p) (H : Built x tr k S) (no : (fun _ => false)∈S)
    (src : ∀ i,f i∈S) :
    ∃ V, Built x tr (k+3*m) V ∧ S⊆V ∧ ∀ i, excluded f i∈V := by
  obtain ⟨U,bu,su,pf⟩ := prefBuild f H no src m (le_refl _)
  let fr := fun i : Fin m => f i.rev
  obtain ⟨T,bt,ut,sf⟩ := prefBuild fr bu (su no) (fun i => su (src i.rev)) m (le_refl _)
  obtain ⟨V,bv,tv,allV⟩ := batch (Finset.univ : Finset (Fin m)) (excluded f) 1 bt (by
    intro K R br trr i _
    have h1 := trr (ut (pf i.val (Nat.le_of_lt i.isLt)))
    have h2 := trr (sf i.rev.val (Nat.le_of_lt i.rev.isLt))
    have add := Built.orGate br h1 h2
    refine ⟨_,add,Set.subset_insert _ _,Set.mem_insert_iff.mpr (Or.inl ?_)⟩
    funext z
    apply Bool.eq_iff_iff.mpr
    simp only [excluded,disj,pref,decide_eq_true_eq,Bool.or_eq_true]
    constructor
    · rintro ⟨j,hj,hz⟩
      rcases lt_or_gt_of_ne hj with less|more
      · exact Or.inl ⟨j,less,hz⟩
      · exact Or.inr ⟨j.rev,Fin.rev_lt_rev.mpr more,by simpa [fr] using hz⟩
    · rintro (⟨j,hj,hz⟩|⟨j,hj,hz⟩)
      · exact ⟨j,ne_of_lt (show j < i from hj),hz⟩
      · refine ⟨j.rev,?_,hz⟩
        intro e
        have eq := congrArg Fin.rev e
        simp only [Fin.rev_rev] at eq
        exact (ne_of_lt (show j < i.rev from hj)) eq)
  exact ⟨V,bv.relax (by simp;omega) Set.Subset.rfl,(su.trans ut).trans tv,fun i => allV i (Finset.mem_univ _)⟩

end DP
end PEqualNP.Outside.L_lib_1425

namespace PEqualNP.Outside.L_lib_1425
namespace Grid
open StageNet
open scoped Classical

abbrev Point {d : Nat} (s : Fin d → Nat) := (j : Fin d) → Fin (s j+1)

noncomputable def closure {d p : Nat} {s : Fin d → Nat} (F : Point s → Col p) (v : Point s) : Col p :=
  fun z => decide (∃ u : Point s, u ≤ v ∧ F u z = true)

noncomputable def previous {d : Nat} {s : Fin d → Nat} (v : Point s) (j : Fin d) : Point s :=
  Function.update v j ⟨(v j).val-1, by have := (v j).isLt; omega⟩

theorem previous_le {d : Nat} {s : Fin d → Nat} (v : Point s) (j : Fin d) : previous v j ≤ v := by
  intro i
  by_cases hi : i=j
  · subst i
    simp only [previous, Function.update_self]
    change (v j).val-1 ≤ (v j).val
    omega
  · simp [previous,Function.update_of_ne hi]

def weight {d : Nat} {s : Fin d → Nat} (v : Point s) : Nat := ∑ j, (v j).val

theorem weight_previous {d : Nat} {s : Fin d → Nat} (v : Point s) (j : Fin d) (hj : (v j).val ≠ 0) :
    weight (previous v j) < weight v := by
  apply Finset.sum_lt_sum
  · intro i _
    exact previous_le v j i
  · refine ⟨j, Finset.mem_univ _, ?_⟩
    simp only [previous, Function.update_self]
    omega

noncomputable def branch {d p : Nat} {s : Fin d → Nat} (F : Point s → Col p) (v : Point s) (j : Fin d) :
    Col p := if (v j).val = 0 then F v else closure F (previous v j)

theorem closure_step {d p : Nat} {s : Fin d → Nat} (F : Point s → Col p) (v : Point s) :
    closure F v = fun z => decide (F v z = true ∨ ∃ j : Fin d, branch F v j z = true) := by
  funext z
  apply Bool.eq_iff_iff.mpr
  simp only [closure, decide_eq_true_eq]
  constructor
  · rintro ⟨u, huv, hf⟩
    by_cases he : u = v
    · exact Or.inl (he ▸ hf)
    · obtain ⟨j, hj⟩ : ∃ j, u j ≠ v j := by
        by_contra! same
        exact he (funext same)
      have hlt : (u j).val < (v j).val := lt_of_le_of_ne (huv j) (fun e => hj (Fin.ext e))
      have hn : (v j).val ≠ 0 := by omega
      right
      refine ⟨j, ?_⟩
      simp only [branch, hn, ite_false, closure, decide_eq_true_eq]
      refine ⟨u, ?_, hf⟩
      intro k
      by_cases hk : k=j
      · subst k
        simp only [previous, Function.update_self]
        change (u j).val ≤ (v j).val-1
        omega
      · simpa [previous, Function.update_of_ne hk] using huv k
  · rintro (hv | ⟨j, hj⟩)
    · exact ⟨v,le_rfl,hv⟩
    · by_cases hz : (v j).val=0
      · exact ⟨v,le_rfl,by simpa [branch,hz] using hj⟩
      · simp only [branch,hz,ite_false,closure,decide_eq_true_eq] at hj
        obtain ⟨u,hu,hf⟩ := hj
        exact ⟨u,hu.trans (previous_le v j),hf⟩

theorem foldFrom {p n : Nat} {x : Fin p → Finset (Fin n)} {tr : List (Col p)}
    {S : Set (Col p)} {k : Nat} {ι : Type} (a : Finset ι) (G : ι → Col p) (f : Col p)
    (built : Built x tr k S) (hf : f∈S) (hg : ∀ j ∈ a, G j ∈ S) :
    ∃ T, Built x tr (k+a.card) T ∧ S⊆T ∧
      (fun z => decide (f z = true ∨ ∃ j ∈ a, G j z = true)) ∈ T := by
  classical
  induction a using Finset.induction_on with
  | empty =>
    refine ⟨S,by simpa using built,Set.Subset.rfl,?_⟩
    simpa using hf
  | @insert j a fresh ih =>
    obtain ⟨U,hU,sub,ht⟩ := ih (fun i hi => hg i (Finset.mem_insert_of_mem hi))
    let f0 : Col p := fun z => decide (f z = true ∨ ∃ i ∈ a, G i z = true)
    have join := hU.orGate (sub (hg j (Finset.mem_insert_self ..))) (show f0 ∈ U from ht)
    refine ⟨insert (disj (G j) f0) U,?_,sub.trans (Set.subset_insert ..),?_⟩
    · simpa [Finset.card_insert_of_notMem fresh, Nat.add_assoc] using join
    · apply Set.mem_insert_iff.mpr
      left
      funext z
      apply Bool.eq_iff_iff.mpr
      simp [disj,f0,Bool.or_eq_true]
      tauto

theorem gridClosure {d p n : Nat} (s : Fin d → Nat) (F : Point s → Col p)
    {x : Fin p → Finset (Fin n)} {tr : List (Col p)} {k : Nat} {S : Set (Col p)}
    (built : Built x tr k S) (hF : ∀ v, F v ∈ S) :
    ∃ T, Built x tr (k+d*Fintype.card (Point s)) T ∧ S⊆T ∧
      ∀ v : Point s, (fun z => decide (∃ u : Point s, u ≤ v ∧ F u z = true)) ∈ T := by
  classical
  have go (rem : Finset (Point s)) :
      ∀ {K : Nat} {U : Set (Col p)}, Built x tr K U → (∀ v, F v∈U) →
        (∀ v ∉ rem, closure F v ∈ U) →
        ∃ V, Built x tr (K+d*rem.card) V ∧ U⊆V ∧ ∀ v, closure F v ∈ V := by
    induction rem using Finset.strongInductionOn
    rename_i rem ih
    intro K U hU init known
    by_cases hne : rem.Nonempty
    · obtain ⟨v,hv,small⟩ := rem.exists_min_image weight hne
      have branches (j : Fin d) : branch F v j ∈ U := by
        by_cases hz : (v j).val=0
        · simpa [branch,hz] using init v
        · simp only [branch,hz,ite_false]
          apply known
          intro h
          exact (not_lt_of_ge (small _ h)) (weight_previous v j hz)
      obtain ⟨U',hU',sub,hnew⟩ := foldFrom Finset.univ (branch F v) (F v) hU (init v) (fun j _ => branches j)
      have hvbuilt : closure F v ∈ U' := by
        rw [closure_step]
        simpa using hnew
      have rest (w : Point s) (hw : w ∉ rem.erase v) : closure F w ∈ U' := by
        by_cases eq : w=v
        · exact eq ▸ hvbuilt
        · exact sub (known w (fun h => hw (Finset.mem_erase.mpr ⟨eq,h⟩)))
      obtain ⟨V,hV,uv,done⟩ := ih (rem.erase v) (Finset.erase_ssubset hv) hU' (fun w => sub (init w)) rest
      refine ⟨V,?_,sub.trans uv,done⟩
      have eq : rem.card = (rem.erase v).card+1 := (Finset.card_erase_add_one hv).symm
      simpa only [eq, Nat.mul_add, Nat.mul_one, Finset.card_univ, Fintype.card_fin,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hV
    · have he : rem = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      subst rem
      exact ⟨U,by simpa using hU, Set.Subset.rfl, fun v => known v (by simp)⟩
  obtain ⟨T,hT,hS,hAll⟩ := go Finset.univ built hF (by simp)
  exact ⟨T,by simpa using hT,hS,hAll⟩
end Grid
end PEqualNP.Outside.L_lib_1425

namespace PEqualNP.Outside.L_lib_1425
namespace DP
open StageNet
open scoped Classical
variable {n p m d k : Nat} {x : Fin p → Finset (Fin n)} {tr : List (Col p)} {S : Set (Col p)}

noncomputable def traceAt {Q : Type} [LE Q] (data : Fin p → Q → Fin m → Bool)
    (l : Nat) (v : Q) (i : Fin m) : Col p := fun z => decide (Reach (data z) l v i)

private theorem sameBool {P Q : Prop} {dP : Decidable P} {dQ : Decidable Q} (eq : P ↔ Q) :
    @decide P dP = @decide Q dQ := by
  by_cases hp : P
  · rw [@decide_eq_true P dP hp,@decide_eq_true Q dQ (eq.mp hp)]
  · rw [@decide_eq_false P dP hp,@decide_eq_false Q dQ (fun q => hp (eq.mpr q))]

theorem firstLayer (s : Fin d → Nat) (data : Fin p → Grid.Point s → Fin m → Bool)
    (H : Built x tr k S) (table : ∀ v i, (fun z => data z v i)∈S) :
    ∃ V, Built x tr (k+(d+4)*Fintype.card (Grid.Point s)*m) V ∧ S⊆V ∧
      ∀ v i, traceAt data 1 v i∈V := by
  let N := Fintype.card (Grid.Point s)
  obtain ⟨V,bv,sv,hit⟩ := multiBatch (Finset.univ : Finset (Fin m)) (fun i v => traceAt data 1 v i)
    (d*N) H (by
      intro K U bu su i _
      let f := fun v z => data z v i
      obtain ⟨R,br,ur,good⟩ := Grid.gridClosure s f bu (fun v => su (table v i))
      refine ⟨R,br,ur,?_⟩
      intro v
      have eq : traceAt data 1 v i = Grid.closure f v := by
        funext z;apply sameBool
        rfl
      rw [eq]
      exact good v)
  refine ⟨V,bv.relax ?_ Set.Subset.rfl,sv,fun v i => hit i (Finset.mem_univ _) v⟩
  simp only [Finset.card_univ,Fintype.card_fin]
  dsimp [N]
  nlinarith [Nat.zero_le (Fintype.card (Grid.Point s)*m)]

theorem nextLayer (s : Fin d → Nat) (data : Fin p → Grid.Point s → Fin m → Bool)
    (l : Nat) (H : Built x tr k S) (no : (fun _ => false)∈S)
    (table : ∀ v i, (fun z => data z v i)∈S) (prev : ∀ v i,traceAt data (l+1) v i∈S) :
    ∃ V, Built x tr (k+(d+4)*Fintype.card (Grid.Point s)*m) V ∧ S⊆V ∧
      ∀ v i, traceAt data (l+2) v i∈V := by
  let N := Fintype.card (Grid.Point s)
  let exc := fun v => excluded (traceAt data (l+1) v)
  obtain ⟨U,bu,su,ex⟩ := multiBatch (Finset.univ : Finset (Grid.Point s)) exc (3*m) H (by
    intro K V bv sv v _
    exact excludeBuild _ bv (sv no) (fun i => sv (prev v i)))
  let raw := fun (v : Grid.Point s) (i : Fin m) => conj (fun z => data z v i) (exc v i)
  obtain ⟨T,bt,ut,rr⟩ := batch (Finset.univ : Finset (Grid.Point s × Fin m))
    (fun a => raw a.1 a.2) 1 bu (by
      intro K V bv uv a _
      have made := Built.andGate bv (uv (su (table a.1 a.2))) (uv (ex a.1 (Finset.mem_univ _) a.2))
      exact ⟨_,made,Set.subset_insert _ _,Set.mem_insert _ _⟩)
  obtain ⟨V,bv,tv,hit⟩ := multiBatch (Finset.univ : Finset (Fin m)) (fun i v => traceAt data (l+2) v i)
    (d*N) bt (by
      intro K R br tr' i _
      obtain ⟨Z,bz,rz,allZ⟩ := Grid.gridClosure s (fun v => raw v i) br
        (fun v => tr' (rr (v,i) (Finset.mem_univ _)))
      refine ⟨Z,bz,rz,?_⟩
      intro v
      have same : traceAt data (l+2) v i = Grid.closure (fun u => raw u i) v := by
        funext z
        apply sameBool
        simp only [Reach,raw,conj,exc,excluded,traceAt,Bool.and_eq_true,decide_eq_true_eq]
      rw [same]
      exact allZ v)
  refine ⟨V,bv.relax ?_ Set.Subset.rfl,(su.trans ut).trans tv,fun v i => hit i (Finset.mem_univ _) v⟩
  simp only [Finset.card_univ,Fintype.card_prod,Fintype.card_fin,mul_one]
  dsimp [N]
  ring_nf <;> exact le_rfl

theorem allLayers (s : Fin d → Nat) (data : Fin p → Grid.Point s → Fin m → Bool)
    (H : Built x tr k S) (no : (fun _ => false)∈S) (table : ∀ v i, (fun z => data z v i)∈S) (L : Nat) :
    ∃ V, Built x tr (k+L*((d+4)*Fintype.card (Grid.Point s)*m)) V ∧ S⊆V ∧
      ∀ l, 0<l → l≤L → ∀ v i, traceAt data l v i∈V := by
  induction L with
  | zero => exact ⟨S,by simpa using H,Set.Subset.rfl,by omega⟩
  | succ L ih =>
    obtain ⟨U,bu,su,prev⟩ := ih
    have step : ∃ V, Built x tr ((k+L*((d+4)*Fintype.card (Grid.Point s)*m))+
        (d+4)*Fintype.card (Grid.Point s)*m) V ∧ U⊆V ∧ ∀ v i, traceAt data (L+1) v i∈V := by
      cases L with
      | zero => exact firstLayer s data bu (fun v i => su (table v i))
      | succ l =>
        exact nextLayer s data l bu (su no) (fun v i => su (table v i)) (prev (l+1) (by omega) (by omega))
    obtain ⟨V,bv,uv,current⟩ := step
    refine ⟨V,by simpa [Nat.succ_mul,Nat.add_assoc] using bv,su.trans uv,?_⟩
    intro a ha le v i
    by_cases eq : a=L+1
    · simpa [eq] using current v i
    · exact uv (prev a ha (by omega) v i)

end DP
end PEqualNP.Outside.L_lib_1425

namespace PEqualNP.Outside.L_lib_1425
namespace DP
open StageNet
open scoped Classical
variable {r d m n p k : Nat} {x : Fin p → Finset (Fin n)} {tr : List (Col p)} {S : Set (Col p)}

lemma reachMono {Q : Type} [Preorder Q] (T : Q → Fin m → Bool) {v w : Q} (le : v≤w) (l : Nat) (i : Fin m) :
    Reach T l v i → Reach T l w i := by
  cases l with
  | zero => exact id
  | succ a =>
    cases a with
    | zero =>
      rintro ⟨u,h,lab⟩
      exact ⟨u,h.trans le,lab⟩
    | succ a =>
      rintro ⟨u,h,lab,pr⟩
      exact ⟨u,h.trans le,lab,pr⟩

noncomputable def dom (g : Fin r → Fin d) (A : Fin p → Finset (Fin r)) (v : Box g) : Col p :=
  fun z => decide (v≤query g (A z))

lemma domination (g : Fin r → Fin d) (A : Fin p → Finset (Fin r)) (H : Built x tr k S)
    (yes : (fun _ => true) ∈ S)
    (threshold : ∀ j (t : Fin ((block g j).card+1)), (fun z => decide (t.val≤((A z)∩block g j).card))∈S) :
    ∃ U, Built x tr (k+Fintype.card (Box g)*d) U ∧ S⊆U ∧ ∀ v, dom g A v∈U := by
  obtain ⟨U,bu,su,hs⟩ := batch (Finset.univ : Finset (Box g)) (dom g A) d H (by
    intro K R br sr v _
    let f := fun (j : Fin d) (z : Fin p) => decide ((v j).val≤((A z)∩block g j).card)
    obtain ⟨Z,bz,rz,hh⟩ := allFold Finset.univ f br (sr yes) (fun j _ => sr (threshold j (v j)))
    refine ⟨Z,by simpa using bz,rz,?_⟩
    have eq : dom g A v = (fun z => decide (∀ j∈(Finset.univ : Finset (Fin d)), f j z=true)) := by
      funext z; apply Bool.eq_iff_iff.mpr
      simp only [dom,f,decide_eq_true_eq,Finset.mem_univ,forall_const]
      rfl
    rw [eq]
    convert hh using 1;funext z;apply Bool.eq_iff_iff.mpr;simp)
  exact ⟨U,by simpa using bu,su,fun v => hs v (Finset.mem_univ _)⟩

noncomputable def queryCol (g : Fin r → Fin d) (T : Fin p → Box g → Fin m → Bool)
    (A : Fin p → Finset (Fin r)) (l : Nat) (i : Fin m) : Col p :=
  fun z => decide (Reach (T z) l (query g (A z)) i)

lemma queryBank (g : Fin r → Fin d) (T : Fin p → Box g → Fin m → Bool)
    (A : Fin p → Finset (Fin r)) (L : Nat) (H : Built x tr k S) (no : (fun _ => false)∈S)
    (ds : ∀ v,dom g A v∈S) (rf : ∀ l,0<l → l≤L → ∀v i,traceAt T l v i∈S) :
    ∃ V, Built x tr (k+L*m*(2*Fintype.card (Box g))) V ∧ S⊆V ∧
       ∀ l,0<l → l≤L → ∀ i,queryCol g T A l i∈V := by
  let N := Fintype.card (Box g)
  let goal := fun (a : Fin L × Fin m) => queryCol g T A (a.1.val+1) a.2
  obtain ⟨V,bv,sv,allV⟩ := batch (Finset.univ : Finset (Fin L × Fin m)) goal (2*N) H (by
    intro K R br sr a _
    let f := fun (v : Box g) => conj (traceAt T (a.1.val+1) v a.2) (dom g A v)
    obtain ⟨U,bu,ru,fU⟩ := batch (Finset.univ : Finset (Box g)) f 1 br (by
      intro M W bw rw' v _
      have hR := sr (rf (a.1.val+1) (by omega) (by have := a.1.isLt;omega) v a.2)
      have and := Built.andGate bw (rw' hR) (rw' (sr (ds v)))
      exact ⟨_,and,Set.subset_insert _ _,Set.mem_insert _ _⟩)
    obtain ⟨Z,bz,uz,zg⟩ := anyFold Finset.univ f bu (ru (sr no)) fU
    refine ⟨Z,bz.relax ?_ Set.Subset.rfl,ru.trans uz,?_⟩
    · simp only [Finset.card_univ,mul_one];dsimp [N];omega
    · have eq : goal a = (fun z => decide (∃ v∈(Finset.univ : Finset (Box g)), f v z=true)) := by
        funext z;apply Bool.eq_iff_iff.mpr
        simp only [goal,queryCol,f,conj,traceAt,dom,Finset.mem_univ,true_and,decide_eq_true_eq,Bool.and_eq_true]
        constructor
        · intro h;exact ⟨query g (A z),h,le_rfl⟩
        · rintro ⟨v,rv,le⟩;exact reachMono (T z) le _ _ rv
      rw [eq]
      exact zg)
  refine ⟨V,by simpa [N] using bv,sv,?_⟩
  intro l pos le i
  let a : Fin L := ⟨l-1,by omega⟩
  have := allV (a,i) (Finset.mem_univ _)
  simpa [goal,a,show l-1+1=l by omega] using this

end DP
end PEqualNP.Outside.L_lib_1425

namespace PEqualNP.Outside.L_lib_1425
namespace BlockBank
open StageNet
open scoped Classical

noncomputable def counter {r d p : Nat} (g : Fin r → Fin d) (A : Fin p → Finset (Fin r))
    (I : Finset (Fin r)) (j : Fin d) (t : Nat) : Col p :=
  fun z => decide (t ≤ (I.filter (fun a => a ∈ A z ∧ g a = j)).card)

theorem sameBlockStep {r d p : Nat} (g : Fin r → Fin d) (A : Fin p → Finset (Fin r))
    {I : Finset (Fin r)} {a : Fin r} (fresh : a ∉ I) (t : Nat) :
    counter g A (insert a I) (g a) t =
      disj (counter g A I (g a) t)
        (conj (fun z => decide (a ∈ A z)) (counter g A I (g a) (t-1))) := by
  funext z
  apply Bool.eq_iff_iff.mpr
  by_cases h : a ∈ A z
  · have nf : a ∉ I.filter (fun u => u ∈ A z ∧ g u = g a) := by
      intro hh; exact fresh (Finset.mem_filter.mp hh).1
    simp [counter,disj,conj,Finset.filter_insert,h,Finset.card_insert_of_notMem nf, Bool.or_eq_true]
    omega
  · simp [counter,disj,conj,Finset.filter_insert,h]

theorem otherBlockStep {r d p : Nat} (g : Fin r → Fin d) (A : Fin p → Finset (Fin r))
    (I : Finset (Fin r)) (a : Fin r) (j : Fin d) (hj : g a ≠ j) (t : Nat) :
    counter g A (insert a I) j t = counter g A I j t := by
  funext z
  simp [counter,Finset.filter_insert,hj]

theorem thresholdBank {r d p n : Nat} (g : Fin r → Fin d) (A : Fin p → Finset (Fin r))
    {x : Fin p → Finset (Fin n)} {tr : List (Col p)} {k : Nat} {S : Set (Col p)}
    (built : Built x tr k S) (hfalse : (fun _ => false) ∈ S)
    (htrue : (fun _ => true) ∈ S) (hbits : ∀ a : Fin r, (fun z => decide (a ∈ A z)) ∈ S) :
    ∃ T, Built x tr (k+2*(r+1)^2) T ∧ S⊆T ∧ ∀ (j : Fin d) (t : Fin ((block g j).card+1)),
      (fun z => decide (t.val ≤ ((A z) ∩ block g j).card)) ∈ T := by
  classical
  have go (I : Finset (Fin r)) :
      ∃ U, Built x tr (k+I.card*((r+1)*2)) U ∧ S⊆U ∧
        ∀ (j : Fin d) (t : Fin (r+1)), counter g A I j t.val ∈ U := by
    induction I using Finset.induction_on with
    | empty =>
      refine ⟨S,by simpa using built,Set.Subset.rfl,?_⟩
      intro j t
      by_cases ht : t.val=0
      · have eq : counter g A ∅ j t.val = (fun _ => true) := by
          funext z; simp [counter,ht]
        rw [eq]; exact htrue
      · have hp : ¬ t.val ≤ 0 := by omega
        have eq : counter g A ∅ j t.val = (fun _ => false) := by
          funext z; simp [counter,hp]
        rw [eq]; exact hfalse
    | @insert a I fresh ih =>
      obtain ⟨U,hU,sub,old⟩ := ih
      let new : Fin (r+1) → Col p := fun t => counter g A (insert a I) (g a) t.val
      obtain ⟨V,hV,uv,hnew⟩ := batch (Finset.univ : Finset (Fin (r+1))) new 2 hU
        (by
          intro K T hT cu t ht
          let prev : Fin (r+1) := ⟨t.val-1, by have := t.isLt; omega⟩
          let c0 := counter g A I (g a) t.val
          let c1 := counter g A I (g a) prev.val
          let x0 : Col p := fun z => decide (a ∈ A z)
          have h1 := hT.andGate (cu (sub (hbits a))) (cu (old (g a) prev))
          have h2 := h1.orGate (Set.mem_insert_of_mem _ (cu (old (g a) t)))
            (Set.mem_insert (conj x0 c1) T)
          refine ⟨insert (disj c0 (conj x0 c1)) (insert (conj x0 c1) T),?_,
            (Set.subset_insert ..).trans (Set.subset_insert ..),?_⟩
          · exact h2
          · apply Set.mem_insert_iff.mpr
            exact Or.inl (sameBlockStep g A fresh t.val))
      refine ⟨V,?_,sub.trans uv,?_⟩
      · simpa [Finset.card_insert_of_notMem fresh, Nat.succ_mul, Nat.add_assoc] using hV
      · intro j t
        by_cases hj : g a = j
        · subst j
          exact hnew t (Finset.mem_univ _)
        · rw [otherBlockStep g A I a j hj t.val]
          exact uv (old j t)
  obtain ⟨T,hT,sub,all⟩ := go Finset.univ
  refine ⟨T, hT.relax ?_ Set.Subset.rfl, sub, ?_⟩
  · simp only [Finset.card_univ,Fintype.card_fin]
    nlinarith
  · intro j t
    have bc : (block g j).card ≤ r := by simpa using Finset.card_le_univ (block g j)
    let tt : Fin (r+1) := ⟨t.val,by have := t.isLt; omega⟩
    have eq : (fun z => decide (t.val ≤ ((A z) ∩ block g j).card)) =
        counter g A Finset.univ j tt.val := by
      funext z
      have hset : (A z) ∩ block g j = Finset.univ.filter (fun a => a∈A z ∧ g a=j) := by
        ext a
        simp [block]
      simp [counter,hset,tt]
    exact eq ▸ all j tt
end BlockBank
end PEqualNP.Outside.L_lib_1425

namespace PEqualNP.Outside.L_lib_1425
namespace DP
open StageNet
open scoped Classical

def prepCost (r d N m K : Nat) :=
  2*(r+1)^2 + N*d + (K+1)*((d+4)*N*m) + (K+1)*m*(2*N) + m

noncomputable def badCol {r d m p : Nat} {g : Fin r → Fin d} (T : Fin p → Box g → Fin m → Bool)
    (K : Nat) : Col p := fun z => decide (∃ i,Reach (T z) (K+1) ⊤ i)

theorem prepare {r d m p n : Nat} (g : Fin r → Fin d) (data : Fin p → Box g → Fin m → Bool)
    (words : Fin p → Finset (Fin r)) (x : Fin p → Finset (Fin n))
    (ht : ∀ v i, (fun z => data z v i)∈base x)
    (hb : ∀ a, (fun z => decide (a∈words z))∈base x) (K : Nat) :
    ∃ S, Built x [] (prepCost r d (Fintype.card (Box g)) m K) S ∧ base x⊆S ∧ badCol data K∈S ∧
      ∀ l, 0<l → l≤K+1 → ∀ i, queryCol g data words l i∈S := by
  let f : (fun _ : Fin p => false) ∈ base x := Or.inl rfl
  let t : (fun _ : Fin p => true) ∈ base x := Or.inr (Or.inl rfl)
  obtain ⟨A,ba,sa,threshold⟩ := BlockBank.thresholdBank g words (Built.start (x:=x)) f t hb
  obtain ⟨B,bb,ab,doms⟩ := domination g words ba (sa t) threshold
  obtain ⟨C,bc,bcSub,layer⟩ := allLayers (fun j => (block g j).card) data bb (ab (sa f)) (fun v i => ab (sa (ht v i))) (K+1)
  obtain ⟨D,bd,cd,q⟩ := queryBank g data words (K+1) bc (bcSub (ab (sa f))) (fun v => bcSub (doms v)) layer
  let v := fun i => traceAt data (K+1) (⊤ : Box g) i
  obtain ⟨E,be,de,flag⟩ := anyFold (Finset.univ : Finset (Fin m)) v bd
    (cd (bcSub (ab (sa f)))) (fun i _ => cd (layer _ (by omega) (le_refl _) _ i))
  refine ⟨E,by simpa [prepCost] using be,(((sa.trans ab).trans bcSub).trans cd).trans de,?_,fun l hl hk i => de (q l hl hk i)⟩
  have eq : badCol data K = fun z => decide (∃i∈(Finset.univ : Finset (Fin m)),v i z=true) := by
    funext z
    apply sameBool
    simp only [Finset.mem_univ,true_and,v,traceAt,decide_eq_true_eq]
  rw [eq]
  convert flag using 1
  funext z
  apply sameBool
  rfl

theorem budget (r d N m K : Nat) :
    prepCost r d N m K + 5*(r+1)^2 + 5*(K+2)*(m+1) ≤
      8*(r+1)^2+32*(d+2)*(N+1)*(m+1)*(K+2) := by
  unfold prepCost
  ring_nf
  omega

end DP
end PEqualNP.Outside.L_lib_1425

namespace PEqualNP.Outside.L_lib_1425
namespace Input
open StageNet
open scoped Classical

noncomputable def square {N m : Nat} (f : Fin N → Fin m → Bool) (u : Fin (N*m)) : Bool :=
  f (finProdFinEquiv.symm u).1 (finProdFinEquiv.symm u).2

theorem square_list {N m : Nat} (f : Fin N → Fin m → Bool) :
    List.ofFn (square f) = (List.ofFn (fun w : Fin N => List.ofFn (f w))).flatten := by
  rw [List.ofFn_mul]
  congr 1
  apply congrArg List.ofFn
  funext w
  apply congrArg List.ofFn
  funext i
  have h : (⟨w.val * m + i.val, by
      have hh := (finProdFinEquiv (w,i)).isLt
      simpa [finProdFinEquiv, Nat.mul_comm, Nat.add_comm] using hh⟩ : Fin (N*m)) =
      finProdFinEquiv (w,i) := by
    apply Fin.ext
    simp [finProdFinEquiv,Nat.mul_comm,Nat.add_comm]
  change square f ⟨w.val*m+i.val,_⟩ = f w i
  rw [h]
  simp [square]

theorem samples {r d m : Nat} (g : Fin r → Fin d) (index : Fin (Fintype.card (Box g)) ≃ Box g) :
    ∃ (p : Nat) (x : Fin p → Finset (Fin (Fintype.card (Box g)*m+r)))
      (tables : Fin p → Box g → Fin m → Bool) (words : Fin p → Finset (Fin r)),
      (∀ v i, (fun z => tables z v i) ∈ base x) ∧
      (∀ a, (fun z => decide (a ∈ words z)) ∈ base x) ∧
      ∀ (T : Box g → Fin m → Bool) (X : Finset (Fin r)), ∃ z,
        tables z = T ∧ words z = X ∧ raw x z =
        (List.ofFn (fun w : Fin (Fintype.card (Box g)) => List.ofFn (fun i : Fin m => T (index w) i))).flatten ++
          Bits X ++ [false,true] := by
  classical
  let Data := (Box g → Fin m → Bool) × Finset (Fin r)
  let e : Data ≃ Fin (Fintype.card Data) := Fintype.equivFin Data
  let T := fun z : Fin (Fintype.card Data) => (e.symm z).1
  let W := fun z : Fin (Fintype.card Data) => (e.symm z).2
  let f := fun z : Fin (Fintype.card Data) => Fin.append
    (square (fun w => T z (index w))) (fun a => decide (a∈W z))
  let x := fun z : Fin (Fintype.card Data) => Finset.univ.filter (fun a => f z a = true)
  have mem (z : Fin (Fintype.card Data)) (a) : decide (a∈x z) = f z a := by
    simp [x]
  refine ⟨_,x,T,W,?_,?_,?_⟩
  · intro v i
    refine Or.inr (Or.inr ⟨(finProdFinEquiv (index.symm v,i)).castAdd r,?_⟩)
    funext z
    simp [sing,mem,f,Fin.append_left,square]
  · intro a
    refine Or.inr (Or.inr ⟨Fin.natAdd (Fintype.card (Box g)*m) a,?_⟩)
    funext z
    simp [sing,mem,f,Fin.append_right]
  · intro table word
    refine ⟨e (table,word),by simp [T],by simp [W],?_⟩
    change (List.ofFn (fun a => decide (a ∈ x (e (table,word))))) ++ [false,true] = _
    simp only [mem]
    rw [show List.ofFn (f (e (table,word))) =
        List.ofFn (square (fun w => T (e (table,word)) (index w))) ++
          List.ofFn (fun a => decide (a∈ W (e (table,word)))) by
      change List.ofFn (Fin.append _ _) = _
      rw [List.ofFn_add]
      simp [Fin.append_right]]
    simp only [T,W,Equiv.symm_apply_apply]
    rw [square_list]
    rfl
end Input
end PEqualNP.Outside.L_lib_1425

namespace PEqualNP.Outside.L_lib_1425
namespace DP
open StageNet
open scoped Classical
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

noncomputable def tableList {r d m : Nat} {g : Fin r → Fin d} (index : Fin (Fintype.card (Box g)) ≃ Box g)
    (T : Box g → Fin m → Bool) : List Bool :=
  (List.ofFn (fun w : Fin (Fintype.card (Box g)) => List.ofFn (fun i : Fin m => T (index w) i))).flatten

theorem tableListLength {r d m : Nat} {g : Fin r → Fin d} (index : Fin (Fintype.card (Box g)) ≃ Box g)
    (T : Box g → Fin m → Bool) : (tableList index T).length=Fintype.card (Box g)*m := by
  simp [tableList,List.length_flatten,List.sum_ofFn]

def Limit (r b : Nat) := min (2^b) (r+1)
def SizeBound (r d N m b : Nat) := 8*(r+1)^2+32*(d+2)*(N+1)*(m+1)*(Limit r b+2)

def Selection {r d m : Nat} (b : Nat) (g : Fin r → Fin d) := ∀ {n p k : Nat}
    (x : Fin p → Finset (Fin n)) (data : Fin p → Box g → Fin m → Bool)
    (words : Fin p → Finset (Fin r)) (S : Set (Col p)), Built x [] k S →
    (fun _ => false)∈S → (fun _ => true)∈S →
    (∀ l, 0<l → l≤Limit r b+1 → ∀ i, queryCol g data words l i∈S) →
    ∃ tr V, tr.length ≤ b ∧ Built x tr (k+5*(r+1)^2+5*(Limit r b+2)*(m+1)) V ∧
      S⊆V ∧ ∃ F : Fin m → Col p, (∀ i,F i∈V) ∧ ∀ z, (¬ ∃ i,Reach (data z) (Limit r b+1) ⊤ i) →
        ∀ i, data z (query g (words z)) i = true → ∀ j, F j z = decide (i=j)

theorem uniform {r d m b : Nat} (g : Fin r → Fin d)
    (index : Fin (Fintype.card (Box g)) ≃ Box g) (sel : Selection (m:=m) b g) :
    ∃ (D : Circuit) (out : Fin m → Nat), Valid (Fintype.card (Box g)*m+r) D ∧
      (∀ j, out j < Fintype.card (Box g)*m+r+2+D.size) ∧
      PEqualNP.NotBracket.notCount D ≤ b ∧ D.size-PEqualNP.NotBracket.notCount D ≤ SizeBound r d (Fintype.card (Box g)) m b ∧
      ∀ (T : Box g → Fin m → Bool) (A : Finset (Fin r)),
        (D.eval (tableList index T ++ Bits A ++ [false,true]) = false ↔ ¬∃ i,Reach T (Limit r b+1) ⊤ i) ∧
        ((¬∃ i,Reach T (Limit r b+1) ⊤ i) → ∀ i,T (query g A) i=true → ∀ j,
          (D.wires (tableList index T ++ Bits A ++ [false,true])).getD (out j) false = decide (i=j)) := by
  classical
  let N := Fintype.card (Box g)
  let K := Limit r b
  obtain ⟨p,x,tables,words,ht,hb,samples⟩ := Input.samples (m:=m) g index
  obtain ⟨S,bs,baseS,bad,qr⟩ := prepare g tables words x ht hb K
  obtain ⟨tr,V,len,bv,sv,F,fmem,good⟩ := sel x tables words S bs (baseS (Or.inl rfl)) (baseS (Or.inr (Or.inl rfl))) qr
  obtain ⟨gs,fan,back,size,trace,sig⟩ := bv
  obtain ⟨root,validRoot,rootEq⟩ := sig _ (sv bad)
  choose tap valid valEq using fun i => sig _ (fmem i)
  have hl := congrArg List.length trace
  simp only [StageNet.trace,List.length_map] at hl
  have inv := (countIx gs).trans hl
  let D : Circuit := ⟨gs,root⟩
  refine ⟨D,tap,⟨fan,back,validRoot⟩,valid,inv.le.trans len,?_,?_⟩
  · exact (Nat.sub_le _ _).trans (size.trans (budget r d N m K))
  · intro T A
    obtain ⟨z,zt,zw,rawEq⟩ := samples T A
    change raw x z = tableList index T ++ Bits A ++ [false,true] at rawEq
    rw [←rawEq]
    have flag := congrFun rootEq z
    change D.eval (raw x z) = decide (∃ i,Reach (tables z) (K+1) ⊤ i) at flag
    rw [zt] at flag
    refine ⟨?_,?_⟩
    · rw [flag]
      exact @decide_eq_false_iff_not _ _
    · intro hn i hit j
      have ok := good z (by simpa [zt] using hn) i (by simpa only [zt,zw] using hit) j
      exact (congrFun (valEq j) z).trans ok

end DP
end PEqualNP.Outside.L_lib_1425

namespace PEqualNP.Outside.L_lib_1425
namespace GridLift

def firstMembers {r : Nat} (s : Finset (Fin r)) (k : Nat) : Finset (Fin r) :=
  ((s.sort (· ≤ ·)).take k).toFinset

theorem prefix_sub {r : Nat} (s : Finset (Fin r)) (k : Nat) : firstMembers s k ⊆ s := by
  intro x hx
  exact (s.mem_sort (· ≤ ·)).mp ((List.take_sublist _ _).subset (List.mem_toFinset.mp hx))

theorem prefix_mono {r : Nat} (s : Finset (Fin r)) {i j : Nat} (le : i ≤ j) :
    firstMembers s i ⊆ firstMembers s j := by
  intro x hx
  apply List.mem_toFinset.mpr
  exact (List.take_prefix_take_left (l:=s.sort (· ≤ ·)) le).subset (List.mem_toFinset.mp hx)

theorem prefix_card {r : Nat} (s : Finset (Fin r)) (k : Nat) (cap : k ≤ s.card) :
    (firstMembers s k).card = k := by
  unfold firstMembers
  rw [List.toFinset_card_of_nodup]
  · simp [List.length_take,Nat.min_eq_left cap]
  · exact (Finset.sort_nodup _ _).sublist (List.take_sublist _ _)

def block {r d : Nat} (g : Fin r → Fin d) (j : Fin d) : Finset (Fin r) :=
  Finset.univ.filter (fun i => g i = j)

abbrev Grid {r d : Nat} (g : Fin r → Fin d) := (j : Fin d) → Fin ((block g j).card+1)

def counts {r d : Nat} (g : Fin r → Fin d) (X : Finset (Fin r)) : Grid g := fun j =>
  ⟨(X ∩ block g j).card, Nat.lt_succ_of_le (Finset.card_le_card Finset.inter_subset_right)⟩

def liftIn {r d : Nat} (g : Fin r → Fin d) (X : Finset (Fin r)) (v : Grid g) : Finset (Fin r) :=
  Finset.univ.biUnion (fun j => firstMembers (X ∩ block g j) (v j).val)

theorem liftIn_sub {r d : Nat} (g : Fin r → Fin d) (X : Finset (Fin r)) (v : Grid g) :
    liftIn g X v ⊆ X := by
  intro x hx
  obtain ⟨j,_,mem⟩ := Finset.mem_biUnion.mp hx
  exact (Finset.mem_inter.mp (prefix_sub _ _ mem)).1

theorem liftIn_mono {r d : Nat} (g : Fin r → Fin d) (X : Finset (Fin r)) {v w : Grid g}
    (le : v ≤ w) : liftIn g X v ⊆ liftIn g X w := by
  intro x hx
  obtain ⟨j,_,mem⟩ := Finset.mem_biUnion.mp hx
  exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,prefix_mono _ (le j) mem⟩

theorem liftIn_inter {r d : Nat} (g : Fin r → Fin d) (X : Finset (Fin r)) (v : Grid g)
    (j : Fin d) : liftIn g X v ∩ block g j = firstMembers (X ∩ block g j) (v j).val := by
  ext x
  constructor
  · intro hx
    obtain ⟨hu,hj⟩ := Finset.mem_inter.mp hx
    obtain ⟨k,_,hk⟩ := Finset.mem_biUnion.mp hu
    have hkj := (Finset.mem_inter.mp (prefix_sub _ _ hk)).2
    have kx : g x = k := (Finset.mem_filter.mp hkj).2
    have jx : g x = j := (Finset.mem_filter.mp hj).2
    have kj : k = j := kx.symm.trans jx
    exact (congrArg (fun z : Fin d => x ∈ firstMembers (X ∩ block g z) (v z).val) kj).mp hk
  · intro hx
    exact Finset.mem_inter.mpr ⟨Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,hx⟩,
      (Finset.mem_inter.mp (prefix_sub _ _ hx)).2⟩

theorem counts_liftIn {r d : Nat} (g : Fin r → Fin d) (X : Finset (Fin r)) (v : Grid g)
    (cap : v ≤ counts g X) : counts g (liftIn g X v) = v := by
  funext j
  apply Fin.ext
  change (liftIn g X v ∩ block g j).card = (v j).val
  rw [liftIn_inter]
  exact prefix_card _ _ (cap j)

theorem counts_lift {r d : Nat} (g : Fin r → Fin d) (v : Grid g) :
    counts g (liftIn g Finset.univ v) = v := by
  apply counts_liftIn
  intro j
  change (v j).val ≤ (Finset.univ ∩ block g j).card
  rw [Finset.univ_inter]
  exact Nat.le_of_lt_succ (v j).isLt

end GridLift
end PEqualNP.Outside.L_lib_1425

namespace PEqualNP.Outside.L_lib_1425
namespace Nec

open PEqualNP.CircuitLowerBounds

private def isNotOp : GateOp → Bool
  | GateOp.not => true
  | _ => false

private lemma decide_eq_not (op : GateOp) (inst : Decidable (op = GateOp.not)) :
    @decide (op = GateOp.not) inst = isNotOp op := by
  cases inst with
  | isTrue h => subst h; rfl
  | isFalse h =>
    cases op with
    | not => exact False.elim (h rfl)
    | and => rfl
    | or => rfl
    | mod _ => rfl
    | maj => rfl

private lemma decide_irrel (P : Prop) (d1 d2 : Decidable P) :
    @decide P d1 = @decide P d2 := by
  by_cases hp : P <;> simp [hp]

private def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private noncomputable def inp (n : Nat) (x : Finset (Fin n)) : List Bool :=
  List.ofFn (fun j : Fin n => @decide (j ∈ x) (Classical.propDecidable _)) ++ [false, true]

private noncomputable def wireVal (n : Nat) (C : Circuit) (x : Finset (Fin n)) (w : Nat) : Bool :=
  (C.wires (inp n x)).getD w false

private lemma wireVal_eq_foldl (n : Nat) (C : Circuit) (x : Finset (Fin n)) (w : Nat) :
    wireVal n C x w = (C.gates.foldl stepWire (inp n x)).getD w false := rfl

private lemma cdecide_true {P : Prop} (h : P) : @decide P (Classical.propDecidable P) = true :=
  @decide_eq_true P (Classical.propDecidable P) h

private lemma cdecide_false {P : Prop} (h : ¬P) : @decide P (Classical.propDecidable P) = false :=
  @decide_eq_false P (Classical.propDecidable P) h

private lemma of_cdecide_true {P : Prop} (h : @decide P (Classical.propDecidable P) = true) : P :=
  @of_decide_eq_true P (Classical.propDecidable P) h

private lemma getD_append_left {α : Type _} (l₁ l₂ : List α) (i : Nat) (d : α)
    (hi : i < l₁.length) : (l₁ ++ l₂).getD i d = l₁.getD i d := by
  induction l₁ generalizing i with
  | nil => cases hi
  | cons a l ih =>
    cases i with
    | zero => rfl
    | succ i =>
      exact ih i (Nat.lt_of_succ_lt_succ hi)

private lemma getD_append_right_eq {α : Type _} (l : List α) (a d : α) :
    (l ++ [a]).getD l.length d = a := by
  induction l with
  | nil => rfl
  | cons x xs ih => exact ih

private lemma getD_eq_getElem {α : Type _} (l : List α) (k : Nat) (d : α) (hk : k < l.length) :
    l.getD k d = l[k] := by
  induction l generalizing k with
  | nil => cases hk
  | cons a l ih =>
    cases k with
    | zero => rfl
    | succ k => exact ih k (Nat.lt_of_succ_lt_succ hk)

private lemma length_inp (n : Nat) (x : Finset (Fin n)) : (inp n x).length = n + 2 := by
  simp [inp]

private lemma getD_inp_lt (n : Nat) (x : Finset (Fin n)) (w : Nat) (hw : w < n) :
    (inp n x).getD w false = @decide (⟨w, hw⟩ ∈ x) (Classical.propDecidable _) := by
  unfold inp
  have hlen : w < (List.ofFn (fun j : Fin n => @decide (j ∈ x) (Classical.propDecidable _))).length := by
    simp [hw]
  rw [getD_append_left _ _ _ _ hlen, getD_eq_getElem _ _ _ hlen]
  simp

private lemma getD_inp_n (n : Nat) (x : Finset (Fin n)) : (inp n x).getD n false = false := by
  let xs := List.ofFn (fun j : Fin n => @decide (j ∈ x) (Classical.propDecidable _))
  have h : inp n x = (xs ++ [false]) ++ [true] := by simp [inp, xs]
  have hlen : n < (xs ++ [false]).length := by simp [xs]
  have hlen2 : xs.length = n := by simp [xs]
  rw [h, getD_append_left _ _ _ _ hlen]
  have h1 := getD_append_right_eq xs false false
  rw [hlen2] at h1
  exact h1

private lemma getD_inp_n1 (n : Nat) (x : Finset (Fin n)) : (inp n x).getD (n + 1) false = true := by
  let xs := List.ofFn (fun j : Fin n => @decide (j ∈ x) (Classical.propDecidable _))
  have h : inp n x = (xs ++ [false]) ++ [true] := by simp [inp, xs]
  have hlen : (xs ++ [false]).length = n + 1 := by simp [xs]
  rw [h]
  have h1 := getD_append_right_eq (xs ++ [false]) true false
  rw [hlen] at h1
  exact h1

private lemma length_foldl_stepWire (gs : List Gate) (v : List Bool) :
    (gs.foldl stepWire v).length = v.length + gs.length := by
  induction gs generalizing v with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

private lemma getD_foldl_stepWire_of_lt (gs : List Gate) (v : List Bool) (i : Nat)
    (hi : i < v.length) : (gs.foldl stepWire v).getD i false = v.getD i false := by
  induction gs generalizing v with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hi' : i < (stepWire v g).length := by
      simp only [stepWire, List.length_append, List.length_singleton]
      omega
    rw [ih (stepWire v g) hi']
    exact getD_append_left v _ i false hi

private lemma map_eq_of_forall {α β : Type _} (l : List α) (f g : α → β)
    (h : ∀ a ∈ l, f a = g a) : l.map f = l.map g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons]
    rw [h a (List.mem_cons_self), ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]

private lemma getD_foldl_at (gs : List Gate) (v : List Bool) (k : Nat) (hk : k < gs.length)
    (hRB : ∀ i ∈ gs[k].inputs, i < v.length + k) :
    (gs.foldl stepWire v).getD (v.length + k) false =
      gs[k].op.eval (gs[k].inputs.map fun i => (gs.foldl stepWire v).getD i false) := by
  induction gs generalizing v k with
  | nil => cases hk
  | cons g gs ih =>
    cases k with
    | zero =>
      simp only [List.foldl_cons, Nat.add_zero, List.getElem_cons_zero]
      have hlen : v.length < (stepWire v g).length := by
        simp [stepWire]
      rw [getD_foldl_stepWire_of_lt gs (stepWire v g) v.length hlen]
      simp only [stepWire, getD_append_right_eq]
      congr 1
      apply map_eq_of_forall
      intro i hi
      have hiv : i < v.length := by
        have := hRB i hi
        omega
      have hiv' : i < (v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]).length := by
        simp; omega
      rw [getD_foldl_stepWire_of_lt gs _ i hiv', getD_append_left v _ i false hiv]
    | succ k =>
      simp only [List.foldl_cons, List.getElem_cons_succ]
      have hlen : (stepWire v g).length = v.length + 1 := by
        simp [stepWire]
      have heq : v.length + (k + 1) = (stepWire v g).length + k := by omega
      rw [heq]
      apply ih (stepWire v g) k (Nat.lt_of_succ_lt_succ hk)
      intro i hi
      have := hRB i hi
      omega

private lemma wireVal_eval_at_gate (n : Nat) (C : Circuit)
    (hRB : PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) C)
    (x : Finset (Fin n)) (k : Nat) (hk : k < C.gates.length) :
    wireVal n C x (n + 2 + k) =
      C.gates[k].op.eval (C.gates[k].inputs.map fun i => wireVal n C x i) := by
  unfold wireVal Circuit.wires
  have hv : (inp n x).length = n + 2 := length_inp n x
  conv_lhs => rw [← hv]
  apply getD_foldl_at C.gates (inp n x) k hk
  intro i hi
  rw [hv]
  have h1 := hRB k hk i
  unfold PEqualNP.MetaComplexity.NestedCover.gateAt at h1
  rw [getD_eq_getElem C.gates k _ hk] at h1
  exact h1 hi

private def isNotGateList (gs : List Gate) (k : Nat) : Bool :=
  if hk : k < gs.length then isNotOp gs[k].op else false

private def B_cntList (gs : List Gate) : Nat → Nat
  | 0 => 0
  | k + 1 => B_cntList gs k + if isNotGateList gs k then 1 else 0

private lemma B_cntList_cons (g : Gate) (gs : List Gate) (k : Nat) :
    B_cntList (g :: gs) (k + 1) = (if isNotOp g.op then 1 else 0) + B_cntList gs k := by
  induction k with
  | zero =>
    simp [B_cntList, isNotGateList]
  | succ k ih =>
    change B_cntList (g :: gs) (k + 1) + (if isNotGateList (g :: gs) (k + 1) then 1 else 0) =
      (if isNotOp g.op then 1 else 0) + (B_cntList gs k + if isNotGateList gs k then 1 else 0)
    rw [ih]
    have hnot : isNotGateList (g :: gs) (k + 1) = isNotGateList gs k := by
      unfold isNotGateList
      by_cases hk : k < gs.length
      · have hk' : k + 1 < (g :: gs).length := by simp [hk]
        simp [hk, hk']
      · have hk' : ¬(k + 1 < (g :: gs).length) := by simp [hk]
        simp [hk, hk']
    rw [hnot]
    omega

private lemma B_cntList_length (gs : List Gate) :
    B_cntList gs gs.length = (gs.filter fun g => isNotOp g.op).length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.length_cons, B_cntList_cons, List.filter_cons]
    cases h : isNotOp g.op <;> simp [ih] <;> omega

private lemma notCount_eq_filter_isNotOp (C : Circuit) :
    PEqualNP.NotBracket.notCount C = (C.gates.filter fun g => isNotOp g.op).length := by
  unfold PEqualNP.NotBracket.notCount
  congr 1
  apply congrArg (fun f => C.gates.filter f)
  funext g
  exact decide_eq_not g.op _

private noncomputable def V (n : Nat) (C : Circuit) (x : Finset (Fin n)) : Nat → Nat
  | 0 => 0
  | k + 1 =>
    if isNotGateList C.gates k then
      2 * V n C x k + if wireVal n C x (n + 2 + k) then 1 else 0
    else
      V n C x k

private lemma V_lt_pow (n : Nat) (C : Circuit) (x : Finset (Fin n)) (k : Nat) :
    V n C x k < 2 ^ B_cntList C.gates k := by
  induction k with
  | zero =>
    simp [V, B_cntList]
  | succ k ih =>
    simp only [V, B_cntList]
    cases h : isNotGateList C.gates k
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      exact ih
    · simp only [↓reduceIte]
      rw [Nat.pow_succ]
      cases wireVal n C x (n + 2 + k) <;> simp <;> omega

private lemma all_id_mono {α : Type _} (l : List α) (f g : α → Bool)
    (h : ∀ a ∈ l, f a = true → g a = true) :
    (l.map f).all id = true → (l.map g).all id = true := by
  induction l with
  | nil => intro _; rfl
  | cons a l ih =>
    simp only [List.map_cons, List.all_cons, id_eq, Bool.and_eq_true]
    intro ⟨ha, hl⟩
    exact ⟨h a (List.mem_cons_self) ha, ih (fun b hb => h b (List.mem_cons_of_mem _ hb)) hl⟩

private lemma any_id_mono {α : Type _} (l : List α) (f g : α → Bool)
    (h : ∀ a ∈ l, f a = true → g a = true) :
    (l.map f).any id = true → (l.map g).any id = true := by
  induction l with
  | nil => intro h0; cases h0
  | cons a l ih =>
    simp only [List.map_cons, List.any_cons, id_eq, Bool.or_eq_true]
    intro h0
    rcases h0 with ha | hl
    · exact Or.inl (h a (List.mem_cons_self) ha)
    · exact Or.inr (ih (fun b hb => h b (List.mem_cons_of_mem _ hb)) hl)

private lemma V_anti_and_mono_wires (n : Nat) (C : Circuit)
    (hFan : PEqualNP.MetaComplexity.FanInTwo C)
    (hRB : PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) C)
    {u v : Finset (Fin n)} (huv : u ⊆ v) :
    ∀ k ≤ C.gates.length,
      V n C v k ≤ V n C u k ∧
      (V n C v k = V n C u k → ∀ w < n + 2 + k, wireVal n C u w = true → wireVal n C v w = true) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨Nat.le_refl _, ?_⟩
    intro _ w hw huw
    rw [wireVal_eq_foldl] at huw ⊢
    have hlen_u : w < (inp n u).length := by rw [length_inp]; exact hw
    have hlen_v : w < (inp n v).length := by rw [length_inp]; exact hw
    rw [getD_foldl_stepWire_of_lt C.gates (inp n u) w hlen_u] at huw
    rw [getD_foldl_stepWire_of_lt C.gates (inp n v) w hlen_v]
    by_cases hwn : w < n
    · rw [getD_inp_lt n u w hwn] at huw
      rw [getD_inp_lt n v w hwn]
      have hmem_u : (⟨w, hwn⟩ : Fin n) ∈ u := of_cdecide_true huw
      exact cdecide_true (huv hmem_u)
    · by_cases hweq : w = n
      · subst hweq
        rw [getD_inp_n] at huw
        cases huw
      · have hweq1 : w = n + 1 := by omega
        subst hweq1
        exact getD_inp_n1 n v
  | succ k ih =>
    intro hk1
    have hk : k < C.gates.length := Nat.lt_of_succ_le hk1
    obtain ⟨ihLe, ihMono⟩ := ih (Nat.le_of_lt hk)
    have hgate_mem : C.gates[k] ∈ C.gates := List.getElem_mem hk
    have hgate_op := (hFan C.gates[k] hgate_mem).1
    have hrb_k : ∀ i ∈ C.gates[k].inputs, i < n + 2 + k := by
      intro i hi
      have h1 := hRB k hk i
      unfold PEqualNP.MetaComplexity.NestedCover.gateAt at h1
      rw [getD_eq_getElem C.gates k _ hk] at h1
      exact h1 hi
    have heval_u := wireVal_eval_at_gate n C hRB u k hk
    have heval_v := wireVal_eval_at_gate n C hRB v k hk
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hgate_op
    rcases hgate_op with hop | hop | hop
    · have hnot : isNotGateList C.gates k = false := by
        simp [isNotGateList, hk, hop, isNotOp]
      simp only [V, hnot, Bool.false_eq_true, ↓reduceIte]
      refine ⟨ihLe, ?_⟩
      intro hveq w hw huw
      by_cases hwk : w < n + 2 + k
      · exact ihMono hveq w hwk huw
      · have hweq : w = n + 2 + k := by omega
        subst hweq
        rw [heval_u, hop, GateOp.eval] at huw
        rw [heval_v, hop, GateOp.eval]
        exact all_id_mono C.gates[k].inputs (wireVal n C u) (wireVal n C v)
          (fun i hi => ihMono hveq i (hrb_k i hi)) huw
    · have hnot : isNotGateList C.gates k = false := by
        simp [isNotGateList, hk, hop, isNotOp]
      simp only [V, hnot, Bool.false_eq_true, ↓reduceIte]
      refine ⟨ihLe, ?_⟩
      intro hveq w hw huw
      by_cases hwk : w < n + 2 + k
      · exact ihMono hveq w hwk huw
      · have hweq : w = n + 2 + k := by omega
        subst hweq
        rw [heval_u, hop, GateOp.eval] at huw
        rw [heval_v, hop, GateOp.eval]
        exact any_id_mono C.gates[k].inputs (wireVal n C u) (wireVal n C v)
          (fun i hi => ihMono hveq i (hrb_k i hi)) huw
    · have hnot : isNotGateList C.gates k = true := by
        simp [isNotGateList, hk, hop, isNotOp]
      simp only [V, hnot, ↓reduceIte]
      by_cases hlt : V n C v k < V n C u k
      · constructor
        · cases wireVal n C v (n + 2 + k) <;> cases wireVal n C u (n + 2 + k) <;>
            simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
        · intro heq
          exfalso
          cases hv : wireVal n C v (n + 2 + k) <;> cases hu : wireVal n C u (n + 2 + k) <;>
            simp only [hv, hu, Bool.false_eq_true, ↓reduceIte] at heq <;> omega
      · have hveq : V n C v k = V n C u k := by omega
        have hbit : wireVal n C v (n + 2 + k) = true → wireVal n C u (n + 2 + k) = true := by
          intro hvtrue
          rw [heval_v, hop, GateOp.eval] at hvtrue
          rw [heval_u, hop, GateOp.eval]
          cases hins : C.gates[k].inputs with
          | nil =>
            simp
          | cons i0 rest =>
            simp only [hins, List.map_cons, List.headD_cons] at hvtrue ⊢
            cases hvi0 : wireVal n C v i0
            · cases hui0 : wireVal n C u i0
              · rfl
              · have hi0 : i0 < n + 2 + k := hrb_k i0 (by simp [hins])
                have hcontr := ihMono hveq i0 hi0 hui0
                rw [hvi0] at hcontr
                cases hcontr
            · rw [hvi0] at hvtrue
              cases hvtrue
        constructor
        · cases hv1 : wireVal n C v (n + 2 + k)
          · cases hu1 : wireVal n C u (n + 2 + k) <;> simp <;> omega
          · have hu1 := hbit hv1
            rw [hu1]
            simp [hveq]
        · intro hveq1 w hw huw
          by_cases hwk : w < n + 2 + k
          · exact ihMono hveq w hwk huw
          · have hweq : w = n + 2 + k := by omega
            subst hweq
            rw [huw] at hveq1
            cases hv1 : wireVal n C v (n + 2 + k)
            · rw [hv1] at hveq1
              simp at hveq1
              omega
            · rfl

private lemma inpOrdinary (n : Nat) (x : Finset (Fin n)) :
    inp n x = List.ofFn (fun j : Fin n => decide (j ∈ x)) ++ [false,true] := by
  unfold inp
  congr 1
  apply congrArg List.ofFn
  funext j
  exact decide_irrel _ _ _

private noncomputable def phase (n : Nat) (C : Circuit) (b : Nat)
    (bound : PEqualNP.NotBracket.notCount C ≤ b) (A : Finset (Fin n)) : Fin (2^b) :=
  ⟨V n C A C.gates.length, by
    apply lt_of_lt_of_le (V_lt_pow n C A C.gates.length)
    apply Nat.pow_le_pow_right (by decide)
    rwa [B_cntList_length, ← notCount_eq_filter_isNotOp]⟩

end Nec
end PEqualNP.Outside.L_lib_1425

namespace PEqualNP.Outside.L_lib_1425
namespace Nec
open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_lib_1425

theorem reach_witness {Q : Type} [Preorder Q] {m c n : Nat}
    (T : Q → Fin m → Bool) (ph : Q → Fin (2^c)) (sz : Q → Nat)
    (strict : ∀ u v, u ≤ v → ∀ i j, T u i = true → T v j = true → i ≠ j →
      ph v < ph u ∧ sz u < sz v) {v : Q} {i : Fin m} (ok : Reach T n v i) :
    ∃ u ≤ v, T u i = true ∧ n+(ph u).val ≤ 2^c ∧ n ≤ sz u+1 := by
  induction n generalizing v i with
  | zero => exact False.elim ok
  | succ n ih =>
    cases n with
    | zero =>
      obtain ⟨u,le,ht⟩ := ok
      exact ⟨u,le,ht,by have := (ph u).isLt; omega,by omega⟩
    | succ n =>
      obtain ⟨u,le,ht,j,ne,path⟩ := ok
      obtain ⟨x,xle,htx,b1,b2⟩ := ih path
      obtain ⟨hp,hs⟩ := strict x u xle j i htx ht ne
      have hp' : (ph u).val < (ph x).val := hp
      exact ⟨u,le,ht,by omega,by omega⟩

theorem necessary {r d m b : Nat} (g : Fin r → Fin d) (T : Box g → Fin m → Bool)
    (pos : Possible b (fun X i => T (query g X) i = true)) :
    ¬ ∃ i, Reach T (min (2^b) (r+1)+1) ⊤ i := by
  classical
  obtain ⟨D,out,⟨fan,back,_⟩,valid,inv,eval⟩ := pos
  let lift := fun v : Box g => GridLift.liftIn g Finset.univ v
  let ph := fun v : Box g => phase r D b inv (lift v)
  have behave (x : Box g) (i : Fin m) (hit : T x i = true) (j : Fin m) :
      wireVal r D (lift x) (out j) = decide (i=j) := by
    have cnt : query g (lift x) = x := GridLift.counts_lift g x
    have own := eval (lift x) i (by simpa [cnt] using hit) j
    simpa only [wireVal,inpOrdinary,Bits] using own
  have strict : ∀ u v : Box g, u ≤ v → ∀ i j : Fin m, T u i = true → T v j = true → i ≠ j →
      ph v < ph u ∧ (lift u).card < (lift v).card := by
    intro u v le i j hi hj ne
    have sub : lift u ⊆ lift v := GridLift.liftIn_mono g Finset.univ le
    have both := V_anti_and_mono_wires r D fan back sub D.gates.length (le_refl _)
    have lo : ph v ≤ ph u := both.1
    have ineq : ph v ≠ ph u := by
      intro he
      have eqV := congrArg Fin.val he
      have rises := both.2 eqV (out i) (valid i)
      have before : wireVal r D (lift u) (out i) = true := by simp [behave u i hi i]
      have after := rises before
      rw [behave v j hj i] at after
      exact ne (of_decide_eq_true after).symm
    refine ⟨lt_of_le_of_ne lo ineq,Finset.card_lt_card (lt_of_le_of_ne sub ?_)⟩
    intro eq
    apply ineq
    exact congrArg (phase r D b inv) eq.symm
  rintro ⟨i,path⟩
  obtain ⟨v,_,_,b1,b2⟩ := reach_witness T ph (fun v => (lift v).card) strict path
  have cap : (lift v).card ≤ r := by simpa using Finset.card_le_univ (lift v)
  omega

end Nec
end PEqualNP.Outside.L_lib_1425

namespace PEqualNP.Outside.L_lib_1425

theorem lab_query_iff {r d m : Nat} (g : Fin r → Fin d) (T : Box g → Fin m → Bool)
    (X : Finset (Fin r)) (i : Fin m) :
    (∃ v : Box g, (∀ j, (v j).val = (X ∩ block g j).card) ∧ T v i = true) ↔
      T (query g X) i = true := by
  constructor
  · rintro ⟨v,fields,hit⟩
    have eq : v = query g X := funext (fun j => Fin.ext (fields j))
    simpa [eq] using hit
  · intro hit
    exact ⟨query g X,fun _ => rfl,hit⟩

theorem possible_lab_iff {r d m b : Nat} (g : Fin r → Fin d) (T : Box g → Fin m → Bool) :
    Possible b (fun X i => ∃ v : Box g, (∀ j, (v j).val = (X ∩ block g j).card) ∧ T v i=true) ↔
    Possible b (fun X i => T (query g X) i = true) := by
  have heq : (fun (X : Finset (Fin r)) (i : Fin m) =>
      ∃ v : Box g, (∀ j, (v j).val = (X ∩ block g j).card) ∧ T v i=true) =
      (fun X i => T (query g X) i = true) := by
    funext X i
    exact propext (lab_query_iff g T X i)
  rw [heq]

end PEqualNP.Outside.L_lib_1425

namespace PEqualNP.Outside.L_lib_1425
namespace Hardwire
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open scoped Classical

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

theorem rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

def pinTable (P : List Bool) (r : Nat) (i : Fin (P.length+r+2)) : Fin (r+2) :=
  if h : i.val<P.length then
    if P.getD i.val false then ⟨r+1,by omega⟩ else ⟨r,by omega⟩
  else ⟨i.val-P.length,by have := i.isLt; omega⟩

theorem wireBound {n m w k : Nat} (π : Fin n → Fin m) (h : w<n+k) : wmap n m π w < m+k := by
  unfold wmap
  split
  · rename_i hi
    have := (π ⟨w,hi⟩).isLt
    omega
  · omega

theorem relValid {p r : Nat} (π : Fin (p+r+2) → Fin (r+2)) {D : Circuit} (hv : Valid (p+r) D) :
    Valid r (relabel (p+r+2) (r+2) π D) := by
  obtain ⟨hf,hb,ho⟩ := hv
  refine ⟨?_,?_,?_⟩
  · intro g hg
    obtain ⟨old,hm,rfl⟩ := List.mem_map.mp hg
    simpa [relGate] using hf old hm
  · intro j hj a ha
    have hjo : j < D.gates.length := by simpa [relabel] using hj
    have he : gateAt (relabel (p+r+2) (r+2) π D) j =
        relGate (p+r+2) (r+2) π (gateAt D j) := by
      unfold gateAt
      rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hjo]
      simp [relabel]
    rw [he] at ha
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp ha
    exact wireBound π (hb j hjo v hv)
  · have hh := wireBound π ho
    simpa [relabel,Circuit.size] using hh

theorem notCount_map {n m : Nat} (π : Fin n → Fin m) (D : Circuit) :
    PEqualNP.NotBracket.notCount (relabel n m π D) = PEqualNP.NotBracket.notCount D := by
  simp [PEqualNP.NotBracket.notCount,relabel,List.filter_map,Function.comp_def,relGate]
  apply congrArg List.length
  apply List.filter_congr
  intro g hg
  by_cases hn : g.op = GateOp.not <;> simp [hn]

theorem rel_input (P : List Bool) {r : Nat} (X : Finset (Fin r)) :
    Rel (P.length+r+2) (r+2) (pinTable P r) (P ++ Bits X ++ [false,true]) (Bits X ++ [false,true]) := by
  refine ⟨by simp [Bits,Nat.add_assoc],by simp [Bits]; omega,?_⟩
  intro w
  rw [List.append_assoc]
  by_cases hi : w<P.length
  · have hw : w < P.length+r+2 := by omega
    rw [List.getD_append _ _ _ _ hi]
    simp only [wmap,hw,dite_true,pinTable,hi]
    cases P.getD w false <;> simp [Bits]
  · have hh : wmap (P.length+r+2) (r+2) (pinTable P r) w = w-P.length := by
      unfold wmap
      split
      · simp [pinTable,hi]
      · omega
    rw [hh, List.getD_append_right _ _ _ _ (by omega : P.length ≤ w)]

theorem hardwire {p r m : Nat} (P : List Bool) (hp : P.length = p) (D : Circuit) (out : Fin m → Nat)
    (hD : Valid (p+r) D) (hout : ∀ j, out j < p+r+2+D.size) :
    ∃ (E : Circuit) (newOut : Fin m → Nat), Valid r E ∧ (∀ j, newOut j < r+2+E.size) ∧
      PEqualNP.NotBracket.notCount E = PEqualNP.NotBracket.notCount D ∧
      ∀ (X : Finset (Fin r)) j, (E.wires (Bits X ++ [false,true])).getD (newOut j) false =
        (D.wires (P ++ Bits X ++ [false,true])).getD (out j) false := by
  subst p
  let π := pinTable P r
  refine ⟨relabel _ _ π D, fun j => wmap _ _ π (out j), relValid π hD, ?_, notCount_map π D, ?_⟩
  · intro j
    have h := wireBound π (hout j)
    simpa [relabel,Circuit.size] using h
  · intro X j
    exact (rel_fold _ _ π D.gates _ _ (rel_input P X)).2.2 (out j)
end Hardwire
end PEqualNP.Outside.L_lib_1425

namespace PEqualNP.Outside.L_lib_1425
namespace ChainNet

open scoped Classical
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.NotBracket

section CircuitBasics

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

lemma wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

lemma wiresFrom_append (gs1 gs2 : List Gate) (w : List Bool) :
    wiresFrom (gs1 ++ gs2) w = wiresFrom gs2 (wiresFrom gs1 w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    rw [wiresFrom_cons, ih]
    simp
    omega

lemma getD_append_left {α : Type*} (l1 l2 : List α) (i : ℕ) (d : α) (hi : i < l1.length) :
    (l1 ++ l2).getD i d = l1.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_right {α : Type*} (l1 l2 : List α) (i : ℕ) (d : α) (hi : l1.length ≤ i) :
    (l1 ++ l2).getD i d = l2.getD (i - l1.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right hi]

lemma getD_ge_length {α : Type*} (l : List α) (i : ℕ) (d : α) (hi : l.length ≤ i) :
    l.getD i d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma getD_take {α : Type*} (l : List α) (m k : ℕ) (d : α) (hk : k < m) :
    (l.take m).getD k d = l.getD k d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hk]

lemma getD_drop {α : Type*} (l : List α) (m k : ℕ) (d : α) :
    (l.drop m).getD k d = l.getD (m + k) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

lemma getD_mem {α : Type*} (l : List α) (k : ℕ) (d : α) (hk : k < l.length) :
    l.getD k d ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  exact List.getElem_mem hk

lemma list_any_congr {α : Type*} (l : List α) (f g : α → Bool) (h : ∀ x ∈ l, f x = g x) :
    l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons a tl ih =>
    simp only [List.any_cons]
    rw [h a (List.mem_cons_self ..), ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

lemma wiresFrom_getD_lt (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < w.length) :
    (wiresFrom gs w).getD k false = w.getD k false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [wiresFrom_cons, ih]
    · exact getD_append_left _ _ k false hk
    · simp; omega

lemma gateAt_eq_getElem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

lemma notCount_nil (o : ℕ) : notCount ⟨[], o⟩ = 0 := rfl

lemma notCount_append (gs1 gs2 : List Gate) (o : ℕ) :
    notCount ⟨gs1 ++ gs2, o⟩ = notCount ⟨gs1, 0⟩ + notCount ⟨gs2, 0⟩ := by
  simp [notCount, List.filter_append]

lemma notCount_le_length (gs : List Gate) (o : ℕ) :
    notCount ⟨gs, o⟩ ≤ gs.length :=
  List.length_filter_le _ _

def nonNot (gs : List Gate) : ℕ := gs.length - notCount ⟨gs, 0⟩

lemma nonNot_nil : nonNot [] = 0 := rfl

lemma nonNot_append (gs1 gs2 : List Gate) :
    nonNot (gs1 ++ gs2) = nonNot gs1 + nonNot gs2 := by
  dsimp only [nonNot]
  rw [List.length_append, notCount_append]
  have h1 := notCount_le_length gs1 0
  have h2 := notCount_le_length gs2 0
  omega

lemma notCount_singleton_and (ins : List ℕ) : notCount ⟨[⟨GateOp.and, ins⟩], 0⟩ = 0 := by
  simp [notCount]

lemma notCount_singleton_or (ins : List ℕ) : notCount ⟨[⟨GateOp.or, ins⟩], 0⟩ = 0 := by
  simp [notCount]

lemma notCount_singleton_not (ins : List ℕ) : notCount ⟨[⟨GateOp.not, ins⟩], 0⟩ = 1 := by
  simp [notCount]

lemma nonNot_singleton_and (ins : List ℕ) : nonNot [⟨GateOp.and, ins⟩] = 1 := by
  simp [nonNot, notCount_singleton_and]

lemma nonNot_singleton_or (ins : List ℕ) : nonNot [⟨GateOp.or, ins⟩] = 1 := by
  simp [nonNot, notCount_singleton_or]

lemma nonNot_singleton_not (ins : List ℕ) : nonNot [⟨GateOp.not, ins⟩] = 0 := by
  simp [nonNot, notCount_singleton_not]

lemma fanInTwo_nil (o : ℕ) : FanInTwo ⟨[], o⟩ := by
  intro g hg; cases hg

lemma fanInTwo_append {gs1 gs2 : List Gate} {o : ℕ}
    (h1 : FanInTwo ⟨gs1, 0⟩) (h2 : FanInTwo ⟨gs2, 0⟩) :
    FanInTwo ⟨gs1 ++ gs2, o⟩ := by
  intro g hg
  rcases List.mem_append.mp hg with hg1 | hg2
  · exact h1 g hg1
  · exact h2 g hg2

lemma readsBack_nil (m o : ℕ) : ReadsBack m ⟨[], o⟩ := by
  intro j hj; cases hj

lemma readsBack_append {m : ℕ} {gs1 gs2 : List Gate} {o : ℕ}
    (h1 : ReadsBack m ⟨gs1, 0⟩) (h2 : ReadsBack (m + gs1.length) ⟨gs2, 0⟩) :
    ReadsBack m ⟨gs1 ++ gs2, o⟩ := by
  intro j hj i hi
  rw [gateAt_eq_getElem _ j hj] at hi
  by_cases hj1 : j < gs1.length
  · have hget : (gs1 ++ gs2)[j] = gs1[j] := List.getElem_append_left hj1
    rw [hget] at hi
    have h1' := h1 j hj1
    rw [gateAt_eq_getElem _ j hj1] at h1'
    exact h1' i hi
  · have hj1' : gs1.length ≤ j := Nat.le_of_not_lt hj1
    have hj2 : j - gs1.length < gs2.length := by
      simp only [List.length_append] at hj
      omega
    have hget : (gs1 ++ gs2)[j] = gs2[j - gs1.length] := List.getElem_append_right hj1'
    rw [hget] at hi
    have h2' := h2 (j - gs1.length) hj2
    rw [gateAt_eq_getElem _ (j - gs1.length) hj2] at h2'
    have hlt := h2' i hi
    omega

def inpVec {n : ℕ} (x : Finset (Fin n)) : List Bool :=
  List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false, true]

lemma inpVec_length {n : ℕ} (x : Finset (Fin n)) : (inpVec x).length = n + 2 := by
  simp [inpVec]

lemma inpVec_getD_fin {n : ℕ} (x : Finset (Fin n)) (i : Fin n) :
    (inpVec x).getD i.val false = decide (i ∈ x) := by
  dsimp only [inpVec]
  rw [getD_append_left _ _ i.val false (by simp [i.isLt])]
  simp [List.getD_eq_getElem?_getD, i.isLt]

lemma inpVec_getD_false {n : ℕ} (x : Finset (Fin n)) :
    (inpVec x).getD n false = false := by
  dsimp only [inpVec]
  rw [getD_append_right _ _ n false (by simp)]
  simp

lemma inpVec_getD_true {n : ℕ} (x : Finset (Fin n)) :
    (inpVec x).getD (n + 1) false = true := by
  dsimp only [inpVec]
  rw [getD_append_right _ _ (n + 1) false (by simp)]
  have hsub : n + 1 - n = 1 := by omega
  simp [hsub]

lemma bool_le_iff (a b : Bool) : a ≤ b ↔ (a = true → b = true) := by
  cases a <;> cases b <;> decide

lemma not_true_le_false (h : (true : Bool) ≤ false) : False := by
  have := (bool_le_iff true false).mp h rfl
  cases this

lemma inpVec_mono {n : ℕ} {u v : Finset (Fin n)} (huv : u ⊆ v) (k : ℕ) :
    (inpVec u).getD k false ≤ (inpVec v).getD k false := by
  by_cases hk1 : k < n
  · have hu := inpVec_getD_fin u ⟨k, hk1⟩
    have hv := inpVec_getD_fin v ⟨k, hk1⟩
    dsimp only at hu hv
    rw [hu, hv, bool_le_iff]
    intro h
    exact decide_eq_true (huv (of_decide_eq_true h))
  · by_cases hk2 : k = n
    · subst hk2; rw [inpVec_getD_false, inpVec_getD_false]
    · by_cases hk3 : k = n + 1
      · subst hk3; rw [inpVec_getD_true, inpVec_getD_true]
      · rw [getD_ge_length _ k false (by rw [inpVec_length]; omega)]
        rw [getD_ge_length _ k false (by rw [inpVec_length]; omega)]

lemma all_map_mono (l : List ℕ) (f g : ℕ → Bool) (h : ∀ i ∈ l, f i ≤ g i) :
    (l.map f).all id ≤ (l.map g).all id := by
  induction l with
  | nil => simp
  | cons a tl ih =>
    simp only [List.map_cons, List.all_cons, id_eq]
    have ha := h a (List.mem_cons_self ..)
    have htl := ih (fun i hi => h i (List.mem_cons_of_mem _ hi))
    cases hfa : f a <;> cases hga : g a <;>
      cases h1 : (tl.map f).all id <;> cases h2 : (tl.map g).all id <;> simp_all

lemma any_map_mono (l : List ℕ) (f g : ℕ → Bool) (h : ∀ i ∈ l, f i ≤ g i) :
    (l.map f).any id ≤ (l.map g).any id := by
  induction l with
  | nil => simp
  | cons a tl ih =>
    simp only [List.map_cons, List.any_cons, id_eq]
    have ha := h a (List.mem_cons_self ..)
    have htl := ih (fun i hi => h i (List.mem_cons_of_mem _ hi))
    cases hfa : f a <;> cases hga : g a <;>
      cases h1 : (tl.map f).any id <;> cases h2 : (tl.map g).any id <;> simp_all

lemma not_headD_anti (l : List ℕ) (f g : ℕ → Bool) (h : ∀ i ∈ l, f i ≤ g i) :
    (!((l.map g).headD false)) ≤ (!((l.map f).headD false)) := by
  cases l with
  | nil => simp
  | cons a tl =>
    simp only [List.map_cons, List.headD_cons]
    have ha := h a (List.mem_cons_self ..)
    cases hfa : f a <;> cases hga : g a <;> simp_all

end CircuitBasics

section Builder

def Extends (base : ℕ) (gs1 gs2 : List Gate) : Prop :=
  ∃ extra : List Gate, gs2 = gs1 ++ extra ∧ FanInTwo ⟨extra, 0⟩ ∧
    ReadsBack (base + gs1.length) ⟨extra, 0⟩

lemma Extends.refl (base : ℕ) (gs : List Gate) : Extends base gs gs :=
  ⟨[], by simp, fanInTwo_nil 0, readsBack_nil _ 0⟩

lemma Extends.trans {base : ℕ} {gs1 gs2 gs3 : List Gate}
    (h1 : Extends base gs1 gs2) (h2 : Extends base gs2 gs3) :
    Extends base gs1 gs3 := by
  rcases h1 with ⟨e1, rfl, hf1, hr1⟩
  rcases h2 with ⟨e2, rfl, hf2, hr2⟩
  refine ⟨e1 ++ e2, by rw [List.append_assoc], fanInTwo_append hf1 hf2, ?_⟩
  have hr2' : ReadsBack ((base + gs1.length) + e1.length) ⟨e2, 0⟩ := by
    simpa [List.length_append, Nat.add_assoc] using hr2
  exact readsBack_append hr1 hr2'

lemma Extends.length_le {base : ℕ} {gs1 gs2 : List Gate} (h : Extends base gs1 gs2) :
    gs1.length ≤ gs2.length := by
  rcases h with ⟨e, rfl, _, _⟩; simp

lemma Extends.wire_eq {base : ℕ} {gs1 gs2 : List Gate} (h : Extends base gs1 gs2)
    (w : List Bool) (hw : w.length = base) (i : ℕ) (hi : i < base + gs1.length) :
    (wiresFrom gs2 w).getD i false = (wiresFrom gs1 w).getD i false := by
  rcases h with ⟨e, rfl, _, _⟩
  rw [wiresFrom_append]
  exact wiresFrom_getD_lt e (wiresFrom gs1 w) i (by rw [wiresFrom_length, hw]; exact hi)

def emitAnd (base : ℕ) (gs : List Gate) (a b : ℕ) : List Gate × ℕ :=
  (gs ++ [⟨GateOp.and, [a, b]⟩], base + gs.length)

def emitOr (base : ℕ) (gs : List Gate) (a b : ℕ) : List Gate × ℕ :=
  (gs ++ [⟨GateOp.or, [a, b]⟩], base + gs.length)

def emitNot (base : ℕ) (gs : List Gate) (a : ℕ) : List Gate × ℕ :=
  (gs ++ [⟨GateOp.not, [a]⟩], base + gs.length)

lemma emitAnd_spec (base : ℕ) (gs : List Gate) (a b : ℕ)
    (ha : a < base + gs.length) (hb : b < base + gs.length) :
    let r := emitAnd base gs a b
    Extends base gs r.1 ∧
    r.2 < base + r.1.length ∧
    notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
    nonNot r.1 = nonNot gs + 1 ∧
    ∀ (w : List Bool), w.length = base →
      (wiresFrom r.1 w).getD r.2 false =
        ((wiresFrom gs w).getD a false && (wiresFrom gs w).getD b false) := by
  dsimp only [emitAnd]
  refine ⟨?_, by simp, ?_, ?_, ?_⟩
  · refine ⟨[⟨GateOp.and, [a, b]⟩], rfl, ?_, ?_⟩
    · intro g hg; simp only [List.mem_singleton] at hg; subst hg; simp
    · intro j hj i hi
      have hj0 : j = 0 := by simp at hj; omega
      subst hj0
      rw [gateAt_eq_getElem _ 0 hj] at hi
      simp only [List.getElem_singleton, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
  · rw [notCount_append, notCount_singleton_and, add_zero]
  · rw [nonNot_append, nonNot_singleton_and]
  · intro w hw
    rw [wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
    have hlen : (wiresFrom gs w).length = base + gs.length := by rw [wiresFrom_length, hw]
    rw [getD_append_right _ _ (base + gs.length) false (by omega)]
    simp [hlen, GateOp.eval]

lemma emitOr_spec (base : ℕ) (gs : List Gate) (a b : ℕ)
    (ha : a < base + gs.length) (hb : b < base + gs.length) :
    let r := emitOr base gs a b
    Extends base gs r.1 ∧
    r.2 < base + r.1.length ∧
    notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
    nonNot r.1 = nonNot gs + 1 ∧
    ∀ (w : List Bool), w.length = base →
      (wiresFrom r.1 w).getD r.2 false =
        ((wiresFrom gs w).getD a false || (wiresFrom gs w).getD b false) := by
  dsimp only [emitOr]
  refine ⟨?_, by simp, ?_, ?_, ?_⟩
  · refine ⟨[⟨GateOp.or, [a, b]⟩], rfl, ?_, ?_⟩
    · intro g hg; simp only [List.mem_singleton] at hg; subst hg; simp
    · intro j hj i hi
      have hj0 : j = 0 := by simp at hj; omega
      subst hj0
      rw [gateAt_eq_getElem _ 0 hj] at hi
      simp only [List.getElem_singleton, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
  · rw [notCount_append, notCount_singleton_or, add_zero]
  · rw [nonNot_append, nonNot_singleton_or]
  · intro w hw
    rw [wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
    have hlen : (wiresFrom gs w).length = base + gs.length := by rw [wiresFrom_length, hw]
    rw [getD_append_right _ _ (base + gs.length) false (by omega)]
    simp [hlen, GateOp.eval]

lemma emitNot_spec (base : ℕ) (gs : List Gate) (a : ℕ)
    (ha : a < base + gs.length) :
    let r := emitNot base gs a
    Extends base gs r.1 ∧
    r.2 < base + r.1.length ∧
    notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ + 1 ∧
    nonNot r.1 = nonNot gs ∧
    ∀ (w : List Bool), w.length = base →
      (wiresFrom r.1 w).getD r.2 false = !((wiresFrom gs w).getD a false) := by
  dsimp only [emitNot]
  refine ⟨?_, by simp, ?_, ?_, ?_⟩
  · refine ⟨[⟨GateOp.not, [a]⟩], rfl, ?_, ?_⟩
    · intro g hg; simp only [List.mem_singleton] at hg; subst hg; simp
    · intro j hj i hi
      have hj0 : j = 0 := by simp at hj; omega
      subst hj0
      rw [gateAt_eq_getElem _ 0 hj] at hi
      simp only [List.getElem_singleton, List.mem_singleton] at hi
      subst hi; omega
  · rw [notCount_append, notCount_singleton_not]
  · rw [nonNot_append, nonNot_singleton_not, add_zero]
  · intro w hw
    rw [wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
    have hlen : (wiresFrom gs w).length = base + gs.length := by rw [wiresFrom_length, hw]
    rw [getD_append_right _ _ (base + gs.length) false (by omega)]
    simp [hlen, GateOp.eval]

def buildMerged (base notM : ℕ) : List Gate → List ℕ → List ℕ → List Gate × List ℕ
  | gs, [], _ => (gs, [])
  | gs, a :: as, [] =>
    let r := emitAnd base gs a notM
    let rest := buildMerged base notM r.1 as []
    (rest.1, r.2 :: rest.2)
  | gs, a :: as, b :: bs =>
    let r1 := emitAnd base gs a notM
    let r2 := emitOr base r1.1 r1.2 b
    let rest := buildMerged base notM r2.1 as bs
    (rest.1, r2.2 :: rest.2)

lemma buildMerged_spec (base notM : ℕ) (leftW rightW : List ℕ) (gs : List Gate)
    (hnotM : notM < base + gs.length)
    (hL : ∀ i ∈ leftW, i < base + gs.length)
    (hR : ∀ i ∈ rightW, i < base + gs.length)
    (hlen : rightW.length ≤ leftW.length) :
    let r := buildMerged base notM gs leftW rightW
    Extends base gs r.1 ∧
    r.2.length = leftW.length ∧
    (∀ i ∈ r.2, i < base + r.1.length) ∧
    notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
    nonNot r.1 = nonNot gs + leftW.length + rightW.length ∧
    ∀ (w : List Bool), w.length = base →
      ∀ (t : ℕ), t < leftW.length →
        (wiresFrom r.1 w).getD (r.2.getD t 0) false =
          if t < rightW.length then
            ((wiresFrom gs w).getD (leftW.getD t 0) false && (wiresFrom gs w).getD notM false) ||
              (wiresFrom gs w).getD (rightW.getD t 0) false
          else
            (wiresFrom gs w).getD (leftW.getD t 0) false && (wiresFrom gs w).getD notM false := by
  induction leftW generalizing rightW gs with
  | nil =>
    dsimp only [buildMerged]
    have hrnil : rightW = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hlen)
    subst hrnil
    refine ⟨Extends.refl base gs, rfl, (fun _ h => by cases h), rfl, by simp, (fun _ _ t ht => by simp at ht)⟩
  | cons a as ih =>
    have ha : a < base + gs.length := hL a (List.mem_cons_self ..)
    have has : ∀ i ∈ as, i < base + gs.length := fun i hi => hL i (List.mem_cons_of_mem _ hi)
    cases rightW with
    | nil =>
      dsimp only [buildMerged]
      set r1 := emitAnd base gs a notM with hr1
      have h1 := emitAnd_spec base gs a notM ha hnotM
      rw [← hr1] at h1
      rcases h1 with ⟨hext1, hlt1, hnc1, hnn1, hval1⟩
      have hgl1 := hext1.length_le
      set rest := buildMerged base notM r1.1 as [] with hrest
      have h2 := ih [] r1.1 (by omega) (fun i hi => lt_of_lt_of_le (has i hi) (by omega))
        (fun _ h => by cases h) (by simp)
      rw [← hrest] at h2
      rcases h2 with ⟨hext2, hlen2, hlt2, hnc2, hnn2, hval2⟩
      have hgl2 := hext2.length_le
      refine ⟨hext1.trans hext2, by simp [hlen2], ?_, by omega,
        by simp only [List.length_cons, List.length_nil] at hnn2 ⊢; omega, ?_⟩
      · intro i hi
        simp only [List.mem_cons] at hi
        rcases hi with rfl | hi
        · omega
        · exact hlt2 i hi
      · intro w hw t ht
        cases t with
        | zero =>
          change (wiresFrom rest.1 w).getD r1.2 false = _
          simp only [List.length_nil, Nat.not_lt_zero, ↓reduceIte]
          rw [hext2.wire_eq w hw _ hlt1, hval1 w hw]; rfl
        | succ t' =>
          have ht' : t' < as.length := by simp at ht; omega
          change (wiresFrom rest.1 w).getD (rest.2.getD t' 0) false = _
          simp only [List.length_nil, Nat.not_lt_zero, ↓reduceIte]
          have hv := hval2 w hw t' ht'
          simp only [List.length_nil, Nat.not_lt_zero, ↓reduceIte] at hv
          rw [hv, hext1.wire_eq w hw _ (has _ (getD_mem as t' 0 ht')), hext1.wire_eq w hw notM hnotM]; rfl
    | cons b bs =>
      dsimp only [buildMerged]
      have hb : b < base + gs.length := hR b (List.mem_cons_self ..)
      have hbs : ∀ i ∈ bs, i < base + gs.length := fun i hi => hR i (List.mem_cons_of_mem _ hi)
      set r1 := emitAnd base gs a notM with hr1
      have h1 := emitAnd_spec base gs a notM ha hnotM
      rw [← hr1] at h1
      rcases h1 with ⟨hext1, hlt1, hnc1, hnn1, hval1⟩
      have hgl1 := hext1.length_le
      set r2 := emitOr base r1.1 r1.2 b with hr2
      have h2 := emitOr_spec base r1.1 r1.2 b hlt1 (by omega)
      rw [← hr2] at h2
      rcases h2 with ⟨hext2, hlt2, hnc2, hnn2, hval2⟩
      have hgl2 := hext2.length_le
      have hext12 := hext1.trans hext2
      set rest := buildMerged base notM r2.1 as bs with hrest
      have h3 := ih bs r2.1 (by omega) (fun i hi => lt_of_lt_of_le (has i hi) (by omega))
        (fun i hi => lt_of_lt_of_le (hbs i hi) (by omega)) (by simp at hlen; omega)
      rw [← hrest] at h3
      rcases h3 with ⟨hext3, hlen3, hlt3, hnc3, hnn3, hval3⟩
      have hgl3 := hext3.length_le
      refine ⟨hext12.trans hext3, by simp [hlen3], ?_, by omega, by simp only [List.length_cons]; omega, ?_⟩
      · intro i hi
        simp only [List.mem_cons] at hi
        rcases hi with rfl | hi
        · omega
        · exact hlt3 i hi
      · intro w hw t ht
        cases t with
        | zero =>
          change (wiresFrom rest.1 w).getD r2.2 false = _
          simp only [List.length_cons, Nat.zero_lt_succ, ↓reduceIte]
          rw [hext3.wire_eq w hw _ hlt2, hval2 w hw, hval1 w hw, hext1.wire_eq w hw b hb]; rfl
        | succ t' =>
          have ht' : t' < as.length := by simp at ht; omega
          change (wiresFrom rest.1 w).getD (rest.2.getD t' 0) false = _
          simp only [List.length_cons, Nat.add_lt_add_iff_right]
          rw [hval3 w hw t' ht']
          split_ifs with hrt
          · rw [hext12.wire_eq w hw _ (has _ (getD_mem as t' 0 ht')),
                hext12.wire_eq w hw notM hnotM,
                hext12.wire_eq w hw _ (hbs _ (getD_mem bs t' 0 hrt))]; rfl
          · rw [hext12.wire_eq w hw _ (has _ (getD_mem as t' 0 ht')),
                hext12.wire_eq w hw notM hnotM]; rfl

def mapAndWith (base c : ℕ) : List Gate → List ℕ → List Gate × List ℕ
  | gs, [] => (gs, [])
  | gs, z :: zs =>
    let r := emitAnd base gs c z
    let rest := mapAndWith base c r.1 zs
    (rest.1, r.2 :: rest.2)

lemma mapAndWith_spec (base c : ℕ) (zs : List ℕ) (gs : List Gate)
    (hc : c < base + gs.length) (hzs : ∀ i ∈ zs, i < base + gs.length) :
    let r := mapAndWith base c gs zs
    Extends base gs r.1 ∧
    r.2.length = zs.length ∧
    (∀ i ∈ r.2, i < base + r.1.length) ∧
    notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
    nonNot r.1 = nonNot gs + zs.length ∧
    ∀ (w : List Bool), w.length = base →
      ∀ (t : ℕ), t < zs.length →
        (wiresFrom r.1 w).getD (r.2.getD t 0) false =
          ((wiresFrom gs w).getD c false && (wiresFrom gs w).getD (zs.getD t 0) false) := by
  induction zs generalizing gs with
  | nil =>
    dsimp only [mapAndWith]
    refine ⟨Extends.refl base gs, rfl, (fun _ h => by cases h), rfl, by simp, (fun _ _ t ht => by simp at ht)⟩
  | cons z zs ih =>
    dsimp only [mapAndWith]
    have hz : z < base + gs.length := hzs z (List.mem_cons_self ..)
    have hzs' : ∀ i ∈ zs, i < base + gs.length := fun i hi => hzs i (List.mem_cons_of_mem _ hi)
    set r1 := emitAnd base gs c z with hr1
    have h1 := emitAnd_spec base gs c z hc hz
    rw [← hr1] at h1
    rcases h1 with ⟨hext1, hlt1, hnc1, hnn1, hval1⟩
    have hgl1 := hext1.length_le
    set rest := mapAndWith base c r1.1 zs with hrest
    have h2 := ih r1.1 (by omega) (fun i hi => lt_of_lt_of_le (hzs' i hi) (by omega))
    rw [← hrest] at h2
    rcases h2 with ⟨hext2, hlen2, hlt2, hnc2, hnn2, hval2⟩
    have hgl2 := hext2.length_le
    refine ⟨hext1.trans hext2, by simp [hlen2], ?_, by omega, by simp only [List.length_cons]; omega, ?_⟩
    · intro i hi
      simp only [List.mem_cons] at hi
      rcases hi with rfl | hi
      · omega
      · exact hlt2 i hi
    · intro w hw t ht
      cases t with
      | zero =>
        change (wiresFrom rest.1 w).getD r1.2 false = _
        rw [hext2.wire_eq w hw _ hlt1, hval1 w hw]; rfl
      | succ t' =>
        have ht' : t' < zs.length := by simp at ht; omega
        change (wiresFrom rest.1 w).getD (rest.2.getD t' 0) false = _
        rw [hval2 w hw t' ht', hext1.wire_eq w hw c hc,
            hext1.wire_eq w hw _ (hzs' _ (getD_mem zs t' 0 ht'))]; rfl

def mapOrWith (base c : ℕ) : List Gate → List ℕ → List Gate × List ℕ
  | gs, [] => (gs, [])
  | gs, z :: zs =>
    let r := emitOr base gs c z
    let rest := mapOrWith base c r.1 zs
    (rest.1, r.2 :: rest.2)

lemma mapOrWith_spec (base c : ℕ) (zs : List ℕ) (gs : List Gate)
    (hc : c < base + gs.length) (hzs : ∀ i ∈ zs, i < base + gs.length) :
    let r := mapOrWith base c gs zs
    Extends base gs r.1 ∧
    r.2.length = zs.length ∧
    (∀ i ∈ r.2, i < base + r.1.length) ∧
    notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
    nonNot r.1 = nonNot gs + zs.length ∧
    ∀ (w : List Bool), w.length = base →
      ∀ (t : ℕ), t < zs.length →
        (wiresFrom r.1 w).getD (r.2.getD t 0) false =
          ((wiresFrom gs w).getD c false || (wiresFrom gs w).getD (zs.getD t 0) false) := by
  induction zs generalizing gs with
  | nil =>
    dsimp only [mapOrWith]
    refine ⟨Extends.refl base gs, rfl, (fun _ h => by cases h), rfl, by simp, (fun _ _ t ht => by simp at ht)⟩
  | cons z zs ih =>
    dsimp only [mapOrWith]
    have hz : z < base + gs.length := hzs z (List.mem_cons_self ..)
    have hzs' : ∀ i ∈ zs, i < base + gs.length := fun i hi => hzs i (List.mem_cons_of_mem _ hi)
    set r1 := emitOr base gs c z with hr1
    have h1 := emitOr_spec base gs c z hc hz
    rw [← hr1] at h1
    rcases h1 with ⟨hext1, hlt1, hnc1, hnn1, hval1⟩
    have hgl1 := hext1.length_le
    set rest := mapOrWith base c r1.1 zs with hrest
    have h2 := ih r1.1 (by omega) (fun i hi => lt_of_lt_of_le (hzs' i hi) (by omega))
    rw [← hrest] at h2
    rcases h2 with ⟨hext2, hlen2, hlt2, hnc2, hnn2, hval2⟩
    have hgl2 := hext2.length_le
    refine ⟨hext1.trans hext2, by simp [hlen2], ?_, by omega, by simp only [List.length_cons]; omega, ?_⟩
    · intro i hi
      simp only [List.mem_cons] at hi
      rcases hi with rfl | hi
      · omega
      · exact hlt2 i hi
    · intro w hw t ht
      cases t with
      | zero =>
        change (wiresFrom rest.1 w).getD r1.2 false = _
        rw [hext2.wire_eq w hw _ hlt1, hval1 w hw]; rfl
      | succ t' =>
        have ht' : t' < zs.length := by simp at ht; omega
        change (wiresFrom rest.1 w).getD (rest.2.getD t' 0) false = _
        rw [hval2 w hw t' ht', hext1.wire_eq w hw c hc,
            hext1.wire_eq w hw _ (hzs' _ (getD_mem zs t' 0 ht'))]; rfl

def chainInv (base : ℕ) : ℕ → List Gate → List ℕ → List Gate × List ℕ
  | 0, gs, _ => (gs, [])
  | r + 1, gs, ys =>
    if ys.length = 0 then (gs, [])
    else
      let q := ys.length / 2
      let leftW := ys.take q
      let mWire := ys.getD q 0
      let rightW := ys.drop (q + 1)
      let rNot := emitNot base gs mWire
      let notM := rNot.2
      let rMerge := buildMerged base notM rNot.1 leftW rightW
      let rRec := chainInv base r rMerge.1 rMerge.2
      let rLeft := mapAndWith base notM rRec.1 rRec.2
      let rRight := mapOrWith base notM rLeft.1 (rRec.2.take rightW.length)
      (rRight.1, rLeft.2 ++ [notM] ++ rRight.2)

lemma chainInv_spec (base : ℕ) :
    ∀ (r : ℕ) (gs : List Gate) (ys : List ℕ),
      ys.length < 2 ^ r →
      (∀ i ∈ ys, i < base + gs.length) →
      let res := chainInv base r gs ys
      Extends base gs res.1 ∧
      res.2.length = ys.length ∧
      (∀ i ∈ res.2, i < base + res.1.length) ∧
      notCount ⟨res.1, 0⟩ ≤ notCount ⟨gs, 0⟩ + r ∧
      nonNot res.1 ≤ nonNot gs + 4 * ys.length ∧
      ∀ (w : List Bool), w.length = base →
        (∀ (i j : ℕ), i < ys.length → j < ys.length → i ≤ j →
          (wiresFrom gs w).getD (ys.getD j 0) false ≤ (wiresFrom gs w).getD (ys.getD i 0) false) →
        ∀ (k : ℕ), k < ys.length →
          (wiresFrom res.1 w).getD (res.2.getD k 0) false =
            !((wiresFrom gs w).getD (ys.getD k 0) false) := by
  intro r
  induction r with
  | zero =>
    intro gs ys hlen _
    dsimp only [chainInv]
    have hnil : ys = [] := List.eq_nil_of_length_eq_zero (by simp only [pow_zero] at hlen; omega)
    subst hnil
    refine ⟨Extends.refl base gs, rfl, (fun _ h => by cases h), by omega, by simp,
      (fun _ _ _ k hk => by simp at hk)⟩
  | succ r ih =>
    intro gs ys hlen hys
    dsimp only [chainInv]
    split_ifs with h0
    · have hnil : ys = [] := List.eq_nil_of_length_eq_zero h0
      subst hnil
      dsimp only
      refine ⟨Extends.refl base gs, rfl, (fun _ h => by cases h), by omega, by simp,
        (fun _ _ _ k hk => by simp at hk)⟩
    · set q := ys.length / 2 with hq_def
      set leftW := ys.take q with hleftW_def
      set mWire := ys.getD q 0 with hmWire_def
      set rightW := ys.drop (q + 1) with hrightW_def
      have hq_lt : q < ys.length := by omega
      have hL_len : leftW.length = q := by rw [hleftW_def, List.length_take]; omega
      have hR_len : rightW.length = ys.length - (q + 1) := by rw [hrightW_def, List.length_drop]
      have hRL_le : rightW.length ≤ leftW.length := by omega
      have hm_lt : mWire < base + gs.length := hys _ (getD_mem ys q 0 hq_lt)
      have hL_lt : ∀ i ∈ leftW, i < base + gs.length := fun i hi => hys i (List.mem_of_mem_take hi)
      have hR_lt : ∀ i ∈ rightW, i < base + gs.length := fun i hi => hys i (List.mem_of_mem_drop hi)
      set rNot := emitNot base gs mWire with hrNot
      have hNot := emitNot_spec base gs mWire hm_lt
      rw [← hrNot] at hNot
      rcases hNot with ⟨hextN, hltN, hncN, hnnN, hvalN⟩
      have hglN := hextN.length_le
      set rMerge := buildMerged base rNot.2 rNot.1 leftW rightW with hrMerge
      have hMerge := buildMerged_spec base rNot.2 leftW rightW rNot.1 hltN
        (fun i hi => lt_of_lt_of_le (hL_lt i hi) (by omega))
        (fun i hi => lt_of_lt_of_le (hR_lt i hi) (by omega)) hRL_le
      rw [← hrMerge] at hMerge
      rcases hMerge with ⟨hextM, hlenM, hltM, hncM, hnnM, hvalM⟩
      have hglM := hextM.length_le
      have hq_pow : rMerge.2.length < 2 ^ r := by
        have hpow : 2 ^ (r + 1) = 2 * 2 ^ r := by rw [pow_succ]; ring
        omega
      set rRec := chainInv base r rMerge.1 rMerge.2 with hrRec
      have hRec := ih rMerge.1 rMerge.2 hq_pow hltM
      rw [← hrRec] at hRec
      rcases hRec with ⟨hextR, hlenR, hltR, hncR, hnnR, hvalR⟩
      have hglR := hextR.length_le
      set rLeft := mapAndWith base rNot.2 rRec.1 rRec.2 with hrLeft
      have hnotM_R : rNot.2 < base + rRec.1.length := by omega
      have hLeft := mapAndWith_spec base rNot.2 rRec.2 rRec.1 hnotM_R hltR
      rw [← hrLeft] at hLeft
      rcases hLeft with ⟨hextL, hlenL, hltL, hncL, hnnL, hvalL⟩
      have hglL := hextL.length_le
      set rRight := mapOrWith base rNot.2 rLeft.1 (rRec.2.take rightW.length) with hrRight
      have hnotM_L : rNot.2 < base + rLeft.1.length := by omega
      have hTake_lt : ∀ i ∈ rRec.2.take rightW.length, i < base + rLeft.1.length := fun i hi =>
        lt_of_lt_of_le (hltR i (List.mem_of_mem_take hi)) (by omega)
      have hRight := mapOrWith_spec base rNot.2 (rRec.2.take rightW.length) rLeft.1 hnotM_L hTake_lt
      rw [← hrRight] at hRight
      rcases hRight with ⟨hextRi, hlenRi, hltRi, hncRi, hnnRi, hvalRi⟩
      have hglRi := hextRi.length_le
      have hTake_len : (rRec.2.take rightW.length).length = rightW.length := by
        rw [List.length_take]; omega
      have hext_all : Extends base gs rRight.1 :=
        (((hextN.trans hextM).trans hextR).trans hextL).trans hextRi
      have hlen_out : (rLeft.2 ++ [rNot.2] ++ rRight.2).length = ys.length := by
        simp only [List.length_append, List.length_singleton]; omega
      dsimp only
      refine ⟨hext_all, hlen_out, ?_, by omega, by omega, ?_⟩
      · intro i hi
        simp only [List.mem_append, List.mem_singleton] at hi
        rcases hi with (hi | rfl) | hi
        · exact lt_of_lt_of_le (hltL i hi) (by omega)
        · omega
        · exact hltRi i hi
      · intro w hw hdec k hk
        have hval_notM : (wiresFrom rNot.1 w).getD rNot.2 false =
            !((wiresFrom gs w).getD (ys.getD q 0) false) := hvalN w hw
        have hval_merge_eval : ∀ (t : ℕ), t < q →
            (wiresFrom rMerge.1 w).getD (rMerge.2.getD t 0) false =
              if (wiresFrom gs w).getD (ys.getD q 0) false = false then
                (wiresFrom gs w).getD (ys.getD t 0) false
              else
                if q + 1 + t < ys.length then
                  (wiresFrom gs w).getD (ys.getD (q + 1 + t) 0) false
                else false := by
          intro t ht
          have hvm := hvalM w hw t (by omega)
          rw [hvm, hval_notM]
          have hL_el : leftW.getD t 0 = ys.getD t 0 := getD_take ys q t 0 ht
          rw [hL_el, hextN.wire_eq w hw _ (hys _ (getD_mem ys t 0 (by omega)))]
          cases hmq : (wiresFrom gs w).getD (ys.getD q 0) false
          · simp only [Bool.not_false, Bool.and_true, ↓reduceIte]
            split_ifs with hrt
            · have hR_el : rightW.getD t 0 = ys.getD (q + 1 + t) 0 := getD_drop ys (q + 1) t 0
              rw [hR_el, hextN.wire_eq w hw _ (hys _ (getD_mem ys (q + 1 + t) 0 (by omega)))]
              have hle := hdec q (q + 1 + t) hq_lt (by omega) (by omega)
              rw [hmq] at hle
              have h0f : (wiresFrom gs w).getD (ys.getD (q + 1 + t) 0) false = false := by
                cases hv : (wiresFrom gs w).getD (ys.getD (q + 1 + t) 0) false
                · rfl
                · rw [hv] at hle; exact absurd hle not_true_le_false
              rw [h0f, Bool.or_false]
            · rfl
          · simp only [Bool.not_true, Bool.and_false, Bool.false_or, Bool.true_eq_false, ↓reduceIte]
            split_ifs with hrt1 hrt2
            · have hR_el : rightW.getD t 0 = ys.getD (q + 1 + t) 0 := getD_drop ys (q + 1) t 0
              rw [hR_el, hextN.wire_eq w hw _ (hys _ (getD_mem ys (q + 1 + t) 0 hrt2))]
            · omega
            · omega
            · rfl
        have hdec_merge : ∀ (i j : ℕ), i < rMerge.2.length → j < rMerge.2.length → i ≤ j →
            (wiresFrom rMerge.1 w).getD (rMerge.2.getD j 0) false ≤
              (wiresFrom rMerge.1 w).getD (rMerge.2.getD i 0) false := by
          intro i j hi hj hij
          rw [hval_merge_eval i (by omega), hval_merge_eval j (by omega)]
          cases hmq : (wiresFrom gs w).getD (ys.getD q 0) false
          · simp only [↓reduceIte]; exact hdec i j (by omega) (by omega) hij
          · simp only [Bool.true_eq_false, ↓reduceIte]
            split_ifs with h1 h2
            · exact hdec (q + 1 + i) (q + 1 + j) h2 h1 (by omega)
            · omega
            · exact Bool.false_le _
            · exact le_refl false
        have hval_rec := hvalR w hw hdec_merge
        have hextNR : Extends base rNot.1 rRec.1 := hextM.trans hextR
        have hextNL : Extends base rNot.1 rLeft.1 := hextNR.trans hextL
        have hextNRi : Extends base rNot.1 rRight.1 := hextNL.trans hextRi
        by_cases hk_lt : k < q
        · have hk1 : k < (rLeft.2 ++ [rNot.2]).length := by
            simp only [List.length_append, List.length_singleton]; omega
          have hget : (rLeft.2 ++ [rNot.2] ++ rRight.2).getD k 0 = rLeft.2.getD k 0 := by
            rw [getD_append_left _ _ k 0 hk1, getD_append_left _ _ k 0 (by omega)]
          rw [hget, hextRi.wire_eq w hw _ (hltL _ (getD_mem rLeft.2 k 0 (by omega))),
              hvalL w hw k (by omega), hextNR.wire_eq w hw rNot.2 hltN, hval_notM,
              hval_rec k (by omega), hval_merge_eval k hk_lt]
          cases hmq : (wiresFrom gs w).getD (ys.getD q 0) false
          · simp
          · have hle := hdec k q (by omega) hq_lt (by omega)
            rw [hmq] at hle
            have hkt : (wiresFrom gs w).getD (ys.getD k 0) false = true := by
              cases hv : (wiresFrom gs w).getD (ys.getD k 0) false
              · rw [hv] at hle; exact absurd hle not_true_le_false
              · rfl
            rw [hkt]; simp
        · by_cases hk_eq : k = q
          · rw [hk_eq]
            have hk1 : q < (rLeft.2 ++ [rNot.2]).length := by
              simp only [List.length_append, List.length_singleton]; omega
            have hget : (rLeft.2 ++ [rNot.2] ++ rRight.2).getD q 0 = rNot.2 := by
              rw [getD_append_left _ _ q 0 hk1, getD_append_right _ _ q 0 (by omega)]
              have hsub : q - rLeft.2.length = 0 := by omega
              rw [hsub]; rfl
            rw [hget, hextNRi.wire_eq w hw rNot.2 hltN, hval_notM]
          · set t := k - (q + 1)
            have ht_lt : t < rightW.length := by omega
            have hk_eq' : q + 1 + t = k := by omega
            have hlen_prefix : (rLeft.2 ++ [rNot.2]).length = q + 1 := by
              simp only [List.length_append, List.length_singleton]; omega
            have hget : (rLeft.2 ++ [rNot.2] ++ rRight.2).getD k 0 = rRight.2.getD t 0 := by
              rw [getD_append_right _ _ k 0 (by omega), hlen_prefix]
            rw [hget, hvalRi w hw t (by omega), hextNL.wire_eq w hw rNot.2 hltN, hval_notM,
                getD_take rRec.2 rightW.length t 0 ht_lt,
                hextL.wire_eq w hw _ (hltR _ (getD_mem rRec.2 t 0 (by omega))),
                hval_rec t (by omega), hval_merge_eval t (by omega)]
            cases hmq : (wiresFrom gs w).getD (ys.getD q 0) false
            · have hle := hdec q k hq_lt hk (by omega)
              rw [hmq] at hle
              have hkf : (wiresFrom gs w).getD (ys.getD k 0) false = false := by
                cases hv : (wiresFrom gs w).getD (ys.getD k 0) false
                · rfl
                · rw [hv] at hle; exact absurd hle not_true_le_false
              rw [hkf]; simp
            · simp only [Bool.not_true, Bool.false_or, Bool.true_eq_false, ↓reduceIte]
              rw [hk_eq', if_pos hk]

def threshStepAux (base w : ℕ) : List Gate → ℕ → List ℕ → List Gate × List ℕ
  | gs, p, [] =>
    let r := emitAnd base gs p w
    (r.1, [r.2])
  | gs, p, q :: qs =>
    let r1 := emitAnd base gs p w
    let r2 := emitOr base r1.1 q r1.2
    let rest := threshStepAux base w r2.1 q qs
    (rest.1, r2.2 :: rest.2)

lemma threshStepAux_spec (base w : ℕ) (qs : List ℕ) (p : ℕ) (gs : List Gate)
    (hw : w < base + gs.length) (hp : p < base + gs.length)
    (hqs : ∀ i ∈ qs, i < base + gs.length) :
    let r := threshStepAux base w gs p qs
    Extends base gs r.1 ∧
    r.2.length = qs.length + 1 ∧
    (∀ i ∈ r.2, i < base + r.1.length) ∧
    notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
    nonNot r.1 = nonNot gs + 2 * qs.length + 1 ∧
    ∀ (v : List Bool), v.length = base →
      ∀ (j : ℕ), j < qs.length + 1 →
        (wiresFrom r.1 v).getD (r.2.getD j 0) false =
          if j < qs.length then
            (wiresFrom gs v).getD (qs.getD j 0) false ||
              ((wiresFrom gs v).getD ((p :: qs).getD j 0) false && (wiresFrom gs v).getD w false)
          else
            (wiresFrom gs v).getD ((p :: qs).getD qs.length 0) false && (wiresFrom gs v).getD w false := by
  induction qs generalizing p gs with
  | nil =>
    dsimp only [threshStepAux]
    have h1 := emitAnd_spec base gs p w hp hw
    rcases h1 with ⟨hext, hlt, hnc, hnn, hval⟩
    refine ⟨hext, rfl, ?_, hnc, by simp [hnn], ?_⟩
    · intro i hi; simp only [List.mem_singleton] at hi; subst hi; exact hlt
    · intro v hv j hj
      have hj0 : j = 0 := by simp at hj; omega
      subst hj0
      simpa using hval v hv
  | cons q qs ih =>
    dsimp only [threshStepAux]
    have hq : q < base + gs.length := hqs q (List.mem_cons_self ..)
    have hqs' : ∀ i ∈ qs, i < base + gs.length := fun i hi => hqs i (List.mem_cons_of_mem _ hi)
    set r1 := emitAnd base gs p w with hr1
    have h1 := emitAnd_spec base gs p w hp hw
    rw [← hr1] at h1
    rcases h1 with ⟨hext1, hlt1, hnc1, hnn1, hval1⟩
    have hgl1 := hext1.length_le
    set r2 := emitOr base r1.1 q r1.2 with hr2
    have h2 := emitOr_spec base r1.1 q r1.2 (by omega) hlt1
    rw [← hr2] at h2
    rcases h2 with ⟨hext2, hlt2, hnc2, hnn2, hval2⟩
    have hgl2 := hext2.length_le
    have hext12 := hext1.trans hext2
    set rest := threshStepAux base w r2.1 q qs with hrest
    have h3 := ih q r2.1 (by omega) (by omega) (fun i hi => lt_of_lt_of_le (hqs' i hi) (by omega))
    rw [← hrest] at h3
    rcases h3 with ⟨hext3, hlen3, hlt3, hnc3, hnn3, hval3⟩
    have hgl3 := hext3.length_le
    refine ⟨hext12.trans hext3, by simp [hlen3], ?_, by omega, by simp only [List.length_cons]; omega, ?_⟩
    · intro i hi
      simp only [List.mem_cons] at hi
      rcases hi with rfl | hi
      · omega
      · exact hlt3 i hi
    · intro v hv j hj
      cases j with
      | zero =>
        change (wiresFrom rest.1 v).getD r2.2 false = _
        simp only [List.length_cons, Nat.zero_lt_succ, ↓reduceIte]
        rw [hext3.wire_eq v hv _ hlt2, hval2 v hv, hval1 v hv, hext1.wire_eq v hv q hq]
        rfl
      | succ j' =>
        have hj' : j' < qs.length + 1 := by simp at hj; omega
        change (wiresFrom rest.1 v).getD (rest.2.getD j' 0) false = _
        simp only [List.length_cons, Nat.add_lt_add_iff_right]
        rw [hval3 v hv j' hj']
        split_ifs with hlt
        · have hmem1 : qs.getD j' 0 ∈ qs := getD_mem qs j' 0 hlt
          have hmem2 : (q :: qs).getD j' 0 ∈ q :: qs := getD_mem (q :: qs) j' 0 (by simp; omega)
          rw [hext12.wire_eq v hv _ (hqs' _ hmem1),
              hext12.wire_eq v hv _ (hqs _ hmem2),
              hext12.wire_eq v hv w hw]
          rfl
        · have hmem2 : (q :: qs).getD qs.length 0 ∈ q :: qs := getD_mem (q :: qs) qs.length 0 (by simp)
          rw [hext12.wire_eq v hv _ (hqs _ hmem2), hext12.wire_eq v hv w hw]
          rfl

def buildAssoc {α : Type*} [DecidableEq α] (step : List Gate → α → List Gate × ℕ)
    (dflt : ℕ) : List Gate → List α → List Gate × (α → ℕ)
  | gs, [] => (gs, fun _ => dflt)
  | gs, a :: as =>
    let r := step gs a
    let rest := buildAssoc step dflt r.1 as
    (rest.1, fun x => if x = a then r.2 else rest.2 x)

lemma buildAssoc_ext_spec {α : Type*} [DecidableEq α] (base dflt : ℕ) (gs0 : List Gate)
    (step : List Gate → α → List Gate × ℕ)
    (cost : α → ℕ)
    (spec : α → List Bool → Bool)
    (hstep : ∀ (gs : List Gate) (a : α), Extends base gs0 gs →
      Extends base gs (step gs a).1 ∧
      (step gs a).2 < base + (step gs a).1.length ∧
      notCount ⟨(step gs a).1, 0⟩ = notCount ⟨gs, 0⟩ ∧
      nonNot (step gs a).1 ≤ nonNot gs + cost a ∧
      ∀ (w : List Bool), w.length = base →
        (wiresFrom (step gs a).1 w).getD (step gs a).2 false = spec a w) :
    ∀ (ks : List α) (gs : List Gate), Extends base gs0 gs → dflt < base + gs.length →
      let r := buildAssoc step dflt gs ks
      Extends base gs r.1 ∧
      (∀ x, r.2 x < base + r.1.length) ∧
      notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
      nonNot r.1 ≤ nonNot gs + (ks.map cost).sum ∧
      ∀ (w : List Bool), w.length = base → ∀ a ∈ ks,
        (wiresFrom r.1 w).getD (r.2 a) false = spec a w := by
  intro ks
  induction ks with
  | nil =>
    intro gs _ hdflt
    dsimp only [buildAssoc]
    refine ⟨Extends.refl base gs, fun _ => hdflt, rfl, by simp, fun _ _ _ ha => by cases ha⟩
  | cons a ks ih =>
    intro gs hExt0 hdflt
    dsimp only [buildAssoc]
    rcases hstep gs a hExt0 with ⟨hext1, hlt1, hnc1, hnn1, hval1⟩
    have hgl1 := hext1.length_le
    rcases ih (step gs a).1 (hExt0.trans hext1) (by omega) with ⟨hext2, hlt2, hnc2, hnn2, hval2⟩
    have hgl2 := hext2.length_le
    refine ⟨hext1.trans hext2, ?_, by omega, by simp only [List.map_cons, List.sum_cons]; omega, ?_⟩
    · intro x
      by_cases hx : x = a
      · simp only [hx, ↓reduceIte]; omega
      · simp only [hx, ↓reduceIte]; exact hlt2 x
    · intro w hw b hb
      by_cases hba : b = a
      · subst hba
        simp only [↓reduceIte]
        rw [hext2.wire_eq w hw _ hlt1, hval1 w hw]
      · simp only [hba, ↓reduceIte]
        exact hval2 w hw b ((List.mem_cons.mp hb).resolve_left hba)

lemma sum_const_le {α : Type*} (l : List α) (c : ℕ) : (l.map (fun _ => c)).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons _ tl ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring

end Builder

end ChainNet
end PEqualNP.Outside.L_lib_1425

namespace PEqualNP.Outside.L_lib_1425
namespace Select
open StageNet
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open scoped Classical

theorem invertThresholds {n p k L b : Nat} {x : Fin p → Finset (Fin n)} {S : Set (Col p)}
    (H : Built x [] k S) (f : Fin L → Col p) (given : ∀ i, f i ∈ S)
    (ordered : ∀ z i j, i ≤ j → f j z ≤ f i z) (cap : L < 2^b) :
    ∃ tr V, tr.length ≤ b ∧ Built x tr (k+5*L) V ∧ S ⊆ V ∧
      ∀ i, (fun z => !(f i z)) ∈ V := by
  classical
  obtain ⟨gs,fan,back,sz,ht,wire⟩ := H
  have initLen : (ix gs).length = 0 := by
    simpa [trace] using congrArg List.length ht
  have nc0 : PEqualNP.NotBracket.notCount ⟨gs,0⟩ = 0 := (countIx gs).trans initLen
  choose tap inRange values using fun i => wire _ (given i)
  let ys := List.ofFn tap
  let t := min b L
  have tl : t ≤ L := Nat.min_le_right _ _
  have tb : t ≤ b := Nat.min_le_left _ _
  have enough : ys.length < 2^t := by
    dsimp [ys,t]
    rw [List.length_ofFn]
    rcases le_total b L with h | h
    · simpa [Nat.min_eq_left h] using cap
    · simpa [Nat.min_eq_right h] using (Nat.lt_two_pow_self (n := L))
  have yr : ∀ j ∈ ys, j < n+2+gs.length := by
    intro j mem
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp mem
    exact inRange i
  let res := ChainNet.chainInv (n+2) t gs ys
  obtain ⟨exts,num,vr,notB,posB,correct⟩ := ChainNet.chainInv_spec (n+2) t gs ys enough yr
  have num' : res.2.length = L := num.trans (by simp [ys])
  have invB : PEqualNP.NotBracket.notCount ⟨res.1,0⟩ ≤ t := by simpa [nc0,res] using notB
  have rawSize (z : Fin p) : (raw x z).length = n+2 := by simp [raw]
  have lens := exts.length_le
  let V : Set (Col p) := S ∪ Set.range (fun i : Fin L => (fun z => !(f i z)))
  refine ⟨trace x res.1,V,?_,?_,Set.subset_union_left,fun i => Or.inr ⟨i,rfl⟩⟩
  · have len : (trace x res.1).length = PEqualNP.NotBracket.notCount ⟨res.1,0⟩ := by
      simpa [trace] using (countIx res.1).symm
    exact len ▸ (invB.trans tb)
  · have fanback : FanInTwo ⟨res.1,0⟩ ∧ ReadsBack (n+2) ⟨res.1,0⟩ := by
      obtain ⟨extra,eq,fe,re⟩ := exts
      change res.1 = gs ++ extra at eq
      rw [eq]
      exact ⟨ChainNet.fanInTwo_append fan fe,ChainNet.readsBack_append back re⟩
    refine ⟨res.1,fanback.1,fanback.2,?_,rfl,?_⟩
    · change res.1.length - PEqualNP.NotBracket.notCount ⟨res.1,0⟩ ≤ _ at posB
      change _ ≤ (gs.length - PEqualNP.NotBracket.notCount ⟨gs,0⟩) + 4 * ys.length at posB
      have ysL : ys.length = L := List.length_ofFn
      omega
    · intro v hv
      rcases hv with old | ⟨i,rfl⟩
      · obtain ⟨a,ha,hv⟩ := wire _ old
        refine ⟨a,lt_of_lt_of_le ha (Nat.add_le_add_left lens _),?_⟩
        funext z
        exact (exts.wire_eq (raw x z) (rawSize z) _ ha).trans (congrFun hv z)
      · have ie : i.val < res.2.length := by rw [num']; exact i.isLt
        refine ⟨res.2.getD i.val 0,vr _ (ChainNet.getD_mem _ _ _ ie),?_⟩
        funext z
        have see (j : Nat) (hj : j < ys.length) :
            (ChainNet.wiresFrom gs (raw x z)).getD (ys.getD j 0) false = f ⟨j,by simpa [ys] using hj⟩ z := by
          let j' : Fin L := ⟨j,by simpa [ys] using hj⟩
          have idx : ys.getD j 0 = tap j' := by
            rw [List.getD_eq_getElem _ _ hj]
            exact List.getElem_ofFn ..
          rw [idx]
          exact congrFun (values j') z
        have sorted : ∀ a q : Nat, a < ys.length → q < ys.length → a ≤ q →
            (ChainNet.wiresFrom gs (raw x z)).getD (ys.getD q 0) false ≤
            (ChainNet.wiresFrom gs (raw x z)).getD (ys.getD a 0) false := by
          intro a q ha hq le
          rw [see q hq,see a ha]
          exact ordered z _ _ le
        have iz : i.val < ys.length := by simpa [ys] using i.isLt
        exact (correct (raw x z) (rawSize z) sorted _ iz).trans (congrArg Bool.not (see _ iz))

end Select
end PEqualNP.Outside.L_lib_1425

namespace PEqualNP.Outside.L_lib_1425
namespace Select
open scoped Classical

theorem dropLen {Q : Type} [Preorder Q] {m : Nat} (T : Q → Fin m → Bool) {l : Nat} {v i} :
    Reach T (l+2) v i → Reach T (l+1) v i := by
  induction l generalizing v i with
  | zero =>
    rintro ⟨u,le,hit,_⟩
    exact ⟨u,le,hit⟩
  | succ l ih =>
    rintro ⟨u,le,hit,j,ne,prev⟩
    exact ⟨u,le,hit,j,ne,ih prev⟩

theorem shorten {Q : Type} [Preorder Q] {m : Nat} (T : Q → Fin m → Bool) {l n : Nat} {v i}
    (le : l ≤ n) : Reach T (n+1) v i → Reach T (l+1) v i := by
  induction le with
  | refl => exact id
  | step _ ih => exact fun reach => ih (dropLen T reach)

theorem extendAt {Q : Type} [Preorder Q] {m : Nat} {T : Q → Fin m → Bool} {l : Nat}
    {v i j} (reach : Reach T (l+1) v j) (label : T v i = true) (ne : j ≠ i) :
    Reach T (l+2) v i := ⟨v,le_rfl,label,j,ne,reach⟩

theorem lastLabel {Q : Type} [Preorder Q] [OrderTop Q] {m K : Nat} (kpos : 0<K)
    (T : Q → Fin m → Bool) (v : Q) (i j : Fin m) (hi : T v i = true)
    (ok : ¬ ∃ a, Reach T (K+1) ⊤ a) :
    (∃ l : Fin K, Reach T (l.val+1) v j ∧ (l.val+2 > K ∨ ¬∃ a, Reach T (l.val+2) v a)) ↔ i=j := by
  constructor
  · rintro ⟨l,reach,upper⟩
    by_contra ne
    have next := extendAt reach hi (Ne.symm ne)
    rcases upper with top | no
    · have eq : l.val+2 = K+1 := by have := l.isLt; omega
      rw [eq] at next
      exact ok ⟨i,DP.reachMono T le_top _ _ next⟩
    · exact no ⟨i,next⟩
  · rintro rfl
    let P := fun l : Fin K => ∃ a, Reach T (l.val+1) v a
    let L := Finset.univ.filter P
    have nonempty : L.Nonempty := by
      refine ⟨⟨0,kpos⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩
      exact ⟨i,v,le_rfl,hi⟩
    let l := L.max' nonempty
    obtain ⟨a,reach⟩ := (Finset.mem_filter.mp (L.max'_mem nonempty)).2
    have last : ¬ ∃ a, Reach T (l.val+2) v a := by
      rintro ⟨a,more⟩
      by_cases cap : l.val+1 < K
      · have member : (⟨l.val+1,cap⟩ : Fin K) ∈ L :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _,a,more⟩
        have ge : l.val+1 ≤ l.val := L.le_max' _ member
        omega
      · have eq : l.val+2 = K+1 := by have := l.isLt; omega
        rw [eq] at more
        exact ok ⟨a,DP.reachMono T le_top _ _ more⟩
    have eq : a = i := by
      by_contra ne
      exact last ⟨i,extendAt reach hi ne⟩
    exact ⟨l,eq ▸ reach,Or.inr last⟩

end Select
end PEqualNP.Outside.L_lib_1425

namespace PEqualNP.Outside.L_lib_1425
namespace Select
open scoped Classical
open StageNet

theorem output {n p r d m b k : Nat} {x : Fin p → Finset (Fin n)} {S : Set (Col p)}
    (g : Fin r → Fin d) (data : Fin p → Box g → Fin m → Bool) (A : Fin p → Finset (Fin r))
    (H : Built x [] k S) (zero : (fun _ => false) ∈ S) (one : (fun _ => true) ∈ S)
    (avail : ∀ l, 0 < l → l ≤ min (2^b) (r+1)+1 → ∀ i, DP.queryCol g data A l i ∈ S) :
    let K := min (2^b) (r+1)
    ∃ tr V, tr.length ≤ b ∧ Built x tr (k+5*(r+1)^2+5*(K+2)*(m+1)) V ∧ S ⊆ V ∧
      ∃ signals : Fin m → Col p, (∀ i, signals i ∈ V) ∧
      ∀ z, (¬ ∃ i, Reach (data z) (K+1) ⊤ i) → ∀ i, data z (query g (A z)) i = true →
        ∀ j, signals j z = decide (i=j) := by
  classical
  let K := min (2^b) (r+1)
  have kp : 0 < K := Nat.lt_min.mpr ⟨Nat.two_pow_pos _,by omega⟩
  have kr : K ≤ r+1 := Nat.min_le_right _ _
  let level := fun l i => DP.queryCol g data A l i
  let v := fun z => query g (A z)
  let hi := fun (l : Fin (K-1)) (z : Fin p) => decide (∃ a, Reach (data z) (l.val+2) (v z) a)
  obtain ⟨U,bU,sU,hu⟩ := batch (Finset.univ : Finset (Fin (K-1))) hi m H (by
    intro k' S' built ext l _
    have cap : l.val+2 ≤ K+1 := by have := l.isLt; omega
    obtain ⟨W,bW,sw,got⟩ := anyFold (Finset.univ : Finset (Fin m)) (level (l.val+2)) built (ext zero)
      (fun j _ => ext (avail _ (by omega) cap j))
    refine ⟨W,by simpa using bW,sw,?_⟩
    convert got using 1
    funext z
    simp [hi,level,v,DP.queryCol])
  have hU : Built x [] (k+(K-1)*m) U := by simpa using bU
  have sorted : ∀ z i j, i ≤ j → hi j z ≤ hi i z := by
    intro z i j le
    apply Bool.le_iff_imp.mpr
    intro yes
    obtain ⟨a,ra⟩ := of_decide_eq_true yes
    exact decide_eq_true ⟨a,shorten (data z) (show i.val+1 ≤ j.val+1 from Nat.succ_le_succ le) ra⟩
  have below : K-1 < 2^b := by have := Nat.min_le_left (2^b) (r+1); omega
  obtain ⟨tr,V,tlen,bV,uv,cpl⟩ := invertThresholds hU hi (fun i => hu i (Finset.mem_univ _)) sorted below
  let tail := fun (l : Fin K) (z : Fin p) =>
    if h : l.val < K-1 then !(hi ⟨l.val,h⟩ z) else true
  have tv (l : Fin K) : tail l ∈ V := by
    by_cases h : l.val < K-1
    · simpa [tail,h] using cpl ⟨l.val,h⟩
    · simpa [tail,h] using uv (sU one)
  let term := fun (i : Fin m) (l : Fin K) => conj (level (l.val+1) i) (tail l)
  let sig := fun (i : Fin m) (z : Fin p) => decide (∃ l : Fin K, term i l z = true)
  obtain ⟨F,bF,vF,got⟩ := batch (Finset.univ : Finset (Fin m)) sig (2*K) bV (by
    intro k' S' built ext i _
    obtain ⟨W,bW,sW,haveTerm⟩ := batch (Finset.univ : Finset (Fin K)) (term i) 1 built (by
      intro q Z bz sz l _
      have bound : l.val+1 ≤ K+1 := by have := l.isLt; omega
      have le := avail (l.val+1) (by omega) bound i
      exact ⟨_,Built.andGate bz (sz (ext (uv (sU le)))) (sz (ext (tv l))),
        Set.subset_insert _ _,Set.mem_insert _ _⟩)
    obtain ⟨F',bF',sub',out'⟩ := anyFold (Finset.univ : Finset (Fin K)) (term i) bW
      (sW (ext (uv (sU zero)))) haveTerm
    refine ⟨F',bF'.relax (by simp; omega) Set.Subset.rfl,sW.trans sub',?_⟩
    convert out' using 1
    funext z
    simp [sig])
  refine ⟨tr,F,tlen,bF.relax ?_ Set.Subset.rfl,sU.trans (uv.trans vF),sig,
    fun i => got i (Finset.mem_univ _),?_⟩
  · simp only [Finset.card_univ,Fintype.card_fin]
    have v1 : (K-1)*m ≤ K*m := Nat.mul_le_mul_right m (Nat.sub_le _ _)
    have v2 : K-1 ≤ K := Nat.sub_le _ _
    change k + (K-1)*m + 5*(K-1) + m*(2*K) ≤ k+5*(r+1)^2+5*(K+2)*(m+1)
    nlinarith
  · intro z ok i hit j
    change decide (∃ l : Fin K, term j l z = true) = decide (i=j)
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    rw [← lastLabel kp (data z) (v z) i j hit ok]
    apply exists_congr
    intro l
    by_cases h : l.val < K-1
    · have no : ¬ (l.val+2 > K) := by omega
      simp [term,conj,level,DP.queryCol,tail,hi,h,no,v]
    · have top : l.val+2 > K := by have := l.isLt; omega
      simp [term,conj,level,DP.queryCol,tail,h,top,v]

end Select
end PEqualNP.Outside.L_lib_1425

namespace PEqualNP.Outside.L_lib_1425
namespace Select
theorem ready {r d m : Nat} (b : Nat) (g : Fin r → Fin d) : DP.Selection (m:=m) b g := by
  intro n p k x data words S H zero one avail
  exact output g data words H zero one avail
end Select
end PEqualNP.Outside.L_lib_1425

namespace PEqualNP.Outside.L_lib_1425
open PEqualNP.CircuitLowerBounds
open scoped Classical

theorem postedBits {r : Nat} (X : Finset (Fin r)) :
    (List.ofFn (fun j : Fin r => @decide (j ∈ X) (Classical.propDecidable _))) = Bits X := by
  unfold Bits
  apply congrArg List.ofFn
  funext j
  by_cases h : j ∈ X <;> simp [h]

theorem postedEquality {m : Nat} (i j : Fin m) :
    @decide (i=j) (Classical.propDecidable _) = decide (i=j) := by
  by_cases h : i=j <;> simp [h]

theorem postedInter {r : Nat} (X Y : Finset (Fin r)) :
    (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
     X ∩ Y) = X ∩ Y := by
  ext a
  simp

def GoalFor {r d m b : Nat} (blocks : Fin d → Finset (Fin r)) : Prop :=
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  let valid := fun (n : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) =>
    PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) D ∧ D.output < n+2+D.size
  let bits := fun {n : Nat} (X : Finset (Fin n)) => List.ofFn (fun j : Fin n => decide (j ∈ X))
  let possible := fun {r m : Nat} (b : Nat) (lab : Finset (Fin r) → Fin m → Prop) =>
    ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (out : Fin m → Nat), valid r D ∧
      (∀ j, out j < r+2+D.size) ∧ PEqualNP.NotBracket.notCount D ≤ b ∧
      ∀ X i, lab X i → ∀ j, (D.wires (bits X ++ [false,true])).getD (out j) false = decide (i=j)
  let Q := (j : Fin d) → Fin ((blocks j).card+1)
  let N := Fintype.card Q
  let K := min (2^b) (r+1)
  let n := N*m+r
  let B := 8*(r+1)^2+32*(d+2)*(N+1)*(m+1)*(K+2)
  ∀ index : Fin N ≃ Q, ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (out : Fin m → Nat), valid n D ∧
    (∀ j, out j < n+2+D.size) ∧ PEqualNP.NotBracket.notCount D ≤ b ∧ D.size-PEqualNP.NotBracket.notCount D ≤ B ∧
    ∀ (T : Q → Fin m → Bool) (X : Finset (Fin r)),
      let lab := fun (Y : Finset (Fin r)) (i : Fin m) => ∃ v : Q,
        (∀ j, (v j).val=(Y ∩ blocks j).card) ∧ T v i=true
      let I := (List.ofFn (fun z : Fin N => List.ofFn (fun i : Fin m => T (index z) i))).flatten ++ bits X ++ [false,true]
      (D.eval I = false ↔ possible b lab) ∧
      (possible b lab → ∀ i, lab X i → ∀ j, (D.wires I).getD (out j) false = decide (i=j))

set_option maxHeartbeats 1400000 in
theorem finishCore (select : ∀ {r d m b : Nat}, ∀ g : Fin r → Fin d, DP.Selection (m:=m) b g) {r d m b : Nat} (g : Fin r → Fin d) : GoalFor (m:=m) (b:=b) (block g) := by
  classical
  unfold GoalFor
  intro valid bits possible Q N
  have hn : N = Fintype.card (Box g) := by
    apply congrArg (fun inst : Fintype (Box g) => @Fintype.card (Box g) inst)
    exact Subsingleton.elim _ _
  rw [hn]
  dsimp only [valid,bits,possible,Q]
  intro index
  obtain ⟨D,out,hD,outBound,notBound,sizeBound,good⟩ :=
    DP.uniform g index (@select r d m b g)
  refine ⟨D,out,hD,outBound,notBound,sizeBound,?_⟩
  intro T X
  let P := DP.tableList index T
  have lengthP := DP.tableListLength index T
  let lab := fun (Y : Finset (Fin r)) (i : Fin m) =>
    ∃ v : Box g, (∀ j, (v j).val=(Y ∩ block g j).card) ∧ T v i=true
  simp only [postedBits,postedEquality,postedInter]
  change (D.eval (P ++ Bits X ++ [false,true]) = false ↔ Possible b lab) ∧
    (Possible b lab → ∀ i, lab X i → ∀ j, (D.wires (P ++ Bits X ++ [false,true])).getD (out j) false = decide (i=j))
  have iffLab : Possible b lab ↔ Possible b (fun Y i => T (query g Y) i = true) := possible_lab_iff g T
  have noBad (poss : Possible b lab) : ¬∃ i, Reach T (DP.Limit r b+1) ⊤ i :=
    Nec.necessary g T (iffLab.mp poss)
  refine ⟨⟨?_, fun poss => (good T X).1.mpr (noBad poss)⟩,?_⟩
  · intro flag
    have hn := (good T X).1.mp flag
    apply iffLab.mpr
    obtain ⟨E,o,ev,ow,eqNot,tap⟩ := Hardwire.hardwire P lengthP D out hD outBound
    refine ⟨E,o,ev,ow,eqNot.le.trans notBound,?_⟩
    intro Y i hi j
    exact (tap Y j).trans ((good T Y).2 hn i hi j)
  · intro poss i hi j
    exact (good T X).2 (noBad poss) i ((lab_query_iff g T X i).mp hi) j

set_option maxHeartbeats 1400000 in
theorem finish (select : ∀ {r d m b : Nat}, ∀ g : Fin r → Fin d, DP.Selection (m:=m) b g) :
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  let valid := fun (n : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) =>
    PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) D ∧ D.output < n+2+D.size
  let bits := fun {n : Nat} (X : Finset (Fin n)) => List.ofFn (fun j : Fin n => decide (j ∈ X))
  let possible := fun {r m : Nat} (b : Nat) (lab : Finset (Fin r) → Fin m → Prop) =>
    ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (out : Fin m → Nat), valid r D ∧
      (∀ j, out j < r+2+D.size) ∧ PEqualNP.NotBracket.notCount D ≤ b ∧
      ∀ X i, lab X i → ∀ j, (D.wires (bits X ++ [false,true])).getD (out j) false = decide (i=j)
  ∀ (r d m b : Nat) (g : Fin r → Fin d),
    let block := fun j : Fin d => Finset.univ.filter (fun i : Fin r => g i=j)
    let Q := (j : Fin d) → Fin ((block j).card+1)
    let N := Fintype.card Q
    let K := min (2^b) (r+1)
    let n := N*m+r
    let B := 8*(r+1)^2+32*(d+2)*(N+1)*(m+1)*(K+2)
    ∀ index : Fin N ≃ Q, ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (out : Fin m → Nat), valid n D ∧
      (∀ j, out j < n+2+D.size) ∧ PEqualNP.NotBracket.notCount D ≤ b ∧ D.size-PEqualNP.NotBracket.notCount D ≤ B ∧
      ∀ (T : Q → Fin m → Bool) (X : Finset (Fin r)),
        let lab := fun (Y : Finset (Fin r)) (i : Fin m) => ∃ v : Q,
          (∀ j, (v j).val=(Y ∩ block j).card) ∧ T v i=true
        let I := (List.ofFn (fun z : Fin N => List.ofFn (fun i : Fin m => T (index z) i))).flatten ++ bits X ++ [false,true]
        (D.eval I = false ↔ possible b lab) ∧
        (possible b lab → ∀ i, lab X i → ∀ j, (D.wires I).getD (out j) false = decide (i=j)) := by
  classical
  dsimp only
  intro r d m b g
  let B : Fin d → Finset (Fin r) := fun j =>
    @Finset.filter (Fin r) (fun i => g i=j) (fun i => Classical.propDecidable _) Finset.univ
  change GoalFor (m:=m) (b:=b) B
  have hB : B = block g := by
    funext j; ext i; simp [B,block]
  rw [hB]
  exact finishCore select g

end PEqualNP.Outside.L_lib_1425

open PEqualNP.Outside.L_lib_1425 in
theorem PEqualNP.Outside.L_lib_1425 :
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  let valid := fun (n : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) =>
    PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) D ∧ D.output < n+2+D.size
  let bits := fun {n : Nat} (X : Finset (Fin n)) => List.ofFn (fun j : Fin n => decide (j ∈ X))
  let possible := fun {r m : Nat} (b : Nat) (lab : Finset (Fin r) → Fin m → Prop) =>
    ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (out : Fin m → Nat), valid r D ∧
      (∀ j, out j < r+2+D.size) ∧ PEqualNP.NotBracket.notCount D ≤ b ∧
      ∀ X i, lab X i → ∀ j, (D.wires (bits X ++ [false,true])).getD (out j) false = decide (i=j)
  ∀ (r d m b : Nat) (g : Fin r → Fin d),
    let block := fun j : Fin d => Finset.univ.filter (fun i : Fin r => g i=j)
    let Q := (j : Fin d) → Fin ((block j).card+1)
    let N := Fintype.card Q
    let K := min (2^b) (r+1)
    let n := N*m+r
    let B := 8*(r+1)^2+32*(d+2)*(N+1)*(m+1)*(K+2)
    ∀ index : Fin N ≃ Q, ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (out : Fin m → Nat), valid n D ∧
      (∀ j, out j < n+2+D.size) ∧ PEqualNP.NotBracket.notCount D ≤ b ∧ D.size-PEqualNP.NotBracket.notCount D ≤ B ∧
      ∀ (T : Q → Fin m → Bool) (X : Finset (Fin r)),
        let lab := fun (Y : Finset (Fin r)) (i : Fin m) => ∃ v : Q,
          (∀ j, (v j).val=(Y ∩ block j).card) ∧ T v i=true
        let I := (List.ofFn (fun z : Fin N => List.ofFn (fun i : Fin m => T (index z) i))).flatten ++ bits X ++ [false,true]
        (D.eval I = false ↔ possible b lab) ∧
        (possible b lab → ∀ i, lab X i → ∀ j, (D.wires I).getD (out j) false = decide (i=j)) := by
  exact finish (fun {r d m b} g => Select.ready (m:=m) b g)

import PEqualNP.Defs
import Mathlib.Data.Finset.Sort
namespace PEqualNP.Outside.L_lib_1426
namespace PulseList
open CircuitLowerBounds
def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = run C.gates x := rfl

theorem run_append (a b : List Gate) (w : List Bool) : run (a ++ b) w = run b (run a w) := by
  unfold run; rw [List.foldl_append]

theorem run_nil (w : List Bool) : run [] w = w := rfl

theorem run_singleton (g : Gate) (w : List Bool) :
    run [g] w = w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] := rfl

theorem run_prefix (gs : List Gate) :
    ∀ w : List Bool, ∃ t, run gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [run]⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, ?_⟩
    · rw [show g :: gs = [g] ++ gs from rfl, run_append, run_singleton, ht]; simp
    · simp [hl]

theorem run_length (gs : List Gate) (w : List Bool) : (run gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := run_prefix gs w
  rw [ht, List.length_append, hl]

theorem getD_run (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := run_prefix gs w
  rw [ht]; simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_snoc_length (l : List Bool) (a : Bool) : (l ++ [a]).getD l.length false = a := by
  simp

theorem eval_or2 (a b : Bool) : GateOp.eval GateOp.or [a, b] = (a || b) := by
  cases a <;> cases b <;> rfl

theorem eval_and2 (a b : Bool) : GateOp.eval GateOp.and [a, b] = (a && b) := by
  cases a <;> cases b <;> rfl

end PulseList

namespace FiniteGateBank

open CircuitLowerBounds MetaComplexity MetaComplexity.NestedCover
open PulseList (run run_length run_append run_singleton)

open Classical

variable {X J : Type} {n : Nat}

structure Net (n : Nat) where
  gates : List Gate
  fan : FanInTwo ⟨gates,0⟩
  back : ∀ j (hj : j < gates.length), ∀ i ∈ gates[j].inputs, i < n+j

def empty (n : Nat) : Net n := ⟨[],by simp [FanInTwo],by simp⟩

def Net.cost (p : Net n) := NotBracket.notCount ⟨p.gates,0⟩

def Net.has (p : Net n) (raw : X → List Bool) (f : X → Bool) :=
  ∃ i, i < n+p.gates.length ∧ ∀ x, (run p.gates (raw x)).getD i false = f x

def Grow (raw : X → List Bool) (p q : Net n) (size neg : Nat) : Prop :=
  (∀ f, p.has raw f → q.has raw f) ∧ q.gates.length ≤ p.gates.length+size ∧ q.cost=p.cost+neg

theorem start (raw : X → List Bool) (p : Net n) : Grow raw p p 0 0 := by simp [Grow]

theorem chain {raw : X → List Bool} {p q r : Net n} {a b c d : Nat}
    (pq : Grow raw p q a b) (qr : Grow raw q r c d) : Grow raw p r (a+c) (b+d) :=
  ⟨fun f h => qr.1 f (pq.1 f h),by have := pq.2.1; have := qr.2.1; omega,
    by rw [qr.2.2,pq.2.2,Nat.add_assoc]⟩

theorem allowance {raw : X → List Bool} {p q : Net n} {a b c : Nat}
    (grow : Grow raw p q a b) (le : a≤c) : Grow raw p q c b :=
  ⟨grow.1,grow.2.1.trans (Nat.add_le_add_left le _),grow.2.2⟩

private def extend (p : Net n) (g : Gate)
    (ops : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (ok : ∀ i ∈ g.inputs, i < n+p.gates.length) : Net n where
  gates := p.gates++[g]
  fan := by
    intro v hv
    rcases List.mem_append.mp hv with old | last
    · exact p.fan v old
    · exact (List.mem_singleton.mp last) ▸ ops
  back := by
    intro j hj i hi
    by_cases h : j < p.gates.length
    · rw [List.getElem_append_left h] at hi
      exact p.back j h i hi
    · have len : j=p.gates.length := by simp at hj; omega
      subst j
      simp at hi
      exact ok i hi

private theorem emit {raw : X → List Bool} (width : ∀ x, (raw x).length=n)
    (p : Net n) (g : Gate)
    (ops : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (ok : ∀ i ∈ g.inputs, i < n+p.gates.length) :
    ∃ q, Grow raw p q 1 (if g.op=.not then 1 else 0) ∧
      q.has raw (fun x => g.op.eval (g.inputs.map (fun i => (run p.gates (raw x)).getD i false))) := by
  let q := extend p g ops ok
  have len (x : X) : (run p.gates (raw x)).length=n+p.gates.length := by rw [run_length,width]
  refine ⟨q,⟨?_,by simp [q,extend],?_⟩,n+p.gates.length,by simp [q,extend],?_⟩
  · rintro f ⟨i,hi,read⟩
    refine ⟨i,by simp [q,extend]; omega,?_⟩
    intro x
    change (run (p.gates++[g]) (raw x)).getD i false = _
    rw [run_append,run_singleton,List.getD_append _ _ _ _ ((len x).symm ▸ hi),read]
  · unfold Net.cost NotBracket.notCount
    simp only [q,extend,List.filter_append,List.length_append]
    split <;> simp_all
  · intro x
    change (run (p.gates++[g]) (raw x)).getD (n+p.gates.length) false = _
    rw [run_append,run_singleton,←len x]; simp

theorem binary {raw : X → List Bool} (width : ∀ x, (raw x).length=n)
    (p : Net n) (a b : X → Bool) (ha : p.has raw a) (hb : p.has raw b) (isAnd : Bool) :
    ∃ q, Grow raw p q 1 0 ∧ q.has raw (fun x => if isAnd then a x && b x else a x || b x) := by
  obtain ⟨i,hi,readI⟩ := ha
  obtain ⟨j,hj,readJ⟩ := hb
  let g : Gate := ⟨if isAnd then .and else .or,[i,j]⟩
  obtain ⟨q,grow,w⟩ := emit width p g (by cases isAnd <;> simp [g]) (by simp [g,hi,hj])
  refine ⟨q,by cases isAnd <;> simpa [g] using grow,?_⟩
  convert w using 2 with x
  cases isAnd <;> simp only [g,Bool.false_eq_true,ite_false,ite_true,List.map_cons,List.map_nil,
    PulseList.eval_and2,PulseList.eval_or2, readI,readJ] <;> rfl

theorem invert {raw : X → List Bool} (width : ∀ x, (raw x).length=n)
    (p : Net n) (a : X → Bool) (ha : p.has raw a) :
    ∃ q, Grow raw p q 1 1 ∧ q.has raw (fun x => !(a x)) := by
  obtain ⟨i,hi,readI⟩ := ha
  let g : Gate := ⟨.not,[i]⟩
  obtain ⟨q,grow,w⟩ := emit width p g (by simp [g]) (by simp [g,hi])
  refine ⟨q,by simpa [g] using grow,?_⟩
  convert w using 2 with x
  change (!(a x)) = (!((run p.gates (raw x)).getD i false))
  rw [readI]

theorem anyList {raw : X → List Bool} (width : ∀ x, (raw x).length=n) (p : Net n)
    (zero : p.has raw (fun _ => false)) (l : List J) (f : J → X → Bool)
    (known : ∀ i ∈ l, p.has raw (f i)) :
    ∃ q, Grow raw p q l.length 0 ∧ q.has raw (fun x => l.any (fun j => f j x)) := by
  induction l with
  | nil => exact ⟨p,start _ _,zero⟩
  | cons j l ih =>
    obtain ⟨q,gq,old⟩ := ih (fun i hi => known i (by simp [hi]))
    obtain ⟨r,gr,ans⟩ := binary width q _ _ (gq.1 _ (known j (by simp))) old false
    exact ⟨r,chain gq gr,by simpa [List.any_cons] using ans⟩

theorem batch {raw : X → List Bool} (p : Net n) (l : List J) (f : J → X → Bool) (s z : Nat)
    (build : ∀ j ∈ l, ∀ q : Net n, (∀ a, p.has raw a → q.has raw a) →
      ∃ r, Grow raw q r s z ∧ r.has raw (f j)) :
    ∃ r, Grow raw p r (l.length*s) (l.length*z) ∧ ∀ j ∈ l, r.has raw (f j) := by
  induction l with
  | nil => exact ⟨p,by simpa using start raw p,by simp⟩
  | cons j l ih =>
    obtain ⟨q,gq,old⟩ := ih (fun i hi => build i (by simp [hi]))
    obtain ⟨r,gr,ans⟩ := build j (by simp) q gq.1
    refine ⟨r,by simpa [Nat.succ_mul] using chain gq gr,?_⟩
    intro i mem
    rcases List.mem_cons.mp mem with rfl | h
    · exact ans
    · exact gr.1 _ (old i h)

theorem Net.readsBack (p : Net n) : ReadsBack n ⟨p.gates,0⟩ := by
  intro j hj i hi
  exact p.back j hj i (by simpa [gateAt,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj] using hi)

end FiniteGateBank

namespace OrderedThresholdBank

open FiniteGateBank

variable {X : Type} {n : Nat}

def high (r : X → Nat) (i : Nat) (x : X) := decide (i ≤ r x)
def low (r : X → Nat) (i : Nat) (x : X) := decide (r x < i)

theorem decode (raw : X → List Bool) (width : ∀ x, (raw x).length=n) (b k : Nat)
    (room : k < 2^b) (r : X → Nat) (bound : ∀ x, r x≤k) (p : Net n)
    (zero : p.has raw (fun _ => false)) (known : ∀ i : Nat, 0 < i → i ≤ k → p.has raw (high r i)) :
    ∃ q, Grow raw p q (4*k+b) b ∧ ∀ i : Nat, 0 < i → i ≤ k → q.has raw (low r i) := by
  induction b generalizing k r p with
  | zero =>
    have : k=0 := by simpa using room
    subst k
    exact ⟨p,by simpa using start raw p,by omega⟩
  | succ b ih =>
    let a := k/2
    let m := a+1
    let rem (x : X) := if r x < m then r x else r x-m
    have small : k < 2*m := by dsimp [m,a]; omega
    have rem_le (x) : rem x≤a := by
      have := bound x
      dsimp [rem,m,a] at *
      split <;> omega
    have limited : a < 2^b := by dsimp [a]; rw [pow_succ] at room; omega
    have avail (i) (pos : 0 < i) : p.has raw (high r i) := by
      by_cases le : i≤k
      · exact known i pos le
      · convert zero using 2 with x
        simp [high,show ¬i≤r x by have := bound x; omega]
    obtain ⟨p₁,g₁,hneg⟩ := invert width p (high r m) (avail m (by dsimp [m]; omega))
    let ids := List.range a
    obtain ⟨p₂,g₂,hrem⟩ := batch (raw:=raw) p₁ ids (fun j => high rem (j+1)) 2 0 (by
      intro j hj q keep
      have index : j < a := List.mem_range.mp hj
      obtain ⟨u,gu,band⟩ := binary width q _ _ (keep _ hneg) (keep _ (g₁.1 _ (avail (j+1) (by omega)))) true
      obtain ⟨v,gv,bor⟩ := binary width u _ _ band (gu.1 _ (keep _ (g₁.1 _ (avail (m+(j+1)) (by omega))))) false
      refine ⟨v,chain gu gv,?_⟩
      convert bor using 2 with x
      have := bound x
      apply Bool.eq_iff_iff.mpr
      simp only [high,rem,Bool.or_eq_true,Bool.and_eq_true,Bool.not_eq_true',decide_eq_true_eq,
        decide_eq_false_iff_not,ite_true,ite_false,Bool.false_eq_true]
      dsimp [m] at *
      split <;> omega)
    have residual (i) (pos : 0 < i) (le : i≤a) : p₂.has raw (high rem i) := by
      obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i≠0)
      exact hrem j (List.mem_range.mpr (by omega))
    obtain ⟨p₃,g₃,remneg⟩ := ih a limited rem rem_le p₂ (g₂.1 _ (g₁.1 _ zero)) residual
    have g123 := chain (chain g₁ g₂) g₃
    have mid := g₃.1 _ (g₂.1 _ hneg)
    obtain ⟨q,g₄,outs⟩ := batch (raw:=raw) p₃ (List.range k) (fun j => low r (j+1)) 1 0 (by
      intro j hj u keep
      have jk : j < k := List.mem_range.mp hj
      by_cases below : j+1 < m
      · have le : j+1≤a := by dsimp [m] at below; omega
        obtain ⟨v,g,h⟩ := binary width u _ _ (keep _ mid) (keep _ (remneg (j+1) (by omega) le)) true
        refine ⟨v,g,?_⟩
        convert h using 2 with x
        apply Bool.eq_iff_iff.mpr
        simp only [low,high,rem,ite_true,Bool.and_eq_true,Bool.not_eq_true',decide_eq_true_eq,decide_eq_false_iff_not]
        split <;> omega
      · by_cases eq : j+1=m
        · refine ⟨u,allowance (start raw u) (by decide : 0≤1),?_⟩
          convert keep _ mid using 2 with x
          apply Bool.eq_iff_iff.mpr
          simp only [high,low,Bool.not_eq_true',decide_eq_true_eq,decide_eq_false_iff_not]
          omega
        · have above : m < j+1 := by omega
          have ix : j+1-m≤a := by dsimp [m,a] at *; omega
          obtain ⟨v,g,h⟩ := binary width u _ _ (keep _ mid) (keep _ (remneg (j+1-m) (by omega) ix)) false
          refine ⟨v,g,?_⟩
          convert h using 2 with x
          apply Bool.eq_iff_iff.mpr
          simp only [low,high,rem,Bool.false_eq_true,ite_false,Bool.or_eq_true,Bool.not_eq_true',decide_eq_true_eq,decide_eq_false_iff_not]
          split <;> omega)
    have gr := chain g123 g₄
    simp only [ids,List.length_range,Nat.mul_zero,Nat.add_zero,Nat.mul_one] at gr
    refine ⟨q,?_,?_⟩
    · have gr' := allowance gr (show 1 + a*2 + (4*a+b) + k ≤ 4*k+(b+1) by dsimp [a]; omega)
      simpa [Nat.add_comm 1 b] using gr'
    · intro i pos le
      obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i≠0)
      exact outs j (List.mem_range.mpr (by omega))

end OrderedThresholdBank



variable {α : Type} [DecidableEq α]

def Label (A B X : Finset α) (a f : ℕ) := ∃ C : Finset α, A ⊆ C ∧ C ⊆ B ∧ (C\X).card≤a ∧ (X\C).card≤f

theorem label_iff {A B X : Finset α} {a f} : Label A B X a f ↔ A⊆B ∧ (A\X).card≤a ∧ (X\B).card≤f := by
  constructor
  · rintro ⟨C,h1,h2,ha,hf⟩
    refine ⟨h1.trans h2,(Finset.card_le_card (t:=C\X) ?_).trans ha,(Finset.card_le_card (t:=X\C) ?_).trans hf⟩
    · intro z hz; exact Finset.mem_sdiff.mpr ⟨h1 (Finset.mem_sdiff.mp hz).1,(Finset.mem_sdiff.mp hz).2⟩
    · intro z hz; exact Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hz).1,fun h => (Finset.mem_sdiff.mp hz).2 (h2 h)⟩
  · rintro ⟨live,ha,hf⟩
    refine ⟨A ∪ (X ∩ B),Finset.subset_union_left,Finset.union_subset live Finset.inter_subset_right,?_,?_⟩
    · apply (Finset.card_le_card (t:=A\X) ?_).trans ha
      intro x hx; simp only [Finset.mem_sdiff,Finset.mem_union,Finset.mem_inter] at *; tauto
    · apply (Finset.card_le_card (t:=X\B) ?_).trans hf
      intro x hx; simp only [Finset.mem_sdiff,Finset.mem_union,Finset.mem_inter] at *; tauto

theorem triangle (A B X : Finset α) : (A\B).card ≤ (A\X).card+(X\B).card := by
  apply le_trans (Finset.card_le_card (t:=(A\X) ∪ (X\B)) ?_) (Finset.card_union_le _ _)
  intro x hx; simp only [Finset.mem_sdiff,Finset.mem_union] at *; tauto

theorem split_diff (K : Finset α) (a f : ℕ) (h : K.card≤a+f) : ∃ U⊆K, (K\U).card≤a ∧ U.card≤f := by
  obtain ⟨U,hu,card⟩ := Finset.exists_subset_card_eq (s:=K) (min_le_left K.card f)
  exact ⟨U,hu,by rw [Finset.card_sdiff_of_subset hu,card]; omega,card.trans_le (min_le_right _ _)⟩

theorem overlap {A B C D : Finset α} {a f e g : ℕ} (ab : A ⊆ B) (cd : C ⊆ D)
    (h1 : (A\D).card ≤ a+g) (h2 : (C\B).card ≤ e+f) : ∃ X, Label A B X a f ∧ Label C D X e g := by
  obtain ⟨U,hu,ua,ug⟩ := split_diff _ _ _ h1
  obtain ⟨V,hv,ve,vf⟩ := split_diff _ _ _ h2
  let X := (A∩D) ∪ (C∩B) ∪ U ∪ V
  have subA : A\X ⊆ (A\D)\U := by dsimp [X]; intro x h; simp only [Finset.mem_union,Finset.mem_sdiff,Finset.mem_inter] at *; tauto
  have subC : C\X ⊆ (C\B)\V := by dsimp [X]; intro x h; simp only [Finset.mem_union,Finset.mem_sdiff,Finset.mem_inter] at *; tauto
  have subB : X\B ⊆ V := by
    intro x h; have u := fun hx : x∈U => ab (Finset.mem_sdiff.mp (hu hx)).1
    dsimp [X] at h; simp only [Finset.mem_union,Finset.mem_sdiff,Finset.mem_inter] at h; have b := @ab x; tauto
  have subD : X\D ⊆ U := by
    intro x h; have v := fun hx : x∈V => cd (Finset.mem_sdiff.mp (hv hx)).1
    dsimp [X] at h; simp only [Finset.mem_union,Finset.mem_sdiff,Finset.mem_inter] at h; have d := @cd x; tauto
  exact ⟨X,label_iff.mpr ⟨ab,(Finset.card_le_card subA).trans ua,(Finset.card_le_card subB).trans vf⟩,
    label_iff.mpr ⟨cd,(Finset.card_le_card subC).trans ve,(Finset.card_le_card subD).trans ug⟩⟩


open FiniteGateBank
variable {X J : Type} [DecidableEq J] {n : ℕ} {raw : X → List Bool}

def tally (S : Finset J) (v : X → J → Bool) (x : X) := (S.filter (fun j => v x j=true)).card

theorem counter (width : ∀ x,(raw x).length=n) (v : X → J → Bool) (w : ℕ) (S : Finset J) (p : Net n)
    (one : p.has raw (fun _ => true)) (zero : p.has raw (fun _ => false)) (get : ∀ j∈S, p.has raw (fun x => v x j)) :
    ∃ q, Grow raw p q (2*w*S.card) 0 ∧ ∀ z ≤ w, q.has raw (fun x => decide (z ≤ tally S v x)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨p,by simpa using start raw p,?_⟩; intro z _; by_cases hz : z=0
    · simpa [tally,hz] using one
    · simpa [tally,hz] using zero
  | @insert j S hj ih =>
    obtain ⟨q,gq,hq⟩ := ih (fun i hi => get i (Finset.mem_insert_of_mem hi))
    obtain ⟨u,gu,hu⟩ := batch (raw:=raw) q (List.range w) (fun k x => decide (k+1 ≤ tally (insert j S) v x)) 2 0 (by
      intro k hk net keep; have kw := List.mem_range.mp hk
      obtain ⟨s,gs,wa⟩ := binary width net _ _ (keep _ (hq k kw.le)) (keep _ (gq.1 _ (get j (Finset.mem_insert_self _ _)))) true
      obtain ⟨z,gz,wo⟩ := binary width s _ _ (gs.1 _ (keep _ (hq (k+1) kw))) wa false
      refine ⟨z,chain gs gz,?_⟩
      convert wo using 2 with x
      apply Bool.eq_iff_iff.mpr
      have notin : j ∉ S.filter (fun i => v x i=true) := fun h => hj (Finset.mem_filter.mp h).1
      have inc : tally (insert j S) v x = tally S v x + (if v x j = true then 1 else 0) := by
        unfold tally
        cases e : v x j <;> simp [Finset.filter_insert,e,Finset.card_insert_of_notMem,notin]
      change decide (k+1 ≤ tally (insert j S) v x) = true ↔ (decide (k+1 ≤ tally S v x) || (decide (k ≤ tally S v x) && v x j)) = true
      simp only [decide_eq_true_eq,Bool.or_eq_true,Bool.and_eq_true,inc]
      cases e : v x j <;> simp <;> omega)
    have bound : 2*w*S.card + (List.range w).length*2 ≤ 2*w*(insert j S).card := by rw [Finset.card_insert_of_notMem hj,List.length_range,Nat.mul_add]; omega
    refine ⟨u,by simpa using allowance (chain gq gu) bound,?_⟩
    intro z hz; cases z with
    | zero => simpa using gu.1 _ (gq.1 _ one)
    | succ k => exact hu _ (List.mem_range.mpr hz)

theorem testSub {d : ℕ} (width : ∀ x,(raw x).length=n) (v : X → Fin d → Bool) (S : Finset (Fin d)) (k : ℕ) (p : Net n)
    (one : p.has raw (fun _ => true)) (zero : p.has raw (fun _ => false)) (get : ∀ j,p.has raw (fun x => v x j)) :
    ∃ q, Grow raw p q (2*d*d) 0 ∧ q.has raw (fun x => decide (k ≤ tally S v x)) := by
  obtain ⟨q,g,hs⟩ := counter width v d S p one zero (fun j _ => get j)
  have sc : S.card ≤ d := by simpa using Finset.card_le_univ S
  refine ⟨q,allowance g (Nat.mul_le_mul_left _ sc),?_⟩
  by_cases hk : k≤d
  · exact hs k hk
  · convert g.1 _ zero using 2 with x
    have bound : tally S v x ≤ d := (Finset.card_filter_le _ _).trans sc
    simp [show ¬ k ≤ tally S v x by omega]


open FiniteGateBank OrderedThresholdBank

variable {X : Type} {n d : ℕ} {raw : X → List Bool}

theorem weightNeg (width : ∀ x,(raw x).length=n) (v : X → Fin d → Bool) (E : Finset ℕ) (b : ℕ)
    (bounds : ∀ z∈E,z≤d) (present : ∀ x, tally Finset.univ v x∈E) (room : E.card ≤ 2^b) (p : Net n)
    (one : p.has raw (fun _ => true)) (zero : p.has raw (fun _ => false)) (get : ∀ j,p.has raw (fun x => v x j)) :
    ∃ q, Grow raw p q (8*(d+1)^3+b) b ∧ ∀ j, q.has raw (fun x => !(v x j)) := by
  classical
  let e : Fin E.card ↪o ℕ := E.orderEmbOfFin rfl
  have em (i) : e i∈E := by simp [e]
  have existsRank (x) : ∃ i, e i=tally Finset.univ v x := by change _ ∈ Set.range (E.orderEmbOfFin rfl); simpa using present x
  choose idx eq using existsRank
  let r (x : X) := (idx x).val
  let k := E.card-1
  have lim (x) : r x≤k := by have := (idx x).isLt; dsimp [r,k]; omega
  obtain ⟨p1,g1,cts⟩ := counter width v d Finset.univ p one zero (fun j _ => get j)
  have rankTest (i : ℕ) (pos : 0 < i) (le : i ≤ k) : p1.has raw (high r i) := by
    have bound : i<E.card := by dsimp [k] at le; omega
    let j : Fin E.card := ⟨i,bound⟩
    convert cts (e j) (bounds _ (em j)) using 2 with x
    apply Bool.eq_iff_iff.mpr; simp only [high,decide_eq_true_eq]; rw [←eq]; change j ≤ idx x ↔ e j ≤ e (idx x); exact e.le_iff_le.symm
  have room' : k<2^b := by have := Nat.two_pow_pos b; dsimp [k]; omega
  obtain ⟨p2,g2,lowRank⟩ := decode raw width b k room' r lim p1 (g1.1 _ zero) rankTest
  have lower (i : Fin E.card) : p2.has raw (fun x => decide (tally Finset.univ v x ≤ e i)) := by
    by_cases h : i.val+1 ≤ k
    · convert lowRank (i.val+1) (by omega) h using 2 with x
      apply Bool.eq_iff_iff.mpr; simp only [low,decide_eq_true_eq]; rw [←eq,e.le_iff_le]; change (idx x).val ≤ i.val ↔ (idx x).val < i.val+1; omega
    · convert g2.1 _ (g1.1 _ one) using 2 with x
      apply decide_eq_true; rw [←eq,e.le_iff_le]; have := lim x; change (idx x).val ≤ i.val; change (idx x).val ≤ k at this; omega
  obtain ⟨q,g3,inv⟩ := batch (raw:=raw) p2 (List.finRange d) (fun j x => !(v x j)) (2*d*d+2*E.card) 0 (by
    intro j _ net keep
    let S : Finset (Fin d) := Finset.univ.erase j
    have cc : S.card ≤ d := by simpa using Finset.card_le_univ S
    obtain ⟨u,gu,other⟩ := counter width v d S net (keep _ (g2.1 _ (g1.1 _ one))) (keep _ (g2.1 _ (g1.1 _ zero)))
      (fun z _ => keep _ (g2.1 _ (g1.1 _ (get z))))
    let lit (i : Fin E.card) (x : X) := decide (tally Finset.univ v x ≤ e i) && decide (e i ≤ tally S v x)
    obtain ⟨z,gz,lits⟩ := batch (raw:=raw) u (List.finRange E.card) lit 1 0 (by
      intro i _ z kept
      obtain ⟨q,g,h⟩ := binary width z _ _ (kept _ (gu.1 _ (keep _ (lower i)))) (kept _ (other _ (bounds _ (em i)))) true
      exact ⟨q,g,h⟩)
    obtain ⟨z',gz',wire⟩ := anyList width z (gz.1 _ (gu.1 _ (keep _ (g2.1 _ (g1.1 _ zero))))) (List.finRange E.card) lit lits
    refine ⟨z',?_,?_⟩
    · have h := chain (chain gu gz) gz'; simp only [List.length_finRange,Nat.mul_one,Nat.mul_zero,Nat.add_zero] at h
      apply allowance h; have := Nat.mul_le_mul_left (2*d) cc; omega
    · convert wire using 2 with x
      have sum : tally Finset.univ v x = tally S v x + (if v x j=true then 1 else 0) := by
        have hs : insert j S=Finset.univ := Finset.insert_erase (Finset.mem_univ _)
        rw [←hs]
        unfold tally
        have hn : j ∉ S.filter (fun i => v x i = true) := fun h => (Finset.notMem_erase _ _) (Finset.mem_filter.mp h).1
        cases h : v x j <;> simp [Finset.filter_insert,h,hn]
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true, List.mem_finRange, true_and,lit,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true']
      constructor
      · intro off; exact ⟨idx x, (eq x).ge, by rw [eq]; simp_all⟩
      · rintro ⟨i,lo,hi⟩; cases h : v x j <;> simp_all <;> omega)
  have total := chain (chain g1 g2) g3
  simp only [List.length_finRange,Finset.card_univ,Fintype.card_fin,Nat.mul_zero,Nat.zero_add,Nat.add_zero] at total
  have ec : E.card ≤ d+1 := by
    have h := Finset.card_le_card (t:=Finset.range (d+1)) (s:=E) (fun z hz => Finset.mem_range.mpr (Nat.lt_succ_of_le (bounds z hz))); simpa using h
  have num : 2*d*d+(4*k+b)+d*(2*d*d+2*E.card) ≤ 8*(d+1)^3+b := by
    have hk : k≤d+1 := (Nat.sub_le _ _).trans ec
    calc
      _ ≤ 2*d*d+(4*(d+1)+b)+d*(2*d*d+2*(d+1)) := by gcongr
      _ ≤ _ := by ring_nf; omega
  exact ⟨q,allowance total num,fun j => inv j (List.mem_finRange j)⟩


open Classical CircuitLowerBounds MetaComplexity MetaComplexity.NestedCover FiniteGateBank

abbrev Book (m r : ℕ) := Fin m → Finset (Fin r)
noncomputable def domain {m r} (A O : Book m r) (a f : Fin m → ℕ) :=
  Finset.univ.filter fun X => ∃ i, Label (A i) (O i) X (a i) (f i)
noncomputable def violations {m r} (O : Book m r) (f : Fin m → ℕ) (X : Finset (Fin r)) :=
  Finset.univ.filter fun i => f i < (X\O i).card
noncomputable def sample {r} (X : Finset (Fin r)) := List.ofFn (fun j => decide (j∈X)) ++ [false,true]
def apart {m r} (A O : Book m r) (a f : Fin m → ℕ) := ∀ i j, i ≠ j → A i ⊆ O i → A j ⊆ O j →
  a i+f j < (A i\O j).card ∨ a j+f i < (A j\O i).card

def solution {m r} (A O : Book m r) (a f : Fin m → ℕ) (b : ℕ) := ∃ (C : Circuit) (out : Fin m → ℕ),
  (FanInTwo C ∧ ReadsBack (r+2) C ∧ C.output < r+2+C.size) ∧ (∀ j, out j < r+2+C.size) ∧
  NotBracket.notCount C ≤ b ∧ C.size-NotBracket.notCount C ≤ 64*(r+m+2)^3 ∧
  ∀ X i, Label (A i) (O i) X (a i) (f i) → ∀ j, (C.wires (sample X)).getD (out j) false = decide (i=j)

theorem separated {m r} {A O : Book m r} {a f b} (h : solution A O a f b) : apart A O a f := by
  obtain ⟨C,out,_,_,_,_,read⟩ := h
  intro i j ij hi hj
  by_contra! h
  obtain ⟨X,p,q⟩ := overlap hi hj h.1 h.2
  have bad := (read X i p i).symm.trans (read X j q i); simp [Ne.symm ij] at bad

theorem uniqueLabel {m r} {A O : Book m r} {a f} (sep : apart A O a f) (X) (i j)
    (hi : Label (A i) (O i) X (a i) (f i)) (hj : Label (A j) (O j) X (a j) (f j)) : i=j := by
  by_contra diff
  obtain ⟨il,ia,ig⟩ := label_iff.mp hi; obtain ⟨jl,ja,jg⟩ := label_iff.mp hj
  rcases sep i j diff il jl with h|h
  · have := triangle (A i) (O j) X; omega
  · have := triangle (A j) (O i) X; omega

theorem small_range {N : ℕ} (u : Finset ℕ) (h : ∀ i∈u,i<N) : u.card ≤ N := by
  have p := Finset.card_le_card (s:=u) (t:=Finset.range N) (fun i hi => Finset.mem_range.mpr (h i hi)); simpa using p

theorem vsmall {m r} (A O : Book m r) (a f) {X} (hx : X∈domain A O a f) : (violations O f X).card<m := by
  obtain ⟨i,hi⟩ := (Finset.mem_filter.mp hx).2
  have hs : violations O f X ⊂ Finset.univ := Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _,fun e => by
    have g : i∈violations O f X := e ▸ Finset.mem_univ _
    exact (not_lt_of_ge (label_iff.mp hi).2.2) (Finset.mem_filter.mp g).2⟩
  simpa using Finset.card_lt_card hs

theorem manyTests {X : Type} {n m d} {raw : X → List Bool} (width : ∀ x, (raw x).length=n) (v : X → Fin d → Bool)
    (S : Fin m → Finset (Fin d)) (k : Fin m → ℕ) (p : Net n) (one : p.has raw (fun _ => true))
    (zero : p.has raw (fun _ => false)) (get : ∀ j,p.has raw (fun x => v x j)) :
    ∃ q, Grow raw p q (m*(2*d*d)) 0 ∧ ∀ j,q.has raw (fun x => decide (k j≤tally (S j) v x)) := by
  obtain ⟨q,g,z⟩ := batch (raw:=raw) p (List.finRange m) _ (2*d*d) 0 (by
    intro j _ net keep; exact testSub width v (S j) (k j) net (keep _ one) (keep _ zero) (fun i => keep _ (get i)))
  exact ⟨q,by simpa using g,fun j => z j (List.mem_finRange j)⟩

theorem construct {m r} (A O : Book m r) (a f : Fin m → ℕ) (b : ℕ) (sep : apart A O a f) (room :
  min ((domain A O a f).image Finset.card).card ((domain A O a f).image (fun X => (violations O f X).card)).card ≤ 2^b) : solution A O a f b := by
  let dom := domain A O a f
  let X := { x // x∈dom }
  let input (x : X) := sample x.1
  let bit (x : X) (j : Fin r) := decide (j ∈ x.val)
  let V (x : X) (i : Fin m) := decide (i ∈ violations O f x.val)
  let U := dom.image Finset.card
  let W := dom.image (fun x => (violations O f x).card)
  let p := empty (r+2)
  have width (x) : (input x).length=r+2 := by simp [input,sample]
  have src (i) : p.has input (fun x => bit x i) := by
    refine ⟨i.val,by simp [p,empty]; omega,fun x => ?_⟩
    change (sample x.1).getD i.val false=bit x i
    simp [sample,bit,List.getD_eq_getElem?_getD,List.getElem?_append_left (show i.val<(List.ofFn (fun j : Fin r => decide (j∈x.1))).length by simpa using i.isLt)]
  have zero : p.has input (fun _ => false) := by
    refine ⟨r,by simp [p,empty],fun x => ?_⟩; change (sample x.1).getD r false=false; simp [sample,List.getD_eq_getElem?_getD]
  have one : p.has input (fun _ => true) := by
    refine ⟨r+1,by simp [p,empty],fun x => ?_⟩; change (sample x.1).getD (r+1) false=true; simp [sample,List.getD_eq_getElem?_getD,List.getElem?_append_right]
  have rawCount (S) (x : X) : tally S bit x = (S∩x.val).card := by
    apply congrArg Finset.card; ext j; simp [bit]
  have negCount (S) (x : X) : tally S (fun x j => !(bit x j)) x = (S\x.val).card := by
    apply congrArg Finset.card; ext j; simp [bit]
  have vc (x : X) : tally Finset.univ V x=(violations O f x.val).card := by
    apply congrArg Finset.card; ext j; simp [V]
  obtain ⟨q,gq,loss⟩ := manyTests width bit A (fun i => (A i).card-a i) p one zero src
  have lo (i) : q.has input (fun x => decide ((A i\x.val).card≤a i)) := by
    convert loss i using 2 with x; apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq,rawCount]; have := Finset.card_sdiff_add_card_inter (A i) x.val; omega
  let D := r+m+2
  have built : ∃ net, Grow input q net (16*D^3+b) b ∧ ∀ i, net.has input (fun x => !(V x i)) := by
    by_cases small : U.card≤2^b
    · have allU (z) (hz : z∈U) : z≤r := by obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hz; simpa using Finset.card_le_univ x
      have present (x : X) : tally Finset.univ bit x ∈ U := by rw [rawCount, Finset.univ_inter]; exact Finset.mem_image.mpr ⟨_,x.2,rfl⟩
      obtain ⟨v,gv,inv⟩ := weightNeg width bit U b allU present small q (gq.1 _ one) (gq.1 _ zero) (fun j => gq.1 _ (src j))
      obtain ⟨z,gz,gain⟩ := manyTests width (fun x j => !(bit x j)) (fun i => Finset.univ\O i) (fun i => (Finset.univ\O i).card-f i) v (gv.1 _ (gq.1 _ one)) (gv.1 _ (gq.1 _ zero)) inv
      have kb : 8*(r+1)^3+b + m*(2*r*r) ≤ 16*D^3+b := by dsimp [D]; ring_nf; omega
      refine ⟨z,by simpa using allowance (chain gv gz) kb,?_⟩
      intro i; convert gain i using 2 with x; apply Bool.eq_iff_iff.mpr
      simp only [V,violations,Finset.mem_filter,Finset.mem_univ,true_and,Bool.not_eq_true',decide_eq_false_iff_not,decide_eq_true_eq,negCount]
      have eq : (Finset.univ\O i)∩x.val=x.val\O i := by ext j; simp; tauto
      have card := Finset.card_sdiff_add_card_inter (Finset.univ\O i) x.val; rw [eq] at card; omega
    · have roomW : W.card ≤ 2^b := by change min U.card W.card ≤ _ at room; omega
      obtain ⟨v,gv,gain⟩ := manyTests width bit (fun i => Finset.univ\O i) (fun i => f i+1) q (gq.1 _ one) (gq.1 _ zero) (fun j => gq.1 _ (src j))
      have vio (i) : v.has input (fun x => V x i) := by
        convert gain i using 2 with x; apply Bool.eq_iff_iff.mpr
        simp only [V,violations,Finset.mem_filter,Finset.mem_univ,true_and,decide_eq_true_eq,rawCount]
        have e : (Finset.univ\O i)∩x.val=x.val\O i := by ext j; simp; tauto
        rw [e]; omega
      have allW (z) (hz : z∈W) : z≤m := by obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hz; simpa using Finset.card_le_univ (violations O f x)
      have present (x : X) : tally Finset.univ V x∈W := by rw [vc]; exact Finset.mem_image.mpr ⟨_,x.2,rfl⟩
      obtain ⟨z,gz,inv⟩ := weightNeg width V W b allW present roomW v (gv.1 _ (gq.1 _ one)) (gv.1 _ (gq.1 _ zero)) vio
      have kb : m*(2*r*r)+(8*(m+1)^3+b) ≤ 16*D^3+b := by dsimp [D]; ring_nf; omega
      exact ⟨z,by simpa using allowance (chain gv gz) kb,inv⟩
  obtain ⟨net,gn,gain⟩ := built
  obtain ⟨z,gz,outputs⟩ := batch (raw:=input) net (List.finRange m) (fun i x => decide (Label (A i) (O i) x.val (a i) (f i))) 1 0 (by
    intro i _ z keep
    by_cases active : A i ⊆ O i
    · obtain ⟨u,gu,ready⟩ := binary width z _ _ (keep _ (gn.1 _ (lo i))) (keep _ (gain i)) true
      refine ⟨u,gu,?_⟩; convert ready using 2 with x; apply Bool.eq_iff_iff.mpr
      simp [label_iff,active,V,violations]
    · refine ⟨z,allowance (start input z) (by decide : 0≤1),?_⟩
      convert keep _ (gn.1 _ (gq.1 _ zero)) using 2 with x; simp [label_iff,active])
  have total := chain (chain gq gn) gz
  have neg : z.cost=b := by simpa [p,empty,Net.cost,NotBracket.notCount] using total.2.2
  have sz := total.2.1; simp only [p,empty,List.length_nil,Nat.zero_add,List.length_finRange,Nat.mul_one] at sz
  have kb : m*(2*r*r) + 16*D^3 + m ≤ 64*D^3 := by dsimp [D]; ring_nf; omega
  let C : Circuit := ⟨z.gates,0⟩
  have tap (j) := outputs j (List.mem_finRange j)
  choose out bound eval using tap
  refine ⟨C,out,⟨z.fan,z.readsBack,by simp [C]⟩,bound,neg.le,?_,?_⟩
  · change z.gates.length - z.cost ≤ 64*D^3; omega
  · intro Y i lab j; let x : X := ⟨Y,Finset.mem_filter.mpr ⟨Finset.mem_univ _,i,lab⟩⟩
    change (PulseList.run z.gates (input x)).getD (out j) false = decide (i=j)
    rw [eval j x]; apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]
    exact ⟨fun h => uniqueLabel sep Y i j lab h,fun eq => eq ▸ lab⟩


end PEqualNP.Outside.L_lib_1426

theorem PEqualNP.Outside.L_lib_1426 : (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
let valid := fun (n : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) =>
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) D ∧ D.output < n+2+D.size
let bits := fun {n : Nat} (X : Finset (Fin n)) => List.ofFn (fun j : Fin n => decide (j ∈ X))
let near := fun {r : Nat} (a f : Nat) (C Y : Finset (Fin r)) => (C \ Y).card ≤ a ∧ (Y \ C).card ≤ f
∀ (r m : Nat) (Z O : Fin m → Finset (Fin r)) (a f : Fin m → Nat),
  let lo := fun i => Finset.univ \ Z i
  let live := fun i => lo i ⊆ O i
  let lab := fun (X : Finset (Fin r)) (i : Fin m) => ∃ C : Finset (Fin r),
    lo i ⊆ C ∧ C ⊆ O i ∧ near (a i) (f i) C X
  let dom := Finset.univ.filter (fun X : Finset (Fin r) => ∃ i, lab X i)
  let violations := fun X : Finset (Fin r) => Finset.univ.filter (fun i : Fin m => f i < (X \ O i).card)
  let t := min (dom.image (fun X => X.card)).card (dom.image (fun X => (violations X).card)).card
  let apart := ∀ i j, i ≠ j → live i → live j →
    a i+f j < (lo i \ O j).card ∨ a j+f i < (lo j \ O i).card
  t ≤ min (r+1) m ∧ ∀ b : Nat, t ≤ 2^b →
    (apart ↔ ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (out : Fin m → Nat), valid r D ∧
      (∀ j, out j < r+2+D.size) ∧ PEqualNP.NotBracket.notCount D ≤ b ∧
      D.size-PEqualNP.NotBracket.notCount D ≤ 64*(r+m+2)^3 ∧
      ∀ X i, lab X i → ∀ j, (D.wires (bits X ++ [false,true])).getD (out j) false = decide (i=j))) := by
  classical
  intro valid bits near r m Z O a f lo live lab dom violations t apart
  let A := fun i => (Finset.univ : Finset (Fin r)) \ Z i
  have core :
      let U := (PEqualNP.Outside.L_lib_1426.domain A O a f).image Finset.card
      let W := (PEqualNP.Outside.L_lib_1426.domain A O a f).image (fun x => (PEqualNP.Outside.L_lib_1426.violations O f x).card)
      min U.card W.card ≤ min (r+1) m ∧ ∀ b, min U.card W.card ≤ 2^b → (PEqualNP.Outside.L_lib_1426.apart A O a f ↔ PEqualNP.Outside.L_lib_1426.solution A O a f b) := by
    intro U W; refine ⟨le_min ?_ ?_,fun b hb => ⟨fun h => PEqualNP.Outside.L_lib_1426.construct A O a f b h hb,PEqualNP.Outside.L_lib_1426.separated⟩⟩
    · apply (min_le_left _ _).trans; apply PEqualNP.Outside.L_lib_1426.small_range
      intro z hz; obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hz; have h : x.card ≤ r := by simpa using Finset.card_le_univ x
      omega
    · apply (min_le_right _ _).trans; apply PEqualNP.Outside.L_lib_1426.small_range
      intro z hz; obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz; exact PEqualNP.Outside.L_lib_1426.vsmall A O a f hx
  dsimp only [t,apart,dom,violations,lab,live,lo,near,bits,valid,A] at *
  unfold PEqualNP.Outside.L_lib_1426.apart PEqualNP.Outside.L_lib_1426.domain PEqualNP.Outside.L_lib_1426.violations
    PEqualNP.Outside.L_lib_1426.solution PEqualNP.Outside.L_lib_1426.sample PEqualNP.Outside.L_lib_1426.Label at core
  convert! core using 100

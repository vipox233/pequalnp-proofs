import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_28604

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity


abbrev Wire := Bool × ℕ
def zero : Wire := (false,0)
def flip (a : Wire) : Wire := (!a.1,a.2)
def combine (d a b : ℕ) : ℕ :=
  match d with
  | 0 => a &&& b
  | 1 => a ||| b
  | 2 => a ^^^ (a &&& b)
  | _ => b ^^^ (a &&& b)
def opIndex (a b : Bool) : ℕ :=
  if a then (if b then 1 else 3) else (if b then 2 else 0)
def meet (a b : Wire) : Wire := (a.1 && b.1,combine (opIndex a.1 b.1) a.2 b.2)
def join (a b : Wire) : Wire := flip (meet (flip a) (flip b))
def read (j : ℕ) (a : Wire) : Bool := a.1 != a.2.testBit j
lemma read_zero (j : ℕ) : read j zero=false := by simp [read,zero]
lemma read_flip (j : ℕ) (a : Wire) : read j (flip a)=!(read j a) := by
  cases a with | mk s a => cases s <;> cases h : a.testBit j <;> simp [read,flip,h]
lemma read_meet (j : ℕ) (a b : Wire) : read j (meet a b) = (read j a && read j b) := by
  obtain ⟨s,a⟩ := a;obtain ⟨t,b⟩ := b
  cases s <;> cases t <;> cases h : a.testBit j <;> cases g : b.testBit j <;>
    simp [read,meet,combine,opIndex,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,h,g]
lemma read_join (j : ℕ) (a b : Wire) : read j (join a b) = (read j a || read j b) := by
  simp only [join,read_flip,read_meet];cases read j a <;> cases read j b <;> rfl

def gate (w : List Wire) (g : Gate) : Wire :=
  let arg := fun i => w.getD i zero
  match g.op,g.inputs with
  | .not, xs => flip (arg (xs.headD w.length))
  | .and, [] => flip zero
  | .or, [] => zero
  | .and, [i] | .or, [i] => arg i
  | .and, i::j::_ => meet (arg i) (arg j)
  | .or, i::j::_ => join (arg i) (arg j)
  | _,_ => zero
def execute (gs : List Gate) (w : List Wire) : List Wire :=
  gs.foldl (fun w g => w++[gate w g]) w
def boolRun (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w++[g.op.eval (g.inputs.map fun i => w.getD i false)]) w
lemma read_get (j : ℕ) (w : List Wire) (i : ℕ) :
    (w.map (read j)).getD i false = read j (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases h : w[i]? with
  | none => exact (read_zero j).symm
  | some a => rfl
lemma gate_read (w : List Wire) (g : Gate) (legal : g.op ∈ ({.and,.or,.not} : Set GateOp) ∧ g.inputs.length ≤ 2) (j : ℕ) :
    read j (gate w g) = g.op.eval (g.inputs.map fun i => (w.map (read j)).getD i false) := by
  simp_rw [read_get]
  obtain ⟨op,xs⟩ := g
  obtain ⟨ops,len⟩ := legal
  change op ∈ ({.and,.or,.not} : Set GateOp) at ops
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ops
  rcases ops with rfl|rfl|rfl <;>
    rcases xs with _|⟨i,_|⟨k,_|⟨h,rest⟩⟩⟩ <;>
    simp_all [gate,GateOp.eval,read_flip,read_meet,read_join,read_zero]
lemma execute_read (j : ℕ) (gs : List Gate) (w : List Wire) (legal : ∀ g ∈ gs,
    g.op ∈ ({.and,.or,.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (execute gs w).map (read j) = boolRun gs (w.map (read j)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gate w g])).map (read j) = boolRun gs (_++[_])
    rw [ih _ (fun v hv => legal v (.tail _ hv))]
    simp [gate_read w g (legal g List.mem_cons_self) j]

def counted (g : Gate) : Bool := match g.op with | .not => false | _ => true
def reps (w : List Wire) := w.map Prod.snd
def simple (w : List Wire) (z : ℕ) := z=0 ∨ z∈reps w
def priced (w : List Wire) (paid : Bool) (z : ℕ) := simple w z ∨
    (paid = true ∧ ∃ d < 4, ∃ a ∈ reps w, ∃ b ∈ reps w, a≠0 ∧ b≠0 ∧ a≠b ∧ z=combine d a b)
lemma get_simple (w : List Wire) (i : ℕ) : simple w (w.getD i zero).2 := by
  simp only [List.getD_eq_getElem?_getD]
  cases eq : w[i]? with
  | none => exact Or.inl rfl
  | some a => exact Or.inr (List.mem_map.mpr ⟨a,List.mem_of_getElem? eq,rfl⟩)
lemma combine_eq_cases (d a b : ℕ) (hd : d<4) (h : a=0 ∨ b=0 ∨ a=b) :
    combine d a b=0 ∨ combine d a b=a ∨ combine d a b=b := by
  rcases h with h|h|h <;> subst_vars <;> interval_cases d <;> simp [combine]
lemma made (w : List Wire) (d : ℕ) (a b : Wire) (hd : d<4) (pa : simple w a.2) (pb : simple w b.2) :
    priced w true (combine d a.2 b.2) := by
  by_cases h : a.2=0 ∨ b.2=0 ∨ a.2=b.2
  · rcases combine_eq_cases _ _ _ hd h with e|e|e
    · exact Or.inl (Or.inl e)
    · apply Or.inl; rw [e]; exact pa
    · apply Or.inl; rw [e]; exact pb
  · push Not at h
    exact Or.inr ⟨rfl,d,hd,a.2,pa.resolve_left h.1,b.2,pb.resolve_left h.2.1,h.1,h.2.1,h.2.2,rfl⟩
lemma op_lt (s t : Bool) : opIndex s t < 4 := by cases s <;> cases t <;> decide
lemma gate_priced (w : List Wire) (g : Gate) : priced w (counted g) (gate w g).2 := by
  obtain ⟨op,xs⟩ := g
  cases op with
  | and =>
    rcases xs with _|⟨i,_|⟨j,t⟩⟩
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (get_simple w i)
    · exact made w _ _ _ (op_lt _ _) (get_simple w i) (get_simple w j)
  | or =>
    rcases xs with _|⟨i,_|⟨j,t⟩⟩
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (get_simple w i)
    · exact made w _ _ _ (op_lt _ _) (get_simple w i) (get_simple w j)
  | mod _ | maj => exact Or.inl (Or.inl rfl)
  | _ => exact Or.inl (get_simple w _)






open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def Good (m a : ℕ) := ∀ i < m, a.testBit i ≠ a.testBit (m+i)
def Live (m : ℕ) : ℕ → Finset ℕ → Prop
  | 0,S => ∃ a, S={a} ∧ Good m a ∧ a≠0
  | k+1,S => ∃ U a b d, S=insert a (insert b U) ∧ d<4 ∧ a≠0 ∧ b≠0 ∧ a≠b ∧
      combine d a b ∉ insert a (insert b U) ∧ Live m k (insert (combine d a b) U)
lemma Live.done {m a} (hg : Good m a) (nz : a≠0) : Live m 0 {a} := ⟨a,rfl,hg,nz⟩
lemma Live.step {m k U a b d} (hd : d<4) (ha : a≠0) (hb : b≠0) (diff : a≠b)
    (fresh : combine d a b ∉ insert a (insert b U)) (next : Live m k (insert (combine d a b) U)) :
    Live m (k+1) (insert a (insert b U)) := ⟨U,a,b,d,rfl,hd,ha,hb,diff,fresh,next⟩
lemma liveNonzero {m k S} (h : Live m k S) : ∀ a∈S,a≠0 := by
  induction k generalizing S with
  | zero => obtain ⟨a,rfl,hg,hn⟩ := h; simpa using hn
  | succ k hyp =>
    obtain ⟨U,a,b,d,rfl,hd,ha,hb,ne,fresh,tail⟩ := h
    have ih := hyp tail
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl|hx
    · exact ha
    rcases Finset.mem_insert.mp hx with rfl|hx
    · exact hb
    exact ih x (Finset.mem_insert_of_mem hx)
lemma liveSize {m k S} (h : Live m k S) : S.card≤k+1 := by
  induction k generalizing S with
  | zero => obtain ⟨a,rfl,hg,hn⟩ := h; simp
  | succ k hyp =>
    obtain ⟨U,a,b,d,rfl,hd,ha,hb,ne,fresh,tail⟩ := h
    have ih := hyp tail
    have z : combine d a b ∉ U := fun m => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m))
    rw [Finset.card_insert_of_notMem z] at ih
    have u := Finset.card_insert_le a (insert b U)
    have v := Finset.card_insert_le b U
    omega
lemma combine_congr_bits (d a b i j : ℕ) (p : a.testBit i=a.testBit j) (q : b.testBit i=b.testBit j) :
    (combine d a b).testBit i=(combine d a b).testBit j := by
  rcases d with _|(_|(_|d)) <;> simp [combine,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,p,q]
lemma liveSeparates {m k S} (h : Live m k S) (i : ℕ) (hi : i < m) :
    ∃ a∈S,a.testBit i≠a.testBit (m+i) := by
  induction k generalizing S with
  | zero => obtain ⟨a,rfl,hg,hn⟩ := h; exact ⟨_,Finset.mem_singleton_self _,hg i hi⟩
  | succ k hyp =>
    obtain ⟨U,a,b,d,rfl,hd,ha,hb,ne,fresh,tail⟩ := h
    have ih := hyp tail
    obtain ⟨x,hx,dist⟩ := ih
    rcases Finset.mem_insert.mp hx with rfl|hx
    · by_cases v : a.testBit i=a.testBit (m+i)
      · exact ⟨b,Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),fun u => dist (combine_congr_bits _ _ _ _ _ v u)⟩
      · exact ⟨a,Finset.mem_insert_self _ _,v⟩
    · exact ⟨x,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx),dist⟩

lemma pull {m k S w z p} (h : Live m k S) (op : priced w p z)
    (sub : ∀ a∈S, a∈reps w ++ [z]) :
    ∃ l T, l ≤ k + p.toNat ∧ Live m l T ∧ ∀ a∈T, a∈reps w := by
  by_cases needed : z∈S
  · by_cases available : z∈reps w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      rcases (by simpa using sub a ha : a∈reps w ∨ a=z) with old|rfl
      · exact old
      · exact available
    · rcases op with easy|⟨rfl,d,hd,a,xa,b,xb,na,nb,ab,rfl⟩
      · rcases easy with e|e
        · exact ((liveNonzero h z needed) e).elim
        · exact (available e).elim
      · let g := combine d a b
        let U := S.erase g
        have tail : Live m k (insert g U) := by change Live m k (insert g (S.erase g)); rw [Finset.insert_erase (show g∈S from needed)]; exact h
        have old (x : ℕ) (hx : x∈U) : x∈reps w := by
          obtain ⟨ne,mem⟩ := Finset.mem_erase.mp hx
          have h' : x∈reps w ∨ x=g := by simpa using sub x mem
          exact h'.resolve_right ne
        have fresh : g ∉ insert a (insert b U) := by
          intro eq
          rcases Finset.mem_insert.mp eq with e|h'
          · exact available (show g∈reps w by rw [e];exact xa)
          rcases Finset.mem_insert.mp h' with e|u
          · exact available (show g∈reps w by rw [e];exact xb)
          · exact available (old _ u)
        refine ⟨k+1,insert a (insert b U),by simp,Live.step hd na nb ab fresh tail,?_⟩
        simpa using And.intro xa (And.intro xb old)
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have ne : a≠z := fun e => needed (e ▸ ha)
    simpa [ne] using sub a ha

lemma extract {m out} (hg : Good m out) (hn : out≠0) (gs : List Gate) (w : List Wire)
    (found : out∈reps (execute gs w)) :
    ∃ k S, k≤gs.countP counted ∧ Live m k S ∧ ∀ a∈S, a∈reps w := by
  induction gs generalizing w with
  | nil => exact ⟨0,{out},by simp,Live.done hg hn,by simpa [execute] using found⟩
  | cons g gs ih =>
    obtain ⟨k,S,lim,h,sub⟩ := ih (w++[gate w g]) found
    have sub' : ∀ a∈S,a∈reps w ++ [(gate w g).2] := by simpa [reps] using sub
    obtain ⟨l,T,cost,ht,raw⟩ := pull h (gate_priced w g) sub'
    refine ⟨l,T,?_,ht,raw⟩
    cases e : counted g <;> simp [e,Bool.toNat] at cost ⊢ <;> omega

def separation (m a : ℕ) := a ^^^ (a >>> m)
def cover (m : ℕ) : List ℕ → ℕ
  | [] => 0
  | a::t => separation m a ||| cover m t
def full (m : ℕ) := (1 <<< m)-1
def enough (m c : ℕ) := (c &&& full m) == full m
lemma coverBit (m i : ℕ) (v : List ℕ) : (cover m v).testBit i=true ↔
    ∃ a∈v,a.testBit i≠a.testBit (m+i) := by
  induction v with
  | nil => simp [cover]
  | cons a t ih =>
    simp only [cover,Nat.testBit_or,Bool.or_eq_true,ih,List.mem_cons,separation,Nat.testBit_xor,Nat.testBit_shiftRight]
    cases v1 : a.testBit i <;> cases v2 : a.testBit (m+i) <;> simp [v1,v2]
lemma enoughLive {m k S} (h : Live m k S) (v : List ℕ) (rep : v.toFinset=S) : enough m (cover m v)=true := by
  apply beq_iff_eq.mpr
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  have bit : (full m).testBit i=decide (i < m) := by simp [full,Nat.shiftLeft_eq,Nat.testBit_two_pow_sub_one]
  by_cases hi : i < m
  · have ⟨x,hx,good⟩ := liveSeparates h i hi
    have xc : x∈v := List.mem_toFinset.mp (rep ▸ hx)
    have mark := (coverBit m i v).2 ⟨x,xc,good⟩
    simp [mark,bit,hi]
  · simp [bit,hi]






def save (keep : Bool) (a : ℕ) (rest : List ℕ) := if keep then a::rest else rest
def without (v : List ℕ) (a b : ℕ) := v.filter (fun x => x != a && x != b)
def optionStep (m fuel : ℕ) (go : List ℕ → Bool) (rest : List ℕ) (n cv a b z : ℕ) (ka kb : Bool) : Bool :=
  let len := 1+n+ka.toNat+kb.toNat
  len ≤ fuel+1 && enough m (((separation m z ||| cv) ||| (if ka then separation m a else 0)) |||
    (if kb then separation m b else 0)) && go (z::save ka a (save kb b rest))
def gateStep (m fuel : ℕ) (go : List ℕ → Bool) (v rest : List ℕ) (n cv a b z : ℕ) : Bool :=
  z != 0 && !(v.contains z) &&
  (optionStep m fuel go rest n cv a b z false false || optionStep m fuel go rest n cv a b z true false ||
   optionStep m fuel go rest n cv a b z false true || optionStep m fuel go rest n cv a b z true true)
def pairStep (m fuel : ℕ) (go : List ℕ → Bool) (v : List ℕ) (a b : ℕ) : Bool :=
  if a<b then
    let rest := without v a b
    let check := gateStep m fuel go v rest rest.length (cover m rest) a b
    check (a &&& b) || check (a ||| b) || check (a ^^^ (a &&& b)) || check (b ^^^ (a &&& b))
  else false
def anyGate (m fuel : ℕ) (go : List ℕ → Bool) (v : List ℕ) : Bool :=
  v.any (fun a => v.any (fun b => pairStep m fuel go v a b))
def terminal (m : ℕ) (v : List ℕ) := v.any (fun a => enough m (separation m a))
def search (m : ℕ) : ℕ → List ℕ → Bool
  | 0, v => terminal m v
  | fuel+1, v => terminal m v || anyGate m fuel (search m fuel) v

lemma surface (m a i : ℕ) : (separation m a).testBit i=true ↔ a.testBit i≠a.testBit (m+i) := by
  simp only [separation,Nat.testBit_xor,Nat.testBit_shiftRight]
  cases a.testBit i <;> cases a.testBit (m+i) <;> decide
lemma ends {m a} (h : Good m a) (v : List ℕ) (mem : a∈v) : terminal m v=true := by
  apply List.any_eq_true.mpr;refine ⟨a,mem,?_⟩
  apply beq_iff_eq.mpr;apply Nat.eq_of_testBit_eq;intro i;rw [Nat.testBit_and]
  have e : (full m).testBit i=decide (i < m) := by simp [full,Nat.shiftLeft_eq,Nat.testBit_two_pow_sub_one]
  by_cases l : i < m
  · simp [e,l,(surface _ _ _).2 (h i l)]
  · simp [e,l]
lemma option_ok {m fuel go rest a b z ka kb} (lim : (z::save ka a (save kb b rest)).length≤fuel+1)
    (cov : enough m (cover m (z::save ka a (save kb b rest)))=true)
    (next : go (z::save ka a (save kb b rest))=true) :
    optionStep m fuel go rest rest.length (cover m rest) a b z ka kb=true := by
  have size : 1+rest.length+ka.toNat+kb.toNat≤fuel+1 := by
    cases ka <;> cases kb <;> simp [save,Bool.toNat] at lim ⊢ <;> omega
  have eq : enough m (((separation m z ||| cover m rest) ||| (if ka then separation m a else 0)) ||| (if kb then separation m b else 0))=true := by
    cases ka <;> cases kb <;> simpa [save,cover,Nat.or_assoc,Nat.or_left_comm,Nat.or_comm] using cov
  simp [optionStep,size,eq,next]
lemma gate_ok {m fuel go v rest n cv a b z ka kb} (nz : z≠0) (fresh : z∉v)
    (which : optionStep m fuel go rest n cv a b z ka kb=true) :
    gateStep m fuel go v rest n cv a b z=true := by
  cases ka <;> cases kb <;> simp [gateStep,nz,fresh,which]
lemma pair_ok {m fuel go v a b d} (ordered : a<b) (hd : d<4)
    (step : let rest := without v a b;gateStep m fuel go v rest rest.length (cover m rest) a b (combine d a b)=true) :
    pairStep m fuel go v a b=true := by
  interval_cases d <;> simp only [combine] at step <;> simp [pairStep,ordered,step]
lemma swapOp (d a b : ℕ) (hd : d<4) : ∃ e<4,combine d a b=combine e b a := by
  interval_cases d
  · exact ⟨0,by decide,Nat.and_comm a b⟩
  · exact ⟨1,by decide,Nat.or_comm a b⟩
  · exact ⟨3,by decide,by simp [combine,Nat.and_comm]⟩
  · exact ⟨2,by decide,by simp [combine,Nat.and_comm]⟩
lemma listNext {v : List ℕ} {a b z : ℕ} {U : Finset ℕ} (rep : v.toFinset=insert a (insert b U))
    (ab : a≠b) (fz : z∉insert a (insert b U)) (nd : v.Nodup) :
    let rest := without v a b
    let next := z::save (decide (a∈U)) a (save (decide (b∈U)) b rest)
    next.toFinset=insert z U ∧ next.Nodup := by
  dsimp only
  have mem (x : ℕ) : x∈without v a b ↔ x∈U ∧ x≠a ∧ x≠b := by
    simp only [without,List.mem_filter,Bool.and_eq_true,bne_iff_ne]
    have e : x∈v ↔ x=a ∨ x=b ∨ x∈U := by rw [← List.mem_toFinset,rep];simp
    tauto
  have nr := nd.filter (fun x => x != a && x != b)
  change (without v a b).Nodup at nr
  have md (x : ℕ) : (x∈save (decide (a∈U)) a (save (decide (b∈U)) b (without v a b))) ↔ x∈U := by
    by_cases xa : x=a
    · subst x; by_cases ka : a∈U <;> by_cases kb : b∈U <;> simp [save,ka,kb,mem,ab]
    by_cases xb : x=b
    · subst x; by_cases ka : a∈U <;> by_cases kb : b∈U <;> simp [save,ka,kb,mem,Ne.symm ab]
    by_cases ka : a∈U <;> by_cases kb : b∈U <;> simp [save,ka,kb,mem,xa,xb]
  constructor
  · ext x;simp [md]
  · simp only [List.nodup_cons,md]
    refine ⟨fun m => fz (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m)),?_⟩
    have an : a∉without v a b := fun x => (mem _).1 x |>.2.1 rfl
    have bn : b∉without v a b := fun x => (mem _).1 x |>.2.2 rfl
    by_cases ka : a∈U <;> by_cases kb : b∈U <;> simp [save,ka,kb,nr,ab,an,bn]
lemma orderedStep {m fuel n U a b d v} {go : List ℕ→Bool} (hd : d<4)
    (lt : a<b) (nz : combine d a b≠0) (fresh : combine d a b∉insert a (insert b U))
    (rep : List.toFinset v=insert a (insert b U)) (nd : v.Nodup) (lim : n≤fuel)
    (tail : Live m n (insert (combine d a b) U))
    (nextOK : ∀ v : List ℕ, v.toFinset=insert (combine d a b) U → v.Nodup → go v=true) :
    pairStep m fuel go v a b=true := by
  let z := combine d a b
  let rest := without v a b
  let next := z::save (decide (a∈U)) a (save (decide (b∈U)) b rest)
  obtain ⟨r,nu⟩ := listNext (z:=z) rep (Nat.ne_of_lt lt) fresh nd
  have small := liveSize tail
  change (insert z U).card≤n+1 at small
  have length : next.length=(insert z U).card := by rw [←r,List.toFinset_card_of_nodup nu]
  have bound : next.length≤fuel+1 := by omega
  have coverOK := enoughLive tail next r
  have ok := option_ok bound coverOK (nextOK next r nu)
  apply pair_ok lt hd
  exact gate_ok nz (fun h => fresh (rep ▸ List.mem_toFinset.mpr h)) ok
lemma transition {m fuel n U a b d v} {go : List ℕ→Bool} (hd : d<4)
    (ab : a≠b) (fresh : combine d a b∉insert a (insert b U))
    (rep : List.toFinset v=insert a (insert b U)) (nd : v.Nodup) (lim : n≤fuel)
    (tail : Live m n (insert (combine d a b) U))
    (nextOK : ∀ v : List ℕ, v.toFinset=insert (combine d a b) U → v.Nodup → go v=true) :
    anyGate m fuel go v=true := by
  have ma : a∈v := List.mem_toFinset.mp (rep ▸ Finset.mem_insert_self _ _)
  have mb : b∈v := List.mem_toFinset.mp (rep ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have nz := liveNonzero tail _ (Finset.mem_insert_self _ _)
  rcases lt_or_gt_of_ne ab with lt|gt
  · exact List.any_eq_true.mpr ⟨a,ma,List.any_eq_true.mpr ⟨b,mb,orderedStep hd lt nz fresh rep nd lim tail nextOK⟩⟩
  · obtain ⟨e,he,eq⟩ := swapOp d a b hd
    have rev : insert a (insert b U)=insert b (insert a U) := Finset.insert_comm a b U
    rw [rev] at fresh rep
    rw [eq] at fresh nz tail nextOK
    exact List.any_eq_true.mpr ⟨b,mb,List.any_eq_true.mpr ⟨a,ma,orderedStep he gt nz fresh rep nd lim tail nextOK⟩⟩

theorem complete (m fuel : ℕ) {n S} (h : Live m n S) (lim : n≤fuel)
    (v : List ℕ) (rep : v.toFinset=S) (nd : v.Nodup) : search m fuel v=true := by
  induction fuel generalizing n S v with
  | zero =>
    cases n with
    | zero => obtain ⟨a,rfl,hg,hn⟩ := h; exact ends hg v (List.mem_toFinset.mp (rep ▸ Finset.mem_singleton_self _))
    | succ n => omega
  | succ k ih =>
    rw [search,Bool.or_eq_true]
    cases n with
    | zero => obtain ⟨a,rfl,hg,hn⟩ := h; exact Or.inl (ends hg v (List.mem_toFinset.mp (rep ▸ Finset.mem_singleton_self _)))
    | succ n =>
      obtain ⟨U,a,b,d,rfl,hd,_,_,ab,fresh,tail⟩ := h
      exact Or.inr (transition hd ab fresh rep nd (by omega) tail (fun v hv nv => ih tail (by omega) v hv nv))




def Projection (m h : ℕ) := { f : ℕ → ℕ // (∀ d a b, d<4 → f (combine d a b)=combine d (f a) (f b)) ∧
  (∀ a, Good m a → Good h (f a)) ∧ 0<h }
abbrev Projection.toFun {m h} (p : Projection m h) := p.val
lemma Projection.combineEq {m h} (p : Projection m h) : ∀ d a b, d<4 → p.toFun (combine d a b)=combine d (p.toFun a) (p.toFun b) := p.property.1
lemma Projection.good {m h} (p : Projection m h) : ∀ a, Good m a → Good h (p.toFun a) := p.property.2.1
lemma Projection.someRow {m h} (p : Projection m h) : 0<h := p.property.2.2
def Possible (m k : ℕ) (av : List ℕ) :=
  ∃ j S, j≤k ∧ Live m j S ∧ ∀ x∈S,x∈av
def charge (av : List ℕ) (z : ℕ) := z != 0 && !(av.contains z)
lemma pullPaid {m k d a b : ℕ} {av : List ℕ} (hd : d<4) (ha : a∈av) (hb : b∈av)
    (later : Possible m k (av++[combine d a b])) :
    Possible m (k+(charge av (combine d a b)).toNat) av := by
  let w := av.map (fun x => (false,x))
  have repr : reps w=av := by simp [w,reps,List.map_map,Function.comp_def]
  obtain ⟨j,S,lim,live,sub⟩ := later
  have needed : ∀ x∈S,x∈reps w++[combine d a b] := by simpa [repr] using sub
  have price : priced w (charge av (combine d a b)) (combine d a b) := by
    by_cases nz : combine d a b=0
    · exact Or.inl (Or.inl nz)
    by_cases old : combine d a b∈av
    · exact Or.inl (Or.inr (repr ▸ old))
    have paid : charge av (combine d a b)=true := by simp [charge,nz,old]
    have special : ¬(a=0 ∨ b=0 ∨ a=b) := by
      intro h
      rcases combine_eq_cases _ _ _ hd h with zero|rfl'|rfl'
      · exact nz zero
      · exact old (by rw [rfl'];exact ha)
      · exact old (by rw [rfl'];exact hb)
    exact Or.inr ⟨paid,d,hd,a,repr ▸ ha,b,repr ▸ hb,
      fun x => special (Or.inl x),fun x => special (Or.inr (Or.inl x)),fun x => special (Or.inr (Or.inr x)),rfl⟩
  obtain ⟨l,T,le,ok,sub'⟩ := pull live price needed
  exact ⟨l,T,by omega,ok,by simpa [repr] using sub'⟩

def dead (p : ℕ→ℕ) (S : Finset ℕ) := (S.filter (fun x => p x=0)).card
lemma deadStay {p : ℕ→ℕ} {a : ℕ} {S : Finset ℕ} (h : p a≠0) : dead p (insert a S)=dead p S := by
  simp [dead,Finset.filter_insert,h]
lemma deadLimit (p : ℕ→ℕ) (a : ℕ) (S : Finset ℕ) : dead p (insert a S)≤dead p S+1 := by
  by_cases x : p a=0
  · simpa [dead,Finset.filter_insert,x] using Finset.card_insert_le a (S.filter (fun x => p x=0))
  · simp [deadStay x]
lemma deadMono (p : ℕ→ℕ) (a : ℕ) (S : Finset ℕ) : dead p S ≤ dead p (insert a S) := by
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert _ _))
lemma deadGrow {p : ℕ→ℕ} {a : ℕ} {S : Finset ℕ} (z : p a=0) (fresh : a∉S) :
    dead p (insert a S)=dead p S+1 := by
  have nf : a∉S.filter (fun x => p x=0) := fun h => fresh (Finset.mem_filter.mp h).1
  simp [dead,Finset.filter_insert,z,Finset.card_insert_of_notMem nf]
lemma countCharge {m h d a b : ℕ} (p : Projection m h) (hd : d<4) (U : Finset ℕ)
    (fz : combine d a b∉insert a (insert b U)) (av : List ℕ) (ma : p.toFun a∈av) (mb : p.toFun b∈av) :
    (charge av (p.toFun (combine d a b))).toNat + dead p.toFun (insert a (insert b U)) ≤
      1+dead p.toFun (insert (combine d a b) U) := by
  have up := deadMono p.toFun (combine d a b) U
  have la := deadLimit p.toFun a (insert b U)
  have lb := deadLimit p.toFun b U
  have free (bad : p.toFun a=0 ∨ p.toFun b=0) : charge av (p.toFun (combine d a b))=false := by
    rw [p.combineEq _ _ _ hd]
    rcases combine_eq_cases _ _ _ hd (bad.imp_right Or.inl) with e|e|e <;> simp [charge,e,ma,mb]
  by_cases az : p.toFun a=0
  · rw [free (Or.inl az)];simp only [Bool.toNat_false,Nat.zero_add]
    by_cases bz : p.toFun b=0
    · have zz : p.toFun (combine d a b)=0 := by
        rw [p.combineEq _ _ _ hd,az,bz];interval_cases d <;> decide
      have fresh : combine d a b∉U := fun m => fz (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m))
      rw [deadGrow zz fresh];omega
    · rw [deadStay bz] at la;omega
  · rw [deadStay az]
    by_cases bz : p.toFun b=0
    · rw [free (Or.inr bz)];simp only [Bool.toNat_false,Nat.zero_add];omega
    · rw [deadStay bz];cases charge av (p.toFun (combine d a b)) <;> simp [Bool.toNat] <;> omega

theorem projectLive {m h k S} (p : Projection m h) (live : Live m k S) :
    ∃ j T,j+dead p.toFun S≤k ∧ Live h j T ∧ ∀ x∈T,x∈S.image p.toFun := by
  induction k generalizing S with
  | zero =>
    obtain ⟨a,rfl,hg,hn⟩ := live
    have gp := p.good a hg
    have nz : p.toFun a≠0 := by intro e;have x := gp 0 p.someRow;simp [e] at x
    exact ⟨0,{p.toFun a},by simp [dead,nz],Live.done gp nz,by simp⟩
  | succ k hyp =>
    obtain ⟨U,a,b,d,rfl,hd,ha,hb,ab,fz,tail⟩ := live
    have ih := hyp tail
    obtain ⟨j,T,cost,ok,raw⟩ := ih
    let av := ((insert a (insert b U)).image p.toFun).toList
    have ma : p.toFun a∈av := by simp [av]
    have mb : p.toFun b∈av := by simp [av]
    have later : Possible h j (av++[combine d (p.toFun a) (p.toFun b)]) := by
      refine ⟨j,T,le_rfl,ok,?_⟩
      intro z hz
      have has := raw _ hz
      simp only [Finset.image_insert,Finset.mem_insert] at has
      rcases has with rfl|old
      · simp [p.combineEq d a b hd]
      · have inav : z∈av := by simpa [av] using (Or.inr (Or.inr old) : z=p.toFun a ∨ z=p.toFun b ∨ z∈U.image p.toFun)
        simp [inav]
    obtain ⟨l,V,lim,good,sub⟩ := pullPaid hd ma mb later
    rw [←p.combineEq d a b hd] at lim
    have bound := countCharge p hd U fz av ma mb
    exact ⟨l,V,by omega,good,by simpa [av] using sub⟩





lemma full_bit (m i : ℕ) : (full m).testBit i=decide (i < m) := by
  simp [full,Nat.shiftLeft_eq,Nat.testBit_two_pow_sub_one]

def half (m q r a : ℕ) := (a &&& q &&& full m) |||
    (if a.testBit r then ((full m ^^^ q) &&& full m) else 0)
def slice (m q r a : ℕ) := half m q r a ||| ((half m q r (a >>> m)) <<< m)
lemma half_bit (m q r a i : ℕ) : (half m q r a).testBit i =
    (decide (i < m) && (if q.testBit i then a.testBit i else a.testBit r)) := by
  cases e : a.testBit r <;> cases f : q.testBit i <;> by_cases l : i < m <;>
    simp [half,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,full_bit,e,f,l]
lemma slice_lo {m i : ℕ} (q r a : ℕ) (hi : i < m) : (slice m q r a).testBit i =
    a.testBit (if q.testBit i then i else r) := by
  cases e : q.testBit i <;> simp [slice,Nat.testBit_or,Nat.testBit_shiftLeft,half_bit,hi,e,(show ¬ (m ≤ i) from by omega)]
lemma slice_hi {m i : ℕ} (q r a : ℕ) (hi : i < m) : (slice m q r a).testBit (m+i) =
    a.testBit (m+(if q.testBit i then i else r)) := by
  have n : ¬ (m + i < m) := by omega
  cases e : q.testBit i <;> simp [slice,Nat.testBit_or,Nat.testBit_shiftLeft,Nat.testBit_shiftRight,half_bit,hi,e,n]
lemma slice_above {m i : ℕ} (q r a : ℕ) (hi : 2 * m ≤ i) : (slice m q r a).testBit i=false := by
  simp [slice,Nat.testBit_or,Nat.testBit_shiftLeft,half_bit,(show ¬ (i < m) from by omega),(show ¬ (i - m < m) from by omega)]
lemma slice_hom (m q r d a b : ℕ) (hd : d<4) : slice m q r (combine d a b)=combine d (slice m q r a) (slice m q r b) := by
  apply Nat.eq_of_testBit_eq;intro i
  by_cases lo : i < m
  · rw [slice_lo _ _ _ lo]
    interval_cases d <;> simp [combine,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,slice_lo _ _ _ lo]
  by_cases upper : i<2*m
  · let j := i-m
    have h : j < m := by dsimp [j];omega
    have e : i=m+j := by dsimp [j];omega
    rw [e,slice_hi _ _ _ h]
    interval_cases d <;> simp [combine,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,slice_hi _ _ _ h]
  · have large := slice_above (m:=m) (i:=i) (hi := (show 2 * m ≤ i from by omega))
    interval_cases d <;> simp [combine,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,large]
def projection (m q r : ℕ) (hr : r < m) : Projection m m := ⟨slice m q r, slice_hom m q r, by
    intro a ga i hi
    rw [slice_lo _ _ _ hi,slice_hi _ _ _ hi]
    cases q.testBit i
    · exact ga r hr
    · exact ga i hi
  , by omega⟩

lemma enoughSup {m k S} (h : Live m k S) (v : List ℕ) (sub : ∀ x∈S,x∈v) : enough m (cover m v)=true := by
  apply beq_iff_eq.mpr;apply Nat.eq_of_testBit_eq;intro i
  rw [Nat.testBit_and,full_bit]
  by_cases hi : i < m
  · obtain ⟨x,hx,g⟩ := liveSeparates h i hi
    have bit := (coverBit m i v).2 ⟨x,sub _ hx,g⟩
    simp [bit,hi]
  · simp [hi]
def start (m fuel : ℕ) (av : List ℕ) :=
  let v := av.eraseDups.filter (fun x => x != 0)
  let needed := fun a => !(enough m (cover m (v.filter (fun x => x != a))))
  let must := v.filter needed
  let extra := v.filter (fun x => !needed x)
  extra.sublists.any (fun t =>
    let s := (must++t).dedup
    s.length≤fuel+1 && enough m (cover m s) && search m fuel s)

theorem start_complete {m k S} (h : Live m k S) (av : List ℕ) (sub : ∀ x∈S,x∈av)
    (fuel : ℕ) (lim : k≤fuel) : start m fuel av=true := by
  let v := av.eraseDups.filter (fun x => x != 0)
  let needed := fun a => !(enough m (cover m (v.filter (fun x => x != a))))
  let must := v.filter needed
  let extra := v.filter (fun x => !needed x)
  let t := extra.filter (fun x => decide (x∈S))
  let s := (must++t).dedup
  have inV (x : ℕ) (hx : x∈S) : x∈v := by simp [v,sub x hx,liveNonzero h x hx]
  have fixed (a : ℕ) (ha : a∈must) : a∈S := by
    by_contra absent
    have no := (List.mem_filter.mp ha).2
    have all (x : ℕ) (hx : x∈S) : x∈v.filter (fun y => y != a) := by
      have ne : x≠a := by rintro rfl;exact absent hx
      simp [inV x hx,ne]
    have yes := enoughSup h _ all
    simp [needed,yes] at no
  have eq : s.toFinset=S := by
    ext x
    constructor
    · intro mem
      have e : x∈must ∨ x∈t := by simpa [s] using mem
      rcases e with l|r
      · exact fixed x l
      · simpa using (List.mem_filter.mp r).2
    · intro mem
      have raw := inV x mem
      cases H : needed x <;> simp [s,must,t,extra,H,raw,mem]
  have nd : s.Nodup := List.nodup_dedup _
  have size : s.length≤fuel+1 := by
    have vsize := liveSize h
    rw [←eq,List.toFinset_card_of_nodup nd] at vsize;omega
  have test := complete m fuel h lim s eq nd
  have cov := enoughLive h s eq
  apply List.any_eq_true.mpr
  refine ⟨t,List.mem_sublists.mpr (List.filter_sublist),?_⟩
  change (decide (s.length≤fuel+1) && enough m (cover m s) && search m fuel s)=true
  simp [size,cov,test]

def oneOutput (m fuel : ℕ) (rest : List ℕ) (n cv a b z : ℕ) (ka kb : Bool) : List (List ℕ) :=
  if optionStep m fuel (fun _ => true) rest n cv a b z ka kb then [z::save ka a (save kb b rest)] else []
def oneGate (m fuel : ℕ) (v rest : List ℕ) (n cv a b z : ℕ) :=
  if z != 0 && !(v.contains z) then
    oneOutput m fuel rest n cv a b z false false ++ oneOutput m fuel rest n cv a b z true false ++
    oneOutput m fuel rest n cv a b z false true ++ oneOutput m fuel rest n cv a b z true true
  else []
def onePair (m fuel : ℕ) (v : List ℕ) (a b : ℕ) :=
  if a<b then
    let rest := without v a b
    let gate := oneGate m fuel v rest rest.length (cover m rest) a b
    gate (a &&& b) ++ gate (a ||| b) ++ gate (a ^^^ (a &&& b)) ++ gate (b ^^^ (a &&& b))
  else []
def successors (m fuel : ℕ) (v : List ℕ) :=
  v.flatMap (fun a => v.flatMap (fun b => onePair m fuel v a b))
lemma output_any (m fuel : ℕ) (go : List ℕ→Bool) (rest : List ℕ) (n cv a b z : ℕ) (ka kb : Bool) :
    (oneOutput m fuel rest n cv a b z ka kb).any go=optionStep m fuel go rest n cv a b z ka kb := by
  have E (t : Bool) (x : List ℕ) : ((if t then [x] else []) : List (List ℕ)).any go = (t && go x) := by cases t <;> simp
  unfold oneOutput
  rw [E]
  simp only [optionStep,Bool.and_true]
lemma gate_any (m fuel : ℕ) (go : List ℕ→Bool) (v rest : List ℕ) (n cv a b z : ℕ) :
    (oneGate m fuel v rest n cv a b z).any go=gateStep m fuel go v rest n cv a b z := by
  have E (t : Bool) (xs : List (List ℕ)) : (if t then xs else []).any go = (t && xs.any go) := by cases t <;> simp
  unfold oneGate gateStep
  rw [E]
  simp only [List.any_append,output_any,Bool.or_assoc,Bool.and_assoc]
lemma pair_any (m fuel : ℕ) (go : List ℕ→Bool) (v : List ℕ) (a b : ℕ) :
    (onePair m fuel v a b).any go=pairStep m fuel go v a b := by
  by_cases h : a<b <;> simp [onePair,pairStep,h,gate_any,Bool.or_assoc]
lemma successors_any (m fuel : ℕ) (go : List ℕ→Bool) (v : List ℕ) :
    (successors m fuel v).any go=anyGate m fuel go v := by simp [successors,anyGate,pair_any]
def feasible (m fuel : ℕ) (v : List ℕ) := ∃ k≤fuel,Live m k v.toFinset ∧ v.Nodup
theorem move {m fuel : ℕ} {v : List ℕ} (h : feasible m (fuel+1) v) :
    terminal m v=true ∨ ∃ w∈successors m fuel v,feasible m fuel w := by
  classical
  obtain ⟨k,lim,live,nd⟩ := h
  generalize e : v.toFinset=S at live
  cases k with
  | zero => obtain ⟨a,rfl,hg,hn⟩ := live; exact Or.inl (ends hg v (List.mem_toFinset.mp (e ▸ Finset.mem_singleton_self _)))
  | succ k =>
    obtain ⟨U,a,b,d,rfl,hd,ha,hb,ab,fz,tail⟩ := live
    let step := fun w => decide (feasible m fuel w)
    have hit := transition (go:=step) hd ab fz e nd (by omega : _≤fuel) tail (fun w rep nu => by
      apply decide_eq_true;exact ⟨_,by omega,rep ▸ tail,nu⟩)
    rw [←successors_any] at hit
    obtain ⟨w,hw,works⟩ := List.any_eq_true.mp hit
    exact Or.inr ⟨w,hw,of_decide_eq_true works⟩
def Excluded (m k : ℕ) (v : List ℕ) := ¬feasible m k v
def Block (m k : ℕ) (vs : List (List ℕ)) (i n : ℕ) := ∀ v∈(vs.drop i).take n,Excluded m k v
lemma blocks_cover {m k width q : ℕ} {vs : List (List ℕ)} (pw : 0<width) (size : vs.length≤q*width)
    (all : ∀ j : Fin q,Block m k vs (j.val*width) width) : ∀ v∈vs,Excluded m k v := by
  intro v hv
  obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hv
  have split := Nat.div_add_mod' i width
  have within := Nat.mod_lt i pw
  have bound : i/width<q := (Nat.div_lt_iff_lt_mul pw).2 (by omega)
  apply all ⟨i/width,bound⟩ _
  apply List.mem_iff_getElem.mpr
  have ix : i % width<((vs.drop (i/width*width)).take width).length := by simp only [List.length_take,List.length_drop];omega
  refine ⟨i % width,ix,?_⟩
  simp only [List.getElem_take,List.getElem_drop]
  simp [split]
lemma join_exclusions {m k : ℕ} {v : List ℕ} (term : terminal m v=false)
    (no : ∀ w∈successors m k v,Excluded m k w) : Excluded m (k+1) v := by
  intro h
  rcases move h with e|⟨w,hw,hf⟩
  · exact Bool.noConfusion (term.symm.trans e)
  · exact no w hw hf

abbrev FloorData := ℕ × ℕ × List ℕ
abbrev FloorData.pairMask (s : FloorData) := s.1
abbrev FloorData.lower (s : FloorData) := s.2.1
abbrev FloorData.basis (s : FloorData) := s.2.2
def Floor (m : ℕ) (s : FloorData) := ∀ k,Possible m k (0::s.basis) → s.lower≤k
theorem floorChecked {m : ℕ} {s : FloorData} (checked : start m (s.lower-1) (0::s.basis)=false) : Floor m s := by
  intro k poss
  by_contra small
  obtain ⟨j,S,le,live,sub⟩ := poss
  exact Bool.noConfusion (checked.symm.trans (start_complete live _ sub _ (by omega)))
lemma getMember {av : List ℕ} (zeroMem : 0∈av) (i : ℕ) : av.getD i 0∈av := by
  simp only [List.getD_eq_getElem?_getD]
  cases e : av[i]? with
  | none => exact zeroMem
  | some t => exact List.mem_of_getElem? e

def instruction (av : List ℕ) (part : ℕ) :=
  let n := (part &&& 4095)-1
  combine (n % 4) (av.getD ((n >>> 2) &&& 15) 0) (av.getD ((n >>> 6) &&& 15) 0)
def replay : ℕ → ℕ → List ℕ → List ℕ
  | 0,_,av => av
  | k+1,code,av => if code=0 then av else replay k (code >>> 12) (av++[instruction av code])
def paidCount : ℕ → ℕ → ℕ
  | 0,_ => 0
  | k+1,code => if code=0 then 0 else paidCount k (code >>> 12)+1

theorem replay_back {m k : ℕ} (count code : ℕ) (av : List ℕ) (hasZero : 0∈av)
    (later : Possible m k (replay count code av)) : Possible m (k+paidCount count code) av := by
  induction count generalizing code av with
  | zero => simpa [replay,paidCount] using later
  | succ n ih =>
    by_cases stop : code=0
    · simpa [replay,paidCount,stop] using later
    rw [replay,ite_eq_right stop] at later
    have post := ih _ (av++[instruction av code]) (by simp [hasZero]) later
    let p := (code &&& 4095)-1
    have full := pullPaid (d:=p % 4) (Nat.mod_lt _ (by decide)) (getMember hasZero ((p >>> 2) &&& 15)) (getMember hasZero ((p >>> 6) &&& 15)) post
    obtain ⟨j,S,lim,live,sub⟩ := full
    refine ⟨j,S,?_,live,sub⟩
    rw [paidCount,ite_eq_right stop]
    have one (b : Bool) : b.toNat≤1 := by cases b <;> decide
    have bound := one (charge av (combine (p % 4) (av.getD ((p >>> 2) &&& 15) 0) (av.getD ((p >>> 6) &&& 15) 0)))
    omega

def contradictsFloor (m fuel : ℕ) (v : List ℕ) (s : FloorData) (code : ℕ) : Bool :=
  let r := min s.pairMask.log2 (m-1)
  let pv := v.map (slice m s.pairMask r)
  let av := replay 5 code (0::s.basis)
  fuel+paidCount 5 code<s.lower+pv.count 0 && pv.all (fun x => av.contains x)
lemma deadCount (f : ℕ→ℕ) {v : List ℕ} (nd : v.Nodup) :
    dead f v.toFinset=(v.map f).count 0 := by
  unfold dead
  have E : v.toFinset.filter (fun x => f x=0) = (v.filter (fun x => decide (f x=0))).toFinset := by ext x;simp
  rw [E,List.toFinset_card_of_nodup (nd.filter _)]
  simp only [List.count_eq_countP,List.countP_map]
  rw [List.countP_eq_length_filter]
  congr 2

theorem floor_consistent {m fuel : ℕ} (pos : 0 < m) {v : List ℕ} (ok : feasible m fuel v) (s : FloorData)
    (known : Floor m s) (code : ℕ) : contradictsFloor m fuel v s code=false := by
  let r := min s.pairMask.log2 (m-1)
  let p := projection m s.pairMask r (show r < m by dsimp [r];omega)
  let pv := v.map p.toFun
  let av := replay 5 code (0::s.basis)
  obtain ⟨k,hk,live,nd⟩ := ok
  obtain ⟨l,T,lim,pr,inside⟩ := projectLive p live
  rw [deadCount _ nd] at lim
  apply Bool.eq_false_iff.mpr
  intro bad
  change (decide (fuel+paidCount 5 code < s.lower+pv.count 0) && pv.all (fun x => av.contains x))=true at bad
  simp only [Bool.and_eq_true] at bad
  obtain ⟨lo,mem⟩ := bad
  have low := of_decide_eq_true lo
  have final : Possible m l av := by
    refine ⟨l,T,le_rfl,pr,?_⟩
    intro x hx
    have active : x∈pv := by simpa [pv] using inside x hx
    exact List.contains_iff_mem.mp (List.all_eq_true.mp mem x active)
  have size := known _ (replay_back 5 code (0::s.basis) (by simp) final)
  change l+pv.count 0≤k at lim
  omega

def essentialSet (m : ℕ) (v : List ℕ) := v.all fun x => !(enough m (cover m (v.filter (fun y => y != x))))
lemma essential_eq {m k S v} (live : Live m k S) (sub : ∀ a∈S, a∈v) (ess : essentialSet m v=true) : S=v.toFinset := by
  ext a
  constructor
  · exact fun h => List.mem_toFinset.mpr (sub a h)
  intro ha
  by_contra bad
  have contra := List.all_eq_true.mp ess a (List.mem_toFinset.mp ha)
  have cv := enoughSup live (v.filter (fun y => y != a)) (by
    intro x hx; have ne : x≠a := by rintro rfl;exact bad hx
    simp [ne,sub x hx])
  simp [cv] at contra
lemma floorEx {m : ℕ} {s : FloorData} (ex : Excluded m (s.lower-1) s.basis)
    (ess : essentialSet m s.basis=true) (nd : s.basis.Nodup) : Floor m s := by
  intro k ⟨j,S,lim,live,sub⟩
  by_contra bad
  have raw (a) (ha : a∈S) : a∈s.basis := (List.mem_cons.mp (sub a ha)).resolve_left (liveNonzero live a ha)
  have eq := essential_eq live raw ess
  exact ex ⟨j,by omega,eq ▸ live,nd⟩
abbrev Shelf (m : ℕ) := ℕ → {s : FloorData // Floor m s}
def lookupRows (go : ℕ → List ℕ → Bool) : List ℕ → List (List ℕ) → Bool
  | _,[] => false
  | code,v::vs => go (code.headD 0) v || lookupRows go code.tail vs
lemma lookup_ok {go : ℕ→List ℕ→Bool} {v : List ℕ} {vs : List (List ℕ)} (mem : v∈vs)
    (all : ∀ g,go g v=true) (tags : List ℕ) : lookupRows go tags vs=true := by
  induction vs generalizing tags with
  | nil => simp at mem
  | cons x xs ih =>
    rw [lookupRows,Bool.or_eq_true]
    rcases List.mem_cons.mp mem with rfl|next
    · exact Or.inl (all _)
    · exact Or.inr (ih next _)
def audit (m : ℕ) (db : Shelf m) (branches : ℕ → List ℕ) : ℕ → ℕ → List ℕ → Bool
  | 0,_,v => terminal m v
  | k+1,g,v => if g=0 then search m (k+1) v else if g%2=1 then
      !(contradictsFloor m (k+1) v (db ((g >>> 1) % 256)).val (g >>> 9))
    else terminal m v || lookupRows (audit m db branches k) (branches (g/2)) (successors m k v)
lemma audit_ok {m : ℕ} (pos : 0 < m) (db : Shelf m) (branches : ℕ → List ℕ)
    (k : ℕ) (v : List ℕ) (ok : feasible m k v) (g : ℕ) : audit m db branches k g v=true := by
  induction k generalizing g v with
  | zero => obtain ⟨j,lim,h,nd⟩ := ok; exact complete _ 0 h lim _ rfl nd
  | succ k ih =>
    rw [audit];split
    · obtain ⟨j,lim,h,nd⟩ := ok;exact complete _ _ h lim _ rfl nd
    split
    · simp [floor_consistent pos ok _ (db _).property]
    rw [Bool.or_eq_true]
    rcases move ok with t|⟨w,hw,next⟩
    · exact Or.inl t
    · exact Or.inr (lookup_ok hw (fun i => ih w next i) _)
lemma audit_off {m k v g db branches} (p : 0 < m) (e : audit m db branches k g v=false) : Excluded m k v := by
  intro h;exact Bool.noConfusion (e.symm.trans (audit_ok p db branches k v h g))
open PEqualNP.CircuitLowerBounds


def edges : List ℕ := [0,4,0,5,1,5,2,5,0,6,1,6,3,6,1,7,2,7,3,7,4,7,5,7]

def target (xs : List Bool) : Bool := decide (∃ i < edges.length / 2,
  xs.getD (edges.getD (2 * i) 0) false = true ∧ xs.getD (edges.getD (2 * i + 1) 0) false = true)

def gs : List Gate := [⟨.or, [0,7]⟩, ⟨.or, [4,5]⟩, ⟨.and, [8,9]⟩, ⟨.or, [1,2]⟩, ⟨.or, [5,7]⟩, ⟨.and, [11,12]⟩, ⟨.and, [0,6]⟩, ⟨.or, [1,3]⟩, ⟨.or, [6,7]⟩, ⟨.and, [15,16]⟩, ⟨.or, [10,13]⟩, ⟨.or, [14,17]⟩, ⟨.or, [18,19]⟩]

theorem count : gs.length = 13 := rfl

theorem basis (g : Gate) (hg : g ∈ gs) : (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  simp [gs] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 8000 in
theorem evalBits : ∀ a b c d e f g h : Bool,
    Circuit.eval ⟨gs, 20⟩ [a,b,c,d,e,f,g,h] = target [a,b,c,d,e,f,g,h] := by
  decide +kernel

theorem computes (x : Fin 8 → Bool) : Circuit.eval ⟨gs, 20⟩ (List.ofFn x) = target (List.ofFn x) :=
  evalBits (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)

def inputs : List ℕ := [0x80000804305012008094189404281409406c8b5096a100000008100400480200082b0868041a8710012000561035a0243858686c1c0800e0020e0238781f20604e0c78061c0e07803e07e00fc00180c07c380e03fc07007fff807c007ffff80ff007ff00fff003ffffffffff,0x100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x200200c560458033408100a009000ec10dd00235d201070f9400950a800cc83db088ba1ddd4088dc12316068d01a3a21c8f012ea47704830070063f003c07fe0c180700f8007e00ff8003ff8000ffffe00ff87c00ffc1ff8007c0fff80007f003ff07ff81fff01fffc01fc03fc00,0x801000480004910001ec08eda0004f5ba0800439e387c4020d160009b1a00018d61d000e1e703e10047bb704843dbdb90240a377724090c038007c0003ff8000fe007ff00007fff000003ffffff0001fff0007fff0001fffff800fffffff80003fff80001ffffe000001fffc0000,0x1f58008dda4e8000201f75d0100008b93c9e21f01000200043fbbdbb009028436edded74090011080206ddadeee812100048103878783e0ffc0007ffffc000000ffff80000007ffffffffc0000000001ffffff80000001ffffffff000000000003fffffffe00000000001ffffffff,0x3d6b44d0000800000017a5e49c221e00200000800000400002bdd62d56dd316800110040000022000404e1c970f21c1c21703c004000101ffffff800000000000fffffffffff80000000000000000001fffffffffffffe00000000000000000003ffffffffffffffffffe00000000,0x17f6f6eb7d6f34aaba400100000090000010090000020004832e1fce64e1be72709e0e790e087c0e1780000180800000018020000040200ffffffffffffffffff0000000000000000000000000000001fffffffffffffffffffffffffffffffffc000000000000000000000000000,0x849b0221b026ccc3800a01214ce0024120ce0420c38187000000000000000000000000000040001800000000000000000040000000400ffffffffffffffffffffffffffffffffffffffffffffffffe0000000000000000000000000000000000000000000000000000000000000]
def seeds : List Wire := inputs.map (fun a => (false,a))
def sample (j : ℕ) (i : Fin 8) : Bool := (inputs.getD i.val 0).testBit j
set_option maxRecDepth 8000 in
lemma listed (j : ℕ) : seeds.map (read j)=List.ofFn (sample j) := by
  let b := fun n => (inputs.getD n 0).testBit j
  change [false != b 0,false != b 1,false != b 2,false != b 3,false != b 4,false != b 5,false != b 6,false != b 7] = [b 0,b 1,b 2,b 3,b 4,b 5,b 6,b 7]
  simp
set_option maxRecDepth 8000 in
lemma labels : ∀ j : Fin 441, target (List.ofFn (sample j.val))=true ∧ target (List.ofFn (sample (441+j.val)))=false := by decide +kernel
theorem trace (C : Circuit) (fan : ∀ g∈C.gates, g.op ∈ ({.and,.or,.not} : Set GateOp) ∧ g.inputs.length≤2)
    (result : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x)=target (List.ofFn x)) :
    ∃ k≤C.gates.countP counted, Live 441 k inputs.toFinset := by
  let final := execute C.gates seeds
  let out := final.getD C.output zero
  have ev (i : ℕ) : read i out = C.eval (seeds.map (read i)) := by
    rw [show read i out = (final.map (read i)).getD C.output false from (read_get i final C.output).symm]
    rw [show final=execute C.gates seeds from rfl,execute_read i _ _ fan];rfl
  have good : Good 441 out.2 := by
    intro i hi same
    let j : Fin 441 := ⟨i,hi⟩
    have diff : read i out=read (441+i) out := by simp [read,same]
    have p := ev i;have n := ev (441+i)
    rw [listed,result,(labels j).1] at p
    rw [listed,result,(labels j).2] at n
    rw [p,n] at diff;contradiction
  have nz : out.2≠0 := by
    intro z;have bad := good 0 (by decide);simp [z] at bad
  have found : out.2∈ reps final := (get_simple final C.output).resolve_left nz
  obtain ⟨k,S,limit,live,sub⟩ := extract good nz C.gates seeds found
  have stays : ∀ a∈S, a∈inputs := by simpa [reps,seeds,List.map_map,Function.comp_def] using sub
  have ess : essentialSet 441 inputs=true := by decide +kernel
  exact ⟨k,limit,essential_eq live stays ess ▸ live⟩
def row0 : List ℕ := []
def row1 : List ℕ := [0,33,0,31,29,0,33,3,31,1,3,29,1,29]
def row2 : List ℕ := [11]
def row3 : List ℕ := [17]
def row4 : List ℕ := [3]
def row5 : List ℕ := [23]
def row6 : List ℕ := [21]
def row7 : List ℕ := [21,4,23,21,17,0,23,17,11,0,23,11,3,6,23,3,17,8,21,17,11,0,21,11,3,0,21,3,11,10,17,11,3,0,17,3,3,12,3,11]
def row8 : List ℕ := [5]
def row9 : List ℕ := [0,37]
def row10 : List ℕ := [37,37,13,13,13,13,0,13,13]
def row11 : List ℕ := [25]
def row12 : List ℕ := [13,13,13,13,13,13,13,13,37,37,37,13,37,37,5,13,13,5,25,16,25,18,37,37,37,37,5,16,25,5,37,20,37,37,37,37,5,22,18,5,37,37,37,37]
def row13 : List ℕ := [15]
def row14 : List ℕ := [7]
def row15 : List ℕ := [27]
def row16 : List ℕ := [25,26,27,25,17,0,27,17,15,0,27,15,7,6,27,7,17,28,25,17,15,0,25,15,7,0,25,7,15,30,17,15,7,0,17,7,7,22,7,15]
def row17 : List ℕ := [19]
def row18 : List ℕ := [0,39]
def row19 : List ℕ := [39,39,13,13,13,13,0,13,13]
def row20 : List ℕ := [13,13,13,13,19,34,27,19,39,39,39,39,27,34,27,36,13,13,13,13,39,39,39,13,39,39,13,13,13,13,39,39,39,39,19,30,19,36,39,38,39,39,39,39]
def row21 : List ℕ := []
def row22 : List ℕ := [1]
def row23 : List ℕ := [44089,0,44087,0,45111,59,44089,1,44087,44087,42,1,44,44089,44087,44087,0,44089,42,44087]
def row24 : List ℕ := [72759,72759,73271,57,72739,72739,37947,37947,44,37947,11,11,11,72759,1,1,0,43]
def row25 : List ℕ := [57]
def row26 : List ℕ := [108599,57,35,107575,0,74811,11,9,107575,107575,1,1,50,35]
def row27 : List ℕ := [108599,72743]
def row28 : List ℕ := [0,107563]
def row29 : List ℕ := [55,55,35,107577,107579,0,107579,107579,42,107579,35,107563,11,107577,54,107577,56,35,107577]
def row30 : List ℕ := [57,109111,0,1,110135,110135,42,1,1,77371,1,77371,0,110135]
def row31 : List ℕ := [57,0,50,56,42,43]
def row32 : List ℕ := [59,59,59,59,57,57,57,57,55,55,55,55,59,59,59,59,59,46,59,59,59,59,57,48,57,57,57,57,55,55,55,55,35,11,43,35,55,55,55,55,55,55,57,52,57,57,57,57,55,58,55,55,55,55,43,50,1,43,57,57,57,60,57,57,55,55,55,55,35,62,1,35]
def row33 : List ℕ := [69,0,67,0,65]
def row34 : List ℕ := [29,142405,107585]
def row35 : List ℕ := [108097,55,55,55,45,55,108609,45,69,69,107589,107589,69,0,107589,0,107589,107589,107589,107589,67,107587,67,107587,107587,107587,65,107585,65,107585,107585,107585,107585,107585,29,66,29,0,68,55]
def row36 : List ℕ := [55,107073,45,107585,29,0,45,29,55,45,55,55,69,108613,69,108613,108613,108613,67,108611,67,108611,65,0,108609,45,65,65,108609,108609,108609,108609]
def row37 : List ℕ := [45,29]
def row38 : List ℕ := [45,29,29,29]
def row39 : List ℕ := [29,29]
def row40 : List ℕ := [29,110657,29,110145,69,74,29,109125,109125,69,109125,69,67,76,29,109123,109123,67,109123,67,65,78,29,109121,109121,65,109121,65,55,0,29,0,29,55,29,55,45,29,29,29]
def row41 : List ℕ := [110145,29,45,29,45,29,110657,45,69,109637,69,109637,109637,109637,67,67,109635,109635,67,0,109635,0,109635,109635,109635,109635,65,109633,65,109633,109633,109633,55,66,55]
def row42 : List ℕ := [69]
def row43 : List ℕ := [29,109121,45,109633,55,84,45,55,29,45,45,29,69,110661,69,110661,67,110659,67,110659,110659,110659,65,110657,65,110657,110657,110657]
def row44 : List ℕ := [65]
def row45 : List ℕ := [29,109121,55,88,29,55,109633,29,29,29,45,29,69,110149,69,110149,110149,110149,67,110147,67,110147,110147,110147,65,110145,65,110145]
def row46 : List ℕ := [143425,55,55,55,29,55,142913,29,69,142405,69,142405,142405,142405,142405,142405,67,142403,67,142403,142403,142403,65,65,142401,142401,65,0,142401,0,142401,142401,142401,142401,45,66,45,0,68,55]
def row47 : List ℕ := [55,141889,29,142401,67,142915,142915,67,65,142913,142913,65,29,0,29,45,55,29,55,55,69,0,142917,29,69,69,142917,142917,142917,142917,142913,142913]
def row48 : List ℕ := [67,67,67,67,65,65,65,65,69,69,69,69,69,69,69,69,69,69,69,69,65,65,65,65,67,67,67,67,67,67,67,67,67,67,67,67,65,65,65,65,65,65,65,65,65,65,65,65,55,70,72,55,80,82,86,90,55,92,94,55]
def row49 : List ℕ := [0,13]
def row50 : List ℕ := [61,46151]
def row51 : List ℕ := [81,0,73,0,71]
def row52 : List ℕ := [81,37953,37953,81,73,37951,37951,73,71,41,71,41,98,0,41,71,37963,53,37951,37963,38475,51,100,37967,38987,41,41,37965,37951,37951,61,102,61]
def row53 : List ℕ := [37959,0,75,37963,53,38477,38479]
def row54 : List ℕ := [53,37963,81,37953,37953,81,73,38975,38975,73,71,41,41,71,41041,37963,39505,38475,38991,37963,0,38991,73809,37963,72273,38987,38989,37963,41,38989,38975,38975,61,0,61,53]
def row55 : List ℕ := [81,0,73,0,75]
def row56 : List ℕ := [81,42051,42051,81,73,42047,42047,73,37959,53,42047,37959,38471,43,38983,59,41,44109,75,41,75,41,42047,42047,61,110,61]
def row57 : List ℕ := [71,37959,53,44621,44623]
def row58 : List ℕ := [81]
def row59 : List ℕ := [61,41]
def row60 : List ℕ := [53,37959,77905,37959,38983,76369,75,41,41,75,81,43075,43075,81,73,43071,43071,73,61,116,53,61,45137,37959,43601,38471,45135,37959,45133,37959,41,45133,37959,41,43071,43071,118,37959]
def row61 : List ℕ := [46151]
def row62 : List ℕ := [46151,61]
def row63 : List ℕ := [37949]
def row64 : List ℕ := [0,46151]
def row65 : List ℕ := [77,46157,77,61,77,46157,77,0,77,188781649,0,44095,44095,155236433,79,61,53,61,53,46157,37949,188781649,188781649,44095,44095,122,0,124,0,188781649,188781649,44095,44095,46151,46151,188782673,79,126,46157,188781649,188781649,44095,46157,128,46157,44095,188781649]
def row66 : List ℕ := [75,72777]
def row67 : List ℕ := [297833553,297833553,63,63,41,41,155263057,77,63,37963,297833543,297833543,75,37963,75,79,75,37963,75,53,75,72777,72777,41,41,79,37967,79,51,37967,37963,297834065,77,63,37967,126,37967,63,297833553,37949,37949,0,37963,132]
def row68 : List ℕ := [77,71]
def row69 : List ℕ := [314610769,314610769,63,63,155267153,77,63,37959,71,37959,71,79,71,37959,71,53,71,41,41,79,44111,79,43,314611281,77,63,44111,128,44111,41,41,63,314610769,37949,37949,136,37959]
def row70 : List ℕ := [73]
def row71 : List ℕ := [81,44095]
def row72 : List ℕ := [75,102,0,75,81,44099,81,44099,42,116,44099,81,73,44095,73,44095,42,140,44095,73,71,110,0,71,47181,53,46157,37949,44095,44095,46669,33,44095,46159,46157,142,132,46157,44099,46157,44095,46157,44095,44095]
def row73 : List ℕ := [37969,0,37961,0,53,53,46669,46669,46671]
def row74 : List ℕ := [46157,46159,0,37959,61,53,46157]
def row75 : List ℕ := [75,0,53,75,81,45123,45123,81,73,45119,45119,73,71,0,53,71,46157,53,47181,47181,37949,47181,47185,77,45649,77,47183,47183,45119,47183,79953,79,47181,47183,78417,47181,47181,0,47181,45123,47181,45119,47181,45119,45119]
def row76 : List ℕ := [77,155267665,79,37949,79,46671,79,0,37949,325096529,325096529,63,37949,0,37949,37949,37949,37949,53,63,37949,79433,79433,79,37949,79,46671,37949,46671,325097041,77,63,46671,63,325096529]
def row77 : List ℕ := [31,102,53,31,77]
def row78 : List ℕ := [81,0,73]
def row79 : List ℕ := [61,156,61,53,77,37949,0,79]
def row80 : List ℕ := [53,110,53,1,71,118,122,77,0,136,37963]
def row81 : List ℕ := [61,0,61,53,77,37949,0,79]
def row82 : List ℕ := [75,37963,104,106,108,53,75,37963,81,37969,37969,37969,37969,37969,81,37969,73,37961,63,63,63,63,73,37961,71,37959,112,114,120,53,71,37959,38481,77,77,77,77,77,79,77,77,77,37963,79,79,37963,37969,37969,37969,37969,37961,63,79,79,79,37961,37959,79,79,37959,79,130,79,79,79,79,38993,79,77,37963,134,77,77,77,37963,37969,37969,37969,37969,37969,37969,37961,63,77,77,77,37961,37959,138,77,77,77,37959,37969,37969,37969,37969,37961,63,37963,37961,37959,41,37963,37959,37969,63,37969,37969,37969,37969,37969,37969,37969,37969,37959,63,37959,37961,61,53,144,146,61,148,150,53,77,77,77,152,77,77,37963,154,158,37963,37969,37969,37969,37969,37961,63,63,37961,37959,160,162,37959]
def row83 : List ℕ := [81,0,77,0,71]
def row84 : List ℕ := [81,40001,40001,81,40009,41,40009,40009,40521,47,100,74831,41033,49,77,37951,77,37951,37951,42059,71,71,41,41,71,98,41,0,41,40009,61,166,61]
def row85 : List ℕ := [0,41,0,77903,0,45131,0,43073,0,0,42]
def row86 : List ℕ := [0,43073]
def row87 : List ℕ := [444641355,43073,440479823,440479823,42]
def row88 : List ℕ := [0,41,0,77903,0,45131,0,43073]
def row89 : List ℕ := [0,41,0,77903,0,45131,0,0,0,43073]
def row90 : List ℕ := [43073,43073,43073,43073,41,41,41,41,45131,45131,40007,45131,45131,45131,45131,45131,77903,77903,77903,77903,77903,77903,77903,77903,77903,77903,77903,77903,77903,77903,77903,77903,45131,45131,40007,45131,45131,45131,45131,45131,45131,45131,45131,45131,41,41,41,41,45131,45131,45131,45131,43073,43073,43073,43073,170,0,0,172,43073,174,43073,43073,43073,43073,41,41,41,41,45131,45131,45131,45131,176,0,0,0,43073,43073,43073,43073,178,42,0,172]
def row91 : List ℕ := [43069]
def row92 : List ℕ := [0,725660743]
def row93 : List ℕ := [0,448836679]
def row94 : List ℕ := [39997,297841735]
def row95 : List ℕ := [42,107595,0,583054407]
def row96 : List ℕ := [75,46155,75,61,75,46155,75,0,75,188783697,182,41,41,163625041,79,61,41,61,41,46155,39997,188783697,188783697,184,0,41,41,188783697,188783697,100,41,46151,41,46151,41,46151,188784721,79,188783697,188783697,186,46155,41,46155,124,41,188,46155,190,188783697]
def row97 : List ℕ := [75,448967751]
def row98 : List ℕ := [73,109639]
def row99 : List ℕ := [440441937,440441937,163686481,75,40009,440441937,73,40009,73,79,73,40009,73,41,73,109639,41,109639,41,109639,79,74831,79,47,440442449,75,41,74831,186,74831,37951,37951,37951,37951,41,41,41,40009,39997,39997,194,40009,196,41]
def row100 : List ℕ := [81,37953,37953,81,73,37951,37951,73,71,41,71,41,98,0,41,71,38987,41,41,37965,38475,51,100,37967,37963,53,37951,37963,37951,37951,61,102,61]
def row101 : List ℕ := [75,297874503]
def row102 : List ℕ := [77,72775]
def row103 : List ℕ := [297835601,297835601,37951,37951,41,41,163651153,75,77,37965,77,41,297835593,297835593,41,37965,77,37965,77,79,77,37951,37951,72775,41,72775,41,72775,79,37967,79,51,37967,37965,297836113,75,41,37967,188,37967,37951,297835601,39997,39997,202,37965,204,41]
def row104 : List ℕ := [41025,142407]
def row105 : List ℕ := [107595]
def row106 : List ℕ := [41537,297869893]
def row107 : List ℕ := [163686481,107599,212,72773]
def row108 : List ℕ := [583185479,0,0,440439885]
def row109 : List ℕ := [45,0,142407]
def row110 : List ℕ := [0,107599,583120455]
def row111 : List ℕ := [40017,40017,72745,208,72745,45,73,40009,40009,73,142407,72745,142407,72745,174,72745,72745,142407,107599,210,107599,40009,40529,107595,107595,107595,107599,107595,72745,107599,190,107599,214,107595,40009,40009,41041,107599,72745,107595,40009,440439885,107597,37951,107597,37951,37951,107595,216,40009,142397,218,142397,72745,107595,220]
def row112 : List ℕ := [81,75305]
def row113 : List ℕ := [71,13]
def row114 : List ℕ := [81,77371]
def row115 : List ℕ := [81,44097,81,44097,42,224,44097,81,73,166,116,73,71,41,71,41,98,226,41,71,47179,41,46155,39997,41,41,46667,31,46155,228,44097,46155,196,46155,77,102,77,0,204,46155,218,44097]
def row116 : List ℕ := [0,42]
def row117 : List ℕ := [75,163689041,79,39997,79,79439,79,0,39997,459316305,459316305,232,39997,41,39997,39997,39997,39997,41,41,39997,112199,41,112199,41,112199,79,39997,79,79439,39997,79439,459316817,75,41,79439,220,459316305]
def row118 : List ℕ := [79]
def row119 : List ℕ := [33,102,33,41,75,236,202,78919]
def row120 : List ℕ := [81,0,71]
def row121 : List ℕ := [75,1]
def row122 : List ℕ := [61,240,61,41,75,39997,79431,0,242,79]
def row123 : List ℕ := [216,41,166,41,3,177223,42,184,75,236,194,37965,42]
def row124 : List ℕ := [61,240,61,41,75,39997,177735,0,242,79]
def row125 : List ℕ := [81,40017,40017,40017,40017,40017,81,40017,73,40009,168,41,41,41,73,40009,71,41,71,40007,41,41,180,41,41,41,71,40007,40529,75,75,75,75,75,79,75,75,75,37965,79,79,37965,40017,40017,40017,40017,40009,79,79,40009,40007,41,79,79,79,40007,79,192,79,79,79,79,41041,79,75,40017,40017,40017,40017,40017,40017,40009,198,75,75,75,40009,40007,41,75,75,75,40007,77,37965,200,41,77,37965,41,41,75,206,75,75,75,75,40017,40017,40017,40017,40009,37951,37965,40009,40007,41,37965,40007,40017,222,40017,40017,40017,40017,40017,40017,40017,40017,40007,41,40007,40009,61,41,230,41,61,41,41,41,75,75,75,234,75,75,37965,238,244,37965,40017,40017,40017,40017,40009,246,248,40009,40007,41,41,40007]
def row126 : List ℕ := [0,43069]
def row127 : List ℕ := [49]
def row128 : List ℕ := [0,45,0,45,73,73,44095,44095,0,0,172013649,107599,49,49]
def row129 : List ℕ := [73,46153,73,61,73,46153,73,0,73,44095,44095,188785745,252,172013649,79,61,49,61,49,46153,46153,188785745,188785745,122,254,188785745,188785745,188786769,79,256,46153,188785745,188785745,188785745,44095,44095,100,0,46151,46151,128,46153]
def row130 : List ℕ := [107599,172008017,172009041,42065,172009041,107599,40511,40511,0,45,0,45]
def row131 : List ℕ := [0,45,0,45,73,73,44095,44095,172013649,107599,0,0,49,49]
def row132 : List ℕ := [107599,65,107601,107599]
def row133 : List ℕ := [40521,583052359]
def row134 : List ℕ := [107599,108101,107599]
def row135 : List ℕ := [107599,110149,107599,0,0,440443981]
def row136 : List ℕ := [109637,107599,144977,0,107599]
def row137 : List ℕ := [107597]
def row138 : List ℕ := [81,109637,81,116,81,47177,49,46665,3,44095,440546383,107597,107597,44095,107597,274]
def row139 : List ℕ := [42065,110149,49,46665,440443981]
def row140 : List ℕ := [46153,0,583052359,46153]
def row141 : List ℕ := [145489,143953,46153,49,73,73,440547407,440547407,45119,440547407,107597,107597]
def row142 : List ℕ := [81,107597]
def row143 : List ℕ := [284,49,0,107599]
def row144 : List ℕ := [0,440443979]
def row145 : List ℕ := [0,49,0,107599]
def row146 : List ℕ := [81,42065,42065,107599,81,42065,107599,107599,42065,107599,260,107599,42577,73,73,440443981,63,107599,107599,107599,440443981,440443979,107599,107599,440443979,583052359,107599,107599,583052359,107599,262,107599,107599,107599,107599,440443981,63,440443981,63,107597,440443981,63,107597,440443981,63,440443979,63,440443981,440443979,583052359,63,440443981,583052359,440443979,264,440443979,19,440443979,266,440443979,49,583052359,72745,440443979,583052359,583052359,268,583052359,19,583052359,0,583052359,49,19,270,272,19,49,276,278,280,282,49,440443981,63,63,440443981,440443979,0,286,440443979,583052359,288,290,583052359]
def row147 : List ℕ := [81,40001,40001,81,41033,49,40521,47,100,74831,40009,41,40009,40009,77,37951,77,37951,37951,42059,71,71,41,41,71,98,41,0,41,40009,61,166,61]
def row148 : List ℕ := [42059,49,40521,40521,75855,266,44103]
def row149 : List ℕ := [108113,41033,41033,107089,81,40001,40001,81,71,41,41,71,40009,49,41033,41033,41041,73,39505,73,75343,42059,0,75343,41033,41033,77,38975,77,38975,41,41033,61,0,61,49]
def row150 : List ℕ := [77,0,75,0,81]
def row151 : List ℕ := [44103,49,44615,35,45127,59,44105,44105,77,42047,77,42047,75,41,75,41,81,107589,81,107589,61,300,61]
def row152 : List ℕ := [44103,49,71,44617,142927]
def row153 : List ℕ := [49,44103,143441,44103,45127,141905,81,108613,108613,81,45129,44103,45137,44103,43601,44615,143439,44103,45129,45129,77,43071,77,43071,75,41,75,41,44103,41,61,116,61,49,118,44103]
def row154 : List ℕ := [71,0,583050315]
def row155 : List ℕ := [172109905,73,71,44103,71,49,71,44103,71,79,71,79,142415,79,35,142415,44103,583050833,73,63,142415,128,142415,63,44103,44103,583050315,41,41,583050321,583050321,308,44103]
def row156 : List ℕ := [109637,110149]
def row157 : List ℕ := [81,116]
def row158 : List ℕ := [81,116,44095]
def row159 : List ℕ := [44095,44095]
def row160 : List ℕ := [77,0,0,274]
def row161 : List ℕ := [81,109637,81,109637,312,314,109637,81,47177,49,46665,3,44095,144463,46153,316,276,46153,109637,46153,46153,77,77,44095,44095,77,318,44095,320,75,166,75,0,71,300,71]
def row162 : List ℕ := [42065,0,49,49,46665,46665,144975,278,42061]
def row163 : List ℕ := [46153,144463,0,44103,61,49,46153,280]
def row164 : List ℕ := [81,110661,110661,81,46153,49,47177,47177,47185,73,45649,73,145487,145487,45119,145487,145489,47177,143953,47177,282,47177,110661,47177,47177,77,45119,77,45119,75,0,75,49,71,0,71,49]
def row165 : List ℕ := [31,166,31,49]
def row166 : List ℕ := [81,0,284,77]
def row167 : List ℕ := [61,332,61,49,140,79,286]
def row168 : List ℕ := [49,300,1,49,71,118,308,122,288,42059]
def row169 : List ℕ := [61,0,61,49,140,79,254,290]
def row170 : List ℕ := [81,42065,42065,42065,42065,42065,81,42065,42577,73,73,73,73,73,79,73,73,73,42061,63,79,79,79,42061,42059,79,79,42059,42065,42065,42065,42065,44103,79,79,44103,79,258,79,79,79,79,43089,79,73,42065,292,73,42065,42065,42065,42065,42065,42065,77,42061,63,63,77,42061,63,63,73,73,73,73,42059,63,42061,42059,42065,42065,42065,42065,44103,63,42061,44103,75,42059,294,296,75,42059,298,49,73,73,73,73,42065,42065,42065,42065,44103,41,42059,44103,71,44103,302,304,71,44103,306,49,44103,310,73,44103,73,73,42065,42065,42065,42065,61,49,322,324,61,326,328,49,73,73,73,73,42061,63,63,42061,42059,330,334,42059,42065,42065,42065,42065,44103,336,338,44103]
def row171 : List ℕ := [45127,59,44105,44105,44615,35,44103,49,77,42047,77,42047,75,41,75,41,81,107589,81,107589,61,300,61]
def row172 : List ℕ := [73,142411]
def row173 : List ℕ := [180498001,71,44105,583052369,73,44105,73,79,73,44105,73,59,73,79,142415,79,35,142415,44105,583052881,71,41,142415,42047,42047,41,44105,142411,142411,583052369,583052369,344,59]
def row174 : List ℕ := [81,42051,42051,81,73,42047,42047,73,38983,59,41,44109,38471,43,37959,53,42047,37959,75,41,75,41,42047,42047,61,110,61]
def row175 : List ℕ := [108101]
def row176 : List ℕ := [180498001,107599]
def row177 : List ℕ := [45,0,107595]
def row178 : List ℕ := [44113,44113,107579,350,107579,45,73,44105,44105,73,107599,44105,44625,142407,142407,142407,107599,142407,72745,107599,352,142407,44105,142407,45137,107599,44105,440446029,107597,42047,107597,42047,107595,72745,107595,107579,0,44105,142397,354,142397,107579]
def row179 : List ℕ := [81,41]
def row180 : List ℕ := [0,75303]
def row181 : List ℕ := [75,75303]
def row182 : List ℕ := [81,142405,81,142405,42,224,142405,81,73,300,116,73,47175,59,46663,1,46151,46151,177231,46151,41,177231,46151,358,142405,46151,344,46151,77,110,77,0,75,75,41,41,75,360,41,362,354,142405]
def row183 : List ℕ := [59,110,33,59]
def row184 : List ℕ := [81,0,75]
def row185 : List ℕ := [61,368,61,59]
def row186 : List ℕ := [0,59,300,59,3,44109]
def row187 : List ℕ := [81,44113,44113,44113,44113,44113,81,44113,73,44105,342,59,59,59,73,44105,44625,71,71,71,71,71,79,71,71,71,44109,79,79,44109,44107,41,79,79,79,44107,44113,44113,44113,44113,44105,79,79,44105,79,79,79,79,45137,79,71,44113,44113,44113,44113,44113,44113,71,346,71,71,71,71,77,44109,348,59,77,44109,59,59,71,71,71,71,44107,41,44109,44107,44113,44113,44113,44113,44105,42047,44109,44105,75,44107,41,59,75,44107,59,59,71,71,71,71,44113,44113,44113,44113,44105,41,44107,44105,44113,356,44113,44113,44113,44113,61,59,364,59,61,59,59,59,71,71,71,71,44109,366,370,44109,44107,41,41,44107,44113,44113,44113,44113,44105,372,370,44105]
def row188 : List ℕ := [75,102,0,75,81,44099,81,44099,42,116,44099,81,73,44095,73,44095,42,140,44095,73,71,110,0,71,46157,142,132,46157,44099,46157,44095,46157,46669,33,44095,46159,47181,53,46157,37949,44095,44095,44095,44095]
def row189 : List ℕ := [46161,81]
def row190 : List ℕ := [67]
def row191 : List ℕ := [46161,378,46153,42,77,46157,142,44099,380,33,47183]
def row192 : List ℕ := [44095,81]
def row193 : List ℕ := [75]
def row194 : List ℕ := [384,46157,75,0,0,75,81,44099,44099,81,73,44095,44095,73,71,386,0,71,46157,44095,38993,46157,37457,46669,46671,46157,44095,46671,79441,46157,78417,47181,0,46157,44095,44095,44095,44095]
def row195 : List ℕ := [77,384,46157,44099,0,188782673,61]
def row196 : List ℕ := [81,44097,81,44097,42,224,44097,81,73,166,116,73,71,41,71,41,98,226,41,71,46155,228,44097,46155,196,46155,46667,31,47179,41,46155,39997,41,41,77,102,77,0,204,46155,218,44097]
def row197 : List ℕ := [13]
def row198 : List ℕ := [65,110139]
def row199 : List ℕ := [46161,378,46151,394,75,46155,228,44097,396,31,79951]
def row200 : List ℕ := [77371,81]
def row201 : List ℕ := [0,77]
def row202 : List ℕ := [0,73]
def row203 : List ℕ := [400,46155,77,0,0,77,81,44097,44097,81,73,402,0,73,71,41,41,71,46155,77371,41041,46155,39505,46667,79439,46155,112209,46155,111185,47179,0,46155,41,41,404,44097]
def row204 : List ℕ := [75,400,46155,44097,0,188784721,61]
def row205 : List ℕ := [110139]
def row206 : List ℕ := [110149,43069,188786769,112207,188888657,0,44099,0,44097,0,110139]
def row207 : List ℕ := [110149]
def row208 : List ℕ := [0,44099]
def row209 : List ℕ := [0,109637,110149,110149,0,0,42]
def row210 : List ℕ := [109637]
def row211 : List ℕ := [44097]
def row212 : List ℕ := [43069,188787281]
def row213 : List ℕ := [109637,112207]
def row214 : List ℕ := [0,110139]
def row215 : List ℕ := [0,0,0,44097]
def row216 : List ℕ := [44099,42,0,44099,44097,410,0,44097,412,414,416,418,42,420,110139,422,424,110139,46161,46161,46161,112207,112207,46161,112207,112207,112207,112207,112207,112207,112207,112207,112207,112207,112207,112207,112207,112207,112207,112207,112207,112207,46161,46161,46161,112207,43069,0,43069,44099,43069,0,43069,44097,43069,416,43069,426,43069,422,43069,110139,44097,0,44099,44097,44099,0,44099,42,44099,0,44099,110139,44097,0,44097,428,44097,75305,44097,110139,110139,0,110139,430]
def row217 : List ℕ := [109125,116]
def row218 : List ℕ := [0,0,67]
def row219 : List ℕ := [110139,0,65]
def row220 : List ℕ := [46161,110149,43069,112207,0,44099,0,44097,0,110139]
def row221 : List ℕ := [110661,116,44099]
def row222 : List ℕ := [110149,81]
def row223 : List ℕ := [143429,44097]
def row224 : List ℕ := [0,112207]
def row225 : List ℕ := [112207,725726799]
def row226 : List ℕ := [81,46161,46161,378,434,44099,436,0,44099,44097,438,0,44097,440,442,444,420,110139,446,0,110139,46161,43069,112207,43069,112207,112207,112207,43069,0,112207,252,112207,252,112207,112207,0,46161,112207,112207,112207,448,0,450]
def row227 : List ℕ := [81,109637,81,116,81,46665,3,44095,440546383,47177,49,107597,107597,44095,107597,274]
def row228 : List ℕ := [81,109637,81,109637,312,314,109637,81,46153,316,454,46153,109637,46153,46153,46665,3,44095,144463,47177,49,77,77,44095,44095,77,318,44095,320,75,166,75,0,71,300,71]
def row229 : List ℕ := [0,17]
def row230 : List ℕ := [46161,458,116,73,3,440547407,440448077]
def row231 : List ℕ := [46161,378,73,46153,316,109637,442,460,3,145487,46157,42]
def row232 : List ℕ := [81,0,116]
def row233 : List ℕ := [81,0,44095]
def row234 : List ℕ := [316,46153,77,44095,44095,77,75,240,0,75,81,110149,81,110149,418,464,110149,81,71,368,0,71,46153,46153,43089,46153,41553,46665,144975,46153,44095,144975,144977,46153,143953,47177,466,46153,46153,44095]
def row235 : List ℕ := [0,110149,81]
def row236 : List ℕ := [73,46161,434,316,46153,110149,470,188786769,61,0,188888657,79]
def row237 : List ℕ := [81,142405,81,142405,42,224,142405,81,73,300,116,73,46151,358,142405,46151,344,46151,46663,1,46151,46151,177231,46151,41,177231,47175,59,77,110,77,0,75,75,41,41,75,360,41,362,354,142405]
def row238 : List ℕ := [75303]
def row239 : List ℕ := [46161,378,71,46151,358,142405,446,1,46151,178255,46155,476]
def row240 : List ℕ := [0,73,583054407]
def row241 : List ℕ := [358,46151,177745,46151,47175,176721,77,0,0,77,75,41,41,75,81,142917,142917,81,73,0,0,73,45137,46151,46151,46151,43601,46151,46663,46151,177743,46151,46151,41,177743,358,46151,46151,41,480,142917]
def row242 : List ℕ := [2972306156113]
def row243 : List ℕ := [71,188921425,79,358,46151,142917,0,46151,188787281,46151,484]
def row244 : List ℕ := [124,0,188781649,188781649,44095,44095,46151,46151,188782673,79,126,46157,188781649,188781649,44095,46157,122,46157,77,46157,77,61,77,46157,77,0,77,188781649,0,44095,44095,61,53,61,53,46157,37949,155236433,79,188781649,188781649,44095,44095,122,0,44095,188781649]
def row245 : List ℕ := [448836679]
def row246 : List ℕ := [297841735,39997]
def row247 : List ℕ := [583054407,42,107595]
def row248 : List ℕ := [188783697,188783697,100,41,46151,41,46151,41,46151,188784721,79,188783697,188783697,490,46155,41,46155,75,46155,75,61,75,46155,75,0,75,188783697,182,41,41,61,41,61,41,46155,39997,163625041,79,188783697,188783697,184,0,41,41,124,41,492,46155,494,188783697]
def row249 : List ℕ := [0,45,0,45,73,73,44095,44095,0,0,49,49,172013649,107599]
def row250 : List ℕ := [188785745,188785745,188786769,79,498,46153,188785745,188785745,188785745,73,46153,73,61,73,46153,73,0,73,44095,44095,188785745,252,61,49,61,49,46153,46153,172013649,79,188785745,188785745,122,254,44095,44095,100,0,46151,46151,122,46153]
def row251 : List ℕ := [77,46157,47181,77,77,0,78929,0,79,33]
def row252 : List ℕ := [75,46155,47179,75,75,0,111697,0,79,31]
def row253 : List ℕ := [0,45,0,45,73,73,44095,44095,0,440546383,440546383,3,591443537,142397,44095,440546383,0,440546383,2388727477319,2388727477319,44095]
def row254 : List ℕ := [725660743]
def row255 : List ℕ := [0,79433]
def row256 : List ℕ := [591443025,591443025,188888657,61,506,46153,591443025,591443025,591443025,73,46153,73,79,73,46153,73,0,73,44095,44095,591443025,448,79,144463,79,3,46153,46153,591443537,61,44095,144463,508,144463,591443025,591443025,725660743,725660743,44095,510,44095,46153,42,46153]
def row257 : List ℕ := [6,0,46153,73,3,440546383,142397,440448077]
def row258 : List ℕ := [109635]
def row259 : List ℕ := [61,514,73,46153,47177,73,73,466,144465,416,79,3,144463,61,46157,516]
def row260 : List ℕ := [188921415]
def row261 : List ℕ := [61,591443025,47177,143951,188888657,188888657,520,61,46153,188888657,73,73,44095,44095,188888657,0,79,144975,79,61,46153,46153,593540689,61,44095,144975,0,144975,188888657,188888657,188921415,188921415]
def row262 : List ℕ := [177231]
def row263 : List ℕ := [112199,188855879]
def row264 : List ℕ := [142407,0,583054407]
def row265 : List ℕ := [725660753,725660753,0,0,188921425,61,725660753,725660753,524,46151,71,46151,71,79,71,46151,71,484,71,41,41,725660753,450,79,177231,79,1,46151,46151,46151,177231,46151,725661265,61,122,177231,41,177231,725660753,725660753,128,177231,524,46151,41,526,41,46151,528,725660753]
def row266 : List ℕ := [142401]
def row267 : List ℕ := [61,71,46151,47175,71,71,358,177233,422,79,1,61,46151,46155,532]
def row268 : List ℕ := [0,79]
def row269 : List ℕ := [0,49]
def row270 : List ℕ := [0,0,107599]
def row271 : List ℕ := [61,725660753,47175,176719,188921425,188921425,536,61,71,71,41,41,188921425,0,79,46151,79,79,177743,46151,46151,191018577,61,0,177743,41,177743,188921425,188921425,538,177743,540,188921425]
def row272 : List ℕ := [51,102,0,51,132,77,204,75,72785,0,124,79,126,492,61]
def row273 : List ℕ := [43,110,0,43,76881,0,79,0,122,524]
def row274 : List ℕ := [47,166,0,47,196,75,107601,0,100,79,490,42]
def row275 : List ℕ := [81,109125,81,81,45,45,109125,109125,45,45,45,45,45,45,45,109125,45,109125,109125,42,109125,109125,0,6,45,45,45,45,17]
def row276 : List ℕ := [110149,46161,458,45]
def row277 : List ℕ := [110149,110149,107597]
def row278 : List ℕ := [46161,73,458,116,3,440547407,440448077]
def row279 : List ℕ := [188786769,142397]
def row280 : List ℕ := [73,73,0,45,0,45,44095,44095,49,49,0,0,172013649,107599]
def row281 : List ℕ := [583054407,107595,42]
def row282 : List ℕ := [188888657,107599]
def row283 : List ℕ := [591443025,45,110149]
def row284 : List ℕ := [73,73,0,45,0,45,44095,44095,440546383,3,0,440546383,591443537,142397,44095,440546383,0,440546383,2388727477319,2388727477319,44095]
def row285 : List ℕ := [46153,73,6,0,3,440546383,142397,440448077]
def row286 : List ℕ := [142407,583054407]
def row287 : List ℕ := [0,107599]
def row288 : List ℕ := [46161,46161,550,552,45,554,418,434,420,45,73,454,556,46153,46153,73,46153,73,107597,44095,44095,107597,107595,218,404,107595,142407,354,480,142407,558,107599,560,107599,46153,46153,46153,46673,142397,107599,107599,107599,142397,44095,107599,562,107599,583054407,583054407,564,566,568,570,46153,46153,46153,47185,107599,572,574,46153,440448077]
def row289 : List ℕ := [61,107589]
def row290 : List ℕ := [35,300,0,35,344,71,142417,0,79,578,46151,122,0,61,524]
def row291 : List ℕ := [77,46157,376,382,388,390,77,46157,75,46155,392,398,406,408,75,46155,81,46161,81,46161,46161,46161,432,452,46161,46161,81,46161,73,46153,456,462,468,472,73,46153,71,46151,474,478,482,486,71,46151,46673,61,79,79,79,79,79,79,61,79,46157,488,79,79,79,46157,46155,496,79,79,79,46155,46161,46161,46161,46161,46161,46161,46153,500,79,79,79,46153,46151,46151,79,79,46151,46151,47185,79,79,46157,502,61,46157,46155,504,61,46155,46161,46161,46161,46161,46161,46161,46153,512,518,522,61,46153,46151,530,534,542,61,46151,46155,544,46157,46155,46161,46161,46161,46161,46153,44095,46157,46153,46151,546,46157,46151,46161,46161,46161,46161,46153,548,46155,46153,46151,41,46155,46151,46161,576,46161,46161,46161,46161,46161,46161,46161,46161,46151,580,46151,46153]
def row292 : List ℕ := [75,0,33,75,81,44611,44611,81,73,44607,44607,73,71,0,33,71,46669,61,0,46669,44611,46669,44607,46669,37457,46157,38993,46669,46159,46669,61,46159,46669,78929,45645,79953,46669,61,44607,61,44607,44607]
def row293 : List ℕ := [81,44609,44609,81,73,0,31,73,71,41,31,71,46667,61,44609,46667,0,46667,39505,46155,41041,46667,78927,46667,61,78927,46667,111697,45643,112721,46667,61,41,61,77,0,77,31,0,46667,0,44609]
def row294 : List ℕ := [81,81,46153,46665,142397,440546383,144465,145489,107597,107597]
def row295 : List ℕ := [81,109637,109637,81,46665,61,588,46665,109637,46665,46665,41553,46153,43089,46665,144463,46665,61,144463,46665,144465,45641,145489,46665,61,77,44607,77,44607,44607,46665,75,0,75,3,0,46665,71,0,71,3]
def row296 : List ℕ := [725723215,142405,440579151,440579151,142397,142397,107553,107553]
def row297 : List ℕ := [142405,142405,142405,142405,1,0,1,3,46663,177231,177231,177231,177231,177231,177231,177231,177231,177231,177231,177231,177231,177231,177231,177231,177231,177231,177231,177231,177231,177231,177231,177231,177231,177231,177231,46663,61,61,61,61,61,61,61,61,61,61,61,61,61,61,61,61,33,0,33,1,31,0,33,31,142405,142405,142405,142405,33,3,33,3,31,1,31,1,142405,142405,142405,142405,31,0,31,3,142405,592,142405,142405,142405,142405]
def row298 : List ℕ := [81,142405,142405,81,73,0,1,73,46663,61,46663,142405,46663,142405,46663,0,46663,3,43601,46151,45137,46663,46663,177231,177231,46663,46663,177233,45639,178257,46663,177231,61,46663,77,0,77,1,46663,0,33,46663,75,41,75,41,46663,41,31,46663,0,142405]
def row299 : List ℕ := [142397,45,440547407,45641,44607,142397,142397,142397,591443025,142397,44607,3]
def row300 : List ℕ := [591443537,591443537,593540689,61,598,46665,591443537,591443537,591443537,145487,45641,73,73,44607,61,61,61,79,79,591443025,61,44607,3,44607,46665,0,46665,0,3]
def row301 : List ℕ := [725661265,725661265,0,1,191018577,61,725661265,725661265,0,46663,178255,45639,71,177231,71,46663,71,41,61,79,79,46663,177231,725660753,61,0,46663,41,1,41,46663,0,725661265]
def row302 : List ℕ := [61,0,61,51,0,77,0,75,0,72775,61]
def row303 : List ℕ := [61,0,61,43,0,71]
def row304 : List ℕ := [61,0,61,47,0,75,0,73,0,109639]
def row305 : List ℕ := [440547407,45641,142397,45,44607,142397,142397,142397,591443025,142397,44607,3]
def row306 : List ℕ := [46673,46673,142397,0,142397,45,73,588,142397,46665,46665,73,46665,73,107599,45649,107597,44607,142397,107597,107595,0,142397,107595,142407,592,142397,0,142397,142407,142397,142407,107599,46665,46161,142397,107599,142397,107599,107599,0,142397,610,142397,46665,46665,46665,0,142397,46665,440448589]
def row307 : List ℕ := [61,0,61,35,0,71,0,61]
def row308 : List ℕ := [79,45649,79,77,46669,584,61,61,61,77,46669,75,46667,586,61,61,61,75,46667,81,46673,46673,46673,46673,46673,81,46673,73,46665,590,61,61,61,73,46665,71,46663,594,61,596,61,61,61,71,61,71,46663,46161,61,79,79,79,61,79,79,79,79,46669,79,79,46669,46667,79,79,46667,46673,46673,46673,46673,46665,79,79,46665,46663,79,79,46663,46669,61,61,46669,46667,61,61,46667,46673,46673,46673,46673,46673,46673,46665,600,61,61,61,46665,46663,602,61,61,61,46663,46667,604,46669,46667,46673,46673,46673,46673,46665,44607,46669,46665,46663,606,46669,46663,46673,46673,46673,46673,46665,608,46667,46665,46663,41,46667,46663,46673,612,46673,46673,46673,46673,46673,46673,46673,46673,46663,614,46663,46665]
def row309 : List ℕ := [72775,51,73287,57,73799,43,72775,72775,79,41,79,41,41,76877,41,76875,81,74817,81,74817,73,74815,73,74815,74815,74815,61,0,61,0,0,72775]
def row310 : List ℕ := [71,72775,51,77387,77389]
def row311 : List ℕ := [51,72775,81,75841,75841,81,73,75839,75839,73,75841,72775,75839,72775,77905,72775,76369,73287,77901,72775,110673,72775,72775,72775,109137,72775,73799,72775,77899,72775,72775,79,41,79,41,72775,41,41,77901,41,77899,75839,75839,61,0,61,51]
def row312 : List ℕ := [72777,72777,297873489,77,63,72775,71,72775,71,75,71,72775,71,51,71,75,76875,75,43,72775,72775,314646609,77,63,76875,41,41,41,41,41,76875,63,314645585,0,0,0,72775,0,76875]
def row313 : List ℕ := [81,37953,37953,81,73,37951,37951,73,71,41,71,41,98,0,41,71,38475,51,100,37967,38987,41,41,37965,37963,53,37951,37963,37951,37951,61,102,61]
def row314 : List ℕ := [72775,0,37967,51,38987,38987,38989]
def row315 : List ℕ := [21,21]
def row316 : List ℕ := [77,75]
def row317 : List ℕ := [81,630,51,38465,38465,81,38465,81,73,38463,38463,73,71,41,41,71,37963,51,38477,38477,38475,38475,38481,75,37457,75,41,38477,40529,38475,39505,38475,38463,38475,38463,38463,61,632,61,51]
def row318 : List ℕ := [75,37963,75,79,75,37963,75,53,75,72777,72777,41,41,297834065,77,79,37967,79,51,37967,37963,63,37967,126,37967,297833553,297833553,63,63,41,41,155263057,77,63,37963,297833543,297833543,63,297833553,132,0,37949,37949,0,37963]
def row319 : List ℕ := [77,37965,77,79,77,37951,37951,72775,41,72775,41,72775,297836113,75,79,37967,79,51,37967,37965,41,37967,188,37967,297835601,297835601,37951,37951,41,41,77,37965,77,41,163651153,75,297835593,297835593,41,37965,37951,297835601,204,41,39997,39997,202,37965]
def row320 : List ℕ := [81,76865,76865,81,73,76863,76863,73,71,0,0,71,79947,51,79435,31,78923,33,76863,78923,79,102,79,0,76863,76863]
def row321 : List ℕ := [51,51,79435,79435,79437]
def row322 : List ℕ := [78923,78923,78925,61,51]
def row323 : List ℕ := [71]
def row324 : List ℕ := [81,77889,77889,81,73,77887,77887,73,71,0,51,71,78923,51,79949,79949,79947,79947,79953,75,78417,75,112721,79947,111185,79947,77887,79947,79,646,79,51,0,0,77887,77887]
def row325 : List ℕ := [77,61,75]
def row326 : List ℕ := [297874503,75]
def row327 : List ℕ := [75,78923,75,61,75,78923,75,33,75,72777,72777,0,0,297875537,77,61,51,61,51,650,78923,63,63,323034193,323034193,63,63,323035217,77,63,78923,297874503,297874503,132,0,652,78923,63,323034193]
def row328 : List ℕ := [75,61,77]
def row329 : List ℕ := [72775]
def row330 : List ℕ := [77,78925,77,61,77,76863,76863,72775,72775,297908305,75,61,51,61,51,656,78925,658,0,457251921,457251921,76863,76863,77,78925,77,31,457252433,75,297907273,297907273,0,78925,204,0,0,78925,76863,457251921]
def row331 : List ℕ := [658,51,0,51,1,0,71,0,77,0,75,0,72775]
def row332 : List ℕ := [61,0,61,51,0,77,0,75,0,0,37967]
def row333 : List ℕ := [81,72785,72785,72785,72785,72785,81,72785,73,72777,63,63,63,63,73,72777,71,72775,618,620,622,51,71,72775,73297,75,75,75,75,75,77,75,75,75,72785,72785,72785,72785,72777,72777,77,77,72777,72777,72775,624,77,77,77,72775,73809,77,75,72785,72785,72785,72785,72777,63,75,75,75,72777,72775,72775,75,75,72775,72775,79,37967,626,628,79,37967,634,51,77,636,77,77,77,77,75,638,75,75,75,75,72785,72785,72785,72785,72777,63,37967,72777,72775,41,37967,72775,37967,544,37967,604,72785,63,72785,72785,72785,72785,72785,72785,72785,72785,72775,63,72775,72777,61,51,640,642,61,644,648,51,77,654,77,77,77,77,75,660,75,75,75,75,72785,72785,72785,72785,72777,63,63,72777,72775,662,664,72775]
def row334 : List ℕ := [71,72775,71,75,71,72775,71,51,71,314646609,77,75,76875,75,43,72775,72775,63,76875,72777,72777,297873489,77,63,72775,41,41,41,76875,41,41,63,314645585,0,76875,0,0,0,72775]
def row335 : List ℕ := [81,42051,42051,81,73,42047,42047,73,38471,43,38983,59,41,44109,37959,53,42047,37959,75,41,75,41,42047,42047,61,110,61]
def row336 : List ℕ := [44111,43,38983,38983,45133]
def row337 : List ℕ := [81,42563,42563,81,73,42559,42559,73,37959,43,44621,44621,38471,38471,0,44111,38481,71,37457,71,41,44621,44625,38471,43601,38471,42559,38471,75,41,75,41,42559,42559,61,632,61,43]
def row338 : List ℕ := [71,0,77]
def row339 : List ℕ := [71,37959,71,79,71,37959,71,53,71,41,41,314611281,77,79,44111,79,43,63,44111,128,44111,314610769,314610769,63,63,155267153,77,63,37959,41,41,63,314610769,37949,37949,676,37959]
def row340 : List ℕ := [73799,43,72775,72775,73287,57,72775,51,79,41,79,41,41,76875,41,76877,81,74817,81,74817,73,74815,73,74815,74815,74815,61,0,61,0,0,72775]
def row341 : List ℕ := [76875,43,73287,73287,77901]
def row342 : List ℕ := [81,74817,74817,81,73,75327,75327,73,72775,43,73799,73799,74817,76875,75327,76875,73809,71,72273,71,77389,76875,110161,73799,109137,73799,79,41,79,41,41,77389,75327,75327,61,0,61,43,76875,42,0,73799]
def row343 : List ℕ := [81,142403,142403,81,73,142399,142399,73,79943,43,79431,1,0,177229,78919,33,142399,78919,79,110,79,0,75,75,0,0,75,42,0,0,142399,142399]
def row344 : List ℕ := [43,43,79431,79431,177741,76875]
def row345 : List ℕ := [78919,78919,177229,61,43,0,44111]
def row346 : List ℕ := [178257,79943,79943,176721,81,143427,143427,81,73,143423,143423,73,78919,43,178253,178253,79943,79943,79953,71,78417,71,0,178253,143423,79943,79,0,79,43,75,0,75,43,143423,143423]
def row347 : List ℕ := [142399,142399,314751057,71,61,43,61,43,0,0,77,77,177229,77,61,725691473,725691473,142399,142399,77,177229,77,1,725691985,71,0,177229,524,0,177231,177231,676,177229,0,0,0,0,142399,725691473]
def row348 : List ℕ := [31,0,31,43]
def row349 : List ℕ := [61,0,61,43,0,71,0,75,42]
def row350 : List ℕ := [81,76881,76881,76881,76881,76881,81,76881,73,76873,63,63,63,63,73,76873,77393,71,71,71,71,71,77,71,71,71,76875,668,77,77,77,76875,76881,76881,76881,76881,76873,77,77,76873,77905,77,71,76881,76881,76881,76881,71,63,71,71,71,71,79,44111,670,672,79,44111,674,43,77,678,77,77,77,77,71,71,71,71,76875,41,44111,76875,76881,76881,76881,76881,76873,63,44111,76873,44111,546,44111,606,75,76875,680,682,75,76875,684,43,71,71,71,71,76881,76881,76881,76881,76873,63,76875,76873,76881,63,76881,76881,76881,76881,61,43,686,688,61,690,692,43,77,77,77,77,71,694,71,71,71,71,76875,696,698,76875,76881,76881,76881,76881,76873,63,63,76873]
def row351 : List ℕ := [81,40001,40001,81,40521,47,100,74831,41033,49,40009,41,40009,40009,77,37951,77,37951,37951,42059,71,71,41,41,71,98,41,0,41,40009,61,166,61]
def row352 : List ℕ := [74831,47,41033,41033,43083,109639]
def row353 : List ℕ := [107595,108619]
def row354 : List ℕ := [75,77]
def row355 : List ℕ := [81,706,47,40513,40513,81,40513,81,40009,47,42571,42571,40521,40521,40529,73,39505,73,42577,40521,41553,40521,40521,40521,77,38463,77,38463,38463,42571,71,41,71,41,41,40521,61,708,61,47]
def row356 : List ℕ := [448967751,0,75]
def row357 : List ℕ := [73,40009,73,79,73,40009,73,41,73,109639,41,109639,41,109639,440442449,75,79,74831,79,47,41,74831,186,74831,440441937,440441937,163686481,75,40009,440441937,37951,37951,37951,37951,41,41,41,40009,196,41,39997,39997,712,40009]
def row358 : List ℕ := [109639,47,110151,35,109639,109639,142411,109639,110663,57,109641,109641,79,41,79,41,41,142411,77,74815,77,74815,81,107585,81,107585,61,402,61,9,0,109639]
def row359 : List ℕ := [47,109639,143441,109639,110663,141905,81,108609,108609,81,110665,109639,108609,109639,110673,109639,109639,109639,109137,109639,110151,109639,143435,109639,109639,110665,110665,79,41,79,41,109639,41,41,143435,77,75839,77,75839,61,0,61,47]
def row360 : List ℕ := [0,142411]
def row361 : List ℕ := [109639]
def row362 : List ℕ := [440545361,73,71,109639,71,47,71,109639,71,75,71,75,142411,75,35,109639,109639,109639,142411,109639,583116369,73,41,109639,41,41,41,142411,63,109639,63,142411,0,9,720,109639,722,142411]
def row363 : List ℕ := [76863,76863]
def row364 : List ℕ := [81,109633,109633,81,112713,47,112201,3,111689,31,111689,111689,79,166,79,0,77,77,76863,76863,77,726,76863,0,76863,144459,71,402,71]
def row365 : List ℕ := [47,47,112201,112201,144971,74829]
def row366 : List ℕ := [111689,111689,144459,61,47]
def row367 : List ℕ := [81,110657,110657,81,111689,47,145483,145483,112713,112713,112721,73,111185,73,145489,112713,143953,112713,112713,112713,79,646,79,47,77,77887,77,77887,77887,145483,71,9,71,47]
def row368 : List ℕ := [61,73,75]
def row369 : List ℕ := [0,109639]
def row370 : List ℕ := [73,111689,73,61,73,111689,73,31,73,109639,109639,440514641,75,61,47,61,47,736,111689,738,0,457286737,457286737,457287761,75,111689,457286737,196,0,76863,76863,76863,76863,722,111689]
def row371 : List ℕ := [73,61,75]
def row372 : List ℕ := [440547409,73,61,47,61,47,742,144459,63,63,75,75,144459,75,61,591504465,591504465,75,144459,75,3,591504977,73,448967751,448967751,42,0,712,144459,63,0,63,63,63,144459]
def row373 : List ℕ := [47,402,1,47,0,73,722,0,71,720,75,0,109639]
def row374 : List ℕ := [61,0,61,47,0,75,0,73,0,0,74831]
def row375 : List ℕ := [81,107601,107601,107601,107601,107601,81,107601,108113,73,73,73,73,73,75,73,73,73,107601,107601,107601,107601,109639,109639,75,75,109639,109639,108625,75,73,107601,73,107601,107601,107601,107601,79,74831,702,704,79,74831,710,47,75,714,75,75,75,75,73,73,73,73,74829,63,74831,74829,107601,107601,107601,107601,109639,41,74831,109639,74831,548,74831,608,77,74829,63,63,77,74829,63,63,75,63,75,75,75,75,73,73,73,73,107601,107601,107601,107601,109639,63,74829,109639,71,109639,716,9,71,109639,718,47,109639,724,73,109639,73,73,107601,107601,107601,107601,61,47,728,730,61,732,734,47,75,740,75,75,75,75,73,744,73,73,73,73,74829,63,63,74829,107601,107601,107601,107601,109639,746,748,109639]
def row376 : List ℕ := [73287,57,73799,43,72775,72775,72775,51,79,41,79,41,41,76877,41,76875,81,74817,81,74817,73,74815,73,74815,74815,74815,61,0,61,0,0,72775]
def row377 : List ℕ := [110663,57,109641,109641,110151,35,109639,109639,142411,109639,109639,47,79,41,79,41,41,142411,77,74815,77,74815,81,107585,81,107585,61,402,61,9,0,109639]
def row378 : List ℕ := [108097,107599]
def row379 : List ℕ := [107577,756,45,107577,109649,109649,73,109641,73,109641,110161,142407,142407,142407,107595,142407,110673,107595,72745,109641,107599,72745,107599,107577,72745,107595,109641,314680397,107597,74815,107597,74815,0,109641,142397,0,142397,107577,0,142407]
def row380 : List ℕ := [112711,57,112199,112199,1,111687,31,79,41,79,41,77,0,77,1,81,142401,81,142401,73,402,73,1,0,142401]
def row381 : List ℕ := [75,177227,75,61,75,448968785,71,61,57,61,57,177227,177227,75,177227,75,1,725724753,71,41,41,177231,177231,41,177227,0,57,448967761,448967761,0,57,0,448967761]
def row382 : List ℕ := [57,0,33,57]
def row383 : List ℕ := [57,402,3,57,0,76877]
def row384 : List ℕ := [110161,71,71,71,71,71,75,71,71,71,109649,109649,109649,109649,109641,75,75,109641,110673,75,71,109649,109649,109649,109649,71,71,71,71,79,76879,41,57,79,76879,57,57,75,41,75,75,75,75,71,71,71,71,76877,41,76879,76877,109649,109649,109649,109649,109641,41,76879,109641,76879,41,76879,41,77,76877,752,57,77,76877,57,57,75,75,75,75,71,71,71,71,109649,109649,109649,109649,109641,74815,76877,109641,81,109649,109649,109649,81,109649,109649,109649,73,109641,754,57,73,109641,57,57,109649,758,109649,109649,109649,109649,61,57,760,57,61,57,57,57,75,75,75,75,71,762,71,71,71,71,76877,764,1,76877,109649,109649,109649,109649,109641,766,1,109641]
def row385 : List ℕ := [142397,0,188786769]
def row386 : List ℕ := [0,108101]
def row387 : List ℕ := [142397,69,142397,19,0,39999]
def row388 : List ℕ := [42577,45,107599,107599,107599,45,42065,42057,770,107599,43089,107599,43089,43089,69,42065,42065,107597,39999,107597,39999,42057,39999,107595,208,107595,19,142407,772,142407,19,0,19,142397,554,142397,19,774,42057]
def row389 : List ℕ := [172009041,42065,172009041,107599,107599,172008017,40511,40511,0,45,0,45]
def row390 : List ℕ := [73,108625]
def row391 : List ℕ := [0,583052871,142929]
def row392 : List ℕ := [107599]
def row393 : List ℕ := [0,73,144977,107597]
def row394 : List ℕ := [42577,81,142397,45,40511]
def row395 : List ℕ := [107599,41553,42065,45,107599,45,107599,107599,778,107599,42569,42569,42577,210,107599,107599,42,42577,42577,42577,81,41553,81,81,42577,42577,42577,107597,40511,107597,40511,42569,40511,107595,780,107595,45,142407,782,142407,45,784,45,142397,786,142397,45,788,42569]
def row396 : List ℕ := [73,73,0,45,0,45,44095,44095,172013649,107599,49,49]
def row397 : List ℕ := [81,42065,42065,107599,81,42065,42577,73,73,107599,107599,42065,107599,260,107599,440443981,63,107599,107599,107599,440443981,440443979,107599,107599,440443979,583052359,107599,107599,583052359,107599,792,107599,107599,107599,107599,107597,440443981,63,107597,440443981,63,440443981,63,440443981,63,440443979,63,440443981,440443979,583052359,63,440443981,583052359,440443979,266,440443979,49,440443979,264,440443979,19,583052359,72745,440443979,583052359,583052359,0,583052359,49,583052359,268,583052359,19,49,276,278,280,282,49,19,270,272,19,440443981,63,63,440443981,440443979,0,286,440443979,583052359,288,290,583052359]
def row398 : List ℕ := [440479823,440479823,444641355,43073,42]
def row399 : List ℕ := [107595,42,0,583054407]
def row400 : List ℕ := [297869893,41537]
def row401 : List ℕ := [107599,800,72773,163686481]
def row402 : List ℕ := [107599,0,583120455]
def row403 : List ℕ := [72745,208,72745,45,73,40009,40009,73,142407,72745,142407,72745,796,72745,72745,142407,40529,107595,107595,107595,107599,107595,107599,210,107599,40009,72745,107599,798,107599,41041,107599,802,107595,40009,40009,72745,107595,40017,40017,107597,37951,107597,37951,37951,107595,40009,440439885,142397,218,142397,72745,107595,804,216,40009]
def row404 : List ℕ := [107599,180498001]
def row405 : List ℕ := [107579,772,107579,45,73,44105,44105,73,44625,142407,142407,142407,107599,142407,107599,44105,72745,107599,45137,107599,808,142407,44105,142407,44113,44113,107597,42047,107597,42047,44105,440446029,107595,72745,107595,107579,142397,354,142397,107579,0,44105]
def row406 : List ℕ := [45,109125,109125,45,81,109125,81,81,45,45,45,45,45,45,45,109125,45,109125,109125,42,109125,109125,0,6,45,45,45,45,17]
def row407 : List ℕ := [73,73,0,45,0,45,44095,44095,49,49,172013649,107599]
def row408 : List ℕ := [107599,0,188888657]
def row409 : List ℕ := [73,73,0,45,0,45,44095,44095,440546383,3,591443537,142397,0,440546383,44095,440546383,0,440546383,2388727477319,2388727477319,44095]
def row410 : List ℕ := [812,552,45,554,418,434,420,45,73,454,556,46153,46153,73,46153,73,107597,44095,44095,107597,107595,218,404,107595,142407,354,480,142407,46673,142397,107599,107599,107599,142397,770,107599,814,107599,46153,46153,46153,44095,107599,562,107599,583054407,583054407,47185,107599,816,566,818,570,46153,46153,46153,572,574,46161,46161,46153,440448077]
def row411 : List ℕ := [440579151,440579151,142397,142397,725723215,142405,107553,107553]
def row412 : List ℕ := [107599,45649,142397,0,142397,45,73,588,142397,46665,46665,73,46665,73,107597,44607,142397,107597,107595,0,142397,107595,142407,822,142397,0,142397,142407,142397,142407,46161,142397,107599,142397,107599,107599,107599,46665,0,142397,610,142397,46665,46665,46665,0,142397,46673,46673,46665,440448589]
def row413 : List ℕ := [45,450996305]
def row414 : List ℕ := [0,107595,42577,65]
def row415 : List ℕ := [142407,107585,72773]
def row416 : List ℕ := [110145,107597]
def row417 : List ℕ := [0,145489,65]
def row418 : List ℕ := [142397,457287761]
def row419 : List ℕ := [142397,65,142397,0,0,72767]
def row420 : List ℕ := [108113,45,107595,107595,107595,45,107595,826,108625,107595,108625,108625,65,107601,107601,107599,208,107599,828,802,107595,72773,72773,264,107593,107597,72767,107597,72767,107593,72767,142407,756,142407,0,830,0,142397,832,142397,834,836,107595,0,0,838,107593]
def row421 : List ℕ := [107585,107585,19,45,45,17,0,45]
def row422 : List ℕ := [142407,73285]
def row423 : List ℕ := [45,0,583185479,73279]
def row424 : List ℕ := [107595,107089,108113,81,81,107089,142407,842,45,0,45,142407,45,142407,107601,45,107595,45,107595,107595,108105,108105,108113,108113,107599,19,107599,45,73285,73285,19,108105,107597,73279,107597,73279,108105,73279,844,45,142397,0,142397,45,0,45,846,108105]
def row425 : List ℕ := [110161,142407,142407,142407,107595,142407,110673,107595,107577,756,45,107577,73,109641,73,109641,109649,109649,107599,72745,107599,107577,72745,107595,72745,109641,107597,74815,107597,74815,109641,314680397,142397,0,142397,107577,0,142407,0,109641]
def row426 : List ℕ := [0,42551,107589,107589,42]
def row427 : List ℕ := [0,0,42577,108101]
def row428 : List ℕ := [107599,42551]
def row429 : List ℕ := [0,107599,0,107597,0,107595]
def row430 : List ℕ := [0,142407,145489,55]
def row431 : List ℕ := [142397,725757521,440579151,107585]
def row432 : List ℕ := [109125]
def row433 : List ℕ := [0,19]
def row434 : List ℕ := [142407,142417,864,866,0,42,109125]
def row435 : List ℕ := [142407,110149]
def row436 : List ℕ := [142397,55,142417,142397,0,42,440546383,0,107583]
def row437 : List ℕ := [143441,45,142407,142407,142407,45,142929,142407,142929,142929,55,142417,142417,107599,107599,772,772,107599,852,854,856,808,142407,0,784,268,142409,107597,107583,107597,107583,107583,107583,142409,107583,107595,756,107595,0,142407,107585,830,844,142397,858,142397,860,862,142407,868,870,872,142409]
def row438 : List ℕ := [108609,108609,19,45,45,17,0,45]
def row439 : List ℕ := [143441,45,108607,0,440546379]
def row440 : List ℕ := [45,142417,142407,141905,143441,81,81,141905,142407,45,142407,142407,143433,142407,143441,143441,107599,19,107599,45,19,45,19,143433,107597,108607,107597,108607,108607,108607,143433,108607,107595,876,0,45,107595,107595,45,45,0,45,142397,0,142397,45,45,0,878,143433]
def row441 : List ℕ := [3,3,0,45]
def row442 : List ℕ := [45,109125,19,45,45,142397,882,142397,45,142397,142397,143421,109125,107553,107553,864,45]
def row443 : List ℕ := [109119,110143,0,45]
def row444 : List ℕ := [109119,109123,142397,142397,886,142397,109119,142397,142397,143421,109123,45,19,19,109119,866,45]
def row445 : List ℕ := [142397,142397,142397,142397,143421,109121,45,19,19,45,107553,107553,0,45]
def row446 : List ℕ := [142397,142397,143421,29,19,45,107553,107553]
def row447 : List ℕ := [142397,144969,142397,591542353,882,142397,19,142397,142397,886,142397,109119,142397,142397,142397,142397,142397,142397,109119,3,42,45]
def row448 : List ℕ := [142397,144977,142397,145489,143953,81,143953,81,81,145489,143945,145489,107599,884,142397,19,142397,107599,142397,107599,107597,888,142397,109119,142397,107597,142397,107597,107595,890,142397,0,142397,107595,142397,107595,142407,892,142397,0,142397,142407,142397,142407,142397,45,142397,142397,894,142397,143945,143945,143945,143953,143953,109125,109125,19,143945,143945,109119,868,45]
def row449 : List ℕ := [81,593639505,109631]
def row450 : List ℕ := [0,42577,110149]
def row451 : List ℕ := [0,109631,0,109631,109631,109635,0,109631]
def row452 : List ℕ := [145489,45,142397,45,142397,45,144465,144457,144977,142397,144977,144977,898,144465,144465,107599,554,107599,900,816,0,270,144457,107597,107597,109631,109631,107597,902,109631,274,109631,109631,144457,109631,107595,832,107595,0,0,0,142407,858,142407]
def row453 : List ℕ := [110149,109637,42577]
def row454 : List ℕ := [45,110149,0,591443025]
def row455 : List ℕ := [144977,0,107599,0,109637,107599]
def row456 : List ℕ := [142397,143953,142397,144465,144465,142397,144465,107597,110143,142397,107597,107595,0,142397,107595,142407,210,142397,142407,142397,142397,142397,45,142397,144969,144977,144977,107599,906,107599,142397,908,142397,110149,110149,910,144969,144969,110143,870]
def row457 : List ℕ := [591542353,144465,591542353,142397,142397,591540817,19,45,110655,0,110655,110655,110655,110655,0,45]
def row458 : List ℕ := [145489,81,145489,142397,142397,110655]
def row459 : List ℕ := [583186503,142929,107599]
def row460 : List ℕ := [142397,143953,144465,45,142397,45,142397,45,914,916,145481,145481,145489,145489,145489,145489,81,143953,81,81,145489,145489,145489,107599,19,107599,45,19,145481,107597,110655,107597,110655,110655,110655,145481,110655,107595,780,107595,45,0,45,142407,918,142407,45]
def row461 : List ℕ := [142397,591542353,142397,144969,882,142397,19,142397,142397,886,142397,109119,142397,142397,142397,142397,142397,142397,109119,3,42,45]
def row462 : List ℕ := [142397,591540817,591542353,144465,591542353,142397,19,45,110655,110655,110655,110655,110655,0,0,45]
def row463 : List ℕ := [142397,142397,145489,81,145489,110655]
def row464 : List ℕ := [440579149,440546379]
def row465 : List ℕ := [45119,109635]
def row466 : List ℕ := [144465,0,3,47177,591504461,0,44095,930]
def row467 : List ℕ := [42577,41553,46153,3,3,440546383,73,73,107597,107597]
def row468 : List ℕ := [73,73,0,45,0,45,44095,44095,591443537,142397,440546383,3,0,440546383,44095,440546383,0,440546383,2388727477319,2388727477319,44095]
def row469 : List ℕ := [46153,73,6,0,440546383,142397,3,440448077]
def row470 : List ℕ := [0,142397,69,142397,19,39999]
def row471 : List ℕ := [109635,45119]
def row472 : List ℕ := [78409,591504461,78409,3,109635,79433,79433,79433,79433,3,0,942,3,0,3]
def row473 : List ℕ := [112713,591504461,0,76863]
def row474 : List ℕ := [0,583185479,45,73279]
def row475 : List ℕ := [178249,591504461,0,142399,440546379]
def row476 : List ℕ := [81,144465,144465,142397,81,144465,145489,73,73,922,142397,144465,142397,924,926,591504461,63,63,63,142397,591504461,440546379,0,142397,440546379,583185479,928,142397,583185479,440546383,454,932,440546383,934,3,440546383,936,938,440546383,610,142397,440546383,940,440546383,788,591504461,63,440546383,591504461,440546379,216,440546383,440546379,583185479,0,440546383,583185479,107597,107597,63,591504461,63,107597,591504461,944,63,591504461,63,591504461,63,440546379,63,591504461,440546379,583185479,63,591504461,583185479,440546379,946,440546379,3,440546379,838,440546379,948,583185479,0,440546379,583185479,583185479,950,583185479,3,583185479,872,583185479,878]
def row477 : List ℕ := [109633]
def row478 : List ℕ := [45,832,954,45,73,111689,111689,73,142407,0,0,142407,112721,107595,107595,107595,142397,107595,0,111689,0,0,112209,142397,836,107595,111689,111689,111697,111697,107599,218,107599,0,0,111689,107597,76863,107597,76863,76863,107595,111689,440480845]
def row479 : List ℕ := [81,81,144465,145489,142397,440546379,440546379,0,284,3,0,440546379,107597,107597,77375,107597,3]
def row480 : List ℕ := [107595,583120455]
def row481 : List ℕ := [45,0,284,73]
def row482 : List ℕ := [583120455,107599]
def row483 : List ℕ := [0,107599,284,49]
def row484 : List ℕ := [107595,111185,142397,111697,142397,832,142397,45,73,958,142397,112201,112201,73,112201,73,107597,77375,142397,107597,142407,0,142397,142407,107595,142397,107595,107595,142397,112201,960,142397,583120455,583120455,112209,112209,107599,962,107599,142397,964,107595,966,112201,112201,440481357]
def row485 : List ℕ := [0,0,587314759,142401,0,0,42]
def row486 : List ℕ := [45,858,42,45,73,177225,177225,73,178257,142407,142407,142407,142397,142407,928,177225,0,960,177745,142397,862,142407,177225,142407,177233,177233,107599,354,107599,0,572,0,142407,440579151,288,177225,107597,142399,107597,142399,142399,142407,177225,440579149,107595,107595,0,0,107595,970,0,0,0,142407]
def row487 : List ℕ := [81,81,144465,145489,142397,583185479,0,3,0,142397,107597,107597]
def row488 : List ℕ := [0,3,142397,142397,587248711,142917,107553,107553]
def row489 : List ℕ := [0,73,0,3]
def row490 : List ℕ := [0,107599,0,0,49]
def row491 : List ℕ := [142407,176721,142397,177233,142397,0,142397,45,73,974,142397,177737,177737,73,177737,73,107597,142911,142397,107597,107595,0,142397,107595,142407,142397,142407,142407,142397,177737,0,142397,177745,177745,107599,976,978,142397,107599,107599,142397,142397,784,142397,980,177737,177737,440579661]
def row492 : List ℕ := [81,81,81,107599,776,107599,790,73,794,73,73,73,73,107597,63,107599,107597,107595,806,107599,107595,142407,810,107599,142407,107599,820,107599,824,107597,63,107597,63,73,73,73,107597,73,73,107595,63,107597,107595,142407,63,107597,142407,107595,840,107595,848,73,73,73,73,142407,850,107595,142407,142407,874,142407,880,142407,73,142407,73,896,904,912,920,73,952,73,73,73,73,107597,63,63,107597,107595,956,968,107595,142407,972,982,142407]
def row493 : List ℕ := [44615,35,44103,49,45127,59,44105,44105,77,42047,77,42047,75,41,75,41,81,107589,81,107589,61,300,61]
def row494 : List ℕ := [142415,35,45127,45129,45127]
def row495 : List ℕ := [77,0,75]
def row496 : List ℕ := [44103,35,44615,44615,44617,44617,142415,107589,578,142415,44625,44615,43601,44615,42577,71,41553,71,44617,44617,77,42559,77,42559,75,41,75,35,81,107589,81,107589,61,990,61,35]
def row497 : List ℕ := [73,44105,73,79,73,44105,73,59,73,583052881,71,79,142415,79,35,142415,44105,41,142415,180498001,71,44105,583052369,42047,42047,142411,142411,41,44105,583052369,583052369,344,59]
def row498 : List ℕ := [71,44103,71,79,71,583050833,73,79,142415,79,35,142415,44103,63,142415,128,142415,71,44103,71,49,172109905,73,63,44103,41,41,44103,583050315,583050321,583050321,308,44103]
def row499 : List ℕ := [110151,35,109639,109639,142411,109639,109639,47,110663,57,109641,109641,79,41,79,41,41,142411,77,74815,77,74815,81,107585,81,107585,61,402,61,9,0,109639]
def row500 : List ℕ := [108113,71,71,107089,81,107585,107585,81,109639,35,110151,110151,142411,110151,110153,110153,107585,142411,110161,73,110151,110153,109137,110151,110151,110153,110153,79,41,79,35,77,75327,77,75327,75327,142411,61,0,61,35,142411,42,720,110151]
def row501 : List ℕ := [71,109639,71,75,71,583116369,73,75,142411,75,35,109639,109639,109639,142411,109639,71,109639,71,47,440545361,73,41,41,41,142411,41,109639,63,142411,63,109639,722,142411,0,9,720,109639]
def row502 : List ℕ := [142399,142399]
def row503 : List ℕ := [77]
def row504 : List ℕ := [0,51]
def row505 : List ℕ := [79,0,77,0,75]
def row506 : List ℕ := [178247,35,177223,3,177735,1,177225,177225,79,300,79,0,0,0,77,77,142399,142399,77,1004,142399,1006,142399,177223,75,75,1008,402,75,42,0,386,0,177225,81,1010,81]
def row507 : List ℕ := [35,35,177735,177737,177735,142413,0,142411]
def row508 : List ℕ := [177223,177225,177223,61,35,0,142415]
def row509 : List ℕ := [142407,143431]
def row510 : List ℕ := [177223,35,178247,178247,178249,178249,178257,178247,176721,178247,145489,71,143953,71,178249,178249,79,0,79,35,77,143423,77,143423,143423,178247,75,9,75,35,9,178249,81,1018,0,35,81,81,35,35]
def row511 : List ℕ := [142411]
def row512 : List ℕ := [111165,1]
def row513 : List ℕ := [111175,112189]
def row514 : List ℕ := [73,177225,73,61,73,177225,73,1,73,583186513,71,61,35,61,35,646,1022,725757521,71,177225,583185489,344,0,524,0,177231,177231,308,177225,142399,142399,142399,142399,142411,142411,1024,142411,1026,0,1022,1022,177225,583185489,583185489]
def row515 : List ℕ := [31,402,31,35,71,0,646,722]
def row516 : List ℕ := [61,402,61,35,0,71,1022,75,42,112199]
def row517 : List ℕ := [143441,73,71,71,71,71,71,71,73,71,142417,142417,142417,142417,142929,71,71,142417,73,142417,142417,142417,142417,79,142415,986,988,79,142415,992,35,71,994,71,71,71,71,73,996,73,73,73,73,142413,63,142415,142413,142411,41,142415,142411,142417,142417,142417,142417,142415,580,142415,614,77,142413,63,63,77,142413,63,63,71,63,71,71,71,71,73,73,73,73,142411,63,142413,142411,142417,142417,142417,142417,75,142411,998,9,75,142411,1000,35,71,71,71,142411,71,71,73,1002,73,73,73,73,142417,142417,142417,142417,81,142417,142417,142417,81,142417,142417,142417,61,35,1012,1014,61,1016,1020,35,71,1028,71,71,71,71,73,73,73,73,142413,63,63,142413,142411,1030,1032,142411,142417,142417,142417,142417]
def row518 : List ℕ := [81,76865,76865,81,73,76863,76863,73,71,0,0,71,78923,33,76863,78923,79947,51,79435,31,79,102,79,0,76863,76863]
def row519 : List ℕ := [75,78923,33,79949,31]
def row520 : List ℕ := [33,78923,81,76865,76865,81,73,77375,77375,73,71,0,33,71,78923,0,112209,78923,111185,79947,33,78923,73809,78923,72273,79435,79437,78923,79,116,79,33,536,78923,77375,77375]
def row521 : List ℕ := [81,142403,142403,81,73,142399,142399,73,78919,33,142399,78919,79943,43,79431,1,0,177229,79,110,79,0,75,75,0,0,75,42,0,0,142399,142399]
def row522 : List ℕ := [71,78919,33,178253,1,78923]
def row523 : List ℕ := [33,78919,177745,78919,79943,176721,77905,78919,79431,76369,75,0,33,75,81,142915,142915,81,73,142911,142911,73,33,78919,177741,78919,0,177741,79,0,79,33,142911,142911]
def row524 : List ℕ := [75,78923,79947,75,75,33,77,31,650]
def row525 : List ℕ := [71,78919,79943,71,71,33,77,1,78923]
def row526 : List ℕ := [323034193,323034193,63,63,323035217,77,63,78923,297874503,297874503,75,78923,75,61,75,78923,75,33,75,72777,72777,0,0,61,51,61,51,650,78923,297875537,77,63,63,652,78923,132,0,63,323034193]
def row527 : List ℕ := [75,102,0,75,81,44099,81,44099,42,116,44099,81,73,44095,73,44095,42,140,44095,73,71,110,0,71,46669,33,44095,46159,47181,53,46157,37949,44095,44095,46157,142,132,46157,44099,46157,44095,46157,44095,44095]
def row528 : List ℕ := [78929,0,78921,0,46159,33,47181,47181,0,37949]
def row529 : List ℕ := [75,0,33,75,81,44611,44611,81,73,44607,44607,73,71,0,33,71,46157,33,33,46159,46669,46669,46673,77,45649,77,46669,38461,44607,44607,38481,46669,37457,46669,0,46669,44611,46669,44607,46669,44607,44607]
def row530 : List ℕ := [78919,0,33,102,33,41,75,236,652]
def row531 : List ℕ := [75,78923,1036,1038,1040,33,75,78923,81,78929,78929,78929,78929,78929,81,78929,73,78921,63,63,63,63,73,78921,71,78919,1042,1044,1046,33,71,78919,79953,77,77,77,77,77,61,77,77,77,78923,1048,61,78923,78929,78929,78929,78929,78921,63,63,63,61,78921,78919,1050,61,78919,79441,61,77,78923,1052,77,77,77,78923,78929,78929,78929,78929,78929,78929,78921,63,77,77,77,78921,78919,77,77,78919,79,46159,1054,1056,79,46159,1058,33,46159,502,46159,61,77,77,77,77,78923,1060,46159,78923,78929,78929,78929,78929,78921,63,46159,78921,78919,366,46159,78919,78929,78929,78929,78929,78921,63,78923,78921,78919,764,78923,78919,78929,63,78929,78929,78929,78929,78929,78929,78929,78929,78919,63,78919,78921]
def row532 : List ℕ := [81,77377,77377,81,73,76863,76863,73,71,1,31,71,79435,61,77377,79435,76863,79435,79435,111697,78411,112721,79435,61,61,78925,72273,78923,73809,79435,78925,79435,78925,76863,79,240,79,31,0,78925,76863,76863]
def row533 : List ℕ := [61,45131]
def row534 : List ℕ := [81,142403,142403,81,73,142399,142399,73,79431,61,142403,79431,142399,79431,79431,177233,78407,178257,79431,61,76369,78919,77905,79431,177229,79431,79,368,79,1,79431,1066,0,177229,75,75,1,1,75,42,1,1,1,79431,142399,142399]
def row535 : List ℕ := [1,75]
def row536 : List ℕ := [37457,46157,46157,38481,75,240,0,75,81,44099,81,44099,42,116,44099,81,73,44095,44095,73,71,368,0,71,46669,61,46671,61,46157,46157,1070,46671,44099,46671,44095,46671,46671,1,77,46161,77,47185,44095,61,44095,44095]
def row537 : List ℕ := [79433,79433,325097041,77,79,37949,79,46671,37949,46671,63,46671,79,37949,79,46671,79,77,155267665,0,37949,325096529,325096529,63,37949,0,37949,37949,37949,37949,53,63,37949,63,325096529]
def row538 : List ℕ := [79431,0,242,79,61,240,61,41,75,39997]
def row539 : List ℕ := [77,78417,77,61,78929,77,75,79435,1064,61,61,61,75,79435,81,79441,79441,79441,79441,79441,81,79441,73,79433,63,61,61,61,73,79433,71,79431,1068,61,61,61,71,79431,77,77,61,77,77,77,77,79435,61,61,79435,79441,79441,79441,79441,79433,63,61,61,61,79433,79431,61,61,79431,79435,77,77,79435,79441,79441,79441,79441,79433,79433,77,77,79433,79433,79431,77,77,79431,79,46671,1072,61,79,46671,61,61,46671,61,46671,61,77,1074,77,77,77,77,79435,1076,46671,79435,79441,79441,79441,79441,79433,63,46671,79433,79431,370,46671,79431,79441,79441,79441,79441,79433,63,79435,79433,79431,1,79435,79431,79441,63,79441,79441,79441,79441,79441,79441,79441,79441,79431,63,79431,79433]
def row540 : List ℕ := [81,109633,109633,81,111689,31,111689,111689,112713,47,112201,3,79,166,79,0,77,77,76863,76863,77,726,76863,0,76863,144459,71,402,71]
def row541 : List ℕ := [73,111689,31,145483,3,78925]
def row542 : List ℕ := [31,111689,108625,111689,112201,107089,77,76863,76863,77,81,110145,110145,81,71,1,31,71,111689,111689,144977,111689,143953,112713,31,111689,144971,111689,79,116,79,31,76863,144971]
def row543 : List ℕ := [111687,31,112711,57,112199,112199,1,79,41,79,41,77,0,77,1,81,142401,81,142401,73,402,73,1,0,142401]
def row544 : List ℕ := [31,111687,81,142913,142913,81,73,0,31,73,142913,111687,0,111687,177745,111687,176721,112711,31,111687,110673,111687,109137,112199,177739,111687,79,41,79,31,111687,41,77,0,77,31,0,142913]
def row545 : List ℕ := [75,78923,79947,75,75,33,77,31,656]
def row546 : List ℕ := [75,61,73]
def row547 : List ℕ := [0,73,111689,112713,73,73,31,75,3,1092,78925]
def row548 : List ℕ := [0,72775]
def row549 : List ℕ := [457356881,61,725726289,725726289,646,111687,71,111687,71,75,71,111687,71,31,71,75,177227,75,1,177227,111687,725726801,61,725726289,725726289,738,177227,111687,725693519,41,41,0,111687,1096,177227,0,725726289]
def row550 : List ℕ := [61,725726289,112711,176715,75,75,71,71,459454033,61,457356881,457356881,0,177739,61,61,41,31,0,177739,0,457356881]
def row551 : List ℕ := [61,75,73]
def row552 : List ℕ := [457286737,457286737,457287761,75,111689,457286737,73,111689,73,61,73,111689,73,31,73,109639,109639,61,47,61,47,1102,111689,440514641,75,738,0,196,0,76863,76863,76863,76863,722,111689]
def row553 : List ℕ := [81,44097,81,44097,42,224,44097,81,73,166,116,73,71,41,71,41,98,226,41,71,46667,31,47179,41,46155,39997,41,41,46155,228,44097,46155,196,46155,77,102,77,0,204,46155,218,44097]
def row554 : List ℕ := [111697,0,111687,0,78927,31,47179,47179,0,39997]
def row555 : List ℕ := [81,44609,44609,81,73,0,31,73,71,41,31,71,46155,31,31,78927,46667,46667,46673,75,45649,75,46667,40509,41,31,40529,46667,39505,46667,44609,46667,0,46667,77,0,77,31,0,46667,0,44609]
def row556 : List ℕ := [0,31,166,31,49]
def row557 : List ℕ := [81,76865,76865,81,73,76863,76863,73,71,0,0,71,79435,31,79947,51,78923,33,76863,78923,79,102,79,0,76863,76863]
def row558 : List ℕ := [78925,31,79947,79947,33]
def row559 : List ℕ := [81,77377,77377,81,73,76863,76863,73,71,1,31,71,78923,31,79435,79435,78925,76863,79441,75,78417,75,31,78925,73297,79435,72273,79435,76863,79435,79,116,79,31,0,78925,76863,76863]
def row560 : List ℕ := [457251921,457251921,76863,76863,457252433,75,77,78925,77,31,297907273,297907273,0,78925,77,78925,77,61,77,76863,76863,72775,72775,61,51,61,51,656,78925,297908305,75,1096,0,0,78925,204,0,76863,457251921]
def row561 : List ℕ := [0,31,0,31,43]
def row562 : List ℕ := [457287761,142397]
def row563 : List ℕ := [111697,111697,45,832,954,45,73,111689,111689,73,142407,0,0,142407,0,111689,112721,107595,107595,107595,142397,107595,0,0,1124,107595,111689,111689,112209,142397,0,111689,107599,218,107599,0,111689,440480845,107597,76863,107597,76863,76863,107595]
def row564 : List ℕ := [81,111697,111697,111697,111697,111697,81,111697,73,111689,1080,1082,1084,31,73,111689,71,111687,1086,1,1088,31,71,111687,112721,75,75,75,75,75,61,75,75,75,78925,1090,61,78925,111697,111697,111697,111697,111689,1094,61,111689,111687,1098,1,1100,61,111687,112209,61,75,111697,111697,111697,111697,111697,111697,111689,1104,75,75,75,111689,111687,75,75,111687,79,78927,1106,1108,79,78927,1110,31,78927,504,78927,61,75,75,75,75,78925,154,78927,78925,111697,111697,111697,111697,111689,1112,78927,111689,111687,41,78927,111687,77,78925,1114,1116,77,78925,1118,31,75,1120,75,75,75,75,111697,111697,111697,111697,111689,76863,78925,111689,111687,1122,78925,111687,111697,1126,111697,111697,111697,111697,111697,111697,111697,111697,111687,1030,111687,111689]
def row565 : List ℕ := [72273,78923,78923,73297,81,76865,76865,81,73,77375,77375,73,71,0,33,71,79435,61,78923,78923,76865,79437,77375,79437,75,78929,75,79953,79437,61,61,78923,78923,0,79,156,79,33,0,78923,77375,77375]
def row566 : List ℕ := [42]
def row567 : List ℕ := [77375,77375,77373,77373,42]
def row568 : List ℕ := [81,109633,109633,81,112201,61,958,112201,109633,112201,112201,112201,144465,111177,145489,112201,61,61,144459,107089,111689,108625,112201,144459,112201,144459,42,79,332,79,3,1132,144459,77,77,77375,77375,77,1134,77375,3,77375,112201,71,402,71,3]
def row569 : List ℕ := [81,142401,142401,81,73,402,1,73,112199,61,142401,112199,0,112199,112199,177233,111175,178257,112199,61,109137,112199,111687,110673,112199,112199,112199,112199,177227,112199,112199,79,41,79,41,112199,41,41,177227,77,0,77,1,0,112199,0,142401]
def row570 : List ℕ := [459454033,61,725726801,725726801,720,112199,178251,111175,112199,71,61,71,61,725726289,75,75,177227,75,112199,112199,177227,112199,112199,112199,112199,725694031,41,61,41,177227,0,112199,960,725726801]
def row571 : List ℕ := [39505,46155,46155,40529,77,156,0,77,81,44097,81,44097,42,116,44097,81,73,332,116,73,71,41,41,71,46667,61,79439,61,46155,46155,0,79439,44097,79439,404,79439,79439,44089,75,46161,75,47185,41,61,962,44097]
def row572 : List ℕ := [583120455,0,107599]
def row573 : List ℕ := [112199,41,112199,41,112199,459316817,75,79,39997,79,79439,39997,79439,41,79439,79,39997,79,79439,79,75,163689041,0,39997,459316305,459316305,232,39997,41,39997,39997,39997,39997,41,41,39997,1144,459316305]
def row574 : List ℕ := [0,79,61,156,61,53,77,37949]
def row575 : List ℕ := [140,79,966,61,332,61,49]
def row576 : List ℕ := [112209,112209,142397,832,142397,45,73,958,142397,112201,112201,73,112201,73,107595,111185,142397,111697,107597,77375,142397,107597,142407,0,142397,142407,142397,112201,107595,142397,107595,107595,960,142397,583120455,583120455,966,112201,107599,962,107599,142397,964,107595,112201,440481357]
def row577 : List ℕ := [75,111185,75,61,111697,75,77,79437,1130,61,61,61,77,79437,81,112209,112209,112209,112209,112209,81,112209,73,112201,1136,61,61,61,73,112201,71,112199,1138,61,61,61,71,112199,75,75,61,75,75,75,75,79437,61,61,79437,112209,112209,112209,112209,112201,61,61,112201,112199,1140,61,61,61,112199,112209,112209,112209,112209,112201,75,75,112201,112199,112199,75,75,112199,112199,79,79439,1142,61,79,79439,61,61,79439,61,79439,61,75,1146,75,75,75,75,79437,1148,79439,79437,112209,112209,112209,112209,112201,1150,79439,112201,112199,41,79439,112199,75,75,75,75,112209,112209,112209,112209,112201,77375,79437,112201,112199,698,79437,112199,112209,1152,112209,112209,112209,112209,112209,112209,112209,112209,112199,1032,112199,112201]
def row578 : List ℕ := [75,73,61]
def row579 : List ℕ := [73,111689,112713,73,73,31,75,3,1156,0,78925]
def row580 : List ℕ := [71,177223,71,178247,73,1,71,3,928,177229,42,144459,42]
def row581 : List ℕ := [0,45,0,45,73,73,44095,44095,591443537,142397,0,440546383,440546383,3,44095,440546383,0,440546383,2388727477319,2388727477319,44095]
def row582 : List ℕ := [6,0,46153,73,440546383,142397,3,440448077]
def row583 : List ℕ := [81,144465,144465,142397,81,144465,922,142397,144465,142397,924,926,145489,73,73,591504461,63,63,63,142397,591504461,440546379,0,142397,440546379,583185479,928,142397,583185479,440546383,940,440546383,788,440546383,454,932,440546383,934,3,440546383,1162,1164,440546383,598,142397,591504461,63,440546383,591504461,440546379,216,440546383,440546379,583185479,0,440546383,583185479,591504461,63,591504461,63,107597,107597,63,591504461,63,107597,591504461,944,63,440546379,63,591504461,440546379,583185479,63,591504461,583185479,440546379,838,440546379,948,440546379,946,440546379,3,583185479,0,440546379,583185479,583185479,872,583185479,878,583185479,950,583185479,3]
def row584 : List ℕ := [81,109637,81,109637,312,314,109637,81,46665,3,44095,144463,47177,49,46153,316,454,46153,109637,46153,46153,77,77,44095,44095,77,318,44095,320,75,166,75,0,71,300,71]
def row585 : List ℕ := [79433,78409]
def row586 : List ℕ := [45119,109635,0,930]
def row587 : List ℕ := [144465,42,144463,3,47177,47177,466,932,144461,1170,44095,1172]
def row588 : List ℕ := [81,109637,109637,81,46153,3,3,144463,46665,46665,46673,73,45649,73,42577,46665,41553,46665,934,46665,109637,46665,46665,77,44607,77,44607,75,0,75,3,71,0,71,3]
def row589 : List ℕ := [0,45,0,45,73,73,44095,44095,0,440546383,591443537,142397,440546383,3,44095,440546383,0,440546383,2388727477319,2388727477319,44095]
def row590 : List ℕ := [79433]
def row591 : List ℕ := [73,46153,73,79,73,46153,73,0,73,44095,44095,591443025,448,591443537,61,79,144463,79,3,46153,46153,44095,144463,508,144463,591443025,591443025,725660743,725660743,591443025,591443025,188888657,61,1178,46153,591443025,591443025,591443025,44095,1180,44095,46153,42,46153]
def row592 : List ℕ := [73,46153,47177,73,73,466,144465,416,144463,61,79,3,61,1164,46157,516]
def row593 : List ℕ := [145487,45641,73,73,44607,61,61,61,591443025,61,79,79,591443537,591443537,593540689,61,598,46665,591443537,591443537,591443537,44607,3,44607,46665,0,46665,0,3]
def row594 : List ℕ := [41,166,41,3,177223,42,508,75,236,194,216,37965,42]
def row595 : List ℕ := [59,300,59,3,0,44109]
def row596 : List ℕ := [0,109635]
def row597 : List ℕ := [44095,79433]
def row598 : List ℕ := [0,3]
def row599 : List ℕ := [0,3,0,77373,0,79433,0,0,0,109635]
def row600 : List ℕ := [109635,0,3,109635,79433,79433,144461,79433,79433,79433,79433,79433,77373,0,77373,0,77373,0,77373,109635,77373,42,77373,1192,79433,79433,79433,79433,79433,79433,79433,79433,79433,79433,3,516,42,3,77373,516,1194,77373,79433,79433,79433,79433,1196,42,0,1192,109635,0,0,109635,1198,0,0,0,3,0,0,3,79433,79433,79433,79433,109635,0,0,109635,1198,0,0,0,3,42,1192,3,79433,79433,79433,79433,109635,0,0,109635]
def row601 : List ℕ := [78409,591504461,78409,3,109635,3,0,79433,79433,79433,79433,942,3,0,3]
def row602 : List ℕ := [78409,77373,109635]
def row603 : List ℕ := [109635,0,45119,942]
def row604 : List ℕ := [44095]
def row605 : List ℕ := [143423]
def row606 : List ℕ := [142399,0,109635]
def row607 : List ℕ := [78409,144461,78409,109635,0,3,109635,79433,79433,79433,79433,79433,79433,77373,79433,79433,77373,79433,77373,1202,79433,1204,79433,79433,3,1206,1208,3,1180,3,3,0,0,3,0,79433,3,1210,1212,3]
def row608 : List ℕ := [81,109633,109633,81,112201,3,112713,47,111689,31,111689,111689,79,166,79,0,77,77,76863,76863,77,726,76863,0,76863,144459,71,402,71]
def row609 : List ℕ := [144459,3,112713,112713,31,946,144461,1170,76863]
def row610 : List ℕ := [108113,112201,112201,107089,81,109633,109633,81,71,0,3,71,111689,3,112201,112201,144459,0,112209,73,111185,73,3,144459,112201,112201,79,116,79,3,236,144459,77,77375,77,77375]
def row611 : List ℕ := [75,75,144459,75,61,591504465,591504465,591504977,73,75,144459,75,3,448967751,448967751,61,47,61,47,742,144459,440547409,73,63,63,712,144459,42,0,63,63,63,144459,63]
def row612 : List ℕ := [177223,3,178247,35,177735,1,177225,177225,79,300,79,0,0,0,77,77,142399,142399,77,1004,142399,1006,142399,177223,75,75,1008,402,75,42,0,386,0,177225,81,1010,81]
def row613 : List ℕ := [177223,3,71,178249,1,950,144461,1170,142399,1210,144459,42]
def row614 : List ℕ := [3,177223,143441,177223,177735,141905,81,0,3,81,177737,177223,177745,177223,176721,178247,3,177223,177737,177737,79,0,79,3,0,3,77,142911,77,142911,75,0,75,3,0,177737]
def row615 : List ℕ := [81,144465,144465,144465,144465,144465,81,144465,145489,73,73,73,73,73,61,73,73,73,144461,63,63,63,61,144461,144459,1158,61,144459,144465,144465,144465,144465,177223,1160,61,177223,144977,61,73,144465,1166,73,144465,144465,144465,144465,144465,144465,79,144463,1168,1174,79,144463,1176,3,144463,1182,1184,144463,1186,61,73,73,73,73,144461,63,144463,144461,144459,1188,144463,144459,144465,144465,144465,144465,177223,1190,144463,177223,77,77,63,144461,63,63,77,144461,1200,63,1214,63,73,63,73,73,73,73,144459,63,144461,144459,144465,144465,144465,144465,177223,63,144461,177223,75,144459,1216,1218,75,144459,1220,3,73,1222,73,73,73,73,144465,144465,144465,144465,177223,766,144459,177223,71,177223,1224,1226,71,177223,1228,3,177223,73,177223,73,144465,144465,144465,144465]
def row616 : List ℕ := [107089,111689,111689,108113,81,110145,110145,81,71,1,31,71,112201,61,111689,111689,110145,144971,73,111697,73,112721,144971,61,61,111689,111689,111689,79,240,79,31,77,76863,77,76863,76863,144971]
def row617 : List ℕ := [81,109643]
def row618 : List ℕ := [141905,177223,177735,143441,81,386,1,81,177735,61,177225,177735,1234,177735,177735,177233,176711,178257,177735,61,177225,177225,79,368,79,1,177735,1066,520,61,77,142399,77,142399,142399,177735,75,75,1,1,75,42,1,1,1,177735]
def row619 : List ℕ := [41553,46153,46153,42577,77,44095,44095,77,75,240,0,75,81,110149,81,110149,312,116,110149,81,71,368,0,71,46665,61,144975,61,46153,46153,44095,144975,1070,144975,110149,144975,144975,1,73,46161,73,47185,46153,46153]
def row620 : List ℕ := [73,73,44095,44095,188888657,0,593540689,61,79,144975,79,61,46153,46153,44095,144975,0,144975,188888657,188888657,188921415,188921415,47177,143951,61,591443025,188888657,188888657,520,61,46153,188888657]
def row621 : List ℕ := [177735,0,242,79,0,61,240,61,41,75,39997]
def row622 : List ℕ := [73,143953,73,61,144465,73,77,144973,63,61,61,61,77,144973,75,144971,1232,61,61,61,75,144971,81,144977,144977,144977,144977,144977,81,144977,71,177735,1236,61,61,61,71,177735,73,73,61,73,73,73,73,144973,63,61,61,61,144973,144971,61,61,144971,144977,144977,144977,144977,177735,61,61,177735,144977,73,144977,144977,144977,144977,79,144975,1238,61,79,144975,61,61,144975,1240,61,144975,61,61,73,73,73,73,144973,63,144975,144973,144971,1242,144975,144971,144977,144977,144977,144977,177735,370,144975,177735,73,73,73,73,144971,63,144973,144971,144977,144977,144977,144977,177735,63,144973,177735,73,73,73,73,144977,144977,144977,144977,177735,1,144971,177735,177735,73,177735,73,144977,144977,144977,144977]
def row623 : List ℕ := [177735,1,177225,177225,178247,35,177223,3,79,300,79,0,0,0,77,77,142399,142399,77,1004,142399,1006,142399,177223,75,75,1008,402,75,42,0,386,0,177225,81,1010,81]
def row624 : List ℕ := [112199,111175]
def row625 : List ℕ := [47]
def row626 : List ℕ := [178247,177225,1,178247,3,177229,42,177227,1248,1008,1250]
def row627 : List ℕ := [1,177223,142929,177735,177735,141905,75,1,1,75,81,0,1,81,177225,177225,144977,71,143953,71,1,177225,177735,177735,79,116,79,1,0,1,77,142399,77,142399,142399,177735]
def row628 : List ℕ := [71,111687,71,75,71,111687,71,31,71,725726801,61,75,177227,75,1,177227,111687,725726289,725726289,722,177227,457356881,61,725726289,725726289,646,111687,41,41,111687,725693519,1096,177227,0,111687,0,725726289]
def row629 : List ℕ := [61,725726289,178251,111175,112199,71,61,71,75,75,177227,75,112199,112199,177227,112199,112199,112199,459454033,61,725726801,725726801,720,112199,41,61,41,177227,112199,725694031,0,112199,960,725726801]
def row630 : List ℕ := [928,71,177223,71,178247,73,1,71,3,177229,42,144459,42]
def row631 : List ℕ := [725757521,71,177225,583185489,73,177225,73,61,73,177225,73,1,73,61,35,61,35,583186513,71,646,720,177231,177231,308,177225,344,0,524,0,142399,142399,142399,142399,0,1022,1022,177225,142411,142411,1024,142411,1026,583185489,583185489]
def row632 : List ℕ := [81,142405,81,142405,42,224,142405,81,73,300,116,73,46663,1,46151,46151,177231,46151,41,177231,47175,59,46151,358,142405,46151,344,46151,77,110,77,0,75,75,41,41,75,360,41,362,354,142405]
def row633 : List ℕ := [75305]
def row634 : List ℕ := [76347,142401]
def row635 : List ℕ := [177233,1266,177231,1,46151,47175,47175,358,177227,1248,41,1268]
def row636 : List ℕ := [81,142405,142405,81,73,0,1,73,46151,1,1,177231,46663,46663,177231,46663,46673,71,45649,71,44625,177231,46663,177231,43601,46663,46663,142405,46663,0,46663,77,0,77,1,75,41,75,41,0,142405]
def row637 : List ℕ := [71,46151,71,79,71,46151,71,484,71,41,41,725660753,450,725661265,61,79,177231,79,1,46151,46151,46151,177231,46151,122,177231,41,177231,725660753,725660753,128,177231,725660753,725660753,0,0,188921425,61,725660753,725660753,524,46151,524,46151,41,526,41,46151,528,725660753]
def row638 : List ℕ := [71,46151,47175,71,71,358,177233,422,61,79,1,46151,61,46155,532]
def row639 : List ℕ := [178255,45639,71,177231,71,46663,71,41,61,725660753,61,79,79,46663,177231,725661265,725661265,0,1,191018577,61,725661265,725661265,0,46663,0,46663,41,1,41,46663,0,725661265]
def row640 : List ℕ := [128,288,49,300,1,49,71,118,308,42059]
def row641 : List ℕ := [81,142403,142403,81,73,142399,142399,73,79431,1,0,177229,79943,43,78919,33,142399,78919,79,110,79,0,75,75,0,0,75,42,0,0,142399,142399]
def row642 : List ℕ := [177229,1,79943,79943,33,177227,1248]
def row643 : List ℕ := [77393,79431,79431,76369,81,142403,142403,81,73,142399,142399,73,78919,1,79431,79431,177229,142399,79441,71,78417,71,1,177229,142399,79431,79,116,79,1,0,177229,75,1,75,1,142399,142399]
def row644 : List ℕ := [77,77,177229,77,61,725691473,725691473,142399,142399,725691985,71,77,177229,77,1,0,177229,142399,142399,61,43,61,43,314751057,71,0,0,177231,177231,676,177229,524,0,0,0,0,0,142399,725691473]
def row645 : List ℕ := [51,0,51,1,0,71,0,77,0,75,0,72775,658]
def row646 : List ℕ := [112199,177227,112199,111175,177227,177227,111175,177227,177227,177227,177227,177227,177227,177227,177227,65,142401,142401,65,47,1008,1,47,111175,111175,111175,111175,111165,111175,111175,111165,142401,111175,1024,111175,76347,41,76347,41,41,41,111175,41,51,0,51,1,0,111175,0,142401]
def row647 : List ℕ := [112199,112199,1,112711,57,111687,31,79,41,79,41,77,0,77,1,81,142401,81,142401,73,402,73,1,0,142401]
def row648 : List ℕ := [0,142401]
def row649 : List ℕ := [0,1,0,112189,0,112199,0,77371,0,142401,42]
def row650 : List ℕ := [587314759,142401,0,0,0,0,42]
def row651 : List ℕ := [142401,583120455,142401,142401]
def row652 : List ℕ := [142401,0,1,142401,1,42,1,1296,112199,112199,177227,112199,112199,112199,112199,112199,112189,0,112189,0,112189,0,112189,142401,112189,42,112189,1296,112199,112199,112199,112199,112199,112199,112199,112199,112199,112199,112199,112199,77371,532,77371,1,112189,532,77371,112189,112199,112199,112199,112199,77371,0,77371,1296,142401,75303,77371,142401,77371,0,77371,1296,1,0,0,1,112199,112199,112199,112199,142401,0,0,142401,1298,0,0,1296,142401,1300,532,0,1302,142401]
def row653 : List ℕ := [0,112199,0,142401]
def row654 : List ℕ := [0,112199]
def row655 : List ℕ := [81,142401,142401,81,73,402,1,73,111687,1,112199,112199,112199,112199,177227,142401,177227,142401,177227,0,177227,1306,112209,71,111185,71,177227,1,112199,177227,110161,112199,109137,112199,79,41,79,41,177227,41,77371,177227,77,0,77,1,177227,0,1308,177227,0,142401]
def row656 : List ℕ := [0,0,142401]
def row657 : List ℕ := [142401,0,76347]
def row658 : List ℕ := [112189,111175]
def row659 : List ℕ := [111175,177227,111175,142401,0,1,142401,1,1250,1,1312,112199,112199,112199,112199,112199,112199,112189,112199,112199,112189,112199,112189,1026,112199,1026,112199,77371,1314,77371,1,526,1,112199,1316,1,0,0,1,0,112199]
def row660 : List ℕ := [725724753,71,75,177227,75,1,75,177227,75,61,75,61,57,61,57,177227,177227,448968785,71,177231,177231,41,177227,41,41,0,57,448967761,448967761,0,57,0,448967761]
def row661 : List ℕ := [75,0,109639,47,402,1,47,0,73,722,0,71,1022]
def row662 : List ℕ := [725757521,142397,440579151,107585]
def row663 : List ℕ := [177233,177233,45,858,42,45,73,177225,177225,73,928,177225,178257,142407,142407,142407,142397,142407,0,960,1324,142407,177225,142407,177745,142397,288,177225,107599,354,107599,0,528,0,142407,440579151,177225,440579149,107597,142399,107597,142399,142399,142407,107595,107595,0,0,107595,1300,0,0,0,142407]
def row664 : List ℕ := [81,177233,177233,177233,177233,177233,81,177233,73,177225,1246,1252,1254,1,73,177225,178257,71,71,71,71,71,61,71,71,71,177229,1050,61,177229,177227,1256,1,1258,61,177227,177233,177233,177233,177233,177225,1260,61,177225,177745,61,71,177233,177233,177233,177233,177233,177233,71,1262,71,71,71,71,79,177231,1264,1270,79,177231,1272,1,177231,1274,1276,177231,1278,61,71,71,71,177231,71,71,177229,160,177231,177229,177227,41,177231,177227,177233,177233,177233,177233,177225,1280,177231,177225,77,177229,1282,1284,77,177229,1286,1,71,1288,71,71,71,71,177227,1290,177229,177227,177233,177233,177233,177233,177225,142399,177229,177225,75,75,1292,177227,1294,1,75,177227,1304,1310,1318,1,71,1320,71,71,71,71,177233,177233,177233,177233,177225,1322,177227,177225,177233,1326,177233,177233,177233,177233]
def row665 : List ℕ := [76369,78919,78919,77393,75,0,33,75,81,142915,142915,81,73,142911,142911,73,79431,61,78919,78919,0,177741,142915,177741,142911,177741,71,78929,71,79953,177741,61,61,78919,79,0,79,33,142911,142911]
def row666 : List ℕ := [109137,111687,111687,110161,81,142913,142913,81,73,0,31,73,112199,61,111687,111687,142913,177739,0,177739,71,111697,71,112721,177739,61,61,111687,79,41,79,31,77,0,77,31,0,177739,0,142913]
def row667 : List ℕ := [81,81]
def row668 : List ℕ := [81,0,3,81,177735,61,974,177737,1334,177737,177737,71,144465,71,145489,177737,61,61,177223,141905,177223,142929,177223,177223,177223,79,0,79,3,236,61,77,142911,77,142911,142911,177737,75,0,75,3,0,177737]
def row669 : List ℕ := [71,71,459454033,61,457356881,457356881,0,177739,112711,176715,75,75,61,725726289,41,31,61,61,0,177739,0,457356881]
def row670 : List ℕ := [587248711,142917,0,3,142397,142397,107553,107553]
def row671 : List ℕ := [142917]
def row672 : List ℕ := [142917,583054407,142917,142917]
def row673 : List ℕ := [46151,46151,177743,46151,46151,46151,46151,46151,33,0,0,33,44089,122,0,44089,142917,0,0,142917,3,0,0,3,46151,46151,46151,46151,61,61,61,61,61,61,61,61,61,61,61,61,61,61,61,61,46151,46151,46151,46151,46151,46151,46151,46151,46151,46151,46151,46151,44089,0,33,44089,142917,7,33,142917,33,3,33,3,46151,46151,46151,46151,142917,42021,44089,142917,44089,0,44089,3,142917,1340,1342,3,1344,142917]
def row674 : List ℕ := [71,46161,47185,71,43601,46151,46151,44625,77,0,0,77,75,41,41,75,81,142917,142917,81,73,0,0,73,46663,61,177743,46151,177743,61,46151,46151,46151,46151,177743,0,177743,33,177743,41,177743,44089,177743,142917,177743,142917,177743,404,177743,3,978,142917]
def row675 : List ℕ := [71,71,41,41,188921425,0,191018577,61,79,46151,79,79,177743,46151,46151,0,177743,41,177743,188921425,188921425,538,177743,47175,176719,61,725660753,188921425,188921425,536,61,574,188921425]
def row676 : List ℕ := [0,79,0,61,0,61,53,77,37949]
def row677 : List ℕ := [140,79,538,980,61,0,61,49]
def row678 : List ℕ := [0,3,587248711,142917,142397,142397,107553,107553]
def row679 : List ℕ := [177745,177745,142397,0,142397,45,73,974,142397,177737,177737,73,177737,73,142407,176721,142397,177233,107597,142911,142397,107597,107595,0,142397,107595,142397,177737,142407,142397,142407,142407,0,142397,980,177737,107599,1356,978,142397,107599,107599,142397,142397,574,142397,177737,440579661]
def row680 : List ℕ := [71,176721,71,61,177233,71,77,177741,1330,61,61,61,77,177741,75,177739,1332,61,61,61,75,177739,81,177745,177745,177745,177745,177745,81,177745,73,177737,1336,61,61,61,73,177737,71,71,61,71,71,71,71,177741,61,61,177741,177739,1338,61,61,61,177739,177745,177745,177745,177745,177737,61,61,177737,177745,177745,177745,177745,71,71,71,71,79,177743,1346,1348,61,61,79,79,61,177743,61,61,177743,1350,61,177743,61,61,71,71,71,71,177741,1352,177743,177741,177739,41,177743,177739,177745,177745,177745,177745,177737,1354,177743,177737,71,71,71,71,177739,664,177741,177739,177745,177745,177745,177745,177737,142911,177741,177737,71,71,71,71,177745,177745,177745,177745,177737,748,177739,177737,177745,1358,177745,177745,177745,177745]
def row681 : List ℕ := [77,164,79,77,75,250,79,75,81,81,81,81,73,340,79,73,71,374,79,71,79,582,79,616,75,666,77,75,81,81,81,81,73,63,77,73,71,700,77,71,81,81,81,81,73,750,75,73,71,768,75,71,81,984,81,81,81,81,81,81,81,81,71,1034,71,73,77,1062,1078,77,75,1128,1154,75,81,81,81,81,73,1230,1244,73,71,1328,1360,71]
def group0 (i : ℕ) : List ℕ := (if i≤15 then (if i≤7 then (if i≤3 then (if i≤1 then (if i≤0 then row0 else row1) else (if i≤2 then row2 else row3)) else (if i≤5 then (if i≤4 then row4 else row5) else (if i≤6 then row6 else row7))) else (if i≤11 then (if i≤9 then (if i≤8 then row8 else row9) else (if i≤10 then row10 else row11)) else (if i≤13 then (if i≤12 then row12 else row13) else (if i≤14 then row14 else row15)))) else (if i≤23 then (if i≤19 then (if i≤17 then (if i≤16 then row16 else row17) else (if i≤18 then row18 else row19)) else (if i≤21 then (if i≤20 then row20 else row21) else (if i≤22 then row22 else row23))) else (if i≤27 then (if i≤25 then (if i≤24 then row24 else row25) else (if i≤26 then row26 else row27)) else (if i≤29 then (if i≤28 then row28 else row29) else (if i≤30 then row30 else row31)))))
def group1 (i : ℕ) : List ℕ := (if i≤47 then (if i≤39 then (if i≤35 then (if i≤33 then (if i≤32 then row32 else row33) else (if i≤34 then row34 else row35)) else (if i≤37 then (if i≤36 then row36 else row37) else (if i≤38 then row38 else row39))) else (if i≤43 then (if i≤41 then (if i≤40 then row40 else row41) else (if i≤42 then row42 else row43)) else (if i≤45 then (if i≤44 then row44 else row45) else (if i≤46 then row46 else row47)))) else (if i≤55 then (if i≤51 then (if i≤49 then (if i≤48 then row48 else row49) else (if i≤50 then row50 else row51)) else (if i≤53 then (if i≤52 then row52 else row53) else (if i≤54 then row54 else row55))) else (if i≤59 then (if i≤57 then (if i≤56 then row56 else row57) else (if i≤58 then row58 else row59)) else (if i≤61 then (if i≤60 then row60 else row61) else (if i≤62 then row62 else row63)))))
def group2 (i : ℕ) : List ℕ := (if i≤79 then (if i≤71 then (if i≤67 then (if i≤65 then (if i≤64 then row64 else row65) else (if i≤66 then row66 else row67)) else (if i≤69 then (if i≤68 then row68 else row69) else (if i≤70 then row70 else row71))) else (if i≤75 then (if i≤73 then (if i≤72 then row72 else row73) else (if i≤74 then row74 else row75)) else (if i≤77 then (if i≤76 then row76 else row77) else (if i≤78 then row78 else row79)))) else (if i≤87 then (if i≤83 then (if i≤81 then (if i≤80 then row80 else row81) else (if i≤82 then row82 else row83)) else (if i≤85 then (if i≤84 then row84 else row85) else (if i≤86 then row86 else row87))) else (if i≤91 then (if i≤89 then (if i≤88 then row88 else row89) else (if i≤90 then row90 else row91)) else (if i≤93 then (if i≤92 then row92 else row93) else (if i≤94 then row94 else row95)))))
def group3 (i : ℕ) : List ℕ := (if i≤111 then (if i≤103 then (if i≤99 then (if i≤97 then (if i≤96 then row96 else row97) else (if i≤98 then row98 else row99)) else (if i≤101 then (if i≤100 then row100 else row101) else (if i≤102 then row102 else row103))) else (if i≤107 then (if i≤105 then (if i≤104 then row104 else row105) else (if i≤106 then row106 else row107)) else (if i≤109 then (if i≤108 then row108 else row109) else (if i≤110 then row110 else row111)))) else (if i≤119 then (if i≤115 then (if i≤113 then (if i≤112 then row112 else row113) else (if i≤114 then row114 else row115)) else (if i≤117 then (if i≤116 then row116 else row117) else (if i≤118 then row118 else row119))) else (if i≤123 then (if i≤121 then (if i≤120 then row120 else row121) else (if i≤122 then row122 else row123)) else (if i≤125 then (if i≤124 then row124 else row125) else (if i≤126 then row126 else row127)))))
def group4 (i : ℕ) : List ℕ := (if i≤143 then (if i≤135 then (if i≤131 then (if i≤129 then (if i≤128 then row128 else row129) else (if i≤130 then row130 else row131)) else (if i≤133 then (if i≤132 then row132 else row133) else (if i≤134 then row134 else row135))) else (if i≤139 then (if i≤137 then (if i≤136 then row136 else row137) else (if i≤138 then row138 else row139)) else (if i≤141 then (if i≤140 then row140 else row141) else (if i≤142 then row142 else row143)))) else (if i≤151 then (if i≤147 then (if i≤145 then (if i≤144 then row144 else row145) else (if i≤146 then row146 else row147)) else (if i≤149 then (if i≤148 then row148 else row149) else (if i≤150 then row150 else row151))) else (if i≤155 then (if i≤153 then (if i≤152 then row152 else row153) else (if i≤154 then row154 else row155)) else (if i≤157 then (if i≤156 then row156 else row157) else (if i≤158 then row158 else row159)))))
def group5 (i : ℕ) : List ℕ := (if i≤175 then (if i≤167 then (if i≤163 then (if i≤161 then (if i≤160 then row160 else row161) else (if i≤162 then row162 else row163)) else (if i≤165 then (if i≤164 then row164 else row165) else (if i≤166 then row166 else row167))) else (if i≤171 then (if i≤169 then (if i≤168 then row168 else row169) else (if i≤170 then row170 else row171)) else (if i≤173 then (if i≤172 then row172 else row173) else (if i≤174 then row174 else row175)))) else (if i≤183 then (if i≤179 then (if i≤177 then (if i≤176 then row176 else row177) else (if i≤178 then row178 else row179)) else (if i≤181 then (if i≤180 then row180 else row181) else (if i≤182 then row182 else row183))) else (if i≤187 then (if i≤185 then (if i≤184 then row184 else row185) else (if i≤186 then row186 else row187)) else (if i≤189 then (if i≤188 then row188 else row189) else (if i≤190 then row190 else row191)))))
def group6 (i : ℕ) : List ℕ := (if i≤207 then (if i≤199 then (if i≤195 then (if i≤193 then (if i≤192 then row192 else row193) else (if i≤194 then row194 else row195)) else (if i≤197 then (if i≤196 then row196 else row197) else (if i≤198 then row198 else row199))) else (if i≤203 then (if i≤201 then (if i≤200 then row200 else row201) else (if i≤202 then row202 else row203)) else (if i≤205 then (if i≤204 then row204 else row205) else (if i≤206 then row206 else row207)))) else (if i≤215 then (if i≤211 then (if i≤209 then (if i≤208 then row208 else row209) else (if i≤210 then row210 else row211)) else (if i≤213 then (if i≤212 then row212 else row213) else (if i≤214 then row214 else row215))) else (if i≤219 then (if i≤217 then (if i≤216 then row216 else row217) else (if i≤218 then row218 else row219)) else (if i≤221 then (if i≤220 then row220 else row221) else (if i≤222 then row222 else row223)))))
def group7 (i : ℕ) : List ℕ := (if i≤239 then (if i≤231 then (if i≤227 then (if i≤225 then (if i≤224 then row224 else row225) else (if i≤226 then row226 else row227)) else (if i≤229 then (if i≤228 then row228 else row229) else (if i≤230 then row230 else row231))) else (if i≤235 then (if i≤233 then (if i≤232 then row232 else row233) else (if i≤234 then row234 else row235)) else (if i≤237 then (if i≤236 then row236 else row237) else (if i≤238 then row238 else row239)))) else (if i≤247 then (if i≤243 then (if i≤241 then (if i≤240 then row240 else row241) else (if i≤242 then row242 else row243)) else (if i≤245 then (if i≤244 then row244 else row245) else (if i≤246 then row246 else row247))) else (if i≤251 then (if i≤249 then (if i≤248 then row248 else row249) else (if i≤250 then row250 else row251)) else (if i≤253 then (if i≤252 then row252 else row253) else (if i≤254 then row254 else row255)))))
def group8 (i : ℕ) : List ℕ := (if i≤271 then (if i≤263 then (if i≤259 then (if i≤257 then (if i≤256 then row256 else row257) else (if i≤258 then row258 else row259)) else (if i≤261 then (if i≤260 then row260 else row261) else (if i≤262 then row262 else row263))) else (if i≤267 then (if i≤265 then (if i≤264 then row264 else row265) else (if i≤266 then row266 else row267)) else (if i≤269 then (if i≤268 then row268 else row269) else (if i≤270 then row270 else row271)))) else (if i≤279 then (if i≤275 then (if i≤273 then (if i≤272 then row272 else row273) else (if i≤274 then row274 else row275)) else (if i≤277 then (if i≤276 then row276 else row277) else (if i≤278 then row278 else row279))) else (if i≤283 then (if i≤281 then (if i≤280 then row280 else row281) else (if i≤282 then row282 else row283)) else (if i≤285 then (if i≤284 then row284 else row285) else (if i≤286 then row286 else row287)))))
def group9 (i : ℕ) : List ℕ := (if i≤303 then (if i≤295 then (if i≤291 then (if i≤289 then (if i≤288 then row288 else row289) else (if i≤290 then row290 else row291)) else (if i≤293 then (if i≤292 then row292 else row293) else (if i≤294 then row294 else row295))) else (if i≤299 then (if i≤297 then (if i≤296 then row296 else row297) else (if i≤298 then row298 else row299)) else (if i≤301 then (if i≤300 then row300 else row301) else (if i≤302 then row302 else row303)))) else (if i≤311 then (if i≤307 then (if i≤305 then (if i≤304 then row304 else row305) else (if i≤306 then row306 else row307)) else (if i≤309 then (if i≤308 then row308 else row309) else (if i≤310 then row310 else row311))) else (if i≤315 then (if i≤313 then (if i≤312 then row312 else row313) else (if i≤314 then row314 else row315)) else (if i≤317 then (if i≤316 then row316 else row317) else (if i≤318 then row318 else row319)))))
def group10 (i : ℕ) : List ℕ := (if i≤335 then (if i≤327 then (if i≤323 then (if i≤321 then (if i≤320 then row320 else row321) else (if i≤322 then row322 else row323)) else (if i≤325 then (if i≤324 then row324 else row325) else (if i≤326 then row326 else row327))) else (if i≤331 then (if i≤329 then (if i≤328 then row328 else row329) else (if i≤330 then row330 else row331)) else (if i≤333 then (if i≤332 then row332 else row333) else (if i≤334 then row334 else row335)))) else (if i≤343 then (if i≤339 then (if i≤337 then (if i≤336 then row336 else row337) else (if i≤338 then row338 else row339)) else (if i≤341 then (if i≤340 then row340 else row341) else (if i≤342 then row342 else row343))) else (if i≤347 then (if i≤345 then (if i≤344 then row344 else row345) else (if i≤346 then row346 else row347)) else (if i≤349 then (if i≤348 then row348 else row349) else (if i≤350 then row350 else row351)))))
def group11 (i : ℕ) : List ℕ := (if i≤367 then (if i≤359 then (if i≤355 then (if i≤353 then (if i≤352 then row352 else row353) else (if i≤354 then row354 else row355)) else (if i≤357 then (if i≤356 then row356 else row357) else (if i≤358 then row358 else row359))) else (if i≤363 then (if i≤361 then (if i≤360 then row360 else row361) else (if i≤362 then row362 else row363)) else (if i≤365 then (if i≤364 then row364 else row365) else (if i≤366 then row366 else row367)))) else (if i≤375 then (if i≤371 then (if i≤369 then (if i≤368 then row368 else row369) else (if i≤370 then row370 else row371)) else (if i≤373 then (if i≤372 then row372 else row373) else (if i≤374 then row374 else row375))) else (if i≤379 then (if i≤377 then (if i≤376 then row376 else row377) else (if i≤378 then row378 else row379)) else (if i≤381 then (if i≤380 then row380 else row381) else (if i≤382 then row382 else row383)))))
def group12 (i : ℕ) : List ℕ := (if i≤399 then (if i≤391 then (if i≤387 then (if i≤385 then (if i≤384 then row384 else row385) else (if i≤386 then row386 else row387)) else (if i≤389 then (if i≤388 then row388 else row389) else (if i≤390 then row390 else row391))) else (if i≤395 then (if i≤393 then (if i≤392 then row392 else row393) else (if i≤394 then row394 else row395)) else (if i≤397 then (if i≤396 then row396 else row397) else (if i≤398 then row398 else row399)))) else (if i≤407 then (if i≤403 then (if i≤401 then (if i≤400 then row400 else row401) else (if i≤402 then row402 else row403)) else (if i≤405 then (if i≤404 then row404 else row405) else (if i≤406 then row406 else row407))) else (if i≤411 then (if i≤409 then (if i≤408 then row408 else row409) else (if i≤410 then row410 else row411)) else (if i≤413 then (if i≤412 then row412 else row413) else (if i≤414 then row414 else row415)))))
def group13 (i : ℕ) : List ℕ := (if i≤431 then (if i≤423 then (if i≤419 then (if i≤417 then (if i≤416 then row416 else row417) else (if i≤418 then row418 else row419)) else (if i≤421 then (if i≤420 then row420 else row421) else (if i≤422 then row422 else row423))) else (if i≤427 then (if i≤425 then (if i≤424 then row424 else row425) else (if i≤426 then row426 else row427)) else (if i≤429 then (if i≤428 then row428 else row429) else (if i≤430 then row430 else row431)))) else (if i≤439 then (if i≤435 then (if i≤433 then (if i≤432 then row432 else row433) else (if i≤434 then row434 else row435)) else (if i≤437 then (if i≤436 then row436 else row437) else (if i≤438 then row438 else row439))) else (if i≤443 then (if i≤441 then (if i≤440 then row440 else row441) else (if i≤442 then row442 else row443)) else (if i≤445 then (if i≤444 then row444 else row445) else (if i≤446 then row446 else row447)))))
def group14 (i : ℕ) : List ℕ := (if i≤463 then (if i≤455 then (if i≤451 then (if i≤449 then (if i≤448 then row448 else row449) else (if i≤450 then row450 else row451)) else (if i≤453 then (if i≤452 then row452 else row453) else (if i≤454 then row454 else row455))) else (if i≤459 then (if i≤457 then (if i≤456 then row456 else row457) else (if i≤458 then row458 else row459)) else (if i≤461 then (if i≤460 then row460 else row461) else (if i≤462 then row462 else row463)))) else (if i≤471 then (if i≤467 then (if i≤465 then (if i≤464 then row464 else row465) else (if i≤466 then row466 else row467)) else (if i≤469 then (if i≤468 then row468 else row469) else (if i≤470 then row470 else row471))) else (if i≤475 then (if i≤473 then (if i≤472 then row472 else row473) else (if i≤474 then row474 else row475)) else (if i≤477 then (if i≤476 then row476 else row477) else (if i≤478 then row478 else row479)))))
def group15 (i : ℕ) : List ℕ := (if i≤495 then (if i≤487 then (if i≤483 then (if i≤481 then (if i≤480 then row480 else row481) else (if i≤482 then row482 else row483)) else (if i≤485 then (if i≤484 then row484 else row485) else (if i≤486 then row486 else row487))) else (if i≤491 then (if i≤489 then (if i≤488 then row488 else row489) else (if i≤490 then row490 else row491)) else (if i≤493 then (if i≤492 then row492 else row493) else (if i≤494 then row494 else row495)))) else (if i≤503 then (if i≤499 then (if i≤497 then (if i≤496 then row496 else row497) else (if i≤498 then row498 else row499)) else (if i≤501 then (if i≤500 then row500 else row501) else (if i≤502 then row502 else row503))) else (if i≤507 then (if i≤505 then (if i≤504 then row504 else row505) else (if i≤506 then row506 else row507)) else (if i≤509 then (if i≤508 then row508 else row509) else (if i≤510 then row510 else row511)))))
def group16 (i : ℕ) : List ℕ := (if i≤527 then (if i≤519 then (if i≤515 then (if i≤513 then (if i≤512 then row512 else row513) else (if i≤514 then row514 else row515)) else (if i≤517 then (if i≤516 then row516 else row517) else (if i≤518 then row518 else row519))) else (if i≤523 then (if i≤521 then (if i≤520 then row520 else row521) else (if i≤522 then row522 else row523)) else (if i≤525 then (if i≤524 then row524 else row525) else (if i≤526 then row526 else row527)))) else (if i≤535 then (if i≤531 then (if i≤529 then (if i≤528 then row528 else row529) else (if i≤530 then row530 else row531)) else (if i≤533 then (if i≤532 then row532 else row533) else (if i≤534 then row534 else row535))) else (if i≤539 then (if i≤537 then (if i≤536 then row536 else row537) else (if i≤538 then row538 else row539)) else (if i≤541 then (if i≤540 then row540 else row541) else (if i≤542 then row542 else row543)))))
def group17 (i : ℕ) : List ℕ := (if i≤559 then (if i≤551 then (if i≤547 then (if i≤545 then (if i≤544 then row544 else row545) else (if i≤546 then row546 else row547)) else (if i≤549 then (if i≤548 then row548 else row549) else (if i≤550 then row550 else row551))) else (if i≤555 then (if i≤553 then (if i≤552 then row552 else row553) else (if i≤554 then row554 else row555)) else (if i≤557 then (if i≤556 then row556 else row557) else (if i≤558 then row558 else row559)))) else (if i≤567 then (if i≤563 then (if i≤561 then (if i≤560 then row560 else row561) else (if i≤562 then row562 else row563)) else (if i≤565 then (if i≤564 then row564 else row565) else (if i≤566 then row566 else row567))) else (if i≤571 then (if i≤569 then (if i≤568 then row568 else row569) else (if i≤570 then row570 else row571)) else (if i≤573 then (if i≤572 then row572 else row573) else (if i≤574 then row574 else row575)))))
def group18 (i : ℕ) : List ℕ := (if i≤591 then (if i≤583 then (if i≤579 then (if i≤577 then (if i≤576 then row576 else row577) else (if i≤578 then row578 else row579)) else (if i≤581 then (if i≤580 then row580 else row581) else (if i≤582 then row582 else row583))) else (if i≤587 then (if i≤585 then (if i≤584 then row584 else row585) else (if i≤586 then row586 else row587)) else (if i≤589 then (if i≤588 then row588 else row589) else (if i≤590 then row590 else row591)))) else (if i≤599 then (if i≤595 then (if i≤593 then (if i≤592 then row592 else row593) else (if i≤594 then row594 else row595)) else (if i≤597 then (if i≤596 then row596 else row597) else (if i≤598 then row598 else row599))) else (if i≤603 then (if i≤601 then (if i≤600 then row600 else row601) else (if i≤602 then row602 else row603)) else (if i≤605 then (if i≤604 then row604 else row605) else (if i≤606 then row606 else row607)))))
def group19 (i : ℕ) : List ℕ := (if i≤623 then (if i≤615 then (if i≤611 then (if i≤609 then (if i≤608 then row608 else row609) else (if i≤610 then row610 else row611)) else (if i≤613 then (if i≤612 then row612 else row613) else (if i≤614 then row614 else row615))) else (if i≤619 then (if i≤617 then (if i≤616 then row616 else row617) else (if i≤618 then row618 else row619)) else (if i≤621 then (if i≤620 then row620 else row621) else (if i≤622 then row622 else row623)))) else (if i≤631 then (if i≤627 then (if i≤625 then (if i≤624 then row624 else row625) else (if i≤626 then row626 else row627)) else (if i≤629 then (if i≤628 then row628 else row629) else (if i≤630 then row630 else row631))) else (if i≤635 then (if i≤633 then (if i≤632 then row632 else row633) else (if i≤634 then row634 else row635)) else (if i≤637 then (if i≤636 then row636 else row637) else (if i≤638 then row638 else row639)))))
def group20 (i : ℕ) : List ℕ := (if i≤655 then (if i≤647 then (if i≤643 then (if i≤641 then (if i≤640 then row640 else row641) else (if i≤642 then row642 else row643)) else (if i≤645 then (if i≤644 then row644 else row645) else (if i≤646 then row646 else row647))) else (if i≤651 then (if i≤649 then (if i≤648 then row648 else row649) else (if i≤650 then row650 else row651)) else (if i≤653 then (if i≤652 then row652 else row653) else (if i≤654 then row654 else row655)))) else (if i≤663 then (if i≤659 then (if i≤657 then (if i≤656 then row656 else row657) else (if i≤658 then row658 else row659)) else (if i≤661 then (if i≤660 then row660 else row661) else (if i≤662 then row662 else row663))) else (if i≤667 then (if i≤665 then (if i≤664 then row664 else row665) else (if i≤666 then row666 else row667)) else (if i≤669 then (if i≤668 then row668 else row669) else (if i≤670 then row670 else row671)))))
def group21 (i : ℕ) : List ℕ := (if i≤676 then (if i≤674 then (if i≤673 then (if i≤672 then row672 else row673) else row674) else (if i≤675 then row675 else row676)) else (if i≤679 then (if i≤678 then (if i≤677 then row677 else row678) else row679) else (if i≤680 then row680 else row681)))
def guides (i : ℕ) : List ℕ := (if (i / 32)≤10 then (if (i / 32)≤5 then (if (i / 32)≤2 then (if (i / 32)≤1 then (if (i / 32)≤0 then group0 i else group1 i) else group2 i) else (if (i / 32)≤4 then (if (i / 32)≤3 then group3 i else group4 i) else group5 i)) else (if (i / 32)≤8 then (if (i / 32)≤7 then (if (i / 32)≤6 then group6 i else group7 i) else group8 i) else (if (i / 32)≤9 then group9 i else group10 i))) else (if (i / 32)≤16 then (if (i / 32)≤13 then (if (i / 32)≤12 then (if (i / 32)≤11 then group11 i else group12 i) else group13 i) else (if (i / 32)≤15 then (if (i / 32)≤14 then group14 i else group15 i) else group16 i)) else (if (i / 32)≤19 then (if (i / 32)≤18 then (if (i / 32)≤17 then group17 i else group18 i) else group19 i) else (if (i / 32)≤20 then group20 i else group21 i))))
def spec53 : FloorData := (0x71b9e0000172dcae0000dcb7,4,[0x2000400000a020180000280dfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe47fffffffd23ffffffffff,0x6050000000c0b01000013049fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe1fffffffff51ffffff48,0x3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdeeebffffd1ec7a3ffffc7f1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe8d2351ffffffff,0x3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9f8f3fffff1f47e3fffe4791ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2348])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof53 : Floor 441 spec53 := floorChecked (by decide +kernel)
def book0 (_i : ℕ) : {s : FloorData // Floor 441 s} := ⟨spec53,proof53⟩
def spec89 : FloorData := (0x73380f0005cab8016c000000000000000000000dc015b,4,[0x200002000280400050000000000000000000000280015ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffcc7fffffff547fffffffffffffffffffffffffffffff,0x605000000301600040000000000000000000001300091ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0fffffffffe93ffffffffffffffffffffffffea4,0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffddeff5fff47b8fff27fffffffffffffffffffffc7ffe9ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa3547fe93fffffffffffffffffffffffffff,0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9f8ff9fffc7e8fffa7ffffffffffffffffffffe47ff49ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff23fea4])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof89 : Floor 441 spec89 := floorChecked (by decide +kernel)
def spec101 : FloorData := (0xebde000000000000000372dc00000000000017c9d2e00000000,4,[0x40040000000000000000a0300000000000000a0201800000001ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff43fffffffffffffffffffffffffffffffffff363ffffffffff,0xc4800000000000000004c1200000000000000c8301000000001fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe1fffffffffffffffffd23ffffffffffffffffed1ffffffff,0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffff396bfffffffffffffff91e47fffffffffffff17c7e3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc8d23fffffffffffffffffffffffffff,0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbe73ffffffffffffffff1fc7ffffffffffffd1ec7a3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe8362d1ffffffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof101 : Floor 441 spec101 := floorChecked (by decide +kernel)
def spec105 : FloorData := (0x3b7001e000000000005d338026c000000000006e00017600000000,4,[0x100000400000000000280400050000000000001400002800000001fffffffffffffffffffffffffffffffffffffffffffffffffffffffffc8ffffffffffffffffecc7fffffffffffffffffffffffffffffff,0x30a00000000000000030260004000000000000980000a000000001fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe1fffffffffffffffffd93ffffffffffffffffe89ffffffff,0x3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffeddffebfffffffffff47b8fff27fffffffffffe3ffffd3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa2cc7fd93fffffffffffffffffffffffffff,0x3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffcf1fff3fffffffffffc7d8fffa7fffffffffff23ffff13ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff91fffe89ffffffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof105 : Floor 441 spec105 := floorChecked (by decide +kernel)
def spec149 : FloorData := (0xf3fb1c000000ddae000000000000000000000000000000000000000000000000000000000de37,4,[0x3fffffffffffffffffffffffffffffffff589dc7ffffff6eb3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffe6f9dfffffffffffffffffffffffffffffffffec7ce3fffffffe51fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0xc5002000000030580000000000000000000000000000000000000000000000000000000013049fffffffffffffffffffffffffffffffffff84e3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdc8,0x86203000000000400000000000000000000000000000000000000000000000000000000018061fffffffffffffffffffffffffffffffffffffffffffff2251fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x3fffffffffffffffffffffffffffffffff38cfc7ffffffc7a3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffe4791ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff21c8])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof149 : Floor 441 spec149 := floorChecked (by decide +kernel)
def spec153 : FloorData := (0x1e7007b2c006ed700000000000000000000000000000000000000000000000000000000000dc025b,4,[0x3ffffffffffffffffffffffffffffffeb1ff9da7ffb759ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe6fff5dfffffffffffffffffffffffffffffffd8fffcd3ffff28fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x18a00004000182c00000000000000000000000000000000000000000000000000000000001300091fffffffffffffffffffffffffffffffffff84d3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffda4,0x10c002050000020000000000000000000000000000000000000000000000000000000000018000a1fffffffffffffffffffffffffffffffffffffffff9128fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x3ffffffffffffffffffffffffffffffe71ffcfa7ffe3d1ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe47ff49ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff23fda4])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof153 : Floor 441 spec153 := floorChecked (by decide +kernel)
def spec164 : FloorData := (0x38118000000000000000008600000000000000000000000000000000000000000000000008c0000000000,4,[0x1000000000000000000000080000000000000000000000000000000000000000000000000100000000001fffffffffffffffffffffffffffee7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x2002000000000000000000000000000000000000000000000000000000000000000000001000000000001fffffffffffffffffffffffffffffffffffffffffffffff79fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x3fffffffffffffffffffffffffcffcfffffffffffffffffff3ffffffffffffffffffffffffffffffffffffffffffffffffee7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff73ffffffffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof164 : Floor 441 spec164 := floorChecked (by decide +kernel)
def spec169 : FloorData := (0xf707b38000000000006ee700000000000000000000000000000000000000000000000006e00027600000000,4,[0x3fffffffffffffffffffffff51f9d8ffffffffffffb739fffffffffffffffffffffffffffffffffffffffffffffffff37ffff3bfffffffffffffffffffffffffffffffe8ffcc7fffffffffffff18fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0xca0004000000000000184c0000000000000000000000000000000000000000000000000980000a000000001ffffffffffffffffffffffffff84c7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd89ffffffff,0x8c020600000000000000400000000000000000000000000000000000000000000000000c00000c000000001fffffffffffffffffffffffffffffffffffffffff9118fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x3fffffffffffffffffffffff31fcf8ffffffffffffe3b1fffffffffffffffffffffffffffffffffffffffffffffffff23ffff13ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff91fffd89ffffffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof169 : Floor 441 spec169 := floorChecked (by decide +kernel)
def book7 (i : ℕ) : {s : FloorData // Floor 441 s} := (if i≤3 then (if i≤1 then (if i≤0 then ⟨spec53,proof53⟩ else ⟨spec89,proof89⟩) else (if i≤2 then ⟨spec101,proof101⟩ else ⟨spec105,proof105⟩)) else (if i≤5 then (if i≤4 then ⟨spec149,proof149⟩ else ⟨spec153,proof153⟩) else (if i≤6 then ⟨spec164,proof164⟩ else ⟨spec169,proof169⟩)))
def spec201 : FloorData := (0x3f801f000000000000000000000006fc7000000000000000000000000000005e2380c6c000000000000000000000000000,4,[0x30001200000000000000000000000950800000000000000000000000000000280400850000000000000000000000000001fffffffffffff87fffffffffffffffffffffffffffe38ffffffffffffffffffffffffffffffddc7fffffffffffffffffffffffffffffff,0x11000000000000000000000000000180c00000000000000000000000000000300600040000000000000000000000000001ffffffffffffffffe0ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff393fffffffffffffffffffffffffff,0x3ffffffffffffcaffe5fffffffffffffffffffffff2271fffffffffffffffffffffffffffffc7f8ff7a7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9038fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x3ffffffffffffecfff9fffffffffffffffffffffffe3f1fffffffffffffffffffffffffffff47b8fff27fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa1dc7f393fffffffffffffffffffffffffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof201 : Floor 441 spec201 := floorChecked (by decide +kernel)
def spec204 : FloorData := (0x1c786e000000000000000000000013814b02d60000000000000000000000033826580000000000000000000000000000000,4,[0x180014000000000000000000000005001000a80000000000000000000000045008800000000000000000000000000000001fffffffffffff87fffffffffffffffffffffffffffeb4ffffffffffffffffffffffffffffffd9a7fffffffffffffffffffffffffffffff,0x81000000000000000000000000006001400200000000000000000000000006000a00000000000000000000000000000001fffffffffffffff91fffffffffffffffffffffffffffffd29fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x3ffffffffffff7afbbffffffffffffffffffffffd8ff69fed3ffffffffffffffffffffffff8fff4fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffec7eb4fd29fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x3fffffffffffe7cfe3fffffffffffffffffffffff8ffe9ff53fffffffffffffffffffffff98ff34ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffcc7d9a7fffffffffffffffffffffffffffffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof204 : Floor 441 spec204 := floorChecked (by decide +kernel)
def spec209 : FloorData := (0xf9c00001f000000000000000007f8c0000000000000000000000000000000f000000000d4c000000000000000000000000313,4,[0x80000001200000000000000000940000000000000000000000000000000002000000000810000000000000000000000000405fffffffffe63ffffffffffffffffffffffff873fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x42800000000000000000000000211000000000000000000000000000000014000000000200000000000000000000000000221ffffffffffffffffe0ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2b3fffffffffffffffffffffffffff,0x3fffffffff6f7ffffe5fffffffffffffffff09e7fffffffffffffffffffffffffffffff9fffffffff7e7ffffffffffffffffffffffffbd9fffffffffffffffffffffffffffffffffff8073ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffcec,0x3fffffffffbc7fffff9fffffffffffffffffcee7ffffffffffffffffffffffffffffffe1fffffffffd67ffffffffffffffffffffffffdd9ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0fffffffff2b3ffffffffffffffffffffffffcec])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof209 : Floor 441 spec209 := floorChecked (by decide +kernel)
def spec216 : FloorData := (0x1c019c0780000000000000000270005ac0001530000000000000000000003380000002a980000000000000000000000000000000,4,[0x8000001000000000000000000a00004000002400000000000000000000005000000001200000000000000000000000000000001fffffffffe63ffffffffffffffffffffffffa53fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x18002800000000000000000000c00015000002000000000000000000000046000000011000000000000000000000000000000001fffffffffffff87fffffffffffffffffffffffffffeacffffffffffffffffffffffffffffffd567fffffffffffffffffffffffffffffff,0x3fffffff7fef7fafffffffffffffffffb1fffda7ffff59ffffffffffffffffffffff8ffffffffecfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd8fffa53fffeacfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x3ffffffe7ffc7fcffffffffffffffffff1fffea7ffffd9fffffffffffffffffffff98fffffffeacffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffcc7ffffffd567fffffffffffffffffffffffffffffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof216 : Floor 441 spec216 := floorChecked (by decide +kernel)
def spec225 : FloorData := (0xfb80000000001f000000007f9800000000000000000000000000000001e00000000000000000e4c000000000000000032600000000,4,[0x8000000000001200000000940000000000000000000000000000000000400000000000000000810000000000000000040800000001ffffe47ffffffffffffffffffff867ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x4500000000000000000000212000000000000000000000000000000002800000000000000000400000000000000000024000000001ffffffffffffffffe0ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff1b3fffffffffffffffffffffffffff,0x3ffff6effffffffffe5ffffffff09cfffffffffffffffffffffffffffffffff3fffffffffffffffff7e7ffffffffffffffffbb3ffffffffffffffffffffffffffffffffff8067fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffcd9ffffffff,0x3ffffb8fffffffffff9ffffffffcecffffffffffffffffffffffffffffffffc3fffffffffffffffffb67ffffffffffffffffdb3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe1fffffffffffffffff1b3ffffffffffffffffcd9ffffffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof225 : Floor 441 spec225 := floorChecked (by decide +kernel)
def spec232 : FloorData := (0x381b8000000780000000017005b800000000000016300000000000037000000000000000033180000000000000000000000000000000,4,[0x1000000000010000000000a000400000000000000440000000000000a000000000000000002200000000000000000000000000000001ffffe47ffffffffffffffffffffa47ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x3005000000000000000000c001600000000000000400000000000004c000000000000000022000000000000000000000000000000001fffffffffffff87fffffffffffffffffffffffffffe9cffffffffffffffffffffffffffffffcce7fffffffffffffffffffffffffffffff,0x3ffefeefffffffafffffffffd1ffd8ffffffffffffff39fffffffffffff1fffffffffffffffffdcfffffffffffffffffffffffffffffffffffffffffffffffffffffffe8ffa47ffffffffffffe9cfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x3ffcff8fffffffcffffffffff1ffe8ffffffffffffffb9ffffffffffff91ffffffffffffffffd9cfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc8ffffffffffffffffcce7fffffffffffffffffffffffffffffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof232 : Floor 441 spec232 := floorChecked (by decide +kernel)
def spec109 : FloorData := (0x7fb7ebde00000000fb7fd77bf2fc00000001f6f7ffdbd7e00000000,5,[0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffff81906847fffffffeb986d149ba77fffffffd73135a4a53bfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc3c8f43ffffffffffc87e887fffffffffffff90fff243ffffffffff,0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffa890ecc3ffffffffddd4598ddb27fffffffdb3b21ccf513ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc48ffe1fffffffffff82887fd03fffffffffff81fffe81ffffffff,0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffff9b9a2843fffffffee9e753e91a47ffffffffdbdb906c5a3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff1421fffffffffffffffc0d03ffffffffffffe024281ffffffff,0x564d112800000000000022000400000000020c0c21302c000000001fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff048028840d03fffffffffffffffffffffffffff,0x646196300000000106082c060580000000000000018020000000001ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe09080024281ffffffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof109 : Floor 441 spec109 := floorChecked (by decide +kernel)
def spec117 : FloorData := (0xfff8000fffe000007ff0000000773dc0007dbde000017eddae0002ddb7,5,[0x40040000008200000000a0300002000400000a020180000280dffffffffffffffffffffffffffffffffffffffffffffffffffffc07ffffe03fffffffffffffffffffffffff247fffffff123ffffffffff,0x9500000cc8000000ba00000000cc1200006850000000c8b01000053049ffffffffffffffffffffffffffffffffffffffffffffffffffffff87fffffc1ffffffc0fffffffffc23ffffffa1ffffffffe51fffffe48,0x3ffffffffffffffffffffffffffffffffffffffffffffffffffffdbbfffe2843fffffd75fffffff91a47fffdeeebffffd06c5a3ffffc7f1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0001fffffffffffffff88c23ffffffffffffe812251ffffffff,0x3ffffffffffffffffffffffffffffffffffffffffffffffffffff62dffff316bfffff041fffffff11c47fff978f3fffff1747e3fffa4591ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff800fffffff88c23ffffffffffffffffffffffd2248,0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffceffffbe73fffffe79ffffffff1fc7fff1c8c3ffffd1a46a3fffe4691ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff82421ffffe812251fffd2248])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof117 : Floor 441 spec117 := floorChecked (by decide +kernel)
def book15 (i : ℕ) : {s : FloorData // Floor 441 s} := if i<8 then book7 i else (if i≤11 then (if i≤9 then (if i≤8 then ⟨spec201,proof201⟩ else ⟨spec204,proof204⟩) else (if i≤10 then ⟨spec209,proof209⟩ else ⟨spec216,proof216⟩)) else (if i≤13 then (if i≤12 then ⟨spec225,proof225⟩ else ⟨spec232,proof232⟩) else (if i≤14 then ⟨spec109,proof109⟩ else ⟨spec117,proof117⟩)))
def spec121 : FloorData := (0x1ff00783ff003e007bb82f0005dbb8036c00f8007e000ee0001f602dc01db,5,[0x100000400200002000280400050001000040001400002800280015ffffffffffffffffffffffffffffffffffffffffffffffffff80fffff80fffffff447ffffffe447fffffffffffffffffffffffffffffff,0x116000031a00000061500000030360004001700040001980000a005300091ffffffffffffffffffffffffffffffffffffffffffffffffffffff87fffffc1ffffffd0fffffffffc93ffffff81ffffffffe09fffffe24,0x3ffffffffffffffffffffffffffffffffffffffffffffffffffbbffbf891ffc3ffddeff5fff4598ffb27ffafffebfff23fffd13ffc7ffe9ffffffffffffffffffffffffffffffffffffffffffffffffffffffffc00ffc1fffffffffffa2447fc93fffffffffff11fffe09ffffffff,0x3ffffffffffffffffffffffffffffffffffffffffffffffffffddffdfeddffebff198fe1fff46a8ffd27ffcffff3fffe3ffffd3fe47fd49fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8447d0fffa2447fc93ffffffffffffffffffffd23fe24,0x3fffffffffffffffffffffffffffffffffffffffffffffffffee1ffefce1fff3ff9e8ff9fffc7c8fffa7fe0fff83ffe23fffe13fa47fe49fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff07ff81fff11fffe09fd23fe24])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof121 : Floor 441 spec121 := floorChecked (by decide +kernel)
def spec157 : FloorData := (0x7feff7fb3ffffedffdbe00000000000000000000000000000000000000000000000000001fdfdfe7f,5,[0x4281409406c8b5096a100000000000000000000000000000000000000000000000000000058686c1dfffffffffffffffffffffffffffffe1d0e87cc3e07f20fe41fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x3fffffffffffffffffffffffffffffec30dd09a35d225074fbffffffffffffffffffffffffffffffffffffffffffffffffffffeee477349ffffffffffffffffffffffffffffffe10ff84c3ff8120ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe03fd80,0x3ffffffffffffffffffffffffffffff5ba1809c39e3a7c44a3fffffffffffffffffffffffffffffffffffffffffffffffffffff77764391fffffffffffffffffffffffffffffffff0804c3ffffff0241ffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0180,0x3fffffffffffffffffffffffffffffb93c9e29f010026004c3fffffffffffffffffffffffffffffffffffffffffffffffffffff878783e1ffffffffffffffffffffffffffffffffffffffc0001200241fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x24120c60420c18183000000000000000000000000000000000000000000000000000000000000401fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe02020180])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof157 : Floor 441 spec157 := floorChecked (by decide +kernel)
def spec165 : FloorData := (0xffb18000000000000000dd8e00000000000000000000000000000000000000000000001709e2e00000000,5,[0x3fffffffffffffffffffffffff89dcffffffffffffffff6ef3ffffffffffffffffffffffffffffffffffffffffffffffdbee7bbfffffffffffffffffffffffffffffffffc7ce7ffffffffffffffffe71fffffffffffffffffffffffffffffffffffffffffffffffff63ffffffffff,0x90000000000000000000301800000000000000000000000000000000000000000000000c0301000000001ffffffffffffffffffffffffff84e7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdd1ffffffff,0x2202000000000000000000000000000000000000000000000000000000000000000000201004000000001fffffffffffffffffffffffffffffffffffffffffffff2271fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x3fffffffffffffffffffffffff4cfcffffffffffffffffc7e3ffffffffffffffffffffffffffffffffffffffffffffffd1ec7a3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe8f61d1ffffffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof165 : Floor 441 spec165 := floorChecked (by decide +kernel)
def spec172 : FloorData := (0x3173813800000000013806b00960000000000000000000000000000000000000000000670001ac0000000000,5,[0x20010000000000000050010002800000000000000000000000000000000000000000000a0000500000000001fffffffffffffffffffffffe8ffec7fffffffffffff94fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x3fffffffffffffffffffffffdb8fdcffffffffffdeff7dfef3fffffffffffffffffffffffffffffffffffffffffffbdfffee7fffffffffffffffffffffffffffffffffffc7ec7fffffffffffffffff69ffffffffffffffffffffffffffffffffffffffffffffffffe53ffffffffff,0x3ffffffffffffffffffffffdddafdeffffffffffd8ff69fed3ffffffffffffffffffffffffffffffffffffffffffff1ffffa7fffffffffffffffffffffffffffffffffffffffffffffffffec7f94ff69fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x204020000000000020008001000000000000000000000000000000000000000000000000000000000000001ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff98fffe53ffffffffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof172 : Floor 441 spec172 := floorChecked (by decide +kernel)
def spec180 : FloorData := (0x1938003815800013815c00000000a6000000000000000000000000000000000000001b800000002cc0000000000,5,[0x1000001000000005002000000000480000000000000000000000000000000000000005000000000900000000001ffffffffffffffffffffec7ffffea7ffffffea3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x3ffffffffffffffffffffddfff8fdcffffdefdf7fffffffef3ffffffffffffffffffffffffffffffffffffffeeffffffffee7fffffffffffffffffffffffffffffffffffc7ea7fffffffffffffffff59ffffffffffffffffffffffffffffffffffffffffffffffffd33ffffffffff,0x3fffffffffffffffffffedefffafdeffffd8fdc7fffffffeb3fffffffffffffffffffffffffffffffffffffff8fffffffff67fffffffffffffffffffffffffffffffffffffffffffec7ea3ffffffff59fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x200004020000020020000000001000000000000000000000000000000000000000000000000000000000000001fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe47fffffffd33ffffffffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof180 : Floor 441 spec180 := floorChecked (by decide +kernel)
def spec185 : FloorData := (0x3e778ff07b781f7007b6c006ef70000000000000000000000000000000000000000f8003e000ee0002f602dc02db,5,[0x801400940028000940000950800000000000000000000000000000000000000001000040001400042800280415ffffffffffffffffffe1e87e0ffc87fc8fffc93ffff08fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x3ffffffffffffffffffef18edbf094fdbbff0967ff3a7dffffffffffffffffffffffffffffffffffffffff7fffc3fffbbfffab3ff77fad9ffffffffffffffffffff887fff8487fffff8493ffffffffffffffffffffffffffffffffffffffffffffffffffc1ffffffffd09fffffd24,0x3fffffffffffffffffff75de11f098fd3dff29f7ff2231ffffffffffffffffffffffffffffffffffffffffafffebfff23fffb13ffc7fbe9fffffffffffffffffffffff00f8487fffffffffff9108fffffffffffffffffffffffffffffffffffffffffffffffff11fffd09ffffffff,0x3fffffffffffffffffffb5ee9df29efc31ff09a7ff2251ffffffffffffffffffffffffffffffffffffffffcffff3fffe3fffbd3fe47fb49ffffffffffffffffffffffffffffffe08ff8493ff9108ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd23fd24,0xa01200c60024000c60000c18000000000000000000000000000000000000000000000000000000040000000401fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff07ffc1fff11fffd09fd23fd24])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof185 : Floor 441 spec185 := floorChecked (by decide +kernel)
def spec205 : FloorData := (0x3fffeff000000000000000000003f7ffcfffde0000000000000000000000fb7fe67bfcfc000000000000000000000000000,5,[0x3fffffffffffc305213ffffffffffffffffffffed8b5696a53fffffffffffffffffffffeb986b349ae77ffffffffffffffffffffffffffffffffffffffe38791ffffffffffffffffffffffe87e30fc21fffffffffffffffffffffffc87d987fffffffffffffffffffffffffffffff,0x3fffffffffffd803341ffffffffffffffffffffb5d207070fbffffffffffffffffffffffddd43b8dc727fffffffffffffffffffffffffffffffffffffffc07fe0fffffffffffffffffffffff8030fffffffffffffffffffffffffffff81987f303fffffffffffffffffffffffffff,0x3fffffffffffc910201ffffffffffffffffffffb9e387c4063fffffffffffffffffffffee9e733e90647fffffffffffffffffffffffffffffffffffffffff8100fffffffffffffffffffffffffff0021fffffffffffffffffffffffffffffc0303fffffffffffffffffffffffffff,0x34aa9a40000000000000000000000002000480000000000000000000000106084c061180000000000000000000000000001ffffffffffffffffffffffffffffffffffffffc0800300021fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x26ccc3800000000000000000000420c38187000000000000000000000000000040001800000000000000000000000000001fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff048019840303fffffffffffffffffffffffffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof205 : Floor 441 spec205 := floorChecked (by decide +kernel)
def spec213 : FloorData := (0x3ffbc007fff000000000000000fbff9c000000dfee00000000000000000007df000000077ddc00000000000000000000002df37,5,[0x8000050120000000000000014094000000012a10000000000000000000008200000000a830000000000000000000000002c0dfffffffe0e43fff81ffffffffffffffffe47863fffffffc11fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x3fffffffd60c7ff3341ffffffffffffffedd00e7fffffe70fbfffffffffffffffffffbe1fffffffdc567fffffffffffffffffffffff71d9fffffffff043ffffe0fffffffffffffffff8063ffffffffffffffffffffffffffffffe0fffffffff223ffffffffffffffffffffffffcc8,0x3fffffffda4efff0201ffffffffffffffe9e21f7fffffe4063fffffffffffffffffffd75fffffff90647fffffffffffffffffffffffc3f1ffffffffffffff8000fffffffffffffffffffffffffff2011fffffffffffffffffffffffffffff88223fffffffffffffffffffffffffff,0x3ffffffffd6f7ffaba5ffffffffffffffe1809c7fffffe44a3fffffffffffffffffffe79ffffffff17c7ffffffffffffffffffffffe4391fffffffffffffffffffffffffffffffff040063ffffff2011ffffffffffffffffffffffffffffffffffffffffffffffffffffffffd20c8,0x21b0000cc3800000000000000120ce0000000187000000000000000000000000000000001800000000000000000000000000401ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff820fffffff88223ffffffffffffffffffffffd20c8])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof213 : Floor 441 spec213 := floorChecked (by decide +kernel)
def book23 (i : ℕ) : {s : FloorData // Floor 441 s} := if i<16 then book15 i else (if i≤19 then (if i≤17 then (if i≤16 then ⟨spec121,proof121⟩ else ⟨spec157,proof157⟩) else (if i≤18 then ⟨spec165,proof165⟩ else ⟨spec172,proof172⟩)) else (if i≤21 then (if i≤20 then ⟨spec180,proof180⟩ else ⟨spec185,proof185⟩) else (if i≤22 then ⟨spec205,proof205⟩ else ⟨spec213,proof213⟩)))
def spec220 : FloorData := (0x7df1bdc787e0000000000001e2f1f85bc1b815b02f6000000000000003f87780007b82ed80000000000000000000000000000000,5,[0x3ffffffc57cc5f0f37ffffffffffffefb1ddf4a7ddfd59fafbffffffffffffffdbf98ffffddfaacffffffffffffffffffffffffffffffffffffffe3fe43f87ffffffffffffffffd0fffa43fffea4fffffffffffffffffffff887ffffffd127fffffffffffffffffffffffffffffff,0x48000081000000000000000341a0800401600340020000000000000000d00d000016001a00000000000000000000000000000001fffffffe0e43fff81ffffffffffffffffe07a43fffffffd09fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x3ffffffddbcec70f23fffffffffffffbbddef5f7d8fd69fa53ffffffffffffffeefdeffff98fb34fffffffffffffffffffffffffffffffffffffffffffe38781ffffffffffffffffffffffe47ea4fd09fffffffffffffffffffffff847d127fffffffffffffffffffffffffffffff,0x3ffffffb7def77afbbffffffffffffc3a1d0fd87c8ff49fe93fffffffffffffff0ff0ffffe8ffe4fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe1d0e07a43e47ea4fd09fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x2203020c0c00000000000000040200a0020028005000000000000000000000000000040000000000000000000000000000000001fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc07887fff847d127fffffffffffffffffffffffffffffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof220 : Floor 441 spec220 := floorChecked (by decide +kernel)
def spec241 : FloorData := (0xfc0ff800fdc00001f007b80007fd8000007fcc00000000000000078000003e0000002f000000000f4c0000005e000000003a600000393,5,[0x8000080000001200800000940000000940000000000000000000000000400000002000000000810000000040000000040800000405f83fe07ffe23ffffffffe47ffff827ffffff833fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x3f5fe08ffe4efffffc1ff5dffff00cffffff21f7fffffffffffffffbffffffc3fffffff5ffffffffe367ffffffebffffffff9b3fffffbf9ffff007fffffffffe0ffffffff8027fffffffffffffffffffffffffffffffc1fffffffffffffffff0b3ffffffffffffffffc59ffffffff,0x3f6fe4dffe0c7ffffc1ff5effff21effffff00e7fffffffffffffffdffffffebffffffe1ffffffffe567fffffff3ffffffffbf3fffff9d9fffffffff023ffffe0fffffffffffffffff8033ffffffffffffffffffffffffffffffd0fffffffff0b3ffffffffffffffffffffffffc6c,0x3ff7f6efff6f7ffffe5ff18ffff094ffffff0967fffffffffffffffefffffff3fffffff9fffffffff7e7ffffffc3ffffffffab3fffffad9ffffffffffffffffffff847fff8027fffff8033ffffffffffffffffffffffffffffffffffffffffffffffffffa1ffffffffc59fffffc6c,0x801b0001b0000003800a00000ce0000000ce0000000000000000000000000000000000000000001800000000000000000040000000401ffffffffffffffffffffffffffffffffffffffffffffffffffffff87fffffc1ffffffd0fffffffff0b3ffffffa1ffffffffc59fffffc6c])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof241 : Floor 441 spec241 := floorChecked (by decide +kernel)
def spec248 : FloorData := (0xc7f81f9c01dc0780001e1f81f005f80370005ec000173000007f000007f0000000bb80000003b980000000000000000000000000000000,5,[0x8010000800000100002c0801a0004002a0000400000640000016000001a000000015000000003200000000000000000000000000000001f83fe07ffe23ffffffffe07ffffa07ffffffa13fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x3f58fc8dffceff0fffff7ddfd1ff48ffbdfff5f7fffd39fffffbbfffff91fffffffdefffffff99cffffffffffffffffffffffffffffffffffc7e07ffffff87ffffffffe0ffa07ffffffffffffe8cffffffffffff80ffffffffffffffffc467fffffffffffffffffffffffffffffff,0x3f6bfcdc7fcc7f0fffffbdefddff5effb1fff4a7fffd59fffffddfffffddfffffff98fffffffaacffffffffffffffffffffffffffffffffffffffe3fe23f87ffffffffffffffffc8fffa13fffe8cfffffffffffffffffffff447ffffffc467fffffffffffffffffffffffffffffff,0x37f6feef7fef7faffffc3d0fc1ffd0ff91fffd27ffff19fffffe1fffffe1fffffffe8ffffffffccffffffffffffffffffffffffffffffffffffffffffffffffffe1e07e0ffa07fc8fffa13fffe8cfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x840302003000c0000002002000a00040000a0000028000000000000000000000000000000040000000000000000000000000000000001ffffffffffffffffffffffffffffffffffffffffffffffffff80fffff80fffffff447ffffffc467fffffffffffffffffffffffffffffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof248 : Floor 441 spec248 := floorChecked (by decide +kernel)
def spec173 : FloorData := (0x7f7ffb38000000003f7feeffd9e000000000000000000000000000000000000000001f6f7ff1be7e00000000,6,[0x3ffffffffffffffffffffff95189d8fffffffffed8b7296ed3fffffffffffffffffffffffffffffffffffffffffd73135bca73bffffffffffffffffffffffffffffffce8c7cc7fffffffffe87f10fe61fffffffffffffffffffffffffffffffffffffffffff90fffe43ffffffffff,0x3ffffffffffffffffffffffa109098fffffffffb5d223074fbfffffffffffffffffffffffffffffffffffffffffdb3b21dcf313fffffffffffffffffffffffffffffff08f84c7fffffffffff8110fffffffffffffffffffffffffffffffffffffffffffffffff81fffd81ffffffff,0x3ffffffffffffffffffffffeda009cfffffffffb9e3a7c44e3ffffffffffffffffffffffffffffffffffffffffffdbdb91ec3a3fffffffffffffffffffffffffffffffff004c7fffffffffffffff0261ffffffffffffffffffffffffffffffffffffffffffffffe0e4181ffffffff,0x48c2206000000000000004000000000000000000000000000000000000000000000020c0c20300c000000001ffffffffffffffffffffffffffffffffffffffc0801100261fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x1214c60000000000420c18183000000000000000000000000000000000000000000000000000040000000001ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe090800e4181ffffffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof173 : Floor 441 spec173 := floorChecked (by decide +kernel)
def spec181 : FloorData := (0x1f3800ffb58000f3fb5c000000ddae000000000000000000000000000000000000071b9e0000172deae0000deb7,6,[0x80001894000014094000000012a1000000000000000000000000000000000000002000400000a0241800002c0c0000000000000000000060000c7800000e07800000000dc0000000000000000000000000000000000000007001e000017002ae0000deb7,0x10000090000000c50020000000305800000000000000000000000000000000000006050000000c0b01000013049ffffffffffffffffffff8c7fff84a7fffff84a3ffffffffffffffffffffffffffffffffffffffffffffffffffe1ffffffffd51fffffd48,0x3ffffffffffffffffffff5dffe009cfffe9e29f7fffffe44e3fffffffffffffffffffffffffffffffffffffdeeebffffd1ec3a3ffffc3f1fffffffffffffffffffffffff004a7fffffffffffffff2251ffffffffffffffffffffffffffffffffffffffffffffffe8d2151ffffffff,0x3fffffffffffffffffffe5effe229efffe1809c7fffffe44a3fffffffffffffffffffffffffffffffffffff9f8f3fffff1f43e3fffe4391fffffffffffffffffffffffffffffffff0c04a3ffffff2251fffffffffffffffffffffffffffffffffffffffffffffffffffffffff2148,0xa00014c60000120c60000000183000000000000000000000000000000000000000000000000000040000000401ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8e461ffffe8d2151ffff2148])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof181 : Floor 441 spec181 := floorChecked (by decide +kernel)
def spec188 : FloorData := (0xdf97b1f38179e3f17817c1b807b00b600000000000000000000000000000000007f003f800f70003ec0000000000,6,[0x810020010002c100d00201500100068000000000000000000000000000000000016000d0002a0000d00000000001ffffffffffffffffffe1e87e0ffe87fc0fffe83ffff84fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x3ffffffffffffffffffecd8fdb8fd4f7bbd8fd47deff7dfeb3ffffffffffffffffffffffffffffffffffbbffc8fffbdfffa67fffffffffffffffffffffffffffffe687ffc7e87fffe87e83ffffffff49ffffffffffffffffffffffffffffffffffffffc07fffffffc13ffffffffff,0x3fffffffffffffffffff7dd9d18fd8fbbddefdf7d8ff29fed3ffffffffffffffffffffffffffffffffffddffeefff31fffca7ffffffffffffffffffffffffffffffffce0c7e87fffffffffe47f84ff49fffffffffffffffffffffffffffffffffffffffffff08fffc13ffffffffff,0x3ffffffffffffffffff7adedddafdec3a1d0fd87c8ff49fe93ffffffffffffffffffffffffffffffffffe1fff0fffd1ffff27fffffffffffffffffffffffffffffffffffffffe1c0e87e83e47f84ff49fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x200204020004020020020008001000000000000000000000000000000000000000000000000000000000000001fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80ffc07ff08fffc13ffffffffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof188 : Floor 441 spec188 := floorChecked (by decide +kernel)
def book29 (i : ℕ) : {s : FloorData // Floor 441 s} := if i<24 then book23 i else (if i≤26 then (if i≤25 then (if i≤24 then ⟨spec220,proof220⟩ else ⟨spec241,proof241⟩) else ⟨spec248,proof248⟩) else (if i≤28 then (if i≤27 then ⟨spec173,proof173⟩ else ⟨spec181,proof181⟩) else ⟨spec188,proof188⟩))
def spec125 : FloorData := (0x1ffffffffffffffffffffffffffdffff3ffffffffffffffffffdfffffffdff,7,[0x8100400480200082b0868041a0710012000561035a020385868681c0000000000000000000000000000000000000000000000000180c07c380e03fc07007fff807c007f3ff80ff007ff00fff001fffffffdff,0x1400950a800cc83db088ba1ddd4088dc12316068d01a3a21c8f012ea477049fffffffffffffffffffffffffffffffffffffffffffffffffe00ff87c00ffc1ff8007c0fff82007fc03ff07ff81fff01fffe01fc03fe00,0xd160009b1a00018d61d000e1e703e10047bb704843dbdb90240a377724091ffffffffffffffffffffffffffffffffffffffffffffffffffff0007fff0001fffff800fffffff80c03fff80001ffffe000201fffc0200,0x3ffffffffffffffffffffffffffffffffffffffffffffffffffbbdbb009028436edded74090051081a06ddadeee812100048503878787e1fffffffffffffffffffffffffffffffffffffffffffffffffffffff80000001ffffffff000020000c03fffffffe00000000201ffffffff,0x3ffffffffffffffffffffffffffffffffffffffffffffffffebdd62d56dd316800110040000062001c04e1c970f21c1c21707c004000501ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe00000000000020000c03ffffffffffffffffffe00000200,0x3fffffffffffffffffffffffffffffffffffffffffffffffff2e1fce64e1be72709e0e790e087c0e1f80000180800000018060000040601ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc000000000000000020000000200])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof125 : Floor 441 spec125 := floorEx (audit_off (db:=book29) (branches:=guides) (g:=2) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def book30 (i : ℕ) : {s : FloorData // Floor 441 s} := if i<24 then book23 i else (if i≤27 then (if i≤25 then (if i≤24 then ⟨spec220,proof220⟩ else ⟨spec241,proof241⟩) else (if i≤26 then ⟨spec248,proof248⟩ else ⟨spec173,proof173⟩)) else (if i≤29 then (if i≤28 then ⟨spec181,proof181⟩ else ⟨spec188,proof188⟩) else ⟨spec125,proof125⟩))
def spec217 : FloorData := (0x1c0f9c3f801f0000000000001e7007fac006fd70000000000000000000073380f0005eab80d6c000000000000000000000dc035b,7,[0x80030001200000000000028000940000950800000000000000000000200002000280400850000000000000000000000280414000000000e0038001f0000000000001c0007800006e000000000000000000000070000f0005c0000d6c000000000000000000000dc035b,0x8000011000000000000000018a00004000182c00000000000000000000605000000301600040000000000000000000001300091fffffffff063ffffe0fffffffffffffffff8053fffffffffffffffffffffffffffffff0fffffffff293ffffffffffffffffffffffffca4,0x18042800000000000000000010c00215000002000000000000000000000c460140000110002000000000000000000000018002a1ffffffffffffc07fe0fffffffffffffffffffffff9028fffffffffffffffffffffffffffffa1547f293fffffffffffffffffffffffffff,0x3fffffff7f6f7caffe5ffffffffffffc31ff09a7ff2251ffffffffffffffffffff9f8ff9fffc7e8ff7a7ffffffffffffffffffffe47fb49ffffffffffffffffffffffffffffffe18ff8053ff9028fffffffffffffffffffffffffffffffffffffffffffffffffffffffffff23fca4,0x3ffffffe7fbc7ecfff9ffffffffffffe71ffcea7ffe3d1ffffffffffffffffffff198fe1fff46a8ffd27ffffffffffffffffffffe47fd49fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8cc7f0fffa1547f293fffffffffffffffffffff23fca4])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof217 : Floor 441 spec217 := floorEx (audit_off (db:=book30) (branches:=guides) (g:=14) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def book31 (i : ℕ) : {s : FloorData // Floor 441 s} := if i<24 then book23 i else (if i≤27 then (if i≤25 then (if i≤24 then ⟨spec220,proof220⟩ else ⟨spec241,proof241⟩) else (if i≤26 then ⟨spec248,proof248⟩ else ⟨spec173,proof173⟩)) else (if i≤29 then (if i≤28 then ⟨spec181,proof181⟩ else ⟨spec188,proof188⟩) else (if i≤30 then ⟨spec125,proof125⟩ else ⟨spec217,proof217⟩)))
def spec229 : FloorData := (0x7fb800000007eff0000000fff98000000000000000dfce0000000000ebde00000000000000037edc00000000000017c9f2e00000000,7,[0x800000000050120000001894000000000000000012a10000000000040040000000000000000a8300000000000000a02418000000000000e000000000781f0000000c7800000000000000000dc000000000000e01e00000000000000037edc000000000000170032e00000000,0x20000000000314000000009000000000000000000030980000000000c4800000000000000004c1200000000000000c8301000000001ffff047fffffffffe0ffffffff8067fffffffffffffffffffffffffffffffe1fffffffffffffffff123ffffffffffffffffcd1ffffffff,0x44500000000000000000002212000000000000000000000000000001112800000000000000000400000000000000211024000000001ffffffffffffff8100fffffffffffffffffffffffffff2031fffffffffffffffffffffffffffffc8123fffffffffffffffffffffffffff,0x3ffff6effffffffaba5ffffffe009cfffffffffffffffe44e3ffffffffffbe73ffffffffffffffff17c7ffffffffffffd1ec3a3fffffffffffffffffffffffffffffffff00067fffffffffffffff2031ffffffffffffffffffffffffffffffffffffffffffffffe8360d1ffffffff,0x3fff9b8ffffffffce39fffffff4cecffffffffffffffffc763fffffffffe2843fffffffffffffff91a47ffffffffffffd06c5a3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff1421fffffffffffffffc8123ffffffffffffe8360d1ffffffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof229 : Floor 441 spec229 := floorEx (audit_off (db:=book31) (branches:=guides) (g:=24) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def book32 (i : ℕ) : {s : FloorData // Floor 441 s} := if i<32 then book31 i else ⟨spec229,proof229⟩
def spec233 : FloorData := (0x38fb8000003f801f00000f707fb8000000000006fe7000000000003b7001e000000000005f3380e6c000000000006e00037600000000,7,[0x80000000300012000014009400000000000009508000000000001000004000000000002804008500000000000014000428000000000000e000000038001f00000e007800000000000006e0000000000000380001e000000000005c0000e6c000000000006e00037600000000,0x100000000011000000000ca0004000000000000184c0000000000030a00000000000000030260004000000000000980000a000000001ffff047fffffffffe0ffffffff8047fffffffffffffffffffffffffffffffe1fffffffffffffffff193ffffffffffffffffc89ffffffff,0x3045000000000000000008c021600000000000000400000000000064c00280000000000002200040000000000000c00002c000000001ffffffffffffc07fe0fffffffffffffffffffffff9018fffffffffffffffffffffffffffffa0cc7f193fffffffffffffffffffffffffff,0x3ffef6effffffcaffe5ffffe11f098ffffffffffff2231fffffffffffcf1fff3fffffffffffc7d8ff7a7fffffffffff23fffb13fffffffffffffffffffffffffffffff08f8047fffffffffff9018fffffffffffffffffffffffffffffffffffffffffffffffff91fffc89ffffffff,0x3ffcfb8ffffffecfff9fffff31fce8ffffffffffffe3b1fffffffffff891ffc3fffffffffff4598ffb27fffffffffff23fffd13ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc48ffe1fffffffffffa0cc7f193fffffffffff91fffc89ffffffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof233 : Floor 441 spec233 := floorEx (audit_off (db:=book32) (branches:=guides) (g:=32) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def book33 (i : ℕ) : {s : FloorData // Floor 441 s} := if i<32 then book31 i else (if i≤32 then ⟨spec229,proof229⟩ else ⟨spec233,proof233⟩)
def spec236 : FloorData := (0x3f1b800001c786e00000317385b800000000013816b02d60000003c370bc00000000003383758000000000000067000dac0000000000,7,[0x20000000180014000002001000000000000005001000a800000028000480000000000450088000000000000000a0008500000000000000700000001c006e000003003800000000000013800002d60000003c000bc00000000003380000000000000000067000dac0000000000,0x1000000000810000000060a000400000000000600540020000000180a000000000000006002a000000000000008c0002400000000001fff8e47ffffffff91ffffffffc7a47ffffffffffffffffd29fffffffffff43fffffffffffffffffffffffffffffffffff253ffffffffff,0x3405000000000000000040c201600000000000000400000000000504c110000000000000022000000000000000c00013000000000001fffffffffffe38791ffffffffffffffffffffffec7e94fd29fffffffffffffffffffffffcc7c8a7fffffffffffffffffffffffffffffff,0x3ffefeeffffff7afbbfffff9d18fd8ffffffffffd8ff29fed3ffffffe7f1fe7fffffffffff8ffd4ffffffffffffff31fffca7ffffffffffffffffffffffffffffffffce8c7a47fffffffffec7e94fd29fffffffffffffffffffffffffffffffffffffffffff98fff253ffffffffff,0x3ffc9f8fffffe7cfe3fffff9f1cfe8fffffffffff8ffa9ff53ffffff8791e87ffffffffff98fd14ffffffffffffff31ffe4a7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc3c8f43ffffffffffcc7c8a7fffffffffffff98fff253ffffffffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof236 : Floor 441 spec236 := floorEx (audit_off (db:=book33) (branches:=guides) (g:=40) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def book34 (i : ℕ) : {s : FloorData // Floor 441 s} := if i<32 then book31 i else (if i≤33 then (if i≤32 then ⟨spec229,proof229⟩ else ⟨spec233,proof233⟩) else ⟨spec236,proof236⟩)
def spec189 : FloorData := (0xfff7fffffb7fffff7fb7ffffefffdbe0000000000000000000000000000000003ffff3fbfffffff3fefffffdfeff,8,[0x8094189404281409406c8b5096a1000000000000000000000000000000000010012000561035a0243858686c1c00000000000000000020604e0c78061c0e07803e07e00fc00000000000000000000000000000000000380ff003ff00fff002fffffdfeff,0x8100a009000ec10cd00235d20107078000000000000000000000000000000000316060d01a3a21c0f012ea437049ffffffffffffffffffc188700f8487e00ff8483ff8100ffffffffffffffffffffffffffffffffffffffff07ffc1fff01fffd01fc03fd00,0x3ffffffffffffffffffec18eda0094f5ba1809439e3a7c44a3ffffffffffffffffffffffffffffffffffbb71c8c3dbdb91a42a377764291fffffffffffffffffffe087ff00487fff080483ffffff0241fffffffffffffffffffffffffffffffffffff8c041ffffe0c0101fffe0100,0x3fffffffffffffffffff75d0100098b93c9e29f010022004c3fffffffffffffffffffffffffffffffffeddadeee8121001c8303878783e1ffffffffffffffffffffff80000487ffffffffc0001000241fffffffffffffffffffffffffffffffffffffffffe000000c0101ffffffff,0x3ffffffffffffffffff7a5e49c229e00201009800002400483fffffffffffffffffffffffffffffffffce1c9f0f21c1c21f03c004040301fffffffffffffffffffffffffffff80000804800001000241ffffffffffffffffffffffffffffffffffffffffffffffffffffe00020100,0xa01214c60024120c60420c18183000000000000000000000000000000000000000000000000000040000000401ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0000c040000000c010000020100])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof189 : Floor 441 spec189 := floorEx (audit_off (db:=book34) (branches:=guides) (g:=64) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def book35 (i : ℕ) : {s : FloorData // Floor 441 s} := if i<32 then book31 i else (if i≤33 then (if i≤32 then ⟨spec229,proof229⟩ else ⟨spec233,proof233⟩) else (if i≤34 then ⟨spec236,proof236⟩ else ⟨spec189,proof189⟩))
def spec221 : FloorData := (0x7fffbfffffff000000000007fefffffbfffffdffffe00000000000001fff77fdfffffeefffdfc0000000000000000001fdffff7f,8,[0x804305012000000000004281409406c8b5096a100000000000000080200082b0868041a870000000000000000000058686c1c000000020e0238781f0000000000061c0e07803e07e00fc0000000000000001c07007dff807c007fdfc0000000000000000001fdffff7f,0x3ffffffc560c5803341fffffffffffec30dd00a35d205070fbffffffffffffffdb198be1ddd42a8dc527ffffffffffffffffffeee477149ffffffe3f043c07fe0ffffffffffffe10ff8043ff8020ffffffffffffffffffff8887e0fff81107f203ffffffffffffffffffffe03fc80,0x48000491000000000000000f59a0800439e383c4020000000000000018d60d000e1e701e10040000000000000000000373724091fffffffc0043ff8000fffffffffffffff000043ffffff0001fffffffffffffffffff820fffffff80203ffffffffffffffffffffffc0080,0x3ffffffdda4e8000201fffffffffffb93c9e21f01000600043ffffffffffffff6edded74090033080607fffffffffffffffffff878783e1fffffffffffc000000ffffffffffffffffffffc0000200001ffffffffffffffffffffff000011000203fffffffffffffffffffffffffff,0x3ffffffb7d6f34aaba5fffffffffff00201009800002400483fffffffffffffe709f0e790e087e0e1787ffffffffffffffffffc04040301fffffffffffffffffffffffffffff80100000400000200001ffffffffffffffffffffffffffffffffffffffffffffffffffffe02000080,0x221b026ccc3800000000000024120ce0420c38187000000000000000000000000000040001800000000000000000000000000401ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe00088020000011000203ffffffffffffffffffe02000080])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof221 : Floor 441 spec221 := floorEx (audit_off (db:=book35) (branches:=guides) (g:=63) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def book36 (i : ℕ) : {s : FloorData // Floor 441 s} := if i<32 then book31 i else (if i≤34 then (if i≤33 then (if i≤32 then ⟨spec229,proof229⟩ else ⟨spec233,proof233⟩) else ⟨spec236,proof236⟩) else (if i≤35 then ⟨spec189,proof189⟩ else ⟨spec221,proof221⟩))
def spec245 : FloorData := (0x3fc7ff83fffc007fff01fb800fffd8000fbffdc000000dfee000fff8000fffe000007ff000000077fdc0007dbde000017edfae0002dfb7,8,[0x800008000050120080001894000014094000000012a10000000000040040000008200000000a8300002000400000a0241800002c0c0800e0020e0000781f0060000c7800000e07800000000dc00000c078000e03e000007ff000000077fdc0007005e000017003ae0002dfb7,0x200200056040003340010000090000000d5002000000030d80009500000cc8000000ba00000000cc1200006850000000c8b01000053049f03f007ff003ffffe0ff847fff8027fffff8023fffffffffffffff87fffffc1ffffffc0fffffffff023ffffffa1ffffffffc51fffffc48,0x3f5f008fda4efff0201ff5dffe000cfffe9e21f7fffffe4063fffdbbfffe2843fffffd75fffffff90247fffdeeebffffd06c1a3ffffc3f1fff8007fffffff8000fffffff00027fffffffffffffff2011ffffffffff0001fffffffffffffff88023ffffffffffffe812051ffffffff,0x3d6f44df80087ff0001fe5effe221efffe0800c7fffffe4023fff62dffff316bfffff041fffffff10447fff978f3fffff1743e3fffa4191fffffffc0003ff8000fffffffffffffff040023ffffff2011fffffffffffffffffff800fffffff88023ffffffffffffffffffffffd2048,0x3ff7f6effd6f7ffaba5fc18ffe0094fffe180947fffffe44a3ffffceffffbe73fffffe79ffffffff17c7fff1c8c3ffffd1a42a3fffe4291fffffffffffffffffffe047ff00027fff040023ffffff2011fffffffffffffffffffffffffffffffffffff82421ffffe812051fffd2048,0x809b0021b0000cc3800a00014ce0000120ce0000000187000000000000000000000000000000001800000000000000000040000000401ffffffffffffffffffffffffffffffffffffffffffffffffffff0007fff0001fffff800fffffff88023fff82421ffffe812051fffd2048])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof245 : Floor 441 spec245 := floorEx (audit_off (db:=book36) (branches:=guides) (g:=65) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def book37 (i : ℕ) : {s : FloorData // Floor 441 s} := if i<32 then book31 i else (if i≤34 then (if i≤33 then (if i≤32 then ⟨spec229,proof229⟩ else ⟨spec233,proof233⟩) else ⟨spec236,proof236⟩) else (if i≤36 then (if i≤35 then ⟨spec189,proof189⟩ else ⟨spec221,proof221⟩) else ⟨spec245,proof245⟩))
def spec249 : FloorData := (0xcff8ff9c0fdc3f801f3e7f8ff07ff81f7007fec006ff700001ff00783ff003e007bb82f0005fbb80f6c00f8007e000ee0003f602dc03db,8,[0x80000800300012008014009400280009400009508000000000001000004002000020002804008500010000400014000428002804140800e0000e0038001f20600e0078001c0007800006e0000001800078380003e0070002f0005c0000f6c00f8007e000ee0003f602dc03db,0x8010000800001100006c080da000401aa00004000186c0000116000031a00000061500000030360004001700040001980000a005300091f03f007ff023ffffe0ff807fff8007fffff8013fffffffffffffff87fffffc1ffffffd0fffffffff093ffffff81ffffffffc09fffffc24,0x3f58e08dfe4ef80ffc1f75de11f008fd3dff21f7ff2031fffffbbffbf891ffc3ffddeff5fff4198fe327ffafffebfff23fff913ffc7fbe9ffc7007fffffc07fe0fffff00f8007fffffffffff9008fffffffffffc00ffc1fffffffffffa0447f093fffffffffff11fffc09ffffffff,0x3f6be4dc7e0c780ffc1fb5ee9df21efc31ff00a7ff2051fffffddffdfeddffebff198fe1fff42a8fe527ffcffff3fffe3fffbd3fe47f949ffffffe3f023c07fe0ffffffffffffe08ff8013ff9008ffffffffffffffffffff8447d0fffa0447f093ffffffffffffffffffffd23fc24,0x37f6f6ef7f6f7caffe58310e01f090fc11ff0927ff2211ffffee1ffefce1fff3ff9e8ff9fffc7c8ff7a7fe0fff83ffe23fffa13fa47fa49ffffffffffffffffffc180700f8007e08ff8013ff9008ffffffffffffffffffffffffffffffffffffffff07ff81fff11fffc09fd23fc24,0x841b0201b006c003800a01200ce0024000ce0000c38000000000000000000000000000000040001800000000000000000040000000401fffffffffffffffffffffffffffffffffffffffffffffffffe00ff87c00ffc1ff8447d0fffa0447f093ff07ff81fff11fffc09fd23fc24])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof249 : Floor 441 spec249 := floorEx (audit_off (db:=book37) (branches:=guides) (g:=63) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def book38 (i : ℕ) : {s : FloorData // Floor 441 s} := if i<32 then book31 i else (if i≤35 then (if i≤33 then (if i≤32 then ⟨spec229,proof229⟩ else ⟨spec233,proof233⟩) else (if i≤34 then ⟨spec236,proof236⟩ else ⟨spec189,proof189⟩)) else (if i≤37 then (if i≤36 then ⟨spec221,proof221⟩ else ⟨spec245,proof245⟩) else ⟨spec249,proof249⟩))
def spec252 : FloorData := (0xf7ff1ffdf1fdc787e0df9fb1f385f9e3f1f85fc1b817b02f7e7f3f83c7f1fc03f8ff80007b83fd800007f00ff800f7000fec0000000000,8,[0x200200c16041800340810020010002c101d002015001000e940015028000c805b0880000d500880000016008d0002a0008d0000000000030070061f001c007e0c18030038001e001f80001b800002f7e003f83c001fc03f80000007b8000000007f00ff800f7000fec0000000000,0x801000480000810001ac0861a0004343a0800401600740020c16000181a00000d01d000016003a00000ba0048001ac0002400000000001c838e07e0e03fff81ffe607ffc7a07fffe07a03fffffffd09fffc07ffffe03fffffffffffffffffffffffff007fffffff013ffffffffff,0x3f581c8ddbcec70f23ff7dd9d18f48fbbddef5f7d8fd29fa53fbbdbf8791e87feefdeffff98f914fffffddffeefff31ffe4a7ffffffffffffc0e07ffffe38781fffffce0c7a07fffffffffe47e84fd09ffffffc380e03ffffffffff847c027fffffffffffff08fff013ffffffffff,0x3d6b5cd041c8470f03f7adedddaf5ec3a1c0f487c8fd49fa12bdde2fd7ddf17f80f10ffff08fa24fffffe1ff70fffd1fff727ffffffffffffffff820e0238781ffffffffffffe1c0e07a03e47e84fd09ffffffffffffffc07007fff847c027fffffffffffffffffffffffffffffff,0x37f6feeb7def77afbbe40d09c18fd0c381d0fd07c8ff09fe933e1fcfe7e1fe7ff0fe0ffffe8ffc4fffff01ff80ffe11fff827ffffffffffffffffffffffffffff20604e0c7a061c0e07a03e47e84fd09ffffffffffffffffffffffffffffffffff80ff007ff08fff013ffffffffff,0x848302203020c0c00002002040a00040200a0020028005000000000000000000000000000040000000000000000000000000000000001ffffffffffffffffffffffffffffffffffffffffffffffffe180c07c380e03fc07007fff847c027ffff80ff007ff08fff013ffffffffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof252 : Floor 441 spec252 := floorEx (audit_off (db:=book38) (branches:=guides) (g:=69) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def book39 (i : ℕ) : {s : FloorData // Floor 441 s} := if i<32 then book31 i else (if i≤35 then (if i≤33 then (if i≤32 then ⟨spec229,proof229⟩ else ⟨spec233,proof233⟩) else (if i≤34 then ⟨spec236,proof236⟩ else ⟨spec189,proof189⟩)) else (if i≤37 then (if i≤36 then ⟨spec221,proof221⟩ else ⟨spec245,proof245⟩) else (if i≤38 then ⟨spec249,proof249⟩ else ⟨spec252,proof252⟩)))
def spec237 : FloorData := (0x3ffb800003fffeff00007f7fffb8000000003f7ffefffde0000007fb7ebde00000000fb7ff77bfefc00000001f6f7ffdbf7e00000000,9,[0x80000004305012000094189400000000006c8b5096a100000008100400400000000b0868041a8700000000161035a02438000000000000e000000238781f00004e0c7800000000003e07e00fc000000004380e01e00000000f807c003fefc00000001f007ff0037e00000000,0x2000000058031400000a00900000000000034d201070b8000000a800c48000000001d4d40885c12000000001a1a21c8701000000000000700000003c07ee00000700f8000000000003f78000ffde0000007c00ebc000000000fb780003f00000000001f6f01fdbc0000000000,0x10000000049100000000eca000400000000038e385c40200000009b0a000000000000e0e702e1004000000003c9cb90240a000000001fff8047fffffff8100fffffff00047fffffffffffffff0021ffffffffff1421fffffffffffffffc0103ffffffffffffe024081ffffffff,0x3445000000000000000048c221600000000000000400000000000564d112800000000000022000400000000020c0c21302c000000001fffffffffffc000100ffffffffffffffffffffc0800100021ffffffffffffffffffffff048008840103fffffffffffffffffffffffffff,0x3ffef6efffffb4aaba5ffff0100098fffffffff810022004c3ffffff64f1be73ffffffff0f087d0e1787fffffffc121001c8303ffffffffffffffffffffffffffffff80800047ffffffffc0800100021fffffffffffffffffffffffffffffffffffffffffe09080024081ffffffff,0x3ffc9b8fffffa6cce39ffff1314ce8fffffffffc30c3a18743ffffff00902843fffffffe090051081a07fffffffc12100048503fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80481421ffffffff048008840103fffffffe09080024081ffffffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof237 : Floor 441 spec237 := floorEx (audit_off (db:=book39) (branches:=guides) (g:=96) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def book40 (i : ℕ) : {s : FloorData // Floor 441 s} := if i<40 then book39 i else ⟨spec237,proof237⟩
def spec253 : FloorData := (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,11,[0x80000804305012008094189404281409406c8b5096a100000008100400480200082b0868041a8710012000561035a0243858686c1c0800e0020e0238781f20604e0c78061c0e07803e07e00fc00180c07c380e03fc07007fff807c007ffff80ff007ff00fff003ffffffffff,0x200200c560458033408100a009000ec10dd00235d201070f9400950a800cc83db088ba1ddd4088dc12316068d01a3a21c8f012ea47704830070063f003c07fe0c180700f8007e00ff8003ff8000ffffe00ff87c00ffc1ff8007c0fff80007f003ff07ff81fff01fffc01fc03fc00,0x801000480004910001ec08eda0004f5ba0800439e387c4020d160009b1a00018d61d000e1e703e10047bb704843dbdb90240a377724091c038007c0003ff8000fe007ff00007fff000003ffffff0001fff0007fff0001fffff800fffffff80003fff80001ffffe000001fffc0000,0x3f58008dda4e8000201f75d0100008b93c9e21f01000200043fbbdbb009028436edded74090011080206ddadeee812100048103878783e1ffc0007ffffc000000ffff80000007ffffffffc0000000001ffffff80000001ffffffff000000000003fffffffe00000000001ffffffff,0x3d6b44d0000800000017a5e49c221e00200000800000400002bdd62d56dd316800110040000022000404e1c970f21c1c21703c004000101ffffff800000000000fffffffffff80000000000000000001fffffffffffffe00000000000000000003ffffffffffffffffffe00000000,0x37f6f6eb7d6f34aaba400100000090000010090000020004832e1fce64e1be72709e0e790e087c0e1780000180800000018020000040201ffffffffffffffffff0000000000000000000000000000001fffffffffffffffffffffffffffffffffc000000000000000000000000000,0x849b0221b026ccc3800a01214ce0024120ce0420c38187000000000000000000000000000040001800000000000000000040000000401ffffffffffffffffffffffffffffffffffffffffffffffffe0000000000000000000000000000000000000000000000000000000000000])
lemma block_off {m k db branches vs i n ts} (p : 0 < m)
    (e : lookupRows (audit m db branches k) ts ((vs.drop i).take n)=false) : Block m k vs i n := by
  intro w hw h
  exact Bool.noConfusion (e.symm.trans (lookup_ok hw (fun g => audit_ok p db branches k w h g) _))
def raw0 : ℕ := 0x80000804305012008094189404281409406c8b5096a100000008100400480200082b0868041a8710012000561035a0243858686c1c0800e0020e0238781f20604e0c78061c0e07803e07e00fc00180c07c380e03fc07007fff807c007ffff80ff007ff00fff003ffffffffff
def raw1 : ℕ := 0x200200c560458033408100a009000ec10dd00235d201070f9400950a800cc83db088ba1ddd4088dc12316068d01a3a21c8f012ea47704830070063f003c07fe0c180700f8007e00ff8003ff8000ffffe00ff87c00ffc1ff8007c0fff80007f003ff07ff81fff01fffc01fc03fc00
def raw2 : ℕ := 0x801000480004910001ec08eda0004f5ba0800439e387c4020d160009b1a00018d61d000e1e703e10047bb704843dbdb90240a377724091c038007c0003ff8000fe007ff00007fff000003ffffff0001fff0007fff0001fffff800fffffff80003fff80001ffffe000001fffc0000
def raw3 : ℕ := 0x3f58008dda4e8000201f75d0100008b93c9e21f01000200043fbbdbb009028436edded74090011080206ddadeee812100048103878783e1ffc0007ffffc000000ffff80000007ffffffffc0000000001ffffff80000001ffffffff000000000003fffffffe00000000001ffffffff
def raw4 : ℕ := 0x3d6b44d0000800000017a5e49c221e00200000800000400002bdd62d56dd316800110040000022000404e1c970f21c1c21703c004000101ffffff800000000000fffffffffff80000000000000000001fffffffffffffe00000000000000000003ffffffffffffffffffe00000000
def raw5 : ℕ := 0x37f6f6eb7d6f34aaba400100000090000010090000020004832e1fce64e1be72709e0e790e087c0e1780000180800000018020000040201ffffffffffffffffff0000000000000000000000000000001fffffffffffffffffffffffffffffffffc000000000000000000000000000
def raw6 : ℕ := 0x849b0221b026ccc3800a01214ce0024120ce0420c38187000000000000000000000000000040001800000000000000000040000000401ffffffffffffffffffffffffffffffffffffffffffffffffe0000000000000000000000000000000000000000000000000000000000000
def state0 : List ℕ := [combine 0 raw0 raw1,raw0,raw1,raw2,raw3,raw4,raw5,raw6]
def state1 : List ℕ := [combine 1 raw0 raw1,raw0,raw1,raw2,raw3,raw4,raw5,raw6]
def state2 : List ℕ := [combine 2 raw0 raw1,raw0,raw1,raw2,raw3,raw4,raw5,raw6]
def state3 : List ℕ := [combine 3 raw0 raw1,raw0,raw1,raw2,raw3,raw4,raw5,raw6]
def state4 : List ℕ := [combine 0 raw0 raw2,raw0,raw2,raw1,raw3,raw4,raw5,raw6]
def state5 : List ℕ := [combine 1 raw0 raw2,raw0,raw2,raw1,raw3,raw4,raw5,raw6]
def state6 : List ℕ := [combine 2 raw0 raw2,raw0,raw2,raw1,raw3,raw4,raw5,raw6]
def state7 : List ℕ := [combine 3 raw0 raw2,raw0,raw2,raw1,raw3,raw4,raw5,raw6]
def state8 : List ℕ := [combine 0 raw0 raw3,raw0,raw3,raw1,raw2,raw4,raw5,raw6]
def state9 : List ℕ := [combine 1 raw0 raw3,raw0,raw3,raw1,raw2,raw4,raw5,raw6]
def state10 : List ℕ := [combine 2 raw0 raw3,raw0,raw3,raw1,raw2,raw4,raw5,raw6]
def state11 : List ℕ := [combine 3 raw0 raw3,raw0,raw3,raw1,raw2,raw4,raw5,raw6]
def state12 : List ℕ := [combine 0 raw0 raw4,raw0,raw4,raw1,raw2,raw3,raw5,raw6]
def state13 : List ℕ := [combine 1 raw0 raw4,raw0,raw4,raw1,raw2,raw3,raw5,raw6]
def state14 : List ℕ := [combine 2 raw0 raw4,raw0,raw4,raw1,raw2,raw3,raw5,raw6]
def state15 : List ℕ := [combine 3 raw0 raw4,raw0,raw4,raw1,raw2,raw3,raw5,raw6]
def state16 : List ℕ := [combine 0 raw0 raw5,raw0,raw5,raw1,raw2,raw3,raw4,raw6]
def state17 : List ℕ := [combine 1 raw0 raw5,raw0,raw5,raw1,raw2,raw3,raw4,raw6]
def state18 : List ℕ := [combine 2 raw0 raw5,raw0,raw5,raw1,raw2,raw3,raw4,raw6]
def state19 : List ℕ := [combine 3 raw0 raw5,raw0,raw5,raw1,raw2,raw3,raw4,raw6]
def state20 : List ℕ := [combine 0 raw0 raw6,raw0,raw6,raw1,raw2,raw3,raw4,raw5]
def state21 : List ℕ := [combine 1 raw0 raw6,raw0,raw6,raw1,raw2,raw3,raw4,raw5]
def state22 : List ℕ := [combine 2 raw0 raw6,raw0,raw6,raw1,raw2,raw3,raw4,raw5]
def state23 : List ℕ := [combine 3 raw0 raw6,raw0,raw6,raw1,raw2,raw3,raw4,raw5]
def state24 : List ℕ := [combine 0 raw1 raw2,raw1,raw2,raw0,raw3,raw4,raw5,raw6]
def state25 : List ℕ := [combine 1 raw1 raw2,raw1,raw2,raw0,raw3,raw4,raw5,raw6]
def state26 : List ℕ := [combine 2 raw1 raw2,raw1,raw2,raw0,raw3,raw4,raw5,raw6]
def state27 : List ℕ := [combine 3 raw1 raw2,raw1,raw2,raw0,raw3,raw4,raw5,raw6]
def state28 : List ℕ := [combine 0 raw1 raw3,raw1,raw3,raw0,raw2,raw4,raw5,raw6]
def state29 : List ℕ := [combine 1 raw1 raw3,raw1,raw3,raw0,raw2,raw4,raw5,raw6]
def state30 : List ℕ := [combine 2 raw1 raw3,raw1,raw3,raw0,raw2,raw4,raw5,raw6]
def state31 : List ℕ := [combine 3 raw1 raw3,raw1,raw3,raw0,raw2,raw4,raw5,raw6]
def state32 : List ℕ := [combine 0 raw1 raw4,raw1,raw4,raw0,raw2,raw3,raw5,raw6]
def state33 : List ℕ := [combine 1 raw1 raw4,raw1,raw4,raw0,raw2,raw3,raw5,raw6]
def state34 : List ℕ := [combine 2 raw1 raw4,raw1,raw4,raw0,raw2,raw3,raw5,raw6]
def state35 : List ℕ := [combine 3 raw1 raw4,raw1,raw4,raw0,raw2,raw3,raw5,raw6]
def state36 : List ℕ := [combine 0 raw1 raw5,raw1,raw5,raw0,raw2,raw3,raw4,raw6]
def state37 : List ℕ := [combine 1 raw1 raw5,raw1,raw5,raw0,raw2,raw3,raw4,raw6]
def state38 : List ℕ := [combine 2 raw1 raw5,raw1,raw5,raw0,raw2,raw3,raw4,raw6]
def state39 : List ℕ := [combine 3 raw1 raw5,raw1,raw5,raw0,raw2,raw3,raw4,raw6]
def state40 : List ℕ := [combine 0 raw2 raw3,raw2,raw3,raw0,raw1,raw4,raw5,raw6]
def state41 : List ℕ := [combine 1 raw2 raw3,raw2,raw3,raw0,raw1,raw4,raw5,raw6]
def state42 : List ℕ := [combine 2 raw2 raw3,raw2,raw3,raw0,raw1,raw4,raw5,raw6]
def state43 : List ℕ := [combine 3 raw2 raw3,raw2,raw3,raw0,raw1,raw4,raw5,raw6]
def state44 : List ℕ := [combine 0 raw2 raw4,raw2,raw4,raw0,raw1,raw3,raw5,raw6]
def state45 : List ℕ := [combine 1 raw2 raw4,raw2,raw4,raw0,raw1,raw3,raw5,raw6]
def state46 : List ℕ := [combine 2 raw2 raw4,raw2,raw4,raw0,raw1,raw3,raw5,raw6]
def state47 : List ℕ := [combine 3 raw2 raw4,raw2,raw4,raw0,raw1,raw3,raw5,raw6]
def state48 : List ℕ := [combine 0 raw2 raw5,raw2,raw5,raw0,raw1,raw3,raw4,raw6]
def state49 : List ℕ := [combine 1 raw2 raw5,raw2,raw5,raw0,raw1,raw3,raw4,raw6]
def state50 : List ℕ := [combine 2 raw2 raw5,raw2,raw5,raw0,raw1,raw3,raw4,raw6]
def state51 : List ℕ := [combine 3 raw2 raw5,raw2,raw5,raw0,raw1,raw3,raw4,raw6]
def state52 : List ℕ := [combine 0 raw4 raw3,raw4,raw3,raw0,raw1,raw2,raw5,raw6]
def state53 : List ℕ := [combine 1 raw4 raw3,raw4,raw0,raw1,raw2,raw5,raw6]
def state54 : List ℕ := [combine 1 raw4 raw3,raw4,raw3,raw0,raw1,raw2,raw5,raw6]
def state55 : List ℕ := [combine 2 raw4 raw3,raw4,raw3,raw0,raw1,raw2,raw5,raw6]
def state56 : List ℕ := [combine 3 raw4 raw3,raw4,raw0,raw1,raw2,raw5,raw6]
def state57 : List ℕ := [combine 3 raw4 raw3,raw4,raw3,raw0,raw1,raw2,raw5,raw6]
def state58 : List ℕ := [combine 0 raw5 raw3,raw5,raw3,raw0,raw1,raw2,raw4,raw6]
def state59 : List ℕ := [combine 1 raw5 raw3,raw5,raw3,raw0,raw1,raw2,raw4,raw6]
def state60 : List ℕ := [combine 2 raw5 raw3,raw5,raw3,raw0,raw1,raw2,raw4,raw6]
def state61 : List ℕ := [combine 3 raw5 raw3,raw5,raw3,raw0,raw1,raw2,raw4,raw6]
def state62 : List ℕ := [combine 0 raw5 raw4,raw5,raw4,raw0,raw1,raw2,raw3,raw6]
def state63 : List ℕ := [combine 1 raw5 raw4,raw5,raw4,raw0,raw1,raw2,raw3,raw6]
def state64 : List ℕ := [combine 2 raw5 raw4,raw5,raw4,raw0,raw1,raw2,raw3,raw6]
def state65 : List ℕ := [combine 3 raw5 raw4,raw5,raw4,raw0,raw1,raw2,raw3,raw6]
def state66 : List ℕ := [combine 0 raw6 raw1,raw6,raw1,raw0,raw2,raw3,raw4,raw5]
def state67 : List ℕ := [combine 1 raw6 raw1,raw6,raw1,raw0,raw2,raw3,raw4,raw5]
def state68 : List ℕ := [combine 2 raw6 raw1,raw6,raw1,raw0,raw2,raw3,raw4,raw5]
def state69 : List ℕ := [combine 3 raw6 raw1,raw6,raw1,raw0,raw2,raw3,raw4,raw5]
def state70 : List ℕ := [combine 0 raw6 raw2,raw6,raw2,raw0,raw1,raw3,raw4,raw5]
def state71 : List ℕ := [combine 1 raw6 raw2,raw6,raw2,raw0,raw1,raw3,raw4,raw5]
def state72 : List ℕ := [combine 2 raw6 raw2,raw6,raw2,raw0,raw1,raw3,raw4,raw5]
def state73 : List ℕ := [combine 3 raw6 raw2,raw6,raw2,raw0,raw1,raw3,raw4,raw5]
def state74 : List ℕ := [combine 0 raw6 raw3,raw6,raw3,raw0,raw1,raw2,raw4,raw5]
def state75 : List ℕ := [combine 1 raw6 raw3,raw6,raw3,raw0,raw1,raw2,raw4,raw5]
def state76 : List ℕ := [combine 2 raw6 raw3,raw6,raw3,raw0,raw1,raw2,raw4,raw5]
def state77 : List ℕ := [combine 3 raw6 raw3,raw6,raw3,raw0,raw1,raw2,raw4,raw5]
def state78 : List ℕ := [combine 0 raw6 raw4,raw6,raw4,raw0,raw1,raw2,raw3,raw5]
def state79 : List ℕ := [combine 1 raw6 raw4,raw6,raw4,raw0,raw1,raw2,raw3,raw5]
def state80 : List ℕ := [combine 2 raw6 raw4,raw6,raw4,raw0,raw1,raw2,raw3,raw5]
def state81 : List ℕ := [combine 3 raw6 raw4,raw6,raw4,raw0,raw1,raw2,raw3,raw5]
def state82 : List ℕ := [combine 0 raw6 raw5,raw6,raw5,raw0,raw1,raw2,raw3,raw4]
def state83 : List ℕ := [combine 1 raw6 raw5,raw6,raw5,raw0,raw1,raw2,raw3,raw4]
def state84 : List ℕ := [combine 2 raw6 raw5,raw6,raw5,raw0,raw1,raw2,raw3,raw4]
def state85 : List ℕ := [combine 3 raw6 raw5,raw6,raw5,raw0,raw1,raw2,raw3,raw4]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off0 : Excluded 441 9 state0 := audit_off (db:=book40) (branches:=guides) (g:=77) (by decide) (by decide +kernel)
def next1 := successors 441 8 state1
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk1_0 : Block 441 8 next1 0 16 := block_off (db:=book40) (branches:=guides) (ts:=[75,37963,104,106,108,53,75,37963,81,37969,37969,37969,37969,37969,81,37969]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk1_1 : Block 441 8 next1 16 16 := block_off (db:=book40) (branches:=guides) (ts:=[73,37961,63,63,63,63,73,37961,71,37959,112,114,120,53,71,37959]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk1_2 : Block 441 8 next1 32 16 := block_off (db:=book40) (branches:=guides) (ts:=[38481,77,77,77,77,77,79,77,77,77,37963,79,79,37963,37969,37969]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk1_3 : Block 441 8 next1 48 16 := block_off (db:=book40) (branches:=guides) (ts:=[37969,37969,37961,63,79,79,79,37961,37959,79,79,37959,79,130,79,79]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk1_4 : Block 441 8 next1 64 16 := block_off (db:=book40) (branches:=guides) (ts:=[79,79,38993,79,77,37963,134,77,77,77,37963,37969,37969,37969,37969,37969]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk1_5 : Block 441 8 next1 80 16 := block_off (db:=book40) (branches:=guides) (ts:=[37969,37961,63,77,77,77,37961,37959,138,77,77,77,37959,37969,37969,37969]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk1_6 : Block 441 8 next1 96 16 := block_off (db:=book40) (branches:=guides) (ts:=[37969,37961,63,37963,37961,37959,41,37963,37959,37969,63,37969,37969,37969,37969,37969]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk1_7 : Block 441 8 next1 112 16 := block_off (db:=book40) (branches:=guides) (ts:=[37969,37969,37969,37959,63,37959,37961,61,53,144,146,61,148,150,53,77]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk1_8 : Block 441 8 next1 128 16 := block_off (db:=book40) (branches:=guides) (ts:=[77,77,152,77,77,37963,154,158,37963,37969,37969,37969,37969,37961,63,63]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk1_9 : Block 441 8 next1 144 16 := block_off (db:=book40) (branches:=guides) (ts:=[37961,37959,160,162,37959]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off1 : Excluded 441 9 state1 := by
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (q:=10) (width:=16) (vs:=next1) (by decide) (by decide +kernel)
  intro j
  fin_cases j
  · exact chk1_0
  · exact chk1_1
  · exact chk1_2
  · exact chk1_3
  · exact chk1_4
  · exact chk1_5
  · exact chk1_6
  · exact chk1_7
  · exact chk1_8
  · exact chk1_9
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off2 : Excluded 441 9 state2 := audit_off (db:=book40) (branches:=guides) (g:=79) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off3 : Excluded 441 9 state3 := audit_off (db:=book40) (branches:=guides) (g:=77) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off4 : Excluded 441 9 state4 := audit_off (db:=book40) (branches:=guides) (g:=75) (by decide) (by decide +kernel)
def next5 := successors 441 8 state5
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk5_0 : Block 441 8 next5 0 16 := block_off (db:=book40) (branches:=guides) (ts:=[81,40017,40017,40017,40017,40017,81,40017,73,40009,168,41,41,41,73,40009]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk5_1 : Block 441 8 next5 16 16 := block_off (db:=book40) (branches:=guides) (ts:=[71,41,71,40007,41,41,180,41,41,41,71,40007,40529,75,75,75]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk5_2 : Block 441 8 next5 32 16 := block_off (db:=book40) (branches:=guides) (ts:=[75,75,79,75,75,75,37965,79,79,37965,40017,40017,40017,40017,40009,79]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk5_3 : Block 441 8 next5 48 16 := block_off (db:=book40) (branches:=guides) (ts:=[79,40009,40007,41,79,79,79,40007,79,192,79,79,79,79,41041,79]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk5_4 : Block 441 8 next5 64 16 := block_off (db:=book40) (branches:=guides) (ts:=[75,40017,40017,40017,40017,40017,40017,40009,198,75,75,75,40009,40007,41,75]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk5_5 : Block 441 8 next5 80 16 := block_off (db:=book40) (branches:=guides) (ts:=[75,75,40007,77,37965,200,41,77,37965,41,41,75,206,75,75,75]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk5_6 : Block 441 8 next5 96 16 := block_off (db:=book40) (branches:=guides) (ts:=[75,40017,40017,40017,40017,40009,37951,37965,40009,40007,41,37965,40007,40017,222,40017]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk5_7 : Block 441 8 next5 112 16 := block_off (db:=book40) (branches:=guides) (ts:=[40017,40017,40017,40017,40017,40017,40017,40007,41,40007,40009,61,41,230,41,61]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk5_8 : Block 441 8 next5 128 16 := block_off (db:=book40) (branches:=guides) (ts:=[41,41,41,75,75,75,234,75,75,37965,238,244,37965,40017,40017,40017]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk5_9 : Block 441 8 next5 144 16 := block_off (db:=book40) (branches:=guides) (ts:=[40017,40009,246,248,40009,40007,41,41,40007]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off5 : Excluded 441 9 state5 := by
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (q:=10) (width:=16) (vs:=next5) (by decide) (by decide +kernel)
  intro j
  fin_cases j
  · exact chk5_0
  · exact chk5_1
  · exact chk5_2
  · exact chk5_3
  · exact chk5_4
  · exact chk5_5
  · exact chk5_6
  · exact chk5_7
  · exact chk5_8
  · exact chk5_9
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off6 : Excluded 441 9 state6 := audit_off (db:=book40) (branches:=guides) (g:=79) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off7 : Excluded 441 9 state7 := audit_off (db:=book40) (branches:=guides) (g:=75) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off8 : Excluded 441 9 state8 := audit_off (db:=book40) (branches:=guides) (g:=81) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off9 : Excluded 441 9 state9 := audit_off (db:=book40) (branches:=guides) (g:=81) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off10 : Excluded 441 9 state10 := audit_off (db:=book40) (branches:=guides) (g:=81) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off11 : Excluded 441 9 state11 := audit_off (db:=book40) (branches:=guides) (g:=81) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off12 : Excluded 441 9 state12 := audit_off (db:=book40) (branches:=guides) (g:=73) (by decide) (by decide +kernel)
def next13 := successors 441 8 state13
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk13_0 : Block 441 8 next13 0 16 := block_off (db:=book40) (branches:=guides) (ts:=[81,42065,42065,42065,42065,42065,81,42065,42577,73,73,73,73,73,79,73]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk13_1 : Block 441 8 next13 16 16 := block_off (db:=book40) (branches:=guides) (ts:=[73,73,42061,63,79,79,79,42061,42059,79,79,42059,42065,42065,42065,42065]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk13_2 : Block 441 8 next13 32 16 := block_off (db:=book40) (branches:=guides) (ts:=[44103,79,79,44103,79,258,79,79,79,79,43089,79,73,42065,292,73]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk13_3 : Block 441 8 next13 48 16 := block_off (db:=book40) (branches:=guides) (ts:=[42065,42065,42065,42065,42065,42065,77,42061,63,63,77,42061,63,63,73,73]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk13_4 : Block 441 8 next13 64 16 := block_off (db:=book40) (branches:=guides) (ts:=[73,73,42059,63,42061,42059,42065,42065,42065,42065,44103,63,42061,44103,75,42059]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk13_5 : Block 441 8 next13 80 16 := block_off (db:=book40) (branches:=guides) (ts:=[294,296,75,42059,298,49,73,73,73,73,42065,42065,42065,42065,44103,41]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk13_6 : Block 441 8 next13 96 16 := block_off (db:=book40) (branches:=guides) (ts:=[42059,44103,71,44103,302,304,71,44103,306,49,44103,310,73,44103,73,73]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk13_7 : Block 441 8 next13 112 16 := block_off (db:=book40) (branches:=guides) (ts:=[42065,42065,42065,42065,61,49,322,324,61,326,328,49,73,73,73,73]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk13_8 : Block 441 8 next13 128 16 := block_off (db:=book40) (branches:=guides) (ts:=[42061,63,63,42061,42059,330,334,42059,42065,42065,42065,42065,44103,336,338,44103]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off13 : Excluded 441 9 state13 := by
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (q:=9) (width:=16) (vs:=next13) (by decide) (by decide +kernel)
  intro j
  fin_cases j
  · exact chk13_0
  · exact chk13_1
  · exact chk13_2
  · exact chk13_3
  · exact chk13_4
  · exact chk13_5
  · exact chk13_6
  · exact chk13_7
  · exact chk13_8
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off14 : Excluded 441 9 state14 := audit_off (db:=book40) (branches:=guides) (g:=79) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off15 : Excluded 441 9 state15 := audit_off (db:=book40) (branches:=guides) (g:=73) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off16 : Excluded 441 9 state16 := audit_off (db:=book40) (branches:=guides) (g:=71) (by decide) (by decide +kernel)
def next17 := successors 441 8 state17
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk17_0 : Block 441 8 next17 0 16 := block_off (db:=book40) (branches:=guides) (ts:=[81,44113,44113,44113,44113,44113,81,44113,73,44105,342,59,59,59,73,44105]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk17_1 : Block 441 8 next17 16 16 := block_off (db:=book40) (branches:=guides) (ts:=[44625,71,71,71,71,71,79,71,71,71,44109,79,79,44109,44107,41]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk17_2 : Block 441 8 next17 32 16 := block_off (db:=book40) (branches:=guides) (ts:=[79,79,79,44107,44113,44113,44113,44113,44105,79,79,44105,79,79,79,79]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk17_3 : Block 441 8 next17 48 16 := block_off (db:=book40) (branches:=guides) (ts:=[45137,79,71,44113,44113,44113,44113,44113,44113,71,346,71,71,71,71,77]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk17_4 : Block 441 8 next17 64 16 := block_off (db:=book40) (branches:=guides) (ts:=[44109,348,59,77,44109,59,59,71,71,71,71,44107,41,44109,44107,44113]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk17_5 : Block 441 8 next17 80 16 := block_off (db:=book40) (branches:=guides) (ts:=[44113,44113,44113,44105,42047,44109,44105,75,44107,41,59,75,44107,59,59,71]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk17_6 : Block 441 8 next17 96 16 := block_off (db:=book40) (branches:=guides) (ts:=[71,71,71,44113,44113,44113,44113,44105,41,44107,44105,44113,356,44113,44113,44113]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk17_7 : Block 441 8 next17 112 16 := block_off (db:=book40) (branches:=guides) (ts:=[44113,61,59,364,59,61,59,59,59,71,71,71,71,44109,366,370]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk17_8 : Block 441 8 next17 128 16 := block_off (db:=book40) (branches:=guides) (ts:=[44109,44107,41,41,44107,44113,44113,44113,44113,44105,372,370,44105]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off17 : Excluded 441 9 state17 := by
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (q:=9) (width:=16) (vs:=next17) (by decide) (by decide +kernel)
  intro j
  fin_cases j
  · exact chk17_0
  · exact chk17_1
  · exact chk17_2
  · exact chk17_3
  · exact chk17_4
  · exact chk17_5
  · exact chk17_6
  · exact chk17_7
  · exact chk17_8
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off18 : Excluded 441 9 state18 := audit_off (db:=book40) (branches:=guides) (g:=79) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off19 : Excluded 441 9 state19 := audit_off (db:=book40) (branches:=guides) (g:=71) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off20 : Excluded 441 9 state20 := audit_off (db:=book40) (branches:=guides) (g:=79) (by decide) (by decide +kernel)
def next21 := successors 441 8 state21
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk21_0 : Block 441 8 next21 0 16 := block_off (db:=book40) (branches:=guides) (ts:=[77,46157,376,382,388,390,77,46157,75,46155,392,398,406,408,75,46155]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk21_1 : Block 441 8 next21 16 16 := block_off (db:=book40) (branches:=guides) (ts:=[81,46161,81,46161,46161,46161,432,452,46161,46161,81,46161,73,46153,456,462]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk21_2 : Block 441 8 next21 32 16 := block_off (db:=book40) (branches:=guides) (ts:=[468,472,73,46153,71,46151,474,478,482,486,71,46151,46673,61,79,79]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk21_3 : Block 441 8 next21 48 16 := block_off (db:=book40) (branches:=guides) (ts:=[79,79,79,79,61,79,46157,488,79,79,79,46157,46155,496,79,79]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk21_4 : Block 441 8 next21 64 16 := block_off (db:=book40) (branches:=guides) (ts:=[79,46155,46161,46161,46161,46161,46161,46161,46153,500,79,79,79,46153,46151,46151]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk21_5 : Block 441 8 next21 80 16 := block_off (db:=book40) (branches:=guides) (ts:=[79,79,46151,46151,47185,79,79,46157,502,61,46157,46155,504,61,46155,46161]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk21_6 : Block 441 8 next21 96 16 := block_off (db:=book40) (branches:=guides) (ts:=[46161,46161,46161,46161,46161,46153,512,518,522,61,46153,46151,530,534,542,61]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk21_7 : Block 441 8 next21 112 16 := block_off (db:=book40) (branches:=guides) (ts:=[46151,46155,544,46157,46155,46161,46161,46161,46161,46153,44095,46157,46153,46151,546,46157]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk21_8 : Block 441 8 next21 128 16 := block_off (db:=book40) (branches:=guides) (ts:=[46151,46161,46161,46161,46161,46153,548,46155,46153,46151,41,46155,46151,46161,576,46161]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk21_9 : Block 441 8 next21 144 16 := block_off (db:=book40) (branches:=guides) (ts:=[46161,46161,46161,46161,46161,46161,46161,46151,580,46151,46153]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off21 : Excluded 441 9 state21 := by
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (q:=10) (width:=16) (vs:=next21) (by decide) (by decide +kernel)
  intro j
  fin_cases j
  · exact chk21_0
  · exact chk21_1
  · exact chk21_2
  · exact chk21_3
  · exact chk21_4
  · exact chk21_5
  · exact chk21_6
  · exact chk21_7
  · exact chk21_8
  · exact chk21_9
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off22 : Excluded 441 9 state22 := audit_off (db:=book40) (branches:=guides) (g:=79) (by decide) (by decide +kernel)
def next23 := successors 441 8 state23
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk23_0 : Block 441 8 next23 0 16 := block_off (db:=book40) (branches:=guides) (ts:=[79,45649,79,77,46669,584,61,61,61,77,46669,75,46667,586,61,61]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk23_1 : Block 441 8 next23 16 16 := block_off (db:=book40) (branches:=guides) (ts:=[61,75,46667,81,46673,46673,46673,46673,46673,81,46673,73,46665,590,61,61]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk23_2 : Block 441 8 next23 32 16 := block_off (db:=book40) (branches:=guides) (ts:=[61,73,46665,71,46663,594,61,596,61,61,61,71,61,71,46663,46161]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk23_3 : Block 441 8 next23 48 16 := block_off (db:=book40) (branches:=guides) (ts:=[61,79,79,79,61,79,79,79,79,46669,79,79,46669,46667,79,79]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk23_4 : Block 441 8 next23 64 16 := block_off (db:=book40) (branches:=guides) (ts:=[46667,46673,46673,46673,46673,46665,79,79,46665,46663,79,79,46663,46669,61,61]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk23_5 : Block 441 8 next23 80 16 := block_off (db:=book40) (branches:=guides) (ts:=[46669,46667,61,61,46667,46673,46673,46673,46673,46673,46673,46665,600,61,61,61]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk23_6 : Block 441 8 next23 96 16 := block_off (db:=book40) (branches:=guides) (ts:=[46665,46663,602,61,61,61,46663,46667,604,46669,46667,46673,46673,46673,46673,46665]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk23_7 : Block 441 8 next23 112 16 := block_off (db:=book40) (branches:=guides) (ts:=[44607,46669,46665,46663,606,46669,46663,46673,46673,46673,46673,46665,608,46667,46665,46663]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk23_8 : Block 441 8 next23 128 16 := block_off (db:=book40) (branches:=guides) (ts:=[41,46667,46663,46673,612,46673,46673,46673,46673,46673,46673,46673,46673,46663,614,46663]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk23_9 : Block 441 8 next23 144 16 := block_off (db:=book40) (branches:=guides) (ts:=[46665]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off23 : Excluded 441 9 state23 := by
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (q:=10) (width:=16) (vs:=next23) (by decide) (by decide +kernel)
  intro j
  fin_cases j
  · exact chk23_0
  · exact chk23_1
  · exact chk23_2
  · exact chk23_3
  · exact chk23_4
  · exact chk23_5
  · exact chk23_6
  · exact chk23_7
  · exact chk23_8
  · exact chk23_9
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off24 : Excluded 441 9 state24 := audit_off (db:=book40) (branches:=guides) (g:=75) (by decide) (by decide +kernel)
def next25 := successors 441 8 state25
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk25_0 : Block 441 8 next25 0 16 := block_off (db:=book40) (branches:=guides) (ts:=[81,72785,72785,72785,72785,72785,81,72785,73,72777,63,63,63,63,73,72777]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk25_1 : Block 441 8 next25 16 16 := block_off (db:=book40) (branches:=guides) (ts:=[71,72775,618,620,622,51,71,72775,73297,75,75,75,75,75,77,75]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk25_2 : Block 441 8 next25 32 16 := block_off (db:=book40) (branches:=guides) (ts:=[75,75,72785,72785,72785,72785,72777,72777,77,77,72777,72777,72775,624,77,77]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk25_3 : Block 441 8 next25 48 16 := block_off (db:=book40) (branches:=guides) (ts:=[77,72775,73809,77,75,72785,72785,72785,72785,72777,63,75,75,75,72777,72775]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk25_4 : Block 441 8 next25 64 16 := block_off (db:=book40) (branches:=guides) (ts:=[72775,75,75,72775,72775,79,37967,626,628,79,37967,634,51,77,636,77]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk25_5 : Block 441 8 next25 80 16 := block_off (db:=book40) (branches:=guides) (ts:=[77,77,77,75,638,75,75,75,75,72785,72785,72785,72785,72777,63,37967]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk25_6 : Block 441 8 next25 96 16 := block_off (db:=book40) (branches:=guides) (ts:=[72777,72775,41,37967,72775,37967,544,37967,604,72785,63,72785,72785,72785,72785,72785]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk25_7 : Block 441 8 next25 112 16 := block_off (db:=book40) (branches:=guides) (ts:=[72785,72785,72785,72775,63,72775,72777,61,51,640,642,61,644,648,51,77]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk25_8 : Block 441 8 next25 128 16 := block_off (db:=book40) (branches:=guides) (ts:=[654,77,77,77,77,75,660,75,75,75,75,72785,72785,72785,72785,72777]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk25_9 : Block 441 8 next25 144 16 := block_off (db:=book40) (branches:=guides) (ts:=[63,63,72777,72775,662,664,72775]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off25 : Excluded 441 9 state25 := by
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (q:=10) (width:=16) (vs:=next25) (by decide) (by decide +kernel)
  intro j
  fin_cases j
  · exact chk25_0
  · exact chk25_1
  · exact chk25_2
  · exact chk25_3
  · exact chk25_4
  · exact chk25_5
  · exact chk25_6
  · exact chk25_7
  · exact chk25_8
  · exact chk25_9
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off26 : Excluded 441 9 state26 := audit_off (db:=book40) (branches:=guides) (g:=77) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off27 : Excluded 441 9 state27 := audit_off (db:=book40) (branches:=guides) (g:=75) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off28 : Excluded 441 9 state28 := audit_off (db:=book40) (branches:=guides) (g:=81) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off29 : Excluded 441 9 state29 := audit_off (db:=book40) (branches:=guides) (g:=81) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off30 : Excluded 441 9 state30 := audit_off (db:=book40) (branches:=guides) (g:=81) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off31 : Excluded 441 9 state31 := audit_off (db:=book40) (branches:=guides) (g:=81) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off32 : Excluded 441 9 state32 := audit_off (db:=book40) (branches:=guides) (g:=73) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off33 : Excluded 441 9 state33 := audit_off (db:=book40) (branches:=guides) (g:=63) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off34 : Excluded 441 9 state34 := audit_off (db:=book40) (branches:=guides) (g:=77) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off35 : Excluded 441 9 state35 := audit_off (db:=book40) (branches:=guides) (g:=73) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off36 : Excluded 441 9 state36 := audit_off (db:=book40) (branches:=guides) (g:=71) (by decide) (by decide +kernel)
def next37 := successors 441 8 state37
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk37_0 : Block 441 8 next37 0 16 := block_off (db:=book40) (branches:=guides) (ts:=[81,76881,76881,76881,76881,76881,81,76881,73,76873,63,63,63,63,73,76873]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk37_1 : Block 441 8 next37 16 16 := block_off (db:=book40) (branches:=guides) (ts:=[77393,71,71,71,71,71,77,71,71,71,76875,668,77,77,77,76875]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk37_2 : Block 441 8 next37 32 16 := block_off (db:=book40) (branches:=guides) (ts:=[76881,76881,76881,76881,76873,77,77,76873,77905,77,71,76881,76881,76881,76881,71]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk37_3 : Block 441 8 next37 48 16 := block_off (db:=book40) (branches:=guides) (ts:=[63,71,71,71,71,79,44111,670,672,79,44111,674,43,77,678,77]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk37_4 : Block 441 8 next37 64 16 := block_off (db:=book40) (branches:=guides) (ts:=[77,77,77,71,71,71,71,76875,41,44111,76875,76881,76881,76881,76881,76873]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk37_5 : Block 441 8 next37 80 16 := block_off (db:=book40) (branches:=guides) (ts:=[63,44111,76873,44111,546,44111,606,75,76875,680,682,75,76875,684,43,71]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk37_6 : Block 441 8 next37 96 16 := block_off (db:=book40) (branches:=guides) (ts:=[71,71,71,76881,76881,76881,76881,76873,63,76875,76873,76881,63,76881,76881,76881]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk37_7 : Block 441 8 next37 112 16 := block_off (db:=book40) (branches:=guides) (ts:=[76881,61,43,686,688,61,690,692,43,77,77,77,77,71,694,71]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk37_8 : Block 441 8 next37 128 16 := block_off (db:=book40) (branches:=guides) (ts:=[71,71,71,76875,696,698,76875,76881,76881,76881,76881,76873,63,63,76873]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off37 : Excluded 441 9 state37 := by
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (q:=9) (width:=16) (vs:=next37) (by decide) (by decide +kernel)
  intro j
  fin_cases j
  · exact chk37_0
  · exact chk37_1
  · exact chk37_2
  · exact chk37_3
  · exact chk37_4
  · exact chk37_5
  · exact chk37_6
  · exact chk37_7
  · exact chk37_8
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off38 : Excluded 441 9 state38 := audit_off (db:=book40) (branches:=guides) (g:=77) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off39 : Excluded 441 9 state39 := audit_off (db:=book40) (branches:=guides) (g:=71) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off40 : Excluded 441 9 state40 := audit_off (db:=book40) (branches:=guides) (g:=81) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off41 : Excluded 441 9 state41 := audit_off (db:=book40) (branches:=guides) (g:=81) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off42 : Excluded 441 9 state42 := audit_off (db:=book40) (branches:=guides) (g:=81) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off43 : Excluded 441 9 state43 := audit_off (db:=book40) (branches:=guides) (g:=81) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off44 : Excluded 441 9 state44 := audit_off (db:=book40) (branches:=guides) (g:=73) (by decide) (by decide +kernel)
def next45 := successors 441 8 state45
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk45_0 : Block 441 8 next45 0 16 := block_off (db:=book40) (branches:=guides) (ts:=[81,107601,107601,107601,107601,107601,81,107601,108113,73,73,73,73,73,75,73]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk45_1 : Block 441 8 next45 16 16 := block_off (db:=book40) (branches:=guides) (ts:=[73,73,107601,107601,107601,107601,109639,109639,75,75,109639,109639,108625,75,73,107601]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk45_2 : Block 441 8 next45 32 16 := block_off (db:=book40) (branches:=guides) (ts:=[73,107601,107601,107601,107601,79,74831,702,704,79,74831,710,47,75,714,75]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk45_3 : Block 441 8 next45 48 16 := block_off (db:=book40) (branches:=guides) (ts:=[75,75,75,73,73,73,73,74829,63,74831,74829,107601,107601,107601,107601,109639]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk45_4 : Block 441 8 next45 64 16 := block_off (db:=book40) (branches:=guides) (ts:=[41,74831,109639,74831,548,74831,608,77,74829,63,63,77,74829,63,63,75]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk45_5 : Block 441 8 next45 80 16 := block_off (db:=book40) (branches:=guides) (ts:=[63,75,75,75,75,73,73,73,73,107601,107601,107601,107601,109639,63,74829]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk45_6 : Block 441 8 next45 96 16 := block_off (db:=book40) (branches:=guides) (ts:=[109639,71,109639,716,9,71,109639,718,47,109639,724,73,109639,73,73,107601]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk45_7 : Block 441 8 next45 112 16 := block_off (db:=book40) (branches:=guides) (ts:=[107601,107601,107601,61,47,728,730,61,732,734,47,75,740,75,75,75]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk45_8 : Block 441 8 next45 128 16 := block_off (db:=book40) (branches:=guides) (ts:=[75,73,744,73,73,73,73,74829,63,63,74829,107601,107601,107601,107601,109639]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk45_9 : Block 441 8 next45 144 16 := block_off (db:=book40) (branches:=guides) (ts:=[746,748,109639]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off45 : Excluded 441 9 state45 := by
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (q:=10) (width:=16) (vs:=next45) (by decide) (by decide +kernel)
  intro j
  fin_cases j
  · exact chk45_0
  · exact chk45_1
  · exact chk45_2
  · exact chk45_3
  · exact chk45_4
  · exact chk45_5
  · exact chk45_6
  · exact chk45_7
  · exact chk45_8
  · exact chk45_9
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off46 : Excluded 441 9 state46 := audit_off (db:=book40) (branches:=guides) (g:=75) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off47 : Excluded 441 9 state47 := audit_off (db:=book40) (branches:=guides) (g:=73) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off48 : Excluded 441 9 state48 := audit_off (db:=book40) (branches:=guides) (g:=71) (by decide) (by decide +kernel)
def next49 := successors 441 8 state49
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk49_0 : Block 441 8 next49 0 16 := block_off (db:=book40) (branches:=guides) (ts:=[110161,71,71,71,71,71,75,71,71,71,109649,109649,109649,109649,109641,75]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk49_1 : Block 441 8 next49 16 16 := block_off (db:=book40) (branches:=guides) (ts:=[75,109641,110673,75,71,109649,109649,109649,109649,71,71,71,71,79,76879,41]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk49_2 : Block 441 8 next49 32 16 := block_off (db:=book40) (branches:=guides) (ts:=[57,79,76879,57,57,75,41,75,75,75,75,71,71,71,71,76877]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk49_3 : Block 441 8 next49 48 16 := block_off (db:=book40) (branches:=guides) (ts:=[41,76879,76877,109649,109649,109649,109649,109641,41,76879,109641,76879,41,76879,41,77]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk49_4 : Block 441 8 next49 64 16 := block_off (db:=book40) (branches:=guides) (ts:=[76877,752,57,77,76877,57,57,75,75,75,75,71,71,71,71,109649]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk49_5 : Block 441 8 next49 80 16 := block_off (db:=book40) (branches:=guides) (ts:=[109649,109649,109649,109641,74815,76877,109641,81,109649,109649,109649,81,109649,109649,109649,73]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk49_6 : Block 441 8 next49 96 16 := block_off (db:=book40) (branches:=guides) (ts:=[109641,754,57,73,109641,57,57,109649,758,109649,109649,109649,109649,61,57,760]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk49_7 : Block 441 8 next49 112 16 := block_off (db:=book40) (branches:=guides) (ts:=[57,61,57,57,57,75,75,75,75,71,762,71,71,71,71,76877]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk49_8 : Block 441 8 next49 128 16 := block_off (db:=book40) (branches:=guides) (ts:=[764,1,76877,109649,109649,109649,109649,109641,766,1,109641]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off49 : Excluded 441 9 state49 := by
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (q:=9) (width:=16) (vs:=next49) (by decide) (by decide +kernel)
  intro j
  fin_cases j
  · exact chk49_0
  · exact chk49_1
  · exact chk49_2
  · exact chk49_3
  · exact chk49_4
  · exact chk49_5
  · exact chk49_6
  · exact chk49_7
  · exact chk49_8
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off50 : Excluded 441 9 state50 := audit_off (db:=book40) (branches:=guides) (g:=75) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off51 : Excluded 441 9 state51 := audit_off (db:=book40) (branches:=guides) (g:=71) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off52 : Excluded 441 9 state52 := audit_off (db:=book40) (branches:=guides) (g:=81) (by decide) (by decide +kernel)
def next53 := successors 441 8 state53
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk53_0 : Block 441 8 next53 0 16 := block_off (db:=book40) (branches:=guides) (ts:=[81,81,81,107599,776,107599,790,73,794,73,73,73,73,107597,63,107599]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk53_1 : Block 441 8 next53 16 16 := block_off (db:=book40) (branches:=guides) (ts:=[107597,107595,806,107599,107595,142407,810,107599,142407,107599,820,107599,824,107597,63,107597]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk53_2 : Block 441 8 next53 32 16 := block_off (db:=book40) (branches:=guides) (ts:=[63,73,73,73,107597,73,73,107595,63,107597,107595,142407,63,107597,142407,107595]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk53_3 : Block 441 8 next53 48 16 := block_off (db:=book40) (branches:=guides) (ts:=[840,107595,848,73,73,73,73,142407,850,107595,142407,142407,874,142407,880,142407]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk53_4 : Block 441 8 next53 64 16 := block_off (db:=book40) (branches:=guides) (ts:=[73,142407,73,896,904,912,920,73,952,73,73,73,73,107597,63,63]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk53_5 : Block 441 8 next53 80 16 := block_off (db:=book40) (branches:=guides) (ts:=[107597,107595,956,968,107595,142407,972,982,142407]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off53 : Excluded 441 9 state53 := by
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (q:=6) (width:=16) (vs:=next53) (by decide) (by decide +kernel)
  intro j
  fin_cases j
  · exact chk53_0
  · exact chk53_1
  · exact chk53_2
  · exact chk53_3
  · exact chk53_4
  · exact chk53_5
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off54 : Excluded 441 9 state54 := audit_off (db:=book40) (branches:=guides) (g:=81) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off55 : Excluded 441 9 state55 := audit_off (db:=book40) (branches:=guides) (g:=81) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off56 : Excluded 441 9 state56 := audit_off (db:=book40) (branches:=guides) (g:=81) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off57 : Excluded 441 9 state57 := audit_off (db:=book40) (branches:=guides) (g:=81) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off58 : Excluded 441 9 state58 := audit_off (db:=book40) (branches:=guides) (g:=81) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off59 : Excluded 441 9 state59 := audit_off (db:=book40) (branches:=guides) (g:=81) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off60 : Excluded 441 9 state60 := audit_off (db:=book40) (branches:=guides) (g:=81) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off61 : Excluded 441 9 state61 := audit_off (db:=book40) (branches:=guides) (g:=81) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off62 : Excluded 441 9 state62 := audit_off (db:=book40) (branches:=guides) (g:=71) (by decide) (by decide +kernel)
def next63 := successors 441 8 state63
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk63_0 : Block 441 8 next63 0 16 := block_off (db:=book40) (branches:=guides) (ts:=[143441,73,71,71,71,71,71,71,73,71,142417,142417,142417,142417,142929,71]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk63_1 : Block 441 8 next63 16 16 := block_off (db:=book40) (branches:=guides) (ts:=[71,142417,73,142417,142417,142417,142417,79,142415,986,988,79,142415,992,35,71]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk63_2 : Block 441 8 next63 32 16 := block_off (db:=book40) (branches:=guides) (ts:=[994,71,71,71,71,73,996,73,73,73,73,142413,63,142415,142413,142411]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk63_3 : Block 441 8 next63 48 16 := block_off (db:=book40) (branches:=guides) (ts:=[41,142415,142411,142417,142417,142417,142417,142415,580,142415,614,77,142413,63,63,77]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk63_4 : Block 441 8 next63 64 16 := block_off (db:=book40) (branches:=guides) (ts:=[142413,63,63,71,63,71,71,71,71,73,73,73,73,142411,63,142413]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk63_5 : Block 441 8 next63 80 16 := block_off (db:=book40) (branches:=guides) (ts:=[142411,142417,142417,142417,142417,75,142411,998,9,75,142411,1000,35,71,71,71]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk63_6 : Block 441 8 next63 96 16 := block_off (db:=book40) (branches:=guides) (ts:=[142411,71,71,73,1002,73,73,73,73,142417,142417,142417,142417,81,142417,142417]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk63_7 : Block 441 8 next63 112 16 := block_off (db:=book40) (branches:=guides) (ts:=[142417,81,142417,142417,142417,61,35,1012,1014,61,1016,1020,35,71,1028,71]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk63_8 : Block 441 8 next63 128 16 := block_off (db:=book40) (branches:=guides) (ts:=[71,71,71,73,73,73,73,142413,63,63,142413,142411,1030,1032,142411,142417]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk63_9 : Block 441 8 next63 144 16 := block_off (db:=book40) (branches:=guides) (ts:=[142417,142417,142417]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off63 : Excluded 441 9 state63 := by
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (q:=10) (width:=16) (vs:=next63) (by decide) (by decide +kernel)
  intro j
  fin_cases j
  · exact chk63_0
  · exact chk63_1
  · exact chk63_2
  · exact chk63_3
  · exact chk63_4
  · exact chk63_5
  · exact chk63_6
  · exact chk63_7
  · exact chk63_8
  · exact chk63_9
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off64 : Excluded 441 9 state64 := audit_off (db:=book40) (branches:=guides) (g:=71) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off65 : Excluded 441 9 state65 := audit_off (db:=book40) (branches:=guides) (g:=73) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off66 : Excluded 441 9 state66 := audit_off (db:=book40) (branches:=guides) (g:=77) (by decide) (by decide +kernel)
def next67 := successors 441 8 state67
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk67_0 : Block 441 8 next67 0 16 := block_off (db:=book40) (branches:=guides) (ts:=[75,78923,1036,1038,1040,33,75,78923,81,78929,78929,78929,78929,78929,81,78929]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk67_1 : Block 441 8 next67 16 16 := block_off (db:=book40) (branches:=guides) (ts:=[73,78921,63,63,63,63,73,78921,71,78919,1042,1044,1046,33,71,78919]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk67_2 : Block 441 8 next67 32 16 := block_off (db:=book40) (branches:=guides) (ts:=[79953,77,77,77,77,77,61,77,77,77,78923,1048,61,78923,78929,78929]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk67_3 : Block 441 8 next67 48 16 := block_off (db:=book40) (branches:=guides) (ts:=[78929,78929,78921,63,63,63,61,78921,78919,1050,61,78919,79441,61,77,78923]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk67_4 : Block 441 8 next67 64 16 := block_off (db:=book40) (branches:=guides) (ts:=[1052,77,77,77,78923,78929,78929,78929,78929,78929,78929,78921,63,77,77,77]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk67_5 : Block 441 8 next67 80 16 := block_off (db:=book40) (branches:=guides) (ts:=[78921,78919,77,77,78919,79,46159,1054,1056,79,46159,1058,33,46159,502,46159]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk67_6 : Block 441 8 next67 96 16 := block_off (db:=book40) (branches:=guides) (ts:=[61,77,77,77,77,78923,1060,46159,78923,78929,78929,78929,78929,78921,63,46159]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk67_7 : Block 441 8 next67 112 16 := block_off (db:=book40) (branches:=guides) (ts:=[78921,78919,366,46159,78919,78929,78929,78929,78929,78921,63,78923,78921,78919,764,78923]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk67_8 : Block 441 8 next67 128 16 := block_off (db:=book40) (branches:=guides) (ts:=[78919,78929,63,78929,78929,78929,78929,78929,78929,78929,78929,78919,63,78919,78921]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off67 : Excluded 441 9 state67 := by
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (q:=9) (width:=16) (vs:=next67) (by decide) (by decide +kernel)
  intro j
  fin_cases j
  · exact chk67_0
  · exact chk67_1
  · exact chk67_2
  · exact chk67_3
  · exact chk67_4
  · exact chk67_5
  · exact chk67_6
  · exact chk67_7
  · exact chk67_8
def next68 := successors 441 8 state68
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk68_0 : Block 441 8 next68 0 16 := block_off (db:=book40) (branches:=guides) (ts:=[77,78417,77,61,78929,77,75,79435,1064,61,61,61,75,79435,81,79441]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk68_1 : Block 441 8 next68 16 16 := block_off (db:=book40) (branches:=guides) (ts:=[79441,79441,79441,79441,81,79441,73,79433,63,61,61,61,73,79433,71,79431]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk68_2 : Block 441 8 next68 32 16 := block_off (db:=book40) (branches:=guides) (ts:=[1068,61,61,61,71,79431,77,77,61,77,77,77,77,79435,61,61]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk68_3 : Block 441 8 next68 48 16 := block_off (db:=book40) (branches:=guides) (ts:=[79435,79441,79441,79441,79441,79433,63,61,61,61,79433,79431,61,61,79431,79435]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk68_4 : Block 441 8 next68 64 16 := block_off (db:=book40) (branches:=guides) (ts:=[77,77,79435,79441,79441,79441,79441,79433,79433,77,77,79433,79433,79431,77,77]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk68_5 : Block 441 8 next68 80 16 := block_off (db:=book40) (branches:=guides) (ts:=[79431,79,46671,1072,61,79,46671,61,61,46671,61,46671,61,77,1074,77]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk68_6 : Block 441 8 next68 96 16 := block_off (db:=book40) (branches:=guides) (ts:=[77,77,77,79435,1076,46671,79435,79441,79441,79441,79441,79433,63,46671,79433,79431]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk68_7 : Block 441 8 next68 112 16 := block_off (db:=book40) (branches:=guides) (ts:=[370,46671,79431,79441,79441,79441,79441,79433,63,79435,79433,79431,1,79435,79431,79441]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk68_8 : Block 441 8 next68 128 16 := block_off (db:=book40) (branches:=guides) (ts:=[63,79441,79441,79441,79441,79441,79441,79441,79441,79431,63,79431,79433]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off68 : Excluded 441 9 state68 := by
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (q:=9) (width:=16) (vs:=next68) (by decide) (by decide +kernel)
  intro j
  fin_cases j
  · exact chk68_0
  · exact chk68_1
  · exact chk68_2
  · exact chk68_3
  · exact chk68_4
  · exact chk68_5
  · exact chk68_6
  · exact chk68_7
  · exact chk68_8
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off69 : Excluded 441 9 state69 := audit_off (db:=book40) (branches:=guides) (g:=77) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off70 : Excluded 441 9 state70 := audit_off (db:=book40) (branches:=guides) (g:=75) (by decide) (by decide +kernel)
def next71 := successors 441 8 state71
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk71_0 : Block 441 8 next71 0 16 := block_off (db:=book40) (branches:=guides) (ts:=[81,111697,111697,111697,111697,111697,81,111697,73,111689,1080,1082,1084,31,73,111689]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk71_1 : Block 441 8 next71 16 16 := block_off (db:=book40) (branches:=guides) (ts:=[71,111687,1086,1,1088,31,71,111687,112721,75,75,75,75,75,61,75]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk71_2 : Block 441 8 next71 32 16 := block_off (db:=book40) (branches:=guides) (ts:=[75,75,78925,1090,61,78925,111697,111697,111697,111697,111689,1094,61,111689,111687,1098]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk71_3 : Block 441 8 next71 48 16 := block_off (db:=book40) (branches:=guides) (ts:=[1,1100,61,111687,112209,61,75,111697,111697,111697,111697,111697,111697,111689,1104,75]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk71_4 : Block 441 8 next71 64 16 := block_off (db:=book40) (branches:=guides) (ts:=[75,75,111689,111687,75,75,111687,79,78927,1106,1108,79,78927,1110,31,78927]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk71_5 : Block 441 8 next71 80 16 := block_off (db:=book40) (branches:=guides) (ts:=[504,78927,61,75,75,75,75,78925,154,78927,78925,111697,111697,111697,111697,111689]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk71_6 : Block 441 8 next71 96 16 := block_off (db:=book40) (branches:=guides) (ts:=[1112,78927,111689,111687,41,78927,111687,77,78925,1114,1116,77,78925,1118,31,75]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk71_7 : Block 441 8 next71 112 16 := block_off (db:=book40) (branches:=guides) (ts:=[1120,75,75,75,75,111697,111697,111697,111697,111689,76863,78925,111689,111687,1122,78925]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk71_8 : Block 441 8 next71 128 16 := block_off (db:=book40) (branches:=guides) (ts:=[111687,111697,1126,111697,111697,111697,111697,111697,111697,111697,111697,111687,1030,111687,111689]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off71 : Excluded 441 9 state71 := by
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (q:=9) (width:=16) (vs:=next71) (by decide) (by decide +kernel)
  intro j
  fin_cases j
  · exact chk71_0
  · exact chk71_1
  · exact chk71_2
  · exact chk71_3
  · exact chk71_4
  · exact chk71_5
  · exact chk71_6
  · exact chk71_7
  · exact chk71_8
def next72 := successors 441 8 state72
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk72_0 : Block 441 8 next72 0 16 := block_off (db:=book40) (branches:=guides) (ts:=[75,111185,75,61,111697,75,77,79437,1130,61,61,61,77,79437,81,112209]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk72_1 : Block 441 8 next72 16 16 := block_off (db:=book40) (branches:=guides) (ts:=[112209,112209,112209,112209,81,112209,73,112201,1136,61,61,61,73,112201,71,112199]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk72_2 : Block 441 8 next72 32 16 := block_off (db:=book40) (branches:=guides) (ts:=[1138,61,61,61,71,112199,75,75,61,75,75,75,75,79437,61,61]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk72_3 : Block 441 8 next72 48 16 := block_off (db:=book40) (branches:=guides) (ts:=[79437,112209,112209,112209,112209,112201,61,61,112201,112199,1140,61,61,61,112199,112209]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk72_4 : Block 441 8 next72 64 16 := block_off (db:=book40) (branches:=guides) (ts:=[112209,112209,112209,112201,75,75,112201,112199,112199,75,75,112199,112199,79,79439,1142]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk72_5 : Block 441 8 next72 80 16 := block_off (db:=book40) (branches:=guides) (ts:=[61,79,79439,61,61,79439,61,79439,61,75,1146,75,75,75,75,79437]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk72_6 : Block 441 8 next72 96 16 := block_off (db:=book40) (branches:=guides) (ts:=[1148,79439,79437,112209,112209,112209,112209,112201,1150,79439,112201,112199,41,79439,112199,75]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk72_7 : Block 441 8 next72 112 16 := block_off (db:=book40) (branches:=guides) (ts:=[75,75,75,112209,112209,112209,112209,112201,77375,79437,112201,112199,698,79437,112199,112209]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk72_8 : Block 441 8 next72 128 16 := block_off (db:=book40) (branches:=guides) (ts:=[1152,112209,112209,112209,112209,112209,112209,112209,112209,112199,1032,112199,112201]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off72 : Excluded 441 9 state72 := by
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (q:=9) (width:=16) (vs:=next72) (by decide) (by decide +kernel)
  intro j
  fin_cases j
  · exact chk72_0
  · exact chk72_1
  · exact chk72_2
  · exact chk72_3
  · exact chk72_4
  · exact chk72_5
  · exact chk72_6
  · exact chk72_7
  · exact chk72_8
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off73 : Excluded 441 9 state73 := audit_off (db:=book40) (branches:=guides) (g:=75) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off74 : Excluded 441 9 state74 := audit_off (db:=book40) (branches:=guides) (g:=81) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off75 : Excluded 441 9 state75 := audit_off (db:=book40) (branches:=guides) (g:=81) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off76 : Excluded 441 9 state76 := audit_off (db:=book40) (branches:=guides) (g:=81) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off77 : Excluded 441 9 state77 := audit_off (db:=book40) (branches:=guides) (g:=81) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off78 : Excluded 441 9 state78 := audit_off (db:=book40) (branches:=guides) (g:=73) (by decide) (by decide +kernel)
def next79 := successors 441 8 state79
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk79_0 : Block 441 8 next79 0 16 := block_off (db:=book40) (branches:=guides) (ts:=[81,144465,144465,144465,144465,144465,81,144465,145489,73,73,73,73,73,61,73]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk79_1 : Block 441 8 next79 16 16 := block_off (db:=book40) (branches:=guides) (ts:=[73,73,144461,63,63,63,61,144461,144459,1158,61,144459,144465,144465,144465,144465]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk79_2 : Block 441 8 next79 32 16 := block_off (db:=book40) (branches:=guides) (ts:=[177223,1160,61,177223,144977,61,73,144465,1166,73,144465,144465,144465,144465,144465,144465]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk79_3 : Block 441 8 next79 48 16 := block_off (db:=book40) (branches:=guides) (ts:=[79,144463,1168,1174,79,144463,1176,3,144463,1182,1184,144463,1186,61,73,73]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk79_4 : Block 441 8 next79 64 16 := block_off (db:=book40) (branches:=guides) (ts:=[73,73,144461,63,144463,144461,144459,1188,144463,144459,144465,144465,144465,144465,177223,1190]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk79_5 : Block 441 8 next79 80 16 := block_off (db:=book40) (branches:=guides) (ts:=[144463,177223,77,77,63,144461,63,63,77,144461,1200,63,1214,63,73,63]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk79_6 : Block 441 8 next79 96 16 := block_off (db:=book40) (branches:=guides) (ts:=[73,73,73,73,144459,63,144461,144459,144465,144465,144465,144465,177223,63,144461,177223]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk79_7 : Block 441 8 next79 112 16 := block_off (db:=book40) (branches:=guides) (ts:=[75,144459,1216,1218,75,144459,1220,3,73,1222,73,73,73,73,144465,144465]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk79_8 : Block 441 8 next79 128 16 := block_off (db:=book40) (branches:=guides) (ts:=[144465,144465,177223,766,144459,177223,71,177223,1224,1226,71,177223,1228,3,177223,73]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk79_9 : Block 441 8 next79 144 16 := block_off (db:=book40) (branches:=guides) (ts:=[177223,73,144465,144465,144465,144465]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off79 : Excluded 441 9 state79 := by
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (q:=10) (width:=16) (vs:=next79) (by decide) (by decide +kernel)
  intro j
  fin_cases j
  · exact chk79_0
  · exact chk79_1
  · exact chk79_2
  · exact chk79_3
  · exact chk79_4
  · exact chk79_5
  · exact chk79_6
  · exact chk79_7
  · exact chk79_8
  · exact chk79_9
def next80 := successors 441 8 state80
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk80_0 : Block 441 8 next80 0 16 := block_off (db:=book40) (branches:=guides) (ts:=[73,143953,73,61,144465,73,77,144973,63,61,61,61,77,144973,75,144971]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk80_1 : Block 441 8 next80 16 16 := block_off (db:=book40) (branches:=guides) (ts:=[1232,61,61,61,75,144971,81,144977,144977,144977,144977,144977,81,144977,71,177735]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk80_2 : Block 441 8 next80 32 16 := block_off (db:=book40) (branches:=guides) (ts:=[1236,61,61,61,71,177735,73,73,61,73,73,73,73,144973,63,61]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk80_3 : Block 441 8 next80 48 16 := block_off (db:=book40) (branches:=guides) (ts:=[61,61,144973,144971,61,61,144971,144977,144977,144977,144977,177735,61,61,177735,144977]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk80_4 : Block 441 8 next80 64 16 := block_off (db:=book40) (branches:=guides) (ts:=[73,144977,144977,144977,144977,79,144975,1238,61,79,144975,61,61,144975,1240,61]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk80_5 : Block 441 8 next80 80 16 := block_off (db:=book40) (branches:=guides) (ts:=[144975,61,61,73,73,73,73,144973,63,144975,144973,144971,1242,144975,144971,144977]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk80_6 : Block 441 8 next80 96 16 := block_off (db:=book40) (branches:=guides) (ts:=[144977,144977,144977,177735,370,144975,177735,73,73,73,73,144971,63,144973,144971,144977]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk80_7 : Block 441 8 next80 112 16 := block_off (db:=book40) (branches:=guides) (ts:=[144977,144977,144977,177735,63,144973,177735,73,73,73,73,144977,144977,144977,144977,177735]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk80_8 : Block 441 8 next80 128 16 := block_off (db:=book40) (branches:=guides) (ts:=[1,144971,177735,177735,73,177735,73,144977,144977,144977,144977]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off80 : Excluded 441 9 state80 := by
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (q:=9) (width:=16) (vs:=next80) (by decide) (by decide +kernel)
  intro j
  fin_cases j
  · exact chk80_0
  · exact chk80_1
  · exact chk80_2
  · exact chk80_3
  · exact chk80_4
  · exact chk80_5
  · exact chk80_6
  · exact chk80_7
  · exact chk80_8
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off81 : Excluded 441 9 state81 := audit_off (db:=book40) (branches:=guides) (g:=73) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off82 : Excluded 441 9 state82 := audit_off (db:=book40) (branches:=guides) (g:=71) (by decide) (by decide +kernel)
def next83 := successors 441 8 state83
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk83_0 : Block 441 8 next83 0 16 := block_off (db:=book40) (branches:=guides) (ts:=[81,177233,177233,177233,177233,177233,81,177233,73,177225,1246,1252,1254,1,73,177225]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk83_1 : Block 441 8 next83 16 16 := block_off (db:=book40) (branches:=guides) (ts:=[178257,71,71,71,71,71,61,71,71,71,177229,1050,61,177229,177227,1256]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk83_2 : Block 441 8 next83 32 16 := block_off (db:=book40) (branches:=guides) (ts:=[1,1258,61,177227,177233,177233,177233,177233,177225,1260,61,177225,177745,61,71,177233]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk83_3 : Block 441 8 next83 48 16 := block_off (db:=book40) (branches:=guides) (ts:=[177233,177233,177233,177233,177233,71,1262,71,71,71,71,79,177231,1264,1270,79]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk83_4 : Block 441 8 next83 64 16 := block_off (db:=book40) (branches:=guides) (ts:=[177231,1272,1,177231,1274,1276,177231,1278,61,71,71,71,177231,71,71,177229]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk83_5 : Block 441 8 next83 80 16 := block_off (db:=book40) (branches:=guides) (ts:=[160,177231,177229,177227,41,177231,177227,177233,177233,177233,177233,177225,1280,177231,177225,77]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk83_6 : Block 441 8 next83 96 16 := block_off (db:=book40) (branches:=guides) (ts:=[177229,1282,1284,77,177229,1286,1,71,1288,71,71,71,71,177227,1290,177229]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk83_7 : Block 441 8 next83 112 16 := block_off (db:=book40) (branches:=guides) (ts:=[177227,177233,177233,177233,177233,177225,142399,177229,177225,75,75,1292,177227,1294,1,75]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk83_8 : Block 441 8 next83 128 16 := block_off (db:=book40) (branches:=guides) (ts:=[177227,1304,1310,1318,1,71,1320,71,71,71,71,177233,177233,177233,177233,177225]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk83_9 : Block 441 8 next83 144 16 := block_off (db:=book40) (branches:=guides) (ts:=[1322,177227,177225,177233,1326,177233,177233,177233,177233]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off83 : Excluded 441 9 state83 := by
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (q:=10) (width:=16) (vs:=next83) (by decide) (by decide +kernel)
  intro j
  fin_cases j
  · exact chk83_0
  · exact chk83_1
  · exact chk83_2
  · exact chk83_3
  · exact chk83_4
  · exact chk83_5
  · exact chk83_6
  · exact chk83_7
  · exact chk83_8
  · exact chk83_9
def next84 := successors 441 8 state84
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk84_0 : Block 441 8 next84 0 16 := block_off (db:=book40) (branches:=guides) (ts:=[71,176721,71,61,177233,71,77,177741,1330,61,61,61,77,177741,75,177739]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk84_1 : Block 441 8 next84 16 16 := block_off (db:=book40) (branches:=guides) (ts:=[1332,61,61,61,75,177739,81,177745,177745,177745,177745,177745,81,177745,73,177737]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk84_2 : Block 441 8 next84 32 16 := block_off (db:=book40) (branches:=guides) (ts:=[1336,61,61,61,73,177737,71,71,61,71,71,71,71,177741,61,61]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk84_3 : Block 441 8 next84 48 16 := block_off (db:=book40) (branches:=guides) (ts:=[177741,177739,1338,61,61,61,177739,177745,177745,177745,177745,177737,61,61,177737,177745]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk84_4 : Block 441 8 next84 64 16 := block_off (db:=book40) (branches:=guides) (ts:=[177745,177745,177745,71,71,71,71,79,177743,1346,1348,61,61,79,79,61]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk84_5 : Block 441 8 next84 80 16 := block_off (db:=book40) (branches:=guides) (ts:=[177743,61,61,177743,1350,61,177743,61,61,71,71,71,71,177741,1352,177743]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk84_6 : Block 441 8 next84 96 16 := block_off (db:=book40) (branches:=guides) (ts:=[177741,177739,41,177743,177739,177745,177745,177745,177745,177737,1354,177743,177737,71,71,71]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk84_7 : Block 441 8 next84 112 16 := block_off (db:=book40) (branches:=guides) (ts:=[71,177739,664,177741,177739,177745,177745,177745,177745,177737,142911,177741,177737,71,71,71]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk84_8 : Block 441 8 next84 128 16 := block_off (db:=book40) (branches:=guides) (ts:=[71,177745,177745,177745,177745,177737,748,177739,177737,177745,1358,177745,177745,177745,177745]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off84 : Excluded 441 9 state84 := by
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (q:=9) (width:=16) (vs:=next84) (by decide) (by decide +kernel)
  intro j
  fin_cases j
  · exact chk84_0
  · exact chk84_1
  · exact chk84_2
  · exact chk84_3
  · exact chk84_4
  · exact chk84_5
  · exact chk84_6
  · exact chk84_7
  · exact chk84_8
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem off85 : Excluded 441 9 state85 := audit_off (db:=book40) (branches:=guides) (g:=71) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem giantOff : Excluded 441 10 spec253.basis := by
  apply join_exclusions (by decide +kernel)
  have eq : successors 441 9 spec253.basis=[state0,state1,state2,state3,state4,state5,state6,state7,state8,state9,state10,state11,state12,state13,state14,state15,state16,state17,state18,state19,state20,state21,state22,state23,state24,state25,state26,state27,state28,state29,state30,state31,state32,state33,state34,state35,state36,state37,state38,state39,state40,state41,state42,state43,state44,state45,state46,state47,state48,state49,state50,state51,state52,state53,state54,state55,state56,state57,state58,state59,state60,state61,state62,state63,state64,state65,state66,state67,state68,state69,state70,state71,state72,state73,state74,state75,state76,state77,state78,state79,state80,state81,state82,state83,state84,state85] := by decide +kernel
  rw [eq]
  exact (List.forall_mem_cons.mpr ⟨off0,(List.forall_mem_cons.mpr ⟨off1,(List.forall_mem_cons.mpr ⟨off2,(List.forall_mem_cons.mpr ⟨off3,(List.forall_mem_cons.mpr ⟨off4,(List.forall_mem_cons.mpr ⟨off5,(List.forall_mem_cons.mpr ⟨off6,(List.forall_mem_cons.mpr ⟨off7,(List.forall_mem_cons.mpr ⟨off8,(List.forall_mem_cons.mpr ⟨off9,(List.forall_mem_cons.mpr ⟨off10,(List.forall_mem_cons.mpr ⟨off11,(List.forall_mem_cons.mpr ⟨off12,(List.forall_mem_cons.mpr ⟨off13,(List.forall_mem_cons.mpr ⟨off14,(List.forall_mem_cons.mpr ⟨off15,(List.forall_mem_cons.mpr ⟨off16,(List.forall_mem_cons.mpr ⟨off17,(List.forall_mem_cons.mpr ⟨off18,(List.forall_mem_cons.mpr ⟨off19,(List.forall_mem_cons.mpr ⟨off20,(List.forall_mem_cons.mpr ⟨off21,(List.forall_mem_cons.mpr ⟨off22,(List.forall_mem_cons.mpr ⟨off23,(List.forall_mem_cons.mpr ⟨off24,(List.forall_mem_cons.mpr ⟨off25,(List.forall_mem_cons.mpr ⟨off26,(List.forall_mem_cons.mpr ⟨off27,(List.forall_mem_cons.mpr ⟨off28,(List.forall_mem_cons.mpr ⟨off29,(List.forall_mem_cons.mpr ⟨off30,(List.forall_mem_cons.mpr ⟨off31,(List.forall_mem_cons.mpr ⟨off32,(List.forall_mem_cons.mpr ⟨off33,(List.forall_mem_cons.mpr ⟨off34,(List.forall_mem_cons.mpr ⟨off35,(List.forall_mem_cons.mpr ⟨off36,(List.forall_mem_cons.mpr ⟨off37,(List.forall_mem_cons.mpr ⟨off38,(List.forall_mem_cons.mpr ⟨off39,(List.forall_mem_cons.mpr ⟨off40,(List.forall_mem_cons.mpr ⟨off41,(List.forall_mem_cons.mpr ⟨off42,(List.forall_mem_cons.mpr ⟨off43,(List.forall_mem_cons.mpr ⟨off44,(List.forall_mem_cons.mpr ⟨off45,(List.forall_mem_cons.mpr ⟨off46,(List.forall_mem_cons.mpr ⟨off47,(List.forall_mem_cons.mpr ⟨off48,(List.forall_mem_cons.mpr ⟨off49,(List.forall_mem_cons.mpr ⟨off50,(List.forall_mem_cons.mpr ⟨off51,(List.forall_mem_cons.mpr ⟨off52,(List.forall_mem_cons.mpr ⟨off53,(List.forall_mem_cons.mpr ⟨off54,(List.forall_mem_cons.mpr ⟨off55,(List.forall_mem_cons.mpr ⟨off56,(List.forall_mem_cons.mpr ⟨off57,(List.forall_mem_cons.mpr ⟨off58,(List.forall_mem_cons.mpr ⟨off59,(List.forall_mem_cons.mpr ⟨off60,(List.forall_mem_cons.mpr ⟨off61,(List.forall_mem_cons.mpr ⟨off62,(List.forall_mem_cons.mpr ⟨off63,(List.forall_mem_cons.mpr ⟨off64,(List.forall_mem_cons.mpr ⟨off65,(List.forall_mem_cons.mpr ⟨off66,(List.forall_mem_cons.mpr ⟨off67,(List.forall_mem_cons.mpr ⟨off68,(List.forall_mem_cons.mpr ⟨off69,(List.forall_mem_cons.mpr ⟨off70,(List.forall_mem_cons.mpr ⟨off71,(List.forall_mem_cons.mpr ⟨off72,(List.forall_mem_cons.mpr ⟨off73,(List.forall_mem_cons.mpr ⟨off74,(List.forall_mem_cons.mpr ⟨off75,(List.forall_mem_cons.mpr ⟨off76,(List.forall_mem_cons.mpr ⟨off77,(List.forall_mem_cons.mpr ⟨off78,(List.forall_mem_cons.mpr ⟨off79,(List.forall_mem_cons.mpr ⟨off80,(List.forall_mem_cons.mpr ⟨off81,(List.forall_mem_cons.mpr ⟨off82,(List.forall_mem_cons.mpr ⟨off83,(List.forall_mem_cons.mpr ⟨off84,(List.forall_mem_cons.mpr ⟨off85,(by simp)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
theorem rootFloor : Floor 441 spec253 := floorEx giantOff (by decide +kernel) (by decide +kernel)
open PEqualNP.CircuitLowerBounds
theorem lower (C : Circuit) (fan : ∀ g∈C.gates, g.op ∈ ({.and,.or,.not} : Set GateOp) ∧ g.inputs.length≤2)
    (result : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x)=target (List.ofFn x)) : 12≤C.gates.countP counted := by
  by_contra small
  obtain ⟨k,lim,h⟩ := trace C fan result
  have ok : feasible 441 11 inputs := ⟨k,by omega,h,by decide +kernel⟩
  have no := floor_consistent (by decide) ok spec253 rootFloor 0
  have yes : contradictsFloor 441 11 inputs spec253 0=true := by decide +kernel
  exact Bool.noConfusion (yes.symm.trans no)
theorem solve (gates : List Gate) (o : ℕ)
    (legal : ∀ g∈gates, (g.op=.and ∨ g.op=.or ∨ g.op=.not) ∧ g.inputs.length≤2)
    (result : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates,o⟩ (List.ofFn x)=target (List.ofFn x)) :
    ∃ (v : List Gate) (p : ℕ), (∀ g∈v, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2) ∧ v.length≤gates.length ∧
      ∀ x : Fin 8 → Bool, Circuit.eval ⟨v,p⟩ (List.ofFn x)=target (List.ofFn x) := by
  by_cases all : ∀ g∈gates, g.op=.and ∨ g.op=.or
  · exact ⟨gates,o,fun g h => ⟨all g h,(legal g h).2⟩,le_rfl,result⟩
  push Not at all
  obtain ⟨g,mem,na,no⟩ := all
  have nt : g.op=.not := ((legal g mem).1.resolve_left na).resolve_left no
  have lt : gates.countP counted < gates.length := List.countP_lt_length_iff.mpr ⟨g,mem,by simp [counted,nt]⟩
  have lb := lower ⟨gates,o⟩ (by intro v hv; simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using legal v hv) result
  change 12≤gates.countP counted at lb
  exact ⟨gs,20,basis,count ▸ (by omega : 13≤gates.length),computes⟩
end PEqualNP.Outside.L_meta_28604

theorem PEqualNP.Outside.L_meta_28604 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o legal _ result
  exact PEqualNP.Outside.L_meta_28604.solve gates o legal result
